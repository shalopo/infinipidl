###################################################
# Samba4 NDR parser generator for IDL structures
# Copyright tridge@samba.org 2000-2003
# Copyright tpot@samba.org 2001
# Copyright jelmer@samba.org 2004-2006
# released under the GNU GPL

package Parse::Pidl::Samba4::NDR::Parser;

require Exporter;
@ISA = qw(Exporter);
@EXPORT_OK = qw(check_null_pointer NeededFunction NeededElement NeededType $res NeededInterface TypeFunctionName);

use strict;
use Data::Dumper;
use Parse::Pidl::Typelist qw(hasType getType mapTypeName typeHasBody mapScalarType);
use Parse::Pidl::Util qw(has_property ParseExpr ParseExprExt print_uuid unmake_str);
use Parse::Pidl::CUtil qw(get_pointer_to get_value_of get_array_element);
use Parse::Pidl::NDR qw(GetPrevLevel GetNextLevel ContainsDeferred ContainsPipe is_charset_array);
use Parse::Pidl::Samba4 qw(is_intree choose_header ArrayDynamicallyAllocated);
use Parse::Pidl::Samba4::Header qw(GenerateFunctionInEnv GenerateFunctionOutEnv EnvSubstituteValue GenerateStructEnv);
use Parse::Pidl qw(warning);

use vars qw($VERSION);
$VERSION = '0.01';

use constant INDENT => "    ";

# list of known types
my %typefamily;

sub assert_unssupported_element($$)
{
	my ($msg, $e) = @_;
	print(Dumper($e));
	die("Unsupported flow: $msg");
}

sub new($$) {
	my ($class) = @_;
	my $self = { res => "", deferred => [], tabs => "", defer_tabs => "", next_switch_var => "", was_last_line_space => "",
				 scoped_flags => undef, remaining_blob => 0 };
	bless($self, $class);
}

sub get_typefamily($)
{
	my $n = shift;
	return $typefamily{$n};
}

sub append_prefix($$)
{
	my ($e, $var_name) = @_;
	my $pointers = 0;
	my $arrays = 0;

	foreach my $l (@{$e->{LEVELS}}) {
		if ($l->{TYPE} eq "POINTER") {
			$pointers++;
		} elsif ($l->{TYPE} eq "ARRAY") {
			$arrays++;
			if (($pointers == 0) and 
			    (not $l->{IS_FIXED}) and
			    (not $l->{IS_INLINE})) {
				return get_value_of($var_name);
			}
		} elsif ($l->{TYPE} eq "DATA") {
			if (Parse::Pidl::Typelist::scalar_is_reference($l->{DATA_TYPE})) {
				return get_value_of($var_name) unless ($pointers or $arrays);
			}
		}
	}
	
	return $var_name;
}

sub has_fast_array($$)
{
	my ($e,$l) = @_;

	# Unnecessary optimization
	return 0;

	# return 0 if ($l->{TYPE} ne "ARRAY");
	#
	# my $nl = GetNextLevel($e,$l);
	# return 0 unless ($nl->{TYPE} eq "DATA");
	# return 0 unless (hasType($nl->{DATA_TYPE}));
	#
	# my $t = getType($nl->{DATA_TYPE});
	#
	# # Only uint8 and string have fast array functions at the moment
	# return ($t->{NAME} eq "uint8") or ($t->{NAME} eq "string");
}


####################################
# pidl() is our basic output routine
sub pidl($$)
{
	my ($self, $d) = @_;
	if ($d) {
        $self->{was_last_line_space} = ($d eq "{");
        $self->{res} .= $self->{tabs};
        $self->{res} .= $d;
	}
    else
    {
        return if ($self->{was_last_line_space});
        $self->{was_last_line_space} = 1;
    }
	$self->{res} .="\n";
}

####################################
# defer() is like pidl(), but adds to 
# a deferred buffer which is then added to the 
# output buffer at the end of the structure/union/function
# This is needed to cope with code that must be pushed back
# to the end of a block of elements
sub defer_indent($) { my ($self) = @_; $self->{defer_tabs}.=INDENT; }
sub defer_deindent($) { my ($self) = @_; $self->{defer_tabs}=substr($self->{defer_tabs}, 0, -length(INDENT)); }

sub defer($$)
{
	my ($self, $d) = @_;
	if ($d) {
		push(@{$self->{deferred}}, $self->{defer_tabs}.$d);
	}
}

########################################
# add the deferred content to the current
# output
sub add_deferred($)
{
	my ($self) = @_;
	$self->pidl($_) foreach (@{$self->{deferred}});
	$self->{deferred} = [];
	$self->{defer_tabs} = "";
}

sub indent($)
{
	my ($self) = @_;
	$self->{tabs} .= INDENT;
}

sub deindent($)
{
	my ($self) = @_;
	$self->{tabs} = substr($self->{tabs}, 0, -length(INDENT));
}

sub start_block($)
{
	my ($self) = @_;
    $self->pidl("{");
    $self->indent;
}

sub end_block($)
{
	my $self = shift;
	my $newline = @_ ? shift : 1;

    $self->deindent;
    $self->pidl("}");

	if ($newline) {
		$self->pidl("");
	}
}

sub start_function($)
{
	my ($self) = @_;
	$self->start_block();
}

sub end_function($)
{
	my ($self) = @_;
	$self->{remaining_blob} = 0;
	$self->end_block();
}

sub end_struct($)
{
	my ($self) = @_;
    $self->deindent;
    $self->pidl("};");
    $self->pidl("");
}

#####################################################################
# declare a function public or static, depending on its attributes
sub fn_declare($$$$)
{
	my ($self,$dir,$fn,$decl) = @_;

	my $no_pull_push_attr_name = $dir eq "get" ? "nopull" : "nopush";

	if (has_property($fn, $no_pull_push_attr_name)) {
		return 0;
	}

	$self->pidl("$decl");

	return 1;
}

###################################################################
# setup any special flags for an element or structure
sub start_flags($$$$)
{
	my ($self, $e, $ndr, $scope_required) = @_;
	my $flags = has_property($e, "flag");
	if ($flags) {
		if ($scope_required) {
			$self->{scoped_flags} = $flags;
			return if ($e->{TYPE} eq "DATA_BLOB");

			$self->pidl("");
			$self->start_block;
		}

		my $options_guard_var_name = $scope_required ? "scoped_options_guard" : "options_guard";
		$self->pidl("const auto $options_guard_var_name = $ndr.push_flags($flags);");
		$self->pidl("");
	}
}

###################################################################
# end any special flags for an element or structure
sub end_flags($$$)
{
	my ($self, $e) = @_;

	if ($self->{scoped_flags}) {
		$self->end_block;
		$self->{scoped_flags} = undef;
	}
}

#####################################################################
# parse the data of an array - push side
sub ParseArrayPushHeader($$$$$$)
{
	my ($self,$e,$l,$ndr,$var_name,$env) = @_;

	assert_unssupported_element("string without charset", $e) if (has_property($e, "string") and !has_property($e, "charset"));

	if ($l->{IS_ZERO_TERMINATED}) {
		assert_unssupported_element("string without charset", $e) unless (has_property($e, "charset"));
		return undef, undef;
	}

	my $length = ParseExpr($l->{LENGTH_IS}, $env, $e);
	my $size = ParseExpr($l->{SIZE_IS}, $env, $e);

	if (is_charset_array($e,$l))
	{
		return $length, $size;
	}

	if ((!$l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT} and $l->{IS_VARYING})
	{
		if ($length eq $size) {
			$self->pidl("$ndr.put_conformant_varying_array_header($length);");
		}
		else {
			$self->pidl("$ndr.put_conformant_varying_array_header($length, $size);");
		}
	}
	else
	{
		if ((!$l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT}) {
			$self->pidl("$ndr.put_array_size($size);");
		}

		if ($l->{IS_VARYING}) {
			$self->pidl("$ndr.put_array_offset(0);");
			$self->pidl("$ndr.put_array_length($length);");
		}
	}

	return $length, $size;
}

sub check_fully_dereferenced($$)
{
	my ($element, $env) = @_;

	return sub ($) {
		my $origvar = shift;
		my $check = 0;

		# Figure out the number of pointers in $ptr
		my $expandedvar = $origvar;
		$expandedvar =~ s/^(\**)//;
		my $ptr = $1;

		my $var = undef;
		foreach (keys %$env) {
			if ($env->{$_} eq $expandedvar) {
				$var = $_;
				last;
			}
		}
		
		return($origvar) unless (defined($var));
		my $e;
		foreach (@{$element->{PARENT}->{ELEMENTS}}) {
			if ($_->{NAME} eq $var) {
				$e = $_;
				last;
			}
		}

		$e or die("Environment doesn't match siblings");

		# See if pointer at pointer level $level
		# needs to be checked.
		my $nump = 0;
		foreach (@{$e->{LEVELS}}) {
			if ($_->{TYPE} eq "POINTER") {
				$nump = $_->{POINTER_INDEX}+1;
			}
		}
		warning($element->{ORIGINAL}, "Got pointer for `$e->{NAME}', expected fully dereferenced variable") if ($nump > length($ptr));
		return ($origvar);
	}
}	

sub check_null_pointer($$$$)
{
	my ($element, $env, $print_fn, $return) = @_;

	return sub ($) {
		my $expandedvar = shift;
		my $check = 0;

		# Figure out the number of pointers in $ptr
		$expandedvar =~ s/^(\**)//;
		my $ptr = $1;

		my $var = undef;
		foreach (keys %$env) {
			if ($env->{$_} eq $expandedvar) {
				$var = $_;
				last;
			}
		}
		
		if (defined($var)) {
			my $e;
			# lookup ptr in $e
			foreach (@{$element->{PARENT}->{ELEMENTS}}) {
				if ($_->{NAME} eq $var) {
					$e = $_;
					last;
				}
			}

			$e or die("Environment doesn't match siblings");

			# See if pointer at pointer level $level
			# needs to be checked.
			foreach my $l (@{$e->{LEVELS}}) {
				if ($l->{TYPE} eq "POINTER" and 
					$l->{POINTER_INDEX} == length($ptr)) {
					# No need to check ref pointers
					$check = ($l->{POINTER_TYPE} ne "ref");
					last;
				}

				if ($l->{TYPE} eq "DATA") {
					warning($element, "too much dereferences for `$var'");
				}
			}
		} else {
			warning($element, "unknown dereferenced expression `$expandedvar'");
			$check = 1;
		}
		
		$print_fn->("if ($ptr$expandedvar == NULL) $return") if $check;
	}
}

sub is_deferred_switch_non_empty($)
{
	# 1 if there needs to be a deferred branch in an ndr_pull/push,
	# 0 otherwise.
	my ($e) = @_;
	my $have_default = 0;
	foreach my $el (@{$e->{ELEMENTS}}) {
		if ($el->{CASE} eq "default") {
			$have_default = 1;
		}
		if ($el->{TYPE} ne "EMPTY") {
			if (ContainsDeferred($el, $el->{LEVELS}[0])) {
				return 1;
			}
		}
	}
	return ! $have_default;
}

sub ParseArrayPullGetSize($$$$$$)
{
	my ($self,$e,$l,$ndr,$var_name,$env) = @_;

	my $array_size_var = "size_$e->{NAME}";

	if ($l->{IS_CONFORMANT}) {
		# we already declared and initialized $array_size_var
	} elsif ($l->{IS_ZERO_TERMINATED} and $l->{SIZE_IS} == 0 and $l->{LENGTH_IS} == 0) { # Noheader arrays
		$self->pidl("const uint32_t $array_size_var = ndr_get_string_size($ndr, sizeof(*$var_name))");
	} else {
		my $size = ParseExprExt($l->{SIZE_IS}, $env, $e->{ORIGINAL},
							 	check_null_pointer($e, $env, sub { $self->pidl(shift); },
									               "return ndr_pull_error($ndr, NDR_ERR_INVALID_POINTER, \"NULL Pointer for size_is()\");"),
							 	check_fully_dereferenced($e, $env));
		$self->pidl("const uint32_t $array_size_var = $size;");
	}

	if (my $range = has_property($e, "range")) {
		my ($low, $high) = split(/,/, $range, 2);
		if ($low < 0) {
			warning(0, "$low is invalid for the range of an array size");
		}
		if ($low == 0) {
			$self->pidl("if ($array_size_var > $high)");
		} else {
			$self->pidl("if ($array_size_var < $low || $array_size_var > $high)");
		}
        $self->struct_block;
		$self->pidl("return ndr_pull_error($ndr, NDR_ERR_RANGE, \"value out of range\");");
		$self->end_block;
	}

	return $array_size_var;
}

#####################################################################
# parse an array - pull side
sub ParseArrayPullGetLength($$$$$$;$)
{
	my ($self,$e,$l,$ndr,$var_name,$env,$array_size) = @_;

	if (not defined($array_size)) {
		$array_size = $self->ParseArrayPullGetSize($e, $l, $ndr, $var_name, $env);
	}

	if (not $l->{IS_VARYING}) {
		return $array_size;
	}

	my $array_length = "length_$e->{NAME}";

	if (my $range = has_property($e, "range")) {
		my ($low, $high) = split(/,/, $range, 2);
		if ($low < 0) {
			warning(0, "$low is invalid for the range of an array size");
		}
		if ($low == 0) {
			$self->pidl("if ($array_length > $high)");
		} else {
			$self->pidl("if ($array_length < $low || $array_length > $high)");
		}
        $self->start_block;
		$self->pidl("return ndr_pull_error($ndr, NDR_ERR_RANGE, \"value out of range\");");
		$self->end_block;
	}

	return $array_length;
}

#####################################################################
# parse an array - pull side
sub ParseArrayPullHeader($$$$$$)
{
	my ($self,$e,$l,$ndr,$var_name,$env) = @_;

	if (is_charset_array($e,$l)) {
		return $self->ParseArrayPullGetSize($e, $l, $ndr, $var_name, $env)
	}

	my $array_length = "length_$e->{NAME}";

	if (!($l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT} and $l->{IS_VARYING})
	{
		$self->pidl("const uint32_t $array_length = $ndr.get_conformant_varying_array_length();");
	}
	else {
		if ((!$l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT}) {
			$self->pidl("const uint32_t size_$e->{NAME} = $ndr.get_array_size();");
		}

		if ($l->{IS_VARYING}) {
			$self->pidl("$ndr.get_zero_offset();");
			$self->pidl("const uint32_t $array_length = $ndr.get_array_length();");
		}

		my $array_size = $self->ParseArrayPullGetSize($e, $l, $ndr, $var_name, $env);
		$array_length = $self->ParseArrayPullGetLength($e, $l, $ndr, $var_name, $env, $array_size);

		if ($array_length ne $array_size) {
			$self->ParseCheck($ndr, "$array_length <= $array_size", "Array size should exceed array length", $array_size, $array_length);
		}
	}

	if (ArrayDynamicallyAllocated($e,$l) and not is_charset_array($e,$l)) {
		$self->AllocateArrayLevel($e,$l,$ndr,$var_name,$array_length);
	}

	return $array_length;
}

sub compression_alg($$)
{
	my ($e, $l) = @_;
	my ($alg, $clen, $dlen) = split(/,/, $l->{COMPRESSION});

	return $alg;
}

sub compression_clen($$$)
{
	my ($e, $l, $env) = @_;
	my ($alg, $clen, $dlen) = split(/,/, $l->{COMPRESSION});

	return ParseExpr($clen, $env, $e->{ORIGINAL});
}

sub compression_dlen($$$)
{
	my ($e,$l,$env) = @_;
	my ($alg, $clen, $dlen) = split(/,/, $l->{COMPRESSION});

	return ParseExpr($dlen, $env, $e->{ORIGINAL});
}

sub ParseCompressionPushStart($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $comndr = "$ndr\_compressed";
	my $alg = compression_alg($e, $l);
	my $dlen = compression_dlen($e, $l, $env);

	$self->start_block;
	$self->pidl("NdrWriter& $comndr;");
	$self->pidl("ndr_push_compression_start($ndr, &$comndr, $alg, $dlen);");

	return $comndr;
}

sub ParseCompressionPushEnd($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $comndr = "$ndr\_compressed";
	my $alg = compression_alg($e, $l);
	my $dlen = compression_dlen($e, $l, $env);

	$self->pidl("ndr_push_compression_end($ndr, $comndr, $alg, $dlen);");
	$self->end_block;
}

sub ParseCompressionPullStart($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $comndr = "$ndr\_compressed";
	my $alg = compression_alg($e, $l);
	my $dlen = compression_dlen($e, $l, $env);
	my $clen = compression_clen($e, $l, $env);

	$self->start_block;
	$self->pidl("NdrReader& $comndr;");
	$self->pidl("ndr_pull_compression_start($ndr, &$comndr, $alg, $dlen, $clen);");

	return $comndr;
}

sub ParseCompressionPullEnd($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $comndr = "$ndr\_compressed";
	my $alg = compression_alg($e, $l);
	my $dlen = compression_dlen($e, $l, $env);

	$self->pidl("ndr_pull_compression_end($ndr, $comndr, $alg, $dlen);");
	$self->end_block;
}

sub ParseSubcontextPushStart($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $subndr = "_ndr_$e->{NAME}";
	my $subcontext_size = ParseExpr($l->{SUBCONTEXT_SIZE}, $env, $e->{ORIGINAL});

	$self->start_block;
	$self->pidl("NdrWriter& $subndr;");
	$self->pidl("ndr_push_subcontext_start($ndr, &$subndr, $l->{HEADER_SIZE}, $subcontext_size);");

	if (defined $l->{COMPRESSION}) {
		$subndr = $self->ParseCompressionPushStart($e, $l, $subndr, $env);
	}

	return $subndr;
}

sub ParseSubcontextPushEnd($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $subndr = "_ndr_$e->{NAME}";
	my $subcontext_size = ParseExpr($l->{SUBCONTEXT_SIZE}, $env, $e->{ORIGINAL});

	if (defined $l->{COMPRESSION}) {
		$self->ParseCompressionPushEnd($e, $l, $subndr, $env);
	}

	$self->pidl("ndr_push_subcontext_end($ndr, $subndr, $l->{HEADER_SIZE}, $subcontext_size);");
	$self->end_block;
}

sub ParseSubcontextPullStart($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $subndr = "_ndr_$e->{NAME}";
	my $subcontext_size = ParseExpr($l->{SUBCONTEXT_SIZE}, $env, $e->{ORIGINAL});

	$self->start_block;
	$self->pidl("NdrReader& $subndr;");
	$self->pidl("ndr_pull_subcontext_start($ndr, &$subndr, $l->{HEADER_SIZE}, $subcontext_size);");

	if (defined $l->{COMPRESSION}) {
		$subndr = $self->ParseCompressionPullStart($e, $l, $subndr, $env);
	}

	return $subndr;
}

sub ParseSubcontextPullEnd($$$$$)
{
	my ($self,$e,$l,$ndr,$env) = @_;
	my $subndr = "_ndr_$e->{NAME}";
	my $subcontext_size = ParseExpr($l->{SUBCONTEXT_SIZE}, $env, $e->{ORIGINAL});

	if (defined $l->{COMPRESSION}) {
		$self->ParseCompressionPullEnd($e, $l, $subndr, $env);
	}

	$self->pidl("ndr_pull_subcontext_end($ndr, $subndr, $l->{HEADER_SIZE}, $subcontext_size);");
	$self->end_block;
}

sub ParseElementPushLevel
{
	my ($self,$e,$l,$ndr,$var_name,$env,$primitives,$deferred) = @_;

	my $scope = CalcNdrScope($l, $primitives, $deferred);

	if ($l->{TYPE} eq "ARRAY" and ($l->{IS_CONFORMANT} or $l->{IS_VARYING})) {
		$var_name = get_pointer_to($var_name);
	}

	if (defined($scope)) {
		if ($l->{TYPE} eq "SUBCONTEXT") {
			my $subndr = $self->ParseSubcontextPushStart($e, $l, $ndr, $env);
			$self->ParseElementPushLevel($e, GetNextLevel($e, $l), $subndr, $var_name, $env, 1, 1);
			$self->ParseSubcontextPushEnd($e, $l, $ndr, $env);
		} elsif ($l->{TYPE} eq "POINTER") {
			$self->ParsePtrPush($e, $l, $ndr, $var_name);
		} elsif ($l->{TYPE} eq "ARRAY") {
			my ($length, $size) = $self->ParseArrayPushHeader($e, $l, $ndr, $var_name, $env);

			my $nl = GetNextLevel($e, $l);

			# Allow speedups for arrays of scalar types
			if (is_charset_array($e,$l)) {
				assert_unssupported_element("to_null string", $e) if ($l->{IS_TO_NULL});
				my $string_params = "";
				if ($length or $size)
				{
					assert_unssupported_element("length-only or size-only custom string", $e) unless ($length and $size);

					if ($length eq $size) {
						if ((!$l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT} and $l->{IS_VARYING}) {
							$string_params = ", NdrStringParams::by_custom_length($length)";
						}
						else {
							$string_params = ", NdrStringParams::by_external_length($length)";
						}
					}
					else {
						$string_params = ", NdrStringParams::by_custom_length($length, $size)";
					}
				}

				$self->pidl("$ndr.put_string<StringEncodingType::$e->{PROPERTIES}->{charset}>($var_name".$string_params.");");
				return;
			} elsif (has_fast_array($e,$l)) {
				$self->pidl("ndr_push_array_$nl->{DATA_TYPE}($ndr, $scope, $var_name, $length);");
				return;
			}
		} elsif ($l->{TYPE} eq "SWITCH") {
			$self->ParseSwitchPush($e, $l, $ndr, $env);
		} elsif ($l->{TYPE} eq "DATA") {
			$self->ParseDataPush($e, $l, $ndr, $var_name, $primitives, $deferred);
		} elsif ($l->{TYPE} eq "TYPEDEF") {
			$typefamily{$e->{DATA}->{TYPE}}->{PUSH_FN_BODY}->($self, $e->{DATA}, $ndr, $var_name, $scope);
		}
	}

	if ($l->{TYPE} eq "POINTER" and $l->{POINTER_TYPE} eq "ignore") {
		$self->pidl("// [ignore] '$e->{NAME}'");
	} elsif ($l->{TYPE} eq "POINTER" and $deferred) {
		my $rel_var_name = $var_name;
		if ($l->{POINTER_TYPE} ne "ref") {
			$self->pidl("if ($var_name)");
			$self->start_block;
			if ($l->{POINTER_TYPE} eq "relative") {
				$self->pidl("ndr_push_relative_ptr2_start($ndr, $rel_var_name);");
			}
			if ($l->{POINTER_TYPE} eq "relative_short") {
				$self->pidl("ndr_push_short_relative_ptr2($ndr, $var_name);");
			}
		}
		$var_name = get_value_of($var_name);
		$self->ParseElementPushLevel($e, GetNextLevel($e, $l), $ndr, $var_name, $env, 1, 1);

		if ($l->{POINTER_TYPE} ne "ref") {
			if ($l->{POINTER_TYPE} eq "relative") {
				$self->pidl("ndr_push_relative_ptr2_end($ndr, $rel_var_name);");
			}
			$self->end_block;
		}
	} elsif ($l->{TYPE} eq "ARRAY" and not has_fast_array($e,$l) and
		not is_charset_array($e, $l)) {
		my $length = ParseExpr($l->{LENGTH_IS}, $env, $e->{ORIGINAL});

        die($e->{ORIGINAL}, "pointless array cntr: 'cntr_$e->{NAME}': length=$length") if ($length eq "0");

		my $counter = "i";

		my $array_pointless = ($length eq "0");

		if ($array_pointless) {
			warning($e->{ORIGINAL}, "pointless array `$e->{NAME}' will always have size 0");
		}

		$var_name = get_array_element($var_name, $counter);

		if ((($primitives and not $l->{IS_DEFERRED}) or ($deferred and $l->{IS_DEFERRED})) and not $array_pointless) {
            $self->pidl();
			$self->pidl("for (uint32_t $counter = 0; $counter < $length; $counter++)");
			$self->start_block;
			$self->ParseElementPushLevel($e, GetNextLevel($e, $l), $ndr, $var_name, $env, 1, 0);
			$self->end_block;
		}

		if ($deferred and ContainsDeferred($e, $l) and not $array_pointless) {
            $self->pidl();
			$self->pidl("for (uint32_t $counter = 0; $counter < $length; $counter++)");
			$self->start_block;
			$self->ParseElementPushLevel($e, GetNextLevel($e, $l), $ndr, $var_name, $env, 0, 1);
			$self->end_block;
		}
	} elsif ($l->{TYPE} eq "SWITCH") {
		$self->ParseElementPushLevel($e, GetNextLevel($e, $l), $ndr, $var_name, $env, $primitives, $deferred);
	}
}

#####################################################################
# parse scalars in a structure element
sub ParseElementPush($$$$$$)
{
	my ($self,$e,$ndr,$env,$primitives,$deferred) = @_;
	my $subndr = undef;

	my $var_name = $env->{$e->{NAME}};

	if (has_property($e, "skip") or has_property($e, "skip_noinit")) {
		$self->pidl("// [skip] '$var_name'");
		return;
	}

	return if ContainsPipe($e, $e->{LEVELS}[0]);

	return unless $primitives or ($deferred and ContainsDeferred($e, $e->{LEVELS}[0]));

	# Representation type is different from transmit_as
	if ($e->{REPRESENTATION_TYPE} ne $e->{TYPE}) {
		$self->start_block;
		my $transmit_name = "_transmit_$e->{NAME}";
		$self->pidl(mapTypeName($e->{TYPE}) ." $transmit_name;");
		$self->pidl("ndr_$e->{REPRESENTATION_TYPE}_to_$e->{TYPE}($var_name, " . get_pointer_to($transmit_name) . ");");
		$var_name = $transmit_name;
	}

	$var_name = append_prefix($e, $var_name);

	$self->start_flags($e, $ndr, 1);

	if (defined(my $value = has_property($e, "value"))) {
		$var_name = ParseExpr($value, $env, $e->{ORIGINAL});
	}

	$self->ParseElementPushLevel($e, $e->{LEVELS}[0], $ndr, $var_name, $env, $primitives, $deferred);

	$self->end_flags($e);

	if ($e->{REPRESENTATION_TYPE} ne $e->{TYPE}) {
		$self->end_block;
	}
}

#####################################################################
# parse a pointer in a struct element or function
sub ParsePtrPush($$$$$)
{
	my ($self,$e,$l,$ndr,$var_name) = @_;

	if ($l->{POINTER_TYPE} eq "ref") {
		if ($l->{LEVEL_INDEX} > 0) {
			$self->pidl("NDR_CHECK($var_name, \"nullptr [ref] pointer\");");
		}
		if ($l->{LEVEL} eq "EMBEDDED") {
			$self->pidl("ndr_push_ref_ptr(ndr); /* $var_name */");
		}
	} elsif ($l->{POINTER_TYPE} eq "relative") {
		$self->pidl("ndr_push_relative_ptr1($ndr, $var_name);");
	} elsif ($l->{POINTER_TYPE} eq "relative_short") {
		$self->pidl("ndr_push_short_relative_ptr1($ndr, $var_name);");
	} elsif ($l->{POINTER_TYPE} eq "unique") {
		$self->pidl("$ndr.put_ptr_ref_id($var_name);");
	} elsif ($l->{POINTER_TYPE} eq "full") {
		assert_unssupported_element("non-unique full pointer", $e);
		$self->pidl("ndr_push_full_ptr($ndr, $var_name);");
	} elsif ($l->{POINTER_TYPE} eq "ignore") {
	        # We don't want this pointer to appear on the wire at all
		$self->pidl("ndr_push_uint3264(ndr, NDR_SCALARS, 0);");
	} else {
		assert_unssupported_element("Unhandled pointer type $l->{POINTER_TYPE}", $e);
	}
}

sub need_pointer_to($$$)
{
	my ($e, $l, $scalar_only) = @_;

	my $t;
	if (ref($l->{DATA_TYPE})) {
		$t = "$l->{DATA_TYPE}->{TYPE}_$l->{DATA_TYPE}->{NAME}";
	} else {
		$t = $l->{DATA_TYPE};
	}

	if (not Parse::Pidl::Typelist::is_scalar($t)) {
		return 1 if $scalar_only;
	}

	my $arrays = 0;

	foreach my $tl (@{$e->{LEVELS}}) {
		last if $l == $tl;
		if ($tl->{TYPE} eq "ARRAY") {
			$arrays++;
		}
	}

	if (Parse::Pidl::Typelist::scalar_is_reference($t)) {
		return 1 unless $arrays;
	}

	return 0;
}

#####################################################################
# parse scalars in a structure element - pull size
sub ParseSwitchPull($$$$$$)
{
	my($self,$e,$l,$ndr,$var_name,$env) = @_;
	my $switch_var = ParseExprExt($l->{SWITCH_IS}, $env, $e->{ORIGINAL},
		check_null_pointer($e, $env, sub { $self->pidl(shift); },
				   "return ndr_pull_error($ndr, NDR_ERR_INVALID_POINTER, \"NULL Pointer for switch_is()\");"),
		check_fully_dereferenced($e, $env));

	$var_name = get_pointer_to($var_name);
	$self->{next_switch_var} = $switch_var;
}

#####################################################################
# push switch element
sub ParseSwitchPush($$$$$$)
{
	my($self,$e,$l,$ndr,$env) = @_;
	my $switch_var = ParseExprExt($l->{SWITCH_IS}, $env, $e->{ORIGINAL},
		check_null_pointer($e, $env, sub { $self->pidl(shift); },
				   "return ndr_push_error($ndr, NDR_ERR_INVALID_POINTER, \"NULL Pointer for switch_is()\");"),
		check_fully_dereferenced($e, $env));

	$self->{next_switch_var} = $switch_var;
}

sub ParseDataPull($$$$$$$)
{
	my ($self,$e,$l,$ndr,$var_name,$primitives,$deferred) = @_;

	if (not ref($l->{DATA_TYPE}) or defined($l->{DATA_TYPE}->{NAME})) {

		my $scope = CalcNdrScope($l, $primitives, $deferred);

		if (need_pointer_to($e, $l, 0)) {
			$var_name = get_pointer_to($var_name);
		}

		my $type_name = $l->{DATA_TYPE};
		my $data_type = getType($type_name)->{DATA}->{TYPE};

        if ($data_type eq "STRUCT")
		{
			if ($scope eq "buffers") {
				$self->pidl("NdrStructTranslator<$type_name>::get_buffers($ndr, $var_name);");
			}
			else {
				$self->pidl("$var_name = NdrStructTranslator<$type_name>::get_$scope($ndr);");
			}
		}
		elsif ($data_type eq "UNION")
		{
			if ($scope eq "buffers") {
				$self->pidl("NdrUnionTranslator<$type_name>::get_buffers($ndr, $var_name, $self->{next_switch_var});");
			}
			else {
				$self->pidl("$var_name = NdrUnionTranslator<$type_name>::get_$scope($ndr, $self->{next_switch_var});");
			}
        }
        else {
			if ($type_name eq "DATA_BLOB") {
				if ($self->{scoped_flags} eq "NDR_REMAINING") {
					$self->pidl("$var_name = $ndr.get_remaining_blob();");
					$self->{remaining_blob} = 1;
				} else {
					assert_unssupported_element("DATA_BLOB with unsupported flags $self->{scoped_flags} - modify IDL by applying flags to the next field", $e) if $self->{scoped_flags};
					assert_unssupported_element("Standard DATA_BLOB", $e);
				}

				$self->{scoped_flags} = undef;
			} else {
    			$self->pidl("$var_name = $ndr.".TypeFunctionName("get", $type_name)."();");
			}
        }

		my $pl = GetPrevLevel($e, $l);

		my $range = has_property($e, "range");
		if ($range and $pl->{TYPE} ne "ARRAY") {
			# $var_name = get_value_of($var_name);
			my $signed = Parse::Pidl::Typelist::is_signed($l->{DATA_TYPE});
			my ($low, $high) = split(/,/, $range, 2);
			if ($low < 0 and not $signed) {
				warning(0, "$low is invalid for the range of an unsigned type");
			}
			if ($low == 0 and not $signed) {
				$self->pidl("NDR_CHECK($var_name <= $high, \"Value is too high\", $var_name);");
			} else {
				$self->pidl("NDR_CHECK($var_name >= $low && $var_name <= $high, \"Value is out of range\", $var_name);");
			}
		}
	} else {
		assert_unssupported_element("", $e);
		# $self->ParseTypePull($l->{DATA_TYPE}, $ndr, $var_name, $primitives, $deferred);
	}
}

sub ParseDataPush($$$$$$$)
{
	my ($self,$e,$l,$ndr,$var_name,$primitives,$deferred) = @_;

	if (not ref($l->{DATA_TYPE}) or defined($l->{DATA_TYPE}->{NAME})) {

		my $scope = CalcNdrScope($l, $primitives, $deferred);

		my $type_name = $l->{DATA_TYPE};
		die("Unknown type $type_name") unless (getType($type_name));

		my $data_type = getType($type_name)->{DATA}->{TYPE};

        if ($data_type eq "STRUCT")
		{
			$self->pidl("NdrStructTranslator<$type_name>::put_$scope($ndr, $var_name);");
		}
		elsif ($data_type eq "UNION")
		{
			$self->pidl("NdrUnionTranslator<$type_name>::put_$scope($ndr, $var_name, $self->{next_switch_var});");
        }
        else
        {
			if ($type_name eq "DATA_BLOB") {
				if ($self->{scoped_flags} eq "NDR_REMAINING") {
					$self->pidl("$ndr.put_remaining_blob($var_name);");
						$self->{remaining_blob} = 1;
				}
				else {
					assert_unssupported_element("DATA_BLOB with unsupported flags $self->{scoped_flags} - modify IDL by applying flags to the next field", $e) if $self->{scoped_flags};
					assert_unssupported_element("Standard DATA_BLOB", $e);
				}

				$self->{scoped_flags} = undef;
			} else {
    			$self->pidl("$ndr.".TypeFunctionName("put", $type_name)."($var_name);");
			}
        }
	} else {
		assert_unssupported_element("", $e);
		# $self->ParseTypePush($l->{DATA_TYPE}, $ndr, $var_name, $primitives, $deferred);
	}
}

sub CalcNdrScope($$$)
{
	my ($l,$primitives,$deferred) = @_;

	my $scalars = 0;
	my $buffers = 0;

	# Add NDR_SCALARS if this one is deferred
	# and deferreds may be pushed
	$scalars = 1 if ($l->{IS_DEFERRED} and $deferred);

	# Add NDR_SCALARS if this one is not deferred and
	# primitives may be pushed
	$scalars = 1 if (!$l->{IS_DEFERRED} and $primitives);

	# Add NDR_BUFFERS if this one contains deferred stuff
	# and deferreds may be pushed
	$buffers = 1 if ($l->{CONTAINS_DEFERRED} and $deferred);

	return "all" if ($scalars and $buffers);
	return "scalars" if ($scalars);
	return "buffers" if ($buffers);
	return undef;
}

sub CheckStringTerminator($$$$$)
{
	my ($self,$ndr,$e,$l,$length) = @_;
	my $nl = GetNextLevel($e, $l);

	# Make sure last element is zero!
	#slupu - ndr_check_string_terminator
	# $self->pidl("ndr_check_string_terminator($ndr, $length, sizeof($nl->{DATA_TYPE}_t));");
}

sub ParseElementPullLevel
{
	my($self,$e,$l,$ndr,$var_name,$env,$primitives,$deferred) = @_;

	my $scope = CalcNdrScope($l, $primitives, $deferred);
	my $array_length = undef;

	assert_unssupported_element("skip_noinit", $e) if (has_property($e, "skip_noinit"));

	if (has_property($e, "skip")) {
		$self->pidl("// [skip] '$var_name'");
		return;
	}

	if ($l->{TYPE} eq "ARRAY" and ($l->{IS_VARYING} or $l->{IS_CONFORMANT})) {
		$var_name = get_pointer_to($var_name);
	}

	# Only pull something if there's actually something to be pulled
	if (defined($scope)) {
		if ($l->{TYPE} eq "SUBCONTEXT") {
			my $subndr = $self->ParseSubcontextPullStart($e, $l, $ndr, $env);
			$self->ParseElementPullLevel($e, GetNextLevel($e,$l), $subndr, $var_name, $env, 1, 1);
			$self->ParseSubcontextPullEnd($e, $l, $ndr, $env);
		} elsif ($l->{TYPE} eq "ARRAY") {
			my $length = $self->ParseArrayPullHeader($e, $l, $ndr, $var_name, $env);
			$array_length = $length;

			my $nl = GetNextLevel($e, $l);

			if (is_charset_array($e,$l)) {
				if ($l->{IS_ZERO_TERMINATED}) {
					$self->CheckStringTerminator($ndr, $e, $l, $length);
				}

				assert_unssupported_element("to_null string", $e) if ($l->{IS_TO_NULL});

				my $string_params;
				if ((!$l->{IS_SURROUNDING}) and $l->{IS_CONFORMANT} and $l->{IS_VARYING}) {
					$string_params = "";
				} else {
					$string_params = "NdrStringParams::by_external_length($length)";
				}
				$self->pidl("$var_name = $ndr.get_string<StringEncodingType::$e->{PROPERTIES}->{charset}>($string_params);");
				return;
			} elsif (has_fast_array($e, $l)) {
				if ($l->{IS_ZERO_TERMINATED}) {
					$self->CheckStringTerminator($ndr,$e,$l,$length);
				}
				$self->pidl("ndr_pull_array_$nl->{DATA_TYPE}($ndr, $scope, $var_name, $length);");
				return;
			}
		} elsif ($l->{TYPE} eq "POINTER") {
			$self->ParsePtrPull($e, $l, $ndr, $var_name);
		} elsif ($l->{TYPE} eq "SWITCH") {
			$self->ParseSwitchPull($e, $l, $ndr, $var_name, $env);
		} elsif ($l->{TYPE} eq "DATA") {
			$self->ParseDataPull($e, $l, $ndr, $var_name, $primitives, $deferred);
		} elsif ($l->{TYPE} eq "TYPEDEF") {
			$typefamily{$e->{DATA}->{TYPE}}->{PULL_FN_BODY}->($self, $e->{DATA}, $ndr, $var_name);
		}
	}

	# add additional constructions
	if ($l->{TYPE} eq "POINTER" and $l->{POINTER_TYPE} eq "ignore") {
		$self->pidl("/* [ignore] '$e->{NAME}' */");
	} elsif ($l->{TYPE} eq "POINTER" and $deferred) {
		if ($l->{POINTER_TYPE} ne "ref") {
			$self->pidl("if ($var_name)");
			$self->start_block;
			my $nl = GetNextLevel($e, $l);
			my $next_is_array = ($nl->{TYPE} eq "ARRAY");
			my $next_is_string = (($nl->{TYPE} eq "DATA") and ($nl->{DATA_TYPE} eq "string"));
			if ($next_is_array or $next_is_string) {
				$self->pidl("ndr.validate_array_place_holder($var_name);");
			}

			if ($l->{POINTER_TYPE} eq "relative" or $l->{POINTER_TYPE} eq "relative_short") {
				$self->pidl("uint32_t _relative_save_offset;");
				$self->pidl("_relative_save_offset = $ndr->offset;");
				$self->pidl("ndr_pull_relative_ptr2($ndr, $var_name);");
			}
		}

		$var_name = get_value_of($var_name);
		$self->ParseElementPullLevel($e, GetNextLevel($e,$l), $ndr, $var_name, $env, 1, 1);

		if ($l->{POINTER_TYPE} ne "ref") {
			if ($l->{POINTER_TYPE} eq "relative" or $l->{POINTER_TYPE} eq "relative_short") {
				$self->pidl("if ($ndr->offset > $ndr->relative_highest_offset)");
				$self->start_block;
				$self->pidl("$ndr->relative_highest_offset = $ndr->offset;");
				$self->end_block;
				$self->pidl("$ndr->offset = _relative_save_offset;");
			}
			$self->end_block;
		}
	} elsif ($l->{TYPE} eq "ARRAY" and
			not has_fast_array($e,$l) and not is_charset_array($e, $l)) {
		my $length = $array_length;
		my $counter = "i";

		if (not defined($length)) {
			$length = $self->ParseArrayPullGetLength($e, $l, $ndr, $var_name, $env);
		}

		$var_name = get_array_element($var_name, $counter);

		if (($primitives and not $l->{IS_DEFERRED}) or ($deferred and $l->{IS_DEFERRED})) {
			my $nl = GetNextLevel($e,$l);

			if ($l->{IS_ZERO_TERMINATED}) {
				$self->CheckStringTerminator($ndr,$e,$l,$length);
			}

            $self->pidl();
			$self->pidl("for (uint32_t $counter = 0; $counter < $length; $counter++)");
			$self->start_block;
			$self->ParseElementPullLevel($e, $nl, $ndr, $var_name, $env, 1, 0);
			$self->end_block;
		}

		if ($deferred and ContainsDeferred($e, $l)) {
            $self->pidl();
			$self->pidl("for (uint32_t $counter = 0; $counter < $length; $counter++)");
			$self->start_block;
			$self->ParseElementPullLevel($e,GetNextLevel($e,$l), $ndr, $var_name, $env, 0, 1);
			$self->end_block;
		}

	} elsif ($l->{TYPE} eq "SWITCH") {
		$self->ParseElementPullLevel($e, GetNextLevel($e,$l), $ndr, $var_name, $env, $primitives, $deferred);
	}
}

#####################################################################
# parse scalars in a structure element - pull size
sub ParseElementPull($$$$$$)
{
	my($self,$e,$ndr,$env,$primitives,$deferred) = @_;

	my $var_name = $env->{$e->{NAME}};
	my $represent_name;
	my $transmit_name;

	return if ContainsPipe($e, $e->{LEVELS}[0]);

	return unless $primitives or ($deferred and ContainsDeferred($e, $e->{LEVELS}[0]));

	if ($e->{REPRESENTATION_TYPE} ne $e->{TYPE}) {
		$self->start_block;
		$represent_name = $var_name;
		$transmit_name = "_transmit_$e->{NAME}";
		$var_name = $transmit_name;
		$self->pidl(mapTypeName($e->{TYPE})." $var_name"."{};");
	}

	$var_name = append_prefix($e, $var_name);

	$self->start_flags($e, $ndr, 1);

	$self->ParseElementPullLevel($e,$e->{LEVELS}[0],$ndr,$var_name,$env,$primitives,$deferred);

	$self->end_flags($e);

	# Representation type is different from transmit_as
	if ($e->{REPRESENTATION_TYPE} ne $e->{TYPE}) {
		$self->pidl("ndr_$e->{TYPE}_to_$e->{REPRESENTATION_TYPE}($transmit_name, ".get_pointer_to($represent_name).");");
		$self->end_block;
	}
}

#####################################################################
# parse a pointer in a struct element or function
sub ParsePtrPull($$$$$)
{
	my($self, $e,$l,$ndr,$var_name) = @_;

	my $nl = GetNextLevel($e, $l);
	my $next_is_array = ($nl->{TYPE} eq "ARRAY");
	my $next_is_string = (($nl->{TYPE} eq "DATA") and
						 ($nl->{DATA_TYPE} eq "string"));


	if ($l->{POINTER_TYPE} eq "ref" and $l->{LEVEL} eq "TOP") {
		$self->pidl("$var_name = $ndr.alloc<decltype(*$var_name)>();") if (!$next_is_array and !$next_is_string);
		return;
	}

	if ($l->{POINTER_TYPE} eq "ignore") {
        $self->pidl("ndr.get_uint32_64(); // pointer ignored");
        $self->pidl("$var_name = nullptr;");
        return;
    }
    
    if ($l->{POINTER_TYPE} eq "ref" and $l->{LEVEL} eq "EMBEDDED") {
        assert_unssupported_element("Embedded ref pointer", $e);
	}

	if ($l->{POINTER_TYPE} eq "relative" or $l->{POINTER_TYPE} eq "relative_short") {
        assert_unssupported_element("relative pointer", $e);
	}

    if (($l->{POINTER_TYPE} eq "unique") or
		 ($l->{POINTER_TYPE} eq "relative") or
		 ($l->{POINTER_TYPE} eq "full"))
    {
        # Don't do this for arrays, they're allocated at the actual level of the array
        unless ($next_is_array or $next_is_string) {
            $self->pidl("$var_name = $ndr.get_ptr_ref_id() ? $ndr.alloc<decltype(*$var_name)>() : nullptr;");
        } else {
            $self->pidl("$var_name = $ndr.get_array_place_holder<decltype($var_name)>();");
        }
	}
    else
    {
        assert_unssupported_element("Unhandled pointer type $l->{POINTER_TYPE}", $e);
    }
}

sub CheckRefPtrs($$$$)
{
	my ($self,$e,$ndr,$env) = @_;

	return if ContainsPipe($e, $e->{LEVELS}[0]);
	return if ($e->{LEVELS}[0]->{TYPE} ne "POINTER");
	return if ($e->{LEVELS}[0]->{POINTER_TYPE} ne "ref");

	# Zero length conformant array may be null (easier for application), thus skipping null check
	return if ($e->{LEVELS}[1]->{IS_CONFORMANT});

	my $var_name = $env->{$e->{NAME}};
	$var_name = append_prefix($e, $var_name);

	$self->ParseCheck($ndr, $var_name, "NULL [ref] pointer");
}

sub ParseStructPushPrimitives($$$$$)
{
	my ($self, $struct, $ndr, $varname, $env) = @_;

	$self->CheckRefPtrs($_, $ndr, $env) foreach (@{$struct->{ELEMENTS}});

	# see if the structure contains a conformant array. If it
	# does, then it must be the last element of the structure, and
	# we need to push the conformant length early, as it fits on
	# the wire before the structure (and even before the structure
	# alignment)
	if (defined($struct->{SURROUNDING_ELEMENT})) {
		my $e = $struct->{SURROUNDING_ELEMENT};

		assert_unssupported_element("SURROUNDING_ELEMENT", $e);

		if (defined($e->{LEVELS}[0]) and
			$e->{LEVELS}[0]->{TYPE} eq "ARRAY") {
			my $size;

			if ($e->{LEVELS}[0]->{IS_ZERO_TERMINATED}) {
				if (has_property($e, "charset")) {
					$size = "ndr_charset_length($varname.$e->{NAME}, CH_$e->{PROPERTIES}->{charset})";
				} else {
					$size = "ndr_string_length($varname.$e->{NAME}, sizeof(*$varname.$e->{NAME}))";
				}
				if (defined($e->{LEVELS}[0]->{SIZE_IS})) {
					$size = ParseExpr($e->{LEVELS}[0]->{SIZE_IS}, $env, $e->{ORIGINAL});
				}
			} else {
				$size = ParseExpr($e->{LEVELS}[0]->{SIZE_IS}, $env, $e->{ORIGINAL});
			}

			$self->pidl("$ndr.put_array_size($size);");
		} else {
			$self->pidl("$ndr.put_uint32_64(ndr_string_array_size($ndr, $varname.$e->{NAME}));");
		}
	}

	$self->pidl(GetAlignmentStatement($ndr, $struct->{ALIGN}));

	if (defined($struct->{PROPERTIES}{relative_base})) {
		# set the current offset as base for relative pointers
		# and store it based on the toplevel struct/union
		$self->pidl("ndr_push_setup_relative_base_offset1($ndr, $varname, $ndr->offset);");
	}

	$self->ParseElementPush($_, $ndr, $env, 1, 0) foreach (@{$struct->{ELEMENTS}});

	$self->pidl("$ndr.trailer_align(".GetNDR64OnlyAlignment($struct->{ALIGN}).");") unless $self->{remaining_blob};
}

sub ParseStructPushDeferred($$$$)
{
	my ($self, $struct, $ndr, $varname, $env) = @_;
	if (defined($struct->{PROPERTIES}{relative_base})) {
		# retrieve the current offset as base for relative pointers
		# based on the toplevel struct/union
		$self->pidl("ndr_push_setup_relative_base_offset2($ndr, $varname);");
	}
	$self->ParseElementPush($_, $ndr, $env, 0, 1) foreach (@{$struct->{ELEMENTS}});
}

#####################################################################
# parse a struct
sub ParseStructPush($$$$$)
{
	my ($self, $struct, $ndr, $varname, $scope) = @_;

	return unless defined($struct->{ELEMENTS});

	my $env = GenerateStructEnv($struct, $varname);

	EnvSubstituteValue($env, $struct);

	$self->start_flags($struct, $ndr, 0);

	$self->ParseStructPushPrimitives($struct, $ndr, $varname, $env) if ($scope eq "scalars");
	$self->ParseStructPushDeferred($struct, $ndr, $varname, $env)  if ($scope eq "buffers");
}

#####################################################################

sub DeclEnum($$$)
{
	my ($e,$t,$name) = @_;
	return $name;
}

$typefamily{ENUM} = {
	DECL => \&DeclEnum,
};

sub DeclBitmap($$$)
{
	my ($e,$t,$name) = @_;
	return mapTypeName(Parse::Pidl::Typelist::bitmap_type_fn($e));
}

$typefamily{BITMAP} = {
	DECL => \&DeclBitmap,
};

#####################################################################

sub ParseStructPullPrimitives($$$$$)
{
	my($self,$struct,$ndr,$varname,$env) = @_;

	if (defined $struct->{SURROUNDING_ELEMENT}) {
        my $e = $struct->{SURROUNDING_ELEMENT};
        my $array_size_var = "size_$e->{NAME}";
        $self->pidl("const uint32_t $array_size_var = $ndr.get_array_size();");
	}

	$self->pidl(GetAlignmentStatement($ndr, $struct->{ALIGN}));;

	if (defined($struct->{PROPERTIES}{relative_base})) {
		# set the current offset as base for relative pointers
		# and store it based on the toplevel struct/union
		$self->pidl("ndr_pull_setup_relative_base_offset1($ndr, $varname, $ndr->offset);");
	}

	$self->ParseElementPull($_, $ndr, $env, 1, 0) foreach (@{$struct->{ELEMENTS}});

	$self->add_deferred();

	$self->pidl("$ndr.trailer_align(".GetNDR64OnlyAlignment($struct->{ALIGN}).");") unless $self->{remaining_blob};
}

sub ParseStructPullDeferred($$$$$)
{
	my ($self,$struct,$ndr,$varname,$env) = @_;

	if (defined($struct->{PROPERTIES}{relative_base})) {
		# retrieve the current offset as base for relative pointers
		# based on the toplevel struct/union
		$self->pidl("ndr_pull_setup_relative_base_offset2($ndr, $varname);");
	}
	foreach my $e (@{$struct->{ELEMENTS}}) {
		$self->ParseElementPull($e, $ndr, $env, 0, 1);
	}

	$self->add_deferred();
}

#####################################################################
# parse a struct - pull side
sub ParseStructPull($$$$$)
{
	my($self,$struct,$ndr,$varname, $scope) = @_;

	return unless defined $struct->{ELEMENTS};

	$self->start_flags($struct, $ndr, 0);

	my $env = GenerateStructEnv($struct, $varname);

	$self->ParseStructPullPrimitives($struct,$ndr,$varname,$env) if ($scope eq "scalars");
	$self->ParseStructPullDeferred($struct,$ndr,$varname,$env) if ($scope eq "buffers");
}

#####################################################################
# calculate size of ndr struct
sub ParseStructNdrSize($$$$)
{
	my ($self,$t, $name, $varname) = @_;
	my $sizevar;

	if (my $flags = has_property($t, "flag")) {
		$self->pidl("flags |= $flags;");
	}
	$self->pidl("return ndr_size_struct($varname, flags, (ndr_push_flags_fn_t)ndr_push_$name);");
}

sub DeclStruct($$$)
{
	my ($e,$t,$name) = @_;
	return $name;
}

sub ArgsStructNdrSize($$)
{
	my ($d, $name) = @_;
	return $name;
}

$typefamily{STRUCT} = {
	PUSH_FN_BODY => \&ParseStructPush,
	DECL => \&DeclStruct,
	PULL_FN_BODY => \&ParseStructPull,
	SIZE_FN_BODY => \&ParseStructNdrSize,
	SIZE_FN_ARGS => \&ArgsStructNdrSize,
};

#####################################################################
# calculate size of ndr struct
sub ParseUnionNdrSize($$$)
{
	my ($self, $t, $name, $varname) = @_;
	my $sizevar;

	if (my $flags = has_property($t, "flag")) {
		$self->pidl("flags |= $flags;");
	}

	$self->pidl("return ndr_size_union($varname, flags, level, (ndr_push_flags_fn_t)ndr_push_$name);");
}

sub ParseUnionPushPrimitives($$$$)
{
	my ($self, $e, $ndr ,$varname) = @_;

	my $have_default = 0;

	if (!has_property($e, "nodiscriminant"))
	{
		if (defined($e->{ALIGN})) {
			$self->pidl("$ndr.union_align(".GetNDR64OnlyAlignment($e->{ALIGN}).");");
		}

		$self->pidl("$ndr.put<".mapTypeName($e->{SWITCH_TYPE}).">(switch_value);");
	}

	if (defined($e->{ALIGN})) {
		if ($e->{IS_MS_UNION}) {
			$self->pidl("/* ms_union is always aligned to the largest union arm*/");
			$self->pidl(GetAlignmentStatement($ndr, $e->{ALIGN}));
		} else {
			$self->pidl("$ndr.union_align(".GetNDR64OnlyAlignment($e->{ALIGN}).");");
		}
	}

    $self->pidl();
	$self->pidl("switch (switch_value)");
	$self->pidl("{");
	foreach my $el (@{$e->{ELEMENTS}}) {
		if ($el->{CASE} eq "default") {
			$have_default = 1;
		}
		$self->pidl("$el->{CASE}:");
        $self->start_block();

		if ($el->{TYPE} ne "EMPTY")
		{
			if (defined($e->{PROPERTIES}{relative_base})) {
				$self->pidl(GetAlignmentStatement($ndr, $e->{ALIGN}));
				# set the current offset as base for relative pointers
				# and store it based on the toplevel struct/union
				$self->pidl("ndr_push_setup_relative_base_offset1($ndr, $varname, $ndr->offset);");
			}

			my $el_env = {$el->{NAME} => "$varname.$el->{NAME}"};
			$self->CheckRefPtrs($el, $ndr, $el_env);
			$self->ParseElementPush($el, $ndr, $el_env, 1, 0);
		}

		$self->pidl("break;");
		$self->end_block(0);
	}
	if (! $have_default) {
		$self->pidl("default:");
        $self->indent;
		$self->pidl("NDR_CHECK(false, \"Bad switch value\", switch_value);");
        $self->deindent;
	}
	$self->pidl("}");
}

sub ParseUnionPushDeferred($$$$)
{
	my ($self,$e,$ndr,$varname) = @_;

	my $have_default = 0;

	if (defined($e->{PROPERTIES}{relative_base})) {
		# retrieve the current offset as base for relative pointers
		# based on the toplevel struct/union
		$self->pidl("ndr_push_setup_relative_base_offset2($ndr, $varname);");
	}

    $self->pidl();
	$self->pidl("switch (switch_value)");
	$self->pidl("{");
	foreach my $el (@{$e->{ELEMENTS}}) {
		if ($el->{CASE} eq "default") {
			$have_default = 1;
		}

		$self->pidl("$el->{CASE}:");
		$self->start_block();
		if ($el->{TYPE} ne "EMPTY") {
			$self->ParseElementPush($el, $ndr, {$el->{NAME} => "$varname.$el->{NAME}"}, 0, 1);
		}
		$self->pidl("break;");
        $self->end_block(0);
	}
	if (! $have_default) {
		$self->pidl("default:");
        $self->indent;
		$self->pidl("NDR_CHECK(false, \"Bad switch value\", switch_value);");
        $self->deindent;
	}
	$self->pidl("}");
}

#####################################################################
# parse a union - push side
sub ParseUnionPush($$$$$)
{
	my ($self,$e,$ndr,$varname, $scope) = @_;

	$self->start_flags($e, $ndr, 0);

	$self->ParseUnionPushPrimitives($e, $ndr, $varname) if ($scope eq "scalars");
	$self->ParseUnionPushDeferred($e, $ndr, $varname) if (is_deferred_switch_non_empty($e) and $scope eq "buffers");
}

#####################################################################

sub ParseCheck
{
	my ($self,$ndr,$expr,$msg,@args) = @_;
	my $args_str = "";
	$args_str .= ", $_" for (@args);

	$self->pidl("NDR_CHECK($expr, \"$msg\""."$args_str);");
}

sub ParseUnionPullPrimitives($$$$$)
{
	my ($self,$e,$ndr,$varname,$switch_type) = @_;
	my $have_default = 0;

	if (!has_property($e, "nodiscriminant"))
	{
		if (defined($e->{ALIGN})) {
			$self->pidl("$ndr.union_align(".GetNDR64OnlyAlignment($e->{ALIGN}).");");
		}

		$self->pidl("$ndr.get_compare_switch_value(switch_value);");
	}

	if (defined($e->{ALIGN})) {
		if ($e->{IS_MS_UNION}) {
			$self->pidl("/* ms_union is always aligned to the largest union arm*/");
			$self->pidl(GetAlignmentStatement($ndr, $e->{ALIGN}));
		} else {
			$self->pidl("$ndr.union_align(".GetNDR64OnlyAlignment($e->{ALIGN}).");");
		}
	}

    $self->pidl();
	$self->pidl("switch (switch_value)");
	$self->pidl("{");
	foreach my $el (@{$e->{ELEMENTS}}) {
		if ($el->{CASE} eq "default") {
			$have_default = 1;
		}
		$self->pidl("$el->{CASE}:");
        $self->start_block();

		if ($el->{TYPE} ne "EMPTY") {
			if (defined($e->{PROPERTIES}{relative_base})) {
				$self->pidl(GetAlignmentStatement($ndr, $el->{ALIGN}));
				# set the current offset as base for relative pointers
				# and store it based on the toplevel struct/union
				$self->pidl("ndr_pull_setup_relative_base_offset1($ndr, $varname, $ndr->offset);");
			}
			$self->ParseElementPull($el, $ndr, {$el->{NAME} => "$varname.$el->{NAME}"}, 1, 0);
		}
		$self->pidl("break;");
        $self->end_block(0);
	}
	if (! $have_default) {
		$self->pidl("default:");
        $self->indent;
		$self->pidl("NDR_CHECK(false, \"Bad switch value\", switch_value);");
        $self->deindent;
	}
	$self->pidl("}");
}

sub ParseUnionPullDeferred($$$$)
{
	my ($self,$e,$ndr,$varname) = @_;
	my $have_default = 0;

	if (defined($e->{PROPERTIES}{relative_base})) {
		# retrieve the current offset as base for relative pointers
		# based on the toplevel struct/union
		$self->pidl("ndr_pull_setup_relative_base_offset2($ndr, $varname);");
	}
    $self->pidl();
	$self->pidl("switch (switch_value)");
	$self->pidl("{");
	foreach my $el (@{$e->{ELEMENTS}}) {
		if ($el->{CASE} eq "default") {
			$have_default = 1;
		}

		$self->pidl("$el->{CASE}:");
		$self->start_block();

		if ($el->{TYPE} ne "EMPTY") {
			$self->ParseElementPull($el, $ndr, {$el->{NAME} => "$varname.$el->{NAME}"}, 0, 1);
		}
		$self->pidl("break;");
        $self->end_block(0);
	}
	if (! $have_default) {
		$self->pidl("default:");
        $self->indent;
		$self->pidl("NDR_CHECK(false, \"Bad switch value\", switch_value);");
        $self->deindent;
	}
	$self->pidl("}");


}

#####################################################################
# parse a union - pull side
sub ParseUnionPull($$$$$)
{
	my ($self,$e,$ndr,$varname, $scope) = @_;
	my $switch_type = $e->{SWITCH_TYPE};
	my $needs_deferred_switch = is_deferred_switch_non_empty($e);

	$self->start_flags($e, $ndr, 0);

	$self->ParseUnionPullPrimitives($e,$ndr,$varname,$switch_type) if ($scope eq "scalars");
	$self->ParseUnionPullDeferred($e,$ndr,$varname) if ($needs_deferred_switch and $scope eq "buffers");

	$self->add_deferred();
}

sub DeclUnion($$$$)
{
	my ($e,$t,$name) = @_;
	return $name;
}

sub ArgsUnionNdrSize($$)
{
	my ($d,$name) = @_;
	return "const union $name *r, uint32_t level, int flags";
}

$typefamily{UNION} = {
	PUSH_FN_BODY => \&ParseUnionPush,
	DECL => \&DeclUnion,
	PULL_FN_BODY => \&ParseUnionPull,
	SIZE_FN_ARGS => \&ArgsUnionNdrSize,
	SIZE_FN_BODY => \&ParseUnionNdrSize,
};

#####################################################################
# parse a typedef - push side
sub ParseTypedefPush($$$$)
{
	my($self,$e,$ndr,$varname, $scope) = @_;

	my $env;

	$env->{$e->{NAME}} = $varname;
	my $underlying_type = $e->{DATA};

	$typefamily{$underlying_type->{TYPE}}->{PUSH_FN_BODY}->($self, $underlying_type, $ndr, $varname, $scope);
}

#####################################################################
# parse a typedef - pull side
sub ParseTypedefPull($$$$$)
{
	my($self,$e,$ndr,$varname, $scope) = @_;

	my $env;

	$env->{$e->{NAME}} = $varname;
	my $underlying_type = $e->{DATA};

	$typefamily{$underlying_type->{TYPE}}->{PULL_FN_BODY}->($self, $underlying_type, $ndr, $varname, $scope);
}

#####################################################################
## calculate the size of a structure
sub ParseTypedefNdrSize($$$)
{
	my($self,$t,$name) = @_;

	$typefamily{$t->{DATA}->{TYPE}}->{SIZE_FN_BODY}->($self, $t->{DATA}, $name);
}

sub DeclTypedef($$$)
{
	my ($e, $t, $name) = @_;

	return $typefamily{$e->{DATA}->{TYPE}}->{DECL}->($e->{DATA}, $t, $name);
}

sub ArgsTypedefNdrSize($$)
{
	my ($d, $name) = @_;
	return $typefamily{$d->{DATA}->{TYPE}}->{SIZE_FN_ARGS}->($d->{DATA}, $name);
}

$typefamily{TYPEDEF} = {
	PUSH_FN_BODY => \&ParseTypedefPush,
	DECL => \&DeclTypedef,
	PULL_FN_BODY => \&ParseTypedefPull,
	SIZE_FN_ARGS => \&ArgsTypedefNdrSize,
	SIZE_FN_BODY => \&ParseTypedefNdrSize,
};

sub ParsePipePushChunk($$)
{
	my ($self, $t) = @_;

	my $pipe = $t;
	$pipe = $t->{DATA} if ($t->{TYPE} eq "TYPEDEF");
	my $struct = $pipe->{DATA};

	my $name = "$struct->{NAME}";
	my $ndr = "ndr";
	my $varname = "r";

	my $args = $typefamily{$struct->{TYPE}}->{DECL}->($struct, "put", $name, $varname);

	$self->fn_declare("put", $struct, "void ndr_push_$name(NdrWriter& $ndr, int ndr_flags, $args)") or return;

	return if has_property($t, "nopush");

	$self->start_function;

	$self->ParseStructPush($struct, $ndr, $varname);
	$self->pidl("");

	$self->pidl("ndr_push_pipe_chunk_trailer(ndr, ndr_flags, $varname.count);");
	$self->pidl("");

	$self->end_function;
}

sub ParsePipePullChunk($$)
{
	my ($self, $t) = @_;

	my $pipe = $t;
	$pipe = $t->{DATA} if ($t->{TYPE} eq "TYPEDEF");
	my $struct = $pipe->{DATA};

	my $name = "$struct->{NAME}";
	my $ndr = "ndr";
	my $varname = "r";

	my $args = $typefamily{$struct->{TYPE}}->{DECL}->($struct, "get", $name, $varname);

	$self->fn_declare("get", $struct, "void ndr_pull_$name(NdrReader& $ndr, int ndr_flags, $args)") or return;

	return if has_property($struct, "nopull");

	$self->start_function;

	$self->ParseStructPull($struct, $ndr, $varname);
	$self->pidl("");

	$self->pidl("ndr_check_pipe_chunk_trailer($ndr, ndr_flags, $varname.count);");
	$self->pidl("");

	$self->end_function;
}

#####################################################################
# parse a function
sub ParseFunctionsPush($$)
{
	my($self, $fn) = @_;

	return if has_property($fn, "nopush");

	if ($self->{gen_client_functions}) {
		$self->ParseFunctionPushIn($fn);
	}

	$self->ParseFunctionPushOut($fn);
}

sub ParseFunctionPushIn($$)
{
	my($self, $fn) = @_;
	my $ndr = "ndr";

	$self->fn_declare("put", $fn, "template<>\nvoid NdrOpTranslator<$fn->{NAME}>::put_input([[maybe_unused]] NdrWriter& $ndr, [[maybe_unused]] const $fn->{NAME}::In& in)") or return;
	$self->start_function;

	my $env = GenerateFunctionInEnv($fn);

	EnvSubstituteValue($env, $fn);

	foreach my $e (@{$fn->{ELEMENTS}}) {
		if (grep(/in/,@{$e->{DIRECTION}})) {
			$self->CheckRefPtrs($e, $ndr, $env);
		}
	}

	foreach my $e (@{$fn->{ELEMENTS}}) {
		if (grep(/in/,@{$e->{DIRECTION}})) {
			$self->ParseElementPush($e, $ndr, $env, 1, 1);
		}
	}

	$self->end_function;
}

sub ParseFunctionPushOut($$)
{
	my($self, $fn) = @_;
	my $ndr = "ndr";

	$self->fn_declare("put", $fn, "template<>\nvoid NdrOpTranslator<$fn->{NAME}>::put_output(".
		"[[maybe_unused]] NdrWriter& $ndr, [[maybe_unused]] const $fn->{NAME}::Out& out, [[maybe_unused]] const $fn->{NAME}::In& in)") or return;
	$self->start_function;

	my $env = GenerateFunctionOutEnv($fn);
	EnvSubstituteValue($env, $fn);

	foreach my $e (@{$fn->{ELEMENTS}}) {
		if (grep(/out/,@{$e->{DIRECTION}})) {
			$self->CheckRefPtrs($e, $ndr, $env);
		}
	}

	foreach my $e (@{$fn->{ELEMENTS}}) {
		if (grep(/out/,@{$e->{DIRECTION}})) {
			$self->ParseElementPush($e, $ndr, $env, 1, 1);
		}
	}

	if ($fn->{RETURN_TYPE}) {
		$self->pidl("$ndr.".TypeFunctionName("put", $fn->{RETURN_TYPE})."(out.result);");
	}

	$self->end_function;
}

sub AllocateArrayLevel($$$$$$)
{
	my ($self,$e,$l,$ndr,$var,$size) = @_;

	my $pl = GetPrevLevel($e, $l);
	if (defined($pl) and
	    $pl->{TYPE} eq "POINTER" and
	    $pl->{POINTER_TYPE} eq "ref"
	    and not $l->{IS_ZERO_TERMINATED}) {
		$self->pidl("$var = $ndr.alloc_array<decltype(*$var)>($size);");
		return;
	}

	$self->pidl("$var = $ndr.alloc_array<decltype(*$var)>($size);");
}

#####################################################################
# parse a function
sub ParseFunctionsPull($$)
{
	my($self, $fn) = @_;

	$self->ParseFunctionPullIn($fn);

	if ($self->{gen_client_functions}) {
		$self->ParseFunctionPullOut($fn);
	}
}

sub ParseFunctionPullIn($$)
{
	my($self, $fn) = @_;
	my $ndr = "ndr";

	$self->fn_declare("get", $fn, "template<>\n"."$fn->{NAME}::In NdrOpTranslator<$fn->{NAME}>::get_input([[maybe_unused]] NdrReader& $ndr)") or return;
	$self->start_function;
	$self->pidl("$fn->{NAME}::In in"."{};");
	$self->pidl;

	# auto-init the out section of a structure. I originally argued that
	# this was a bad idea as it hides bugs, but coping correctly
	# with initialisation and not wiping ref vars is turning
	# out to be too tricky (tridge)
	foreach my $e (@{$fn->{ELEMENTS}}) {
		next unless grep (/out/, @{$e->{DIRECTION}});
		$self->pidl("");
		last;
	}

	my $env = GenerateFunctionInEnv($fn);

	foreach my $e (@{$fn->{ELEMENTS}}) {
		next unless (grep (/in/, @{$e->{DIRECTION}}));
		$self->ParseElementPull($e, $ndr, $env, 1, 1);
	}

	$self->add_deferred();

	$self->pidl("return in;");
	$self->end_function;
}

sub ParseFunctionPullOut($$)
{
	my($self, $fn) = @_;
	my $ndr = "ndr";

	$self->fn_declare("get", $fn, "template<>\n"."$fn->{NAME}::Out NdrOpTranslator<$fn->{NAME}>::get_output([[maybe_unused]] NdrReader& $ndr, [[maybe_unused]] const $fn->{NAME}::In& in)") or return;
	$self->start_function;
	$self->pidl("$fn->{NAME}::Out out"."{};");
	$self->pidl;

	my $env = GenerateFunctionOutEnv($fn);
	foreach my $e (@{$fn->{ELEMENTS}}) {
		next unless grep (/out/, @{$e->{DIRECTION}});
		$self->ParseElementPull($e, $ndr, $env, 1, 1);
	}

	if ($fn->{RETURN_TYPE}) {
		$self->pidl("out.result = $ndr.".TypeFunctionName("get", $fn->{RETURN_TYPE})."();");
	}

	$self->add_deferred();

	$self->pidl("return out;");
	$self->end_function;
}

sub AuthServiceStruct($$$)
{
	my ($self, $ifacename, $authservice) = @_;
	my @a = split /,/, $authservice;
	my $authservice_count = $#a + 1;

	$self->pidl("static const char * const $ifacename\_authservice_strings[] =");
    $self->start_block;
	foreach my $ap (@a) {
		$self->pidl("$ap, ");
	}
    $self->end_struct;

	$self->pidl("static const struct ndr_interface_string_array $ifacename\_authservices =");
    $self->start_block;
	$self->pidl(".count = $authservice_count,");
	$self->pidl(".names = $ifacename\_authservice_strings");
    $self->end_struct;
}

sub ParseGeneratePipeArray($$$)
{
	my ($self, $fn, $direction) = @_;

	$self->pidl("static const struct ndr_interface_call_pipe $fn->{NAME}\_$direction\_pipes[] =");
	$self->start_block;

	foreach my $e (@{$fn->{ELEMENTS}}) {
		next unless ContainsPipe($e, $e->{LEVELS}[0]);
		next unless (grep(/$direction/, @{$e->{DIRECTION}}));

		my $cname = "$e->{TYPE}_chunk";

		$self->start_block;
		$self->pidl("\"$direction.$e->{NAME}\",");
		$self->pidl("\"$cname\",");
		$self->pidl("sizeof(struct $cname),");
		$self->pidl("(ndr_push_flags_fn_t) ndr_push_$cname,");
		$self->pidl("(ndr_pull_flags_fn_t) ndr_pull_$cname,");
		$self->deindent;
		$self->pidl("},");
	}
	$self->pidl("{ .name = nullptr }");
	$self->end_struct;
}

sub FunctionCallPipes($$)
{
	my ($self, $d) = @_;
	return if not defined($d->{OPNUM});

	my $in_pipes = 0;
	my $out_pipes = 0;

	foreach my $e (@{$d->{ELEMENTS}}) {
		next unless ContainsPipe($e, $e->{LEVELS}[0]);

		if (grep(/in/, @{$e->{DIRECTION}})) {
			$in_pipes++;
		}
		if (grep(/out/, @{$e->{DIRECTION}})) {
			$out_pipes++;
		}
	}

	if ($in_pipes) {
		$self->ParseGeneratePipeArray($d, "in");
	}

	if ($out_pipes) {
		$self->ParseGeneratePipeArray($d, "out");
	}
}

sub FunctionCallEntry($$)
{
	my ($self, $d) = @_;
	return 0 if not defined($d->{OPNUM});

	my $in_pipes = 0;
	my $out_pipes = 0;

	foreach my $e (@{$d->{ELEMENTS}}) {
		next unless ContainsPipe($e, $e->{LEVELS}[0]);

		if (grep(/in/, @{$e->{DIRECTION}})) {
			$in_pipes++;
		}
		if (grep(/out/, @{$e->{DIRECTION}})) {
			$out_pipes++;
		}
	}

	my $in_pipes_ptr = "nullptr";
	my $out_pipes_ptr = "nullptr";

	if ($in_pipes) {
		$in_pipes_ptr = "$d->{NAME}_in_pipes";
	}

	if ($out_pipes) {
		$out_pipes_ptr = "$d->{NAME}_out_pipes";
	}

	$self->start_block;
	$self->pidl("\"$d->{NAME}\",");
	$self->pidl("sizeof(struct $d->{NAME}),");
	$self->pidl("(ndr_push_flags_fn_t) ndr_push_$d->{NAME},");
	$self->pidl("(ndr_pull_flags_fn_t) ndr_pull_$d->{NAME},");
	$self->pidl("{ $in_pipes, $in_pipes_ptr },");
	$self->pidl("{ $out_pipes, $out_pipes_ptr },");
    $self->deindent;
	$self->pidl("},");
	return 1;
}

#####################################################################
# produce a function call table
sub FunctionTable($$)
{
	my($self,$interface) = @_;
	my $count = 0;
	my $uname = uc $interface->{NAME};

	return if ($#{$interface->{FUNCTIONS}}+1 == 0);
	return unless defined ($interface->{PROPERTIES}->{uuid});

	foreach my $d (@{$interface->{INHERITED_FUNCTIONS}},@{$interface->{FUNCTIONS}}) {
		$self->FunctionCallPipes($d);
	}

	$self->pidl("static const struct ndr_interface_call $interface->{NAME}\_calls[] =");
    $self->start_block;

	foreach my $d (@{$interface->{INHERITED_FUNCTIONS}},@{$interface->{FUNCTIONS}}) {
		$count += $self->FunctionCallEntry($d);
	}
	$self->pidl("{ .name = nullptr }");
	$self->end_struct;

	$self->pidl("static const char * const $interface->{NAME}\_endpoint_strings[] =");
    $self->start_block;
    foreach my $ep (@{$interface->{ENDPOINTS}}) {
		$self->pidl("$ep, ");
	}
	my $endpoint_count = $#{$interface->{ENDPOINTS}}+1;

	$self->end_struct;

	$self->pidl("static const struct ndr_interface_string_array $interface->{NAME}\_endpoints =");
    $self->start_block;
	$self->pidl(".count = $endpoint_count,");
	$self->pidl(".names = $interface->{NAME}\_endpoint_strings");
	$self->end_struct;

	if (! defined $interface->{PROPERTIES}->{authservice}) {
		$interface->{PROPERTIES}->{authservice} = "\"host\"";
	}

	$self->AuthServiceStruct($interface->{NAME},
		                     $interface->{PROPERTIES}->{authservice});

	$self->pidl("\nconst struct ndr_interface_table ndr_table_$interface->{NAME} =");
    $self->start_block;
	$self->pidl(".name = \"$interface->{NAME}\",");
	$self->pidl(".syntax_id = {");
	$self->pidl(print_uuid($interface->{UUID}) .",");
    $self->indent;
	$self->pidl($interface->{VERSION});
    $self->deindent;
	$self->pidl("},");
	$self->pidl(".helpstring = " . $interface->{PROPERTIES}->{helpstring} . ",");
	$self->pidl(".num_calls = $count,");
	$self->pidl(".calls = $interface->{NAME}\_calls,");
	$self->pidl(".endpoints = &$interface->{NAME}\_endpoints,");
	$self->pidl(".authservices = &$interface->{NAME}\_authservices");
    $self->end_struct;

}

#####################################################################
# generate prototypes and defines for the interface definitions
# FIXME: these prototypes are for the DCE/RPC client functions, not the
# NDR parser and so do not belong here, technically speaking
sub HeaderInterface($$$)
{
	my($self,$interface,$needed) = @_;

	my $count = 0;

	if ($needed->{"compression"}) {
		$self->pidl(choose_header("librpc/dce_rpc/ndr/ndr_compression.h", "dce_rpc/ndr/compression.h"));
	}

	if (has_property($interface, "object")) {
		$self->pidl(choose_header("librpc/gen_dce_rpc/ndr/ndr_orpc.h", "dce_rpc/ndr/orpc.h"));
	}

	foreach (@{$interface->{FUNCTIONS}}) {
		next if has_property($_, "noopnum");
		next if grep(/^$_->{NAME}$/,@{$interface->{INHERITED_FUNCTIONS}});
		my $u_name = uc $_->{NAME};

		my $val = sprintf("0x%02x", $count);
		if (defined($interface->{BASE})) {
			$val .= " + NDR_" . uc $interface->{BASE} . "_CALL_COUNT";
		}

		$count++;
	}

	my $val = $count;

	if (defined($interface->{BASE})) {
		$val .= " + NDR_" . uc $interface->{BASE} . "_CALL_COUNT";
	}
}

sub ParseTypePush($$$$$)
{
	my ($self,$e, $ndr, $varname, $scope) = @_;

	# save the old relative_base_offset
	$self->pidl("uint32_t _save_relative_base_offset = ndr_push_get_relative_base_offset($ndr);") if defined(has_property($e, "relative_base"));
	$typefamily{$e->{TYPE}}->{PUSH_FN_BODY}->($self, $e, $ndr, $varname, $scope);
	# restore the old relative_base_offset
	$self->pidl("ndr_push_restore_relative_base_offset($ndr, _save_relative_base_offset);") if defined(has_property($e, "relative_base"));
}

sub ParseTypePushFunction($$$)
{
	my ($self, $e, $varname) = @_;
	my $ndr = "ndr";

	my $type_name = $e->{NAME};
	my $data_type = ($e->{DATA}->{TYPE});

	for my $scope ("scalars", "buffers") {
		if ($data_type eq "STRUCT") {
			$self->fn_declare("put", $e, "template<>\n" . "void NdrStructTranslator<$type_name>::put_$scope" .
				"([[maybe_unused]] NdrWriter& $ndr, [[maybe_unused]] const $type_name& $varname)") or return;
		}
		elsif ($data_type eq "UNION") {
			my $switch_type = mapTypeName($e->{DATA}->{SWITCH_TYPE});

			$self->fn_declare("put", $e, "template<>\n" . "void NdrUnionTranslator<$type_name>::put_$scope" .
				"([[maybe_unused]] NdrWriter& $ndr, [[maybe_unused]] const $type_name& $varname, [[maybe_unused]] $switch_type switch_value)") or return;
		}
		else {
			next;
		}

		$self->start_function;
		$self->ParseTypePush($e, $ndr, $varname, $scope);
		$self->end_function;
	}
}

sub ParseTypePull($$$$$)
{
	my ($self, $e, $ndr, $varname, $scope) = @_;

	# save the old relative_base_offset
	$self->pidl("uint32_t _save_relative_base_offset = ndr_pull_get_relative_base_offset($ndr);") if defined(has_property($e, "relative_base"));
	$typefamily{$e->{TYPE}}->{PULL_FN_BODY}->($self, $e, $ndr, $varname, $scope);
	# restore the old relative_base_offset
	$self->pidl("ndr_pull_restore_relative_base_offset($ndr, _save_relative_base_offset);") if defined(has_property($e, "relative_base"));
}

sub ParseTypePullFunction($$)
{
	my ($self, $e, $varname) = @_;
	my $ndr = "ndr";

	my $type_name = $e->{NAME};
	my $data_type = ($e->{DATA}->{TYPE});

	for my $scope ("scalars", "buffers") {
		my $obj_arg = ($scope eq "scalars") ? "" : ", [[maybe_unused]] $type_name& $varname";
		my $return_value = ($scope eq "scalars") ? $type_name : "void";

		if ($data_type eq "STRUCT") {
			$self->fn_declare("get", $e, "template<>\n" . "$return_value NdrStructTranslator<$type_name>::get_$scope" .
				"([[maybe_unused]] NdrReader& $ndr".$obj_arg.")") or return;
		}
		elsif ($data_type eq "UNION") {
			my $switch_type = mapTypeName($e->{DATA}->{SWITCH_TYPE});

			$self->fn_declare("get", $e, "template<>\n" . "$return_value NdrUnionTranslator<$type_name>::get_$scope" .
				"([[maybe_unused]] NdrReader& $ndr".$obj_arg.", [[maybe_unused]] $switch_type switch_value)") or return;
		}
		else {
			next;
		}

		$self->start_function;
		$self->pidl("$type_name $varname" . "{};") if ($scope eq "scalars");
		$self->ParseTypePull($e, $ndr, $varname, $scope);
		$self->pidl("return $varname;") if ($scope eq "scalars");
		$self->end_function;
	}
}

sub ParseTypeNdrSize($$)
{
	my ($self,$t) = @_;

	my $varname = "r";
	my $tf = $typefamily{$t->{TYPE}};
	my $args = $tf->{SIZE_FN_ARGS}->($t, $t->{NAME}, $varname);

	$self->fn_declare("size", $t, "size_t ndr_size_$t->{NAME}($args)") or return;

	$self->start_function;
	$typefamily{$t->{TYPE}}->{SIZE_FN_BODY}->($self,$t, $t->{NAME}, $varname);
	$self->end_function;
}

#####################################################################
# parse the interface definitions
sub ParseInterface($$$)
{
	my($self,$interface,$needed) = @_;

	$self->HeaderInterface($interface, $needed);

	# Typedefs
	foreach my $d (@{$interface->{TYPES}}) {
		if (Parse::Pidl::Typelist::typeIs($d, "PIPE")) {
			($needed->{TypeFunctionName("put", $d)}) &&
				$self->ParsePipePushChunk($d);
			($needed->{TypeFunctionName("get", $d)}) &&
				$self->ParsePipePullChunk($d);

			$needed->{TypeFunctionName("get", $d)} = 0;
			$needed->{TypeFunctionName("put", $d)} = 0;
			next;
		}

		next unless(typeHasBody($d));

		($needed->{TypeFunctionName("get", $d)}) && $self->ParseTypePullFunction($d, "r");
		($needed->{TypeFunctionName("put", $d)}) && $self->ParseTypePushFunction($d, "r");

		# Make sure we don't generate a function twice...
		$needed->{TypeFunctionName("put", $d)} = 
		    $needed->{TypeFunctionName("get", $d)} = 0;

#		($needed->{"ndr_size_$d->{NAME}"}) && $self->ParseTypeNdrSize($d);
	}

	# Functions
	foreach my $d (@{$interface->{FUNCTIONS}}) {
		($needed->{"ndr_pull_$d->{NAME}"}) && $self->ParseFunctionsPull($d);
		($needed->{"ndr_push_$d->{NAME}"}) && $self->ParseFunctionsPush($d);
	}

	# $self->FunctionTable($interface);
}

sub GenerateIncludes($)
{
	my ($self) = @_;
	if (is_intree()) {
		$self->pidl("#include \"includes.h\"");
	} else {
		$self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_common.hpp\"");
		$self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_reader.hpp\"");
		$self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_writer.hpp\"");
        $self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_op_translator.hpp\"");
        $self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_internal_translator.hpp\"");
        $self->pidl("#include \"nas/modules/smb/dce_rpc/ndr/ndr_string_utils.hpp\"");
	}
}

#####################################################################
# parse a parsed IDL structure back into an IDL file
sub Parse($$$$)
{
	my($self, $ndr,$gen_header,$gen_client_functions) = @_;

	$self->{gen_client_functions} = $gen_client_functions;

	use File::Basename;

	$self->pidl("// auto-generated by infinipidl");
	$self->pidl("");
	$self->GenerateIncludes();
	$self->pidl("#include \"../include/".basename($gen_header)."\"");
	$self->pidl("");
	$self->pidl("using namespace nas;");
	$self->pidl("using namespace smb;");
	$self->pidl("using namespace dcerpc;");
    $self->pidl("using namespace ndr;");

	my %needed = ();

	foreach (@{$ndr}) {
		if ($_->{TYPE} eq "INTERFACE")
		{
    		$self->pidl("using namespace smb::dcerpc::services::$_->{NAME};");
			NeededInterface($_, \%needed);
		}
	}

    $self->pidl("");

	foreach (@{$ndr}) {
		($_->{TYPE} eq "INTERFACE") && $self->ParseInterface($_, \%needed);
	}

	return $self->{res};
}

sub NeededElement($$$)
{
	my ($e, $dir, $needed) = @_;

	return if ($e->{TYPE} eq "EMPTY");

	return if (ref($e->{TYPE}) eq "HASH" and 
		       not defined($e->{TYPE}->{NAME}));

	my ($t, $rt);
	if (ref($e->{TYPE}) eq "HASH") {
		$t = $e->{TYPE}->{TYPE}."_".$e->{TYPE}->{NAME};
	} else {
		$t = $e->{TYPE};
	}

	if (ref($e->{REPRESENTATION_TYPE}) eq "HASH") {
		$rt = $e->{REPRESENTATION_TYPE}->{TYPE}."_".$e->{REPRESENTATION_TYPE}->{NAME};
	} else {
		$rt = $e->{REPRESENTATION_TYPE};
	}

	die ("$e->{NAME} $t, $rt FOO") unless ($rt ne "");

	my @fn = ();
	push (@fn, TypeFunctionName($dir, $e->{TYPE}));

	if ($dir eq "get") {;
		push (@fn, "ndr_$t\_to_$rt")
			if ($rt ne $t);
	} elsif ($dir eq "put") {
		push (@fn, "ndr_$rt\_to_$t")
			if ($rt ne $t);
	} else {
		die("invalid direction `$dir'");
	}

	foreach (@fn) {
		unless (defined($needed->{$_})) {
			$needed->{$_} = 1;
		}
	}
}

sub NeededFunction($$)
{
	my ($fn,$needed) = @_;
	$needed->{"ndr_pull_$fn->{NAME}"} = 1;
	$needed->{"ndr_push_$fn->{NAME}"} = 1;
	foreach my $e (@{$fn->{ELEMENTS}}) {
		$e->{PARENT} = $fn;
		NeededElement($e, $_, $needed) foreach ("get", "put");
	}
}

sub NeededType($$$)
{
	sub NeededType($$$);
	my ($t,$needed,$req) = @_;

	NeededType($t->{DATA}, $needed, $req) if ($t->{TYPE} eq "TYPEDEF");
	NeededType($t->{DATA}, $needed, $req) if ($t->{TYPE} eq "PIPE");

	if ($t->{TYPE} eq "STRUCT" or $t->{TYPE} eq "UNION") {
		return unless defined($t->{ELEMENTS});
		for my $e (@{$t->{ELEMENTS}}) {
			$e->{PARENT} = $t;
			if (has_property($e, "compression")) { 
				$needed->{"compression"} = 1;
			}
			NeededElement($e, $req, $needed);
			NeededType($e->{TYPE}, $needed, $req) if (ref($e->{TYPE}) eq "HASH");
		}
	}
}

#####################################################################
# work out what parse functions are needed
sub NeededInterface($$)
{
	my ($interface,$needed) = @_;
	NeededFunction($_, $needed) foreach (@{$interface->{FUNCTIONS}});
	foreach (reverse @{$interface->{TYPES}}) {

		if (has_property($_, "public")) {
			$needed->{TypeFunctionName("get", $_)} = $needed->{TypeFunctionName("put", $_)} = 1;
		}

		NeededType($_, $needed, "get") if ($needed->{TypeFunctionName("get", $_)});
		NeededType($_, $needed, "put") if ($needed->{TypeFunctionName("put", $_)});
		if (has_property($_, "gensize")) {
			$needed->{"ndr_size_$_->{NAME}"} = 1;
		}
	}
}

sub TypeFunctionName($$)
{
	my ($action, $t) = @_;

	return "$action\_uint32_64" if ($t eq "uint3264");
	return "$action\_uint16_32" if ($t eq "uint1632");
	return "$action\_ipv4" if ($t eq "ipv4address");
	return "$action\_ipv6" if ($t eq "ipv6address");
	return "$action\_blob" if ($t eq "DATA_BLOB");
	return "$action\<" . mapTypeName($t) . ">";
}

sub GetAlignmentStatement($$)
{
	my ($ndr, $alignment) = @_;

	return "$ndr.align_16_32();" if ($alignment == 3);
	return "$ndr.align_32_64();" if ($alignment == 5);
	return "$ndr.align($alignment);";
}

sub GetNDR64OnlyAlignment($)
{
	my ($alignment) = @_;

	return 4 if ($alignment == 3);
	return 8 if ($alignment == 5);
	return $alignment;
}

1;
