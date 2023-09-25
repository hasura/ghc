# Note [Preparing variables for GHC.Toolchain.Target]
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# In configure, we generate default.target and default.host.target files that
# contain a value of the Haskell type GHC.Toolchain.Target.Target.
#
# Since we substitute in those files with configured variables, we have to
# preparate them as Haskell values, for example, turning YES/NO into
# True,False, or empty variables into Nothing or Just something otherwise.
#
# This toolchain will additionally be used to validate the one generated by
# ghc-toolchain. See Note [ghc-toolchain consistency checking].

# PREP_MAYBE_SIMPLE_PROGRAM
# =========================
#
# Issue a substitution of [$1MaybeProg] with
# * Nothing, if $1 is empty
# * Just (Program {prgPath = "$$1", prgFlags = []}), otherwise
#
# $1 = optional value
AC_DEFUN([PREP_MAYBE_SIMPLE_PROGRAM],[
    if test -z "$$1"; then
        $1MaybeProg=Nothing
    else
        $1MaybeProg="Just (Program {prgPath = \"$$1\", prgFlags = @<:@@:>@})"
    fi
    AC_SUBST([$1MaybeProg])
])

# PREP_MAYBE_STRING
# =========================
#
# Issue a substitution of [$1MaybeStr] with
# * Nothing, if $1 is empty
# * Just "$$1", otherwise
#
# $1 = optional value
AC_DEFUN([PREP_MAYBE_STRING],[
    if test -z "$$1"; then
        $1MaybeStr=Nothing
    else
        $1MaybeStr="Just \"$$1\""
    fi
    AC_SUBST([$1MaybeStr])
])

# PREP_BOOLEAN
# ============
#
# Issue a substitution with True/False of [$1Bool] when $1 has YES/NO value
# $1 = boolean variable to substitute
AC_DEFUN([PREP_BOOLEAN],[
    case "$$1" in
        YES)
          $1Bool=True
          ;;
        NO)
          $1Bool=False
          ;;
        *)
          AC_MSG_WARN([m4/prep_target_file.m4: Expecting YES/NO but got $$1 in $1. Defaulting to False.])
          $1Bool=False
          ;;
    esac
    AC_SUBST([$1Bool])
])

# PREP_NOT_BOOLEAN
# ============
#
# Issue a substitution with True/False of [Not$1Bool] when $1 has NO/YES value
# $1 = boolean variable to substitute
AC_DEFUN([PREP_NOT_BOOLEAN],[
    case "$$1" in
        NO)
          Not$1Bool=True
          ;;
        YES)
          Not$1Bool=False
          ;;
        *)
          AC_MSG_WARN([m4/prep_target_file.m4: Expecting YES/NO but got $$1 in $1. Defaulting to False.])
          Not$1Bool=False
          ;;
    esac
    AC_SUBST([Not$1Bool])
])

# PREP_LIST
# ============
#
# Issue a substitution with ["list","of","args"] of [$1List] when $1 is a
# space-separated list of args
# i.e.
# "arg1 arg2 arg3"
# ==>
# ["arg1","arg2","arg3"]
#
# $1 = list variable to substitute
dnl In autoconf, '@<:@' stands for '[', and '@:>@' for ']'.
AC_DEFUN([PREP_LIST],[
    # shell array
    set -- $$1
    $1List="@<:@"
    if test "[$]#" -eq 0; then
        # no arguments
        true
    else
        $1List="${$1List}\"[$]1\""
        shift # drop first elem
        for arg in "[$]@"
        do
            $1List="${$1List},\"$arg\""
        done
    fi
    $1List="${$1List}@:>@"

    AC_SUBST([$1List])
])

# Eventually: PREP_BUILD_TARGET_FILE, PREP_HOST_TARGET_FILE, PREP_TARGET_TARGET_FILE
# Prepares required substitutions to generate the target file
AC_DEFUN([PREP_TARGET_FILE],[

    dnl Target target
    PREP_BOOLEAN([MergeObjsSupportsResponseFiles])
    PREP_BOOLEAN([TargetHasGnuNonexecStack])
    PREP_BOOLEAN([LeadingUnderscore])
    PREP_BOOLEAN([ArSupportsAtFile])
    PREP_BOOLEAN([ArSupportsDashL])
    PREP_BOOLEAN([TargetHasIdentDirective])
    PREP_BOOLEAN([CONF_GCC_SUPPORTS_NO_PIE])
    PREP_BOOLEAN([LdHasFilelist])
    PREP_BOOLEAN([LdIsGNULd])
    PREP_BOOLEAN([LdHasNoCompactUnwind])
    PREP_BOOLEAN([TargetHasSubsectionsViaSymbols])
    PREP_BOOLEAN([Unregisterised])
    PREP_BOOLEAN([TablesNextToCode])
    PREP_BOOLEAN([UseLibffiForAdjustors])
    PREP_BOOLEAN([ArIsGNUAr])
    PREP_BOOLEAN([ArNeedsRanLib])
    PREP_NOT_BOOLEAN([CrossCompiling])
    PREP_LIST([MergeObjsArgs])
    PREP_LIST([ArArgs])
    PREP_LIST([CONF_GCC_LINKER_OPTS_STAGE2])
    PREP_LIST([HaskellCPPArgs])
    PREP_MAYBE_SIMPLE_PROGRAM([WindresCmd])
    PREP_MAYBE_STRING([TargetVendor_CPP])
    PREP_MAYBE_STRING([HostVendor_CPP])
    PREP_LIST([CONF_CPP_OPTS_STAGE2])
    PREP_LIST([CONF_CXX_OPTS_STAGE2])
    PREP_LIST([CONF_CC_OPTS_STAGE2])

    dnl Host target
    PREP_BOOLEAN([ArSupportsAtFile_STAGE0])
    PREP_BOOLEAN([ArSupportsDashL_STAGE0])
    PREP_LIST([AR_OPTS_STAGE0])
    PREP_LIST([CONF_CC_OPTS_STAGE0])
    PREP_LIST([CONF_CPP_OPTS_STAGE0])
    PREP_LIST([CONF_CXX_OPTS_STAGE0])
    PREP_LIST([CONF_GCC_LINKER_OPTS_STAGE0])

    PREP_BOOLEAN([LdHasNoCompactUnwind_STAGE0])
    PREP_BOOLEAN([LdIsGNULd_STAGE0])
    PREP_BOOLEAN([LdHasFilelist_STAGE0])
    PREP_BOOLEAN([CONF_GCC_SUPPORTS_NO_PIE_STAGE0])


    if test -z "$MergeObjsCmd"; then
      MergeObjsCmdMaybe=Nothing
    else
      MergeObjsCmdMaybe="Just (MergeObjs {mergeObjsProgram = Program {prgPath = \"$MergeObjsCmd\", prgFlags = $MergeObjsArgsList}, mergeObjsSupportsResponseFiles = $MergeObjsSupportsResponseFilesBool})"
    fi
    AC_SUBST([MergeObjsCmdMaybe])

    dnl PREP_ENDIANNESS
    case "$TargetWordBigEndian" in
        YES)
            TargetEndianness=BigEndian
            ;;
        NO)
            TargetEndianness=LittleEndian
            ;;
        *)
            AC_MSG_ERROR([m4/prep_target_file.m4: Expecting YES/NO but got $TargetWordBigEndian in TargetWordBigEndian])
            ;;
    esac
    AC_SUBST([TargetEndianness])
])

AC_DEFUN()
