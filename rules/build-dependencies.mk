# -----------------------------------------------------------------------------
#
# (c) 2009 The University of Glasgow
#
# This file is part of the GHC build system.
#
# To understand how the build system works and how to modify it, see
#      http://hackage.haskell.org/trac/ghc/wiki/Building/Architecture
#      http://hackage.haskell.org/trac/ghc/wiki/Building/Modifying
#
# -----------------------------------------------------------------------------

define build-dependencies # args: $1 = dir, $2 = distdir

$1_$2_depfile_haskell = $$($1_$2_depfile_base).haskell
$1_$2_depfile_c_asm = $$($1_$2_depfile_base).c_asm

$1_$2_C_FILES_DEPS = $$(filter-out $$($1_$2_C_FILES_NODEPS),$$($1_$2_C_FILES))

ifeq "$$($1_$2_ghc_ge_609)" "YES"
$1_$2_MKDEPENDHS_FLAGS = -include-pkg-deps -dep-makefile $$($1_$2_depfile_haskell).tmp $$(foreach way,$$(filter-out v,$$($1_$2_WAYS)),-dep-suffix $$(way))
else
$1_$2_MKDEPENDHS_FLAGS = -optdep--include-pkg-deps -optdep-f -optdep$$($1_$2_depfile_haskell).tmp $$(foreach way,$$(filter-out v,$$($1_$2_WAYS)),-optdep-s -optdep$$(way))
endif

ifneq "$$($1_$2_NO_BUILD_DEPS)" "YES"

$$($1_$2_depfile_haskell) : $$($1_$2_HS_SRCS) $$($1_$2_HS_BOOT_SRCS) $$($1_$2_HC_MK_DEPEND_DEP) | $$$$(dir $$$$@)/.
	"$$(RM)" $$(RM_OPTS) $$@.tmp
	touch $$@.tmp
ifneq "$$($1_$2_HS_SRCS)" ""
	"$$($1_$2_HC_MK_DEPEND)" -M $$($1_$2_MKDEPENDHS_FLAGS) \
	    $$(filter-out -split-objs, $$($1_$2_v_ALL_HC_OPTS)) \
	    $$($1_$2_HS_SRCS)
endif
	echo "$1_$2_depfile_haskell_EXISTS = YES" >> $$@.tmp
ifneq "$$($1_$2_SLASH_MODS)" ""
	for dir in $$(sort $$(foreach mod,$$($1_$2_SLASH_MODS),$1/$2/build/$$(dir $$(mod)))); do \
		if test ! -d $$$$dir; then mkdir -p $$$$dir; fi \
	done
endif
	mv $$@.tmp $$@

$$($1_$2_depfile_c_asm) : $$($1_$2_C_FILES_DEPS) $$($1_$2_S_FILES) | $$$$(dir $$$$@)/.
	"$$(RM)" $$(RM_OPTS) $$@.tmp
	touch $$@.tmp
ifneq "$$(strip $$($1_$2_C_FILES_DEPS)$$($1_$2_S_FILES))" ""
	$$(foreach f,$$($1_$2_C_FILES_DEPS) $$($1_$2_S_FILES), \
	  $$(foreach w,$$($1_$2_WAYS), \
	    $$(call addCFileDeps,$1,$2,$$($1_$2_depfile_c_asm),$$f,$$w)))
	"$$(RM)" $$(RM_OPTS) $$@.bit
endif
	echo "$1_$2_depfile_c_asm_EXISTS = YES" >> $$@.tmp
	mv $$@.tmp $$@

endif # $1_$2_NO_BUILD_DEPS

# Note sed magic above: mkdependC can't do -odir stuff, so we have to
# munge the dependencies it generates to refer to the correct targets.

# Seems as good a place as any to attach the unlit dependency
$$($1_$2_depfile_haskell) : $$(UNLIT)

ifneq "$$(NO_INCLUDE_DEPS)" "YES"
include $$($1_$2_depfile_haskell)
include $$($1_$2_depfile_c_asm)
else
ifeq "$$(DEBUG)" "YES"
$$(warning not building dependencies in $1)
endif
endif

endef

define addCFileDeps

# $1 = dir
# $2 = distdir
# $3 = depfile
# $4 = file
# $5 = way
# The formatting of this definition (e.g. the blank line above) is
# important, in order to get make to generate the right makefile code.
	$(CPP) $($1_$2_MKDEPENDC_OPTS) $($1_$2_$5_ALL_CC_OPTS) $($(basename $4)_CC_OPTS) -MM $4 -MF $3.bit
	sed -e "1s|\.o|\.$($5_osuf)|" -e "1s|^|$(dir $4)|" -e "1s|$1/|$1/$2/build/|" -e "s|$(TOP)/||g" -e "s|$2/build/$2/build|$2/build|g" $3.bit >> $3.tmp
endef

