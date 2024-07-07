TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

size_hello_artifact_gzip:
	'$(TEST_HC)' $(TEST_HC_OPTS) ./size_hello_artifact.hs -v0 -fforce-recomp
	gzip --best "./size_hello_artifact$(EXE_EXTENSION_TEST)"

size_hello_unicode_gzip:
	'$(TEST_HC)' $(TEST_HC_OPTS) ./size_hello_unicode.hs -v0 -fforce-recomp
	gzip --best "./size_hello_unicode$(EXE_EXTENSION_TEST)"
