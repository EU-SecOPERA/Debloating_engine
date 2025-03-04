.PHONY: all build clean

FRAMAC_SHARE:=$(shell frama-c-config -print-share-path)

include ${FRAMAC_SHARE}/Makefile.common

##########################################################################
# Build

all:: build

build::
	dune build @install

clean:: purge-tests
	dune clean
	rm -rf _build .merlin

##########################################################################
# Tests

include ${FRAMAC_SHARE}/Makefile.testing

##########################################################################
# Install

include ${FRAMAC_SHARE}/Makefile.installation

##########################################################################
# Linting

include ${FRAMAC_SHARE}/Makefile.linting

##########################################################################
