#!/usr/bin/env bash

# create the docker image. Must only be done once

MYDIR=$(dirname $0)

rm -fr $MYDIR/debloating
mkdir -p $MYDIR/debloating
cp -r "$MYDIR"/../*.ml "$MYDIR"/../*.mli "$MYDIR"/../Makefile \
      "$MYDIR"/../dune "$MYDIR"/../dune-project "$MYDIR"/../tests \
   $MYDIR/debloating

docker build $MYDIR -t secopera/frama-c-debloating:latest \
       --build-arg=DISTRO=debian:12.9 \
       --build-arg=OCAML_VERSION=5.3.0 \
       --build-arg=FC_COMMIT=31.0 \
       --target frama-c-slim

rm -fr $MYDIR/debloating
