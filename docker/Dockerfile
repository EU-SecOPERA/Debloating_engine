# Inspired by https://github.com/Frederic-Boulanger-UPS/docker-framac and
# https://gitlab.inria.fr/why3/why3/-/blob/master/misc/Dockerfile.deploy

# DISTRO must be passed via --build-arg (see Makefile)
ARG DISTRO
FROM $DISTRO AS base

# Use specific Frama-C commit to ensure compatibility with Debloating plug-in

ARG FC_COMMIT

# Stage 1: install opam 2.1 and create 'opam' user

ENV DEBIAN_FRONTEND=noninteractive

COPY install.sh /init/
RUN chmod +x /init/install.sh
RUN /init/install.sh \
  bash \
  bubblewrap \
  build-base \
  bzip2 \
  clang \
  curl \
  diffutils \
  gcc \
  git \
  make \
  patch \
  python \
  python3-pip \
  tar \
  time \
  unzip \
  virtualenv \
  wget \
  which

RUN bash -c "yes '' | sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)" --version 2.1.5

COPY requirements.txt /py-env/requirements.txt
RUN virtualenv /py-env && /py-env/bin/pip install -r /py-env/requirements.txt

RUN curl -fsSL https://git.frama-c.com/pub/frama-c/-/archive/${FC_COMMIT}/frama-c-${FC_COMMIT}.tar.gz -o /frama-c.tar.gz
RUN mkdir /frama-c
RUN cd /frama-c && tar xzvf /frama-c.tar.gz --strip-components=1

# Avoid using root (opam dislikes it)
RUN /frama-c/dev/docker/add-user.sh opam
RUN chown -R opam /frama-c
RUN chown -R opam /init
USER opam
WORKDIR /home/opam

# Stage 2: initialize opam

FROM base AS opam-init
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

COPY secopera-configuration.md /init/reference-configuration.md
RUN cp /frama-c/dev/docker/opam-init-from-ref-config.sh /init/
RUN /init/opam-init-from-ref-config.sh "${OCAML_VERSION}"

# "RUN eval $(opam env)" does not work, so we manually set its variables.
# We also set other potentially useful environment variables

## Avoid prompts for time zone
ENV TZ=Europe/Paris
## Fix issue with libGL on Windows
ENV LIBGL_ALWAYS_INDIRECT=1

ENV OPAM_SWITCH_PREFIX "/home/opam/.opam/${OCAML_VERSION}"
ENV CAML_LD_LIBRARY_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/toplevel"
ENV MANPATH "$MANPATH:/home/opam/.opam/${OCAML_VERSION}/man"
ENV PATH "/home/opam/.opam/${OCAML_VERSION}/bin:$PATH"

## Add file to help with interactive Docker image use
RUN if [ ! -e /home/opam/.bashrc ]; then echo ". .bash_profile" > /home/opam/.bashrc; fi

# Stage 3: install Frama-C dependencies

FROM opam-init AS fc-deps
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

# Install external provers
## CVC4 1.7
RUN \
 wget --quiet http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.7-x86_64-linux-opt -O cvc4-1.7 \
 && chmod a+x cvc4-1.7 \
 && sudo mv cvc4-1.7 /usr/local/bin/
RUN /init/install.sh z3

# Install Frama-C depexts and dependencies
RUN cp /frama-c/dev/docker/opam-install-fc-deps-from-ref-config.sh /init/
RUN sudo chmod +x /init/opam-install-fc-deps-from-ref-config.sh
RUN /init/opam-install-fc-deps-from-ref-config.sh

RUN why3 config detect

# Stage 4: install Frama-C itself

FROM fc-deps AS frama-c
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

## The following line copies a frama-c archive if it exists, else nothing
COPY --chown=opam:opam debloating /frama-c/src/plugins/debloating

# E-ACSL (incompatible with musl-libc) is disabled on Alpine
RUN cd /frama-c && ./dev/disable-plugins.sh gui $([ -e /etc/alpine-release ] && echo "e-acsl") && make clean && make && make install

## Run quick sanity checks
## Note: E-ACSL tests are disabled on Alpine
RUN \
printf "int g;\n//@assigns g;\nvoid f(){g = 1;}\nint main() {f(); return g;}" > /tmp/simple.c && \
frama-c -eva -wp -report /tmp/simple.c && \
rm -f /tmp/simple.c && \
echo "int main() { /*@ assert 1 + 2 == 2; */ return 0; }" > /tmp/test-eacsl.c && \
[ -e /etc/alpine-release ] || \
 (cd /tmp && e-acsl-gcc.sh -c test-eacsl.c && \
 ./a.out.e-acsl 2>&1 | grep -q "Assertion failed" && \
 rm -f ./a.out* test-eacsl.c)

## Cleanup
RUN \
  opam clean --yes --switch-cleanup && \
  rm -rf /home/opam/opam-repository && \
  rm -rf /home/opam/.opam/repo/default/.git*

# Stage 5 (optional): tests

FROM frama-c AS tests
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

## Run standard Frama-C tests
RUN cd /frama-c && make run-ptests && dune build @ptests_config

## Run an extra test for WP with provers
RUN cd /frama-c/ && cd src/plugins/wp/tests/ && frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,z3

# Stage 6 (optional): GUI

FROM frama-c AS frama-c-gui
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

RUN /init/install.sh adwaita-icon-theme font-noto gdk-pixbuf
RUN cd /frama-c && ./dev/disable-plugins.sh $([ -e /etc/alpine-release ] && echo "e-acsl" || echo "none") && make clean && make && make install

## Sanity check
RUN which frama-c-gui

# Stage 7 (to be deployed): 'slim' image

FROM $DISTRO AS frama-c-slim
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

# Note: Debian and Fedora have 'useradd', but Alpine has 'adduser'
RUN useradd opam || adduser --disabled-password opam

COPY --from=frama-c /bin /bin/
COPY --from=frama-c /etc /etc/
COPY --from=frama-c /lib /lib/
COPY --from=frama-c /sbin /sbin/
COPY --from=frama-c /py-env /py-env/

## RUN true cmds are a workaround against
## obscure docker bug (https://github.com/moby/moby/issues/37965)
## manifesting in sequences of COPY
RUN true
COPY --from=frama-c /usr /usr/
RUN true
COPY --from=frama-c --chown=opam:opam /home/opam/.opam /home/opam/.opam/
COPY --from=frama-c /home/opam/.bashrc /home/opam/

USER opam
WORKDIR /home/opam
ENV OPAM_SWITCH_PREFIX "/home/opam/.opam/${OCAML_VERSION}"
ENV CAML_LD_LIBRARY_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/toplevel"
ENV MANPATH "$MANPATH:/home/opam/.opam/${OCAML_VERSION}/man"
ENV PATH "/home/opam/.opam/${OCAML_VERSION}/bin:$PATH"
## Avoid prompts for time zone
ENV TZ=Europe/Paris
## Fix issue with libGL on Windows
ENV LIBGL_ALWAYS_INDIRECT=1

RUN why3 config detect

# Stage 8 (optional, to be deployed): 'slim' image with frama-c-gui

FROM $DISTRO AS frama-c-gui-slim
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

# Transfers ownership of /home/opam to user opam
# Note: Debian and Fedora have 'useradd', but Alpine has 'adduser'
RUN useradd opam || adduser --disabled-password opam

COPY --from=frama-c-gui /bin /bin/
COPY --from=frama-c-gui /etc /etc/
COPY --from=frama-c-gui /lib /lib/
COPY --from=frama-c-gui /sbin /sbin/
RUN true
COPY --from=frama-c-gui /usr /usr/
RUN true
COPY --from=frama-c-gui --chown=opam:opam /home/opam/.opam /home/opam/.opam/
COPY --from=frama-c /home/opam/.bashrc /home/opam/

USER opam
WORKDIR /home/opam
ENV OPAM_SWITCH_PREFIX "/home/opam/.opam/${OCAML_VERSION}"
ENV CAML_LD_LIBRARY_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/toplevel"
ENV MANPATH "$MANPATH:/home/opam/.opam/${OCAML_VERSION}/man"
ENV PATH "/home/opam/.opam/${OCAML_VERSION}/bin:$PATH"
## Avoid prompts for time zone
ENV TZ=Europe/Paris
## Fix issue with libGL on Windows
ENV LIBGL_ALWAYS_INDIRECT=1

RUN why3 config detect

## Sanity check
RUN which frama-c-gui

## Stage 9: preparation of 'stripped' image (~200 MB compressed)
## Note: this image only contains the Frama-C binaries and files closely
## related to it; most other OCaml tools have been removed.
## Even recompilation of Frama-C is not guaranteed to work.

FROM frama-c-slim AS frama-c-stripped-prepare
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

ENV OPAM_SWITCH_PREFIX "/home/opam/.opam/${OCAML_VERSION}"
ENV CAML_LD_LIBRARY_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/toplevel"
ENV MANPATH "$MANPATH:/home/opam/.opam/${OCAML_VERSION}/man"
ENV PATH "/home/opam/.opam/${OCAML_VERSION}/bin:$PATH"
## Avoid prompts for time zone
ENV TZ=Europe/Paris
## Fix issue with libGL on Windows
ENV LIBGL_ALWAYS_INDIRECT=1


## Remove all non-essential ocaml binaries
RUN \
mkdir -p /home/opam/minimal/bin && \
(cd /home/opam/.opam/*/bin && \
  cp -P $(ls -d frama-c frama-c-config frama-c-script e-acsl-gcc.sh alt-ergo ocaml ocamlc ocamlc.opt ocamlfind ocamlopt ocamlopt.opt why3) /home/opam/minimal/bin/) && \
rm -rf /home/opam/.opam/${OCAML_VERSION}/bin && \
mv /home/opam/minimal/bin /home/opam/.opam/${OCAML_VERSION}/bin/

## Remove non-essential opam files
RUN rm -rf /home/opam/.opam/repo/default/packages
RUN rm -rf /home/opam/.opam/download-cache
RUN rm -rf /home/opam/.opam/repo/state.cache
RUN rm -f  /home/opam/.opam/repo/default.tar.gz

## Further stripping: remove non-essential files from tools used by Frama-C
## (Apron, Alt-Ergo, large OCaml compiler files, etc)
RUN rm -f /home/opam/.opam/${OCAML_VERSION}/share/apron/lib/*.a
RUN rm -f /home/opam/.opam/${OCAML_VERSION}/share/apron/lib/*_debug.so
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/share/apron/bin
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/share/apron/include
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/alt-ergo
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/lablgtk3
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/lablgtk3-sourceview3
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/ppx_deriving
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/ppx_tools
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/ppxlib
RUN rm -rf /home/opam/.opam/${OCAML_VERSION}/lib/psmt2-frontend
RUN rm -rf /home/opam/.opam/*/lib/ocaml/expunge
RUN rm -rf /home/opam/.opam/*/lib/ocaml-migrate-parsetree

## Remove all non-essential OCaml files (everything else other than
## *.cmxs, *.cmx and *.cmi)
## Exceptions: libeacsl-dlmalloc.a (used by e-acsl-gcc.sh during linking)
RUN find /home/opam/.opam \( -name "*.cmt*" -o -name "*.[ao]" -o -name "*.cm[ao]" -o -name "*.cmxa" \) -a -not -name "libeacsl-dlmalloc.a" -exec rm {} \;

## Remove non-essential installed files
RUN sudo rm -r /usr/share/gtk-3.0 /usr/share/X11
RUN sudo rm -f /usr/bin/*gnu-lto-dump*

## Stage 10 (optional): stripped, slimmest image (running Frama-C works,
## but almost everything else does not (e.g. recompiling OCaml modules))

FROM $DISTRO AS frama-c-stripped
ARG OCAML_VERSION

ENV DEBIAN_FRONTEND=noninteractive

# Transfers ownership of /home/opam to user opam
# Note: Debian and Fedora have 'useradd', but Alpine has 'adduser'
RUN useradd opam || adduser --disabled-password opam

COPY --from=frama-c-stripped-prepare /bin /bin/
COPY --from=frama-c-stripped-prepare /etc /etc/
COPY --from=frama-c-stripped-prepare /lib /lib/
COPY --from=frama-c-stripped-prepare /sbin /sbin/
RUN true
COPY --from=frama-c-stripped-prepare /usr /usr/
RUN true
COPY --from=frama-c-stripped-prepare --chown=opam:opam /home/opam/.opam /home/opam/.opam/
COPY --from=frama-c /home/opam/.bashrc /home/opam/

USER opam
WORKDIR /home/opam
ENV OPAM_SWITCH_PREFIX "/home/opam/.opam/${OCAML_VERSION}"
ENV CAML_LD_LIBRARY_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml/stublibs:/home/opam/.opam/${OCAML_VERSION}/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH "/home/opam/.opam/${OCAML_VERSION}/lib/toplevel"
ENV MANPATH "$MANPATH:/home/opam/.opam/${OCAML_VERSION}/man"
ENV PATH "/home/opam/.opam/${OCAML_VERSION}/bin:$PATH"
## Avoid prompts for time zone
ENV TZ=Europe/Paris
## Fix issue with libGL on Windows
ENV LIBGL_ALWAYS_INDIRECT=1

RUN why3 config detect

## Re-run quick sanity checks
RUN \
printf "int g;\n//@assigns g;\nvoid f(){g = 1;}\nint main() {f(); return g;}" > /tmp/simple.c && \
frama-c -val -wp -report /tmp/simple.c && \
rm -f /tmp/simple.c && \
echo "int main() { /*@ assert 1 + 2 == 2; */ return 0; }" > /tmp/test-eacsl.c && \
[ -e /etc/alpine-release ] || \
 (cd /tmp && e-acsl-gcc.sh -c test-eacsl.c && \
 ./a.out.e-acsl 2>&1 | grep -q "Assertion failed" && \
 rm -f ./a.out* test-eacsl.c)
