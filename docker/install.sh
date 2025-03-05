#!/bin/sh -eu

# (Note: this script cannot use bash, since Alpine does not have it by default)

# Download and install packages, using the distribution's package manager
# Note: package managers usually fail when a package name does not exist,
# but we want to factorize the code, so we give as many package names as
# possible (including all variants from all distributions) and hope for
# the best. Therefore we install one by one and skip in case of failure.
# If there are actual errors installing them, the Dockerfile will end up
# failing later anyway (or so we hope).

if [ $# -lt 1 ]; then
    echo "usage: $0 package1 [package2 ...]"
    exit 2
fi

# Use sudo if not root
if [ $(id -u) -ne 0 ]; then
    SUDO=sudo
else
    SUDO=
fi


# Update package cache once, then iterate over packages

if [ -e /etc/debian_version ]; then
    # Debian
    $SUDO apt-get update -y
    INSTALL="apt-get install -y"
elif [ -e /etc/fedora-release ]; then
    # Fedora
    $SUDO dnf update -y
    INSTALL="dnf install -y"
elif [ -e /etc/alpine-release ]; then
    # Alpine
    $SUDO apk update
    INSTALL="apk add"
else
    echo "error: unsupported Linux distribution"
    exit 1
fi

for name in "$@"
do
    $SUDO $INSTALL $name || echo "$name not found, skipping"
done
