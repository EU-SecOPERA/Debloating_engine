# Debloating Plug-in

This plug-in performs code debloating, based on the alias analysis of the Alias plug-in. It outputs
in a new project, called `Debloated` by default, the debloated code, i.e. the initial program where
statements and functions that are known not to be reachable from the initial entry point have been
removed. Typical usage, which will print the debloated code on stdout, looks like the following:
```
frama-c -debloating [pre-processing options] [C files] [-main entry_point] -then-last -print
```

# Options

- `-debloating` enables debloating transformation
- `-debloating-project name` sets the name of the generated project to `name` instead of `Debloated`

# Installation

If you have Frama-C installed, `make` and `make install` will compile the plug-in and install it
together with the main Frama-C installation (may require administrative rights). Alternatively,
you can create a Docker image called `secopera/frama-c-debloating` by using the script
`./docker/mkdocker.sh`.
