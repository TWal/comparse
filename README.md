# Comparse

Read the Comparse paper:
[doi](https://dl.acm.org/doi/10.1145/3576915.3623201)
[eprint](https://eprint.iacr.org/2023/1390).

## Dependencies

The Makefile expects either to have `fstar.exe` in the PATH,
or to have the `FSTAR_EXE` environment variable set to the path
for `fstar.exe`. To run the tests, `dune` is required.

Otherwise, using Nix, all the dependencies are fetched automatically.

## Compiling

To verify Comparse, run the following command:

    make

To run Comparse tests, run the following command:

    make check

This will test the meta-program in a variety of scenarios,
and also run the generated parsers / serializers
to check if their output actually correspond to what we expect.

Comparse can also be built using Nix:

    nix build

Comparse can also be tested with Nix:

    nix flake check
