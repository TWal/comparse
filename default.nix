{lib, stdenv, which, fstar, z3, ocamlPackages}:

let
  comparse = stdenv.mkDerivation {
    name = "comparse";
    # TODO: exclude tests
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "src(/.*)?"
      ]
    ;
    buildInputs = [ which fstar z3 ];
    installPhase = ''
      mkdir -p $out
      cp -r ml src cache hints $out
    '';
    passthru.tests = comparse-tests;
  };
  comparse-tests = stdenv.mkDerivation {
    name = "comparse-tests";
    src =
      lib.sources.sourceByRegex ./. [
        "Makefile"
        "src(/.*)?"
        "dune-project"
        "ml(/lib(/dune)?)?"
        "ml(/tests(/dune)?)?"
        "comparse.opam"
      ]
    ;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml dune_3 findlib
      ])
      ++ (fstar.buildInputs);
    # pre-patch uses build output from comparse, to avoid building things twice
    prePatch = ''
      cp -pr --no-preserve=mode ${comparse}/cache ${comparse}/ml .
      mkdir obj
      cp -p ml/lib/src/* obj/
    '';
    doCheck = true;
    installPhase = ''
      touch $out
    '';
  };
in
  comparse
