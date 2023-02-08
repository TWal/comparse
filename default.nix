{stdenv, which, fstar, z3, ocamlPackages}:

let
  comparse = stdenv.mkDerivation {
    name = "comparse";
    src = ./.;
    buildInputs = [ which fstar z3 ];
    FSTAR_HOME = fstar;
    installPhase = ''
      mkdir -p $out
      cp -r ml src cache hints $out
    '';
    passthru.tests = comparse-tests;
  };
  comparse-tests = stdenv.mkDerivation {
    name = "comparse-tests";
    src = ./.;
    buildInputs =
      [ which fstar z3 ]
      ++ (with ocamlPackages; [
        ocaml dune_3 findlib
        # # fstarlib dependencies
        # batteries stdint zarith ppx_deriving_yojson
      ])
      ++ (fstar.buildInputs);
    FSTAR_HOME = fstar;
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
