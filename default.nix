{stdenv, which, fstar, z3}:

stdenv.mkDerivation {
  name = "comparse";
  src = ./.;
  buildInputs = [ which fstar z3 ];
  FSTAR_HOME = fstar;
  installPhase = ''
    mkdir -p $out
    cp obj/* $out
  '';
}
