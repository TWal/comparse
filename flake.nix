{
  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar-src = {
      url = "github:FStarLang/FStar";
      flake = false;
    };
  };

  outputs = {self, nixpkgs, fstar-src}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = pkgs.callPackage ./z3.nix {};
    fstar = (pkgs.callPackage ./fstar.nix {inherit z3;}).binary-of-fstar { src = fstar-src; name = "fstar"; };
    comparse = pkgs.callPackage ./default.nix {inherit fstar z3;};
  in {
    packages.${system} = {
      inherit fstar comparse;
    };
    defaultPackage.${system} = comparse;
    hydraJobs = {
      comparse-build.${system} = comparse;
      # comparse-test.${system} = ...;
    };
  };
}
