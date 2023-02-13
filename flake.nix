{
  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar-flake = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {self, nixpkgs, fstar-flake}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    comparse = pkgs.callPackage ./default.nix {inherit fstar z3; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    packages.${system} = {
      inherit fstar comparse;
    };
    defaultPackage.${system} = comparse;
    hydraJobs = {
      comparse-build.${system} = comparse;
      comparse-tests.${system} = comparse.tests;
    };
  };
}
