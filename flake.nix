{
  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar-src = {
      url = "github:FStarLang/FStar";
      flake = false;
    };

    everest = {
      url = github:project-everest/everest-nix?dir=projects;
      inputs.fstar-src.follows    = "fstar-src";
    };
  };

  outputs = {self, nixpkgs, fstar-src, everest}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = everest.packages.${system}.z3;
    fstar = everest.packages.${system}.fstar;
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
