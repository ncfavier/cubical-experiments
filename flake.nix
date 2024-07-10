{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    onelab = {
      url = "github:ncfavier/1lab/agda-lib-nix";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
    inherit (nixpkgs) lib;
    agdaLibs = p: with p; [
      standard-library
      cubical
      # _1lab
      (import inputs.onelab { interactive = false; inherit system; })._1lab-agda
    ];
    myAgda = pkgs.agda.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.writeText "libraries"
      (lib.concatMapStrings (p: "${p}/${p.libraryFile}\n") (agdaLibs pkgs.agdaPackages));
    shakefile = pkgs.haskellPackages.callCabal2nix "cubical-experiments-shake" ./shake {};
  in {
    devShells.${system}.shakefile = pkgs.haskellPackages.shellFor {
      packages = _: [ shakefile ];
      inherit AGDA_LIBRARIES_FILE;
    };

    packages.${system}.default = pkgs.stdenv.mkDerivation {
      name = "cubical-experiments";
      src = self;
      nativeBuildInputs = [
        myAgda
        shakefile
      ];
      inherit AGDA_LIBRARIES_FILE;
      LC_ALL = "C.UTF-8";
      buildPhase = ''
        cubical-experiments-shake
        mv _build/site "$out"
      '';
    };
  };
}
