{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    # onelab = {
    #   url = "github:plt-amy/1lab";
    #   flake = false;
    # };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
    inherit (nixpkgs) lib;
    myAgda = pkgs.agda.withPackages (p: with p; [
      cubical
      _1lab
    ]);
    AGDA_LIBRARIES_FILE = pkgs.writeText "libraries"
      (lib.concatMapStrings (p: "${p}/${p.libraryFile}\n") (with pkgs.agdaPackages; [
        cubical
        _1lab
      ]));
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
