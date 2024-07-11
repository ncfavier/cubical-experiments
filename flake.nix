{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    # onelab = {
    #   url = "github:plt-amy/1lab";
    #   flake = false;
    # };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ (self: super: {
        haskell = super.haskell // {
          packageOverrides = hself: hsuper: {
            Agda = with self.haskell.lib.compose; lib.pipe hsuper.Agda [
              (overrideSrc {
                version = "2.6.5";
                src = pkgs.fetchFromGitHub {
                  owner = "agda";
                  repo = "agda";
                  rev = "403ee4263e0f14222956e398d2610ae1a4f05467";
                  hash = "sha256-laM5s1F6NnPmejSHQiTvjd0G+9TJTAUJv6sbsLSHKyc=";
                };
              })
              dontCheck
              (addBuildDepend hself.pqueue)
            ];
          };
        };
        agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
          _1lab = asuper._1lab.overrideAttrs {
            src = pkgs.fetchFromGitHub {
              owner = "plt-amy";
              repo = "1lab";
              rev = "11f611363c01d24e8c46d5d99622066d04a32597";
              hash = "sha256-DKwVAV1gPOVImunaJe+XIPQX+ehjG/RcOiYJmGKnnrQ=";
            };
          };
        });
      }) ];
    };
    inherit (nixpkgs) lib;

    agdaLibs = p: with p; [
      standard-library
      cubical
      _1lab
    ];
    agda = pkgs.agda.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.agdaPackages.mkLibraryFile agdaLibs;

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
        agda
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
