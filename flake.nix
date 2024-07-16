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
                version = "2.8.0";
                src = pkgs.fetchFromGitHub {
                  owner = "agda";
                  repo = "agda";
                  rev = "3a9d3893737b3a47c57e1c997f588931d592b0b6";
                  hash = "sha256-2MI5jBIpVNscAFn3N3/jS+ZZIfRwmcJiTueE9QDZQxk=";
                };
              })
              dontCheck
              (addBuildDepend hself.pqueue)
            ];
          };
        };
        agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
          _1lab = asuper._1lab.overrideAttrs {
            version = "unstable-50ea36cb";
            src = pkgs.fetchFromGitHub {
              owner = "plt-amy";
              repo = "1lab";
              rev = "50ea36cb139cb5947303851cb177d3cf2aa3dfa8";
              hash = "sha256-aEB4WQ096ynO5v5BmsPD4RR9AqIRPEiu1PQCqIAxm/A=";
            };
          };
          standard-library = asuper.standard-library.overrideAttrs {
            version = "2.1";
            src = pkgs.fetchFromGitHub {
              owner = "agda";
              repo = "agda-stdlib";
              rev = "96d44779bdd34e61624c2fe5ae161df223748238";
              hash = "sha256-7i98epTFZ757ciBOcnV9/uNh9VEaXmdUGcKyidmiy8E=";
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
