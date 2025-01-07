{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    the1lab = {
      url = "github:the1lab/1lab/aliao/list-sigma";
      flake = false;
    };
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
                  rev = "3344ca8058ec35d08e13dfd188df19517023efb5";
                  hash = "sha256-sZ6afNUBXZPjauLA0JGoFlCKlgcGrGhEJQvKYW2VhtY=";
                };
              })
              disableLibraryProfiling
              disableExecutableProfiling
              dontCheck
              dontHaddock
              (addBuildDepends [ hself.enummapset hself.generic-data hself.nonempty-containers hself.process-extras hself.pqueue ])
            ];
          };
        };
        agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
          _1lab = asuper._1lab.overrideAttrs {
            version = "unstable-${inputs.the1lab.shortRev}";
            src = inputs.the1lab;
          };
          cubical = asuper.cubical.overrideAttrs {
            version = "unstable";
            src = pkgs.fetchFromGitHub {
              owner = "agda";
              repo = "cubical";
              rev = "2f085f5675066c0e1708752587ae788c036ade87";
              hash = "sha256-3pTaQGJPDh9G68RmQAZM7AgBQ8jcqvEUteQep0MsVhw=";
            };
          };
          standard-library = asuper.standard-library.overrideAttrs {
            version = "2.1.1";
            src = pkgs.fetchFromGitHub {
              owner = "agda";
              repo = "agda-stdlib";
              rev = "v2.1.1";
              hash = "sha256-4HfwNAkIhk1yC/oSxZ30xilzUM5/22nzbUSqTjcW5Ng=";
            };
          };
        });
      }) ];
    };
    inherit (nixpkgs) lib;

    agdaLibs = libs: [
      libs.standard-library
      libs.cubical
      libs._1lab
    ];
    agda = pkgs.agda.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.agdaPackages.mkLibraryFile agdaLibs;

    shakefile = pkgs.haskellPackages.callCabal2nix "cubical-experiments-shake" ./shake {};
  in {
    devShells.${system} = {
      default = self.packages.${system}.default.overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs or [] ++ [ agda ];
      });

      shakefile = pkgs.haskellPackages.shellFor {
        packages = _: [ shakefile ];
        inherit AGDA_LIBRARIES_FILE;
      };
    };

    packages.${system} = {
      default = pkgs.stdenv.mkDerivation {
        name = "cubical-experiments";
        src = self;
        nativeBuildInputs = [ shakefile ];
        inherit AGDA_LIBRARIES_FILE;
        LC_ALL = "C.UTF-8";
        buildPhase = ''
          cubical-experiments-shake
          mv _build/site "$out"
        '';
      };

      inherit shakefile;
    };
  };
}
