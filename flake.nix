{
  inputs = {
    nixpkgs.url = "github:ncfavier/nixpkgs/agda-bump";
    the1lab = {
      url = "github:the1lab/1lab";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ (self: super: {
        agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
          _1lab = asuper._1lab.overrideAttrs {
            version = "unstable-${inputs.the1lab.shortRev}";
            src = inputs.the1lab;
          };
        });
      }) ];
    };

    agdaLibs = libs: [
      libs.standard-library
      libs.cubical
      libs._1lab
    ];
    agda = pkgs.agda.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.agdaPackages.mkLibraryFile agdaLibs;
    Agda_datadir = "${pkgs.haskellPackages.Agda.data}/share/agda";

    shakefile = pkgs.haskellPackages.callCabal2nix "cubical-experiments-shake" ./shake {};
  in {
    devShells.${system} = {
      default = self.packages.${system}.default.overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs or [] ++ [ agda ];
      });

      shakefile = pkgs.haskellPackages.shellFor {
        packages = _: [ shakefile ];
        inherit AGDA_LIBRARIES_FILE Agda_datadir;
      };
    };

    packages.${system} = {
      default = pkgs.stdenv.mkDerivation {
        name = "cubical-experiments";
        src = self;
        nativeBuildInputs = [ shakefile ];
        inherit AGDA_LIBRARIES_FILE Agda_datadir;
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
