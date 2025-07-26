{
  inputs = {
    nixpkgs.url = "nixpkgs/haskell-updates";
    agda.url = "github:agda/agda";
    the1lab = {
      url = "github:the1lab/1lab";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
      overlays = [
        inputs.agda.overlays.default
        (self: super: {
          agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
            _1lab = asuper._1lab.overrideAttrs {
              version = "unstable-${inputs.the1lab.shortRev}";
              src = inputs.the1lab;
            };
          });
        })
      ];
    };

    agdaLibs = libs: [
      libs.standard-library
      libs.cubical
      libs._1lab
    ];
    agda = pkgs.agda.withPackages agdaLibs;
    AGDA_LIBRARIES_FILE = pkgs.agdaPackages.mkLibraryFile agdaLibs;

    PANDOC_KATEX_CONFIG_FILE = pkgs.writeText "katex-config.toml" ''
      trust = true
      throw_on_error = true

      [macros]
      "\\bN" = "\\mathbb{N}"
      "\\bZ" = "\\mathbb{Z}"
    '';

    shakefile = pkgs.haskellPackages.callCabal2nix "cubical-experiments-shake" ./shake {};
  in {
    devShells.${system} = {
      default = self.packages.${system}.default.overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs or [] ++ [ agda ];
      });

      shakefile = pkgs.haskellPackages.shellFor {
        packages = _: [ shakefile ];
        nativeBuildInputs = [ pkgs.pandoc-katex ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
      };
    };

    packages.${system} = {
      default = pkgs.stdenv.mkDerivation {
        name = "cubical-experiments";
        src = self;
        nativeBuildInputs = [ shakefile pkgs.pandoc-katex ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
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
