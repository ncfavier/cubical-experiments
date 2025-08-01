{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    agda.url = "github:agda/agda";
    agda-stdlib = {
      url = "github:agda/agda-stdlib";
      flake = false;
    };
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
        (final: prev: {
          haskell = prev.haskell // {
            packageOverrides = final.lib.composeExtensions prev.haskell.packageOverrides
              (hfinal: hprev: {
                Agda = final.haskell.lib.enableCabalFlag hprev.Agda "debug";
              });
          };
        })
        (self: super: {
          agdaPackages = super.agdaPackages.overrideScope (aself: asuper: {
            standard-library = asuper.standard-library.overrideAttrs {
              version = "unstable-${inputs.agda-stdlib.shortRev}";
              src = inputs.agda-stdlib;
            };
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

    texlive = pkgs.texlive.combine {
      inherit (pkgs.texlive)
        collection-basic
        collection-latex
        xcolor
        preview
        pgf tikz-cd pgfplots
        mathpazo
        varwidth xkeyval standalone;
    };

    deps = [
      pkgs.pandoc-katex
      texlive
      pkgs.poppler-utils
    ];

    PANDOC_KATEX_CONFIG_FILE = pkgs.writeText "katex-config.toml" ''
      trust = true
      throw_on_error = true

      [macros]
      "\\bN" = "\\mathbb{N}"
      "\\bZ" = "\\mathbb{Z}"
    '';

    shakefile = pkgs.haskellPackages.callCabal2nix "agda-stuff-shake" ./shake {};
  in {
    devShells.${system} = {
      default = self.packages.${system}.default.overrideAttrs (old: {
        nativeBuildInputs = old.nativeBuildInputs or [] ++ [ agda ];
        Agda = pkgs.haskellPackages.Agda; # prevent garbage collection
      });

      shakefile = pkgs.haskellPackages.shellFor {
        packages = _: [ shakefile ];
        nativeBuildInputs = deps ++ [
          pkgs.haskell-language-server
        ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
      };
    };

    packages.${system} = {
      default = pkgs.stdenv.mkDerivation {
        name = "agda-stuff";
        src = self;
        nativeBuildInputs = deps ++ [ shakefile ];
        inherit AGDA_LIBRARIES_FILE PANDOC_KATEX_CONFIG_FILE;
        LC_ALL = "C.UTF-8";
        buildPhase = ''
          agda-stuff-shake
          mv _build/site "$out"
        '';
      };

      inherit shakefile;
    };
  };
}
