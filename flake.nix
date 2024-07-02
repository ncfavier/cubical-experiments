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
  in {
    packages.${system}.default = pkgs.stdenv.mkDerivation {
      name = "cubical-experiments";
      src = self;
      nativeBuildInputs = with pkgs; [
        (agda.withPackages (p: with p; [
          cubical
          _1lab
        ]))
        htmlq
      ];
      LC_ALL = "C.UTF-8";
      postHead = ''
        <meta name="author" content="Naïm Favier">
        <meta name="viewport" content="width=device-width, initial-scale=1, user-scalable=yes">
        <link rel="icon" type="image/png" href="//monade.li/favicon.png">
      '';
      preBodyInternal = ''
        <h3>
          <a href="/">index</a> ∙
          <a href="https://github.com/ncfavier/cubical-experiments/blob/main/@MODULE@">source</a>
        </h3>
      '';
      preBodyExternal = ''
        <h3><a href="/">index</a></h3>
        <p style="border-left: 5px solid #facc15; padding: 1rem;">
          ⚠️ This module is not part of this project and is only included for reference.<br>
          It is either part of the <a href="https://1lab.dev">1lab</a>, the <a href="https://github.com/agda/cubical">cubical</a> library, or a built-in Agda module.
        </p>
      '';
      buildPhase = ''
        shopt -s extglob nullglob
        for f in src/*.agda src/*.lagda*; do
          base=''${f##*/} mod=''${base%%.@(agda|lagda*)}
          if grep -qE 'import *(1Lab|Cat)\.' "$f"; then
            echo "import $mod" >> Everything-1Lab.agda
          else
            echo "import $mod" >> Everything.agda
          fi
        done
        agda -i . --html --html-dir="$out" --html-highlight=all --css=style.css --highlight-occurrences Everything.agda
        agda -i . --html --html-dir="$out" --html-highlight=all --css=style.css --highlight-occurrences Everything-1Lab.agda
        for f in "$out"/*.html; do
          base=''${f##*/} mod=''${base%%.html}
          printf -v mod %b "''${mod//%/'\x'}"
          src=(src/"$mod".@(agda|lagda*))
          if (( ''${#src} )); then
            substituteInPlace "$f" \
              --replace-fail '</head>' "$postHead</head>" \
              --replace-fail '<body>' "<body>''${preBodyInternal/@MODULE@/"''${src[0]}"}"
          else
            substituteInPlace "$f" \
              --replace-fail '</head>' "$postHead</head>" \
              --replace-fail '<body>' "<body>$preBodyExternal"
          fi
        done
        cp ${self}/{index.html,style.css} "$out"/
        modules=$(for e in Everything-1Lab Everything; do htmlq pre.Agda -f "$out/$e.html"; done)
        substituteInPlace "$out"/index.html --subst-var-by modules "$modules"
      '';
    };
  };
}
