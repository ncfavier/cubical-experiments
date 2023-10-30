{
  inputs = {
    nixpkgs.url = "nixpkgs/haskell-updates";
  };

  outputs = { self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
  in {
    packages.${system}.default = pkgs.stdenv.mkDerivation {
      name = "cubical-experiments";
      src = self;
      nativeBuildInputs = with pkgs; [
        (agda.withPackages (p: with p; [ cubical _1lab ]))
      ];
      LC_ALL = "C.UTF-8";
      extraHead = ''
        <meta name="author" content="Naïm Favier">
        <meta name="viewport" content="width=device-width, initial-scale=1, user-scalable=yes">
        <link rel="icon" type="image/png" href="//monade.li/favicon.png">
      '';
      buildPhase = ''
        shopt -s extglob
        for f in src/*.agda src/*.lagda*; do
          mod=''${f%%.@(agda|lagda*)} mod=''${mod##*/}
          if grep -qE 'import *(1Lab|Cat)\.' "$f"; then
            echo "import $mod" >> Everything-1Lab.agda
          else
            echo "import $mod" >> Everything.agda
          fi
          cat >> mods << EOF
        <a class="Keyword">import</a> <a href="$mod.html" class="Module">$mod</a>
        EOF
        done
        agda -i . --html --html-dir="$out" --html-highlight=all --css=style.css --highlight-occurrences Everything.agda
        agda -i . --html --html-dir="$out" --html-highlight=all --css=style.css --highlight-occurrences Everything-1Lab.agda
        substituteInPlace "$out"/highlight-hover.js --replace getSelectorAll querySelectorAll
        substituteInPlace "$out"/*.html --replace '</head>' "$extraHead</head>"
        cp ${self}/{index.html,style.css} "$out"/
        substituteInPlace "$out"/index.html --subst-var-by modules "$(< mods)"
      '';
    };
  };
}
