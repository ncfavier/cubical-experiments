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
      buildPhase =  ''
        shopt -s extglob
        for f in src/*.agda src/*.lagda*; do
          agda --html --html-dir="$out" --html-highlight=all --css=style.css --highlight-occurrences "$f"
          mod=''${f%%.@(agda|lagda*)} mod=''${mod##*/}
          cat >> mods << EOF
          <a class="Keyword">import</a> <a href="$mod.html" class="Module">$mod</a>
        EOF
        done
        cp ${self}/{index.html,style.css} "$out"/
        substituteInPlace "$out"/index.html --replace '@modules@' "$(< mods)"
        sed -i 's/getSelectorAll/querySelectorAll/g' "$out"/highlight-hover.js
      '';
    };
  };
}
