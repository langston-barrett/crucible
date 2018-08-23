{ pkgs ? import ./pinned-pkgs.nix { } }:

with pkgs;
let what4 = haskellPackages.callCabal2nix "what4" ./. { };
    # nix-shell -p nix-prefetch-git --run
    # "GHN=galois-haskell-nix nix-prefetch-git https://github.com/siddharthist/$GHN > $GHN.json"
    gpkgs_json = builtins.fromJSON (builtins.readFile ./galois-haskell-nix.json);
    gpkgs = import (fetchFromGitHub {
      inherit (gpkgs_json) rev sha256;
      owner = "siddharthist";
      repo = "galois-haskell-nix";
    }) { };
in stdenv.mkDerivation {
  name = "what4-shell";
  src = lib.sourceFilesBySuffices ./. [ ".cabal" ".hs" ];
  shellHook = ''
    # Get a purer shell by unsetting HOME
    tmp=$(mktemp -d -p /run/user/$(id -u $(whoami)))
    export HOME=$tmp
    cd $HOME

    # But still retain just a few configs
    ln -s /home/siddharthist/.emacs.d .
    ln -s /home/siddharthist/.spacemacs .
    ln -s /home/siddharthist/.gitconfig .
    ln -s /home/siddharthist/.zshrc .
    ln -s /home/siddharthist/.zsh_history .

    cd -
  '';
  buildInputs = [
    (haskell.packages.ghc843.ghcWithPackages (hpkgs: with hpkgs; [
      cabal-install
      hoogle
      hlint
      hindent
      # ghc-mod
      # hasktags
      stack
    # ]))
    # ] ++ what4.buildInputs ++
    #      what4.propagatedBuildInputs))
    ] ++ gpkgs.haskellPackages.what4.buildInputs ++
         gpkgs.haskellPackages.what4.propagatedBuildInputs))
    git
    emacs
    zsh
  ];
}
