let
  pkgs = import <nixpkgs> { };
in
pkgs.mkShell {
  buildInputs = [
    pkgs.llama-cpp
    pkgs.gmp
    # pkgs.ghc
    # pkgs.haskell-language-server
    # pkgs.haskellPackages.fourmolu
    # pkgs.haskellPackages.cabal-fmt
    # # (pkgs.haskell.packages.ghc944.haskell-language-server.override { supportedGhcVersions = [ "944" ]; })
    # pkgs.niv
    # pkgs.cabal2nix
    # pkgs.cabal-install
    # pkgs.hpack
    # pkgs.gcc
    # pkgs.icu
    # pkgs.zlib
    # pkgs.haskellPackages.hspec-discover
    # pkgs.pkg-config
  ];
  shellHook=''
      LD_LIBRARY_PATH="$LD_LIBRARY_PATH:${pkgs.dotnet-sdk.icu}/lib"
  '';

}
