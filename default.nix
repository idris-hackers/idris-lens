# This is used in the Travis build to install the Idris compiler.
let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;
in {
  lens = stdenv.mkDerivation {
    name = "lens";
    src = ./.;
    buildInputs = with pkgs; [ haskellPackages.idris gmp ];
  };
}
