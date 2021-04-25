with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "quicksort";
  src = ./.;
  dontStrip = true;

  buildInputs = [ gdb ];

  buildPhase = "gcc -g -o quicksort quicksort.cpp";

  installPhase = ''
    mkdir -p $out/bin
    cp quicksort $out/bin/
  '';
}
