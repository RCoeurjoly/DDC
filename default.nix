with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "quicksort";
  src = ./.;
  dontStrip = true;

  buildInputs = [ gdb python3 rr];

  buildPhase = "gcc -g -o quicksort quicksort.cpp -lstdc++";

  installPhase = ''
    mkdir -p $out/bin
    cp quicksort $out/bin/
  '';
}
