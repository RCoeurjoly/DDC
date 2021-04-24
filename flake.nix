{
  description = "A flake for building quicksort";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }: {

    defaultPackage.x86_64-linux =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation {
        name = "quicksort";
        src = self;
        buildPhase = "gcc -g -o quicksort ./quicksort.cpp";
        installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort";
      };

  };
}
