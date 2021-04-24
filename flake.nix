{
  description = "A flake for building quicksort";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-20.03;

  outputs = { self, nixpkgs }: {

    defaultPackage.x86_64-linux =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation {
        name = "quicksort";
        src = self;
        buildPhase = "gcc -o quicksort ./quicksort.cpp";
        installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort";
      };

  };
}
