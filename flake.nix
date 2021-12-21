{
  description = "Declarative debugger for C++";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;

      customOverrides = self: super: {
        # Overrides go here
      };

      app = pkgs.poetry2nix.mkPoetryApplication {
        projectDir = ./.;
        overrides =
          [ pkgs.poetry2nix.defaultPoetryOverrides customOverrides ];
      };

      packageName = "declarative-debugger-for-Cpp";
    in {
      packages.x86_64-linux.${packageName} = app;

      defaultPackage.x86_64-linux =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o quicksort ./quicksort.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort";
        };

      packages.x86_64-linux.test =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o test_quicksort ./test_quicksort.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests test_quicksort";
        };

      packages.x86_64-linux.palindrome =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "palindrome";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o palindrome ./palindrome.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests palindrome";
        };

      # devShell.x86_64-linux = pkgs.poetry2nix.mkPoetryEnv {
      #   # inputsFrom = builtins.attrValues self.packages.x86_64-linux;
      #   projectDir = ./.;
      #   # buildInputs = with pkgs; [ gdb rr poetry python3Packages.pylint python3Packages.autopep8 ];
      # };

      devShell.x86_64-linux = pkgs.mkShell {
        inputsFrom = builtins.attrValues self.packages.x86_64-linux;
        buildInputs = with pkgs; [ python38 gdb rr poetry python38Packages.pylint python38Packages.autopep8 ];
      };

      checks.x86_64-linux = {

        # Additional tests, if applicable.
        test = pkgs.stdenv.mkDerivation {
          name = "DDC-test";

          buildInputs = with pkgs; [ python38Packages.pylint ];

          unpackPhase = "true";

          doCheck = true;
          src = ./.;
          # preCheck = self.defaultPackage.x86_64-linux.installPhase;
          doInstallCheck = true;
          installCheckPhase = ''
                pylint declarative_debugger.py
              '';

          installPhase = "mkdir -p $out";
        };
      };
    };
}
