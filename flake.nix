{
  description = "Declarative debugger for C++";

  inputs = {
    # nixpkgs.url = "github:RCoeurjoly/nixpkgs";
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;

      customOverrides = self: super: {
        # Overrides go here
        tomli = super.tomli.overridePythonAttrs (
          old: {
            buildInputs = (old.buildInputs or [ ]) ++ [ self.flit-core ];
          }
        );

        typing-extensions = super.typing-extensions.overridePythonAttrs (
          old: {
            buildInputs = (old.buildInputs or [ ]) ++ [ self.flit-core ];
          }
        );

        platformdirs = super.platformdirs.overridePythonAttrs (
          old: {
            postPatch = ''
          substituteInPlace setup.py --replace 'setup()' 'setup(version="${old.version}")'
        '';
          }
        );

        black = super.black.overridePythonAttrs (
          old: {
            buildInputs = (old.buildInputs or [ ]) ++ [ self.flit-core self.platformdirs ];
          }
        );
      };

      app = pkgs.poetry2nix.mkPoetryApplication {
        projectDir = ./.;
        python = pkgs.python38;
        overrides =
          [ pkgs.poetry2nix.defaultPoetryOverrides customOverrides ];
      };

      packageName = "declarative-debugger-for-cpp";
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

      packages.x86_64-linux.quicksort_wrong_bt =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort_wrong_bt";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o quicksort_wrong_bt ./quicksort_wrong_bt.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort_wrong_bt";
        };

      packages.x86_64-linux.test_quicksort =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "test_quicksort";
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

      packages.x86_64-linux.quicksort_array =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort_array";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o quicksort_array ./quicksort_array.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests quicksort_array";
        };


      devShell.x86_64-linux = pkgs.mkShell {
        inputsFrom = builtins.attrValues self.packages.x86_64-linux;
        buildInputs = with pkgs; [ python38 gdb rr z3 boogie poetry python38Packages.pylint python38Packages.autopep8 ];
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
