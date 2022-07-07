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

      myAppEnv = pkgs.poetry2nix.mkPoetryEnv {
        projectDir = ./.;
        editablePackageSources = {
          my-app = ./src;
        };
      };

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
        python = pkgs.python39;
        overrides =
          [ pkgs.poetry2nix.defaultPoetryOverrides customOverrides ];
      };

      packageName = "declarative-debugger-for-cpp";
    in {
      packages.x86_64-linux.${packageName} = app;

      packages.x86_64-linux.default =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o quicksort ./quicksort.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort";
        };

      packages.x86_64-linux.test_cases_as_oracle =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "test_cases_as_oracle";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o test_cases_as_oracle ./test_cases_as_oracle.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin test_cases_as_oracle";
        };

      packages.x86_64-linux.non_terminating_quicksort =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "non_terminating_quicksort";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o non_terminating_quicksort ./non_terminating_quicksort.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin non_terminating_quicksort";
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


      packages.x86_64-linux.quicksort_benchmarks =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort_benchmarks";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -o quicksort_benchmarks ./quicksort_benchmarks.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort_benchmarks";
        };

      packages.x86_64-linux.benchmarks =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "benchmarks";
          src = self;
          dontStrip = true;
          buildInputs = [ gdb rr ];
          installPhase = ''
          mkdir -p $out;
          touch $out/execution_time.txt;
          touch $out/recording_time.txt;
          for i in {1..17}
          do
             input_vector=""
             power_i=$((2 ** $i))
             for j in $( eval echo {1..$power_i})
             do
                input_vector+=" $RANDOM"
             done
             START="$(date +%s%N)"
             ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks $input_vector
             DURATION=$[ $(date +%s%N) - $START ]
             echo $power_i $DURATION >> $out/execution_time.txt
             START="$(date +%s%N)"
             #${rr}/bin/rr record ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks $input_vector
             rr record ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks
             DURATION=$[ $(date +%s%N) - $START ]
             echo $power_i $DURATION >> $out/recording_time.txt
          done
          '';
        };


      packages.x86_64-linux.multithreading =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "multithreading";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -I./ -O0 -g -pthread -o multithreading ./multithreading.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin multithreading";
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

      packages.x86_64-linux.car =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "car";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o car ./car.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests car";
        };

      packages.x86_64-linux.fibonacci =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "fibonacci";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o fibonacci ./fibonacci.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests fibonacci";
        };

      packages.x86_64-linux.BST =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "BST";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o BST ./BST.cpp -lstdc++";
          installPhase = "mkdir -p $out/tests; install -t $out/tests BST";
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

      devShell.x86_64-linux = myAppEnv.env.overrideAttrs (oldAttrs: {
        buildInputs = with pkgs; [ gdb rr csmith mercury z3 boogie poetry python39Packages.pylint python39Packages.autopep8 ];
      });

      checks.x86_64-linux = {

        # Additional tests, if applicable.
        test = pkgs.stdenv.mkDerivation {
          name = "DDC-test";

          buildInputs = with pkgs; [ python39Packages.pylint ];

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
