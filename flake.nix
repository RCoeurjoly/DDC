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

      # DON'T FORGET TO PUT YOUR PACKAGE NAME HERE, REMOVING `throw`
      packageName = "poetry-test";
    in {
      packages.x86_64-linux.${packageName} = app;

      defaultPackage.x86_64-linux =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "quicksort";
          src = self;
          dontStrip = true;
          buildPhase = "gcc -O0 -g -o quicksort ./quicksort.cpp -lstdc++";
          installPhase = "mkdir -p $out/bin; install -t $out/bin quicksort";
        };

      devShell.x86_64-linux = pkgs.mkShell {
        inputsFrom = builtins.attrValues self.packages.x86_64-linux;
        buildInputs = with pkgs; [ gdb rr poetry python3Packages.pylint python3Packages.autopep8 ];
      };

      checks.x86_64-linux = {

        # Additional tests, if applicable.
        test = pkgs.stdenv.mkDerivation {
          name = "DDC-test";

          buildInputs = with pkgs; [ python3Packages.pylint ];

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
