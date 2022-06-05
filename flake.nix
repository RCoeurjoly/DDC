{
  description = "Declarative debugger for C++";

  # inputs.nixpkgs.url = "nixpkgs/nixos-21.05-small";
  inputs.nixpkgs.url = "nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";

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

        cfg = {  # default configuration
          mysqlPort = "3307";
          mysqlPassword = "admin";
        };

        rootDir   = "/";
        mysqlDir  = "${rootDir}/mysql";
        mysqlConf     = (import ./mysql/config/mysql.conf.nix) {inherit pkgs mysqlDir; mysqlPort = cfg.mysqlPort; };

      packageName = "declarative-debugger-for-cpp";
    in {
      packages.x86_64-linux.${packageName} = app;

      packages.x86_64-linux.default = self.packages.x86_64-linux.quicksort;

      packages.x86_64-linux.quicksort =
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
          nativeBuildInputs = [ pkgs.gdb
                                pkgs.rr
                                self.packages.x86_64-linux.quicksort_benchmarks ];
          installPhase = ''
          mkdir -p $out;
          touch $out/execution_time.txt;
          touch $out/recording_time.txt;
          touch $out/gdb_time.txt;
          touch $out/rr_time.txt;
          for exponent in {1..17}
          do
             input_vector=""
             list_length=$((2 ** $exponent))
             for j in $( eval echo {1..$list_length})
             do
                input_vector+=" $RANDOM"
             done
             for iteration in {1..10}
             do
              START="$(date +%s%N)"
              ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks $input_vector
              DURATION=$[ $(date +%s%N) - $START ]
              echo "$list_length" $DURATION >> $out/execution_time.txt
              START="$(date +%s%N)"
              rr record -o $out/traces_"$exponent"_"$iteration" ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks $input_vector
              DURATION=$[ $(date +%s%N) - $START ]
              echo "$list_length" $DURATION >> $out/recording_time.txt
              START="$(date +%s%N)"
              gdb -x gdb_script ${self.packages.x86_64-linux.quicksort_benchmarks.outPath}/bin/quicksort_benchmarks $input_vector
              DURATION=$[ $(date +%s%N) - $START ]
              echo "$list_length" $DURATION >> $out/gdb_time.txt
              START="$(date +%s%N)"
              rr replay -x gdb_script $out/traces_"$exponent"_"$iteration"
              DURATION=$[ $(date +%s%N) - $START ]
              echo "$list_length" $DURATION >> $out/rr_time.txt
             done
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
          installPhase = "mkdir -p $out/bin; install -t $out/bin car";
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

      packages.x86_64-linux.database =
        # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "database";
          src = self;
          installPhase =
            ''
          mkdir -p $out/db
          mkdir -p $out/db/migrations
          cp ${./mysql/db/schema.sql} $out/db/schema.sql
          cp ${./mysql/db/migrations}/*.sql $out/db/migrations/
          '';
        };

      packages.x86_64-linux.z3 = pkgs.z3;

      packages.x86_64-linux.alea =
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
	        name = "coq${coq.coq-version}-alea";

	        src = fetchFromGitHub {
	          owner = "coq-community";
	          repo = "alea";
	          rev = "v8.12.0";
	          sha256 = "0vpq9yh1v131mpykh8r8javzybapfv65gxqx8palpxhsyid602mj";
	        };

	        propagatedBuildInputs = [ coq ];
	        enableParallelBuilding = true;

          installFlags = [ "COQMF_COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        };

      packages.x86_64-linux.proofs = # Notice the reference to nixpkgs here.
        with import nixpkgs { system = "x86_64-linux"; };
        stdenv.mkDerivation {
          name = "proofs";
          src = self;
          buildInputs = [
            coq
            self.packages.x86_64-linux.alea
          ];
          installFlags = [ "COQMF_COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
        };

      checks.x86_64-linux.rollback =
        pkgs.stdenv.mkDerivation {
          name = "database_up_and_rollback";

          buildInputs = [ self.packages.x86_64-linux.database pkgs.dbmate pkgs.mysql80 ];

          unpackPhase = "true";

          doCheck = true;
          src = ./.;
          preCheck = self.packages.x86_64-linux.database.installPhase;
          doInstallCheck = true;
          postInstallCheckPhase = ''
          export DATABASE_URL="mysql://root:ddc@db/test_rollback"
          if [ -z "$out" ] || [[ $out != /nix* ]]; then
          out="."
          fi

          rm -rf $out/db_*
          dbmate drop
          COUNT=0
          LAST_COUNT=0
          for f in $out/db/migrations/*.sql ; do
              mkdir -p $out/db_$COUNT/migrations
              if [ $COUNT -ne 0 ];  then
                 cp -rf "$out/db_$((COUNT-1))/migrations" "$out/db_$COUNT/"

              fi
              cp "$f" "$out/db_$COUNT/migrations/"
              dbmate --migrations-dir $out/db_$COUNT/migrations --schema-file $out/db_$COUNT/schema.sql up
              cat $out/db_$COUNT/schema.sql
              LAST_COUNT=$COUNT
              COUNT=$((COUNT+1))
          done

          COUNT=$((COUNT-2))

          echo "Testing rollback"
          for ((i=COUNT; i>=0; i--)); do
              LOG_ROOLBACK=$(dbmate --migrations-dir $out/db/migrations --schema-file $out/db_$COUNT/schema.sql rollback)
              echo "$i: $LOG_ROOLBACK"
              diff -u $out/db/schema.sql $out/db_$i/schema.sql
              if [ $? -ne 0 ] ; then
                 echo "Bad rollback on step: $i: $LOG_ROOLBACK"
                 exit 1
              fi
          done

          # Last step
          LOG_ROOLBACK=$(dbmate -d="$out/db/migrations" rollback)
          echo "Last step: $LOG_ROOLBACK"
          RESULT=$(grep "CREATE TABLE" -c $out/db/schema.sql)
          if [  "$RESULT" != "1"  ] ; then
             cat $out/db/schema.sql
             echo "bad last step rollback: $LOG_ROOLBACK"
             exit 1
          fi
          exit 0
              '';

          installPhase = "mkdir -p $out";
        };

      checks.x86_64-linux.schema =
        pkgs.stdenv.mkDerivation {
          name = "database_schema_sql_up_to_date";

          buildInputs = [ self.packages.x86_64-linux.database pkgs.dbmate pkgs.mysql80 pkgs.mysql ];

          unpackPhase = "true";

          doCheck = true;
          src = ./.;
          preCheck = self.packages.x86_64-linux.database.installPhase;
          doInstallCheck = true;
          installCheckPhase = ''
                dbmate --version
                export DATABASE_URL="mysql://root:ddc@db/test_schema"
                mysql -u root -pddc -h 127.0.0.1 -e "DROP DATABASE IF EXISTS test_schema;"
                export DBMATE_MIGRATIONS_DIR="$out"
                dbmate wait
                mysql -u root -pddc -h 127.0.0.1 -e "SET GLOBAL sql_mode='NO_ENGINE_SUBSTITUTION';"
                pwd
                grep -v "^/\*" $out/db/schema.sql  | grep -v "^--" > schema.clean.repo
                dbmate -d="$out/db/migrations" -s="schema_up.sql" up
                grep -v "^/\*" schema_up.sql  | grep -v "^--" > schema.clean.new_generated
                cat schema.clean.repo
                cat schema.clean.new_generated
                diff -q schema.clean.repo schema.clean.new_generated
                cmp -s schema.clean.repo schema.clean.new_generated
              '';

          installPhase = "mkdir -p $out";
        };


      devShells.x86_64-linux.dbmate = pkgs.mkShell {
        buildInputs = with pkgs; [ dbmate mysql80 mysql ];
        # groupadd mysql
        # useradd -r -g mysql -s /bin/false mysql
        # cd mysql
        # mkdir mysql-files
        # chown mysql:mysql mysql-files
        # chmod 750 mysql-files
        # bin/mysqld --initialize --user=mysql
        # bin/mysql_ssl_rsa_setup
        # bin/mysqld_safe --user=mysql &
      };

      devShells.x86_64-linux.dbmate_mysql80 = pkgs.mkShell {
        buildInputs = with pkgs; [ dbmate mysql80 mysql ];
        shellHook = ''

      if test -f ${mysqlDir}/data/mysqld.pid && ps -p $(cat ${mysqlDir}/data/mysqld.pid) > /dev/null; then
        echo "Mysql already started"
      else
        echo "==============   Starting mysql..."
        echo "pour activer logs mysql:"
        echo "start-stop-daemon --stop --pidfile mysql/data/mysqld.pid"
        echo "${pkgs.mysql}/bin/mysqld --defaults-extra-file=${mysqlConf} --general_log=1 --general_log_file=${mysqlDir}/tmp/requests.log &)"
        echo ""
        echo ""
        test -e ${mysqlDir}/data/mysql || (${pkgs.mysql}/bin/mysql_install_db --basedir=${pkgs.mysql} --datadir=${mysqlDir}/data && touch ${mysqlDir}/data/initRequired)
        ${pkgs.mysql}/bin/mysqld --defaults-extra-file=${mysqlConf} &
        test -e ${mysqlDir}/data/initRequired && (echo "Initializing root password..." && sleep 5 && mysqladmin -uroot -h127.0.0.1 -P${cfg.mysqlPort} password "${cfg.mysqlPassword}" && rm -f ${mysqlDir}/data/initRequired)
      fi
    }
  '';

      };

      devShells.x86_64-linux.default = myAppEnv.env.overrideAttrs (oldAttrs: {
        buildInputs = with pkgs; [ gdb
                                   rr
                                   glibc
                                   # csmith
                                   z3
                                   # boogie
                                   coq
                                   coqPackages.mathcomp
                                   # coqPackages.alea
                                   poetry
                                   python39Packages.pylint
                                   python39Packages.autopep8 ] ++ [ self.packages.x86_64-linux.alea ];
      });

      checks.x86_64-linux = {
        # Additional tests, if applicable.
        test = pkgs.stdenv.mkDerivation {
          name = "DDC-test";
          buildInputs = with pkgs; [ python39Packages.pylint ];
          unpackPhase = "true";
          doCheck = true;
          src = ./.;
          doInstallCheck = true;
          installCheckPhase = ''
                pylint declarative_debugger.py
              '';
          installPhase = "mkdir -p $out";
        };
      };

    };
}
