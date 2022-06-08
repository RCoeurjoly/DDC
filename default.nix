with import <nixpkgs> {};

let
  ncoq = coq_8_10;
  ncoqPackages = coqPackages_8_10;
  ceres = ncoqPackages.callPackage
    ( { coq, stdenv, fetchFromGithub }:
      stdenv.mkDerivation {
	name = "coq${coq.coq-version}-ceres";

	src = fetchFromGitHub {
	  owner = "Lysxia";
	  repo = "coq-ceres";
	  rev = "4e682cf97ec0006a9d5b3f98e648e5d69206b614";
	  sha256 = "0n3bjsh7cb11y3kv467m7xm0iygrygw7flblbcngklh4gy5qi5qk";
	};

	buildInputs = with coq.ocamlPackages; [ ocaml camlp5 ];
	propagatedBuildInputs = [ coq ];
	enableParallelBuilding = true;

	installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
      } ) { } ;
in
stdenv.mkDerivation {
  name = "coq${coq.coq-version}-vellvm";

  src = fetchGit {
    url = "https://github.com/vellvm/vellvm";
  };

  buildInputs = [ git ncoq ocamlPackages.menhir dune ncoqPackages.flocq
		  ncoqPackages.coq-ext-lib ncoqPackages.paco ceres ocaml ];

  buildPhase = ''
      cd src && make
  '';

  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
}
