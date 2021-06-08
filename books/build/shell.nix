# This is a Nix shell environment definition that creates a sandbox with all
# programs/libraries needed to build ACL2 and the books.

# Instructions: 1) Install Nix from https://nixos.org/download.html (requires
# sudo).  2) Go to any directory containing this file and run `nix-shell`.
# This will download all of ACL2's dependencies if they are not already cached
# on the system, and then open a shell where those dependencies are made
# available.  Now you can run `make`, `make regression`, etc.

# When you exit the shell, the dependencies will no longer be in your PATH
# etc., but will remain cached on the system.  You can clear the cache with
# `nix-collect-garbage` after exiting the shell to recover disk space if
# necessary.  Note that this will make any ACL2 image or compiled books you
# built in the shell become invalid, as they depend on a now-deleted CCL.

# See https://nixos.org/learn.html for more information.

{ pkgs ? import <nixpkgs> {} }:

with pkgs; let

  # implements http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/?topic=IPASIR____BUILDING-AN-IPASIR-SOLVER-LIBRARY
  libipasirglucose4 = stdenv.mkDerivation rec {
    pname = "libipasirglucose4";
    version = "2017";

    src = fetchurl {
      url = "https://baldur.iti.kit.edu/sat-competition-2017/solvers/incremental/glucose-ipasir.zip";
      sha256 = "0xchgady9vwdh8frmc8swz6va53igp2wj1y9sshd0g7549n87wdj";
    };
    sourceRoot = "sat/glucose4";

    patches = [(writeText "patch" ''
      --- /makefile
      @@ -32,1 +32,2 @@
      -CXXFLAGS= -g -std=c++11 -Wall -DNDEBUG -O3
      +CXXFLAGS= -g -std=c++11 -Wall -DNDEBUG -O3 -fPIC
      +export CXXFLAGS
      @@ -70,1 +71,1 @@
      -	$(CXX) -g  -std=c++11 $(CXXLAGS) \
      +	$(CXX) -g  -std=c++11 $(CXXFLAGS) \
    '')];

    nativeBuildInputs = [ unzip ];
    buildInputs = [ zlib ];

    postBuild = ''
      g++ -shared -Wl,-soname,libipasirglucose4.so -o libipasirglucose4.so \
          ipasirglucoseglue.o libipasirglucose4.a
    '';

    installPhase = ''
      install -D libipasirglucose4.so $out/lib/libipasirglucose4.so
    '';
  };

in mkShell rec {
  buildInputs = [
    ccl git # for ACL2 system
    which perl nettools # for any books
    openssl.out glucose minisat abc-verifier libipasirglucose4 # for quicklisp, satlink, etc.
    z3 (python2.withPackages (ps: [ ps.z3 ])) # for smtlink
  ];
  shellHook = ''
    export LD_LIBRARY_PATH=${stdenv.lib.makeLibraryPath [ openssl.out libipasirglucose4 ]}
  '';
}
