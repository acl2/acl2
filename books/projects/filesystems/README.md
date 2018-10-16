This is the accompanying artefact submission for the paper titled
"Formalising filesystems in the ACL2 theorem prover: an application to
FAT32". The paper details certain filesystem models and co-simulation
tests applied to them; instructions for reviewing and executing these
tests follow.

Note: The books mentioned below were certified with a development
snapshot of ACL2, dated 2018-07-23 and identified by commit hash
1593cfb3df6a592f9a2bf3a8fe4b30430ac06fba. The GNU/Linux programs
mkfs.fat, cp, diff, and sudo are required in order to run the tests.

Abstract models L1 through L6 can be found in the files
file-system-1.lisp through file-system-6.lisp, and concrete models M1
and M2 can be found in files file-system-m1.lisp and
file-system-m2.lisp respectively. These depend on a number of helper
functions and lemmas in other files; the cert.pl utility distributed
with ACL2 is useful in tracking and building these dependencies. Thus,
the shell command provided on the conference homepage is adapted for
the purpose of certifying all the filesystem models, assuming proper
substitutions for ACL2_DIR and ACL2 below.

$ ACL2_DIR/books/build/cert.pl --acl2 ACL2 file-system-*.lisp

This must be run before attempting the tests, which are located in the
test/ subdirectory. This subdirectory has its own Makefile, which can
be invoked as follows, again substituting a proper value for ACL2.

$ cd test; sudo make ACL2=ACL2 test

This should run a number of tests built on the FAT32 model (M2)
against the actual programs mkfs.fat and cp. mkfs.fat versions 3.0.28
and 3.0.20 are supported; the former is configured by default, while
the latter can be configured with some changes to the Makefile. sudo is
required for mounting and unmounting the disk images involved in these
tests; thus, root privileges on the testing machine are
required. Implementation details can be found in the "Co-simulation"
section of the accompanying paper.
