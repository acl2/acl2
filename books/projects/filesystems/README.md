This is the accompanying artefact submission for the paper titled
"Binary-compatible verification of filesystems with ACL2". The paper
details certain filesystem models and co-simulation tests applied to
them; instructions for reviewing and executing these tests follow.

Note: The books mentioned below were certified with a development
snapshot of ACL2, dated 2019-03-28 and identified by commit hash
9a0cae90792ee68add705b782b5f3cde1170b94e. The GNU/Linux programs
mkfs.fat, diff, sudo, cp, mkdir, mv, rm, rmdir, stat, unlink, and wc
are required in order to run the tests, as is the mtools suite of
programs (version 4.0.18).

The FAT32 models HiFAT and LoFAT can be found in files hifat.lisp and
lofat.lisp respectively. These depend on a number of helper
functions and lemmas in other files; the cert.pl utility distributed
with ACL2 is useful in tracking and building these dependencies. The
shell command below certifies all the filesystem models, assuming
proper substitutions for ACL2_DIR and ACL2 below.

$ ACL2_DIR/books/build/cert.pl --acl2 ACL2 file-system-*.lisp

This must be run before attempting the tests, which are located in the
test/ subdirectory. This subdirectory has its own Makefile, which can
be invoked as follows, again substituting a proper value for ACL2.

$ cd test; sudo make ACL2=ACL2 test

This should run a number of tests built on LoFAT against the actual
programs from the Coreutils and the mtools. mkfs.fat versions 3.0.28
and 3.0.20 are supported; the former is configured by default, while
the latter can be configured with some changes to the Makefile. sudo is
required for mounting and unmounting the disk images involved in these
tests; thus, root privileges on the testing machine are
required. Implementation details can be found in the "Co-simulation"
section of the accompanying paper.
