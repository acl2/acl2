This is the accompanying artefact submission for the paper titled
"Binary-compatible verification of filesystems with ACL2". The paper
details certain filesystem models and co-simulation tests applied to
them; instructions for reviewing and executing these tests follow.

Note: The books mentioned below were certified with a development
snapshot of ACL2, dated 2019-03-30 and identified by commit hash
d7e8dac3dd41c8b46281b5f26e09f108dbf995fb. The GNU/Linux programs
mkfs.fat, diff, sudo, cp, mkdir, mv, rm, rmdir, stat, unlink, and wc
are required in order to run the tests, as is the mtools suite of
programs (version 4.0.18).

The FAT32 models HiFAT and LoFAT can be found in files hifat.lisp and
lofat.lisp respectively. These depend on a number of helper
functions and lemmas in other files; the cert.pl utility distributed
with ACL2 is useful in tracking and building these dependencies. The
shell command below certifies all the filesystem models, assuming
proper substitutions for ACL2_DIR (the directory containing ACL2) and
ACL2 (the ACL2 executable, likely to be $ACL2/saved_acl2) below.

$ ACL2_DIR/books/build/cert.pl --acl2 ACL2 file-system-*.lisp

Alternatively, the filesystem models can be certified through the
normal process of building the ACL2 books, explained on the ACL2
[installation
page](http://www.cs.utexas.edu/users/moore/acl2/v8-1/HTML/installation/installation.html). The
"make certify-books" command in step 4 will build the filesystem
books; this is simpler than using cert.pl although it takes longer.

Either way, the certification must be completed before attempting the
tests, which are located in the test/ subdirectory. This subdirectory
has its own Makefile, which can be invoked as follows, again
substituting a proper value for ACL2.

$ cd test; sudo make ACL2=ACL2 test

This should run a number of tests built on LoFAT against the actual
programs from the Coreutils and the mtools. mkfs.fat versions 3.0.28
and 3.0.20 are supported; the former is configured by default while
the latter can be configured with some changes to the Makefile. sudo is
required for mounting and unmounting the disk images involved in these
tests; thus, root privileges on the testing machine are
required. Implementation details can be found in the "Co-simulation"
subsection of the accompanying paper.

Installation note: these tests are known to work with an ACL2 built atop
Clozure Common Lisp (CCL). At least one other Common Lisp
implementation (SBCL) causes some tests to fail, on account of
inconsistent handling of command line arguments by
[oslib::argv](http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=OSLIB____ARGV). The
ACL2 installation page points to instructions for
[obtaining](http://www.cs.utexas.edu/users/moore/acl2/v8-1/HTML/installation/requirements.html#Obtaining-CCL)
and
[installing](http://www.cs.utexas.edu/users/moore/acl2/v8-1/HTML/installation/ccl.html)
CCL.

A brief listing of functions and theorems mentioned in the paper
follows.
* The function lofat-fs-p is in lofat.lisp.
* The functions lofat-to-hifat-helper and lofat-to-hifat are in
lofat.lisp.
* The functions hifat-subsetp and hifat-equiv are in hifat-equiv.lisp.
* The functions lofat-equiv and eqfat are in lofat.lisp.
* The equivalence proofs hifat-to-lofat-inversion,
lofat-to-hifat-inversion, lofat-to-string-inversion,
string-to-lofat-inversion and string-to-m1-fs-inversion are in
lofat.lisp. Note, string-to-m1-fs-inversion has been renamed to
string-to-hifat-inversion for consistency with the other functions.
* The LoFAT implementations of the various system calls are in
lofat.lisp; the HiFAT implementations are in hifat-syscalls.lisp.
* An ACL2 program for checking disk equivalence is mentioned in the
"Co-simulation" subsection; this is test/compare-disks.lisp. A proof
of its correspondence with the equivalence relation eqfat is in the
theorem compare-disks-correctness-1 in test-stuff.lisp.
* Two optimizations are mentioned in the "Performance" subsection; they
are implemented in the functions disk-image-to-lofat and
lofat-to-disk-image in lofat.lisp.
* Finally, all co-simulation tests, along with the ACL2 programs used
for each, are enumerated in test/Makefile.