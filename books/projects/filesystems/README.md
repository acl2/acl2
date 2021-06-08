This ACL2 project demonstrates the verification of a model of the
FAT32 filesystem and the development of code proofs based on formal
descriptions of FAT32 system calls. Details about this project are
available in the papers "Formalising Filesystems in the ACL2 Theorem
Prover: an Application to FAT32" (in the proceedings of the 15th
International Workshop on the ACL2 Theorem Prover and Its
Applications) and "Binary-Compatible Verification of Filesystems with
ACL2" (in the proceedings of the Tenth International Conference on
Interactive Theorem Proving).

These ACL2 books have been certified with a development version of
ACL2 (https://github.com/acl2/acl2), identified by commit
568ff7a813b33660b89b7a9a4bbb8aa0f97c0217. In addition to certifiable
books, there is a co-simulation test suite in the test/
subdirectory. The GNU/Linux programs mkfs.fat, diff, sudo, cp, mkdir,
mv, rm, rmdir, stat, truncate, unlink, and wc are required in order to
run the tests, as is the mtools suite of programs (version 4.0.18).

The FAT32 models HiFAT and LoFAT depend on a number of helper
functions and lemmas in other files; the cert.pl utility distributed
with ACL2 is useful in tracking and building these dependencies. The
shell command below certifies all the filesystem models, assuming
proper substitutions for ACL2_DIR (the directory containing ACL2) and
ACL2 (the ACL2 executable, likely to be $ACL2/saved_acl2) below.

$ ACL2_DIR/books/build/cert.pl --acl2 ACL2 *.lisp

This certification must be completed before attempting the co-simulation
tests, which are located in the test/ subdirectory. This subdirectory
has its own Makefile, which can be invoked as follows, again
substituting a proper value for ACL2.

$ cd test; sudo make ACL2=ACL2 test

This should run a number of tests built on LoFAT against the actual
programs from the Coreutils and the mtools. These include
co-simulation tests for the ls and rm programs, and proofs about the
interaction of these programs can be found in the file
ls-rm-example.lisp. Another proof which displays the model's ablility
to reason about file contents can be found in the file
wc-truncate-example.lisp, which states that after truncation of a
given file to a given size, running wc -c on that same file will
return that same size.

sudo is required for mounting and unmounting the disk images involved
in these tests; thus, root privileges on the testing machine are
required. Installation note: these tests are known to work with an ACL2 built atop
Clozure Common Lisp (CCL). At least one other Common Lisp
implementation (SBCL) causes some tests to fail, on account of
inconsistent handling of command line arguments by
[oslib::argv](http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/?topic=OSLIB____ARGV). The
ACL2 installation page points to instructions for
[obtaining](http://www.cs.utexas.edu/users/moore/acl2/v8-2/HTML/installation/requirements.html#Obtaining-CCL)
and
[installing](http://www.cs.utexas.edu/users/moore/acl2/v8-2/HTML/installation/ccl.html)
CCL.
