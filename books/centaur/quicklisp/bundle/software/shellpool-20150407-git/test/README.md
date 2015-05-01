Shellpool Tests
===============

These are tests that can be run to see if Shellpool seems to be working.

These tests may be especially useful when

  - making changes to Shellpool source code, or
  - porting Shellpool to other Lisps or operating systems.

Note that these tests require some software that is not required by Shellpool
itself, but which is likely to be available for your system.  For instance, the
tests make use of a few [Perl](http://www.perl.org/) scripts.

Basic usage is just, e.g., `ccl < top.lisp`.  Failures should be obvious, and
on success, it should eventually `All tests passed.`

Current test suite:

 - **basic.lisp** has some tests of basic return code, opcode capture, and
   distinguishing between stdout/stderr.  It also has a few trivial attempts to
   "break" Shellpool (unbalanced parens, quotes, etc.)

 - **kill.lisp** has tests of graceful interruption.  It tries to ensure that
   subprograms can be killed and that Shellpool is still functional after
   killing has occurred.

TODO list:

 - Basic tests of background commands







