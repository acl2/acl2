Copyright (C) 2018, ARM Holdings
Written by David Russinoff
License: A 3-clause BSD license.  See the LICENSE file distributed with
ACL2.

RAC: Restricted Algorithmic C
====================================

Documentation
-------------

  RAC is described in Chapter 15 of the book

    Russinoff, D.M., Formal Verification of Floating-Point Hardware Design:
    A Mathematical Approach, Springer, 2nd edition, 2022.

Contents of this Directory
--------------------------

This directory contains this README, Makefile, and the following subdirectories:

  src

    Makefile; the parser source files parser.*, output.c, and main.c; and
    rac-skel, which generates the script bin/rac.  Compilation produces some
    other stuff via Flex/Bison.

  bin

    Initially empty.  Compilation produces the rac script and the parser executable.

  lisp

    Makefile and translate.lisp, which converts the output of the parser to
    ACL2 code.  Compilation produces translate.cert.

    internal-fns-gen.lisp consists of two tools, CONST-FNS-GEN and
    LOOP-FNS-GEN, for generating functions that compute values of
    local (bound) variables of an input function.  CONST-FNS-GEN is
    applicable to functions with non-recursive definitions, while
    LOOP-FNS-GEN can be applied to certain functions with restricted
    recursive definitions.

  include

    rac.h, which must be included in any RAC program, and the Algorithmic C header
    files ac_int.h and ac_fixed.h.

  examples

    Two simple examples of RAC programs, as described in examples/README.


Compiling RAC
-------------

  Compilation requires ACL2 and a reasonably recent version of g++ supporting
  C++17 (version 9.4 works fine).

  Edit Makefile so that ACL2 points to the local distribution of ACL2 (where
  the saved_acl2 is to be found) and RAC points to the current directory (which
  is normally the subdirectory books/projects/rac of the ACL2 directory).

  Then,

    make

  After compilation, 'make clean' removes temporary files (lex.yy.c and the like).
  'make veryclean' removes all that was generated, e.g., binaries and ACL2 books.

Structure of a RAC Program
--------------------------

  Every RAC program should contain

    #include <rac.h>

  possibly preceded by one of these two lines

    #include <ac_int.h>
    #include <ac_fixed.h>

  as needed.

  Every program must also contain the delimiting comments

    // RAC begin

    ...

    // RAC end

  A program may contain any compilable C++ code, but the code between these
  comments, which is the input to the RAC parser, must conform to the RAC
  restrictions.

Parsing, pretty-printing, and translating RAC programs
------------------------------------------------------

  The script bin/rac is invoked in one of the following ways:

    rac prog

      Check prog.cpp for conformance to the RAC subset and programming
      conventions.  This also performs g++ pre-processing, which resolves
      file inclusions, etc., and generates the file prog.i.

    rac -r prog

      Create prog.i, extract the RAC code (between the 'RAC begin' and
      RAC end' delimiters) and pretty-print it. The pretty-printed
      output is not parsable RAC code, but it looks better on slides and
      in documentation.  Unfortunately, the pretty-printer is not smart
      enough to preserve comments.

    rac -a prog

      Create prog.i, translate the RAC code into a set of ACL2 function
      definitions, and certify the definitions as an ACL2 book.
      The translation is a two-step process: (1) the parser produces a
      set of S-expressions in the file prog.ast.lisp, and (2) the ACL2
      program translate.lisp converts these to a set of ACL2 functions in
      prog.lisp and certifies that file.  If this process succeeds, the file
      prog.cert is created.  If not, the file prog.acl2.log should provide
      clues to the cause of failure.

  In case of bug of the parser (like when an error is reported but the code is
  valid), it is possible to define RAC_BYPASS_ERROR environement variable to
  any value. The errors will be still reported, but will not make the parser
  fails (but crashes and failed assertions can still happen !). In that case,
  be extra carefull and check the translation as anything can happen,
  especially if it is a type related error.

  To enable extra checks (to avoid possible mistranslation and undefined
  behavior), define RAC_EXTRA_FLAGS=-pedantic. Note with this flags, "good
  enough" program can fails to compile.


Compiling RAC programs for simulation
--------------------------------------

  This should do the trick:

    g++ -std=c++14 -I <this directory>/include prog.cpp


Testing and debuging
--------------------

  To know how to run the regression test, see tests/README.md. Even if thoose
  tests should covered most parts of the parse, it a good idea to test the
  translations on some real life models (like the ones in examples).

  By default, the parser will be compile in release mode (with all
  optimisation and without the debuging symbols), to debug use 'make debug'.

  For more in depth debuging, the -dump-ast is really usefull to understand
  what's happening. For now, it only display the name of the nodes and the
  expression's types. Fell free to add more information if needed. Also, the
  "diagnostics" can be really usefull to know which parts of the input code
  cause a bug.

TODOs and possible ameliorations
-------------------------------

  Here a non-exautive list of possible ameliorations:

    * generalize template
    * generate a list of type usable in Lisp to generate bvecthm for each
      extracted functions.
    * continue to refactore and clean up the code, bison in C++ mode
    * improve the display of location for typedef types.


Contact
-------

  David Russinoff     david@russinoff.com
  John O'Leary        john.w.oleary@intel.com
