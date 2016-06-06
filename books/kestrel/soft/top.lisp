; SOFT ('Second-Order Functions and Theorems')
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides SOFT ('Second-Order Functions and Theorems'),
; a tool to mimic second-order functions and theorems
; in the first-order logic of ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft

  :parents (acl2::kestrel-books acl2::macro-libraries)

  :short
  "SOFT (&lsquo;Second-Order Functions and Theorems&rsquo;),
  a tool to mimic second-order functions and theorems
  in the first-order logic of ACL2."

  :long

  "<p>
  In SOFT,
  second-order functions are mimicked
  by first-order functions that reference
  explicitly designated uninterpreted functions that mimic function variables.
  First-order theorems over these second-order functions
  mimic second-order theorems universally quantified over function variables.
  Instances of second-order functions and theorems
  are systematically generated
  by replacing function variables with functions.
  Theorem instances are proved automatically,
  via automatically generated
  <see topic='@(url functional-instantiation)'> functional instantiations</see>.
  </p>

  <p>
  SOFT does not extend the ACL2 logic.
  It is a library that provides macros to introduce
  function variables,
  second-order functions,
  second-order theorems,
  and instances thereof.
  The macros modify the ACL2 state
  only by submitting sound and conservative events;
  they cannot introduce unsoundness or inconsistency on their own.
  </p>

  <p>
  The
  <a href='http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3'
  >ACL2 Workshop 2015 paper on SOFT</a>
  provides
  and overview of the macros and some simple examples of their use,
  a description of the use of SOFT in program refinement,
  and a discussion of related and future work.
  The presentation of the Workshop talk is available
  <a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2015/program.html'
  >here</a>.
  The examples from the paper are in
  @('[books]/kestrel/soft/workshop-paper-examples.lisp');
  the examples from the talk that are not in the paper are in
  @('[books]/kestrel/soft/workshop-talk-examples.lisp').
  </p>")
