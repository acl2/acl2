; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defsection pseudo-tests-and-callsp
  :parents (system-utilities-non-built-in)
  :short "Recognize well-formed @('tests-and-calls') records."
  :long
  "<p>A @('tests-and-call') record is defined as</p>
   @({
     (defrec tests-and-calls (tests . calls) nil)
   })
   <p>(see the ACL2 source code)</p>
   <p>In a well-formed @('tests-and-call') record,
      @('tests') and @('calls') must be lists of terms.</p>
   <p>This recognizer is analogous to @(tsee pseudo-tests-and-callp).</p>"

  (defun pseudo-tests-and-callsp (x)
    (declare (xargs :guard t))
    (case-match x
      (('tests-and-calls tests . calls)
       (and (pseudo-term-listp tests)
            (pseudo-term-listp calls)))
      (& nil))))
