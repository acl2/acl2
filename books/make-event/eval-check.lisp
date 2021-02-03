; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (sometime before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This was originally a modification of community book misc/eval.lisp (now
; std/testing/eval.lisp) that uses :check-expansion t.  Now, std/testing/eval.lisp
; provides utilities with a :check-expansion option, which is used in this file
; to create "!" versions of the macros that check expansions, leave output on,
; and generally leave ld-skip-proofsp alone, to obtain behavior originally (and
; still) tested in eval-check-tests.lisp.  One can similarly define one's own
; "!" versions, rather than including the present book.

(in-package "ACL2")

(include-book "std/testing/eval" :dir :system)
(include-book "xdoc/top" :dir :system) ; redundant

(defmacro must-eval-to! (form expr)
  `(must-eval-to ,form ,expr
                 :with-output-off nil
                 :check-expansion t))

(defmacro must-eval-to-t! (form)
  `(must-eval-to! ,form t))

(defmacro must-succeed! (form)
  `(must-succeed ,form
                 :with-output-off nil
                 :check-expansion t))

(defxdoc must-succeed!
  :parents (errors)
  :short "A variant of @(tsee must-succeed)"
  :long "<p>See @(see must-succeed).  @('Must-succeed!') is a convenient
 wrapper for calling @('must-succeed') using @(':with-output-off nil') and
 @(':check-expansion t').</p>")

(defmacro must-fail! (form)
  `(must-fail ,form
              :with-output-off nil
              :check-expansion t))

(defxdoc must-fail!
  :parents (errors)
  :short "A variant of @(tsee must-fail) suitable for inclusion in books"
  :long "<p>See @(see must-fail), including the ``CAVEAT'' about an issue with
 the use of @('must-fail') in @(see books), which can be solved by using
 @('must-fail!').  @('Must-fail!') is a convenient wrapper for calling
 @('must-fail') using @(':with-output-off nil') and @(':check-expansion
 t').</p>")
