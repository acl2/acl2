; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (sometime before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This was originally a modification of community book misc/eval.lisp that uses
; :check-expansion t.  Now, misc/eval.lisp provides utilities with a
; :check-expansion option, which is used in this file to create "!" versions of
; the macros that check expansions, leave output on, and generally leave
; ld-skip-profosp alone, to obtain behavior originally (and still) tested in
; eval-check-tests.lisp.  One can similarly define one's own "!" versions,
; rather than including the present book.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

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

(defmacro must-fail! (form)
  `(must-fail ,form
              :with-output-off nil
              :check-expansion t))
