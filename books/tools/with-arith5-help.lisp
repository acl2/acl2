; Copyright (C) 2009-2015, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Authorship note: The above copyright/license info was added by Matt Kaufmann
; on 9/2/2015, after noticing "MattKaufmann authored on Mar 27, 2009" at
; https://github.com/acl2/acl2/commits/master/books/tools/with-arith5-help.lisp.
; Clearly it has been modified since then to add rulesets info.

(in-package "ACL2")

(include-book "rulesets")

(defun check-for-arith5-rulesets (world)
  (let ((ruleset-alist (table-alist 'ruleset-table world)))
    (and (consp (assoc 'arith5-enable-ruleset ruleset-alist))
         (consp (assoc 'arith5-disable-ruleset ruleset-alist)))))

(defconst *allow-arith5-help-form*
  '(local
    (progn

      (defun before-including-arithmetic-5 () nil)

      (table pre-arith5-theory-invariants nil
             (table-alist 'theory-invariant-table world)
             :clear)

      (include-book "arithmetic-5/top" :dir :system)


      (def-ruleset! arith5-enable-ruleset (set-difference-theories
                                           (current-theory :here)
                                           (current-theory
                                            'before-including-arithmetic-5)))

      (def-ruleset! arith5-disable-ruleset (set-difference-theories
                                            (current-theory 'before-including-arithmetic-5)
                                            (current-theory :here)))


      (table post-arith5-theory-invariants nil
             (table-alist 'theory-invariant-table world)
             :clear)

      (table theory-invariant-table nil
             (table-alist 'pre-arith5-theory-invariants world)
             :clear)

      (in-theory (current-theory 'before-including-arithmetic-5)))))

(defun allow-arith5-help-fn (world)
  (if (check-for-arith5-rulesets world)
      '(value-triple :redundant-allow-arith5-help)
    *allow-arith5-help-form*))

(defmacro allow-arith5-help ()
  '(make-event (allow-arith5-help-fn (w state))))

(defmacro my-enable-arith5 (ctx)
  `(if (check-for-arith5-rulesets world)
       (e/d* ((:ruleset arith5-enable-ruleset))
             ((:ruleset arith5-disable-ruleset)))
     (er hard ,ctx
         "~
Run (ALLOW-ARITH5-HELP) in the current local scope before using ~x0.~%" ,ctx)))


(defmacro with-arith5-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-help)))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro with-arith5-nonlinear-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-nonlinear-help)))
     (local (set-default-hints '((nonlinearp-default-hint
                                  stable-under-simplificationp
                                  hist pspv))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro with-arith5-nonlinear++-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-nonlinear++-help)))
     (local (set-default-hints '((nonlinearp-default-hint++
                                  id stable-under-simplificationp
                                  hist nil))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))


(defmacro enable-arith5 ()
  '(my-enable-arith5 'enable-arith5))

;; Notes:

;; This book allows the arithmetic-5 library to be included locally within a book
;; while only affecting (i.e. arithmetically helping and slowing down proofs of)
;; forms that are surrounded by (with-arith5-help  ...).  To allow this,
;; include the following two forms.

;; (include-book "tools/with-arith5-help" :dir :system)
;; (allow-arith5-help)

;; The form (allow-arith5-help) locally includes arithmetic-5/top, then reverts
;; to the pre-existing theory, in support of the with-arith5-help macro.
