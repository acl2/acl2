; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; WARNING: If you want to use both the arithmetic/ and arithmetic-5/ libraries,
; evaluate (allow-arith-help) after including the book with-arith-help.lisp.

; This book is an adaptation of with-arith5-help.lisp book to
; arithmetic/top-with-meta.lisp.  However, it is coded in a way that allows its
; functionality minus inclusion of the book above; see with-arith-help.

(in-package "ACL2")

(include-book "rulesets")

(defun check-for-arith1-rulesets (world)
  (let ((ruleset-alist (table-alist 'ruleset-table world)))
    (and (consp (assoc 'arith1-enable-ruleset ruleset-alist))
         (consp (assoc 'arith1-disable-ruleset ruleset-alist)))))

(defconst *allow-arith1-help-form*

; This is like *allow-arith5-help-form*, except that it does not actually
; include the relevant book or set the theory at the end.

  '(local
    (progn

      (defun before-including-arithmetic-1 () nil)

      (make-event
       '(table pre-arith1-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear))

      (local (include-book "arithmetic/top-with-meta" :dir :system))

      (make-event
       '(def-ruleset! arith1-enable-ruleset (set-difference-theories
                                             (current-theory :here)
                                             (current-theory
                                              'before-including-arithmetic-1))))

      (make-event
       '(def-ruleset! arith1-disable-ruleset (set-difference-theories
                                              (current-theory 'before-including-arithmetic-1)
                                              (current-theory :here))))


      (make-event
       '(table post-arith1-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear))

      (make-event
       '(table theory-invariant-table nil
             (table-alist 'pre-arith1-theory-invariants world)
             :clear)))))

(defun allow-arith1-help-fn (world)
  (if (check-for-arith1-rulesets world)
      '(value-triple :redundant-allow-arith1-help)
    `(progn ,*allow-arith1-help-form*
            (include-book "arithmetic/top-with-meta" :dir :system)
            (in-theory (current-theory 'before-including-arithmetic-1)))))

(defmacro allow-arith1-help ()
  '(make-event (allow-arith1-help-fn (w state))))

(defmacro my-enable-arith1 (ctx)
  `(if (check-for-arith1-rulesets world)
       (e/d* ((:ruleset arith1-enable-ruleset))
             ((:ruleset arith1-disable-ruleset)))
     (er hard ,ctx
         "~
Run (ALLOW-ARITH1-HELP) in the current local scope before using ~x0.~%" ,ctx)))


(defmacro with-arith1-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith1 'with-arith1-help)))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith1-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro enable-arith1 ()
  '(my-enable-arith1 'enable-arith1))

;; Notes:

; WARNING: If you want to use both the arithmetic/ and arithmetic-5/ libraries,
; evaluate (allow-arith-help) after including the book with-arith-help.lisp.

;; This book allows the arithmetic library to be included locally within a book
;; while only affecting (i.e. arithmetically helping and slowing down proofs of)
;; forms that are surrounded by (with-arith1-help  ...).  To allow this,
;; include the following two forms.

;; (include-book "tools/with-arith1-help" :dir :system)
;; (allow-arith1-help)

;; The form (allow-arith1-help) locally includes arithmetic/top-with-meta, then
;; reverts to the pre-existing theory, in support of the with-arith1-help
;; macro.
