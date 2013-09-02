; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, August, 2013
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This small, pedagogical example shows how to use the :OR feature of
; make-event.  The macros defun-measures computes a trivial list of measures
; for a defun and keeps the first one that works.  A more serious such utility
; would compute more interesting measures, do much more thorough
; error-checking, work for defund and defun-nx, perhaps try different
; :ruler-extenders, and consider what happens when a measure is already
; provided.  We present a variant, defun-measures-check, to illustrate how one
; can arrange to check the result at include-book time.  Actually there's
; no reason I can see to do so in this case, but we illustrate how
; keyword :check-expansion interacts with keyword :expansion?.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

(defun add-measures1 (vars name formals rest)
  (declare (xargs :mode :program))
  (cond ((endp vars)
         nil)
        (t (cons `(defun ,name ,formals
                    (declare (xargs :measure (acl2-count ,(car vars))))
                    ,@rest)
                 (add-measures1 (cdr vars) name formals rest)))))

(defun add-measures (event)
  (declare (xargs :mode :program))
  (case-match event
    (('defun name formals . rest)
     (add-measures1 formals name formals rest))
    (& (er hard 'compute-measures
           "Not a well-formed defun: ~x0"
           event))))

(defn cons-to-all (a lst)
  (cond ((atom lst) lst)
        (t (cons (cons a (car lst))
                 (cons-to-all a (cdr lst))))))

(defmacro defun-measures (name formals &rest rest)

; The use of :expansion? avoids storing an expansion in the .cert file, in the
; case that the first event specified with :or turns out to be the expansion.

  (let ((defs (add-measures `(defun ,name ,formals ,@rest))))
    `(make-event '(:or ,@defs)
                 :expansion? ,(car defs))))

(defmacro defun-measures-check (name formals &rest rest)

; See also defun-measures.  Here, we add :check-expansion t, to illustrate how
; we can check expansions.  Notice that we replace each argument of :or, E, by
; (:do-proofs E), so that when we check the expansion we get the right one.
; Otherwise, when including a book and checking the expansion, we would be
; skipping proofs and the first measure would always be the expansion, causing
; an error in the case that a later measure had instead generated the expansion
; (which is saved in the .cert file, to check against the expansion recomputed
; at include-book time).

  (let ((defs (add-measures `(defun ,name ,formals ,@rest))))
    `(make-event '(:or ,@(cons-to-all :do-proofs (pairlis$ defs nil)))
                 :expansion? ,(car defs)
                 :check-expansion t)))

; Here are examples illustrating usage of the above macros.

; The following example generates an expansion that stores the first measure
; that works, namely, (acl2-count x2).  This shows up in the .cert file; see
; make-event-keywords-or-exp-check.lisp.
(defun-measures f1 (x0 x1 x2 x3)
  (if (consp x0)
      (if (consp x1)
          (if (consp x2)
              (if (consp x3)
                  (f1 (cons x0 x0) (cons x1 x1) (cdr x2) (cdr x3))
                x3)
            x2)
        x1)
    x0))

; The next example uses :expansion? as well as :check-expansion t.  The
; expansion turns out not to match what is specified by :expansion?, so a
; make-event form is constructed with a cons for :check-expansion and without
; :expansion?.  See make-event-keywords-or-exp-check.lisp.
(defun-measures-check f1c (x0 x1 x2 x3)
  (if (consp x0)
      (if (consp x1)
          (if (consp x2)
              (if (consp x3)
                  (f1c (cons x0 x0) (cons x1 x1) (cdr x2) (cdr x3))
                x3)
            x2)
        x1)
    x0))

; Unlike f1, the following example's expansion matches the value of
; :expansion?.  Therefore no expansion is generated in the .cert file (as
; checked in make-event-keywords-or-exp-check.lisp).
(defun-measures f2 (x0 x1 x2 x3)
  (if (consp x0)
      (if (consp x1)
          (if (consp x2)
              (if (consp x3)
                  (f2 (cdr x0) (cons x1 x1) (cdr x2) (cdr x3))
                x3)
            x2)
        x1)
    x0))

; Unlike f1c, the following example's expansion matches the value of
; :expansion?.  Normally, in the case of original keyword value
; :check-expansion t, the recorded expansion is stored in the value of
; :check-expansion.  But that isn't necessary, and isn't done, when the value
; of :expansion? equals the expansion.  So even though :check-expansion t is
; specified, no expansion is generated in the .cert file (as checked in
; make-event-keywords-or-exp-check.lisp).
(defun-measures-check f2c (x0 x1 x2 x3)
  (if (consp x0)
      (if (consp x1)
          (if (consp x2)
              (if (consp x3)
                  (f2c (cdr x0) (cons x1 x1) (cdr x2) (cdr x3))
                x3)
            x2)
        x1)
    x0))
