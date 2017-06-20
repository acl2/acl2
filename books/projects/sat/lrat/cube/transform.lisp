; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.  Here we complete the proof for (1).

(in-package "LRAT")

(include-book "cube")
(include-book "clean-formula")

(defun sp-valid-proofp$-top-rec (formula clrat-file posn chunk-size
                                         clrat-file-length old-suffix debug
                                         old-max-var a$ ctx state)

; This version of incl-valid-proofp$-top-rec additionally returns the current
; formula, and for the flag, instead of :complete or :incomplete or nil it
; returns a Boolean flag.

  (declare (xargs :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (natp posn)
                              (< posn *2^56*)
                              (posp chunk-size)
                              (posp clrat-file-length)
                              (stringp old-suffix)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :guard-hints
                  (("Goal"
                    :in-theory
                    (disable incl-valid-proofp$ a$ptr clrat-read-next)))
                  :ruler-extenders
                  (:lambdas mv-list return-last) ; ugly bug work-around
                  :measure (nfix (- clrat-file-length posn))
                  :stobjs (state a$)))
  (cond
   ((and (mbt (natp posn))
         (mbt (posp clrat-file-length))
         (mbt (posp chunk-size))
         (<= posn clrat-file-length))
    (prog2$
     (and debug
          (cw "; Note: Reading from position ~x0~|" posn))
     (mv-let (proof suffix new-posn)
       (clrat-read-next clrat-file posn chunk-size old-suffix
                        clrat-file-length state)
       (cond
        ((null suffix) ; error (normally a string, possibly even "")
         (mv (er hard? ctx "Implementation error: Null suffix!")
             formula
             a$))
        ((null proof)
         (mv t formula a$))
        ((stringp proof) ; impossible
         (mv (er hard? ctx
                 "Implementation error: ~x0 returned a string for its proof, ~
                  which we thought was impossible!"
                 'clrat-read-next)
             formula
             a$))
        (t
         (mv-let (v new-formula new-max-var a$)
           (prog2$
            (cw "; Note: Checking next proof segment.~|")
            (incl-valid-proofp$ formula proof old-max-var a$))
           (cond
; !! Move this up if possible.
            ((>= new-posn *2^56*)
             (mv (er hard? ctx
                     "Attempted to read at position ~x0, but the maximum ~
                      legal such position is 2^56 = ~x1."
                     new-posn *2^56*)
                 formula
                 a$))
            ((not v) (mv nil formula a$))
            ((eq v :complete)
             (mv t new-formula a$))
            ((> new-posn clrat-file-length)

; If new-posn is exactly clrat-file-length, then as per the discussion of the
; "truncation case" in :doc read-file-into-string, we need to iterate.  But if
; new-posn exceeds clrat-file-length, then we have a valid proof that does not
; include the empty clause.

             (mv t new-formula a$))
            (t
             (sp-valid-proofp$-top-rec new-formula clrat-file new-posn
                                       chunk-size clrat-file-length suffix
                                       debug new-max-var a$ ctx
                                       state)))))))))
   (t ; impossible
    (mv nil formula a$))))

(defun sp-valid-proofp$-top-aux (formula clrat-file chunk-size
                                         clrat-file-length debug a$ ctx state)

; This is a variant of incl-valid-proofp$-top-aux.

  (declare (xargs :stobjs (a$ state)
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (posp chunk-size)
                              (posp clrat-file-length))))
  (sp-valid-proofp$-top-rec formula clrat-file 0 chunk-size
                            clrat-file-length "" debug
                            (formula-max-var formula 0)
                            a$ ctx state))

(defthm sp-valid-proofp$-top-rec-preserves-formula-p
  (implies (and (a$p a$)
                (eql (a$ptr a$) 0)
                (formula-p formula)
                (stringp clrat-file)
                (natp posn)
                (< posn *2^56*)
                (posp chunk-size)
                (posp clrat-file-length)
                (stringp old-suffix)
                (natp old-max-var)
                (<= (formula-max-var formula 0)
                    old-max-var))
           (formula-p
            (mv-nth 1
                    (sp-valid-proofp$-top-rec formula clrat-file posn chunk-size
                                              clrat-file-length old-suffix debug
                                              old-max-var a$ ctx state))))
  :hints (("Goal"
           :in-theory
           (e/d (sp-valid-proofp$-top-rec)
                (incl-valid-proofp$ a$ptr clrat-read-next)))))

(defun transform (cnf-file clrat-file chunk-size debug state)

; This is a variant of incl-valid-proofp$-top.
; See sp-valid-proofp$-top-rec.

  (declare (xargs :guard t
                  :stobjs state
                  :guard-hints
                  (("Goal" :in-theory (disable sp-valid-proofp$-top-rec)))))
  (let ((formula (ec-call (cnf-read-file cnf-file state)))
        (ctx 'transform))
    (cond
     ((not (stringp clrat-file))
      (er-soft-logic
       ctx
       "The filename argument is not a string:~|~x0"
       clrat-file))
     ((not (posp chunk-size))
      (er-soft-logic
       ctx
       "The supplied :chunk-size must be a positive integer, but ~x0 is ~
        not.~|~x0"
       clrat-file))
     ((not (ordered-formula-p formula))
      (er-soft-logic ctx "An invalid formula was supplied by the parser!"))
     (t
      (mv-let (clrat-file-length state)
        (file-length$ clrat-file state)
        (cond
         ((posp clrat-file-length)
          (mv-let (val new-formula)
            (prog2$
             (and debug
                  (cw "Length of file ~x0: ~x1~|" clrat-file clrat-file-length))
             (with-fast-alist
               formula
               (with-local-stobj a$
                 (mv-let
                   (val new-formula a$)
                   (let ((a$ (resize-a$arr 2 a$))) ; to get a$p to hold
                     (sp-valid-proofp$-top-aux formula clrat-file chunk-size
                                               clrat-file-length debug a$
                                               ctx state))
                   (mv val (clean-formula new-formula))))))
            (cond (val (value (cons formula new-formula)))
                  (t (er-soft-logic
                      ctx
                      "Invalid proof (check failed)."
                      clrat-file)))))
         ((eql clrat-file-length 0)
          (er-soft-logic
           ctx
           "Zero-length file: ~x0."
           clrat-file))
         (t (er-soft-logic
             ctx
             "Sorry, Lisp cannot determine the file-length of file ~x0."
             clrat-file))))))))

; Start proof of transform-preserves-sat-main

(include-book "../incremental/soundness-main")

(defthm transform-preserves-sat-main
  (implies
   (and (car (sp-valid-proofp$-top-rec formula
                                       clrat-file posn chunk-size
                                       clrat-file-length
                                       old-suffix debug max-var a$ ctx
                                       state))
        (formula-p formula)
        (a$p a$)
        (equal (a$ptr a$) 0)
        (integerp max-var)
        (<= (formula-max-var formula 0) max-var)
        (satisfiable formula))
   (satisfiable
    (mv-nth 1 (sp-valid-proofp$-top-rec formula
                                        clrat-file posn chunk-size
                                        clrat-file-length
                                        old-suffix debug max-var a$ ctx
                                        state))))
  :hints (("Goal"
           :in-theory (e/d (formula-max-var-is-formula-max-var-1)
                           (incl-valid-proofp$ clrat-read-next a$ptr))
           :induct t)))

(defthm transform-preserves-sat
  (let* ((result
          (mv-nth 1 (transform cnf-file clrat-file chunk-size debug state)))
         (formula (car result))
         (new-formula (cdr result)))
    (implies (and result ; non-error case
                  (satisfiable formula))
             (satisfiable new-formula)))
  :hints (("Goal"
           :in-theory
           (union-theories '(transform
                             acl2::error1-logic
                             sp-valid-proofp$-top-aux
                             transform-preserves-sat-main
                             (:e a$p)
                             (:e resize-a$arr)
                             create-a$
                             (:e a$ptr)
                             natp-formula-max-var
                             ordered-formula-p-implies-formula-p
                             clean-formula-preserves-satisfiable
                             sp-valid-proofp$-top-rec-preserves-formula-p)
                           (theory 'ground-zero)))))
