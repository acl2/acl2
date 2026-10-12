; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For background, see file README.txt.

(in-package "ZF")

; The goal in this book is to prove (DEFGOAL EVAL_SUM_POLY_DISTRIB ...) as
; displayed in a comment at the end of eval-poly-thy.lisp.  That goal is stated
; in the ZF package as the final theorem, HOL{EVAL_SUM_POLY_DISTRIB}, in the
; present book; it is redundantly phrased in terms of DEFGOAL in
; eval-poly-top.lisp.

; Actually, this is a theorem when the HP-IMPLIES call is replaced by its
; second argument, i.e., the HP= call.  That's what we'll prove as the
; penultimate theorem in the present book, EVAL_SUM_POLY_DISTRIB-main.

; Those theorems are a bit of a nightmare to read, but we can get a prettier
; picture as follows.

;  (include-book "../acl2/hol-pprint")
;  (include-book "eval-poly-thy")
;  (in-package "HOL")

; And then, applying hol-pprint to the quotation of the conclusion of the
; IMPLIES in that theorem -- that is, evaluating
;   (hol-pprint '(equal (hp= ...) (hp-true)))
; --  returns:

#|
(EQUAL (= (EVAL_POLY (SUM_POLYS X Y) V)
          (+ (EVAL_POLY X V) (EVAL_POLY Y V)))
       HP-TRUE)
|#

; So what is our proof strategy?  First we include the following two books.

; Import the translator output into ACL2:
(include-book "eval-poly-thy") ; no_port

; Define eval-poly in ACL2 and prove that it distributes over sum.  That proof
; is automatic, i.e., it requires no lemmas.
(include-book "eval-poly-acl2") ; no_port

; Include a book of general lemmas, developed during the proof below but
; reusable for other such proofs.
(include-book "../acl2/lemmas") ; no_port

; Include the set-theory library (redundant).
(include-book "projects/set-theory/top" :dir :system) ; no_port

; Include a book of helpful alternatives to generated lemmas.
(include-book "eval-poly-thy-alt") ; no_port

; Then we reduce calls of HOL eval_poly and sum_polys to respective calls of
; ACL2 eval-poly and sum-polys, to reduce the main goal to the one already
; proved for ACL2.

; We start with a convenient abbreviation:
(defconst *sum_polys-type*
  (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                (:LIST (:HASH :NUM :NUM))
                (:LIST (:HASH :NUM :NUM)))))

(defthm alist-subsetp-eval-poly$hta-implies-alist-subsetp-hta0

; !! Should be in the thy exports, maybe.

; This forward-chaining rule allows us to replace the hypothesis
; (alist-subsetp (eval-poly$hta) hta)
; by the more generally applicable hypothesis
; (alist-subsetp (hta0) hta)
; in some of the lemmas developed for this proof, so that they are reusable for
; other proofs.

  (implies (alist-subsetp (hol::eval-poly$hta) hta)
           (alist-subsetp (hta0) hta))
  :rule-classes :forward-chaining)

(defthmz htap1-eval-poly$hta
; !! Should be in the thy exports
  (htap1 (hol::eval-poly$hta))
  :hints (("Goal" :in-theory (enable hol::eval-poly$hta)))
  :props (hta-prop))

(defthm alist-subsetp-hta0-eval-poly$hta
; !! Should be in the thy exports
  (alist-subsetp (hta0) (hol::eval-poly$hta))
  :hints (("Goal" :in-theory (enable hol::eval-poly$hta))))

(defthmz htap-eval-poly$hta
; !! Should be in the thy exports
  (htap (hol::eval-poly$hta))
  :props (hta-prop))

(defun h2a (x)

; Without an hta, it's challenging to provide a reasonable guard.  So we do not
; guard-verify this function.

; This is a bit ad hoc.  Eventually it might be nice for h2a to work regardless
; of the ground type of x, but then we'll presumably need an hta argument.

  (let ((val (hp-value x))
        (typ (hp-type x)))
    (cond
     ((eq typ :num) val)
     ((equal typ '(:hash :num :num))
      val)
     ((equal typ '(:list (:hash :num :num)))
      (finseq-to-list val))
     (t :fail))))

(defun exp-reduction-induction (n)
       (if (or (atom n) (zp (hp-value n)))
	   n
	 (exp-reduction-induction (make-hp (1- (hp-value n)) :num))))

(defthm exp-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (hpp m hta)
                (equal (hp-type m) (typ :num))
                (hpp n hta)
                (equal (hp-type n) (typ :num))
                (force (hol::eval-poly$prop))
                (force (hta-prop)) ; !! added for now
                )
           (equal (hap* (hol::exp (typ (:arrow* :num :num :num)))
                        m
                        n)
                  (make-hp (expt (hp-value m) (hp-value n))
                           :num)))
  :hints (("Goal" :induct (exp-reduction-induction n))))

(defun eval_poly-reduction-induction (x xa)
  (cond ((endp xa) (list x xa))
        (t (eval_poly-reduction-induction
            (hp-list-cdr x)
            (cdr xa)))))

(defthm eval_poly-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (force (hpp x hta))
                (htap hta)
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp v hta))
                (force (equal (hp-type v) (typ :num)))
                (force (hol::eval-poly$prop))
                (force (hta-prop)) ; !! added for now
                (equal xa (h2a x)))
           (equal (hap* (hol::eval_poly (typ (:arrow* (:list (:hash :num :num))
                                                      :num :num)))
                        x v)
                  (make-hp (eval-poly xa (hp-value v))
                           :num)))
  :hints
  (("Goal"
    :in-theory (e/d (hp-list-car hp-list-cdr) (hpp-monotone-for-alist-subsetp))
    :induct (eval_poly-reduction-induction x xa))))

(defun sum_polys-reduction-induction (x xa y ya)
  (declare (xargs :measure (+ (len xa) (len ya))))
  (cond ((or (endp xa) (endp ya))
         (list x xa y ya))
        ((= (cdar xa) (cdar ya)) ; same exponent
         (sum_polys-reduction-induction
          (hp-list-cdr x)
          (cdr xa)
          (hp-list-cdr y)
          (cdr ya)))
        ((< (cdar xa) (cdar ya))
         (sum_polys-reduction-induction
          x
          xa
          (hp-list-cdr y)
          (cdr ya)))
        (t
         (sum_polys-reduction-induction
          (hp-list-cdr x)
          (cdr xa)
          y
          ya))))

; Start final efforts towards proof of sum_polys-reduction.

(encapsulate ()

(local ; weird little lemma that's needed here
 (defthm sum_polys-reduction-1-lemma
  (implies (force (hol::eval-poly$prop))
           (hol::sum_polys *sum_polys-type*))
  :hints (("Goal"
           :in-theory (e/d (hpp) (hol::sum_polys$type))
           :use hol::sum_polys$type))))

(defthm sum_polys-reduction-1 ; follows from SUM_POLYS$TYPE
  (implies (and (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (equal (hp-type y)
                              (typ (:list (:hash :num :num)))))
                (force (hol::eval-poly$prop)))
           (equal (cdr (hap (hap (hol::sum_polys *sum_polys-type*)
                                 x)
                            y))
                  (typ (:list (:hash :num :num)))))
  :hints (("Goal" :in-theory (enable hap)))))

(local (defthm equal-cons-0

; This lemma has been unnecessary but has sped up the proof of
; sum_polys-reduction a bit.

         (equal (equal x (cons 0 typ))
                (and (equal (car x) 0) (equal (cdr x) typ)))))

(defthm natp-domain-apply-sum_polys

; This lemma has been unnecessary but has sped up the proof of
; sum_polys-reduction a bit.

  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (htap1 hta)
                (hpp x hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (force (hta-prop)) ; !! added for now
                (hol::eval-poly$prop))
           (natp (domain (car (hap* (hol::sum_polys *sum_polys-type*)
                                    x
                                    y)))))
  :hints (("Goal"
           :in-theory (disable hol-valuep)
           :use ((:instance list-type-implies-funp-with-natp-domain
                            (x (hap* (hol::sum_polys *sum_polys-type*)
                                              x
                                              y))
                            (rest '((:hash :num :num))))))))

(defthmz sum_polys-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (htap1 hta)
                (force (hpp x hta))
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp y hta))
                (force (equal (hp-type y)
                              (typ (:list (:hash :num :num)))))
                (equal xa (h2a x))
                (equal ya (h2a y))
                (force (hta-prop)) ; !! added for now
                (force (hol::eval-poly$prop)))
           (equal (h2a (hap* (hol::sum_polys *sum_polys-type*) x y))
                  (sum-polys xa ya)))
  :hints (("Goal"
           :restrict ((list-type-is-funp
                       ((hta hta)
                        (rest '((:HASH :NUM :NUM)))))
                      (list-type-implies-funp-with-natp-domain-rewrite
                       ((hta hta) (rest '((:hash :num :num))))) )
           :induct (sum_polys-reduction-induction x xa y ya)
           :do-not-induct t))
  :props (hta-prop))

(defthm EVAL_SUM_POLY_DISTRIB-main
  (IMPLIES
   (AND (ALIST-SUBSETP (hol::EVAL-POLY$HTA) HTA)
        (htap1 hta)
        (HPP X HTA)
        (EQUAL (HP-TYPE X)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP Y HTA)
        (EQUAL (HP-TYPE Y)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP V HTA)
        (EQUAL (HP-TYPE V) (TYP :NUM))
        (force (hta-prop)) ; !! added for now
        (FORCE (hol::EVAL-POLY$PROP)))
   (EQUAL
    (HP= (HAP* (hol::EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             :NUM :NUM)))
               (HAP* (hol::SUM_POLYS (TYP (:ARROW*
                                           (:LIST (:HASH :NUM :NUM))
                                           (:LIST (:HASH :NUM :NUM))
                                           (:LIST (:HASH :NUM :NUM)))))
                     X Y)
               V)
         (HP+ (HAP* (hol::EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                  :NUM :NUM)))
                    X V)
              (HAP* (hol::EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                  :NUM :NUM)))
                    Y V)))
    (HP-TRUE))))

; The following is generated by the form
;   (DEFGOAL EVAL_SUM_POLY_DISTRIB ...)
; in the superior book, eval-poly-top.lisp.
#!hol
(DEFTHM HOL{EVAL_SUM_POLY_DISTRIB}
 (IMPLIES
  (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
       (htap1 hta)
       (HPP X HTA)
       (EQUAL (HP-TYPE X)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP Y HTA)
       (EQUAL (HP-TYPE Y)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP V HTA)
       (EQUAL (HP-TYPE V) (TYP :NUM))
       (force (zf::hta-prop)) ; !! added for now
       (FORCE (EVAL-POLY$PROP)))
  (EQUAL
   (HP-IMPLIES
       (HP-AND (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     X)
               (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     Y))
       (HP= (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                           :NUM :NUM)))
                  (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        X Y)
                  V)
            (HP+ (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       X V)
                 (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       Y V))))
   (HP-TRUE))))
