; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; The goal in this book is to prove the goal (DEFGOAL EVAL_SUM_POLY_DISTRIB
; ...) from eval-poly-thy.lisp, which is a file produced with a translator from
; HOL to ACL2 written by Konrad Slind.  That goal is stated in the ZF package
; as the final theorem, hol::HOL{EVAL_SUM_POLY_DISTRIB}, in the present book.

; Actually, this is a theorem when the HP-IMPLIES call is replaced by its
; second argument, i.e., the HP= call.  That's what we'll prove as the
; penultimate theorem in the present book, EVAL_SUM_POLY_DISTRIB-main.

; Those theorems are a bit of a nightmare to read, but we can get a prettier
; picture as follows.

;  (include-book "../acl2/hol-pprint")
;  (include-book "eval-poly-thy")
;  (in-package "HOL")

; And then, applying hol-pprint to the quotation of the HP= call in those
; returns:

#|
(EQUAL (= (EVAL_POLY (SUM_POLYS X Y) V)
          (+ (EVAL_POLY X V) (EVAL_POLY Y V)))
       HP-TRUE)
|#

; So what is our proof strategy?  First we include the following two books.

; Define eval_poly in HOL, towards the main goal, to prove that it distributes
; over sum.
(include-book "eval-poly-thy")

; Define eval-poly in ACL2 and prove that it distributes over sum.  That proof
; is automatic, i.e., it requires no lemmas.
(include-book "eval-poly-acl2")

; Include a book of general lemmas, developed during the proof below but
; reusable for other such proofs.
(include-book "../acl2/lemmas")

; Include the set-theory library.
(include-book "projects/set-theory/top" :dir :system)

; Include a book of helpful alternatives to generated lemmas.
(include-book "eval-poly-thy-alt")

; Then we reduce calls of HOL eval_poly and sum_polys to respective calls of
; ACL2 eval-poly and sum-polys, to reduce the main goal to the one already
; proved for ACL2.

(defconst *eval_poly-type*
  (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                :NUM :NUM)))

(defconst *sum_polys-type*
  (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                (:LIST (:HASH :NUM :NUM))
                (:LIST (:HASH :NUM :NUM)))))

(defthm alist-subsetp-eval-poly$hta-implies-alist-subsetp-hta0

; This forward-chaining rule allows us to replace the hypothesis
; (alist-subsetp (eval-poly$hta) hta)
; by the more generally applicable hypothesis
; (alist-subsetp (hta0) hta)
; in some of the lemmas developed for this proof, so that they are reusable for
; other proofs.

  (implies (alist-subsetp (hol::eval-poly$hta) hta)
           (alist-subsetp (hta0) hta))
  :rule-classes :forward-chaining)

(defun h2a (x)

; Without an hta, it's challenging to provide a reasonable guard.  So we do not
; guard-verify this function.

; This is a bit ad hoc.  Eventually it might be nice for h2a to work regardless
; of the ground type of x, but then we'll presumalby need an hta argument.

  (let ((val (hp-value x))
        (typ (hp-type x)))
    (cond
     ((eq typ :num) val)
     ((equal typ '(:hash :num :num))
      val)
     ((equal typ '(:list (:hash :num :num)))
      (finseq-to-list val))
     (t :fail))))

(in-theory (disable (:e h2a)))

(defun eval_poly-reduction-induction (x xa)
  (cond ((endp xa) (list x xa))
        (t (eval_poly-reduction-induction
            (hp-list-cdr x)
            (cdr xa)))))

(defun exp-reduction-lemma-induction (k n)
  (if (zp k)
      n
    (exp-reduction-lemma-induction (1- k)
                                   (make-hp (1- (hp-value n)) :num))))

(defthm exp-reduction-lemma
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (hpp m hta)
                (equal (hp-type m) (typ :num))
                (hpp n hta)
                (equal (hp-type n) (typ :num))
                (force (hol::eval-poly$prop))
                (equal k (hp-value n)))
           (equal (hap* (hol::exp (typ (:arrow* :num :num :num)))
                        m
                        n)
                  (make-hp (expt (hp-value m) k)
                           :num)))
  :hints (("Goal" :induct (exp-reduction-lemma-induction k n))))

(defthm exp-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (hpp m hta)
                (equal (hp-type m) (typ :num))
                (hpp n hta)
                (equal (hp-type n) (typ :num))
                (force (hol::eval-poly$prop)))
           (equal (hap* (hol::exp (typ (:arrow* :num :num :num)))
                        m
                        n)
                  (make-hp (expt (hp-value m) (hp-value n))
                           :num))))

(defthm natp-eval-poly-finseq-to-list
  (implies (natp v)
           (natp (eval-poly (finseq-to-list x) v))))

(defun weak-polyp (x)
  (cond ((atom x) (null x))
        (t (let ((m (car x)))
             (and (consp (car x))
                  (let* ((c (car m)) (e (cdr m)) (r (cdr x)))
                    (and (weak-polyp r)
                         (natp c)
                         (natp e))))))))

(defthm natp-eval-poly
  (implies (and (force (weak-polyp x))
                (force (natp v)))
           (natp (eval-poly x v))))

(defthmz weak-polyp-cdr-finseq-to-list-car-lemma
  (implies (and (alist-subsetp (hta0) hta)
                (hpp (cons val (typ (:list (:hash :num :num)))) hta))
           (weak-polyp (finseq-to-list val)))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthm weak-polyp-cdr
  (implies (weak-polyp x)
           (weak-polyp (cdr x))))

(defthmz weak-polyp-cdr-finseq-to-list-car
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x)
                       (typ (:list (:hash :num :num))))
                (not (equal x '(0 :list (:hash :num :num)))))
           (weak-polyp (cdr (finseq-to-list (car x)))))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthmz eval_poly-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (force (hpp x hta))
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp v hta))
                (force (equal (hp-type v) (typ :num)))
                (force (hol::eval-poly$prop))
                (equal xa (h2a x)))
           (equal (hap* (hol::eval_poly *eval_poly-type*) x v)
                  (make-hp (eval-poly xa (hp-value v))
                           :num)))
  :hints
  (("Goal"
    :in-theory (disable hpp-monotone-for-alist-subsetp)
    :do-not '(eliminate-destructors) ; necessary
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
  :hints (("Goal" :in-theory (enable hap hp-cons hpp hol-valuep hol-type-eval)))))

(defthm sum_polys-type-properties-lemma-1
  (implies (and (hpp fn hta)
                (equal (cdr fn)
                       *sum_polys-type*)
                (hpp x hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (force (hol::eval-poly$prop)))
           (hpp (hap* fn x y) hta)))

(defthm hol::sum_polys$type-2-alt
  (implies (force (hol::eval-poly$prop))
           (equal (cdr (hol::sum_polys *sum_polys-type*))
                  *sum_polys-type*))
  :hints (("Goal" :use hol::sum_polys$type)))

(defthm funp-apply-sum_polys
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (hpp x hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (hol::eval-poly$prop))
           (funp (car (hap* (hol::sum_polys *sum_polys-type*)
                            x
                            y))))
  :hints (("Goal"
           :restrict ((list-type-is-funp
                       ((hta hta) (rest '((:hash :num :num)))))))))

(defthm natp-domain-apply-sum_polys
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (hpp x hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (hol::eval-poly$prop))
           (natp (domain (car (hap* (hol::sum_polys *sum_polys-type*)
                                    x
                                    y)))))
  :hints (("Goal"
           :use ((:instance list-type-implies-funp-with-natp-domain
                            (x (hap* (hol::sum_polys *sum_polys-type*)
                                              x
                                              y))
                            (rest '((:hash :num :num))))))))

(defthm sum_polys-reduction
  (implies (and (alist-subsetp (hol::eval-poly$hta) hta)
                (force (hpp x hta))
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp y hta))
                (force (equal (hp-type y)
                              (typ (:list (:hash :num :num)))))
                (equal xa (h2a x))
                (equal ya (h2a y))
                (force (hol::eval-poly$prop)))
           (equal (h2a (hap* (hol::sum_polys *sum_polys-type*) x y))
                  (sum-polys xa ya)))
  :hints (("Goal"
           :induct (sum_polys-reduction-induction x xa y ya)
           :do-not-induct t)))

(defthm EVAL_SUM_POLY_DISTRIB-main
  (IMPLIES
   (AND (ALIST-SUBSETP (hol::EVAL-POLY$HTA) HTA)
        (HPP X HTA)
        (EQUAL (HP-TYPE X)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP Y HTA)
        (EQUAL (HP-TYPE Y)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP V HTA)
        (EQUAL (HP-TYPE V) (TYP :NUM))
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

(defthm hol::HOL{EVAL_SUM_POLY_DISTRIB}
  (IMPLIES
   (AND (ALIST-SUBSETP (hol::EVAL-POLY$HTA) HTA)
        (HPP X HTA)
        (EQUAL (HP-TYPE X)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP Y HTA)
        (EQUAL (HP-TYPE Y)
               (TYP (:LIST (:HASH :NUM :NUM))))
        (HPP V HTA)
        (EQUAL (HP-TYPE V) (TYP :NUM))
        (FORCE (hol::EVAL-POLY$PROP)))
   (EQUAL
    (HP-IMPLIES
     (HP-AND (HAP* (hol::POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             :BOOL)))
                   X)
             (HAP* (hol::POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             :BOOL)))
                   Y))
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
                     Y V))))
    (HP-TRUE))))
