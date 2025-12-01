; DAG exprs that mention only nodes below some bound
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-exprs")
(include-book "bounded-darg-listp")
(include-book "largest-non-quotep")
(local (include-book "kestrel/lists-light/len" :dir :system))

(defthm <-of-largest-non-quotep
  (implies (and (bounded-darg-listp args nodenum)
    ;(natp nodenum)
                (<= 0 NODENUM)
                )
           (< (largest-non-quotep args)
              nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep bounded-darg-listp))))

;this weaker version is needed to match right
(defthm <=-of-largest-non-quotep
  (implies (and (bounded-darg-listp args nodenum)
                (natp nodenum))
           (<= (largest-non-quotep args)
               nodenum))
  :hints (("Goal" :in-theory (enable largest-non-quotep bounded-darg-listp))))

;;;
;;; bounded-dag-exprp
;;;

;; Check that EXPR is a suitable DAG expr for node NODENUM.  That is, EXPR must
;; be a dag-expr and all nodenums it mentions must be less than NODENUM.
;; TODO: Put the bound second, to match dargp-less-than?
(defund bounded-dag-exprp (bound expr)
  (declare (xargs :guard (natp bound)
                  :split-types t)
           (type (integer 0 *) bound))
  (mbe :logic (and (dag-exprp expr)
                   (if (and (consp expr)
                            (not (eq 'quote (car expr))))
                       (bounded-darg-listp (dargs expr) bound)
                     t))
       :exec (if (atom expr)
                 (symbolp expr)
               (let ((fn (ffn-symb expr)))
                 (if (eq 'quote fn)
                     (let ((cdr (cdr expr)))
                       (and (consp cdr)
                            (null (cdr cdr))))
                   ;; regular function call:
                   (and (symbolp fn) ; not a lambda
                        (bounded-darg-listp (cdr ; can't call dargs here due to its guard
                                             expr) bound)))))))

(defthm bounded-dag-exprp-when-not-consp-cheap
  (implies (not (consp expr))
           (equal (bounded-dag-exprp bound expr)
                  (symbolp expr)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp))))

(defthm bounded-dag-exprp-of-cons
  (equal (bounded-dag-exprp bound (cons fn args))
         (if (equal 'quote fn)
             (and (consp args)
                  (equal nil (cdr args)))
           (and (symbolp fn)
                (true-listp args)
                (bounded-darg-listp args bound))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-darg-listp-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp bound expr)
                ;; (consp expr)
                (not (eq 'quote (car expr))))
           (bounded-darg-listp (dargs expr) bound))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dargs-when-not-consp-cheap))))

(defthm bounded-darg-listp-when-bounded-dag-exprp-gen
  (implies (and (bounded-dag-exprp free expr)
                ;; (consp expr)
                (not (eq 'quote (car expr)))
                (<= free bound))
           (bounded-darg-listp (dargs expr) bound))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-and-consp-forward-to-true-listp-of-dargs
  (implies (and (bounded-dag-exprp bound expr)
                (consp expr))
           (true-listp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     ;dargs ;todo: this theorem happens to be true for quoteps too
                                     ))))

(defthm bounded-dag-exprp-and-equal-of-quote-and-car-forward-to-true-listp
  (implies (and (bounded-dag-exprp bound expr)
                (eq 'quote (car expr)))
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     ;dargs ;todo: this theorem happens to be true for quoteps too
                                     ))))

(defthm true-listp-of-dargs-when-bounded-dag-exprp-and-consp
  (implies (and (bounded-dag-exprp bound expr)
                (not (symbolp expr)) ;or say (consp expr)
                )
           (true-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp dargs))))

(defthm true-listp-of-dargs-better
  (implies (and (bounded-dag-exprp bound expr)
                ;; (not (equal 'quote (car expr)))
                )
           (true-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp dargs))))

(defthm bounded-dag-exprp-and-consp-forward-to-symbolp-of-car
  (implies (and (bounded-dag-exprp bound expr)
                (consp expr))
           (symbolp (car expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-and-not-consp-forward-to-symbolp
  (implies (and (bounded-dag-exprp bound expr)
                (not (consp expr)))
           (symbolp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-forward-to-darg-listp-of-dargs
  (implies (and (bounded-dag-exprp bound expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (darg-listp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm dag-exprp-when-bounded-dag-exprp
  (implies (bounded-dag-exprp bound expr) ;free var
           (dag-exprp expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp))))

(defthm bounded-dag-exprp-monotone
  (implies (and (bounded-dag-exprp bound2 expr) ;bound2 is a free var
                (<= bound2 bound))
           (bounded-dag-exprp bound expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm <-of-nth-of-dargs
  (implies (and (bounded-dag-exprp bound expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
                (not (consp (nth n (dargs expr)))) ;rules out a quotep
                )
           (< (nth n (dargs expr)) bound))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp <-OF-NTH-WHEN-BOUNDED-DARG-LISTP))))

;; Not tight.
;; Disabled since hung on <
(defthmd not-<-of-nth-of-dargs
  (implies (and (bounded-dag-exprp bound expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
                (not (consp (nth n (dargs expr)))))
           (not (< bound (nth n (dargs expr)))))
  :hints (("Goal" :use <-of-nth-of-dargs
           :in-theory (disable <-of-nth-of-dargs))))

(defthm symbolp-of-car-when-bounded-dag-exprp
  (implies (bounded-dag-exprp bound expr) ;bound is a free var
           (symbolp (car expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-when-symbolp-cheap
  (implies (symbolp var)
           (bounded-dag-exprp n var))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm not-<-of-plus1-of-largest-non-quotep
  (implies (and (bounded-dag-exprp bound expr)
                (natp bound)
                ;; (consp expr)
                (not (EQUAL 'QUOTE (CAR EXPR)))
                )
           (not (< bound (+ 1 (largest-non-quotep (dargs expr))))))
  :hints (("Goal" :in-theory (e/d (bounded-dag-exprp
                                   dag-exprp
                                   dargs-when-not-consp-cheap)
                                  (<-of-largest-non-quotep))
           :use (:instance <-of-largest-non-quotep (args (dargs expr)) (nodenum bound)))))

;consider using polarities
(defthm myquotep-when-bounded-dag-exprp
  (implies (bounded-dag-exprp bound expr)
           (equal (myquotep expr)
                  (equal 'quote (car expr))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dag-exprp))))

(defthm bounded-darg-listp-of-dargs-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp bound expr)
                ;; (consp expr)
                (not (equal 'quote (car expr))))
           (bounded-darg-listp (dargs expr) bound))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dargs-when-not-consp-cheap))))

;; We use consp as the normal form
(defthm symbolp-when-bounded-dag-exprp
  (implies (bounded-dag-exprp bound expr) ;bound is a free var
           (equal (symbolp expr)
                  (not (consp expr)))))

;; ;drop?
;; (defthm dargp-when-bounded-dag-exprp
;;   (implies (bounded-dag-exprp bound expr)
;;            (equal (dargp expr)
;;                   (equal 'quote (car expr))))
;;   :hints (("Goal" :in-theory (enable dargp dag-exprp))))

(defthm bounded-dag-exprp-when-myquotep-cheap
  (implies (myquotep expr)
           (bounded-dag-exprp bound expr))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthmd bounded-dag-exprp-when-myquotep
  (implies (myquotep expr)
           (bounded-dag-exprp bound expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-when-equal-of-quote-and-car-cheap
  (implies (equal 'quote (car expr))
           (equal (bounded-dag-exprp bound expr)
                  (myquotep expr)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;;;
;;; bounded-dag-expr-listp
;;;

;; todo: reorder args
(defund bounded-dag-expr-listp (bound exprs)
  (declare (type (integer 0 *) bound))
  (if (atom exprs)
      (null exprs)
    (and (bounded-dag-exprp bound (first exprs))
         (bounded-dag-expr-listp bound (rest exprs)))))

(defthm bounded-dag-expr-listp-of-cons
  (equal (bounded-dag-expr-listp bound (cons expr exprs))
         (and (bounded-dag-exprp bound expr)
              (bounded-dag-expr-listp bound exprs)))
  :hints (("Goal" :in-theory (enable bounded-dag-expr-listp))))

(defthm bounded-dag-expr-listp-of-nil
  (bounded-dag-expr-listp bound nil)
  :hints (("Goal" :in-theory (enable bounded-dag-expr-listp))))

(defthm bounded-dag-expr-listp-monotone
  (implies (and (bounded-dag-expr-listp bound2 exprs)
                (<= bound2 bound)
                ;(integerp bound)
                ;(integerp bound2)
                )
           (bounded-dag-expr-listp bound exprs))
  :hints (("Goal" :in-theory (enable bounded-dag-expr-listp))))
