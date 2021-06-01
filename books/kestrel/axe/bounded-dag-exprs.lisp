; DAG exprs that mention only nodes below some bound
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-exprs")
(include-book "all-dargp-less-than")
(local (include-book "kestrel/lists-light/len" :dir :system))

;;;
;;; bounded-dag-exprp
;;;

;; Check that EXPR is a suitable DAG expr for node NODENUM.  That is, EXPR must
;; be a dag-expr and all nodenums it mentions must be less that NODENUM.
(defund bounded-dag-exprp (nodenum expr)
  (declare (type (integer 0 *) nodenum))
  (and (dag-exprp0 expr)
       (if (and (consp expr)
                (not (eq 'quote (car expr))))
           (all-dargp-less-than (dargs expr) nodenum)
         t)))

(defthm bounded-dag-exprp-when-not-consp-cheap
  (implies (not (consp expr))
           (equal (bounded-dag-exprp nodenum expr)
                  (symbolp expr)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0))))

(defthm bounded-dag-exprp-of-cons
  (equal (bounded-dag-exprp nodenum (cons fn args))
         (if (equal 'quote fn)
             (and (consp args)
                  (equal nil (cdr args)))
           (and (symbolp fn)
                (true-listp args)
                (all-dargp-less-than args nodenum))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm all-dargp-less-than-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp nodenum expr)
                ;; (consp expr)
                (not (eq 'quote (car expr))))
           (all-dargp-less-than (dargs expr) nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dargs-when-not-consp-cheap))))

(defthm all-dargp-less-than-when-bounded-dag-exprp-gen
  (implies (and (bounded-dag-exprp free expr)
                ;; (consp expr)
                (not (eq 'quote (car expr)))
                (<= free nodenum))
           (all-dargp-less-than (dargs expr) nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-and-consp-forward-to-true-listp-of-dargs
  (implies (and (bounded-dag-exprp nodenum expr)
                (consp expr))
           (true-listp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     ;dargs ;todo: this theorem happens to be true for quoteps too
                                     ))))

(defthm bounded-dag-exprp-and-equal-of-quote-and-car-forward-to-true-listp
  (implies (and (bounded-dag-exprp nodenum expr)
                (eq 'quote (car expr)))
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     ;dargs ;todo: this theorem happens to be true for quoteps too
                                     ))))

(defthm true-listp-of-dargs-when-bounded-dag-exprp-and-consp
  (implies (and (bounded-dag-exprp nodenum expr)
                (not (symbolp expr)) ;or say (consp expr)
                )
           (true-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0 dargs))))

(defthm true-listp-of-dargs-better
  (implies (and (bounded-dag-exprp nodenum expr)
                ;; (not (equal 'quote (car expr)))
                )
           (true-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0 dargs))))

(defthm bounded-dag-exprp-and-consp-forward-to-symbolp-of-car
  (implies (and (bounded-dag-exprp nodenum expr)
                (consp expr))
           (symbolp (car expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-and-not-consp-forward-to-symbolp
  (implies (and (bounded-dag-exprp nodenum expr)
                (not (consp expr)))
           (symbolp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-forward-to-all-dargp-of-dargs
  (implies (and (bounded-dag-exprp nodenum expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (all-dargp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm dag-exprp0-when-bounded-dag-exprp
  (implies (bounded-dag-exprp nodenum expr) ;free var
           (dag-exprp0 expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0))))

(defthm bounded-dag-exprp-monotone
  (implies (and (bounded-dag-exprp nodenum2 expr) ;nodenum2 is a free var
                (<= nodenum2 nodenum))
           (bounded-dag-exprp nodenum expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm <-of-nth-of-dargs
  (implies (and (bounded-dag-exprp nodenum expr)
                (< n2 (len (dargs expr)))
                (natp n2)
                (not (equal 'quote (car expr)))
                (not (consp (nth n2 (dargs expr)))) ;rules out a quotep
                )
           (< (nth n2 (dargs expr)) nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp <-OF-NTH-WHEN-ALL-DARGP-LESS-THAN))))

(defthm symbolp-of-car-when-bounded-dag-exprp
  (implies (bounded-dag-exprp nodenum expr) ;nodenum is a free var
           (symbolp (car expr)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm all-dargp-less-than-of-0
  (equal (all-dargp-less-than items 0)
         (all-myquotep items))
  :hints (("Goal" :in-theory (enable all-myquotep))))

(defthm bounded-dag-exprp-when-symbolp-cheap
  (implies (symbolp var)
           (bounded-dag-exprp n var))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;not tight?
(defthmd bound-lemma-for-car-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items n)
                (consp items)
                (not (consp (car items))))
           (not (< n (car items))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

;;;
;;; largest-non-quotep
;;;

;; Return the largest nodenum in the ITEMS, each of which should be a nodenum
;; or a quoted constant.  If ITEMS contains no nodenums, return -1.
(defund largest-non-quotep (items)
  (declare (xargs :guard (and (true-listp items)
                              (all-dargp items))))
  (if (endp items)
      -1 ;think about this as the default
    (let ((item (car items)))
      (if (consp item) ; skip quoteps
          (largest-non-quotep (cdr items))
        (max (mbe :logic (nfix item)
                  :exec item)
             (largest-non-quotep (cdr items)))))))

(defthm integerp-of-largest-non-quotep
  (integerp (largest-non-quotep items))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable all-dargp largest-non-quotep))))

(defthm largest-non-quotep-of-cons
  (implies (and (dargp arg)
                (all-dargp args))
           (equal (largest-non-quotep (cons arg args))
                  (if (consp arg)
                      (largest-non-quotep args)
                    (max arg (largest-non-quotep args)))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-of-cdr-bound
  (<= (largest-non-quotep (cdr items)) (largest-non-quotep items))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound-linear
  (<= -1 (largest-non-quotep items))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound
  (implies (natp (car items))
           (<= (car items) (largest-non-quotep items)))
  :rule-classes (:rewrite (:linear :trigger-terms ((largest-non-quotep items))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-bound-alt
  (implies (natp (nth 0 items))
           (<= (nth 0 items) (largest-non-quotep items)))
  :rule-classes (:rewrite (:linear :trigger-terms ((largest-non-quotep items))))
  :hints (("Goal" :use (:instance largest-non-quotep-bound)
           :in-theory (disable largest-non-quotep-bound))))

(defthm natp-of-largest-non-quotep
  (implies (and (all-dargp items)
                (not (all-myquotep items)))
           (natp (largest-non-quotep items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable ALL-DARGP LARGEST-NON-QUOTEP))))

(defthm natp-of-largest-non-quotep-2
  (implies (all-dargp items)
           (equal (natp (largest-non-quotep items))
                  (not (equal -1 (largest-non-quotep items))))))

(defthm equal-of--1-and-largest-non-quotep
  (implies (all-dargp items)
           (equal (equal -1 (largest-non-quotep items))
                  (all-myquotep items)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm <-of-largest-non-quotep
  (implies (and (all-dargp-less-than args nodenum)
    ;(natp nodenum)
                (<= 0 NODENUM)
                )
           (< (largest-non-quotep args)
              nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep all-dargp-less-than))))

;this weaker version is needed to match right
(defthm <=-of-largest-non-quotep
  (implies (and (all-dargp-less-than args nodenum)
                (natp nodenum))
           (<= (largest-non-quotep args)
               nodenum))
  :hints (("Goal" :in-theory (enable largest-non-quotep all-dargp-less-than))))

(defthm largest-non-quotep-when-all-myquotep-cheap
  (implies (all-myquotep items)
           (equal (largest-non-quotep items)
                  -1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm largest-non-quotep-when-all-consp-cheap
  (implies (all-consp items)
           (equal (largest-non-quotep items)
                  -1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

(defthm <-of-1-and-len-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (natp n)
                (< n (len args)))
           (equal (< 1 (len (nth n args)))
                  (consp (nth n args))))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than dargp-less-than nth) ()))))

(defthm natp-of-nth-when-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (natp n)
                (< n (len vals)))
           (equal (natp (nth n vals))
                  (not (consp (nth n vals)))))
  :hints
  (("Goal" :in-theory (enable all-dargp-less-than))))

;true whether it's a quotep or nodenum
(defthmd not-cddr-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items bound)
         ;       (consp item)
                (member-equal item items))
           (not (cddr item)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm not-cddr-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound) ;bound is a free var
                (natp n)
                (< n (len args)))
           (not (cddr (nth n args))))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm all-dargp-less-than-of-reverse-list
  (equal (all-dargp-less-than (reverse-list items) bound)
         (all-dargp-less-than items bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than reverse-list))))

(defthm dargp-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (< n (len args))
                (natp n))
           (dargp (nth n args)))
  :hints (("Goal" :in-theory (e/d (all-dargp) ()))))

(defthm not-<-of-plus1-of-largest-non-quotep
  (implies (and (bounded-dag-exprp nodenum expr)
                (natp nodenum)
                ;; (consp expr)
                (not (EQUAL 'QUOTE (CAR EXPR)))
                )
           (not (< nodenum (+ 1 (largest-non-quotep (dargs expr))))))
  :hints (("Goal" :in-theory (e/d (bounded-dag-exprp
                                   dag-exprp0
                                   dargs-when-not-consp-cheap)
                                  (<-of-largest-non-quotep))
           :use (:instance <-of-largest-non-quotep (args (dargs expr))))))

;consider using polarities
(defthm myquotep-when-bounded-dag-exprp
  (implies (bounded-dag-exprp nodenum expr)
           (equal (myquotep expr)
                  (equal 'quote (car expr))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dag-exprp0))))

(defthm all-dargp-less-than-of-dargs-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp nodenum expr)
                ;; (consp expr)
                (not (equal 'quote (car expr))))
           (all-dargp-less-than (dargs expr) nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp
                                     dargs-when-not-consp-cheap))))

(defthm natp-of-+-of-a-and-largest-non-quotep
  (implies (all-dargp items)
           (natp (+ 1 (largest-non-quotep items))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

;; We use consp as the normal form
(defthm symbolp-when-bounded-dag-exprp
  (implies (bounded-dag-exprp nodenum expr) ;nodenum is a free var
           (equal (symbolp expr)
                  (not (consp expr)))))

;; ;drop?
;; (defthm dargp-when-bounded-dag-exprp
;;   (implies (bounded-dag-exprp nodenum expr)
;;            (equal (dargp expr)
;;                   (equal 'quote (car expr))))
;;   :hints (("Goal" :in-theory (enable dargp dag-exprp0))))

(defthm bounded-dag-exprp-when-myquotep-cheap
  (implies (myquotep expr)
           (bounded-dag-exprp nodenum expr))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthmd bounded-dag-exprp-when-myquotep
  (implies (myquotep expr)
           (bounded-dag-exprp nodenum expr))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm bounded-dag-exprp-when-equal-of-quote-and-car-cheap
  (implies (equal 'quote (car expr))
           (equal (bounded-dag-exprp nodenum expr)
                  (myquotep expr)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))
