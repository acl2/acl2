; DAGs represented in arrays
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

;; This books contains notions related to DAGs represented using ACL2 arrays,
;; as is done internally by Axe.

(include-book "dags") ;for pseudo-dagp
(include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system)
(include-book "kestrel/acl2-arrays/expandable-arrays" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "rational-lists")
(local (include-book "kestrel/lists-light/memberp" :dir :system))
;(include-book "kestrel/utilities/polarity" :dir :system) ;drop?
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;move
(in-theory (disable true-listp ;looped?
                    ))

(defthm memberp-of-nth-and-cdr
  (implies (posp n)
           (equal (memberp (nth n lst) (cdr lst))
                  (if (< n (len lst))
                      t
                    (memberp nil (cdr lst))
                    )))
  :hints (("Goal" :in-theory (e/d (memberp nth NTH-WHEN-<=-LEN)
                                  (nth-of-cdr)))))

(local (in-theory (enable len-when-dargp-less-than)))

(defund array-len-with-slack (len slack-amount)
  (declare (xargs :guard (and (posp len)
                              (natp slack-amount))))
  ;; don't exceed the max array length:
  (min *maximum-1-d-array-length*
       (+ len slack-amount)))

(defthm integerp-of-array-len-with-slack
  (implies (and (integerp len)
                (integerp slack-amount))
           (integerp (array-len-with-slack len slack-amount)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable array-len-with-slack))))

(defthm array-len-with-slack-linear
  (< (array-len-with-slack len slack-amount)
     2147483647)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable array-len-with-slack))))

(defthm array-len-with-slack-linear-2
  (implies (and (<= 0 SLACK-AMOUNT)
                (<= LEN 2147483646))
           (<= len (array-len-with-slack len slack-amount)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable array-len-with-slack))))

;; A DAG in array form is represented by 5 components:
; dag-array - maps nodenums to exprs, which are: variables, quoted constants, or function calls applied to lists of args (nodenums and quoted constants)
; dag-len - the number of valid nodes in the DAG
; dag-parent-array - maps each nodenum to the list of its parents - does soundness depend on this? yes? no dups in the list?
; dag-constant-alist - maps constants and ground terms (function calls whose args are all quoted constants) to their nodenums in the DAG
; dag-variable-alist - maps variables to their nodenums in the DAG
;fixme are the auxiliary data structures updated right when nodes are dropped?

;;
;; pseudo-dag-arrayp-aux
;;

(defund pseudo-dag-arrayp-aux (array-name array top-nodenum-to-check)
  (declare (xargs :measure (nfix (+ 1 top-nodenum-to-check))
                  :guard (and (array1p array-name array)
                              (integerp top-nodenum-to-check)
                              (< top-nodenum-to-check (alen1 array-name array)))))
  (if (not (natp top-nodenum-to-check))
      t
    (let ((expr (aref1 array-name array top-nodenum-to-check)))
      (and (bounded-dag-exprp top-nodenum-to-check expr)
           (pseudo-dag-arrayp-aux array-name array (+ -1 top-nodenum-to-check))))))

(defthm pseudo-dag-arrayp-aux-of-minus1
  (pseudo-dag-arrayp-aux array-name array -1)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

(defthm pseudo-dag-arrayp-aux-monotone
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (<= m n)
                (integerp m)
                (integerp n);(natp n)
                )
           (pseudo-dag-arrayp-aux dag-array-name dag-array m))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

;;;
;;; pseudo-dag-arrayp (this does check every node, starting at top-nodenum-to-check, with no gaps)
;;;

(defund pseudo-dag-arrayp (dag-array-name dag-array dag-len)
  (declare (xargs :guard t))
  (and (array1p dag-array-name dag-array)
       (natp dag-len) ;allowing 0 lets us talk about empty pseudo-dag-arrays
       (<= dag-len (alen1 dag-array-name dag-array))
       (pseudo-dag-arrayp-aux dag-array-name dag-array (+ -1 dag-len))))

(defthm array1p-when-pseudo-dag-arrayp
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (array1p dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-chaining
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (<= dag-len (alen1 dag-array-name dag-array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-chaining-another
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (<= 1 (alen1 dag-array-name dag-array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-to-natp-arg3
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (natp dag-len))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-to-symbolp-arg1
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (symbolp dag-array-name))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-to-<=-of-alen1
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (<= (alen1 dag-array-name dag-array) 2147483646))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-forward-4
  (implies (pseudo-dag-arrayp array-name array dag-len)
           (<= dag-len 2147483646))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-monotone
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array n)
                (<= m n)
                (natp m)
                (integerp n))
           (pseudo-dag-arrayp dag-array-name dag-array m))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

;limit?
;; (defthm true-listp-of-cdr-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n) ;allow this n to differ?
;;                 (natp n)
;;                 (consp (aref1 dag-array-name dag-array n))
;;                 (not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
;;                 (< n (car (dimensions dag-array-name dag-array))))
;;            (true-listp (cdr (aref1 dag-array-name dag-array n))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable pseudo-dag-arrayp-aux))))

;no free var
(defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-simple
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp n)
                ;(not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
                ;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                )
           (true-listp (dargs (aref1 dag-array-name dag-array n))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (pseudo-dag-arrayp-aux) (bounded-dag-exprp)))))

(defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< n dag-len)
                (natp n)
;(not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                )

           (true-listp (dargs (aref1 dag-array-name dag-array n))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                (natp n)
                ;;(not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
                ;;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                )
           (true-listp (dargs (aref1 dag-array-name dag-array n))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum-to-check)
                (natp n)
                (integerp top-nodenum-to-check)
;                (not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
                ;;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                (<= n top-nodenum-to-check))
           (true-listp (dargs (aref1 dag-array-name dag-array n))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
  ;         :cases ((symbolp (aref1 dag-array-name dag-array n)))
           :in-theory (e/d (pseudo-dag-arrayp-aux) (bounded-dag-exprp)))))

(defthm all-dargp-less-than-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array m)
                (<= n m)
                (natp n)
                (integerp m)
;                (consp (aref1 dag-array-name dag-array n))
                (not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
;                (< n (car (dimensions dag-array-name dag-array)))
                (<= n bound)
                (integerp bound)
                )
           (ALL-DARGP-LESS-THAN (dargs (aref1 dag-array-name dag-array n)) bound))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dag-arrayp-aux
                              dargs-when-not-consp-cheap))))

(defthm all-dargp-less-than-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< n dag-len)
                (natp n)
;                (consp (aref1 dag-array-name dag-array n))
                (not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
;                (< n (car (dimensions dag-array-name dag-array)))
                (<= n bound)
                (integerp bound)
                )
           (all-dargp-less-than (dargs (aref1 dag-array-name dag-array n)) bound))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm all-dargp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array m)
                (<= n m)
                (natp n)
                (integerp m)
                (consp (aref1 dag-array-name dag-array n))
                (not (eq 'quote
                         (ffn-symb (aref1 dag-array-name dag-array n)))))
           (all-dargp (dargs (aref1 dag-array-name dag-array n))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (bounded-dag-exprp m (aref1 dag-array-name dag-array m))
           :in-theory (enable pseudo-dag-arrayp-aux))))

(local
 (defthmd bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp n))
           (bounded-dag-exprp n (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dag-arrayp-aux)))))

(defthm bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp m)
                (<= m n)
                (natp n))
           (bounded-dag-exprp m (aref1 dag-array-name dag-array m)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper))))

(defthm bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-gen
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp m)
                (<= m n)
                (natp n)
                (<= m bound))
           (bounded-dag-exprp bound (aref1 dag-array-name dag-array m)))
  :hints (("Goal" :use (bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
           :in-theory (disable bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux))))

(defthm bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                (<= n m)
                (integerp m)
                (natp n))
           (bounded-dag-exprp m (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :in-theory (e/d (pseudo-dag-arrayp
                                   BOUNDED-DAG-EXPRP ;prove a monotone rule for this
                                   ) (bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux))
           :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                           (m n)))))

(defthm symbolp-of-aref1-when-pseudo-dag-arrayp-aux-and-not-consp
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (not (consp (aref1 dag-array-name dag-array nodenum)))
                (natp nodenum))
           (symbolp (aref1 dag-array-name dag-array nodenum)))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)))))

(defthm cdr-of-aref1-when-PSEUDO-DAG-ARRAYP-AUX-and-quotep
  (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY n)
                (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY m)))
                (<= m n)
                (integerp n)
                (natp m))
           (cdr (AREF1 DAG-ARRAY-NAME DAG-ARRAY m)))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
           :in-theory (e/d (BOUNDED-DAG-EXPRP dag-exprp0 CAR-BECOMES-NTH-OF-0)
                           (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-GEN)))))

(defthm consp-of-cdr-of-aref1-when-PSEUDO-DAG-ARRAYP-AUX-and-quotep
  (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY n)
                (EQUAL 'QUOTE (car (AREF1 DAG-ARRAY-NAME DAG-ARRAY m)))
                (integerp n)
                (natp m)
                (<= m n))
           (consp (CDR (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
           :in-theory (e/d (bounded-DAG-EXPRP; CAR-BECOMES-NTH-OF-0
                            dag-exprp0
                            )
                           (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-GEN)))))

(defthm symbolp-of-car-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;                (consp (aref1 dag-array-name dag-array nodenum))
                (natp nodenum)
;                (< nodenum (car (dimensions dag-array-name dag-array)))
                )
           (symbolp (car (aref1 dag-array-name dag-array nodenum))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                                  (dag-array-name dag-array-name)
                                  (m nodenum)
                                  (n nodenum))
           :in-theory (disable bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                               BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-GEN))))



;; (defthm ALL-DARGP-of-cdr-of-aref1-when-PSEUDO-DAG-ARRAYP-AUX-and-len-1
;;   (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY n)
;;                 (natp n)
;;                 (natp m)
;;                 (<= m n)
;;                 (EQUAL (LEN (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))
;;                      1))
;;            (ALL-DARGP (CDR (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))))
;;   :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :in-theory (e/d (BOUNDED-DAG-EXPRP CAR-BECOMES-NTH-OF-0)
;;                            (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))


;; (defthm true-listp-of-aref1-when-PSEUDO-DAG-ARRAYP-AUX-and-len-1
;;   (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY n)
;;                 (natp n)
;;                 (natp m)
;;                 (<= m n)
;;                 (EQUAL (LEN (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))
;;                      1))
;;            (true-listp (AREF1 DAG-ARRAY-NAME DAG-ARRAY m)))
;;   :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :in-theory (e/d (BOUNDED-DAG-EXPRP CAR-BECOMES-NTH-OF-0)
;;                            (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

;; ;not true...  could change bounded-dag-exprp to make it true..
;; (defthm len-when-PSEUDO-DAG-ARRAYP-AUX-and-quotep
;;   (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY n)
;;                 (natp n)
;;                 (natp m)
;;                 (<= m n)
;;                 (EQUAL (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))
;;                        'QUOTE))
;;            (EQUAL (LEN (AREF1 DAG-ARRAY-NAME DAG-ARRAY m))
;;                   2))
;;   :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :in-theory (e/d (BOUNDED-DAG-EXPRP CAR-BECOMES-NTH-OF-0)
;;                            (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

;; (defthm true-listp-of-cdddr-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (cddr (dargs (aref1 dag-array-name dag-array nodenum)))))
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (enable pseudo-dag-arrayp-aux))))

;; (defthm true-listp-of-cdddr-of-aref1-when-pseudo-dag-arrayp-aux-type
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (cddr (dargs (aref1 dag-array-name dag-array nodenum)))))
;;   :rule-classes ((:type-prescription)))

;; (defthm true-listp-of-cddr-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (cdr (dargs (aref1 dag-array-name dag-array nodenum)))))
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (enable pseudo-dag-arrayp-aux))))

;; (defthm true-listp-of-cddr-of-aref1-when-pseudo-dag-arrayp-aux-type
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (cdr (dargs (aref1 dag-array-name dag-array nodenum)))))
;;   :rule-classes ((:type-prescription)))

;avoid name clash
;; (defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-no-clash
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (dargs (aref1 dag-array-name dag-array nodenum))))
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (enable pseudo-dag-arrayp-aux))))

;; (defthm true-listp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-type
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            (true-listp (dargs (aref1 dag-array-name dag-array nodenum))))
;;   :rule-classes ((:type-prescription)))

(defthm <-when-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (member-equal val vals)
                (not (consp val)) ;not a quotep
                )
           (< val bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

;; we'll use consp or "not consp" as the normal form for reasoning about
;; whether dag args are nodenums or quoteps.
(defthm natp-when-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (member-equal val vals))
           (equal (natp val)
                  (not (consp val)) ;not a quotep
                  ))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

(defthmd natp-of-car-when-all-dargp-less-than-gen
  (implies (all-dargp-less-than vals bound)
           (equal (natp (car vals))
                  (and (consp vals)
                       (not (consp (car vals))) ;not a quotep
                       )))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

(defthm quote-lemma-for-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (member-equal val vals)
;                (not (consp val)) ;not a quotep
                )
           (equal (equal 'quote (nth 0 val))
                  (consp val)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

(defthm quote-lemma-for-all-dargp-less-than-gen-alt
  (implies (and (all-dargp-less-than vals bound)
                (member-equal val vals)
;                (not (consp val)) ;not a quotep
                )
           (equal (equal 'quote (car val))
                  (consp val)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

(defthmd consp-cdr-lemma-for-all-dargp-less-than-gen
  (implies (and (all-dargp-less-than vals bound)
                (member-equal val vals)
;                (not (consp val)) ;not a quotep
                )
           (equal (consp (cdr val))
                  (consp val)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than memberp))))

(in-theory (disable PSEUDO-DAG-ARRAYP-AUX))

(defthm nth-when-not-cddr
  (implies (and (not (cddr x))
                (<= 2 n)
                (natp n))
           (equal (nth n x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (e/d (nth len) (len-of-cdr nth-of-cdr)))))

(defthm <-of-len-when-integerp-of-nth
  (implies (and (INTEGERP (NTH n x))
                (natp n))
           (< n (len x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable NTH-WHEN-<=-LEN))))

(defthm <-of-len-when-nth-non-nil
  (implies (and (nth n x)
                (natp n))
           (< n (len x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable NTH-WHEN-<=-LEN))))



(defthmd len-bound-when-not-cddr
  (implies (not (cddr x))
           (<= (len x) 2))
  :rule-classes :linear)

(local (in-theory (enable len-bound-when-not-cddr)))




;todo: don't retest the array1p etc for each index
;todo: put nodenum/quoteps arg last!
(defund pseudo-dag-arrayp-list (nodenum/quoteps dag-array-name dag-array)
  (declare (xargs :guard t))
  (if (atom nodenum/quoteps)
      t
    (let ((item (first nodenum/quoteps)))
      (and (or (myquotep item)
               (and (natp item)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 item))))
           (pseudo-dag-arrayp-list (rest nodenum/quoteps) dag-array-name dag-array)))))

(defthm pseudo-dag-arrayp-list-of-cdr
  (implies (pseudo-dag-arrayp-list nodenum/quoteps dag-array-name dag-array)
           (pseudo-dag-arrayp-list (cdr nodenum/quoteps) dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list))))


(defthm pseudo-dag-arrayp-list-when-all-dargp-less-than
  (implies (and (all-dargp-less-than lst nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (pseudo-dag-arrayp-list lst dag-array-name dag-array))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dag-arrayp-list all-dargp-less-than))))

(defthm pseudo-dag-arrayp-list-when-all-dargp-less-than-special
  (implies (and (all-dargp-less-than lst nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (natp nodenum)
                ;;(< dag-len nodenum)
                )
           (pseudo-dag-arrayp-list lst dag-array-name dag-array))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ALL-DARGP-LESS-THAN))))

(defthm pseudo-dag-arrayp-list-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum))
           (pseudo-dag-arrayp-list (dargs (aref1 dag-array-name dag-array nodenum)) dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list
                                     pseudo-dag-arrayp
                                     dargs-when-not-consp-cheap
                                     bounded-dag-exprp ;why?
                                     )
           :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)))))

;for when we turn car into nth of 0
;rename
(defthm <-of-nth-and-alen1
  (implies (and (pseudo-dag-arrayp-list nodenums-or-quoteps dag-array-name dag-array)
                (true-listp nodenums-or-quoteps)
                (consp nodenums-or-quoteps)
                (not (consp (nth 0 nodenums-or-quoteps))))
           (< (nth 0 nodenums-or-quoteps)
              (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list pseudo-dag-arrayp))))

(defthm dag-exprp0-of-aref1-when-bounded-dag-exprp-of-aref1
  (implies (bounded-dag-exprp nodenum (aref1 dag-array-name dag-array nodenum))
           (dag-exprp0 (aref1 dag-array-name dag-array nodenum)))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm dag-exprp0-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp n))
           (dag-exprp0 (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array n))
           :in-theory (enable bounded-dag-exprp))))

(defthm dag-exprp0-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                (natp n))
           (dag-exprp0 (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array n))
           :in-theory (enable bounded-dag-exprp pseudo-dag-arrayp))))

;; We normalize claims about dag-args to consp.
(defthm consp-of-cdr-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                (natp nodenum)
                )
           (equal (consp (cdr (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) (dag-exprp0)))))

;; We normalize claims about dag-args to consp.
(defthm equal-of-quote-and-nth-0-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                (natp nodenum)
                )
           (equal (equal 'quote (nth 0 (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
           :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
                                                  ;;LIST::LEN-OF-CDR-BETTER
                                                  )
                           (len)))))

;; same as above except uses car instead of nth 0
(defthm equal-of-quote-and-car-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp nodenum)
                (natp n);drop?
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (equal 'quote (car (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

(defthm myquotep-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp nodenum)
                (natp n);drop?
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (myquotep (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :in-theory (e/d (pseudo-dag-arrayp-aux)
                                  (myquotep)))))

(defthm dargp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp nodenum)
                (natp n);drop?
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                )
           (dargp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (e/d (pseudo-dag-arrayp-aux DARGP-OF-NTH-WHEN-ALL-DARGP)
                                  (DARGP)))))

(defthm dargp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (natp nodenum)
                (natp n);drop?
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                )
           (dargp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (e/d (pseudo-dag-arrayp)
                                  (DARGP)))))

;todo
;; (defthm natp-of-nth-of-dargs-of-aref1
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp n)
;;                 (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (natp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
;;   :rule-classes (:rewrite :forward-chaining)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm integerp-of-nth-of-aref1
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (aref1 dag-array-name dag-array nodenum)))
;;                 (posp n)
;;                 (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (integerp (nth n (aref1 dag-array-name dag-array nodenum))))
;;   :rule-classes (:rewrite :forward-chaining)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

(defthm nonneg-of-nth-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                ;(< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (not (EQUAL 'QUOTE (car (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;                (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                (natp nodenum)
                )
           (<= 0 (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :rule-classes (:rewrite :forward-chaining :linear)
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper (n nodenum))
           :cases ((< n (len (dargs (aref1 dag-array-name dag-array nodenum)))))
           ;; :cases ((consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
           ;; :expand ((PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0))
           :in-theory (e/d (<-of-nth-when-all-dargp-less-than)
                           (bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                             DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                             ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1)))))

(defthm eqlable-listp-when-integer-listp-cheap
  (implies (integer-listp x)
           (eqlable-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;TODO: some of this may duplicate some stuff above

(local (in-theory (enable NTH-WHEN-<=-LEN)))

;; (defthm natp-of-nth-of-aref1-when-dag-exprp
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node))))
;;                 )
;;            (equal (natp (nth n (aref1 'dag-array dag-array node)))
;;                   (if (< n (len (aref1 'dag-array dag-array node)))
;;                       (not (consp (nth n (aref1 'dag-array dag-array node))))
;;                     nil)))
;;   :hints (("Goal" :use (:instance natp-when-all-dargp-less-than-gen
;;                                   (val (nth n (aref1 'dag-array dag-array node)))
;;                                   (vals (cdr (aref1 'dag-array dag-array node)))
;;                                   (bound node))
;;            :in-theory (disable natp-when-all-dargp-less-than-gen))))

;; (defthm integerp-of-nth-of-aref1-when-dag-exprp
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node))))
;;                 )
;;            (equal (integerp (nth n (aref1 'dag-array dag-array node)))
;;                   (if (< n (len (aref1 'dag-array dag-array node)))
;;                       (not (consp (nth n (aref1 'dag-array dag-array node))))
;;                     nil)))
;;   :hints (("Goal" :use (:instance natp-of-nth-of-aref1-when-dag-exprp)
;;            :in-theory (disable natp-of-nth-of-aref1-when-dag-exprp))))

;; (defthm nonneg-of-nth-of-aref1-when-dag-exprp
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 ;(< n (len (aref1 'dag-array dag-array node)))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node))))
;;                 (not (consp (nth n (aref1 'dag-array dag-array node)))))
;;            (<= 0 (nth n (aref1 'dag-array dag-array node))))
;;   :hints (("Goal" :use (:instance natp-of-nth-of-aref1-when-dag-exprp)
;;            :in-theory (disable natp-of-nth-of-aref1-when-dag-exprp))))

;; (defthm consp-of-cdr-of-nth-of-aref1-when-dag-exprp
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 (< n (len (aref1 'dag-array dag-array node)))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node)))))
;;            (equal (consp (cdr (nth n (aref1 'dag-array dag-array node))))
;;                   (consp (nth n (aref1 'dag-array dag-array node))))))

(in-theory (disable INTEGER-LISTP))

;; (defthm equal-quote-nth-0-lemma-for-nth-of-aref1-when-dag-exprp
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node))))
;;                 )
;;            (equal (equal 'quote (nth 0 (nth n (aref1 'dag-array dag-array node))))
;;                   (if (< n (len (aref1 'dag-array dag-array node)))
;;                       (consp (nth n (aref1 'dag-array dag-array node)))
;;                     nil)))
;;   :hints (("Goal" :use (:instance quote-lemma-for-all-dargp-less-than-gen
;;                                   (val (nth n (aref1 'dag-array dag-array node)))
;;                                   (vals (cdr (aref1 'dag-array dag-array node)))
;;                                   (bound node))
;;            :in-theory (disable natp-when-all-dargp-less-than-gen))))

;; (defthm nth-0-of-nth-of-aref1
;;   (implies (and (bounded-dag-exprp node (aref1 'dag-array dag-array node))
;;                 (posp n)
;;                 (not (equal 'quote (car (aref1 'dag-array dag-array node))))
;;                 (< n (len (aref1 'dag-array dag-array node)))
;;                 (consp (nth n (aref1 'dag-array dag-array node)))
;;                 )
;;            (equal (nth 0 (nth n (aref1 'dag-array dag-array node)))
;;                   'quote))
;;   :hints (("Goal" :use (:instance quote-lemma-for-all-dargp-less-than-gen
;;                                   (val (nth n (aref1 'dag-array dag-array node)))
;;                                   (vals (cdr (aref1 'dag-array dag-array node)))
;;                                   (bound node))
;;            :in-theory (disable natp-when-all-dargp-less-than-gen))))

;; for termination:

;; todo: compare to largest-non-quotep
(defund greatest-nodenum-in-list (nodenum-or-quoteps)
  (declare (xargs :guard (and (true-listp nodenum-or-quoteps)
                              (all-dargp nodenum-or-quoteps))))
  (if (endp nodenum-or-quoteps)
      -1
    (let ((nodenum-or-quotep (first nodenum-or-quoteps)))
      (if (consp nodenum-or-quotep)
          ;; it's a quotep, so skip it:
          (greatest-nodenum-in-list (rest nodenum-or-quoteps))
        (max (nfix nodenum-or-quotep) ;force the result to be an integer
             (greatest-nodenum-in-list (rest nodenum-or-quoteps)))))))

(defthm greatest-nodenum-in-list-bound
  (<= -1 (greatest-nodenum-in-list nodenum-or-quoteps))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

(defthm integerp-of-greatest-nodenum-in-list
  (integerp (greatest-nodenum-in-list nodenum-or-quoteps))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

(defthm <-of-greatest-nodenum-in-list-when-all-dargp-less-than
  (implies (and (all-dargp-less-than items nodenum)
                (natp nodenum))
           (< (greatest-nodenum-in-list items)
              nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

;; (thm
;;  (implies (INTEGERP (GREATEST-NODENUM-IN-LIST (CDR NODENUM-OR-QUOTEPS)))
;;           (INTEGERP (GREATEST-NODENUM-IN-LIST NODENUM-OR-QUOTEPS))

(defthm greatest-nodenum-in-list-bound2
  (<= (greatest-nodenum-in-list (cdr nodenum-or-quoteps))
      (greatest-nodenum-in-list nodenum-or-quoteps))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

(defthm greatest-nodenum-in-list-bound3
  (IMPLIES (AND (CONSP NODENUM-OR-QUOTEPS)
                (NOT (CONSP (CAR NODENUM-OR-QUOTEPS))))
           (<= 0 (GREATEST-NODENUM-IN-LIST NODENUM-OR-QUOTEPS)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

(defthm greatest-nodenum-in-list-bound4
  (IMPLIES (AND (CONSP NODENUM-OR-QUOTEPS)
                (NOT (CONSP (CAR NODENUM-OR-QUOTEPS)))
                (integerp (CAR NODENUM-OR-QUOTEPS)))
           (<= (car NODENUM-OR-QUOTEPS) (GREATEST-NODENUM-IN-LIST NODENUM-OR-QUOTEPS)))
  :rule-classes (:rewrite (:linear :trigger-terms ((GREATEST-NODENUM-IN-LIST NODENUM-OR-QUOTEPS))))
  :hints (("Goal" :in-theory (enable greatest-nodenum-in-list))))

(mutual-recursion
 ;; Create a term corresponding to the given nodenum or quotep.
 (defund dag-to-term-aux-array (dag-array-name dag-array nodenum-or-quotep)
   (declare (xargs :measure (make-ord 1
                                      (if (consp nodenum-or-quotep) ;check for quotep
                                          1 ;ordinal coeff must be positive
                                        (+ 2 (nfix nodenum-or-quotep))) ;add 2 to make this greater than in the other branch (necessary?)
                                      0)
                   :guard (and (dargp nodenum-or-quotep)
                               (if (consp nodenum-or-quotep)
                                   t
                                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))))
                   :guard-hints (("Goal" :in-theory (enable pseudo-dag-arrayp)))))
   (if (quotep nodenum-or-quotep)
       nodenum-or-quotep
     (and (mbt (natp nodenum-or-quotep)) ;for termination ;drop somehow?
          (let ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
            (if (or (variablep expr)
                    (quotep expr))
                expr
              ;;function call
              (let ((args (dargs expr)))
                (if (not (mbt (all-dargp-less-than args nodenum-or-quotep)))
                    (er hard 'dag-to-term-aux "Child not less than parent: ~x0" expr)
                  (cons (ffn-symb expr)
                        (dag-to-term-aux-lst-array dag-array-name dag-array args)))))))))

 ;; Create a list of terms corresponding to the given nodenums / quoteps.
 (defund dag-to-term-aux-lst-array (dag-array-name dag-array nodenum-or-quoteps)
   (declare (xargs :measure (make-ord 1
                                      (+ 2 (greatest-nodenum-in-list nodenum-or-quoteps)) ;add 2 because it might be -1 and ordinal coeffs must be positive
                                      (len nodenum-or-quoteps))
                   :guard (and (all-dargp nodenum-or-quoteps)
                               (true-listp nodenum-or-quoteps)
                               (if (all-myquotep nodenum-or-quoteps)
                                   t
                                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (largest-non-quotep nodenum-or-quoteps)))))))
   (if (endp nodenum-or-quoteps)
       nil
     (cons (dag-to-term-aux-array dag-array-name dag-array (car nodenum-or-quoteps))
           (dag-to-term-aux-lst-array dag-array-name dag-array (cdr nodenum-or-quoteps))))))

(defthm not-cddr-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
        ;       (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n) ;; drop?
;                (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))) ;means the arg is a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a constant
;                (not (symbolp (aref1 dag-array-name dag-array nodenum))) ;excludes the whole node from being a variable
                )
           (not (cddr (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" ;:in-theory (enable not-cddr-when-all-dargp-less-than)
           :use (:instance not-cddr-when-all-dargp-less-than
                           (item (NTH N (dargs (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))))
                           (bound nodenum)
                           (items (dargs (aref1 dag-array-name dag-array nodenum)))
                           )
           :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)))))

;should be cheap, but this is hung on len...
(defthm len-when-bounded-dag-exprp-and-quotep
  (implies (and (bounded-dag-exprp nodenum expr) ;nodenum is a free var
                (equal 'quote (car expr)))
           (equal (len expr)
                  2))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;might be slow?
(defthm len-of-aref1-when-quotep-and-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array arg)
                (equal 'quote (car (aref1 dag-array-name dag-array arg)))
                (natp arg)
                )
           (equal (len (aref1 dag-array-name dag-array arg))
                  2))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array arg))
           :in-theory (enable dag-exprp0))))

;might be slow
(defthm not-equal-of-car-and-quote-when-len-wrong-and-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array arg)
                (not (equal (len (aref1 dag-array-name dag-array arg))
                            2))
                (natp arg))
           (not (equal 'quote (car (aref1 dag-array-name dag-array arg)))))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array arg)))))

;; In order for some of these to fire, we'll need cad...dr to be turned into
;; nth.

;; (defthm natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n) ;also rules out the expr from being a var (which would have len of 0 when tested above)
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (equal (natp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
;;                   (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)))))

;; (defthm integerp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n)
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (equal (integerp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
;;                   (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
;;                   ))
;;   :hints (("Goal" :use (:instance natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :in-theory (disable natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux))))

;; (defthm nonneg-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;         ;        (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n);drop?
;; ;                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (not (< (nth n (dargs (aref1 dag-array-name dag-array nodenum))) 0)))
;;   :hints (("Goal" :use (:instance natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :cases ((consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
;;            :in-theory (disable natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux))))

(defthm <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum))) nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper (n nodenum))
           ;; :cases ((consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
           ;; :expand ((PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0))
           :in-theory (e/d (<-of-nth-when-all-dargp-less-than)
                           ( bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                             DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                             ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1)))))

;;this one allows the bound to be >= nodenum
(defthm <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-gen
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp bound)
                (<= nodenum bound)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum))) bound))
  :hints (("Goal" :use (:instance <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux)
           :in-theory (disable <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux))))

(defthm not-<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-gen
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp bound)
                (<= nodenum bound)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (not (< bound
                   (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :use (:instance <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-gen)
           :in-theory (disable <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux-gen))))

(defthm <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum)))
              nodenum)))

(defthm <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-linear
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum)))
              nodenum))
  :rule-classes :linear)

(defthm <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-gen
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (<= dag-len bound)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (natp bound)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum)))
              bound)))

(defthm <-of-nth-of-dargs-of-aref1-and-alen1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< (nth n (dargs (aref1 dag-array-name dag-array nodenum)))
              (alen1 dag-array-name dag-array))))

;; (defthm not-<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-auxa
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n)
;;                 (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (not (< nodenum (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
;;   :hints (("Goal" :use (:instance <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux)
;;            :in-theory (disable <-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux))))

;; (defthm len-bound-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n);drop?
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (equal (< 1 (len (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
;;                   (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
;;   :hints (("Goal" :expand ((PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY NODENUM))
;;            :in-theory (e/d (len)
;;                            (len-of-cdr NONNEG-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX)))))

(defthmd len-bound-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (memberp item args)
                (not (natp item))
                )
           (<= 2 (len item)))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than
                                   MEMBERP
                                   ;CAR-BECOMES-NTH-OF-0 CONSP-FROM-LEN consp-to-len-bound  LIST::LEN-OF-CDR-BETTER
                                   )
                                  (;LIST::NTH-WITH-LARGE-INDEX len LIST::LEN-POS-REWRITE LIST::LEN-WHEN-AT-MOST-1
                                   len
                                   )))))

(defthmd len-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (memberp item args)
                (consp item)
                )
           (equal (len item)
                  2))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than
                                   MEMBERP
                                   ;CAR-BECOMES-NTH-OF-0 CONSP-FROM-LEN consp-to-len-bound  LIST::LEN-OF-CDR-BETTER
                                   )
                                  (;LIST::NTH-WITH-LARGE-INDEX len LIST::LEN-POS-REWRITE LIST::LEN-WHEN-AT-MOST-1
                                   len
                                   )))))

;; (defthm len-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum)
;;                 (natp n)                                                 ;drop?
;;                 (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))) ;the arg is a quotep
;;                 (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;;                 )
;;            (equal (len (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
;;                   2))
;;   :hints (("Goal" :in-theory (disable len-when-all-dargp-less-than)
;;            :use (:instance len-when-all-dargp-less-than
;;                            (item (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
;;                            (args (cdr (aref1 dag-array-name dag-array nodenum)))
;;                            (bound nodenum)))))


(defthmd len-of-nth-when-all-dargp-less-than-of-dargs
  (implies (and (all-dargp-less-than (dargs expr) bound)
                (natp n)
                (< n (len (dargs expr)))
                (not (natp (nth n (dargs expr)))))
           (<= 2 (len (nth n (dargs expr)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance len-bound-when-all-dargp-less-than
                                  (args (dargs expr))
                                  (item (nth n (dargs expr)))))))

;; ;drop?
;; (defthmd integerp-of-nth-when-all-dargp-less-than-of-cdr-weaken
;;   (implies (and (syntaxp (want-to-weaken (integerp (nth n expr))))
;;                 (all-dargp-less-than (cdr expr) bound)
;;                 (posp n)
;;                 (< n (len expr))
;;                 (not (natp (nth n expr))))
;;            (equal (integerp (nth n expr))
;;                   (or (not (equal 'quote (car (nth n expr))))
;;                       (not (< 1 (len (nth n expr)))))))
;;   :hints (("Goal" :use (:instance len-bound-when-all-dargp-less-than
;;                                   (args (fargs expr))
;;                                   (item (nth n expr)))
;;            :in-theory (disable ALL-DARGP-LESS-THAN-MONOTONE))))

(defthm <-of-1-and-len-of-nth-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp n)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (consp (aref1 dag-array-name dag-array nodenum))
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum))))
                ;(not (natp (nth n (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum))
           (equal (< 1 (len (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper (n nodenum))
           ;; :cases ((consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
           ;; :expand ((PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0))
           :in-theory (e/d (<-of-nth-when-all-dargp-less-than)
                           ( bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
                             bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                             DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                             ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1)))))


;; (defthm integerp-of-nth-of-aref1-when-pseudo-dag-arrayp-aux-weaken
;;   (implies (and (syntaxp (want-to-weaken (integerp (nth n (aref1 dag-array-name dag-array nodenum)))))
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (posp n)
;;                 (< n (len (aref1 dag-array-name dag-array nodenum)))
;;                 (consp (aref1 dag-array-name dag-array nodenum))
;;                 (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum))))
;;                 (not (SYMBOLP (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))))
;;                 (not (natp (nth n (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum))
;;            (equal (integerp (nth n (aref1 dag-array-name dag-array nodenum)))
;;                   (or (not (equal 'quotep (car (nth n (aref1 dag-array-name dag-array nodenum)))))
;;                       (not (< 1 (len (nth n (aref1 dag-array-name dag-array nodenum))))))))
;;   :hints (("Goal" :do-not-induct t
;;            :use (:instance integerp-of-nth-when-all-dargp-less-than-of-cdr-weaken
;;                            (expr (AREF1 DAG-ARRAY-NAME
;;                                         DAG-ARRAY NODENUM))
;;                            (bound nodenum)
;;                            )
;;            :expand (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))))

;; ;drop?
;; (defthm len-bound-of-nth-of-aref1-when-pseudo-dag-arrayp-aux-weaken
;;   (implies (and (syntaxp (want-to-weaken (< 1 (len (nth n (aref1 dag-array-name dag-array nodenum-or-quotep))))))
;;                 (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum-or-quotep)
;;                 (posp n)
;;                 (< n (len (aref1 dag-array-name dag-array nodenum-or-quotep)))
;;                 (consp (aref1 dag-array-name dag-array nodenum-or-quotep))
;;                 (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum-or-quotep))))
;;                 (not (SYMBOLP (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM-OR-QUOTEP))))
;;                 (not (natp (nth n (aref1 dag-array-name dag-array nodenum-or-quotep))))
;;                 (natp nodenum-or-quotep))
;;            (equal (< 1 (len (nth n (aref1 dag-array-name dag-array nodenum-or-quotep))))
;;                   (not (integerp (nth n (aref1 dag-array-name dag-array nodenum-or-quotep))))))
;;   :hints (("Goal" :do-not-induct t
;;            :use (:instance integerp-of-nth-when-all-dargp-less-than-of-cdr-weaken
;;                            (expr (AREF1 DAG-ARRAY-NAME
;;                                         DAG-ARRAY NODENUM-OR-QUOTEP))
;;                            (bound nodenum-or-quotep)
;;                            )
;;            :expand (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum-or-quotep))))

;; This is about the args of a dag node.
(defthm all-dargp-less-than-of-alen1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp n)
                (consp (aref1 dag-array-name dag-array n))
                (not (eq 'quote
                         (ffn-symb (aref1 dag-array-name dag-array n))))
                (<= n (alen1 dag-array-name dag-array)) ;drop?
                (natp (alen1 dag-array-name dag-array)) ;drop?
                )
           (all-dargp-less-than (dargs (aref1 dag-array-name dag-array n))
                                           (alen1 dag-array-name dag-array)))
  :hints (("Goal" :use (:instance ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1
                                  (bound (alen1 dag-array-name dag-array))
                                  (m n))
           :in-theory (disable ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1))))

(defthm pseudo-dag-arrayp-aux-of-car
  (implies (and (pseudo-dag-arrayp-list worklist dag-array-name dag-array)
                (consp worklist)
                (not (consp (car worklist))) ;excludes a quotep
                )
           (pseudo-dag-arrayp-aux dag-array-name dag-array (car worklist)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp pseudo-dag-arrayp-list))))

;; (defthm not-consp-of-car-when-ALL-NATP
;;   (implies (ALL-NATP x)
;;            (not (consp (car x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm all-dargp-of-alen1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                (natp n)
                (consp (aref1 dag-array-name dag-array n)) ;not a var
                (not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n)))) ;not a constant
                ;(<= n (alen1 dag-array-name dag-array)) ;drop?
                ;(natp (alen1 dag-array-name dag-array)) ;drop?
                )
           (all-dargp-less-than (dargs (aref1 dag-array-name dag-array n))
                                           (alen1 dag-array-name dag-array)))
  :hints (("Goal" :use (:instance all-dargp-less-than-of-dargs-of-aref1
                                  (bound (alen1 dag-array-name dag-array))
                                  (m n))
           :in-theory (disable all-dargp-less-than-of-dargs-of-aref1))))

(defthm all-natp-of-keep-atoms-when-all-dargp-less-than
  (implies (all-dargp-less-than items nodenum)
           (all-natp (keep-atoms items)))
  :hints (("Goal" :in-theory (enable keep-atoms
                                     dargs-when-not-consp-cheap))))

(defthm all-natp-of-keep-atoms-of-dargs-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp nodenum expr) ;nodenum is a free var - introduce a weak-dag-exprp?
                (not (eq 'quote (car expr))))
           (all-natp (keep-atoms (dargs expr))))
  :hints (("Goal" :in-theory (enable dargs-when-not-consp-cheap
                                     bounded-dag-exprp))))

(defthm all-natp-of-keep-atoms-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum)
                (natp nodenum)
                (integerp top-nodenum)
                (<= nodenum top-nodenum)
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (all-natp (keep-atoms (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :use (:instance all-natp-of-keep-atoms-of-dargs-when-bounded-dag-exprp (expr (aref1 dag-array-name dag-array nodenum)))
           :in-theory (disable all-natp-of-keep-atoms-of-dargs-when-bounded-dag-exprp))))

;; (defthm true-listp-of-dargs-of-aref1-when-PSEUDO-DAG-ARRAYP-AUX
;;   (implies (and (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY top-nodenum)
;;                 (integerp top-nodenum)
;;                 (natp nodenum)
;;                 (<= nodenum top-nodenum)
;;                 (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
;;            (true-listp (dargs (aref1 dag-array-name dag-array nodenum))))
;;   :hints (("Goal" :use (:instance BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
;;                                   (m nodenum)
;;                                   (n top-nodenum))
;;            :in-theory (disable BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))))

(defthmd all-integerp-when-all-natp
  (implies (all-natp x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-natp all-integerp))))

(defthm all-integerp-of-keep-atoms-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum)
                (natp nodenum)
                (integerp top-nodenum)
                (<= nodenum top-nodenum)
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (all-integerp (keep-atoms (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (enable all-integerp-when-all-natp))))

(defthm all-integerp-of-keep-atoms-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (integerp dag-len)
                (< nodenum dag-len)
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (all-integerp (keep-atoms (dargs (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm all-<-of-keep-atoms
  (implies (all-dargp-less-than items nodenum)
           (all-< (keep-atoms items) nodenum))
  :hints (("Goal" :in-theory (enable ALL-DARGP-LESS-THAN keep-atoms))))

(defthm all-<-of-keep-atoms-of-dargs-when-bounded-dag-exprp
  (implies (and (bounded-dag-exprp nodenum expr) ;nodenum is a free var - introduce a weak-dag-exprp?
                (consp expr)
                (not (eq 'quote (car expr))))
           (all-< (keep-atoms (dargs expr))
                  nodenum)))

(defthm all-<-of-keep-atoms-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum)
                (natp nodenum)
                (integerp top-nodenum)
                (<= nodenum top-nodenum)
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (all-< (keep-atoms (dargs (aref1 dag-array-name dag-array nodenum)))
                  nodenum))
  :hints (("Goal" :use (:instance all-<-of-keep-atoms-of-dargs-when-bounded-dag-exprp (expr (aref1 dag-array-name dag-array nodenum)))
           :in-theory (disable all-<-of-keep-atoms-of-dargs-when-bounded-dag-exprp))))

(defthm all-<-of-keep-atoms-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp nodenum)
                (integerp top-nodenum)
                (<= nodenum top-nodenum)
                (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (all-< (keep-atoms (dargs (aref1 dag-array-name dag-array nodenum)))
                  nodenum))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm all-natp-of-keep-atoms
  (implies (all-dargp x)
           (all-natp (keep-atoms x)))
  :hints (("Goal" :in-theory (enable keep-atoms))))

(defthm all-natp-of-keep-atoms-of-dargs-when-dag-exprp0
  (implies (and (dag-exprp0 expr)
                (not (eq 'quote (car expr))))
           (all-natp (keep-atoms (dargs expr)))))

;; (defthm <-of-lemma-for-arg4-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (cadr (cdddr (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (not (consp (cadr (cdddr (dargs (aref1 dag-array-name dag-array nodenum)))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cdddr (dargs (aref1 dag-array-name dag-array nodenum)))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                   LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg3-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (cadr (cddr (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (not (consp (cadr (cddr (dargs (aref1 dag-array-name dag-array nodenum))))))
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cddr (dargs (aref1 dag-array-name dag-array nodenum)))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg2-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (cadr (cdr (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (not (consp (cadr (cdr (dargs (aref1 dag-array-name dag-array nodenum))))))
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cdr (dargs (aref1 dag-array-name dag-array nodenum)))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (cadr (dargs (aref1 dag-array-name dag-array nodenum)))
;;                 (not (consp (cadr (dargs (aref1 dag-array-name dag-array nodenum)))))
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (dargs (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg0-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (car (dargs (aref1 dag-array-name dag-array nodenum)))
;;                 (not (consp (car (dargs (aref1 dag-array-name dag-array nodenum)))))
;;                 (natp nodenum)
;;                 (not (eq 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;note this
;;                 )
;;            (< (car (dargs (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg4-when-pseudo-dag-arrayp-aux-alt
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (<= 5 (len (dargs (aref1 dag-array-name dag-array nodenum))))
;; ;                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (cadr (cddddr (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cddddr (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg3-when-pseudo-dag-arrayp-aux-alt
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (<= 4 (len (dargs (aref1 dag-array-name dag-array nodenum))))
;; ;                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodeum))))
;;                 (not (consp (cadr (cdddr (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cdddr (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg2-when-pseudo-dag-arrayp-aux-alt
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (<= 3 (len (dargs (aref1 dag-array-name dag-array nodenum))))
;; ;                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (cadr (cddr (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (cddr (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg1-when-pseudo-dag-arrayp-aux-alt
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (<= 2 (len (dargs (aref1 dag-array-name dag-array nodenum))))
;; ;                (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (cadr (dargs (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (dargs (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg1-when-pseudo-dag-arrayp-aux-alt-nth-version
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp n)
;;                 (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (nth n (dargs (aref1 dag-array-name dag-array nodenum))) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))

;; (defthm <-of-lemma-for-arg0-when-pseudo-dag-arrayp-aux-alt
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                 (<= 1 (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (not (EQUAL 'QUOTE (NTH 0 (AREF1 DAG-ARRAY-NAME DAG-ARRAY nodenum))))
;;                 (not (consp (cadr (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 (natp nodenum)
;;                 )
;;            (< (cadr (aref1 dag-array-name dag-array nodenum)) nodenum))
;;   :rule-classes (:rewrite :linear)
;;   :otf-flg t
;;   :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array nodenum))
;;            :in-theory (e/d (pseudo-dag-arrayp-aux car-becomes-nth-of-0
;;                                                 LIST::LEN-OF-CDR-BETTER)
;;                            (len)))))


;; (thm
;;  (IMPLIES (AND (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY N)
;;                (INTEGERP N)
;;                (<= 0 N)
;;                (CONSP (AREF1 DAG-ARRAY-NAME DAG-ARRAY N)))
;;          (SYMBOLP (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY N)))))

(defthm pseudo-dag-arrayp-aux-of-compress1
  (implies (and (force (array1p array-name array))
                (< top-nodenum-to-check (alen1 array-name array)))
           (equal (pseudo-dag-arrayp-aux array-name (compress1 array-name array) top-nodenum-to-check)
                  (pseudo-dag-arrayp-aux array-name array top-nodenum-to-check)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dag-arrayp-aux ;compress1
                              ))))

(defthm pseudo-dag-arrayp-aux-of-cons-of-cons-of-header
  (implies (and (pseudo-dag-arrayp-aux array-name dag-lst n)
                (pseudo-dagp dag-lst)
                (<= n (car (car dag-lst)))
                )
           (pseudo-dag-arrayp-aux array-name (cons (cons :header x) dag-lst) n))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dag-arrayp-aux aref1-when-not-assoc-equal
                              assoc-equal-when-PSEUDO-DAGP))))

(defthm all-<-of-0-when-nat-listp
  (implies (nat-listp nats)
           (equal (ALL-< nats 0)
                  (atom nats))))

(defthm all-<-of-0-when-all-natp
  (implies (all-natp nats)
           (equal (all-< nats 0)
                  (atom nats)))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthm not-<-of-alen1-when-pseudo-dag-arrayp
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (not (< (alen1 dag-array-name dag-array) dag-len))))

(defthmd <-when-member-equal-of-dargs-of-aref1
  (implies (and (member-equal darg (dargs (aref1 dag-array-name dag-array nodenum)))
                (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp nodenum)
                (not (consp darg)) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (< darg nodenum))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper (n nodenum))
           ;; :cases ((consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
           ;; :expand ((PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY 0))
           :in-theory (e/d (<-of-nth-when-all-dargp-less-than
                            MEMBER-EQUAL-BECOMES-MEMBERP
                            dargs-when-not-consp-cheap
                            bounded-dag-exprp)
                           (bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-helper
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-gen
                            DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            ALL-DARGP-LESS-THAN-OF-DARGS-OF-AREF1
                            ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            ALL-DARGP-OF-DARGS-WHEN-DAG-EXPRP0)))))

;may loop with the defn
(defthmd pseudo-dag-arrayp-aux-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                (natp nodenum-or-quotep))
           (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum-or-quotep))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-aux-of-aset1
  (implies (and (pseudo-dag-arrayp-aux array-name array top-nodenum-to-check)
                (< index (alen1 array-name array))
                (< top-nodenum-to-check (alen1 array-name array))
                (array1p array-name array)
                (natp index)
                (integerp top-nodenum-to-check)
                (<= index 2147483645)
                (bounded-dag-exprp index val))
           (pseudo-dag-arrayp-aux array-name (aset1 array-name array index val) top-nodenum-to-check))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

(defthm pseudo-dag-arrayp-aux-of-aset1-expandable
  (implies (and (<= top-nodenum-to-check index) ;drop?
                (pseudo-dag-arrayp-aux array-name array top-nodenum-to-check)
                (array1p array-name array)
                (integerp index)
                (integerp top-nodenum-to-check)
                (<= index 2147483645)
                (bounded-dag-exprp index val))
           (pseudo-dag-arrayp-aux array-name (aset1-expandable array-name array index val) top-nodenum-to-check))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

(defthm pseudo-dag-arrayp-of-aset1-expandable
  (implies (and (<= (+ -1 n) index) ;drop?
                (pseudo-dag-arrayp array-name array n)
                (array1p array-name array)
                (natp index)
                (integerp top-nodenum-to-check)
                (<= index 2147483645)
                (bounded-dag-exprp index val))
           (pseudo-dag-arrayp array-name (aset1-expandable array-name array index val) n))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-aux-of-aset1-expandable-special
  (implies (and (equal index2 index) ;this case
                (pseudo-dag-arrayp-aux array-name array (+ -1 index)) ;the item at position index is being overwritten
                (array1p array-name array)
                (integerp index)
                (<= INDEX 2147483645)
                (bounded-dag-exprp index val))
           (pseudo-dag-arrayp-aux array-name (aset1-expandable array-name array index2 val) index))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-aux))))

(defthm pseudo-dag-arrayp-of-aset1-expandable-special
  (implies (and (equal index2 (+ -1 index)) ;this case
                (pseudo-dag-arrayp array-name array (+ -1 index)) ;the item at position index is being overwritten
                (array1p array-name array)
                (integerp index)
                (<= index 2147483646)
                (bounded-dag-exprp (+ -1 index) val))
           (pseudo-dag-arrayp array-name (aset1-expandable array-name array index2 val) index))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm integerp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (integerp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (DAG-EXPRP0 INTEGERP-OF-NTH-WHEN-ALL-DARGP)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp)))))

(defthm integerp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (natp nodenum)
                (natp n) ;drop?
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (integerp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))))

(defthm acl2-numberp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (acl2-numberp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (dag-exprp0 integerp-of-nth-when-all-dargp)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            dag-exprp0-of-aref1-when-pseudo-dag-arrayp-aux
                            dag-exprp0-of-aref1-when-bounded-dag-exprp-of-aref1
                            all-dargp-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux)))))

(defthm natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (equal (natp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                  (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (DAG-EXPRP0 INTEGERP-OF-NTH-WHEN-ALL-DARGP)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp)))))

(defthm not-<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (<= bound 0)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (not (< (nth n (dargs (aref1 dag-array-name dag-array nodenum))) bound)))
  :hints (("Goal" :use (:instance natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp)
           :in-theory (e/d (pseudo-dag-arrayp) (natp-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp)))))

(defthm <=-of-0-and-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                ;; (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                ;; (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                )
           (<= 0 (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :rule-classes (:rewrite :linear :forward-chaining)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm <=-of-0-and-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                ;; (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                (natp nodenum)
                (natp n) ;drop?
                ;; (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                )
           (<= 0 (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
  :rule-classes (:rewrite :linear :forward-chaining)
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm equal-of-quote-and-car-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
 ;               (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
;                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                )
           (equal (equal 'quote (car (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                  (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (DAG-EXPRP0 INTEGERP-OF-NTH-WHEN-ALL-DARGP)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp)))))

(defthm cdr-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-iff
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
                ;; (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                ;; (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                )
           (iff (cdr (nth n (dargs (aref1 dag-array-name dag-array nodenum))))
                (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))

(defthmd not-equal-of-1-and-len-of-nth-when-all-dargp
  (implies (all-dargp items)
           (not (equal 1 (len (nth n items)))))
  :hints (("Goal" :in-theory (enable all-dargp (:i nth)))))

(defthm all-dargp-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (all-dargp (dargs (aref1 dag-array-name dag-array nodenum))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (DAG-EXPRP0 INTEGERP-OF-NTH-WHEN-ALL-DARGP)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp)))))

(defthm all-dargp-of-dargs-of-aref1-when-pseudo-dag-arrayp-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (natp nodenum)
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (all-dargp (dargs (aref1 dag-array-name dag-array nodenum)))))

(defthm not-equal-1-of-len-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-iff
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (natp n) ;drop?
     ;               (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
     ;                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))
                )
           (not (equal 1 (len (nth n (dargs (aref1 dag-array-name dag-array nodenum)))))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (DAG-EXPRP0 INTEGERP-OF-NTH-WHEN-ALL-DARGP not-equal-of-1-and-len-of-nth-when-all-dargp)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP)))))

(defthm symbolp-of-car-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (natp nodenum))
           (symbolp (car (aref1 dag-array-name dag-array nodenum))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (dag-exprp0 integerp-of-nth-when-all-dargp)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp)))))

(defthm symbolp-of-nth-0-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (natp nodenum))
           (symbolp (nth 0 (aref1 dag-array-name dag-array nodenum))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance symbolp-of-car-of-aref1-when-pseudo-dag-arrayp)
           :in-theory (e/d (nth) (symbolp-of-car-of-aref1-when-pseudo-dag-arrayp nth-of-cdr)))))

(defthm myquotep-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (natp nodenum))
           (equal (myquotep (aref1 dag-array-name dag-array nodenum))
                  (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp (n nodenum))
           :in-theory (e/d (dag-exprp0 integerp-of-nth-when-all-dargp myquotep)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp)))))

(defthm pseudo-dag-arrayp-of-make-empty-array
  (implies (and (symbolp dag-array-name)
                (posp size)
                (<= size 2147483646))
           (pseudo-dag-arrayp dag-array-name
                              (make-empty-array dag-array-name size)
                              0))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm not-<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (natp bound)
                (<= nodenum bound)
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                (natp n)
                (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (not (< bound
                   (nth n (dargs (aref1 dag-array-name dag-array nodenum))))))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm aref1-of-cdr-irrel
  (implies (and (< index (CAR (CAR DAG-LST)))
                (natp index))
           (equal (AREF1 ARRAY-NAME (CDR DAG-LST) index)
                  (AREF1 ARRAY-NAME DAG-LST index)))
  :hints (("Goal" :in-theory (enable aref1))))

(defthm PSEUDO-DAG-ARRAYP-AUX-of-cdr-irrel
  (implies (and (< top-nodenum (car (car dag-lst)))
                (integerp top-nodenum)
                )
           (equal (PSEUDO-DAG-ARRAYP-AUX ARRAY-NAME (CDR DAG-LST) top-nodenum)
                  (PSEUDO-DAG-ARRAYP-AUX ARRAY-NAME DAG-LST top-nodenum)))
  :hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-AUX))))

(defthm aref1-of-car-of-car-2
  (implies (natp (CAR (CAR DAG-LST)))
           (equal (AREF1 ARRAY-NAME DAG-LST (CAR (CAR DAG-LST)))
                  (cdr (car dag-lst))))
  :hints (("Goal" :in-theory (enable AREF1))))

(defthm pseudo-dag-arrayp-aux-lemma
  (implies (and (natp (car (car dag-lst)))
                (consp dag-lst)
                (consp (car dag-lst))
                (bounded-dag-exprp (car (car dag-lst)) (cdr (car dag-lst)))
                (pseudo-dag-arrayp-aux array-name (cdr dag-lst) (+ -1 (car (car dag-lst))))
                )
           (pseudo-dag-arrayp-aux array-name dag-lst (car (car dag-lst))))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux array-name dag-lst (car (car dag-lst)))))))

(defthm pseudo-dag-arrayp-aux-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (natp top-nodenum))
           (pseudo-dag-arrayp-aux array-name dag-lst top-nodenum))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((PSEUDO-DAG-ARRAYP-AUX ARRAY-NAME DAG-LST (+ -1 (CAR (CAR DAG-LST))))
                    (PSEUDO-DAGP-AUX DAG-LST TOP-NODENUM)
                    (AREF1 ARRAY-NAME DAG-LST 0)
                    (ASSOC-EQUAL 0 DAG-LST))
           :induct (pseudo-dagp-aux dag-lst top-nodenum)
           :in-theory (enable pseudo-dagp-aux
                              pseudo-dag-arrayp-aux
                              ))))

(defthm pseudo-dag-arrayp-aux-of-make-into-array
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
                (< top-nodenum 2147483646)
                (natp top-nodenum)
                (symbolp array-name))
           (pseudo-dag-arrayp-aux array-name
                                (make-into-array array-name dag-lst)
                                (car (car dag-lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :expand ((:free (a) (array1p array-name (cons a dag-lst))))
           :in-theory (enable PSEUDO-DAGP
                              pseudo-dag-arrayp-aux
                              make-into-array
                              make-into-array-with-len
                              array1p))))

(defthm pseudo-dag-arrayp-aux-of-make-into-array-with-len
  (implies (and (pseudo-dagp-aux dag-lst top-nodenum)
;                (< top-nodenum 2147483646)
                (natp top-nodenum)
                (< top-nodenum len)
                (natp len)
                (< len 2147483647)
                (symbolp array-name))
           (pseudo-dag-arrayp-aux array-name (make-into-array-with-len array-name dag-lst len) top-nodenum))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable pseudo-dagp
                              make-into-array-with-len
                              pseudo-dag-arrayp-aux
                              array1p-rewrite))))

(defthm bounded-integer-alistp-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag-lst current-nodenum)
                (< current-nodenum len)
                (integerp current-nodenum)
                (integerp len))
           (bounded-integer-alistp dag-lst len))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp pseudo-dagp-aux))))

(defthm pseudo-dag-arrayp-of-make-into-array-with-len
  (implies (and (pseudo-dagp dag-lst)
                (< len 2147483647)
                (integerp len)
                (<= (len dag-lst) len)
                (symbolp array-name))
           (pseudo-dag-arrayp array-name (make-into-array-with-len array-name dag-lst len) (len dag-lst)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp PSEUDO-DAGP))))

(defthm pseudo-dag-arrayp-of-make-into-array-with-len-gen
  (implies (and (pseudo-dagp dag-lst)
                (<= dag-len (len dag-lst))
                (natp dag-len)
                (< len 2147483647)
                (integerp len)
                (<= (len dag-lst) len)
                (symbolp array-name))
           (pseudo-dag-arrayp array-name (make-into-array-with-len array-name dag-lst len) dag-len))
  :hints (("Goal" :use (:instance pseudo-dag-arrayp-of-make-into-array-with-len)
           :in-theory (disable pseudo-dag-arrayp-of-make-into-array-with-len))))

;drop?
(defthm pseudo-dag-arrayp-of-make-into-array
  (implies (and (pseudo-dagp dag-lst)
                (< (len dag-lst) 2147483647)
                (symbolp array-name))
           (pseudo-dag-arrayp array-name (make-into-array array-name dag-lst) (len dag-lst)))
  :hints (("Goal" :in-theory (e/d (pseudo-dag-arrayp pseudo-dagp)
                                  (consp-from-len-cheap ;else we lose the consp fact
                                   )))))

;drop?
(defthm pseudo-dag-arrayp-of-make-into-array-gen
  (implies (and (pseudo-dagp dag-lst)
                (<= dag-len (len dag-lst))
                (natp dag-len)
                (< (len dag-lst) 2147483647)
                (symbolp array-name))
           (pseudo-dag-arrayp array-name (make-into-array array-name dag-lst) dag-len))
  :hints (("Goal" :use (:instance pseudo-dag-arrayp-of-make-into-array)
           :in-theory (disable pseudo-dag-arrayp-of-make-into-array))))

;; normalize to consp
(defthm symbolp-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (natp nodenum))
           (equal (symbolp (aref1 dag-array-name dag-array nodenum))
                  (not (consp (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :use (:instance symbolp-of-aref1-when-pseudo-dag-arrayp-aux-and-not-consp)
           :in-theory (e/d (pseudo-dag-arrayp) (symbolp-of-aref1-when-pseudo-dag-arrayp-aux-and-not-consp)))))

;; normalize to consp
(defthm symbolp-of-aref1-when-pseudo-dag-arrayp-2
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                ;; (< nodenum dag-len)
                (natp nodenum))
           (equal (symbolp (aref1 dag-array-name dag-array nodenum))
                  (not (consp (aref1 dag-array-name dag-array nodenum)))))
  :hints (("Goal" :use (:instance symbolp-of-aref1-when-pseudo-dag-arrayp-aux-and-not-consp)
           :in-theory (e/d (pseudo-dag-arrayp) (symbolp-of-aref1-when-pseudo-dag-arrayp-aux-and-not-consp)))))

(defthm not-cdr-of-cdr-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (equal 'quote (car (aref1 dag-array-name dag-array n)))
                (< n dag-len)
                (natp n))
           (not (cdr (cdr (aref1 dag-array-name dag-array n)))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp)
           :in-theory (e/d (pseudo-dag-arrayp dag-exprp0)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            dag-exprp0-of-aref1-when-pseudo-dag-arrayp-aux
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                            dag-exprp0-of-aref1-when-bounded-dag-exprp-of-aref1
                            dag-exprp0-when-equal-of-quote-and-car-cheap
                            cdr-iff)))))

(defthm consp-of-cdr-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (equal 'quote (car (aref1 dag-array-name dag-array n)))
                (< n dag-len)
                (natp n))
           (consp (cdr (aref1 dag-array-name dag-array n))))
  :hints (("Goal" :use (:instance dag-exprp0-of-aref1-when-pseudo-dag-arrayp)
           :in-theory (e/d (pseudo-dag-arrayp)
                           (dag-exprp0-of-aref1-when-pseudo-dag-arrayp
                            dag-exprp0-of-aref1-when-pseudo-dag-arrayp-aux
                            bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                            dag-exprp0-of-aref1-when-bounded-dag-exprp-of-aref1
                            )))))

;; (thm
;;  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                (consp (aref1 dag-array-name dag-array n))
;;                (not (equal 'quote (car (aref1 dag-array-name dag-array n))))
;;                (< n dag-len)
;;                (natp n))
;;           (NOT (< (+ -1 N) (LARGEST-NON-QUOTEP (DARGS$INLINE (AREF1 DAG-ARRAY-NAME DAG-ARRAY N)))))))

;todo: kill the other
(defthm bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-better
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array free)
                (< n free)
                (natp n)
                (integerp free))
           (bounded-dag-exprp n (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

(defthm pseudo-dag-arrayp-list-when-all-dargp-less-than-special-alt
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-dargp-less-than lst dag-len)
                (natp nodenum))
           (pseudo-dag-arrayp-list lst dag-array-name dag-array))
  :hints
  (("Goal"
    :do-not '(generalize eliminate-destructors)
    :in-theory (enable all-dargp-less-than
                       pseudo-dag-arrayp-list))))

(defthm not-<-of-nth-of-dargs-of-aref1-and-constant-when-pseudo-dag-arrayp
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (pseudo-dag-arrayp-aux dag-array-name dag-array (+ 1 nodenum))
                ;; (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp nodenum)
                ;; (natp n)
                ;; (not (consp (nth n (dargs (aref1 dag-array-name dag-array nodenum))))) ;excludes the arg from being a quotep
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))) ;excludes the whole node from being a quotep
                )
           (not (< (nth n (dargs (aref1 dag-array-name dag-array nodenum)))
                   k)))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable pseudo-dag-arrayp))))



;; (defthm dargp-less-than-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array bound)
;;                 (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
;;                 (natp n)
;;                 (not (equal 'quote (nth 0 (aref1 dag-array-name dag-array nodenum))))
;;                 (natp nodenum))
;;            (dargp-less-than (nth n (dargs (aref1 dag-array-name dag-array nodenum))) bound))
;;   :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) (dag-exprp0)))))

(defthm dargp-less-than-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (< n (len (dargs (aref1 dag-array-name dag-array nodenum))))
                (natp n)
                (not (equal 'quote (nth 0 (aref1 dag-array-name dag-array nodenum))))
                (not (EQUAL 'QUOTE (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))))
                (natp nodenum)
                (<= nodenum bound)
                (natp bound))
           (dargp-less-than (nth n (dargs (aref1 dag-array-name dag-array nodenum))) bound))
  :hints (("Goal" :use (:instance all-dargp-less-than-of-dargs-of-aref1
                                  (n nodenum)
                                  (m nodenum))
           :in-theory (e/d (PSEUDO-DAG-ARRAYP)
                           (dargp-less-than
                            all-dargp-less-than-of-dargs-of-aref1)))))

(defthm type-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum-to-check)
                (natp n)
                (integerp top-nodenum-to-check)
                (<= n top-nodenum-to-check))
           (or (symbolp (aref1 dag-array-name dag-array n))
               (consp (aref1 dag-array-name dag-array n))))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                                  (n top-nodenum-to-check)
                                  (m n))
           :in-theory (e/d (BOUNDED-DAG-EXPRP DAG-EXPRP0 DAG-FUNCTION-CALL-EXPRP)
                           (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-gen
                            DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            LEN-OF-AREF1-WHEN-QUOTEP-AND-PSEUDO-DAG-ARRAYP-AUX
                            DAG-FUNCTION-CALL-EXPRP-REDEF
                            TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            SYMBOLP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-AND-NOT-CONSP)))))

;; True whether or not it is a quotep
(defthm true-listp-of-aref1-when-pseudo-dag-arrayp-aux
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum-to-check)
                (natp n)
                (integerp top-nodenum-to-check)
                (not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
                ;;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                (<= n top-nodenum-to-check))
           (true-listp (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                                  (n top-nodenum-to-check)
                                  (m n))
           :in-theory (e/d (BOUNDED-DAG-EXPRP DAG-EXPRP0 DAG-FUNCTION-CALL-EXPRP)
                           (BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-gen
                            DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            LEN-OF-AREF1-WHEN-QUOTEP-AND-PSEUDO-DAG-ARRAYP-AUX
                            DAG-FUNCTION-CALL-EXPRP-REDEF
                            TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
                            SYMBOLP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-AND-NOT-CONSP)))))

(defthm true-listp-of-aref1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp n)
                (not (symbolp (aref1 dag-array-name dag-array n))) ;can't be a var
                ;;(not (eq 'quote (ffn-symb (aref1 dag-array-name dag-array n))))
                (< n dag-len))
           (true-listp (aref1 dag-array-name dag-array n)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

;move up
(defthm pseudo-dag-arrayp-of-aset1
  (implies (and (pseudo-dag-arrayp array-name array dag-len)
                (< index dag-len)
                (natp index)
                (bounded-dag-exprp index val))
           (pseudo-dag-arrayp array-name (aset1 array-name array index val) dag-len))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp))))

;;;
;;; make-dag-into-array
;;;

;; Convert DAG into an array named DAG-ARRAY-NAME, leaving SLACK-AMOUNT of
;; unused nodes if possible.
;; TODO: Use this more instead of make-into-array? But see make-dag-into-array2 !
(defund make-dag-into-array (dag-array-name dag slack-amount)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (symbolp dag-array-name)
                              (< (top-nodenum-of-dag dag)
                                 *maximum-1-d-array-length*)
                              (natp slack-amount)
                              (<= slack-amount 2147483646))
                  :guard-hints (("Goal" :use (:instance bounded-natp-alistp-when-pseudo-dagp (dag-lst dag))
                                 :in-theory (e/d (car-of-car-when-pseudo-dagp-cheap
                                                  array-len-with-slack
                                                  top-nodenum-of-dag-becomes-top-nodenum)
                                                 (bounded-natp-alistp-when-pseudo-dagp))))
                  :split-types t)
           (type (integer 0 2147483646) slack-amount)
           (type symbol dag-array-name))
  (let* ((dag-len (+ 1 (top-nodenum dag))) ;no need to search for the max key, since we know it's the top node
         (length-with-slack (array-len-with-slack dag-len slack-amount)))
    (make-into-array-with-len dag-array-name dag length-with-slack)))

(defthm alen1-of-make-dag-into-array
  (implies (pseudo-dagp dag)
           (equal (alen1 dag-array-name (make-dag-into-array dag-array-name dag slack-amount))
                  (array-len-with-slack (len dag) slack-amount)))
  :hints (("Goal" :in-theory (enable make-dag-into-array
                                     car-of-car-when-pseudo-dagp-cheap))))

(defthm pseudo-dag-arrayp-of-make-dag-into-array
  (implies (and (pseudo-dagp dag)
                (< (len dag) 2147483647) ;or express using top-nodenum?
                (<= dag-len (len dag))
                (natp dag-len)
                (symbolp dag-array-name)
                (natp slack-amount))
           (pseudo-dag-arrayp dag-array-name (make-dag-into-array dag-array-name dag slack-amount) dag-len))
  :hints (("Goal" :in-theory (e/d (make-dag-into-array car-of-car-when-pseudo-dagp-cheap ARRAY-LEN-WITH-SLACK)
                                  (pseudo-dag-arrayp-of-make-into-array-with-len-gen))
           :use (:instance pseudo-dag-arrayp-of-make-into-array-with-len-gen
                           (dag-len dag-len)
                           (len (min *maximum-1-d-array-length*
                                     (+ (len dag) slack-amount)))
                           (dag-lst dag)
                           (array-name dag-array-name)))))

;;;
;;; make-dag-into-array2
;;;

;; Convert DAG into an array named DAG-ARRAY-NAME, leaving SLACK-AMOUNT of
;; unused nodes if possible.
;; TODO: Use this more instead of make-into-array and make-dag-into-array.
;; Similar to make-dag-into-array
;; Returns (mv erp dag-array).
(defund make-dag-into-array2 (dag-array-name dag slack-amount)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (symbolp dag-array-name)
                              (natp slack-amount))
                  :guard-hints (("Goal" :use (:instance bounded-natp-alistp-when-pseudo-dagp)
                                 :in-theory (e/d (car-of-car-when-pseudo-dagp-cheap
                                                  array-len-with-slack
                                                  top-nodenum-of-dag-becomes-top-nodenum)
                                                 (bounded-natp-alistp-when-pseudo-dagp))))
                  :split-types t)
           (type symbol dag-array-name))
  (let ((dag-len (+ 1 (top-nodenum-of-dag dag)))) ;no need to search for the max key, since we know it's a dag
    (if (< *maximum-1-d-array-length* dag-len)
        (mv :dag-too-big nil)
      (let* ((length-with-slack (array-len-with-slack dag-len slack-amount)))
        (mv (erp-nil)
            (make-into-array-with-len dag-array-name dag length-with-slack))))))

(defthm alen1-of-mv-nth-1-of-make-dag-into-array2
  (implies (and (pseudo-dagp dag)
                (not (mv-nth 0 (make-dag-into-array2 dag-array-name dag slack-amount))))
           (equal (alen1 dag-array-name (mv-nth 1 (make-dag-into-array2 dag-array-name dag slack-amount)))
                  (array-len-with-slack (len dag) slack-amount)))
  :hints (("Goal" :in-theory (enable top-nodenum-of-dag-when-pseudo-dagp
                                     ;;array-len-with-slack
                                     make-dag-into-array2
                                     car-of-car-when-pseudo-dagp-cheap))))

(defthm pseudo-dag-arrayp-of-make-dag-into-array2
  (implies (and (pseudo-dagp dag)
                (symbolp dag-array-name)
                (natp slack-amount)
                (not (mv-nth 0 (make-dag-into-array2 dag-array-name dag slack-amount))))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 1 (make-dag-into-array2 dag-array-name dag slack-amount))
                              (len dag)))
  :hints (("Goal" :in-theory (enable make-dag-into-array2 array-len-with-slack top-nodenum-of-dag-when-pseudo-dagp))))

(defthm pseudo-dag-arrayp-of-make-dag-into-array2-gen
  (implies (and (<= n (len dag))
                (natp n)
                (pseudo-dagp dag)
                (symbolp dag-array-name)
                (natp slack-amount)
                (not (mv-nth 0 (make-dag-into-array2 dag-array-name dag slack-amount))))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 1 (make-dag-into-array2 dag-array-name dag slack-amount))
                              n))
  :hints (("Goal" :use (:instance pseudo-dag-arrayp-of-make-dag-into-array2)
           :in-theory (disable pseudo-dag-arrayp-of-make-dag-into-array2))))

;move or drop
(defthm all-<-of-alen1-when-pseudo-dag-arrayp-list
  (implies (and (pseudo-dag-arrayp-list nodenums
                                      dag-array-name dag-array)
                (nat-listp nodenums))
           (all-< nodenums
                  (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable all-< pseudo-dag-arrayp-list))))

(defthm <-of-maxelem-and-alen1-when-pseudo-dag-arrayp-list
  (implies (and (pseudo-dag-arrayp-list nodenums
                                      dag-array-name dag-array)
                (nat-listp nodenums)
                (consp nodenums))
           (< (maxelem nodenums)
              (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list))))

(defthmd all-dargp-less-than-of-alen1-when-pseudo-dag-arrayp
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (largest-non-quotep items)))
                (all-dargp items))
           (all-dargp-less-than items (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthmd all-dargp-less-than-of-alen1-when-pseudo-dag-arrayp-forward
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (largest-non-quotep items)))
                (all-dargp items))
           (all-dargp-less-than items (alen1 dag-array-name dag-array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

(defthm <-of-car-and-alen1
  (implies (and (pseudo-dag-arrayp-list worklist dag-array-name dag-array)
                (all-natp worklist)
                (consp worklist))
           (< (car worklist) (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-LIST))))

(defthm <-helper
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (consp (aref1 dag-array-name dag-array nodenum))
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum))))
                (< nodenum (alen1 dag-array-name dag-array))
                (natp nodenum))
           (not (< (alen1 dag-array-name dag-array)
                   (+ 1 (largest-non-quotep (dargs (aref1 dag-array-name dag-array nodenum)))))))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux
                                  (dag-array-name dag-array-name)
                                  (m nodenum)
                                  (n nodenum))
           :in-theory (disable bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux))))

;not needed?
;; (defthm <-of-alen1-when-pseudo-dag-arrayp-aux
;;   (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array top-nodenum-to-check)
;;                 (<= x top-nodenum-to-check)
;;                 (natp x)
;;                 (natp top-nodenum-to-check)
;;                 )
;;            (< x (alen1 dag-array-name dag-array))))

(defthm <-of-car-and-alen1-when-pseudo-dag-arrayp-list
  (implies (and (pseudo-dag-arrayp-list worklist dag-array-name dag-array)
                (consp worklist)
                (natp (car worklist))
                )
           (< (car worklist)
              (alen1 dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list))))

(defthm all-dargp-less-than-of-alen1-of-maybe-expand-array
  (implies (and (all-dargp-less-than args (alen1 array-name array))
                (natp index)
                (array1p array-name array))
           (all-dargp-less-than args (alen1 array-name (maybe-expand-array array-name array index)))))

(defthm pseudo-dag-arrayp-list-of-append-atoms
  (implies (and (pseudo-dag-arrayp-list args dag-array-name dag-array)
                (pseudo-dag-arrayp-list acc dag-array-name dag-array))
           (pseudo-dag-arrayp-list (append-atoms args acc) dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list append-atoms all-<))))

(defthm pseudo-dagp-aux-of-array-to-alist-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp n)
                (<= n dag-len)
                (pseudo-dagp-aux acc (+ -1 n)))
           (pseudo-dagp-aux (array-to-alist-aux n dag-len dag-array-name dag-array acc) (+ -1 dag-len)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (array-to-alist-aux
                            pseudo-dagp-aux)
                           (bounded-dag-exprp
                            car-of-car-when-pseudo-dagp-aux)))))

(defthm pseudo-dagp-of-array-to-alist
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len) ;a pseudo-dag can't be empty
                )
           (pseudo-dagp (array-to-alist dag-array-name dag-array dag-len)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance pseudo-dagp-aux-of-array-to-alist-aux
                           (n 0)
                           (acc nil))
           :in-theory (e/d (array-to-alist pseudo-dagp)
                           (car-of-car-when-pseudo-dagp-aux
                            natp
                            pseudo-dagp-aux-of-array-to-alist-aux)))))
