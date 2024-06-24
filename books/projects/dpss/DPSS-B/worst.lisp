;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(defun list-fix (x)
  (if (not (consp x)) nil
    (cons (car x) (list-fix (cdr x)))))

(defthm list-fix-list-fix
  (equal (list-fix (list-fix x))
         (list-fix x)))

;; (include-book "std/lists/top" :dir :system)

;; Of course none of these work the way you want them to ..

;; (defthm open-true-list-fix
;;   (implies
;;    (consp x)
;;    (equal (list-fix x)
;;           (cons (car x) (list-fix (cdr x))))))

;; (defthm open-list-equiv
;;   (implies
;;    (or (consp x) (consp y))
;;    (iff (list-equiv x y)
;;         (and (consp x)
;;              (consp y)
;;              (equal (car x) (car y))
;;              (list-equiv (cdr x) (cdr y))))))

;; (defun count-diffs (x ens)
;;   (if (not (consp ens)) 0
;;     (let ((y (car ens)))
;;       (if (equiv x y) (count-diffs x (cdr ens))
;;         (1+ (count-diffs y (cdr ens)))))))

;; (defthm count-diffs-bound
;;   (<= (count-diffs x ens) (len ens)))

;; (defun fix-diff (n x ens)
;;   (if (not (consp ens)) nil
;;     (if (zp n) (cons x (cons x (cdr ens)))
;;       (cons x (fix-diff (1- n) (car ens) (cdr ens))))))

;; (encapsulate
;;     (
;;      )

;;   ;; If you

;;   )

;; (defun all-agree (ens)
;;   (forall (n m)
;;     (implies
;;      (and
;;       (< (nfix n) (len ens))
;;       (< (nfix m) (len ens)))
;;      (equiv (get n ens) (get m ens)))))

;; (defun all-unique-values (vals)
;;   (forall (n m)
;;     (implies
;;      (and
;;       (not (equal (nfix n) (nfix m)))
;;       (< (nfix n) (len ens))
;;       (< (nfix m) (len ens)))
;;      (not (equiv (get n ens) (get m ens))))))

;; ;; Every value in vals appears in ens
;; (defun subsetp (vals ens)
;;   (forall (n)
;;     (implies
;;      (< (nfix n) (len vals))
;;      (exits (m)
;;             (and (< (nfix m) (len ens))
;;                  (equiv (get n vals) (get m ens)))))))

;; (defun perm (vals ens)
;;   (and (subsetp vals ens)
;;        (subsetp enns vals)))

;; (defun differ (n ens)
;;   (declare (xargs :signature ((pos any) bool)))
;;   (not (equiv (get (1- n) ens) (get n ens))))

;; ;;
;; ;; every value in ens has some number of equivalent values.
;; ;; sets of adjacent equivalent values are of most interest.
;; ;;
;; ;; 0 < k < (len ens)
;; ;;
;; ;; 
;; ;; (fix n)
;; ;; 

;; (defun max-steps (ens)
;;   (/ (* (len ens) (1- (len ens))) 2))


;; (defun all-differences (n ens)
;;   (declare (xargs :signature ((pos any) plist)))
;;   (if (<= (len ens) (nfix n)) nil
;;     (if (not (equal (get (1- n) ens) (get n ens)))
;;         (cons (nfix n) (all-differences (1+  n) ens))
;;       (all-differences (1+  n) ens))))

;; (defun all-differences (ens)
;;   (all-differences 1 ens))

;; (defun differ (n ens)
;;   (let ((n (ifix n)))
;;     (and (< 0 n)
;;          (< n (len ens))
;;          (not (equiv (get (1- n) ens) (get n ens))))))

;; (defthm all-difference-membership
;;   (iff (member (ifix n) (all-differences ens))
;;        (differ n ens)))

;; (<= (len (all-differences (fix k ens)))
;;     (len (all-differences ens)))


;; (time-to-meet k ens)

;; ;;
;; ;; At an absolute minimum, it eliminates k as a difference.
;; ;; However, that does not guarantee that 'k' will never
;; ;; again have a difference.
;; ;;
;; (not (member (ifix k) (all-differences (fix k ens))))

;; - number of cliques.
;; - right cliques get smaller.

;; A B C D
;; A B C C
;; A B B C
;; A B B B
;; A A B B
;; A A A B
;; A A A A

;; ;;
;; ;; If you make a left number bigger,
;; ;;

;; (len ens)

;; (nat-list-measure )

;; (gather-equiv ens)

;; git submodule add -b demo https://vspells.ext.bbn.com/galois/polymorph/solution-template galois

;; git submodule add -b demo https://vspells.ext.bbn.com/bae-systems/ta-1-bae-solution-template bae

;; git submodule add -b demo https://vspells.ext.bbn.com/vanderbilt/solution-template vanderbilt

(defthm nfix-natp
  (implies
   (natp x)
   (equal (nfix x) x)))

(defthm natp-sum
  (implies
   (and (natp x) (natp y))
   (equal (nfix (+ x y))
          (+ x y))))

(defthm nfix-minus
  (implies
   (and (natp a) (natp b) (<= b a))
   (equal (nfix (+ a (- b)))
          (+ a (- b)))))

(in-theory (disable nfix))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defun pool-rec (n v ens)
  (declare (xargs :measure (len ens)))
  (let ((n (nfix n)))
    (if (not (consp ens)) (list n)
      (if (equal v (car ens))
          (append (pool-rec (1+ n) (car ens) (cdr ens)) (list 0))
        (cons n (pool-rec 1 (car ens) (cdr ens)))))))

(defthm pool-rec-list-fix
  (equal (pool-rec n v (list-fix ens))
         (pool-rec n v ens)))

(defthm true-listp-pool-rec
  (true-listp (pool-rec n v ens))
  :rule-classes (:type-prescription))
(in-theory (disable (:type-prescription pool-rec)))

(defthm len-pool-rec
  (equal (len (pool-rec n v ens))
         (+ 1 (len ens))))

(defun sub-list (x list)
  (if (not (consp list)) nil
    (cons (- (nfix x) (nfix (car list)))
          (sub-list x (cdr list)))))

(defthm len-sub-list
  (equal (len (sub-list x list))
         (len list)))

(defun gte-all (x list)
  ;;(declare (xargs :measure (len list)))
  (if (not (consp list)) t
    (and (<= (nfix (car list)) (nfix x))
         (gte-all x (cdr list)))))

(defun list-list-induction (x y)
  (if (and (consp x) (consp y))
      (list-list-induction (cdr x) (cdr y))
    (list x y)))

(include-book "std/basic/two-nats-measure" :dir :system)

(defthm alt-open-nat-list-<
  (implies
   (and (consp x) (consp y) (true-listp x) (true-listp y) (equal (len x) (len y)))
   (equal (nat-list-< x y)
          (if (equal (nfix (car x)) (nfix (car y)))
              (nat-list-< (cdr x) (cdr y))
            (< (nfix (car x)) (nfix (car y))))))
  :hints (("Goal" :do-not-induct t
           :use (:instance open-nat-list-<
                           (a x)
                           (b y)))))
  
(defthm sub-list-invsersion
  (implies
   (and
    (gte-all x a)
    (gte-all x b)
    (nat-list-< a b)
    (true-listp a)
    (true-listp b)
    (equal (len a) (len b)))
   (nat-list-< (sub-list x b)
               (sub-list x a)))
  :hints (("Goal" :induct (list-list-induction a b))))
  
(defun fix-rec (n v ens)
  (if (not (consp ens)) (list v)
    (if (zp n) (cons v (cons v (list-fix (cdr ens))))
      (cons v (fix-rec (1- n) (car ens) (cdr ens))))))

(defthm fix-rec-list-fix
  (equal (fix-rec n v (list-fix x))
         (fix-rec n v x)))

(defthm true-listp-fix-rec
  (true-listp (fix-rec n v ens))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription fix-rec)))

(defthm len-fix-rec
  (equal (len (fix-rec n v ens))
         (+ 1 (len ens))))
         
(defthm car-append-to-len
  (equal (car (append x y))
         (if (equal (len x) 0)
             (car y)
           (car x))))

(defthm cdr-append-to-len
  (equal (cdr (append x y))
         (if (equal (len x) 0) (cdr y)
           (append (cdr x) y))))

(defthm natp-car-pool-rec
  (natp (car (pool-rec m v ens))))

(defthmd equal-len-o-to-consp
  (iff (equal (len x) 0)
       (not (consp x))))

(defthm nat-list-<-equal
  (implies
   (true-listp a)
   (not (nat-list-< a a)))
  :hints (("Goal" :induct (len a))))

(defthm nat-list-append-common-suffix
  (implies
   (and (true-listp x) (true-listp y) (equal (len x) (len y)) (true-listp a))
   (iff (nat-list-< (append x a) (append y a))
        (nat-list-< x y)))
  :hints (("Goal" :in-theory (enable equal-len-o-to-consp)
           :induct (list-list-induction x y))))

(defthmd len-cdr
  (equal (len (cdr x))
         (if (consp x)
             (1- (len x))
           0)))

(defthm car-pool-rec
  (<= (nfix m) (car (pool-rec m v1 ens)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((car (pool-rec m v1 ens))))))

(defthm equal-m-pool-rec
  (implies
   (and
    (natp m0)
    (equal m0 (nfix m1)))
   (iff (equal m0 (car (pool-rec m1 v1 ens)))
        (and (<= (nfix m1) (nfix m0))
             (or (not (consp ens))
                 (not (equal (car ens) v1))))))
  :hints (("Goal" :induct (pool-rec m v1 ens))))

(defun pool-fix (m v1 n v2 ens)
  (if (not (consp ens)) (pool-rec m v1 (list v2))
    (if (zp n) (pool-rec m v1 (cons v2 (cons v2 (cdr ens))))
      (if (equal v1 v2) (append (pool-fix (1+ (nfix m)) v2 (1- n) (car ens) (cdr ens)) (list 0))
        (cons (nfix m) (pool-fix 1 v2 (1- n) (car ens) (cdr ens)))))))

(defthmd pool-fix-combination
  (equal (pool-rec m v1 (fix-rec n v2 ens))
         (pool-fix m v1 n v2 ens)))

(defun diff-rec-p (n v ens)
  (if (not (consp ens)) nil
    (if (zp n) (not (equal v (car ens)))
      (diff-rec-p (1- n) (car ens) (cdr ens)))))

(defthm diff-rec-p-nfix-n
  (equal (diff-rec-p (nfix n) v ens)
         (diff-rec-p n v ens))
  :hints (("Goal" :in-theory (enable nfix zp))))

(defthm diff-rec-p-list-fix
  (equal (diff-rec-p n v (list-fix ens))
         (diff-rec-p n v ens)))

(defthm idempotence
  (implies
   (not (diff-rec-p n v2 ens))
   (equal (pool-rec m v1 (cons v2 ens))
          (pool-rec m v1 (fix-rec n v2 ens))))
  :hints (("Goal" :in-theory (enable equal-len-o-to-consp len-cdr)
           :induct (pool-fix m v1 n v2 ens))
          ))
  
(defthm good-rule
  (implies
   (diff-rec-p n v2 ens)
   (nat-list-< (pool-rec m v1 (cons v2 ens))
               (pool-rec m v1 (fix-rec n v2 ens))))
  :hints (("Goal" :in-theory (enable equal-len-o-to-consp len-cdr)
           :induct (pool-fix m v1 n v2 ens))
          ))

(defun pool-fix-2 (m v1 n1 n2 v2 ens)
  (if (not (consp ens)) (list m v1 n1 n2 v2)
    (if (zp n2) (list m v1 n1 n2 v2)
      (if (zp n1) (list m v1 n1 n2 v2)
        (let ((n1 (nfix n1))
              (n2 (nfix n2)))
          (if (equal v1 v2) (pool-fix-2 (1+ (nfix m)) v2 (1- n1) (1- n2) (car ens) (cdr ens))
            (pool-fix-2 1 v2 (1- n1) (1- n2) (car ens) (cdr ens))))))))

(defthm car-fix-rec
  (equal (car (fix-rec n v ens)) v)
  :hints (("Goal" :expand (fix-rec n v ens))))

(defthm zp-implies-nfix-0
  (implies
   (zp n)
   (equal (nfix n) 0))
  :hints (("Goal" :in-theory (enable zp nfix))))

(defthm open-pool-rec
  (equal (pool-rec n v (cons a ens))
         (let ((n (nfix n)))
           (if (equal v a)
               (append (pool-rec (1+ n) a ens) (list 0))
             (cons n (pool-rec 1 a ens))))))

(defthm open-fix-rec
  (implies
   (consp ens)
   (equal (fix-rec n v ens)
          (if (zp n) (cons v (cons v (list-fix (cdr ens))))
            (cons v (fix-rec (1- n) (car ens) (cdr ens)))))))
          
;;
;; This feels like an important part of figuring out the maximum
;; time to convergence.
;;
(defthm order-matters
  (implies
   (and
    (< (nfix n2) (nfix n1))
    (diff-rec-p n2 v2 ens))
   (nat-list-< (pool-rec m v1 (fix-rec n1 v2 ens))
               (pool-rec m v1 (fix-rec n2 v2 ens))))
  :hints (("Goal" :in-theory (e/d (len-cdr) ())
           :induct (pool-fix-2 m v1 n1 n2 v2 ens))
#|          
          ("Subgoal *1/2.3" :in-theory (enable len-cdr)
           :expand ((POOL-REC (+ 1 (NFIX M))
                              V1
                              (FIX-REC (+ -1 N1) (CAR ENS) (CDR ENS)))))
          ("Subgoal *1/5.1" :in-theory (enable len-cdr))
          ("Subgoal *1/2.1" :expand ((POOL-REC 1 V2
                                     (FIX-REC (+ -1 N1)
                                              (CAR ENS)
                                              (CDR ENS)))))
          #+joe
          (and stable-under-simplificationp
               '(:in-theory (enable len-cdr)))))
          |#
          ))

(defun find-diff-rec (v ens)
  (if (not (consp ens)) 0
    (if (not (equal v (car ens))) 0
      (1+ (find-diff-rec (car ens) (cdr ens))))))

(defthm if-diff-rec-p-diff-rec-p-find-diff-rec
  (implies
   (diff-rec-p n v ens)
   (diff-rec-p (find-diff-rec v ens) v ens))
  :hints (("Goal" :induct (diff-rec-p n v ens))))

;;
;; This is the smallest step we could take ..
;;
(defun find-max-diff-rec (v ens)
  (if (not (consp ens)) 0
    (if (not (equal v (car ens)))
        (let ((n (find-max-diff-rec (car ens) (cdr ens))))
          (if (diff-rec-p n (car ens) (cdr ens)) (1+ n)
            0))
      (1+ (find-max-diff-rec (car ens) (cdr ens))))))

;; It actually points to a difference if one exists ..
(defthm if-diff-rec-p-diff-rec-p-find-max-diff-rec
  (implies
   (diff-rec-p n v ens)
   (diff-rec-p (find-max-diff-rec v ens) v ens))
  :hints (("Goal" :induct (diff-rec-p n v ens))
          ("Subgoal *1/2" :expand ((FIND-MAX-DIFF-REC V ENS)))))

(defthm if-diff-rec-p-diff-rec-p-find-max-diff-rec-better
  (implies
   (not (diff-rec-p (find-max-diff-rec v ens) v ens))
   (not (diff-rec-p n v ens))))

;; And it is the largest index that does ..
(defthm fix-max-returns-largest-index
  (implies
   (diff-rec-p n v ens)
   (<= (nfix n) (find-max-diff-rec v ens)))
  :hints (("Goal" :induct (diff-rec-p n v ens))
          ("Subgoal *1/2" :expand ((FIND-MAX-DIFF-REC V ENS)))))

(defthm not-diff-rec-p
  (not (diff-rec-p (+ (nfix m) 1) v1 (fix-rec m v2 ens)))
  :hints (("Goal" :induct (fix-rec m v2 ens))
          ("Subgoal *1/2" :in-theory (enable nfix)
           :expand ((DIFF-REC-P (NFIX M)
                            V2 (CONS V2 (CDR ENS)))
                    (DIFF-REC-P (+ 1 (NFIX M))
                            V1 (LIST* V2 V2 (CDR ENS)))))))

(defun all-equal-rec (x list)
  (if (not (consp list)) t
    (and (equal x (car list))
         (all-equal-rec x (cdr list)))))

(defthm all-equal-rec-list-fix
  (equal (all-equal-rec v (list-fix x))
         (all-equal-rec v x))
  :hints (("Goal" :in-theory (enable all-equal-rec))))

(defund all-equal (ens)
  (if (not (consp ens)) t
    (all-equal-rec (car ens) (cdr ens))))

(defthm all-equal-list-fix
  (equal (all-equal (list-fix x))
         (all-equal x))
  :hints (("Goal" :in-theory (enable all-equal))))

(defthm diff-find-max-diff-rec-to-all-equal-rec
  (equal (diff-rec-p (find-max-diff-rec v1 ens)
                     v1 ens)
         (not (all-equal-rec v1 ens))))

(defthm diff-find-diff-to-all-equal-rec
  (equal (diff-rec-p (find-diff-rec v1 ens)
                     v1 ens)
         (not (all-equal-rec v1 ens))))

(defthm all-equal-rec-implies-fix-rec-idempotent
  (implies
   (all-equal-rec v1 ens)
   (equal (FIX-REC n1 v1 ens)
          (cons v1 (list-fix ens)))))

(defthm len-list-fix
  (equal (len (list-fix x))
         (len x)))

;; (defun choose-diff (ens)
;;   (if (not (consp ens)) (equal n 0)
;;     (diff-rec-p n (car ens) (cdr ens))))

(defun find-diff-ens (ens)
  (if (not (consp ens)) 0
    (find-diff-rec (car ens) (cdr ens))))

(defun fix-ens (n ens)
  (if (not (consp ens)) nil
    ;;(let ((n (find-diff-rec (car ens) (cdr ens))))
    (fix-rec n (car ens) (cdr ens))))

(defthm fix-ens-list-fix
  (equal (fix-ens n (list-fix ens))
         (fix-ens n ens)))

(defthm all-equal-fix-ens
  (implies
   (all-equal ens)
   (equal (fix-ens n ens) 
          (list-fix ens)))
  :hints (("Goal" :in-theory (enable all-equal))))

(defthm cdr-fix-rec
  (equal (cdr (fix-rec n v ens))
         (if (not (consp ens)) nil
           (if (zp n) (cons v (list-fix (cdr ens)))
             (fix-rec (1- n) (car ens) (cdr ens))))))

(defun pool-ens (ens)
  (if (not (consp ens)) nil
    (pool-rec 1 (car ens) (cdr ens))))

(defun diff-ens-p (n ens)
  (if (not (consp ens)) nil
    (diff-rec-p n (car ens) (cdr ens))))

(defthm diff-ens-p-nfix
  (equal (diff-ens-p (nfix n) ens)
         (diff-ens-p n ens)))

(defthm diff-ens-p-list-fix
  (equal (diff-ens-p n (list-fix ens))
         (diff-ens-p n ens)))

;; Choose an 'n' such that diff-ens-p is true ..

(defun diff-exists (ens)
  (if (not (consp ens)) nil
    (diff-rec-p (find-diff-rec (car ens) (cdr ens)) (car ens) (cdr ens))))

(defthm idempotence-2
  (implies
   (not (diff-exists ens))
   (equal (pool-ens (fix-ens n ens))
          (pool-ens ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fix-rec pool-rec open-pool-rec))
          ("Subgoal 2.2" :expand ((POOL-REC 1 (CAR ENS) (CDR ENS))
                                  (POOL-REC 1 (CAR ENS)
                                            (CONS (CAR ENS) (LIST-FIX (CDDR ENS))))
                                  ))
          ("Subgoal 2.3" :expand ((POOL-REC 1 (CAR ENS) NIL)
                                  (POOL-REC 1 (CAR ENS) (CDR ENS))))
          ))

(defthm good-rule-2
  (implies
   (diff-exists ens)
   (nat-list-< (pool-ens ens)
               (pool-ens (fix-ens (find-diff-ens ens) ens))))
  :hints (("Goal" :in-theory (disable ALT-OPEN-NAT-LIST-< POOL-REC open-pool-rec))
          ("Subgoal 1" :in-theory (enable alt-open-nat-list-<)
           :expand ((POOL-REC 1 (CAR ENS) (CONS (CAR ENS) (CDDR ENS)))
                    (POOL-REC 1 (CAR ENS) (CDR ENS))))))
  
(defthmd gte-all-len-ens-pool-rec
  (gte-all (+ (nfix n) (len ens)) (pool-rec n v ens)))

(defthm get-all-len-ens-pool-ens
  (implies
   (equal m (len ens))
   (gte-all m (pool-ens ens)))
  :hints (("Goal" :do-not-induct t
           :use (:instance gte-all-len-ens-pool-rec
                           (n 1)
                           (v (car ens))
                           (ens (cdr ens))))))

(defun ens-measure (ens)
  (sub-list (len ens) (pool-ens ens)))
  
(defthm len-fix-ens
  (equal (len (fix-ens n ens))
         (len ens)))

(defthm len-pool-ens
  (equal (len (pool-ens ens))
         (len ens)))

(defthm ens-measure-monotonic
  (implies
   (not (diff-exists ens))
   (equal (ens-measure (fix-ens n ens))
          (ens-measure ens)))
  :hints (("Goal" :in-theory (disable pool-ens fix-ens diff-exists)
           :do-not-induct t)))

(defthm ens-measure-decreases
  (implies
   (diff-exists ens)
   (nat-list-< (ens-measure (fix-ens (find-diff-ens ens) ens))
               (ens-measure ens)))
  :hints (("Goal" :in-theory (disable pool-ens fix-ens diff-exists find-diff-ens)
           :do-not-induct t)))
  
;; If no diff exists, then ens is uniform.

;; The question is: How long until no differences exist?



;; ====================================================================
;;
;; So this might be a recursive version of the step count that lends
;; itself nicely to induction.  We prove that it is the same as the
;; closed form.
;;
;; ====================================================================

(defun summ (n)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) 0
      (let ((n (1- n)))
        (+ n (summ n))))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm summ-closed-form
    (equal (summ n)
           (let ((n (nfix n)))
             (/ (* n (1- n)) 2))))
  )

;; A B C D   (1 1 1 1)
;; A B C C   (1 1 2 0)
;; A B B C   (1 2 1 0)
;; A B B B   (1 3 0 0)
;; A A B B   (2 2 0 0)
;; A A A B   (3 1 0 0)
;; A A A A   (4 0 0 0)

;;
;; Consider an arbitrary schedule that selects a change "at random".
;; That will never be faster than 
;;

;; (defun arbitrary-fix-steps (ens)
;;   (if (not (diff-exists ens)) 0
;;     (let ((n (arbitrary-diff ens)))
;;       (let ((ens (fix-nth n ens)))
;;         (1+ (arbitrary-fix-steps ens))))))

;; (defun slowest-fix-steps (ens)
;;   (if (not (diff-exists ens)) 0
;;     (let ((n (slowest-diff ens)))
;;       (let ((ens (fix-nth n ens)))
;;         (1+ (arbitrary-fix-steps ens))))))

;; (defthm can-you-prove-this?
;;   (<= (arbitrary-fix-steps ens) (slowest-fix-steps ens)))

;;
;; You need to map them to the slowest number of steps.
;; 3 2 2 1 7
;; 3 2 2 1 1
;; 3 2 2 2 1
;; 3 2 2 2 2
;; 3 3 2 2 2
;; 3 3 3 2 2
;; 3 3 3 3 2
;; 3 3 3 3 3
;;
;; at each difference, you count the number until the end
;; of the string.  Now you can prove that this natural
;; number is always getting smaller.
;;


(defun max-steps-rec (v ens)
  (if (not (consp ens)) 0
    (if (not (equal v (car ens)))
        (+ (len ens) (max-steps-rec (car ens) (cdr ens)))
      (max-steps-rec (car ens) (cdr ens)))))

(defthm mmax-steps-rec-list-fix
  (equal (max-steps-rec v (list-fix x))
         (max-steps-rec v x)))

(defun max-steps-fix (v1 n v2 ens)
  (if (not (consp ens)) v1
    (if (zp n) v1
      (max-steps-fix v2 (1- n) (car ens) (cdr ens)))))

(defthm max-step-rec-fix-rec-arbitrary
  (<= (max-steps-rec v1 (fix-rec n v2 ens))
      (max-steps-rec v1 (cons v2 ens)))
  :hints (("Goal" 
           :do-not-induct t
           :induct (max-steps-fix v1 n v2 ens))
          (and stable-under-simplificationp
               '(:expand (MAX-STEPS-REC V1 (CDR ENS))))
          (and stable-under-simplificationp
               '(:expand (MAX-STEPS-REC V2 (CDR ENS))))
          ))

(defthmd max-step-rec-fix-rec-arbitrary-smaller
  (implies
   (diff-rec-p n v2 ens)
   (< (max-steps-rec v1 (fix-rec n v2 ens))
      (max-steps-rec v1 (cons v2 ens))))
  :hints (("Goal"            :do-not-induct t
           :induct (max-steps-fix v1 n v2 ens))
          (and stable-under-simplificationp
               '(:expand (MAX-STEPS-REC V1 (CDR ENS))))
          (and stable-under-simplificationp
               '(:expand (MAX-STEPS-REC V2 (CDR ENS))))
          ))

(defun max-steps-max-diff-induction (v1 v2 ens)
  (if (not (consp ens)) v1
    (if (not (equal v2 (car ens)))
        (max-steps-max-diff-induction v2 (car ens) (cdr ens))
      (max-steps-max-diff-induction v2 (car ens) (cdr ens)))))

;; DAG : 
;; So .. what we can say is that this change is equal to 1 .. and
;; any other change is at least 1.  That will allow us to prove that
;; this is an upper bound on the number of changes possible before
;; reaching uniformity.

(defthm all-equal-rec-implies-zero-steps
  (implies
   (all-equal-rec v1 ens)
   (equal (MAX-STEPS-REC v1 ens) 0)))

(defthm all-equal-rec-max-steps
  (implies
   (all-equal-rec v1 ens)
   (equal (max-steps-rec v2 ens)
          (if (equal v2 v1) 0
            (len ens)))))

(defthm max-step-rec-fix-rec-smallest
  (implies
   (not (all-equal-rec v2 ens))
   (equal (max-steps-rec v1 (fix-rec (find-max-diff-rec v2 ens) v2 ens))
          (1- (max-steps-rec v1 (cons v2 ens)))))
  :hints (("Goal" :induct (max-steps-max-diff-induction v1 v2 ens))))

(defthm diff-rec-p-implies-not-all-equal-rec
  (implies
   (diff-rec-p n v2 ens)
   (not (all-equal-rec v2 ens))))

;;
;; DAG : so there you go .. now you can prove that there is a
;; worst-case strategy.
;;
(defthm max-step-rec-fix-rec-lte
  (implies
   (diff-rec-p n v2 ens)
   (<= (max-steps-rec v1 (fix-rec n v2 ens))
       (max-steps-rec v1 (fix-rec (find-max-diff-rec v2 ens) v2 ens))))
  :hints (("Goal" :do-not-induct t
           :use max-step-rec-fix-rec-arbitrary-smaller)))

;; 1 2 3 3 4
;; 1 2 3 3 3
;; 1 2 2 3 3
;; 1 2 2 2 3
;; 1 2 2 2 2
;; 1 1 2 2 2
;; 1 1 1 2 2
;; 1 1 1 1 2
;; 1 1 1 1 1

(defun max-steps (ens)
  (if (not (consp ens)) 0
    (max-steps-rec (car ens) (cdr ens))))

;; If you run the system max-steps-rec

(defchoose diff-index-raw (n) (ens)
  (diff-ens-p n ens))

(defund diff-index (ens)
  (nfix (diff-index-raw (list-fix ens))))

(defthm diff-index-list-fix
  (equal (diff-index (list-fix ens))
         (diff-index ens))
  :hints (("Goal" :in-theory (enable diff-index))))

(defthm diff-index-property
  (implies
   (diff-ens-p n ens)
   (diff-ens-p (diff-index ens) ens))
  :hints (("Goal" :in-theory (e/d (diff-index) (diff-ens-p))
           :use (:instance diff-index-raw
                           (ens (list-fix ens))))))

(defthm not-all-equal-rec-implies-positive-max-steps-rec
  (IMPLIES
   (not (all-equal-rec v0 ens))
   (< 0 (max-steps-rec v0 ens))))
         
(defthm not-all-equal-implies-positive-max-steps
  (implies
   (not (all-equal ens))
   (< 0 (MAX-STEPS ENS)))
  :hints (("Goal" :in-theory (enable all-equal max-steps))))

(defthm all-equal-rec-not-consp
  (implies
   (not (consp ens))
   (equal (all-equal-rec v ens) t))
  :hints (("Goal" :in-theory (enable all-equal-rec))))

(defthm all-equal-not-consp
  (implies
   (not (consp ens))
   (equal (all-equal ens) t))
  :hints (("Goal" :in-theory (enable all-equal))))

(in-theory (disable ALL-EQUAL-REC MAX-STEPS-REC fix-rec OPEN-FIX-REC))

(defthmd not-all-equal-implies-diff-end-p-diff-index
  (implies
   (not (all-equal ens))
   (diff-ens-p (DIFF-INDEX ENS) ens))
  :hints (("Goal" :in-theory (enable all-equal)
           :use (:instance diff-index-property
                           (n (find-diff-rec (car ens) (cdr ens)))))))

(defun max-steps-fix-rec-induction (v2 n v1 ens)
  (if (not (consp ens)) v2
    (if (zp n) v2
      (max-steps-fix-rec-induction v1 (1- n) (car ens) (cdr ens)))))

(defthm max-steps-rec-fix-rec-smaller
  (implies
   (diff-rec-p n v1 ens)
   (< (max-steps-rec v2 (fix-rec n v1 ens))
      (max-steps-rec v2 (cons v1 ens))))
  :hints (("Goal" :in-theory (enable max-steps-rec fix-rec)
           :induct (max-steps-fix-rec-induction v2 n v1 ens))
          (and stable-under-simplificationp
               '(:expand ((MAX-STEPS-REC V1 (CDR ENS))
                          )))
          ))

(in-theory (disable fix-ens max-steps))

(defthm measure-property
  (IMPLIES
   (NOT (ALL-EQUAL ENS))
   (< (MAX-STEPS (FIX-ENS (DIFF-INDEX ENS) ENS))
      (MAX-STEPS ENS)))
  :hints (("Goal" :use not-all-equal-implies-diff-end-p-diff-index
           :in-theory (enable fix-ens max-steps))
          ("Subgoal 1"
           :expand ((MAX-STEPS-REC (CAR ENS)  (CDR ENS))
                    (MAX-STEPS-REC (CAR ENS)  (CDDR ENS))
                    (MAX-STEPS-REC (CADR ENS) (CDDR ENS))
                    (MAX-STEPS-REC (CAR ENS)  (CONS (CAR ENS) (LIST-FIX (CDDR ENS))))))))


(in-theory (disable fix-ens max-steps))

(defun actual-steps (ens)
  (declare (xargs :measure (max-steps ens)))
  (if (all-equal ens) 0
    (let ((n (diff-index ens)))
      (let ((ens (fix-ens n ens)))
        (1+ (actual-steps ens))))))

(defund max-index (ens)
  (if (not (consp ens)) 0
    (find-max-diff-rec (car ens) (cdr ens))))

(defun max-steps-induction (v1 v2 ens)
  (if (not (consp ens)) (list v1 v2)
    (max-steps-induction (car ens) (car ens) (cdr ens))))

(defthm max-steps-rec-property
  (IMPLIES (NOT (ALL-EQUAL-REC V1 ens))
           (<= (MAX-STEPS-REC V2 ens)
               (+ (len ens) (MAX-STEPS-REC v1 ens))))
  :hints (("Goal" :induct (max-steps-induction v1 v2 ens)
           :in-theory (enable max-steps-rec all-equal-rec))))

(defthm max-step-fix-lte
  (implies
   (diff-ens-p n ens)
   (<= (max-steps (fix-ens n ens))
       (max-steps (fix-ens (max-index ens) ens))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (max-steps
                            fix-ens
                            max-index)
                           (;;MAX-STEP-REC-FIX-REC-SMALLEST
                            FIND-MAX-DIFF-REC
                            DIFF-REC-P)))
          ("Subgoal 3" :expand ((DIFF-REC-P N (CAR ENS) (CDR ENS))
                                (FIND-MAX-DIFF-REC (CAR ENS) (CDR ENS))))
          ("Subgoal 4" :in-theory (disable MAX-STEP-REC-FIX-REC-SMALLEST)
           :expand ((DIFF-REC-P N (CAR ENS) (CDR ENS))
                    (FIND-MAX-DIFF-REC (CAR ENS) (CDR ENS))))
          ("Subgoal 5" :expand ((MAX-STEPS-REC (CAR ENS) (CONS (CAR ENS) (LIST-FIX (CDDR ENS))))
                                (MAX-STEPS-REC (CAR ENS) (CDR ENS))
                                (DIFF-REC-P N (CAR ENS) (CDR ENS))
                                (FIND-MAX-DIFF-REC (CAR ENS) (CDR ENS))))))

(defthm max-step-fix-lte-instance
  (implies
   (not (all-equal ens))
   (<= (max-steps (fix-ens (DIFF-INDEX ENS) ens))
       (max-steps (fix-ens (max-index ens) ens))))
  :hints (("Goal" :in-theory (enable all-equal)
           :use ((:instance max-step-fix-lte
                            (n (DIFF-INDEX ENS)))
                 (:instance diff-index-property
                            (n (find-diff-rec (car ens) (cdr ens)))))))
  :rule-classes :linear)

(defthm open-max-steps
  (implies
   (not (all-equal ens))
   (equal (max-steps ens)
          (1+ (max-steps (fix-ens (max-index ens) ens)))))
  :hints (("Goal" :in-theory (enable all-equal
                                     max-steps
                                     FIX-ENS max-index))
          ("Subgoal 2" :expand (ALL-EQUAL-REC (CAR ENS) (CDR ENS)))
          ("Subgoal 1" :expand ((ALL-EQUAL-REC (CAR ENS) (CDR ENS))
                                (FIND-MAX-DIFF-REC (CAR ENS) (CDR ENS))
                                (MAX-STEPS-REC (CAR ENS) (CDR ENS))
                                (MAX-STEPS-REC (CAR ENS)
                                  (CONS (CAR ENS)
                                        (LIST-FIX (CDDR ENS))))
                                ))
          ))

(defthm actual-steps-is-less-than-max-steps
  (<= (actual-steps ens) (max-steps ens)))

(defun run (n ens)
  (if (zp n) (list-fix ens)
    (let ((m (diff-index ens)))
      (let ((ens (fix-ens m ens)))
        (run (1- n) ens)))))

(defthm run-list-fix
  (equal (run n (list-fix x))
         (run n x)))

(defthm actual-steps-is-sufficient-for-convergence
  (implies
   (<= (actual-steps ens) (nfix n))
   (all-equal (run n ens))))

(defthm max-steps-results-in-all-equal
  (all-equal (run (max-steps ens) ens)))

(defthmd max-steps-rec-is-bounded
  (<= (* 2 (max-steps-rec v ens))
      (* (1+ (len ens)) (len ens)))
  :hints (("Goal" :in-theory (enable max-steps-rec)
           :induct (max-steps-rec v ens))))

(defun all-diff-rec-p (v ens)
  (if (not (consp ens)) t
    (and (not (equal v (car ens)))
         (all-diff-rec-p (car ens) (cdr ens)))))

(defun all-diff-p (ens)
  (if (not (consp ens)) t
    (all-diff-rec-p (car ens) (cdr ens))))

(defthmd max-steps-rec-worst-case
  (implies
   (all-diff-rec-p v ens)
   (equal (* 2 (max-steps-rec v ens))
          (* (1+ (len ens)) (len ens))))
  :hints (("Goal" :in-theory (enable max-steps-rec)
           :induct (max-steps-rec v ens))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm max-steps-is-bounded
    (<= (max-steps ens)
        (/ (* (len ens) (1- (len ens))) 2))
    :hints (("Goal" :do-not-induct t
             :use (:instance max-steps-rec-is-bounded
                             (v (car ens))
                             (ens (cdr ens)))
             :in-theory (enable max-steps))))

  (defthm max-steps-worst-case
    (implies
     (all-diff-p ens)
     (equal (max-steps ens)
            (/ (* (len ens) (1- (len ens))) 2)))
    :hints (("Goal" :in-theory (enable max-steps)
             :use (:instance max-steps-rec-worst-case
                             (v (car ens))
                             (ens (cdr ens)))
             :do-not-induct t)))
  
  )
  
