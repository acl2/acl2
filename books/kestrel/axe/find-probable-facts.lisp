; Finding likely facts to break down a proof
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(include-book "test-cases")
(include-book "evaluator") ; todo: use basic eval but need to avaluate dag-val-with-axe-evaluator in examples like rc4-loop, make this file a generator that takes an evaluator?
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove
(include-book "kestrel/bv/bvif" :dir :system) ; do not remove
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (e/d (true-listp-of-cdr-strong)
                       (true-listp-of-cdr))))

(local
   ;dup
 (defthm all-<=-when-all-<
   (implies (all-< x bound)
            (all-<= x bound))
   :hints (("Goal" :in-theory (enable all-< all-<=)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-consp-of-array-to-alist-aux
  (implies (all-consp acc)
           (all-consp (array-to-alist-aux n len array-name array acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm all-consp-of-array-to-alist
  (all-consp (array-to-alist array-name array len))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm nat-listp-of-strip-cars-of-of-array-to-alist-aux
  (implies (nat-listp (strip-cars acc))
           (nat-listp (strip-cars (array-to-alist-aux n len array-name array acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm nat-listp-of-strip-cars-of-of-array-to-alist
  (nat-listp (strip-cars (array-to-alist array-name array len)))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm all-<-of-strip-cars-of-of-array-to-alist-aux
  (implies (and (all-< (strip-cars acc) bound)
                (<= len bound))
           (all-< (strip-cars (array-to-alist-aux n len array-name array acc)) bound))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm all-<-of-strip-cars-of-of-array-to-alist
  (implies (<= len bound)
           (all-< (strip-cars (array-to-alist array-name array len)) bound))
  :hints (("Goal" :in-theory (enable array-to-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund nat-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (nat-listp (first x))
         (nat-list-listp (rest x)))))

(defthm nat-list-listp-of-cons
  (equal (nat-list-listp (cons a x))
         (and (nat-listp a)
              (nat-list-listp x)))
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(defthmd nat-listp-of-car-when-nat-list-listp
  (implies (nat-list-listp x)
           (nat-listp (car x)))
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(local (in-theory (enable nat-listp-of-car-when-nat-list-listp)))

(defthm nat-list-listp-forward-to-true-listp
  (implies (nat-list-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable nat-list-listp))))

(defthm nat-list-listp-of-append
  (equal (nat-list-listp (append x y))
         (and (nat-list-listp (true-list-fix x))
              (nat-list-listp y)))
  :hints (("Goal" :in-theory (enable nat-list-listp append))))

(defthm nat-listp-of-lookup-equal
  (implies (nat-list-listp (strip-cdrs alist))
           (nat-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs
                                     nat-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund all-all-< (x bound)
  (declare (xargs :guard (and (nat-list-listp x) ;gen?
                              (rationalp bound))
                  :guard-hints (("Goal" :in-theory (enable nat-list-listp)))))
  (if (endp x)
      t
    (and (all-< (first x) bound)
         (all-all-< (rest x) bound))))

(defthm all-all-<-of-nil
  (all-all-< nil bound)
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-<-of-car-when-all-all-<
  (implies (and (all-all-< x bound)
                (consp x))
           (all-< (car x) bound))
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-all-<-of-cons
  (equal (all-all-< (cons a x) bound)
         (and (all-< a bound)
              (all-all-< x bound)))
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-all-<-of-append
  (equal (all-all-< (append x y) bound)
         (and (all-all-< x bound)
              (all-all-< y bound)))
  :hints (("Goal" :in-theory (enable all-all-<))))

(defthm all-<-of-lookup-equal
  (implies (all-all-< (strip-cdrs alist) bound)
           (all-< (lookup-equal key alist) bound))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs
                                     all-all-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;args are nodenums and/or quoteps
;;returns (mv worklist worklist-extendedp) where nodenum-worklist has been extended by any args to compute (non quoteps not marked done)
;; and worklist-extendedp indicates whether there were any such args
;rename?
(defund add-args-not-done (dargs done-nodes-array worklist worklist-extendedp)
  (declare (xargs :guard (and (array1p 'done-nodes-array done-nodes-array)
                              (bounded-darg-listp dargs (alen1 'done-nodes-array done-nodes-array)))))
  (if (endp dargs)
      (mv worklist worklist-extendedp)
    (let ((arg (first dargs)))
      (if (or (consp arg) ; skip quoted constants
              (aref1 'done-nodes-array done-nodes-array arg) ;;skip dargs that are marked as done
              )
          (add-args-not-done (rest dargs) done-nodes-array worklist worklist-extendedp)
        (add-args-not-done (rest dargs) done-nodes-array (cons arg worklist) t ;we've extended the worklist
                           )))))

(defthm add-args-not-done-of-nil-arg1
  (equal (add-args-not-done nil done-nodes-array worklist worklist-extendedp)
         (mv worklist worklist-extendedp))
  :hints (("Goal" :in-theory (enable add-args-not-done))))

(defthm nat-listp-of-mv-nth-0-of-add-args-not-done
  (implies (and ;(array1p 'done-nodes-array done-nodes-array)
            (all-dargp args) ; (bounded-darg-listp args (alen1 'done-nodes-array done-nodes-array))
            (NAT-LISTP WORKLIST))
           (nat-listp (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))))
  :hints (("Goal" :in-theory (enable add-args-not-done))))

(defthm all-<-of-mv-nth-0-of-add-args-not-done
  (implies (and ;(array1p 'done-nodes-array done-nodes-array)
            (bounded-darg-listp args bound)
            (all-< WORKLIST bound))
           (all-< (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))
                   bound))
  :hints (("Goal" :in-theory (enable add-args-not-done))))

(defthm true-listp-of-mv-nth-0-of-add-args-not-done
  (implies (true-listp worklist)
           (true-listp (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-args-not-done))))

;; once it's true, it stays true
(defthm mv-nth-1-of-add-args-not-done-of-t
  (mv-nth 1 (add-args-not-done args done-nodes-array worklist t))
  :hints (("Goal" :in-theory (enable add-args-not-done))))

(defthm mv-nth-0-of-add-args-not-done-when-not-mv-nth-1-of-add-args-not-done
  (implies (not (mv-nth 1 (add-args-not-done args done-nodes-array worklist worklist-extendedp)))
           (equal (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))
                  worklist))
  :hints (("Goal" :in-theory (enable add-args-not-done))))


;args are nodenums with values in the array, or quoteps
;looks up the nodenums and unquotes the constants
;does similar functionality exist elsewhere (array names might differ)?
(defund get-vals-of-args (dargs test-case-array-name test-case-array)
  (declare (xargs :guard (and (array1p test-case-array-name test-case-array)
                              (bounded-darg-listp dargs (alen1 test-case-array-name test-case-array)))))
  (if (endp dargs)
      nil
    (let ((darg (first dargs)))
      (cons (if (consp darg) ; check for quoted constant
                (unquote darg)
              ;;otherwise it's a nodenum:
              (aref1 test-case-array-name test-case-array darg))
            (get-vals-of-args (rest dargs) test-case-array-name test-case-array)))))

(defund num-true-nodes (n array-name array)
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      0
      (if (aref1 array-name array n)
          (+ 1
             (num-true-nodes (+ -1 n) array-name array))
        (num-true-nodes (+ -1 n) array-name array))))

(defthm <=-of-num-true-nodes-linear
  (implies (and (integerp n)
                (<= -1 n))
           (<= (num-true-nodes n array-name array)
               (+ 1 n)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable num-true-nodes))))

(defund print-vals-of-nodes (nodenums array-name array)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p array-name array)
                              (all-< nodenums (alen1 array-name array)))))
  (if (endp nodenums)
      nil
    (prog2$ (cw "Node ~x0 is ~x1.~%" (first nodenums) (aref1 array-name array (car nodenums)))
            (print-vals-of-nodes (rest nodenums) array-name array))))


;; ;move, optimize
;; (defund evens-tail (lst acc)
;;   (declare (xargs :guard (true-listp acc)
;;                   ))
;;   (if (atom lst)
;;       (reverse acc)
;;     (if (atom (cdr lst))
;;         (reverse (cons (car lst) acc))
;;       (evens-tail (cddr lst)
;;                   (cons (car lst) acc)))))

;; (defthm len-of-evens-tail-bound
;;   (implies (< 1 (len l))
;;            (< (len (evens-tail l acc))
;;               (+ (len acc) (len l))))
;;   :hints (("Goal" :expand (evens-tail (cddr l)
;;                                       (cons (car l) acc))
;;            :in-theory (enable evens-tail))))

;; (defthm evens-tail-of-singleton
;;   (implies (equal (len l) 1)
;;            (equal (evens-tail l nil)
;;                   (list (car l))))
;;   :hints (("Goal" :in-theory (enable evens-tail reverse))))

;; ;; (defun odds-tail (l)
;; ;;   (declare (xargs :guard t))
;; ;;   (if (consp l)
;; ;;       (evens-tail (cdr l) nil)
;; ;;     nil))

;; (in-theory (disable evens-tail))

;; comparison function for the sort
(defun-inline lexorder-of-cdrs (x y)
  (declare (xargs :guard (and (consp x)
                              (consp y))))
  (lexorder (cdr x) (cdr y)))

;; todo: put the merge-sort arg first
;; todo: pass in a list-pred (a kind of alist)?
(defmergesort merge-lexorder-of-cdrs
  merge-sort-lexorder-of-cdrs
  lexorder-of-cdrs
  consp)

(local
 (defthmd alistp-when-all-consp
   (implies (all-consp x)
            (equal (alistp x)
                   (true-listp x)))
   :hints (("Goal" :in-theory (enable alistp)))))

(local
 (defthmd alistp-becomes-all-consp
   (equal (alistp x)
          (and (all-consp x)
               (true-listp x)))
   :hints (("Goal" :in-theory (enable alistp)))))

;; (defthm alistp-of-merge-lexorder-of-cdrs
;;   (implies (and (alistp l1)
;;                 (alistp l2)
;;                 (alistp acc))
;;            (alistp (merge-lexorder-of-cdrs l1 l2 acc)))
;;   :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm alistp-of-merge-sort-lexorder-of-cdrs
  (implies (alistp l)
           (alistp (merge-sort-lexorder-of-cdrs l)))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs alistp-becomes-all-consp))))

(defthm nat-listp-of-strip-cars-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (nat-listp (strip-cars lst))
                (nat-listp (strip-cars acc))
                (<= (len tail) (len lst)))
           (nat-listp (strip-cars (mv-nth 0 (split-list-fast-aux lst tail acc)))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm nat-listp-of-strip-cars-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (nat-listp (strip-cars lst))
                (nat-listp (strip-cars acc))
                (<= (len tail) (len lst)))
           (nat-listp (strip-cars (mv-nth 1 (split-list-fast-aux lst tail acc)))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm nat-listp-of-strip-cars-of-mv-nth-0-of-split-list-fast
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (mv-nth 0 (split-list-fast lst)))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm nat-listp-of-strip-cars-of-mv-nth-1-of-split-list-fast
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (mv-nth 1 (split-list-fast lst)))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm nat-listp-of-strip-cars-of-merge-lexorder-of-cdrs
  (implies (and (nat-listp (strip-cars l1))
                (nat-listp (strip-cars l2))
                (nat-listp (strip-cars acc)))
           (nat-listp (strip-cars (merge-lexorder-of-cdrs l1 l2 acc))))
  :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm nat-listp-of-strip-cars-of-merge-sort-lexorder-of-cdrs
  (implies (nat-listp (strip-cars lst))
           (nat-listp (strip-cars (merge-sort-lexorder-of-cdrs lst))))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs))))

(defthm all-<-of-strip-cars-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-< (strip-cars lst) bound)
                (all-< (strip-cars acc) bound)
                (<= (len tail) (len lst)))
           (all-< (strip-cars (mv-nth 0 (split-list-fast-aux lst tail acc)))
                  bound))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm all-<-of-strip-cars-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (all-< (strip-cars lst) bound)
                (all-< (strip-cars acc) bound)
                (<= (len tail) (len lst)))
           (all-< (strip-cars (mv-nth 1 (split-list-fast-aux lst tail acc)))
                   bound))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm all-<-of-strip-cars-of-mv-nth-0-of-split-list-fast
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (mv-nth 0 (split-list-fast lst))) bound))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-<-of-strip-cars-of-mv-nth-1-of-split-list-fast
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (mv-nth 1 (split-list-fast lst))) bound))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-<-of-strip-cars-of-merge-lexorder-of-cdrs
  (implies (and (all-< (strip-cars l1) bound)
                (all-< (strip-cars l2) bound)
                (all-< (strip-cars acc) bound))
           (all-< (strip-cars (merge-lexorder-of-cdrs l1 l2 acc))
                   bound))
  :hints (("Goal" :in-theory (enable merge-lexorder-of-cdrs))))

(defthm all-<-of-strip-cars-of-merge-sort-lexorder-of-cdrs
  (implies (all-< (strip-cars lst) bound)
           (all-< (strip-cars (merge-sort-lexorder-of-cdrs lst)) bound))
  :hints (("Goal" :in-theory (enable merge-sort-lexorder-of-cdrs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm nat-listp-of-mv-nth-0-of-split-list-fast-aux
;;   (implies (and (nat-listp lst)
;;                 (nat-listp acc)
;;                 (<= (len tail) (len lst)))
;;            (nat-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm nat-listp-of-mv-nth-1-of-split-list-fast-aux
;;   (implies (and (nat-listp lst)
;;                 (nat-listp acc)
;;                 (<= (len tail) (len lst)))
;;            (nat-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm nat-listp-of-mv-nth-0-of-split-list-fast
;;   (implies (nat-listp lst)
;;            (nat-listp (mv-nth 0 (split-list-fast lst))))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm nat-listp-of-mv-nth-1-of-split-list-fast
;;   (implies (nat-listp lst)
;;            (nat-listp (mv-nth 1 (split-list-fast lst))))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm nat-listp-of-merge-<
;;   (implies (and (nat-listp l1)
;;                 (nat-listp l2)
;;                 (nat-listp acc))
;;            (nat-listp (merge-< l1 l2 acc)))
;;   :hints (("Goal" :in-theory (enable merge-<))))

;; (defthm nat-listp-of-merge-sort-<
;;   (implies (nat-listp lst)
;;            (nat-listp (merge-sort-< lst)))
;;   :hints (("Goal" :in-theory (enable merge-sort-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm all-<-of-mv-nth-0-of-split-list-fast-aux
;;   (implies (and (all-< lst bound)
;;                 (all-< acc bound)
;;                 (<= (len tail) (len lst)))
;;            (all-< (mv-nth 0 (split-list-fast-aux lst tail acc))
;;                   bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm all-<-of-mv-nth-1-of-split-list-fast-aux
;;   (implies (and (all-< lst bound)
;;                 (all-< acc bound)
;;                 (<= (len tail) (len lst)))
;;            (all-< (mv-nth 1 (split-list-fast-aux lst tail acc))
;;                    bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast-aux))))

;; (defthm all-<-of-mv-nth-0-of-split-list-fast
;;   (implies (all-< lst bound)
;;            (all-< (mv-nth 0 (split-list-fast lst)) bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm all-<-of-mv-nth-1-of-split-list-fast
;;   (implies (all-< lst bound)
;;            (all-< (mv-nth 1 (split-list-fast lst)) bound))
;;   :hints (("Goal" :in-theory (enable split-list-fast))))

;; (defthm all-<-of-merge-<
;;   (implies (and (all-< l1 bound)
;;                 (all-< l2 bound)
;;                 (all-< acc bound))
;;            (all-< (merge-< l1 l2 acc)
;;                    bound))
;;   :hints (("Goal" :in-theory (enable merge-<))))

;; (defthm all-<-of-merge-sort-<
;;   (implies (all-< lst bound)
;;            (all-< (merge-sort-< lst) bound))
;;   :hints (("Goal" :in-theory (enable merge-sort-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm num-true-nodes-of-aset1
;;   (implies (and (array1p array-name array)
;;                 (natp n)
;;                 (< n (alen1 array-name array))
;;                 (natp index)
;;                 (<= index n)
;;                 val)
;;            (equal (num-true-nodes n array-name (aset1 array-name array index val))
;;                   (if (aref1 array-name array index)
;;                       (num-true-nodes n array-name array)
;;                     (+ 1 (num-true-nodes n array-name array)))))
;;   :hints (("Goal" :expand ((num-true-nodes 0 array-name (aset1 array-name array 0 val))))))

;returns (mv test-case-array done-nodes-array), where TEST-CASE-ARRAY will have values for each node that is relevant (supports the nodes in the initial work-list) on this test case (note that because of ifs, the set of relevant nodes can differ between test cases).  nodes that have had their values set in TEST-CASE-ARRAY will be associated with t in DONE-NODES-ARRAY
;ffixme could speed this up using stobj arrays?
;fixme if there are no ifs in the dag, it would probably be faster to just evaluate every node in order?
;ffffixme add short-circuit evaluation for booland and boolor?
(defund evaluate-test-case-aux (count ; forces termination (todo: try having two kinds of :examined status for IF nodes (whether the test has been pushed, whether the relevant branch has been pushed), and base a measure on that
                                nodenum-worklist
                                dag-array-name dag-array dag-len
                                test-case ;the test case (gives values for variables)
                                test-case-array
                                done-nodes-array
                                interpreted-function-alist test-case-array-name)
  (declare (xargs ;; :measure (make-ord 1 (+ 1 (- (nfix (alen1 'done-nodes-array done-nodes-array))
            ;;                              (num-true-nodes (+ -1 (alen1 'done-nodes-array done-nodes-array))
            ;;                                              'done-nodes-array done-nodes-array)))
            ;;                    (len nodenum-worklist))
            :guard (and (natp count)
                        (nat-listp nodenum-worklist)
                        (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                        (all-< nodenum-worklist dag-len)
                        (array1p test-case-array-name test-case-array)
                        (equal (alen1 test-case-array-name test-case-array) dag-len)
                        (array1p 'done-nodes-array done-nodes-array)
                        (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                        (symbol-alistp test-case)
                        (interpreted-function-alistp interpreted-function-alist))
            :verify-guards nil ; done below
            ))
  (if (zp count)
      (prog2$ (er hard? 'evaluate-test-case-aux "Limit reached.")
              (mv test-case-array done-nodes-array))
    (if (endp nodenum-worklist)
        (mv test-case-array done-nodes-array)
      (let ((nodenum (first nodenum-worklist)))
        (if (aref1 'done-nodes-array done-nodes-array nodenum)
            ;;it's possible that the node became done while this copy of its nodenum was sitting on the worklist (it was pushed again and processed, while this copy of it was still sitting there)
            (evaluate-test-case-aux (+ -1 count) (rest nodenum-worklist) dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
          ;;the node is not yet done:
          (let ((expr (aref1 dag-array-name dag-array nodenum)))
            (if (variablep expr)
                (b* ((entry (assoc-eq expr test-case))
                     (- (if (not entry)
                            (cw "WARNING: No entry for ~x0 in alist.~%" expr) ;previously this was an error
                          nil))
                     (value (cdr entry)))
                  (evaluate-test-case-aux (+ -1 count)
                                          (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                          (aset1 test-case-array-name test-case-array nodenum value)
                                          (aset1 'done-nodes-array done-nodes-array nodenum t)
                                          interpreted-function-alist test-case-array-name))
              (let ((fn (ffn-symb expr)))
                (if (eq 'quote fn)
                    (let ((value (unquote expr)))
                      (evaluate-test-case-aux (+ -1 count)
                                              (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                              (aset1 test-case-array-name test-case-array nodenum value)
                                              (aset1 'done-nodes-array done-nodes-array nodenum t)
                                              interpreted-function-alist test-case-array-name))
                  ;;function call or if (clean this up?)
                  (let ((dargs (dargs expr)))
                    (if (or (eq 'if fn)
                            (eq 'myif fn))
                        (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                      :logic (<= 3 (len dargs)))) ; for guard proof
                            (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                    (mv test-case-array done-nodes-array))
                          ;; It's an IF/MYIF, so only evaluate the branch we need:
                          (let* ((test (first dargs))
                                 (test-quotep (consp test))
                                 (test-done (or test-quotep
                                                (aref1 'done-nodes-array done-nodes-array test))))
                            (if (not test-done)
                                ;;will reanalyze the IF/MYIF node once the test is evaluated:
                                (evaluate-test-case-aux (+ -1 count)
                                                        (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                              ;;we know the result of the test, so handle the relevant branch
                              (let* ((test-val (if test-quotep
                                                   (unquote test)
                                                 (aref1 test-case-array-name test-case-array test)))
                                     (relevant-branch (if test-val (second dargs) (third dargs)))
                                     (quotep-relevant-branch (consp relevant-branch))
                                     (relevant-branch-done (or quotep-relevant-branch
                                                               (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                (if (not relevant-branch-done)
                                    ;;will reanalyze the IF/MYIF again after once the relevant branch is evaluated:
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (cons relevant-branch nodenum-worklist) dag-array-name
                                                            dag-array dag-len test-case test-case-array done-nodes-array
                                                            interpreted-function-alist test-case-array-name)
                                  ;; if the relevant branch has been computed, the value of the IF/MYIF is just that branch
                                  (let ((relevant-branch-value (if quotep-relevant-branch
                                                                   (unquote relevant-branch)
                                                                 (aref1 test-case-array-name test-case-array relevant-branch))))
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (rest nodenum-worklist)
                                                            dag-array-name dag-array dag-len
                                                            test-case
                                                            (aset1 test-case-array-name test-case-array nodenum relevant-branch-value)
                                                            (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                            interpreted-function-alist test-case-array-name)))))))
                      (if (eq 'boolif fn)
                          (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                        :logic (<= 3 (len dargs))))
                              (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                      (mv test-case-array done-nodes-array))
                            ;; It's a BOOLIF so only evaluate the branch we need:
                            (let* ((test (first dargs))
                                   (test-quotep (consp test))
                                   (test-done (or test-quotep
                                                  (aref1 'done-nodes-array done-nodes-array test))))
                              (if (not test-done)
                                  ;;will reanalyze the BOOLIF node once the test is evaluated:
                                  (evaluate-test-case-aux (+ -1 count)
                                                          (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                          test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                                ;;we know the result of the test, so handle the relevant branch
                                (let* ((test-val (if test-quotep
                                                     (unquote test)
                                                   (aref1 test-case-array-name test-case-array test)))
                                       (relevant-branch (if test-val (second dargs) (third dargs)))
                                       (quotep-relevant-branch (consp relevant-branch))
                                       (relevant-branch-done (or quotep-relevant-branch
                                                                 (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                  (if (not relevant-branch-done)
                                      ;;will reanalyze the BOOLIF node once the relevant branch is evaluated:
                                      (evaluate-test-case-aux (+ -1 count)
                                                              (cons relevant-branch nodenum-worklist) dag-array-name
                                                              dag-array dag-len test-case test-case-array done-nodes-array
                                                              interpreted-function-alist test-case-array-name)
                                    ;; if the relevant branch has been computed, the value of the BOOLIF is just that branch,
                                    ;; except that we have to bvchop/bool-fix it
                                    (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                      (unquote relevant-branch)
                                                                    (aref1 test-case-array-name test-case-array relevant-branch)))
                                           (value (bool-fix relevant-branch-value)))
                                      (evaluate-test-case-aux (+ -1 count)
                                                              (rest nodenum-worklist)
                                                              dag-array-name dag-array dag-len test-case
                                                              (aset1 test-case-array-name test-case-array nodenum value)
                                                              (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                              interpreted-function-alist test-case-array-name)))))))
                        (if (eq 'bvif fn)
                            (if (not (mbe :exec (consp (cdr (cdr (cdr dargs))))
                                          :logic (<= 4 (len dargs))))
                                (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                        (mv test-case-array done-nodes-array))
                              ;; It's a BVIF, so only evaluate the branch we need:
                              (let* ((test (second dargs))
                                     (test-quotep (consp test))
                                     (test-done (or test-quotep
                                                    (aref1 'done-nodes-array done-nodes-array test))))
                                (if (not test-done)
                                    ;;will reanalyze the BVIF node once the test is evaluated:
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                            test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                                  ;;we know the result of the test, so handle the relevant branch
                                  (let* ((test-val (if test-quotep
                                                       (unquote test)
                                                     (aref1 test-case-array-name test-case-array test)))
                                         (relevant-branch (if test-val (third dargs) (fourth dargs)))
                                         (quotep-relevant-branch (consp relevant-branch))
                                         (relevant-branch-done (or quotep-relevant-branch
                                                                   (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                    (if (not relevant-branch-done)
                                        ;;will reanalyze the BVIF node once the relevant branch is evaluated:
                                        (evaluate-test-case-aux (+ -1 count)
                                                                (cons relevant-branch nodenum-worklist) dag-array-name
                                                                dag-array dag-len test-case test-case-array done-nodes-array
                                                                interpreted-function-alist test-case-array-name)
                                      ;; if the relevant branch has been computed, the value of the BVIF is just that branch,
                                      ;; except that we have to bvchop it
                                      (let* ((size-not-done (let ((size (first dargs)))
                                                              (not (or (consp size)
                                                                       (aref1 'done-nodes-array done-nodes-array size))))))
                                        (if size-not-done
                                            ;;will reanalyze the BVIF node once the size arg. is evaluated: ; TODO: Handle the size and the test together
                                            (evaluate-test-case-aux (+ -1 count)
                                                                    (cons (first dargs) nodenum-worklist) dag-array-name
                                                                    dag-array dag-len test-case test-case-array done-nodes-array
                                                                    interpreted-function-alist test-case-array-name)
                                          (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                            (unquote relevant-branch)
                                                                          (aref1 test-case-array-name test-case-array relevant-branch)))
                                                 (value (bvchop (nfix ; justified by bvchop-of-nfix
                                                                 (let ((size (first dargs)))
                                                                   (if (consp size)
                                                                       (unquote size)
                                                                     (aref1 test-case-array-name test-case-array size))))
                                                                (ifix ; justified by bvchop-of-ifix
                                                                 relevant-branch-value))))
                                            (evaluate-test-case-aux (+ -1 count)
                                                                    (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                                    (aset1 test-case-array-name test-case-array nodenum value)
                                                                    (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                                    interpreted-function-alist test-case-array-name)))))))))
                          ;;regular function call:
                          (mv-let (nodenum-worklist worklist-extendedp)
                            (add-args-not-done dargs done-nodes-array nodenum-worklist nil)
                            (if worklist-extendedp
                                ;;will reanalyze this node once the args are done:
                                (evaluate-test-case-aux (+ -1 count)
                                                        nodenum-worklist ;has been extended
                                                        dag-array-name dag-array dag-len test-case test-case-array
                                                        done-nodes-array interpreted-function-alist test-case-array-name)
                              ;;the args are done, so call the function:
                              (b* ((arg-values (get-vals-of-args dargs test-case-array-name test-case-array))
                                   (value (apply-axe-evaluator fn arg-values interpreted-function-alist 0))
                                   ;; ((mv erp value) (apply-axe-evaluator-basic fn arg-values interpreted-function-alist 1000000000))
                                   ;; ((when erp) (er hard? 'evaluate-test-case-aux "Error (~x0) evaluating: ~x1" erp expr)
                                   ;;  (mv test-case-array done-nodes-array))
                                   )
                                (evaluate-test-case-aux (+ -1 count)
                                                        (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        (aset1 test-case-array-name test-case-array nodenum value)
                                                        (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                        interpreted-function-alist
                                                        test-case-array-name)))))))))))))))))

(verify-guards evaluate-test-case-aux
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp)))))

(local
 (defthm array1p-of-mv-nth-0-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 test-case-array-name test-case-array) dag-len)
                 ;;(array1p 'done-nodes-array done-nodes-array)
                 ;;(symbol-alistp test-case)
                 ;;(interpreted-function-alistp interpreted-function-alist)
                 )
            (array1p test-case-array-name
                     (mv-nth 0 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name))))
   :hints (("Goal"
            :expand ((:free (dag-len) (EVALUATE-TEST-CASE-AUX count NODENUM-WORKLIST
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME))
                     (:free (dag-len) (EVALUATE-TEST-CASE-AUX count nil
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp USE-ALL-RATIONALP-FOR-CAR
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm alen1-of-mv-nth-0-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 test-case-array-name test-case-array) dag-len)
                 ;;(array1p 'done-nodes-array done-nodes-array)
                 ;;(symbol-alistp test-case)
                 ;;(interpreted-function-alistp interpreted-function-alist)
                 )
            (equal (alen1 test-case-array-name (mv-nth 0 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
                   (alen1 test-case-array-name test-case-array)))
   :hints (("Goal"
            :expand ((:free (dag-len) (EVALUATE-TEST-CASE-AUX count NODENUM-WORKLIST
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME))
                     (:free (dag-len) (EVALUATE-TEST-CASE-AUX count nil
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp USE-ALL-RATIONALP-FOR-CAR
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm array1p-of-mv-nth-1-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
          ;(array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                 (array1p 'done-nodes-array done-nodes-array)
                 ;;(symbol-alistp test-case)
                 ;;(interpreted-function-alistp interpreted-function-alist)
                 )
            (array1p 'done-nodes-array
                     (mv-nth 1 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name))))
   :hints (("Goal"
            :expand ((:free (dag-len) (EVALUATE-TEST-CASE-AUX count NODENUM-WORKLIST
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME))
                     (:free (dag-len) (EVALUATE-TEST-CASE-AUX count nil
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp USE-ALL-RATIONALP-FOR-CAR
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm alen1-of-mv-nth-1-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
          ;(array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                 (array1p 'done-nodes-array done-nodes-array)
                 ;;(symbol-alistp test-case)
                 ;;(interpreted-function-alistp interpreted-function-alist)
                 )
            (equal (alen1 'done-nodes-array (mv-nth 1 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
                   (alen1 'done-nodes-array done-nodes-array)))
   :hints (("Goal"
            :induct t
            :expand ((:free (dag-len) (EVALUATE-TEST-CASE-AUX count NODENUM-WORKLIST
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME))
                     (:free (dag-len) (EVALUATE-TEST-CASE-AUX count nil
                                                              DAG-ARRAY-NAME DAG-ARRAY
                                                              dag-len
                                                              TEST-CASE
                                                              TEST-CASE-ARRAY DONE-NODES-ARRAY
                                                              INTERPRETED-FUNCTION-ALIST
                                                              TEST-CASE-ARRAY-NAME)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp USE-ALL-RATIONALP-FOR-CAR
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns test-case-array, which has the name test-case-array-name.
;;ffixme use a separate array?
;;todo: this seems inefficient for very sparse tests.
(defund tag-not-done-nodes-as-unused (current-nodenum done-nodes-array test-case-array test-case-array-name)
  (declare (xargs :guard (and (integerp current-nodenum)
                              (array1p test-case-array-name test-case-array)
                              (array1p 'done-nodes-array done-nodes-array)
                              (< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                              (< current-nodenum (alen1 test-case-array-name test-case-array)))
                  :measure (nfix (+ 1 current-nodenum))))
  (if (not (natp current-nodenum))
      test-case-array
    (let* ((donep (aref1 'done-nodes-array done-nodes-array current-nodenum)))
      (if donep
          (tag-not-done-nodes-as-unused (+ -1 current-nodenum) done-nodes-array test-case-array test-case-array-name)
        (tag-not-done-nodes-as-unused (+ -1 current-nodenum) done-nodes-array
                                      (aset1-safe test-case-array-name test-case-array current-nodenum :unused)
                                      test-case-array-name)))))

(local
 (defthm array1p-of-tag-not-done-nodes-as-unused
   (implies (and (integerp current-nodenum)
                 (array1p test-case-array-name test-case-array)
                 ;(array1p 'done-nodes-array done-nodes-array)
                 ;(< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                 (< current-nodenum (alen1 test-case-array-name test-case-array)))
            (array1p test-case-array-name (tag-not-done-nodes-as-unused current-nodenum done-nodes-array test-case-array test-case-array-name)))
   :hints (("Goal" :in-theory (enable tag-not-done-nodes-as-unused)))))

(local
 (defthm alen1-of-tag-not-done-nodes-as-unused
   (implies (and ;(integerp current-nodenum)
                 ;(array1p test-case-array-name test-case-array)
                 ;(array1p 'done-nodes-array done-nodes-array)
                 ;(< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                 (< current-nodenum (alen1 test-case-array-name test-case-array))
                 )
            (equal (alen1 test-case-array-name (tag-not-done-nodes-as-unused current-nodenum done-nodes-array test-case-array test-case-array-name))
                   (alen1 test-case-array-name test-case-array)))
   :hints (("Goal" :in-theory (enable tag-not-done-nodes-as-unused)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns TEST-CASE-ARRAY, which has the name TEST-CASE-ARRAY-NAME and which has values for each node that supports any node in NODES-TO-EVAL for this test case (different test cases may evaluate the ifs differently)
; TEST-CASE-ARRAY will associate irrelevant nodes with the value :unused - FFIXME what if a node actually evaluates to :unused?  could return done-nodes-array (but if we are keeping several done-node-arrays we might want to give them different names paralleling the test case array names)
;; todo: count and print the number of nodes that are not :unused
(defund evaluate-test-case (nodes-to-eval ; we'll find values for all of these nodes
                            dag-array-name dag-array
                            test-case
                            interpreted-function-alist
                            test-case-array-name)
  (declare (xargs :guard (and (nat-listp nodes-to-eval)
                              (consp nodes-to-eval) ; must be at least one node, so we can find the max
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                              (test-casep test-case)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbolp test-case-array-name))))
  (let* ((max-nodenum (maxelem nodes-to-eval))
         (dag-len (+ 1 max-nodenum)) ; the effective length of the dag, for the purposes of this test case
         ;;would it be faster to reuse this array and just clear it out here?
         (test-case-array (make-empty-array test-case-array-name dag-len))
         ;;would it be faster to reuse this array and just clear it out here?
         (done-nodes-array (make-empty-array 'done-nodes-array dag-len)))
    (mv-let (test-case-array done-nodes-array)
      (evaluate-test-case-aux 1000000000 ; todo
                              nodes-to-eval ;initial worklist
                              dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
      ;;can we avoid this step? just return the done-nodes-array?
      (tag-not-done-nodes-as-unused max-nodenum done-nodes-array test-case-array test-case-array-name))))

(local
 (defthm array1p-of-evaluate-test-case
   (implies (and (nat-listp nodes-to-eval)
                 (consp nodes-to-eval) ; must be at least one node, so we can find the max
                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                 (test-casep test-case)
                 (interpreted-function-alistp interpreted-function-alist)
                 (symbolp test-case-array-name))
            (array1p test-case-array-name (evaluate-test-case nodes-to-eval dag-array-name dag-array test-case interpreted-function-alist test-case-array-name)))
   :hints (("Goal" :in-theory (enable evaluate-test-case)))))

(local
 (defthm alen1-of-evaluate-test-case
   (implies (and (nat-listp nodes-to-eval)
                 (consp nodes-to-eval) ; must be at least one node, so we can find the max
                 (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                 (symbolp test-case-array-name)
                 )
            (equal (alen1 test-case-array-name (evaluate-test-case nodes-to-eval dag-array-name dag-array test-case interpreted-function-alist test-case-array-name))
                   (+ 1 (maxelem nodes-to-eval))))
   :hints (("Goal" :in-theory (enable evaluate-test-case)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If the test passed (top node evaluated to T), returns TEST-CASE-ARRAY, which has a value for each node that supports the top node for this test (and :unused for other nodes) and which has name TEST-CASE-ARRAY-NAME.  If the test failed, returns nil.
(defund evaluate-and-check-test-case (test-case
                                      dag-array-name dag-array dag-len
                                      interpreted-function-alist
                                      test-case-array-name
                                      debug-nodes ; call these debug nodes?  this notion of tracing is differenct from the tracing we do for rec-fns
                                      )
  (declare (xargs :guard (and (test-casep test-case)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbolp test-case-array-name)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes dag-len))))
  (let* ((top-nodenum (+ -1 dag-len))
         (test-case-array
          (evaluate-test-case (list top-nodenum)
                              dag-array-name dag-array
                              test-case
                              interpreted-function-alist
                              test-case-array-name))
         (top-node-value (aref1 test-case-array-name test-case-array top-nodenum)))
    (if (eq t top-node-value) ; TODO: Consider relaxing this to allow any non-nil value.
        (prog2$ (print-vals-of-nodes debug-nodes test-case-array-name test-case-array)
                test-case-array)
      ;;fixme return an error flag and catch it later?
      (progn$ (cw "!!!! We found a test case that does not evaluate to true:~%")
              (cw "Test case: ~x0~%" test-case)
              (print-array2 test-case-array-name test-case-array dag-len) ;this can be big!
              (er hard? 'evaluate-and-check-test-case "Untrue test case (see above)")))))

(local
 (defthm array1p-of-evaluate-and-check-test-case
   (implies (and (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes) ; no error
                 (test-casep test-case)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (< 0 dag-len)
                 (interpreted-function-alistp interpreted-function-alist)
                 (symbolp test-case-array-name)
                 (nat-listp debug-nodes)
                 (all-< debug-nodes dag-len))
            (array1p test-case-array-name (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes)))
   :hints (("Goal" :in-theory (enable evaluate-and-check-test-case)))))

(local
 (defthm alen1-of-evaluate-and-check-test-case
   (implies (and (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes) ; no error
                 (test-casep test-case)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (< 0 dag-len)
                 (interpreted-function-alistp interpreted-function-alist)
                 (symbolp test-case-array-name)
                 (nat-listp debug-nodes)
                 (all-< debug-nodes dag-len))
            (equal (alen1 test-case-array-name (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes))
                   dag-len))
   :hints (("Goal" :in-theory (enable evaluate-and-check-test-case)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-val-other-than (val nodenums test-case-array test-case-array-name)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p test-case-array-name test-case-array)
                              (all-< nodenums (alen1 test-case-array-name test-case-array)))))
  (if (endp nodenums)
      nil ;failed to find such a val
    (let* ((nodenum (first nodenums))
           (val2 (aref1 test-case-array-name test-case-array nodenum)))
      (if (equal val val2)
          ;;keep looking:
          (find-val-other-than val (cdr nodenums) test-case-array test-case-array-name)
        ;;we found a difference:
        t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns an alist pairing values with nodenum lists
;the alist may include shadowed pairs
;fixme think about :unused nodes
(defund test-case-alist-for-set (set test-case-array-name test-case-array acc)
  (declare (xargs :guard (and (nat-listp set)
                              (array1p test-case-array-name test-case-array)
                              (all-< set (alen1 test-case-array-name test-case-array))
                              (alistp acc))))
  (if (endp set)
      acc
    (let* ((nodenum (first set))
           (value (aref1 test-case-array-name test-case-array nodenum))
           (nodes-for-value (lookup-equal value acc)))
      (test-case-alist-for-set (cdr set) test-case-array-name test-case-array
                               (acons-fast value (cons nodenum nodes-for-value) acc)))))

(local
 (defthm alistp-of-test-case-alist-for-set
   (implies (alistp acc)
            (alistp (test-case-alist-for-set set test-case-array-name test-case-array acc)))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

(local
 (defthm all-consp-of-strip-cdrs-of-test-case-alist-for-set
   (implies (all-consp (strip-cdrs acc))
            (all-consp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

(local
 (defthm all-all-<-of-strip-cdrs-of-test-case-alist-for-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (alistp acc)
                 (all-all-< (strip-cdrs acc) bound)
                 (<= (alen1 test-case-array-name test-case-array) bound))
            (all-all-< (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc)) bound))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set all-all-<)))))

(local
 (defthm nat-list-listp-of-strip-cdrs-of-test-case-alist-for-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (alistp acc)
                 (NAT-LIST-LISTP (STRIP-CDRS ACC)))
            (nat-list-listp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
   :hints (("Goal" :in-theory (enable test-case-alist-for-set nat-list-listp)))))

;; Returns (mv non-singletons singleton-count).
(defund drop-and-count-singletons (lst non-singletons-acc count-acc)
  (declare (xargs :guard (and (integerp count-acc)
                              (true-listp lst))))
  (if (endp lst)
      (mv non-singletons-acc count-acc)
    (let* ((item (car lst)))
      (if (and (consp item) ; drop if all are known to be non empty lists?
               (not (consp (cdr item))))
          ;; it's a singleton, so drop it and count it:
          (drop-and-count-singletons (cdr lst) non-singletons-acc (+ 1 count-acc))
        ;; it's not a singleton, so keep it:
        (drop-and-count-singletons (cdr lst) (cons item non-singletons-acc) count-acc)))))

(local
 (defthm true-listp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (true-listp acc)
            (true-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (nat-list-listp acc)
                 (nat-list-listp lst))
            (nat-list-listp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp)))))

(local
 (defthm all-consp-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (all-consp acc)
                 (all-consp lst)
                 )
            (all-consp (mv-nth 0 (drop-and-count-singletons lst acc count-acc))))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-drop-and-count-singletons
   (implies (and (all-all-< acc bound)
                 (all-all-< lst bound)
                 )
            (all-all-< (mv-nth 0 (drop-and-count-singletons lst acc count-acc))
                       bound))
   :hints (("Goal" :in-theory (enable drop-and-count-singletons
                                      nat-list-listp
                                      all-all-<)))))

(local
 (defthm natp-mv-nth-1-of-drop-and-count-singletons
   (implies (natp count-acc)
            (natp (mv-nth 1 (drop-and-count-singletons lst acc count-acc))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable drop-and-count-singletons)))))

;ignores later pairs that bind already-bound keys
(defund strip-cdrs-unique (lst keys-seen acc)
  (declare (xargs :guard (and (alistp lst)
                              (true-listp keys-seen))))
  (if (endp lst)
      acc ;we don't bother to reverse this
    (let* ((entry (car lst))
           (key (car entry)))
      (if (member-equal key keys-seen)
          (strip-cdrs-unique (cdr lst) keys-seen acc)
        (strip-cdrs-unique (cdr lst) (cons key keys-seen) (cons (cdr entry) acc))))))

(local
 (defthm true-listp-of-strip-cdrs-unique
   (implies (true-listp acc)
            (true-listp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique)))))

(local
 (defthm nat-list-listp-of-strip-cdrs-unique
   (implies (and (nat-list-listp acc)
                 (nat-list-listp (strip-cdrs lst)))
            (nat-list-listp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

(local
 (defthm all-consp-of-strip-cdrs-unique
   (implies (and (all-consp acc)
                 (all-consp (strip-cdrs lst)))
            (all-consp (strip-cdrs-unique lst keys-seen acc)))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp)))))

(local
 (defthm all-all-<-of-strip-cdrs-unique
   (implies (and (all-all-< acc bound)
                 (all-all-< (strip-cdrs lst) bound))
            (all-all-< (strip-cdrs-unique lst keys-seen acc) bound))
   :hints (("Goal" :in-theory (enable strip-cdrs-unique nat-list-listp all-all-<)))))

;;we first make an alist whose keys are data values (often 0 or 1?) and whose vals are sets of nodenums
;returns (mv new-sets new-singleton-count)
(defund split-set (set test-case-array test-case-array-name)
  (declare (xargs :guard (and (nat-listp set)
                              (array1p test-case-array-name test-case-array)
                              (all-< set (alen1 test-case-array-name test-case-array)))))
  (let* ((alist (test-case-alist-for-set set test-case-array-name test-case-array nil)) ;this could be slow?  better to pair nodenums with vals and merge-sort the pairs by value?
         (new-node-sets (strip-cdrs-unique alist nil nil)) ;don't cons this up?
         )
    ;;fixme combine this with the work above:
    (drop-and-count-singletons new-node-sets nil 0)))

(local
 (defthm true-listp-of-mv-nth-0-of-split-set
   (true-listp (mv-nth 0 (split-set set test-case-array test-case-array-name)))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array)))
            (nat-list-listp (mv-nth 0 (split-set set test-case-array test-case-array-name))))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm all-consp-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array)))
            (all-consp (mv-nth 0 (split-set set test-case-array test-case-array-name))))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-split-set
   (implies (and (nat-listp set)
                 (array1p test-case-array-name test-case-array)
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (<= (alen1 test-case-array-name test-case-array) bound))
            (all-all-< (mv-nth 0 (split-set set test-case-array test-case-array-name))
                       bound))
   :hints (("Goal" :in-theory (enable split-set)))))

(local
 (defthm natp-of-mv-nth-1-of-split-set
   (natp (mv-nth 1 (split-set set test-case-array test-case-array-name)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-set)))))

;takes a set and adds zero or more sets to acc (also returns a new singleton count)
;returns (mv acc new-singleton-count change-flg)
;set should have at least two elements
;should not return singletons or empty sets
;most of the time, this won't be able to distinguish any nodes and so will return (list set) - we try to make that case fast (don't recons the whole set)...
;inline this?
(defund try-to-split-set (set test-case-array-name test-case-array print acc)
  (declare (xargs :guard (and (nat-listp set)
                              (consp set)
                              (array1p test-case-array-name test-case-array)
                              ;; print
                              (all-< set (alen1 test-case-array-name test-case-array))
                              (true-listp acc))))
  (let* ((first-nodenum (first set))
         (first-val (aref1 test-case-array-name test-case-array first-nodenum))
         (need-to-splitp (find-val-other-than first-val (rest set) test-case-array test-case-array-name)))
    (if (not need-to-splitp)
        ;;in this case we don't recons the whole set
        (mv (cons set acc) 0 nil) ;fixme try to save even this cons?
      (prog2$ (and print (cw "~% (Splitting a set of ~x0 nodes.)" (len set)))
              (mv-let (new-sets new-singleton-count)
                      (split-set set test-case-array test-case-array-name) ;fixme pass acc into this?
                      (mv (append new-sets acc)
                          new-singleton-count t))))))

(local
 (defthm true-listp-of-mv-nth-0-of-try-to-split-set
   (implies (true-listp acc)
            (true-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (consp set)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc))
            (nat-list-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all-consp-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (consp set)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-consp acc))
            (all-consp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (all-< set bound)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-all-< acc bound)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-all-< (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))
                       bound))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm natp-of-mv-nth-1-of-try-to-split-set
   (natp (mv-nth 1 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm booleanp-of-mv-nth-2-of-try-to-split-set
   (booleanp (mv-nth 2 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))



;try to split the sets using test-case-array
;returns (mv new-sets new-singleton-count changep)
;sets are moved from SETS to ACC.  as they are moved they are split if indicated by this test case.
;sets are lists of nodenums.  each set has length at least 2 (singleton sets are dropped).
(defund new-probably-equal-node-sets (sets test-case-array acc singleton-count-acc print test-case-array-name changep)
  (declare (xargs :guard (and (nat-list-listp sets)
                              (all-consp sets)
                              (array1p test-case-array-name test-case-array)
                              (true-listp acc)
                              (natp singleton-count-acc)
                              ;; print
                              (all-all-< sets (alen1 test-case-array-name test-case-array))
                              (booleanp changep))
                  :guard-hints (("Goal" :in-theory (enable all-all-<)))))
  (if (endp sets)
      (mv acc singleton-count-acc changep)
    (let* ((set (first sets)))
      (mv-let (acc ;has the new sets appended onto it
               new-singleton-count change-flg-for-this-set)
              (try-to-split-set set test-case-array-name test-case-array print acc)
              (new-probably-equal-node-sets (rest sets)
                                            test-case-array
                                            acc
                                            (+ singleton-count-acc new-singleton-count)
                                            print
                                            test-case-array-name
                                            (or changep change-flg-for-this-set))))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-new-probably-equal-node-sets
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
          ;                (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (nat-list-listp (mv-nth 0 (new-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :hints (("Goal" :in-theory (enable new-probably-equal-node-sets all-all-<)))))

(local
 (defthm all-consp-of-mv-nth-0-of-new-probably-equal-node-sets
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
                 (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (all-consp (mv-nth 0 (new-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :hints (("Goal" :in-theory (enable new-probably-equal-node-sets all-all-<)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-new-probably-equal-node-sets
   (implies (and (<= (alen1 test-case-array-name test-case-array) dag-len)
                 (nat-list-listp sets)
                 (nat-list-listp acc)
                 (all-consp acc)
                 (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 (ALL-ALL-< ACC DAG-LEN)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (all-all-< (mv-nth 0 (new-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))
                       dag-len))
   :hints (("Goal" :in-theory (enable new-probably-equal-node-sets all-all-<)))))

(local
 (defthm natp-of-mv-nth-1-of-new-probably-equal-node-sets
   (implies (natp singleton-count-acc)
            (natp (mv-nth 1 (new-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable new-probably-equal-node-sets)))))

(local
 (defthm booleanp-of-mv-nth-2-of-new-probably-equal-node-sets
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (new-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable new-probably-equal-node-sets)))))



;; Looks for an initial segment of NODE-TO-VALUE-ALIST all of whose vals are SIG.
;; Returns (mv entries-with-value remaining-node-to-value-alist).
(defund find-entries-with-value (node-to-value-alist value acc)
  (declare (xargs :guard (and (alistp node-to-value-alist)
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-listp acc))))
  (if (endp node-to-value-alist)
      (mv acc node-to-value-alist)
    (let* ((entry (car node-to-value-alist))
           (nodenum (car entry))
           (value2 (cdr entry)))
      (if (equal value value2)
          (find-entries-with-value (cdr node-to-value-alist) value (cons nodenum acc))
        ;; stop looking, since the entries are sorted by value and we found a difference:
        (mv acc node-to-value-alist)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-find-entries-with-value
   (implies (and (nat-listp (strip-cars node-to-value-alist))
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (find-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

(local
 (defthm all-<-of-mv-nth-0-of-find-entries-with-value
   (implies (and (all-< (strip-cars node-to-value-alist) bound)
                 (all-< acc bound)
                 )
            (all-< (mv-nth 0 (find-entries-with-value node-to-value-alist value acc)) bound))
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-find-entries-with-value
   (<= (len (mv-nth 1 (find-entries-with-value node-to-value-alist value acc)))
       (len node-to-value-alist))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-find-entries-with-value
   (implies (nat-listp (strip-cars node-to-value-alist))
            (nat-listp (strip-cars (mv-nth 1 (find-entries-with-value node-to-value-alist value acc)))))
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

(local
 (defthm alistp-of-strip-cars-of-mv-nth-1-of-find-entries-with-value
   (implies (alistp node-to-value-alist)
            (alistp (mv-nth 1 (find-entries-with-value node-to-value-alist value acc))))
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-find-entries-with-value
   (implies (and (all-< (strip-cars node-to-value-alist) bound)
                 (all-< acc bound)
                 )
            (all-< (strip-cars (mv-nth 1 (find-entries-with-value node-to-value-alist value acc))) bound))
   :hints (("Goal" :in-theory (enable find-entries-with-value)))))

;; Returns (mv sets singleton-count).
(defund group-same-entries (node-to-value-alist acc singleton-count)
  (declare (xargs :guard (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                              (nat-listp (strip-cars node-to-value-alist))
                              (nat-list-listp acc)
                              (natp singleton-count))
                  :measure (len node-to-value-alist)))
  (if (atom node-to-value-alist)
      (mv acc singleton-count)
    (let* ((entry (car node-to-value-alist))
           (nodenum (car entry))
           (value (cdr entry)))
      (mv-let (equiv-set node-to-value-alist)
        (find-entries-with-value (cdr node-to-value-alist) value nil)
        (if equiv-set ; there's at least one other node with the same value
            (group-same-entries node-to-value-alist (cons (cons nodenum equiv-set) acc) singleton-count)
          (group-same-entries node-to-value-alist acc (+ 1 singleton-count)))))))

(local
 (defthm all-all-<-of-mv-nth-0-of-group-same-entries
   (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                 (nat-listp (strip-cars node-to-value-alist))
                 (all-< (strip-cars node-to-value-alist) bound)
                 (nat-list-listp acc)
                 (all-all-< acc bound)
                 (natp singleton-count))
            (all-all-< (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count)) bound))
   :hints (("Goal" :in-theory (enable group-same-entries)))))

(local
 (defthm all-consp-of-mv-nth-0-of-group-same-entries
   (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                 (nat-listp (strip-cars node-to-value-alist))
                 (nat-list-listp acc)
                 (all-consp acc)
                 (natp singleton-count))
            (all-consp (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count))))
   :hints (("Goal" :in-theory (enable group-same-entries)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-group-same-entries
   (implies (and (alistp node-to-value-alist) ; should be sorted, or at least grouped, by the values of its key/value pairs
                 (nat-listp (strip-cars node-to-value-alist))
                 (nat-list-listp acc)
                 (all-consp acc)
                 (natp singleton-count))
            (nat-list-listp (mv-nth 0 (group-same-entries node-to-value-alist acc singleton-count))))
   :hints (("Goal" :in-theory (enable group-same-entries)))))

(local
 (defthm natp-of-mv-nth-1-of-group-same-entries
   (implies (natp singleton-count)
            (natp (mv-nth 1 (group-same-entries node-to-value-alist acc singleton-count))))
   :hints (("Goal" :in-theory (enable group-same-entries)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Handles nodes that are used on this test case but have not been used on a previous test case.
;Such nodes are moved from the never-used-nodes list to the probably-constant-node-alist, where they are paired with their value on this test case.
;Returns (mv never-used-nodes probably-constant-node-alist changep) where changep remains true if it was initially true.
;fixme might be faster to process more than 1 test case at a time
(defund handle-newly-used-nodes (never-used-nodes ;these are moved to acc or get entries in the alist
                                 probably-constant-node-alist ;;pairs nodenums with probable constants
                                 test-case-array-name test-case-array
                                 acc
                                 changep)
  (declare (xargs :guard (and (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist)
                              (array1p test-case-array-name test-case-array)
                              (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp never-used-nodes)
      (mv acc probably-constant-node-alist changep)
    (let* ((nodenum (first never-used-nodes))
           (value (aref1 test-case-array-name test-case-array nodenum)))
      (if (eq :unused value)
          ;; the node is still unused:
          (handle-newly-used-nodes (rest never-used-nodes)
                                   probably-constant-node-alist
                                   test-case-array-name test-case-array
                                   (cons nodenum acc)
                                   changep)
        ;;the node is used for the first time on this test case:
        (handle-newly-used-nodes (rest never-used-nodes)
                                 (acons-fast nodenum value probably-constant-node-alist)
                                 test-case-array-name test-case-array
                                 acc
                                 t)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (array1p test-case-array-name test-case-array)
                 (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                 (all-< never-used-nodes dag-len)
                 (all-< acc dag-len)
                 (booleanp changep))
            (all-< (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))
                   dag-len))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm alistp-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (alistp probably-constant-node-alist)
            (alistp (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp (strip-cars probably-constant-node-alist)))
            (nat-listp (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (all-< never-used-nodes bound)
                 (all-< (strip-cars probably-constant-node-alist) bound))
            (all-< (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm booleanp-of-mv-nth-2-of-handle-newly-used-nodes
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this function drops any pairs which are invalidated by the current test case
;this rebuilds the whole alist - hope that is okay...
;returns (mv probably-constant-node-alist changep)
;fixme might be faster to process more than 1 test case at a time
;every node in probably-constant-node-alist has been used on at least one test case
(defund new-probably-constant-alist (probably-constant-node-alist ;;pairs nodenums with probable constants
                                     test-case-array-name test-case-array
                                     acc ;pairs are moved from probably-constant-node-alist to this
                                     changep)
  (declare (xargs :guard (and (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (array1p test-case-array-name test-case-array)
                              (all-< (strip-cars probably-constant-node-alist)
                                     (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp probably-constant-node-alist)
      (mv acc changep)
    (let* ((pair (first probably-constant-node-alist))
           (nodenum (car pair))
           (probable-value (cdr pair))
           (value-for-this-test-case (aref1 test-case-array-name test-case-array nodenum)))
      (if (or (eq :unused value-for-this-test-case)
              (equal probable-value value-for-this-test-case))
          ;; this test case doesn't invalidate the pair:
          (new-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                       (cons pair acc) changep)
        ;; the node is used and the value is different from the value in the alist, so drop the pair:
        (new-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                     acc t)))))

(local
 (defthm alistp-of-mv-nth-0-of-new-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (alistp (mv-nth 0 (new-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable new-probably-constant-alist)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-0-of-new-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (booleanp changep))
            (nat-listp (strip-cars (mv-nth 0 (new-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable new-probably-constant-alist)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-0-of-new-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (ALL-< (STRIP-CARS ACC) BOUND)
                 (booleanp changep)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-< (strip-cars (mv-nth 0 (new-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable new-probably-constant-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run test cases and use them to split probably-equal-node-sets and eliminate probable constants
;; returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist), where test-case-array-alist is valid iff keep-test-casesp is non-nil
;ffixme think about what to do with nodes that are unreachable (don't influence the top node, because of ifs) on a single test case, or on all test cases.  maybe i now handle that?
;now the tests come in randomized?
(defund update-probable-facts-with-test-cases (test-cases
                                               singleton-count
                                               dag-array-name dag-array dag-len
                                               probably-equal-node-sets
                                               never-used-nodes
                                               probably-constant-node-alist
                                               interpreted-function-alist print
                                               test-case-array-name-base
                                               keep-test-casesp
                                               test-case-array-alist
                                               test-case-number
                                               debug-nodes
                                               num-of-last-interesting-test-case)
  (declare (xargs :guard (and (test-casesp test-cases)
                              (natp singleton-count)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (nat-list-listp probably-equal-node-sets)
                              (all-consp probably-equal-node-sets)
                              (all-all-< probably-equal-node-sets dag-len)
                              (nat-listp never-used-nodes)
                              (all-< never-used-nodes dag-len)
                              (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (all-< (strip-cars probably-constant-node-alist) dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                              (symbolp test-case-array-name-base)
                              (booleanp keep-test-casesp)
                              (alistp test-case-array-alist)
                              (natp test-case-number)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes dag-len)
                              (or (null num-of-last-interesting-test-case)
                                  (natp num-of-last-interesting-test-case)))
                  :guard-hints (("Goal" :in-theory (disable natp strip-cars)))))
  (if (or (endp test-cases)
          ;;stop if we've done at least 100 test cases and nothing has happened in the last 90% of them:
          ;;fixme could allow the user to change the 10 and the 100 here:
          (if (and t ;abandon-testing-when-boringp ;(or t abandon-testing-when-boringp)
                   num-of-last-interesting-test-case
                   (<= 100 test-case-number)
                   (<= (* 10 num-of-last-interesting-test-case) test-case-number))
              (prog2$ (cw "(Abandoning testing because nothing interesting is happening.)")
                      t)
            nil))
      (mv t ; all tests passed
          probably-equal-node-sets never-used-nodes probably-constant-node-alist
          (reverse test-case-array-alist) ;new; keeps this in sync with the test cases (or do non-interesting ones get dropped?)
          )
    (b* ((- ;;TODO: Only print when things change?:
          (cw "(Test ~x0 (~x1 total sets, ~x2 singletons, ~x3 constants)"
              test-case-number
              (+ singleton-count (len probably-equal-node-sets)) ;slow? could keep a count?
              singleton-count
              (len probably-constant-node-alist) ;slow?
              ))
         (test-case (first test-cases))
         (test-case-array-name (if keep-test-casesp
                                   (pack$ test-case-array-name-base '- (nat-to-string test-case-number))
                                 ;;if we are not keeping test cases (e.g., because they'd take too much memory), reuse the same array:
                                 test-case-array-name-base))
         ;; Evaluate the test case and ensure the top node is true:
         (test-case-array
          (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist
                                        test-case-array-name
                                        debug-nodes))
         ((when (not test-case-array)) ; some test failed! (rare)
          (mv nil probably-equal-node-sets never-used-nodes probably-constant-node-alist nil))
         (changep nil)
         ;; Update the probably-equal-node-sets:
         ((mv new-sets new-singleton-count changep)
          (new-probably-equal-node-sets probably-equal-node-sets test-case-array nil 0 print test-case-array-name changep))
         ;; Handle nodes that are used for the first time on this test case (they become probable constants):
         ((mv never-used-nodes probably-constant-node-alist changep)
          (handle-newly-used-nodes never-used-nodes
                                   probably-constant-node-alist
                                   test-case-array-name
                                   test-case-array
                                   nil
                                   changep))
         ;; Update the probable constants (TODO: Do this before handle-newly-used-nodes):
         ((mv probably-constant-node-alist changep)
          (new-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array nil changep))
         (- (if (and (or (eq print :verbose)
                         (eq print :verbose!))
                     changep) ; todo: use this value to decide whether to keep the test case? maybe keep the first few boring ones so we have enough..
                (cw "~%interesting test case ~x0.)~%" test-case)
              (cw ")~%"))))
      (update-probable-facts-with-test-cases (rest test-cases)
                                             (+ singleton-count new-singleton-count)
                                             dag-array-name dag-array dag-len
                                             new-sets
                                             never-used-nodes
                                             probably-constant-node-alist
                                             interpreted-function-alist print test-case-array-name-base keep-test-casesp
                                             (if keep-test-casesp
                                                 (acons-fast test-case-array-name
                                                             test-case-array
                                                             test-case-array-alist)
                                               nil)
                                             (+ 1 test-case-number)
                                             debug-nodes
                                             (if changep
                                                 test-case-number
                                               num-of-last-interesting-test-case)))))

;test-case-array maps nodenums 0..(1 - dag-len) to their values for the current test case
;each pair in the resulting alist pairs a value with the list of nodenums that have that value under the current test case
;returns (mv initial-probably-equal-node-sets initial-singleton-count)
(defund initial-probably-equal-node-sets (dag-len test-case-array-name test-case-array)
  (declare (xargs :guard (and (array1p test-case-array-name test-case-array)
                              (natp dag-len)
                              (<= dag-len (alen1 test-case-array-name test-case-array)))))
  (let* ((node-to-value-alist (array-to-alist test-case-array-name test-case-array dag-len)) ; avoid this?
         (sorted-node-to-value-alist (merge-sort-lexorder-of-cdrs node-to-value-alist)) ; sorted by the values
         )
    (group-same-entries sorted-node-to-value-alist nil 0)))

(local
 (defthm all-all-<-of-mv-nth-0-of-initial-probably-equal-node-sets
   (implies (and (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 (<= dag-len bound))
            (all-all-< (mv-nth 0 (initial-probably-equal-node-sets dag-len test-case-array-name test-case-array)) bound))
   :hints (("Goal" :in-theory (enable initial-probably-equal-node-sets)))))

(local
 (defthm all-consp-of-mv-nth-0-of-initial-probably-equal-node-sets
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (all-consp (mv-nth 0 (initial-probably-equal-node-sets dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probably-equal-node-sets)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-initial-probably-equal-node-sets
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-list-listp (mv-nth 0 (initial-probably-equal-node-sets dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probably-equal-node-sets)))))

(local
 (defthm natp-of-mv-nth-1-of-initial-probably-equal-node-sets
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (natp (mv-nth 1 (initial-probably-equal-node-sets dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (e/d (initial-probably-equal-node-sets) (natp))))))


;; Returns (mv never-used-nodes probably-constant-node-alist ;pairs nodenums used on the first test case with their values
;;         )
(defund harvest-probable-constants-from-first-test-case (nodenum
                                                         miter-len
                                                         test-case-array-name test-case-array
                                                         never-used-nodes
                                                         probably-constant-node-alist)
  (declare (xargs :guard (and (natp nodenum)
                              (natp miter-len)
                              (array1p test-case-array-name test-case-array)
                              (<= miter-len (alen1 test-case-array-name test-case-array))
                              (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist))
                  :measure (nfix (+ 1 (- miter-len nodenum)))))
  (if (or (<= miter-len nodenum)
          (not (integerp miter-len))
          (not (integerp nodenum))
          )
      (mv never-used-nodes probably-constant-node-alist)
    (let* ((value (aref1 test-case-array-name test-case-array nodenum)))
      (if (eq :unused value)
          (harvest-probable-constants-from-first-test-case (+ 1 nodenum) miter-len test-case-array-name test-case-array
                                                           (cons nodenum never-used-nodes)
                                                           probably-constant-node-alist)
        (harvest-probable-constants-from-first-test-case (+ 1 nodenum) miter-len test-case-array-name test-case-array
                                                         never-used-nodes
                                                         (acons-fast nodenum value probably-constant-node-alist))))))

(local
 (defthm all-<-of-mv-nth-0-of-harvest-probable-constants-from-first-test-case
   (implies (and (natp nodenum)
                 (natp miter-len)
                 (array1p test-case-array-name test-case-array)
                 (<= miter-len (alen1 test-case-array-name test-case-array))
                 (nat-listp never-used-nodes)
                 (ALL-< NEVER-USED-NODES MITER-LEN)
                 (alistp probably-constant-node-alist))
            (all-< (mv-nth 0 (harvest-probable-constants-from-first-test-case nodenum
                                                                              miter-len
                                                                              test-case-array-name test-case-array
                                                                              never-used-nodes
                                                                              probably-constant-node-alist))
                   miter-len))
   :hints (("Goal" :in-theory (enable harvest-probable-constants-from-first-test-case)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-harvest-probable-constants-from-first-test-case
   (implies (and (natp nodenum)
                 (natp miter-len)
                 (array1p test-case-array-name test-case-array)
                 (<= miter-len (alen1 test-case-array-name test-case-array))
                 (nat-listp never-used-nodes)
                 (ALL-< NEVER-USED-NODES MITER-LEN)
                 (alistp probably-constant-node-alist))
            (nat-listp (mv-nth 0 (harvest-probable-constants-from-first-test-case nodenum
                                                                                  miter-len
                                                                                  test-case-array-name test-case-array
                                                                                  never-used-nodes
                                                                                  probably-constant-node-alist))))
   :hints (("Goal" :in-theory (enable harvest-probable-constants-from-first-test-case)))))

(local
 (defthm alistp-of-mv-nth-1-of-harvest-probable-constants-from-first-test-case
   (implies (and (natp nodenum)
                 (natp miter-len)
                 (array1p test-case-array-name test-case-array)
                 (<= miter-len (alen1 test-case-array-name test-case-array))
                 (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist))
            (alistp (mv-nth 1 (harvest-probable-constants-from-first-test-case nodenum
                                                                               miter-len
                                                                               test-case-array-name test-case-array
                                                                               never-used-nodes
                                                                               probably-constant-node-alist))))
   :hints (("Goal" :in-theory (enable harvest-probable-constants-from-first-test-case)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-harvest-probable-constants-from-first-test-case
   (implies (and (natp nodenum)
                 (natp miter-len)
                 (array1p test-case-array-name test-case-array)
                 (<= miter-len (alen1 test-case-array-name test-case-array))
                 (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (all-< (strip-cars probably-constant-node-alist) miter-len))
            (all-< (strip-cars (mv-nth 1 (harvest-probable-constants-from-first-test-case nodenum
                                                                                          miter-len
                                                                                          test-case-array-name test-case-array
                                                                                          never-used-nodes
                                                                                          probably-constant-node-alist)))
                   miter-len))
   :hints (("Goal" :in-theory (enable harvest-probable-constants-from-first-test-case)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-harvest-probable-constants-from-first-test-case
   (implies (and (natp nodenum)
                 (natp miter-len)
                 (array1p test-case-array-name test-case-array)
                 (<= miter-len (alen1 test-case-array-name test-case-array))
                 (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (all-< (strip-cars probably-constant-node-alist) miter-len)
                 (NAT-LISTP (STRIP-CARS PROBABLY-CONSTANT-NODE-ALIST)))
            (nat-listp (strip-cars (mv-nth 1 (harvest-probable-constants-from-first-test-case nodenum
                                                                                              miter-len
                                                                                              test-case-array-name test-case-array
                                                                                              never-used-nodes
                                                                                              probably-constant-node-alist)))))
   :hints (("Goal" :in-theory (enable harvest-probable-constants-from-first-test-case)))))

;repeatedly generate a test case and then use it to split possibly-equal node sets and eliminate possibly-constant nodes
;;returns (mv all-passedp
;             probably-equal-node-sets ;includes sets believed to be a constant
;             never-used-nodes
;             probably-constant-node-alist ;pairs nodes with the constants they seem to be equal to
;             test-case-array-alist ; valid iff keep-test-casesp is non-nil, pairs array names with arrays that give values to all the nodes
;        )
;todo: should this return the used test cases (I guess they can be extracted from the test-case-array-alist)?
(defund probable-facts (miter-array-name miter-array miter-len
                                         miter-depth
                                         test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
                                         interpreted-function-alist print keep-test-casesp
                                         debug-nodes)
  (declare (xargs :guard (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                              (< 0 miter-len)
                              (natp miter-depth)
                              (test-casesp test-cases)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                              (booleanp keep-test-casesp)
                              (nat-listp debug-nodes)
                              (ALL-< DEBUG-NODES MITER-LEN))
                  :guard-hints (("Goal" :in-theory (disable natp)))))
  (b* ((test-cases test-cases ;(firstn 1024 test-cases) ;Thu Feb 17 20:25:10 2011
                   )
       (- (cw "(Evaluating test cases (keep-test-casesp is ~x0):~%" keep-test-casesp))
       ;; use the first test case to make initial-probably-equal-node-sets (I think this is faster than starting with one huge set and then splitting it):
       (- (cw "(Test 0 (initial)"))
       (test-case-array-name-base (pack$ 'test-case-array-depth- miter-depth '-)) ;using the depth is new
       (first-test-case-array-name (pack$ test-case-array-name-base 0))
       (test-case-array
        (evaluate-and-check-test-case (first test-cases)
                                      miter-array-name
                                      miter-array
                                      miter-len
                                      interpreted-function-alist
                                      first-test-case-array-name
                                      debug-nodes))
       ((when (not test-case-array)) ; actually, a hard erorr will have already been thrown
        (mv nil                      ; all-passedp
            nil nil nil nil))
       ((mv initial-probably-equal-node-sets initial-singleton-count)
        (initial-probably-equal-node-sets miter-len first-test-case-array-name test-case-array))
       ((mv initial-never-used-nodes
            initial-probably-constant-node-alist ;pairs nodenums used on the first test case with their values
            )
        (harvest-probable-constants-from-first-test-case 0
                                                         miter-len
                                                         first-test-case-array-name test-case-array
                                                         nil
                                                         nil))
       ;;((array-to-alist first-test-case-array-name test-case-array miter-len)) ;slow?
       ;;save the first test case in the test-case-array-alist:
       (test-case-array-alist (if keep-test-casesp
                                  (acons-fast first-test-case-array-name test-case-array nil)
                                nil))
       (- (cw ")~%"))
       ;;use additional test cases to split the sets and update the probable constant facts:
       ((mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist)
        (update-probable-facts-with-test-cases (rest test-cases)
                                               initial-singleton-count
                                               miter-array-name
                                               miter-array
                                               miter-len
                                               initial-probably-equal-node-sets
                                               initial-never-used-nodes
                                               initial-probably-constant-node-alist
                                               interpreted-function-alist
                                               print
                                               test-case-array-name-base
                                               keep-test-casesp ;just check whether test-case-array-alist is nil?
                                               test-case-array-alist
                                               1 ;test case number
                                               debug-nodes
                                               nil ;;number of last interesting test case
                                               ))
       (- (cw ")~%")))
    (mv all-passedp
        probably-equal-node-sets
        never-used-nodes
        probably-constant-node-alist
        test-case-array-alist)))
