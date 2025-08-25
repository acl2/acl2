; DAGs, represented as lists
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

;; This books contains notions related to DAGs represented as alists.  See also
;; dag-arrays.lisp.

(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq" :dir :system)
;(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/utilities/printing" :dir :system) ;for print-list
(include-book "kestrel/acl2-arrays/bounded-nat-alists" :dir :system) ; for bounded-natp-alistp
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system) ; drop?
;(include-book "numeric-lists")
(include-book "bounded-dag-exprs")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "keep-nodenum-dargs")
;(include-book "darg-listp")
;(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/utilities/mv-nth" :dir :system))
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(in-theory (disable mv-nth)) ; so the rules in this book fire

(local (in-theory (disable symbol-alistp strip-cdrs alistp))) ;prevent inductions

(defthm all-myquotep-forward-to-all-consp
  (implies (all-myquotep x)
           (all-consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ALL-MYQUOTEP all-consp))))

;rename
(defthmd alistp-guard-hack
  (implies (and (alistp dag)
                (not (consp (nth 0 dag))))
           (not (nth 0 dag)))
  :hints (("Goal" :in-theory (enable alistp))))

(defthm dargp-less-than-of-cdr-of-assoc-equal
  (implies (and (bounded-darg-listp (strip-cdrs alist) bound)
                (assoc-equal term alist))
           (dargp-less-than (cdr (assoc-equal term alist))
                                       bound))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

;rename
(local
  (defthm acl2-numberp-of-lookup-equal
    (implies (and (nat-listp (strip-cdrs alist))
                  (lookup-equal key alist))
             (acl2-numberp (lookup-equal key alist)))
    :hints (("Goal" :in-theory (enable strip-cdrs)))))

;make local?
(defthm natp-of-lookup-equal-when-nat-listp-of-strip-cdrs
  (implies (nat-listp (strip-cdrs alist))
           (iff (natp (lookup-equal key alist))
                (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Deprecate in favor of top-nodenum-of-dag?
(defun top-nodenum (dag)
  (declare (xargs :guard (alistp dag) ;or require weak-dagp?  at least require non-empty?
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
                  ))
  (if (endp dag)
      -1
    (let* ((entry (car dag))
           (nodenum (car entry)))
      nodenum)))

;;
;; definition of DAGs
;;

;;
;; weak-dagp
;;

;; Checks that DAG is a true-list of pairs of the form (<nodenum> . <bounded-dag-expr>).
;; TODO: Disable?
(defun weak-dagp-aux (dag)
  (declare (xargs :guard t))
  (if (atom dag)
      (null dag)
    (let ((entry (car dag)))
      (and (consp entry)
           (let* ((nodenum (car entry))
                  (expr (cdr entry)))
                (and (natp nodenum)
                     (bounded-dag-exprp nodenum expr)
                     (weak-dagp-aux (cdr dag))))))))

(defthm bounded-dag-exprp-of-cdr-of-car-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (consp dag)
                (<= (car (car dag)) nodenum))
           (bounded-dag-exprp nodenum (cdr (car dag))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm dag-exprp-of-cdr-of-car-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (dag-exprp (cdr (car dag))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm symbolp-of-cdar-when-weak-dagp-aux-cheap
  (implies (and (weak-dagp-aux dag)
                (consp dag)
                (not (consp (cdr (car dag)))))
           (symbolp (cdr (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux bounded-dag-exprp))))

(defthm weak-dagp-aux-of-acons
  (equal (weak-dagp-aux (acons nodenum expr dag))
         (and (natp nodenum)
              (bounded-dag-exprp nodenum expr)
              (weak-dagp-aux dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm rational-listp-of-strip-cars-when-weak-dagp-aux-cheap
  (implies (weak-dagp-aux dag)
           (rational-listp (strip-cars dag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd integer-listp-of-strip-cars-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (integer-listp (strip-cars dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-of-cdr
  (implies (weak-dagp-aux dag)
           (weak-dagp-aux (cdr dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-forward-to-alistp
  (implies (weak-dagp-aux dag)
           (alistp dag))
  :rule-classes :forward-chaining)

(defthm weak-dagp-aux-forward-to-true-alistp
  (implies (weak-dagp-aux dag)
           (true-listp dag))
  :rule-classes :forward-chaining)

(defthm integerp-of-car-of-car-when-weak-dagp-aux-cheap
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (integerp (car (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthmd natp-of-car-of-car-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (natp (car (car dag))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

;; (defthm dargp-of-cdr-of-car-when-weak-dagp-aux
;;   (implies (and (weak-dagp-aux dag)
;;                 (consp dag))
;;            (dargp (cdr (car dag))))
;;   :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm integerp-of-car-of-car-of-last-when-weak-dagp-aux-cheap
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (integerp (car (car (last dag)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthmd acl2-numberp-of-car-of-car-of-last-when-weak-dagp-aux
  (implies (and (weak-dagp-aux rev-dag)
                (consp rev-dag))
           (acl2-numberp (car (car (last rev-dag)))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthmd consp-of-car-of-last-when-weak-dagp-aux
  (implies (and (weak-dagp-aux rev-dag)
                (consp rev-dag))
           (consp (car (last rev-dag))))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

;even holds for bad nodenums or nodenums of vars, since the cdr will return nil
(defthm true-listp-of-dargs-of-lookup-equal-when-weak-dagp-aux-cheap
  (implies (weak-dagp-aux dag)
           (true-listp (dargs (lookup-equal nodenum dag))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp dargs))))

(defthm bounded-darg-listp-of-dargs-of-lookup-equal
  (implies (and (weak-dagp-aux dag)
                (natp nodenum)
                (natp nodenum2)
                (<= nodenum nodenum2)
                (consp (lookup-equal nodenum dag))
                (not (equal (car (lookup-equal nodenum dag))
                            'quote)))
           (bounded-darg-listp (dargs (lookup-equal nodenum dag)) nodenum2))
  :hints (("Goal" :expand ((ASSOC-EQUAL NODENUM DAG)
                           (LOOKUP-EQUAL NODENUM DAG)
                           (LOOKUP-EQUAL NODENUM (CDR DAG)))
           :in-theory (enable bounded-dag-exprp
                              dag-exprp))))

(defthm dag-exprp-of-lookup-equal-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (lookup-equal n dag))
           (dag-exprp (lookup-equal n dag)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux lookup-equal))))

(defthm symbolp-of-car-of-lookup-equal-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
;                (<= nodenum-or-quotep (car (car dag)))
                ;(natp nodenum-or-quotep)
                )
           (symbolp (car (lookup-equal nodenum-or-quotep dag)))))

(defthm natp-of-maxelem-of-strip-cars-when-weak-dagp-aux
  (implies (and (weak-dagp-aux rev-dag)
                (consp rev-dag))
           (natp (maxelem (strip-cars rev-dag))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable weak-dagp-aux strip-cars))))

(defthm weak-dagp-aux-of-append
  (equal (weak-dagp-aux (append x y))
         (and (weak-dagp-aux (true-list-fix x))
              (weak-dagp-aux y)))
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

(defthm weak-dagp-aux-of-reverse-list
  (equal (weak-dagp-aux (reverse-list dag))
         (weak-dagp-aux (true-list-fix dag)))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm weak-dagp-aux-forward-to-natp-of-car-of-car
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (natp (car (car dag))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable weak-dagp-aux))))

;disable?
(defthm all-integerp-of-strip-cars-when-weak-dagp-aux
  (implies (weak-dagp-aux dag)
           (all-integerp (strip-cars dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this does enforce that children are less than the parents
;does not enforce that all the nodes come in order!
;does not enforce that child nodes exist!
;does not enforce that each node appears only once
;does not enforce that there are no gaps in the node numbering
;does not enforce that function calls in dag exprs have the right arity
(defund weak-dagp (dag)
  (declare (xargs :guard t))
  (and ;(true-listp dag)
       (consp dag) ;a dag can't be empty (but often we have items that are either dags or quoted constants)
       (weak-dagp-aux dag)))

(defthm weak-dagp-of-cdr
  (implies (weak-dagp dag)
           (equal (weak-dagp (cdr dag))
                  (consp (cdr dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;keeping this disabled for now, since it could be expensive.
(defthmd alistp-when-weak-dagp
  (implies (weak-dagp dag)
           (alistp dag)))

(defthm weak-dagp-forward-to-alistp
  (implies (weak-dagp dag)
           (alistp dag))
  :rule-classes :forward-chaining)

(defthm weak-dagp-forward-to-natp-of-car-of-car
  (implies (weak-dagp dag)
           (natp (car (car dag))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm weak-dagp-of-reverse-list
  (equal (weak-dagp (reverse-list dag))
         (weak-dagp (true-list-fix dag)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm integerp-of-car-of-car-when-weak-dagp-cheap
  (implies (and (weak-dagp dag)
                (consp dag))
           (integerp (car (car dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm true-listp-of-dargs-of-lookup-equal-when-weak-dagp-cheap
  (implies (weak-dagp dag)
           (true-listp (dargs (lookup-equal nodenum dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm bounded-darg-listp-of-dargs-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
                (natp nodenum)
                (natp nodenum2)
                (<= nodenum nodenum2)
                (consp (lookup-equal nodenum dag))
                (not (equal (car (lookup-equal nodenum dag))
                            'quote)))
           (bounded-darg-listp (dargs (lookup-equal nodenum dag)) nodenum2))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm dag-exprp-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
                (lookup-equal n dag))
           (dag-exprp (lookup-equal n dag)))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;rename
(defthm symbolp-of-car-of-lookup-equal-when-weak-dagp
  (implies (and (weak-dagp dag)
;                (<= nodenum-or-quotep (car (car dag)))
                ;(natp nodenum-or-quotep)
                )
           (symbolp (car (lookup-equal nodenum-or-quotep dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

;; Recognize a DAG or a quoted constant (often the result of rewriting a DAG)
(defun weak-dag-or-quotep (obj)
  (declare (xargs :guard t))
  (or (weak-dagp obj)
      (myquotep obj)))

;;
;; pseudo-dagp
;;

; current-nodenum should be the top nodenum of dag.  it counts down to -1, in which case the dag should be nil.
(defund pseudo-dagp-aux (dag current-nodenum)
  (declare (type (integer -1 *) current-nodenum))
  (if (< current-nodenum 0)
      (null dag)
    (and (consp dag)
         (let ((entry (first dag)))
           (and (consp entry)
                (let ((nodenum (car entry))
                      (expr (cdr entry)))
                  (and (eql nodenum current-nodenum)
                       (bounded-dag-exprp current-nodenum expr)
                       (pseudo-dagp-aux (rest dag) (+ -1 current-nodenum)))))))))

(defthm true-listp-when-pseudo-dagp-aux
  (implies (pseudo-dagp-aux dag current-nodenum)
           (true-listp dag))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm alistp-when-pseudo-dagp-aux
  (implies (pseudo-dagp-aux dag current-nodenum)
           (alistp dag))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-cdr
  (implies (and (pseudo-dagp-aux dag (+ 1 n))
                (integerp n))
           (pseudo-dagp-aux (cdr dag) n))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp-aux) (bounded-dag-exprp)))))

(defthm pseudo-dagp-aux-when-not-consp-cheap
  (implies (not (consp dag))
           (equal (pseudo-dagp-aux dag n)
                  (and (null dag)
                       (< n 0))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm bounded-dag-exprp-of-lookup-equal-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (<= n current-nodenum)
                (natp n)
                (integerp current-nodenum))
           (bounded-dag-exprp n (lookup-equal n dag)))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp-aux LOOKUP-EQUAL assoc-equal)
                                  (bounded-dag-exprp)))))

(defthm pseudo-dagp-aux-forward
  (implies (and (pseudo-dagp-aux dag n)
                (integerp n)
                (consp dag))
           (<= 0 n))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-nthcdr
  (implies (and (pseudo-dagp-aux dag (+ current-nodenum n))
                (natp n)
                (integerp current-nodenum))
           (pseudo-dagp-aux (nthcdr n dag) current-nodenum))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux nthcdr))))

(defthm car-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (natp top-nodenum))
           (equal (car (car dag))
                  top-nodenum))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm bounded-natp-alistp-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (< top-nodenum bound)
                (natp top-nodenum)
                (natp bound))
           (bounded-natp-alistp dag bound))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-natp-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that the node numbering is correct with no gaps and that nodes only
;; refer to smaller nodes.  Does not check that the arities of the functions
;; are correct (so this is kind of like pseudo-termp).  This is not a good
;; function to use as a guard when recurring down dags because you want to go
;; until nil is reached, but nil is not a pseudo-dag.  Instead, see
;; pseudo-dagp-aux (or weak-dagp-aux).
(defund pseudo-dagp (dag)
  (declare (xargs :guard t))
  (and (consp dag) ;a dag can't be empty (but often we have items that are either dags or quoted constants)
       (let ((first-entry (first dag)))
         (and (consp first-entry)
              (let ((top-nodenum (car first-entry)))
                (and (natp top-nodenum) ; we check this here but avoid checking natp for every nodenum in pseudo-dagp-aux as we decrement
                     (pseudo-dagp-aux dag top-nodenum)))))))

;; So we can always tell which we have:
;; In fact, even an untranslated term cannot be a dag (consider its car).
(thm
  (not (and (pseudo-dagp x)
            (pseudo-termp x)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

;keeping this disabled for now, since it could be expensive.
(defthmd alistp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (alistp dag))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

;keeping this disabled for now, since it could be expensive.
(defthmd consp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (consp dag))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

;keeping this disabled for now, since it could be expensive.
(defthmd true-listp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (true-listp dag)))

(defthm pseudo-dagp-forward-to-true-listp
  (implies (pseudo-dagp dag)
           (true-listp dag))
  :rule-classes :forward-chaining)

(defthm pseudo-dagp-forward-to-natp-of-caar
  (implies (pseudo-dagp dag)
           (natp (car (car dag))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthmd natp-of-car-of-car-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (natp (car (car dag)))))

(defthm pseudo-dagp-forward-to-posp-of-len
  (implies (pseudo-dagp dag)
           (posp (len dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-of-cdr-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (pseudo-dagp (cdr dag))
                  (consp (cdr dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

(defthm bounded-dag-exprp-of-lookup-equal-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (<= n (top-nodenum dag))
                (natp n))
           (bounded-dag-exprp n (lookup-equal n dag)))
  :hints (("Goal" :in-theory (e/d (PSEUDO-DAGP) (bounded-dag-exprp)))))

(defthm bounded-dag-exprp-of-lookup-equal-when-pseudo-dagp-gen
  (implies (and (<= n bound)
                (pseudo-dagp dag)
                (<= n (top-nodenum dag))
                (natp n))
           (bounded-dag-exprp bound (lookup-equal n dag)))
  :hints (("Goal" :use bounded-dag-exprp-of-lookup-equal-when-pseudo-dagp
           :in-theory (disable bounded-dag-exprp-of-lookup-equal-when-pseudo-dagp))))

(defthmd natp-of-car-of-nth-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag curr)
                (natp n)
                (natp curr))
           (equal (natp (car (nth n dag)))
                  (<= n curr)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd integerp-of-car-of-nth-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag curr)
                (natp n)
                (natp curr))
           (equal (integerp (car (nth n dag)))
                  (<= n curr)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;subsumes the 2 above?
(defthmd car-of-nth-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag curr)
                ;(natp n)
                (natp curr))
           (equal (car (nth n dag))
                  (if (<= (nfix n) curr)
                      (- curr (nfix n))
                    nil)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd consp-of-nth-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag curr)
                ;(natp n)
                (natp curr))
           (equal (consp (nth n dag))
                  (<= (nfix n) curr)))
  :hints (("Goal" ;:induct (PSEUDO-DAGP-AUX DAG CURR)
           :in-theory (enable pseudo-dagp-aux))))

(defthm len-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (natp top-nodenum))
           (equal (len dag)
                  (+ 1 (car (car dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-of-nthcdr
  (implies (and (pseudo-dagp dag)
                (natp n)
                (< 0 (- (len dag) n)) ;must be at least one node left)
                )
           (pseudo-dagp (nthcdr n dag)))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp
                                   natp-of-car-of-nth-when-pseudo-dagp-aux
                                   consp-of-nth-when-pseudo-dagp-aux
                                   car-of-nth-when-pseudo-dagp-aux)
                                  (nthcdr natp)))))

(defthmd pseudo-dagp-rewrite
  (equal (pseudo-dagp dag)
         (and (consp dag)
              (natp (top-nodenum dag))
              (pseudo-dagp-aux dag (top-nodenum dag))))
  :hints (("Goal" :expand (pseudo-dagp-aux dag nil)
           :in-theory (enable pseudo-dagp))))

;(pseudo-dagp '((2 foo '77 1) (1 bar 0) (0 . x)))

(defthm weak-dagp-aux-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (integerp nodenum))
           (weak-dagp-aux dag))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX WEAK-DAGP-AUX))))

(defthm weak-dagp-aux-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag (top-nodenum dag))
                (natp (top-nodenum dag)))
           (weak-dagp-aux dag)))

(defthm weak-dagp-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum))
           (weak-dagp dag))
  :hints (("Goal" :in-theory (enable weak-dagp pseudo-dagp-aux weak-dagp-aux))))

;; Pseudo-dagp is a stronger check
(defthm weak-dagp-when-pseudo-dagp
  (implies (pseudo-dagp x)
           (weak-dagp x))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthmd not-pseudo-dagp-when-quotep-cheap
  (implies (quotep x)
           (not (pseudo-dagp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize either a dag or a quoted constant (which can occur if rewriting
;; reduces a dag to simply a constant).
;; Disable?
(defun pseudo-dag-or-quotep (obj)
  (declare (xargs :guard t))
  (or (pseudo-dagp obj)
      (myquotep obj)))

(defthm pseudo-dag-or-quotep-forward-to-pseudo-dagp-when-not-quotep
  (implies (and (pseudo-dag-or-quotep dag)
                (not (quotep dag)))
           (pseudo-dagp dag))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dag-or-quotep))))

(defthm pseudo-dag-or-quotep-when-quotep-cheap
  (implies (quotep x)
           (equal (pseudo-dag-or-quotep x)
                  (myquotep x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dag-or-quotep))))

;; ;; uses quotep as the normal form
;; (defthmd pseudo-dagp-when-pseudo-dag-or-quotep-cheap
;;   (implies (pseudo-dag-or-quotep obj)
;;            (equal (pseudo-dagp obj)
;;                   (not (quotep obj))))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; uses quotep as the normal form
(defthmd myquotep-when-pseudo-dag-or-quotep-cheap
  (implies (pseudo-dag-or-quotep obj)
           (equal (myquotep obj)
                  (quotep obj)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The result is not necessarily sorted
(defun dag-vars-aux (dag acc)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (symbol-listp acc))))
  (if (endp dag)
      acc
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (dag-vars-aux (cdr dag)
                    (if (variablep expr)
                        (cons expr acc) ;could do add-to-set-eq, but there should be no duplicates, i guess
                      acc)))))

(defthm symbol-listp-of-dag-vars-aux
  (implies (and (symbol-listp acc)
                (weak-dagp-aux dag))
           (symbol-listp (dag-vars-aux dag acc)))
  :hints (("Goal" :in-theory (enable weak-dagp dag-exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The result is not necessarily sorted
(defund dag-vars-unsorted (dag)
  (declare (xargs :guard (or (quotep dag)
                             (weak-dagp dag))))
  (if (quotep dag)
      nil
    (dag-vars-aux dag nil)))

(defthm symbol-listp-of-dag-vars-unsorted
  (implies (weak-dagp dag)
           (symbol-listp (dag-vars-unsorted dag)))
  :hints (("Goal" :in-theory (enable dag-vars-unsorted))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a sorted list of symbols.
;; todo: use a better ordering that sorted numbered symbols numerically (x10 should not follow x1; x2-x9 should come first)
;; todo: remove handling of quoteps here (use dag-or-quotep-vars below)
(defund dag-vars (dag)
  (declare (xargs :guard (or (quotep dag)
                             (weak-dagp dag))))
  (if (quotep dag)
      nil
    (merge-sort-symbol< (dag-vars-unsorted dag))))

(defthm symbol-listp-of-dag-vars
  (implies (weak-dagp dag)
           (symbol-listp (dag-vars dag)))
  :hints (("Goal" :in-theory (enable dag-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund dag-or-quotep-vars (x)
  (declare (xargs :guard (or (quotep x)
                             (weak-dagp x))))
  (if (quotep x)
      nil ; no vars
    (dag-vars x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The result is not necessarily sorted
(defun get-vars-from-dags-aux (dags acc)
  (if (endp dags)
      acc
    (let* ((dag (first dags))
           (vars (dag-vars-unsorted dag)))
      (get-vars-from-dags-aux (rest dags) (union-eq vars acc)))))

(defun get-vars-from-dags (dags)
  (get-vars-from-dags-aux dags nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dag-fns-aux (dag acc)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (symbol-listp acc))
                  :guard-hints (("Goal" :in-theory (enable dag-exprp
                                                           symbolp-of-car-when-dag-exprp)))))
  (if (endp dag)
      acc
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (and (consp expr)
               (not (eq 'quote (car expr))))
          (dag-fns-aux (cdr dag) (add-to-set-eq (car expr) acc))
        (dag-fns-aux (cdr dag) acc)))))

(defthm symbol-listp-of-dag-fns-aux
  (implies (and (symbol-listp acc)
                (weak-dagp-aux dag))
           (symbol-listp (dag-fns-aux dag acc)))
  :hints (("Goal" :in-theory (enable weak-dagp dag-exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return a list of all the functions that appear in the DAG-OR-QUOTEP
;; todo: remove handling of quoteps here (use dag-or-quotep-fns below)
(defund dag-fns (dag-or-quotep)
  (declare (xargs :guard (or (quotep dag-or-quotep)
                             (weak-dagp dag-or-quotep))))
  (if (quotep dag-or-quotep)
      nil
    (merge-sort-symbol< (dag-fns-aux dag-or-quotep nil))))

(defthm symbol-listp-of-dag-fns
  (implies (or (quotep dag-or-quotep)
               (weak-dagp dag-or-quotep))
           (symbol-listp (dag-fns dag-or-quotep)))
  :hints (("Goal" :in-theory (enable dag-fns))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund dag-or-quotep-fns (x)
  (declare (xargs :guard (or (quotep x)
                             (weak-dagp x))))
  (if (quotep x)
      nil ; no fns
    (dag-fns x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether the functions that appear in DAG include any of the
;; FNS.  Stops as soon as it finds any of the FNS.  Does not cons up the list
;; of all fns found.
(defund dag-fns-include-anyp (dag fns)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (symbol-listp fns)
                              (not (member-eq 'quote fns)))
                  :guard-hints (("Goal" :in-theory (enable dag-exprp
                                                           symbolp-of-car-when-dag-exprp)))))
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (and (consp expr)
               ;; implies that (ffn-symb expr) can't be 'quote, since FNS should not include 'quote:
               (member-eq (ffn-symb expr) fns))
          t
        (dag-fns-include-anyp (rest dag) fns)))))

;; ;; Checks whether the functions that appear in DAG-OR-QUOTEP include any of the
;; ;; FNS.  Stops as soon as it finds any of the FNS.  Does not cons up the list
;; ;; of all fns found.
;; (defund dag-or-quotep-fns-include-any (dag-or-quotep fns)
;;   (declare (xargs :guard (and (or (quotep dag-or-quotep)
;;                                   (weak-dagp dag-or-quotep))
;;                               (symbol-listp fns)
;;                               (not (member-eq 'quote fns)))))
;;   (if (quotep dag-or-quotep)
;;       nil
;;     (dag-fns-include-anyp dag-or-quotep fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; allows a subset
(defun check-dag-vars (allowed-vars dag)
  (let ((actual-vars (dag-vars-unsorted dag)))
    (if (subsetp-eq actual-vars allowed-vars)
        dag
      (er hard? 'check-dag-vars "unexpected vars (got: ~x0, expected ~x1) in dag: ~X23" actual-vars allowed-vars dag nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prints OBJ, which may be a dag or a quoted constant.
(defund print-dag-or-quotep (obj)
  (declare (xargs :guard (weak-dag-or-quotep obj)))
  (if (quotep obj)
      (cw "~x0~%" obj)
    (print-list obj)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;deprecate? maybe not. first add the functionality to get-subdag?
(defund drop-nodes-past (nodenum dag)
  (declare (xargs :guard (and (natp nodenum)
                              (weak-dagp-aux dag))))

  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (nodenum2 (car entry)))
      (if (< nodenum nodenum2)
          (drop-nodes-past nodenum (cdr dag))
        dag))))

;; ;does not include inlined constants
;; (defund dag-constants-aux (dag acc)
;;   (declare (xargs :guard (and (alistp dag)
;;                               (true-listp acc))
;;                   :guard-hints (("Goal" :in-theory (enable alistp)))))
;;   (if (endp dag)
;;       acc
;;     (let* ((entry (first dag))
;;            (expr (cdr entry)))
;;       (dag-constants-aux (cdr dag)
;;                          (if (quotep expr)
;;                              (add-to-set-equal expr acc)
;;                            acc)))))

;; (defund dag-constants (dag)
;;   (declare (xargs :guard (alistp dag)))
;;   (dag-constants-aux dag nil))

;; test: (dag-equal-term-at-node '((2 foo 1 0) (1 quote 3) (0 . x)) '(foo '3 x) 2)
;; test: (not (dag-equal-term-at-node '((2 foo 1 0) (1 quote 3) (0 . x)) '(foo '3 y) 2))

;kill
;i guess this is a weakend obligation for checking that an arg is a quoted thing?
;; (defthm <-of-len-of-nth-of-dargs-and-3
;;   (implies (and (dag-exprp expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (< (len (nth n (dargs expr))) 3))
;;   :hints (("Goal" :in-theory (enable <-of-len-of-nth-and-3-when-darg-listp))))

;kill
;; (defthm not-<-of-len-of-nth-of-dargs-and-2
;;   (implies (and (dag-exprp expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (not (< 2 (len (nth n (dargs expr))))))
;;   :hints (("Goal" :use (:instance <-of-len-of-nth-of-dargs-and-3)
;;            :in-theory (disable <-of-len-of-nth-of-dargs-and-3))))

;kill
;; (defthm <-of-1-and-len-of-nth-of-dargs
;;   (implies (and (dag-exprp expr)
;;                 (< n (len (dargs expr)))
;;                 (natp n)
;;                 (not (equal 'quote (car expr)))
;; ;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
;;                 )
;;            (equal (< 1 (len (nth n (dargs expr))))
;;                   (consp (nth n (dargs expr)))))
;;   :hints (("Goal" :in-theory (enable <-of-1-and-len-of-nth-when-darg-listp))))

(defthmd len-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (consp dag))
           (equal (len dag)
                  (+ 1 (car (car dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm max-key-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (acl2-numberp max-so-far) ;may not be needed
                (natp top-nodenum))
           (equal (max-key dag max-so-far)
                  (max (car (car dag))
                       max-so-far)))
  :hints (("Goal" ;:cases ()
           :do-not '(generalize)
           :in-theory (enable pseudo-dagp-aux max-key))))

(defthm max-key-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (acl2-numberp max-so-far) ;may not be needed
                )
           (equal (max-key dag max-so-far)
                  (max (car (car dag))
                       max-so-far)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm nth-0-of-nth-0-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (nth 0 (nth 0 dag))
                  (+ -1 (len dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm assoc-equal-when-PSEUDO-DAGP-AUX
 (IMPLIES (AND (PSEUDO-DAGP-AUX DAG m)
               (<= N m)
               (natp N)
               (natp m))
          (ASSOC-EQUAL N DAG))
 :hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX))))

(defthmd assoc-equal-when-PSEUDO-DAGP
  (IMPLIES (AND (PSEUDO-DAGP DAG)
                (<= N (CAR (CAR DAG)))
                (natp N))
           (ASSOC-EQUAL N DAG))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP))))

(defthm dag-exprp-of-lookup-equal-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (<= n current-nodenum)
                (natp n)
                (integerp current-nodenum))
           (dag-exprp (lookup-equal n dag)))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp-aux LOOKUP-EQUAL assoc-equal)
                                  (dag-exprp)))))

(defthm dag-exprp-of-lookup-equal-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (<= n (top-nodenum dag))
                (natp n))
           (dag-exprp (lookup-equal n dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm not-<-of-plus1-of-largest-non-quotep-when-bounded-darg-listp
  (implies (and (bounded-darg-listp nodenum-or-quotep-or-lst bound)
                (natp bound))
           (not (< bound (+ 1 (largest-non-quotep nodenum-or-quotep-or-lst)))))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))

;move
(defthmd largest-non-quotep-when-all-myquotep
  (implies (all-myquotep items)
           (equal (largest-non-quotep items)
                  -1))
  :hints (("Goal" :in-theory (enable largest-non-quotep))))



;move?
;todo: why didn't dag-walker-measure-for-item work here?  may need some mbts
(mutual-recursion
 (defun dag-equal-term-at-node (dag term nodenum-or-quotep)
   (declare (xargs :guard (and (or (myquotep nodenum-or-quotep)
                                   (natp nodenum-or-quotep))
                               (pseudo-dagp dag) ;(alistp dag)
                               (if (not (consp nodenum-or-quotep)) ;check for nodenum
                                   (<= nodenum-or-quotep (top-nodenum dag))
                                 t)
                               (pseudo-termp term))
                   :guard-hints (("Goal" :expand ((PSEUDO-DAGP-AUX DAG NODENUM-OR-QUOTEP))
                                  :use (:instance dag-exprp-of-lookup-equal-when-pseudo-dagp (n NODENUM-OR-QUOTEP))
                                  :in-theory (e/d (bounded-darg-listp dag-exprp)
                                                  (len true-listp dag-exprp-of-lookup-equal-when-pseudo-dagp))
                                  :do-not '(generalize eliminate-destructors)
                                  ))
                   :measure (acl2-count term)))
   (if (quotep nodenum-or-quotep)
       (equal nodenum-or-quotep term)
     (let ((expr (lookup nodenum-or-quotep dag)))
       (if (symbolp expr)
           (equal expr term)
         (if (quotep expr)
             (equal expr term)
           ;; it's a function call
           (and (consp term)
                (eq (ffn-symb expr) (ffn-symb term))
                (if (eql (len (dargs expr)) (len (fargs term))) ;should always be true
                    t
                  (er hard? 'dag-equal-term-at-node "Arity mismatch: ~x0, ~x1." expr term))
                (dag-equal-terms-at-nodes dag (fargs term) (dargs expr))))))))

 (defun dag-equal-terms-at-nodes (dag terms nodenums-and-quoteps)
   (declare (xargs :guard (and (pseudo-dagp dag)
                               (bounded-darg-listp nodenums-and-quoteps (+ 1 (top-nodenum dag)))
                               (true-listp nodenums-and-quoteps)
                               (pseudo-term-listp terms)
                               (equal (len terms) (len nodenums-and-quoteps)))
                   :measure (acl2-count terms)))
   (if (endp terms)
       t
     (and (dag-equal-term-at-node dag (first terms) (first nodenums-and-quoteps))
          (dag-equal-terms-at-nodes dag (rest terms) (rest nodenums-and-quoteps))))))

;; (defun dag-equal-term (dag term)
;;   (declare (xargs :guard (and (good-dagp dag)
;;                               (pseudo-termp term))))
;;   (dag-equal-term-at-node dag term (top-nodenum dag)))

;enable?
(defthmd top-nodenum-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (top-nodenum dag)
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable top-nodenum pseudo-dagp))))

(defthm natp-of-top-nodenum-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (natp (top-nodenum dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

;mixes car and "nth 0"
(defthm car-of-nth-0-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (nth 0 dag))
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

(defthm dargp-less-than-of-nth-when-bounded-darg-listp-gen
  (implies (and (bounded-darg-listp vals bound)
                (natp n)
                (< n (len vals)))
           (dargp-less-than (nth n vals) bound))
  :hints
  (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm dargp-less-than-when-myquotep-cheap
  (implies (myquotep item)
           (dargp-less-than item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm dargp-less-than-when-equal-of-nth-0-and-quote
  (implies (and (equal 'quote (nth 0 item))
                (dargp item))
           (dargp-less-than item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm pseudo-dagp-aux-forward-to-true-listp
  (implies (pseudo-dagp-aux dag current-nodenum)
           (true-listp dag))
  :rule-classes :forward-chaining)

(defthm pseudo-dagp-aux-of-cons-of-cons
  (implies (integerp nodenum)
           (equal (pseudo-dagp-aux (cons (cons nodenum expr) dag) nodenum)
                  (and (natp nodenum)
                       (bounded-dag-exprp nodenum expr)
                       (pseudo-dagp-aux dag (+ -1 nodenum)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-nil
  (equal (pseudo-dagp-aux nil current-nodenum)
         (< current-nodenum 0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm pseudo-dagp-aux-of-car-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag num)
                (natp num)
                )
           (pseudo-dagp-aux dag (car (car dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;; can introduce bounded-darg-listp out of nowhere, so kept disabled
(defthmd not-<-of-nth-when-bounded-darg-listp-gen
  (implies (and (bounded-darg-listp vals bound)
                (natp n)
                (< n (len vals))
                ;; (not (consp val))
                (natp bound))
           (not (< bound (nth n vals))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp nth))))

(defthm not-<-of-nth-when-bounded-darg-listp-gen-constant
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (bounded-darg-listp vals bound)
                ;; (natp n)
                ;; (< n (len vals))
                ;; (not (consp val))
                )
           (not (< (nth n vals) k)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp dargp-less-than nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; move these?

;; Tests that DARG is a quoted constant, not a nodenum, and that the constant is an integerp.
(defund darg-quoted-integerp (darg)
  (declare (xargs :guard (dargp darg)))
  (and (consp darg)
       (integerp (unquote darg))))

(defthm darg-quoted-integerp-forward
  (implies (darg-quoted-integerp darg)
           (and (consp darg)
                (integerp (cadr darg))
                (integerp (nth 1 darg))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable darg-quoted-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests that DARG is a quoted constant, not a nodenum, and that the constant is a natp.
(defund darg-quoted-natp (darg)
  (declare (xargs :guard (dargp darg)))
  (and (consp darg)
       (natp (unquote darg))))

(defthm darg-quoted-natp-forward
  (implies (darg-quoted-natp darg)
           (and (consp darg)
                (natp (cadr darg))
                (natp (nth 1 darg))
                (darg-quoted-integerp darg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable darg-quoted-natp
                                     darg-quoted-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests that DARG is a quoted constant, not a nodenum, and that the constant is a posp.
(defund darg-quoted-posp (darg)
  (declare (xargs :guard (dargp darg)))
  (and (consp darg)
       (posp (unquote darg))))

(defthm darg-quoted-posp-forward
  (implies (darg-quoted-posp darg)
           (and (consp darg)
                (posp (cadr darg))
                (posp (nth 1 darg))
                (darg-quoted-natp darg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable darg-quoted-posp
                                     darg-quoted-natp))))

(defthm not-<-of-+-1-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp items dag-len)
                (natp n)
                (< n (len items))
                (natp dag-len)
                (not (consp (nth n items))))
           (not (< dag-len (+ 1 (nth n items)))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp nth))))

(defthm bounded-darg-listp-when-all-<
  (implies (and (all-< items bound)
                (all-natp items))
           (equal (bounded-darg-listp items bound)
                  (true-listp items)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp all-< all-natp))))

(defthm bounded-darg-listp-of-dargs-when-<-simple
  (implies (and (bounded-dag-exprp limit expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (bounded-darg-listp (dargs expr) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;drop?
(defthmd bounded-darg-listp-of-dargs-when-<
  (implies (and (< nodenum limit)
                (bounded-dag-exprp nodenum expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                )
           (bounded-darg-listp (dargs expr) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;move
;; use consp as our normal form
(defthm len-of-nth-when-bounded-darg-listp
  (implies (and (bounded-darg-listp items bound)
                (< (nfix n) (len items)))
           (equal (len (nth n items))
                  (if (consp (nth n items))
                      2
                    0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp nth))))

;move
(defthmd len-of-nth-when-darg-listp
  (implies (and (darg-listp items)
                (< (nfix n) (len items)))
           (equal (len (nth n items))
                  (if (consp (nth n items))
                      2
                    0)))
  :hints (("Goal" :in-theory (enable darg-listp nth))))

;; (defthm <-of-car-when-bounded-darg-listp
;;   (implies (and (bounded-darg-listp items bound)
;;                 (not (consp (car items)))
;;                 (consp items))
;;            (< (car items) bound))
;;   :hints (("Goal" :in-theory (enable bounded-darg-listp))))

(defthm bounded-natp-alistp-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (bounded-natp-alistp dag (len dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux bounded-natp-alistp))))

(defthm bounded-natp-alistp-when-pseudo-dagp-gen
  (implies (and (pseudo-dagp dag)
                (<= (len dag) bound)
                (natp bound))
           (bounded-natp-alistp dag bound))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm bounded-natp-alistp-of-+-1-of-caar-when-pseudo-dagp-gen-2
  (implies (pseudo-dagp dag)
           (bounded-natp-alistp dag (+ 1 (caar dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthmd car-of-car-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (car dag))
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(theory-invariant (incompatible (:rewrite car-of-car-when-pseudo-dagp)
                                (:rewrite len-when-pseudo-dagp)))

(defthmd car-of-car-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (car (car dag))
                  (+ -1 (len dag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm acl2-numberp-of-largest-non-quotep
  (implies (darg-listp items)
           (acl2-numberp (largest-non-quotep items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable DARG-LISTP LARGEST-NON-QUOTEP))))

(defthm myquotep-of-cdr-of-assoc-equal
  (implies (and (assoc-equal form alist)
                (equal 'quote (cadr (assoc-equal form alist)))
                (darg-listp (strip-cdrs alist)))
           (myquotep (cdr (assoc-equal form alist))))
  :hints (("Goal" :use (:instance DARGP-OF-CDR-OF-ASSOC-EQUAL-WHEN-DARG-LISTP-OF-STRIP-CDRS (var form))
           :in-theory (e/d (dargp) ( ;dargp-of-cdr-of-assoc-equal
                                    DARGP-OF-CDR-OF-ASSOC-EQUAL-WHEN-DARG-LISTP-OF-STRIP-CDRS
                                    dargp-when-equal-of-quote-and-car-cheap)))))

(defthm <=-of-largest-non-quotep-when-bounded-darg-listp
  (implies (and (bounded-darg-listp items (+ 1 bound))
                (natp bound))
           (<= (largest-non-quotep items) bound))
  :hints (("Goal" :in-theory (enable bounded-darg-listp
                                     largest-non-quotep))))

(defthm bounded-darg-listp-of-+-of-1-and-largest-non-quotep
  (implies (darg-listp dargs)
           (bounded-darg-listp dargs (+ 1 (largest-non-quotep dargs))))
  :hints (("Goal" :in-theory (enable bounded-darg-listp largest-non-quotep darg-listp))))

(defthm <-of-largest-non-quotep-of-dargs-when-dag-exprp
  (implies (and (bounded-dag-exprp (+ 1 n) expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (natp n))
           (not (< n (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm <-of-LARGEST-NON-QUOTEP-of-dargs
  (implies (and (bounded-dag-exprp nodenum expr)
                (not (equal 'quote (car expr)))
                (natp nodenum))
           (< (LARGEST-NON-QUOTEP (DARGS expr))
              nodenum))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;remove the other?
(defthm <-of-largest-non-quotep-of-dargs-when-dag-exprp-gen
  (implies (and (bounded-dag-exprp (+ 1 n) expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (integerp n) ;this version
                (<= -1 N) ;this version
                )
           (not (< n (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :cases ((< n 0))
           :in-theory (enable bounded-dag-exprp bounded-darg-listp-when-non-positive))))

;todo: limit?
;move
(defthm consp-of-car-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (natp top-nodenum)
                )
           (consp (car dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm consp-of-car-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (consp dag))
           (consp (car dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm natp-of-car-of-car-when-pseudo-dagp-aux-2
  (implies (and (pseudo-dagp-aux dag top-nodenum)
                (natp top-nodenum))
           (natp (car (car dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthm consp-of-car-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (consp (car dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
  (implies (and (pseudo-dagp dag)
                (consp dag))
           (true-listp (dargs (cdr (car dag)))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm dag-exprp-of-cdr-of-car-when-weak-dagp
  (implies (weak-dagp dag)
           (dag-exprp (cdr (car dag))))
  :hints (("Goal" :in-theory (enable weak-dagp))))

(defthm pseudo-dagp-forward-to-consp-of-car
  (implies (pseudo-dagp dag)
           (consp (car dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-forward-to-consp-of-nth-0
  (implies (pseudo-dagp dag)
           (consp (nth 0 dag)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm pseudo-dagp-forward-to-consp
  (implies (pseudo-dagp dag)
           (consp dag))
  :rule-classes :forward-chaining)

(defthm all-<-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (all-< (strip-cars dag) (len dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))

(defthm all-<-of-strip-cars-of-+-1-of-top-nodenum
  (implies (pseudo-dagp dag)
           (all-< (strip-cars dag) (+ 1 (top-nodenum dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux))))


;disable or limit?
(defthm weak-dagp-aux-when-pseudo-dagp
  (implies (pseudo-dagp x)
           (weak-dagp-aux x))
  :hints (("Goal" :in-theory (enable PSEUDO-DAGP))))

(defthmd car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (natp current-nodenum))
           (equal (car (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;here we are getting the nodenum of the last element
(defthm car-of-nth-of-caar-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag nodenum)
                (natp nodenum))
           (equal (car (nth (car (car dag)) dag))
                  0))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd car-of-nth-of-+-of--1-and-len-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp)
                                  (;nth-of-cdr
                                   )))))

(defthm car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (car (NTH (+ -1 (LEN dag)) dag))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable car-of-nth-of-+-of--1-and-len-when-pseudo-dagp))))

(defthmd nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (nth 0 (nth (+ -1 (len dag)) dag))
                  0))
  :hints (("Goal" :use (:instance car-of-nth-of-+-of--1-and-len-when-pseudo-dagp)
           :in-theory (e/d (nth)
                           (;nth-of-cdr
                            car-of-nth-of-+-of--1-and-len-when-pseudo-dagp
                            car-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap)))))

(defthm nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp-cheap
  (implies (pseudo-dagp dag)
           (equal (nth 0 (nth (+ -1 (len dag)) dag))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :use nth-0-of-nth-of-+-of--1-and-len-when-pseudo-dagp
           :in-theory (disable car-of-nth-of-+-of--1-and-len-when-pseudo-dagp))))

(defthm pseudo-dagp-aux-of-minus1-of-len
  (implies (pseudo-dagp dag)
           (pseudo-dagp-aux dag (binary-+ '-1 (len dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))

(defthm rational-listp-of-strip-cars-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag current-nodenum)
                (integerp current-nodenum))
           (rational-listp (strip-cars dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-dag-exprp strip-cars))))

(defthm all-<-of-strip-cars-and-+-1-of-caar
  (implies (pseudo-dagp-aux dag (car (car dag)))
           (all-< (strip-cars dag)
                  (+ 1 (car (car dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux strip-cars))))

(defthm rational-listp-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (rational-listp (strip-cars dag))))

(defthm maxelem-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (maxelem (strip-cars dag))
                  (car (car dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux strip-cars))))


;; ;drop?
;; (defthm pseudo-dagp-aux-of-cdr-lemma
;;   (implies (and (pseudo-dagp-aux dag (car (car dag)))
;;                 (equal (car (car dag)) (+ -1 (len dag)))
;;                 (< 1 (len dag))
;;                 (true-listp dag))
;;            (pseudo-dagp-aux (cdr dag) (car (cadr dag))))
;;   :hints (("Goal" :expand ((pseudo-dagp-aux dag (car (car dag)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG)
;;                                             (CAR (CADR DAG)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG)
;;                                             (+ -1 (CAR (CAR DAG))))))))

;; (defthmd integerp-of-car-of-car-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag nodenum)
;;                 (consp dag)
;;                 (integerp nodenum))
;;            (integerp (car (car dag))))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

;; (local (in-theory (enable integerp-of-car-of-car-when-pseudo-dagp-aux)))

;; ;todo: some of this stuff is not needed

;; (defthm PSEUDO-DAGP-AUX-of-cdr-lemma2
;;   (implies (and (PSEUDO-DAGP-AUX REV-DAG (+ -1 (LEN REV-DAG)))
;;                 (consp REV-DAG))
;;            (PSEUDO-DAGP-AUX (CDR REV-DAG) (+ -2 (LEN REV-DAG))))
;;   :hints (("Goal" :expand (PSEUDO-DAGP-AUX REV-DAG (+ -1 (LEN REV-DAG)))
;;            :in-theory (disable LEN-WHEN-PSEUDO-DAGP-AUX))))

;; (local (in-theory (disable LEN-WHEN-PSEUDO-DAGP-AUX))) ;looped!

;; (defthmd caar-of-cdr-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag (+ -1 (len dag)))
;;                 (consp (cdr dag)))
;;            (equal (car (car (cdr dag)))
;;                   (+ -2 (len dag))))
;;   :hints (("Goal" :expand ((pseudo-dagp-aux dag (+ -1 (len dag)))
;;                            (PSEUDO-DAGP-AUX (CDR DAG)
;;                                             (+ -1 (CAR (CAR DAG))))))))


;move?
(defthm <-of-largest-non-quotep-of-dargs-2
  (implies (and (bounded-dag-exprp nodenum expr)
                (natp nodenum)
                (consp expr)
                (not (equal (car expr) 'quote)))
           (not (< (+  -1 nodenum)
                   (largest-non-quotep (dargs expr)))))
  :hints (("Goal" :use (:instance <-of-largest-non-quotep-of-dargs-when-dag-exprp
                                  (n (+ -1 nodenum)))
           :expand (bounded-dag-exprp 0 expr)
           :in-theory (disable <-of-largest-non-quotep-of-dargs-when-dag-exprp))))

(defthm dargp-of-lookup-equal-when-bounded-darg-listp-of-strip-cdrs
  (implies (and (bounded-darg-listp (strip-cdrs alist) dag-len)
                (lookup-equal var alist))
           (dargp (lookup-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (bounded-darg-listp lookup-equal strip-cdrs
                                                           dargp-less-than)
                           (myquotep)))))

(defthmd <-of-lookup-equal-when-bounded-darg-listp-of-strip-cdrs
  (implies (and (bounded-darg-listp (strip-cdrs alist) dag-len)
                (lookup-equal var alist)
                (not (consp (lookup-equal var alist))))
           (< (lookup-equal var alist) dag-len))
  :hints (("Goal" :in-theory (e/d (bounded-darg-listp lookup-equal strip-cdrs)
                                  (myquotep)))))

;may subsume stuff above
(defthmd car-of-nth-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (car (nth n dag))
                  (if (< (nfix n) (+ 1 (car (car dag))))
                      (+ -1 (len dag) (- (nfix n)))
                    nil)))
  :hints (("Goal" :in-theory (enable pseudo-dagp
                                     CAR-OF-NTH-WHEN-PSEUDO-DAGP-AUX))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this one has a better guard than top-nodenum
(defund top-nodenum-of-dag (dag)
  (declare (xargs :guard (pseudo-dagp dag)
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))))
  (let* ((entry (car dag))
         (nodenum (car entry)))
    nodenum))

;; for reasoning (for execution, len would be much slower)
(defthm top-nodenum-of-dag-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (equal (top-nodenum-of-dag dag)
                  (+ -1 (len dag))))
  :hints (("Goal" :in-theory (enable top-nodenum-of-dag pseudo-dagp))))

(defthm natp-of-top-nodenum-of-dag
  (implies (pseudo-dagp dag)
           (natp (top-nodenum-of-dag dag)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable top-nodenum-of-dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; similar to (append (keep-nodenum-dargs items) acc).
;move?
;; Extends ACC with the members of ITEMS that are nodenums (also reverses their
;; order).  Each member of ITEMS must be a nodenum or a quoted constant.
(defund append-nodenum-dargs (items acc)
  (declare (xargs :guard (and (darg-listp items)
                              (true-listp acc))))
  (if (endp items)
      acc
    (let ((item (first items)))
      (append-nodenum-dargs (rest items)
                    (if (atom item)
                        (cons item acc)
                      acc)))))

(defthm all-<-of-append-nodenum-dargs
  (equal (all-< (append-nodenum-dargs args acc) bound)
         (and (all-< (keep-nodenum-dargs args) bound)
              (all-< acc bound)))
  :hints (("Goal" :in-theory (enable keep-nodenum-dargs append-nodenum-dargs all-<))))

(defthm true-listp-of-append-nodenum-dargs
  (implies (true-listp acc)
           (true-listp (append-nodenum-dargs args acc)))
  :hints (("Goal" :in-theory (enable append-nodenum-dargs))))

(defthm true-listp-of-append-nodenum-dargs-type
  (implies (true-listp acc)
           (true-listp (append-nodenum-dargs args acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable append-nodenum-dargs))))

(defthm nat-listp-of-append-nodenum-dargs
  (implies (darg-listp dargs)
           (equal (nat-listp (append-nodenum-dargs dargs acc))
                  (nat-listp acc)))
  :hints (("Goal" :in-theory (enable append-nodenum-dargs nat-listp))))

(defthmd append-nodenum-dargs-becomes-append-of-keep-nodenum-dargs
  (equal (append-nodenum-dargs items acc)
         (append (reverse-list (keep-nodenum-dargs items))
                 acc))
  :hints (("Goal" :in-theory (enable append-nodenum-dargs keep-nodenum-dargs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd natp-of-car-of-nth-when-pseudo-dagp
  (implies (and (pseudo-dagp dag)
                (natp n))
           (equal (natp (car (nth n dag)))
                  (<= n (top-nodenum dag))))
  :hints (("Goal" :in-theory (e/d (pseudo-dagp
                                   natp-of-car-of-nth-when-pseudo-dagp-aux)
                                  (natp)))))

(defthmd <-of-car-of-nth-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp dag bound)
                (natp n)
                (< n (len dag))
                )
           (< (car (nth n dag)) bound))
  :hints (("Goal" :in-theory (e/d (bounded-natp-alistp nth)
                                  (natp)))))

(defthmd <-of-car-of-nth-when-pseudo-dagp
  (implies (and (<= (len dag) bound)
                (pseudo-dagp dag)
                (natp n)
                (< n (len dag))
                (natp bound))
           (< (car (nth n dag)) bound))
  :hints (("Goal" :in-theory (e/d (<-of-car-of-nth-when-bounded-natp-alistp)
                                  (natp)))))

(defthmd not-equal-of-car-of-nth-when-not-member-equal-of-strip-cars
  (implies (and (not (member-equal key (strip-cars alist)))
                (natp n)
                (< n (len alist))
                (alistp alist))
           (not (equal key (car (nth n alist)))))
  :hints (("Goal" :in-theory (enable nth))))

(defthmd assoc-equal-of-car-of-nth-same-when-alistp-and-no-duplicatesp-equal-of-strip-cars
  (implies (and (alistp alist)
                (no-duplicatesp-equal (strip-cars alist))
                (natp n)
                (< n (len alist)))
           (equal (assoc-equal (car (nth n alist)) alist)
                  (nth n alist)))
  :hints (("Goal" :in-theory (enable assoc-equal nth not-equal-of-car-of-nth-when-not-member-equal-of-strip-cars))))

(defthmd member-equal-of-strip-cars-when-pseudo-dagp-aux-iff
  (implies (and (pseudo-dagp-aux dag curr)
                (integerp curr)
                (<= -1 curr))
           (iff (member-equal n (strip-cars dag))
                (and (natp n)
                     (<= n curr))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux))))

(defthmd member-equal-of-strip-cars-when-pseudo-dagp-iff
  (implies (pseudo-dagp dag)
           (iff (member-equal n (strip-cars dag))
                (and (natp n)
                     (<= n (top-nodenum dag)))))
  :hints (("Goal" :in-theory (enable pseudo-dagp member-equal-of-strip-cars-when-pseudo-dagp-aux-iff))))

(defthmd no-duplicatesp-equal-of-strip-cars-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag curr)
                (natp curr))
           (no-duplicatesp-equal (strip-cars dag)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable pseudo-dagp-aux member-equal-of-strip-cars-when-pseudo-dagp-aux-iff))))

(defthmd no-duplicatesp-equal-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (no-duplicatesp-equal (strip-cars dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp no-duplicatesp-equal-of-strip-cars-when-pseudo-dagp-aux))))
