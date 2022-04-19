; Memoizing the DAG nodes that Axe trees rewrote to.
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

;; The memoization conceptually maps objects (axe-trees) to the nodenum/quotep
;; to which they rewrote.  It is implemented as a hash table with chaining,
;; where the hash of a tree is the sum of the nodenums in the object modulo
;; *memoization-size*.

(include-book "tools/flag" :dir :system)
;(include-book "arrays-of-alists")
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "axe-trees")
(include-book "count-worlds")
(include-book "all-dargp")
(include-book "bounded-darg-listp")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)) ;todo
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))

;; TODO: Consider using a stobj for the memoization, perhaps with a Lisp hash table.
;; TODO: Consider not memoizing things with unsimplified args? (that seemed to slow things down)
;; TODO: Consider not memoizing things that didn't take a lot of work to compute.
;; TODO: Consider whether to memoize rewrites of lambda applications (but not memoizing them slowed things down?)
;; TODO: Consider whether to memoize rewrites of ground terms
;; TODO: Consider making a separate memoization for tree that are functions applied to simplified args (common).
;; TODO: Consider using an info world for the memoization (to make it per head symbol)
;; TODO: Consider memoizing only destructor trees, not constructor trees
;; NOTE: For anything we won't memoize, we should avoid consing it onto trees-equal-to-tree in the rewriter

;maybe we should think of the memoization as part of the dag (it is just a list of equalities which mention nodenums from the dag)

(local (in-theory (disable mod natp)))

(local (in-theory (enable integerp-when-natp
                           <=-of-0-when-0-natp)))

;; Recognize an axe-tree that is a cons
;; TODO: Restrict to bounded-axe-trees?
(defund tree-to-memoizep (tree)
  (declare (xargs :guard t))
  (and (axe-treep tree)
       (bounded-axe-treep tree 2147483646)
       (consp tree)
       (not (eq 'quote (ffn-symb tree)))))

(defthm tree-to-memoizep-forward-to-axe-treep
  (implies (tree-to-memoizep tree)
           (axe-treep tree))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

(defthm tree-to-memoizep-forward-to-consp
  (implies (tree-to-memoizep tree)
           (consp tree))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

;why needed?
(defthm tree-to-memoizep-forward-to-not-equal-of-car-and-quote
  (implies (tree-to-memoizep tree)
           (not (eq 'quote (ffn-symb tree))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

(defthm tree-to-memoizep-of-cons
  (equal (tree-to-memoizep (cons fn args))
         (and (or (symbolp fn)
                  (and (true-listp fn)
                       (equal (len fn) 3)
                       (eq (car fn) 'lambda)
                       (symbol-listp (cadr fn))
                       (pseudo-termp (caddr fn))
                       (equal (len (cadr fn))
                              (len args))))
              (not (equal 'quote fn))
              (bounded-axe-tree-listp args 2147483646)))
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

(defthmd axe-treep-when-tree-to-memoizep
  (implies (tree-to-memoizep tree)
           (axe-treep tree))
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

(defthmd tree-to-memoizep-when-axe-treep-and-bounded-axe-treep-cheap
  (implies (and (axe-treep tree)
                (bounded-axe-treep tree bound)
                (<= bound 2147483646)
                ;; (natp bound)
                )
           (equal (tree-to-memoizep tree)
                  (and (consp tree)
                       (not (equal 'quote (ffn-symb tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil)))
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

(defthm tree-to-memoizep-when-axe-treep-and-bounded-axe-treep-cheap-2
  (implies (and (axe-treep tree)
                (bounded-axe-treep tree bound)
                (<= bound 2147483646)
                ;; (natp bound)
                (consp tree)
                (not (equal 'quote (ffn-symb tree)))
                )
           (tree-to-memoizep tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil nil)))
  :hints (("Goal" :in-theory (enable tree-to-memoizep))))

;; (defthm tree-to-memoizep-when-axe-treep
;;   (implies (axe-treep tree)
;;            (equal (tree-to-memoizep tree)
;;                   (and (consp tree))))
;;   :hints (("Goal" :in-theory (e/d (tree-to-memoizep) (axe-treep)))))

;; Recognize a true-list of axe-trees that are conses
(defund trees-to-memoizep (trees)
  (declare (xargs :guard t))
  (if (atom trees)
      (null trees)
    (and (tree-to-memoizep (first trees))
         (trees-to-memoizep (rest trees)))))

(defthm trees-to-memoizep-forward-to-true-listp
  (implies (trees-to-memoizep trees)
           (true-listp trees))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable trees-to-memoizep))))

(defthm trees-to-memoizep-of-cons
  (equal (trees-to-memoizep (cons tree trees))
         (and (tree-to-memoizep tree)
              (trees-to-memoizep trees)))
  :hints (("Goal" :in-theory (enable trees-to-memoizep))))

(defthm tree-to-memoizep-of-car
  (implies (and (trees-to-memoizep trees)
                (consp trees))
           (tree-to-memoizep (car trees)))
  :hints (("Goal" :in-theory (enable trees-to-memoizep))))

(defthm dargp-of-lookup-equal-alt ;name clash
  (implies (and ;(alistp alist)
                (all-dargp (strip-cdrs alist))
                (lookup-equal tree alist))
           (dargp (lookup-equal tree alist)))
  :hints (("Goal" :in-theory (e/d (lookup-equal assoc-equal) (dargp)))))

(defthm dargp-less-than-of-lookup-equal-alt ;name clash
  (implies (and ;(alistp alist)
                (bounded-darg-listp (strip-cdrs alist) bound)
                (lookup-equal tree alist))
           (dargp-less-than (lookup-equal tree alist) bound))
  :hints (("Goal" :in-theory (e/d (lookup-equal) (dargp-less-than)))))

(local
 (defthm mod-bound-special
   (implies (integerp x)
            (not (< '1048575 (mod x '1048576))))))

(defconst *memoization-size* 1048576) ;todo: allow this to vary (may be best to keep it a power of 2)

;; TODO: Consider using fixnums here (doing the mod [or mask] operation on each addition).
(mutual-recursion

 ;; If TREE is a ground-term, this should return ACC (usually 0).
 ;; TODO: Can variables actually occur in this?
 (defun sum-of-nodenums-aux (tree acc)
   (declare (xargs :guard (and (axe-treep tree)
                               (bounded-axe-treep tree 2147483646)
                               (natp acc)
                               (< acc *memoization-size*))
                   :split-types t)
            (type (integer 0 1048575) acc))
   (if (atom tree)
       (if (symbolp tree)
           acc ;it's a variable
         ;;it's a nodenum
         (logand 1048575 ; 20 ones
                 (+ (the (integer 0 2147483645) tree)
                    acc)))
     (if (eq 'quote (ffn-symb tree))
         acc ;it's a quoted constant
       ;;it's a term:
       (sum-of-nodenums-aux-lst (fargs tree) acc))))

 (defun sum-of-nodenums-aux-lst (trees acc)
   (declare (xargs :guard (and (bounded-axe-tree-listp trees 2147483646)
                               (natp acc)
                               (< acc *memoization-size*))
                   :verify-guards nil ;done below
                   ))
   (if (atom trees)
       acc
     (sum-of-nodenums-aux-lst (cdr trees) (sum-of-nodenums-aux (car trees) acc)))))

(make-flag sum-of-nodenums-aux)

;; (defthm-flag-sum-of-nodenums-aux
;;   (defthm integerp-of-sum-of-nodenums-aux-lst
;;     (implies (and (integerp acc)
;;                   (axe-tree-listp trees))
;;              (integerp (sum-of-nodenums-aux-lst trees acc)))
;;     :flag sum-of-nodenums-aux-lst)
;;   (defthm integerp-of-sum-of-nodenums-aux
;;     (implies (and (integerp acc)
;;                   (axe-treep tree))
;;              (integerp (sum-of-nodenums-aux tree acc)))
;;     :flag sum-of-nodenums-aux))

(defthm-flag-sum-of-nodenums-aux
  (defthm natp-of-sum-of-nodenums-aux-lst
    (implies (and (natp acc)
                  (axe-tree-listp trees))
             (natp (sum-of-nodenums-aux-lst trees acc)))
    :flag sum-of-nodenums-aux-lst)
  (defthm natp-of-sum-of-nodenums-aux
    (implies (and (natp acc)
                  (axe-treep tree))
             (natp (sum-of-nodenums-aux tree acc)))
    :flag sum-of-nodenums-aux))

(defthm-flag-sum-of-nodenums-aux
  (defthm <=-of-sum-of-nodenums-aux-lst
    (implies (and (natp acc)
                  (<= ACC 1048575)
                  (axe-tree-listp trees))
             (<= (sum-of-nodenums-aux-lst trees acc) 1048575))
    :rule-classes (:rewrite :linear)
    :flag sum-of-nodenums-aux-lst)
  (defthm <=-of-sum-of-nodenums-aux
    (implies (and (natp acc)
                  (<= ACC 1048575)
                  (axe-treep tree))
             (<= (sum-of-nodenums-aux tree acc) 1048575))
    :rule-classes (:rewrite :linear)
    :flag sum-of-nodenums-aux))

(verify-guards sum-of-nodenums-aux :hints (("Goal" :in-theory (e/d (axe-tree-listp bounded-axe-tree-listp) (natp)))))



;bozo eventually pass in the memoization length?
;this will be the memo-key
;todo: use logand with a mask instead of mod?
(defund sum-of-nodenums (tree)
  (declare (xargs :guard (tree-to-memoizep tree)
                  :guard-hints (("Goal" :in-theory (enable tree-to-memoizep)))))
  (sum-of-nodenums-aux tree 0))

(defthm natp-of-sum-of-nodenums
  (implies (tree-to-memoizep tree)
           (natp (sum-of-nodenums tree)))
  :hints (("Goal" :in-theory (enable sum-of-nodenums))))

(defthm natp-of-sum-of-nodenums-type
  (implies (tree-to-memoizep tree)
           (natp (sum-of-nodenums tree)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable sum-of-nodenums))))

(defthm sum-of-nodenums-bound
  (implies (tree-to-memoizep tree)
           (<= (sum-of-nodenums tree) 1048575))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable sum-of-nodenums
                                     tree-to-memoizep))))

;;fixme gross to have this hard-coded
;;fixme - use this?
;;todo: consider JVM::UPDATE-NTH-LOCAL JVM::MAKE-FRAME
;(defconst *fns-not-to-memoize* '(step-state-with-pc-and-call-stack-height get-field))

;;;
;;; memo-alistp
;;;

;; Maps trees (that can be memoized) to the nodenums/quoteps to which they rewrote.
(defund memo-alistp (alist)
  (declare (xargs :guard t))
  (and (alistp alist)
       (trees-to-memoizep (strip-cars alist))
       (all-dargp (strip-cdrs alist))))

(defthm memo-alistp-of-cons-of-cons
  (equal (memo-alistp (cons (cons tree result) memo-alist))
         (and (tree-to-memoizep tree)
              (dargp result)
              (memo-alistp memo-alist)))
  :hints (("Goal" :in-theory (enable memo-alistp))))

(local
 (defthm alistp-when-memo-alistp
   (implies (memo-alistp alist)
            (alistp alist))
   :hints (("Goal" :in-theory (enable memo-alistp)))))

(local
 (defthm all-dargp-of-strip-cdrs-when-memo-alistp
   (implies (memo-alistp alist)
            (all-dargp (strip-cdrs alist)))
   :hints (("Goal" :in-theory (enable memo-alistp)))))

(local
 (defthm trees-to-memoizep-of-strip-cars-when-memo-alistp
   (implies (memo-alistp alist)
            (trees-to-memoizep (strip-cars alist)))
   :hints (("Goal" :in-theory (enable memo-alistp)))))

;;;
;;; memoizationp
;;;

(def-typed-acl2-array2 array-of-memo-alistsp (memo-alistp val))

;; Maps tree hashes to memo-alists.
(defund memoizationp (memoization)
  (declare (xargs :guard t))
  (and (array-of-memo-alistsp 'memoization memoization)
       (equal (alen1 'memoization memoization) *memoization-size*)))

;; This allows us to use nil to mean "no memoization".
(defthmd not-memoizationp-of-nil
  (not (memoizationp nil)))

;;;
;;; empty-memoization
;;;

(defund empty-memoization ()
  (declare (xargs :guard t))
  (make-empty-array 'memoization *memoization-size*))

(in-theory (disable (:e empty-memoization)))

(defthm array1p-of-empty-memoization
  (array1p 'memoization (empty-memoization))
  :hints (("Goal" :in-theory (enable empty-memoization))))

(defthm alen1-of-empty-memoization
  (equal (alen1 'memoization (empty-memoization))
         *memoization-size*)
  :hints (("Goal" :in-theory (enable empty-memoization))))

(defthm memoizationp-of-empty-memoization
  (memoizationp (empty-memoization))
  :hints (("Goal" :in-theory (enable empty-memoization memoizationp))))

;;;
;;; add-pair-to-memoization
;;;

;; Record the fact that the TREE rewrote to RESULT.
;; RESULT should be a nodenum/quotep.
;; TODO: Consider not adding certain pairs (see *fns-not-to-memoize*).
(defund add-pair-to-memoization (tree result memoization)
  (declare (xargs :guard (and (tree-to-memoizep tree)
                              (dargp result)
                              (memoizationp memoization))
                  :guard-hints (("Goal" :in-theory (enable memoizationp
                                                           axe-treep-when-tree-to-memoizep
                                                           ;;TREES-TO-MEMOIZEP
                                                           )))))

  (b* ((key (sum-of-nodenums tree))
       (alist-for-key (aref1 'memoization memoization key))
       ;; (- (cw "Memoizing ~x0 -> ~x3 (~x1 items for key ~x2).~%"
       ;;        tree
       ;;        (len alist-for-key)
       ;;        key
       ;;        result))
       (new-alist (acons-fast tree result alist-for-key))
       (memoization (aset1 'memoization memoization key new-alist)))
    memoization))

(defthm memoizationp-of-add-pair-to-memoization
  (implies (and (memoizationp memoization)
                (dargp result)
                (tree-to-memoizep tree))
           (memoizationp (add-pair-to-memoization tree result memoization)))
  :hints (("Goal" :in-theory (e/d (add-pair-to-memoization
                                   memoizationp)
                                  (dargp natp)))))

;;;
;;; add-pairs-to-memoization
;;;

;; Record the fact that all of the TREES rewrote to RESULT.
;; RESULT should be a nodenum/quotep.
(defund add-pairs-to-memoization (trees result memoization)
  (declare (xargs :guard (and (trees-to-memoizep trees)
                              (dargp result)
                              (memoizationp memoization))
                  :guard-hints (("Goal" :in-theory (enable memoizationp
                                                           axe-treep-when-tree-to-memoizep
                                                           ;;TREES-TO-MEMOIZEP
                                                           )))))
  (if (endp trees)
      memoization
    (add-pairs-to-memoization (rest trees)
                              result
                              (add-pair-to-memoization (first trees) result memoization))))

(defthm memoizationp-of-add-pairs-to-memoization
  (implies (and (memoizationp memoization)
                (dargp result)
                (trees-to-memoizep trees))
           (memoizationp (add-pairs-to-memoization trees result memoization)))
  :hints (("Goal" :in-theory (e/d (add-pairs-to-memoization memoizationp trees-to-memoizep
                                                            ;;tree-to-memoizep
                                                            )
                                  (dargp natp)))))

;;;
;;; lookup-in-memoization
;;;

;; Returns a nodenum/quotep (to which the memozation equates TREE), or nil
;; (meaning TREE is not equated to anything in the memoization).
;todo: check *fns-not-to-memoize*?
;todo: can't we sort the memoization by function symbol?
;; Tree must be a function call (possibly a lambda application).
(defund lookup-in-memoization (tree memoization)
  (declare (xargs :guard (and (tree-to-memoizep tree)
                              (memoizationp memoization))
                  :guard-hints (("Goal" :in-theory (enable memoizationp)))))
  (let* ((key (sum-of-nodenums tree))
         (alist-for-key (aref1 'memoization memoization key))
         (res (lookup-equal tree alist-for-key)))
    (progn$ ;; (and res (cw "(Memo hit for ~x0.)~%" tree))
            res)))

(defthm dargp-of-lookup-in-memoization-when-memoizationp
  (implies (and (memoizationp memoization)
                (lookup-in-memoization tree memoization) ;there is a match
                (tree-to-memoizep tree))
           (dargp (lookup-in-memoization tree memoization)))
  :hints (("Goal" :in-theory (e/d (lookup-in-memoization memoizationp)
                                  (dargp)))))

;;;
;;; bounded memoizations
;;;

(defund bounded-memo-alistp (alist bound)
  (declare (xargs :guard (natp bound)))
  (and (memo-alistp alist)
       (bounded-darg-listp (strip-cdrs alist) bound)))

(defthm bounded-memo-alistp-mono
  (implies (and (bounded-memo-alistp alist bound2)
                (<= bound2 bound))
           (bounded-memo-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-memo-alistp))))

(defthm bounded-memo-alistp-implies-memo-alistp
  (implies (bounded-memo-alistp alist bound)
           (memo-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-memo-alistp))))

(defthm bounded-memo-alistp-of-cons-of-cons
  (equal (bounded-memo-alistp (cons (cons tree result) memo-alist) bound)
         (and (tree-to-memoizep tree)
              (dargp-less-than result bound)
              (bounded-memo-alistp memo-alist bound)))
  :hints (("Goal" :in-theory (enable bounded-memo-alistp))))

(defthm dargp-less-than-of-lookup-equal-when-bounded-memo-alistp
  (implies (and (bounded-memo-alistp alist bound)
                (lookup-equal key alist))
           (dargp-less-than (lookup-equal key alist)
                            bound))
  :hints (("Goal" :in-theory (enable bounded-memo-alistp))))

(defthm bounded-memo-alistp-of-nil
  (bounded-memo-alistp nil bound)
  :hints (("Goal" :in-theory (enable bounded-memo-alistp))))

(def-typed-acl2-array2 array-of-bounded-memo-alistsp (bounded-memo-alistp val bound)
  :extra-vars (bound)
  :extra-guards ((natp bound)))

(defund bounded-memoizationp (memoization bound)
  (declare (xargs :guard (natp bound)))
  (and (array-of-bounded-memo-alistsp 'memoization memoization bound)
       (equal (alen1 'memoization memoization) *memoization-size*)))

(defthm array-of-memo-alistsp-aux-when-array-of-bounded-memo-alistsp-aux
  (implies (and (array-of-bounded-memo-alistsp-aux 'memoization memoization max bound)
                (natp max))
           (array-of-memo-alistsp-aux 'memoization memoization max))
  :hints (("Goal" :in-theory (enable array-of-memo-alistsp-aux
                                     array-of-bounded-memo-alistsp-aux))))

(defthm memoizationp-when-bounded-memoizationp
  (implies (bounded-memoizationp memoization bound)
           (memoizationp memoization))
  :hints (("Goal" :in-theory (enable bounded-memoizationp
                                     memoizationp
                                     array-of-bounded-memo-alistsp
                                     array-of-memo-alistsp))))

(defthm bounded-memoizationp-forward-to-memoizationp
  (implies (bounded-memoizationp memoization bound)
           (memoizationp memoization))
  :rule-classes :forward-chaining)

(defthm dargp-less-than-of-lookup-in-memoization-when-bounded-memoizationp
  (implies (and (bounded-memoizationp memoization bound)
                (lookup-in-memoization tree memoization) ;there is a match
                (tree-to-memoizep tree)
                )
           (dargp-less-than (lookup-in-memoization tree memoization) bound))
  :hints (("Goal" :in-theory (e/d (lookup-in-memoization bounded-memoizationp)
                                  (dargp-less-than)))))

(defthm bounded-memoizationp-aux-of-empty-memoization
  (implies (and (symbolp array-name)
                (natp index)
                (posp size)
                (< size 2147483647))
           (array-of-bounded-memo-alistsp-aux array-name
                                         (make-empty-array array-name size)
                                         index
                                         bound))
  :hints (("Goal" :in-theory (enable array-of-bounded-memo-alistsp-aux))))

(defthm bounded-memoizationp-of-empty-memoization
  (bounded-memoizationp (empty-memoization) bound)
  :hints (("Goal" :in-theory (enable bounded-memoizationp empty-memoization))))

(defthm bounded-memoizationp-of-add-pair-to-memoization
  (implies (and (bounded-memoizationp memoization bound)
                (dargp-less-than result bound)
                (tree-to-memoizep tree))
           (bounded-memoizationp (add-pair-to-memoization tree result memoization) bound))
  :hints (("Goal" :in-theory (e/d (add-pair-to-memoization
                                   ;memoizationp
                                   bounded-memoizationp)
                                  (dargp natp)))))

(defthm bounded-memoizationp-of-add-pairs-to-memoization
  (implies (and (bounded-memoizationp memoization bound)
                (dargp-less-than result bound)
                (trees-to-memoizep trees))
           (bounded-memoizationp (add-pairs-to-memoization trees result memoization) bound))
  :hints (("Goal" :in-theory (e/d (add-pairs-to-memoization
;bounded-memoizationp trees-to-memoizep tree-to-memoizep
                                   )
                                  (;dargp-less-than
                                   natp)))))

;same index, different bound
(defthm array-of-bounded-memo-alistsp-aux-monotone2
  (implies (and (array-of-bounded-memo-alistsp-aux array-name array n bound2)
                (<= bound2 bound)
                (integerp n))
           (array-of-bounded-memo-alistsp-aux array-name array n bound))
  :hints
  (("Goal" :in-theory (enable array-of-bounded-memo-alistsp-aux))))

(defthm bounded-memoizationp-monotone
  (implies (and (bounded-memoizationp memoization bound2)
                (<= bound2 bound))
           (bounded-memoizationp memoization bound))
  :hints (("Goal" :in-theory (enable bounded-memoizationp
                                     array-of-bounded-memo-alistsp))))

;;;
;;; maybe-memoizationp
;;;

;; Recognizes an object that is a memoization or nil (meaning no memoization).
(defund maybe-memoizationp (memoization)
  (declare (xargs :guard t))
  (or (eq nil memoization)
      (memoizationp memoization)))

(defthm maybe-memoizationp-forward-to-memoizationp
  (implies (and (maybe-memoizationp memoization)
                memoization)
           (memoizationp memoization))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-memoizationp))))

(defthm maybe-memoizationp-of-add-pairs-to-memoization
  (implies (and (maybe-memoizationp memoization)
                memoization
                (dargp tree)
                (trees-to-memoizep trees-equal-to-tree))
           (maybe-memoizationp (add-pairs-to-memoization trees-equal-to-tree tree memoization)))
  :hints (("Goal" :in-theory (enable maybe-memoizationp))))

(defthmd memoizationp-when-maybe-memoizationp
  (implies (and (maybe-memoizationp memoization)
                memoization)
           (memoizationp memoization))
  :hints (("Goal" :in-theory (enable maybe-memoizationp))))


;;;
;;; maybe-bounded-memoizationp
;;;

;; Recognizes an object that is a bounded-memoization or nil (meaning no memoization).
(defund maybe-bounded-memoizationp (memoization bound)
  (declare (xargs :guard (natp bound)))
  (or (eq nil memoization)
      (bounded-memoizationp memoization bound)))

(defthm maybe-bounded-memoizationp-of-empty-memoization
  (maybe-bounded-memoizationp (empty-memoization) bound)
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp))))

(defthm maybe-bounded-memoizationp-of-nil
  (maybe-bounded-memoizationp nil bound)
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp))))

(defthm maybe-bounded-memoizationp-forward-to-bounded-memoizationp
  (implies (and (maybe-bounded-memoizationp memoization bound)
                memoization)
           (bounded-memoizationp memoization bound))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp))))

(defthm maybe-bounded-memoizationp-of-add-pairs-to-memoization
  (implies (and (dargp-less-than tree bound)
                (trees-to-memoizep trees-equal-to-tree)
                (maybe-bounded-memoizationp memoization bound)
                memoization ; todo?
                )
           (maybe-bounded-memoizationp (add-pairs-to-memoization trees-equal-to-tree tree memoization) bound))
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp))))

(defthm maybe-memoizationp-when-maybe-bounded-memoizationp
  (implies (maybe-bounded-memoizationp memoization bound)
           (maybe-memoizationp memoization))
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp maybe-memoizationp))))

(defthm maybe-bounded-memoizationp-monotone
  (implies (and (maybe-bounded-memoizationp memoization bound2)
                (<= bound2 bound))
           (maybe-bounded-memoizationp memoization bound))
  :hints (("Goal" :in-theory (enable maybe-bounded-memoizationp))))

;;;
;;; print-memo-stats
;;;

;; these may not all be symbols if a term is a lambda-application.  the result includes 'quote for constants
(defund head-function-symbols (terms)
  (declare (xargs :guard  t;(pseudo-term-listp terms)
                  ))
  (if (atom terms)
      nil
    (let ((term (first terms)))
      (if (variablep term)
          ;; no head symbol, so we have to skip it
          (head-function-symbols (rest terms))
        (let ((fn (ffn-symb term)))
          (cons (if (symbolp fn)
                    fn
                  :lambda)
                (head-function-symbols (rest terms))))))))

(defthm symbol-listp-of-head-function-symbols
  (symbol-listp (head-function-symbols terms))
  :hints (("Goal" :in-theory (enable head-function-symbols))))

(defund print-memo-stats-aux (n memoization total-items longest-slot longest-slot-len last-filled-slot memo-count-world)
  (declare (xargs :measure (nfix (- *memoization-size* n))
                  :hints (("Goal" :in-theory (enable natp)))
                  :guard (and (memoizationp memoization)
                              (natp n)
                              (natp total-items)
                              (natp longest-slot-len)
                              (natp longest-slot)
                              (< longest-slot *memoization-size*)
                              (symbol-count-worldp memo-count-world))
                  :guard-hints (("Goal" :in-theory (enable memoizationp)))))
  (if (or (not (mbt (natp n)))
          (<= *memoization-size* n))
      (let* ((contents-of-slot-0 (aref1 'memoization memoization 0)) ;; where ground terms go
             (len-of-slot0 (len contents-of-slot-0))
             (contents-of-longest-slot (aref1 'memoization memoization longest-slot))
             (len-of-longest-slot (len contents-of-longest-slot)))
        (progn$ (cw "~%(Memo stats:~%")
                (cw "Memo items: ~x0.~%" total-items)
                (cw "Index with the most items : ~x0 (~x1 items)~%" longest-slot longest-slot-len)
                (cw "Last used index: ~x0.~%" last-filled-slot)
                (cw "Items at index 0: ~x0.~%" len-of-slot0)
                (cw "First few items at index 0: ~x0~%" (if (< 20 len-of-slot0)
                                                            (take 20 (true-list-fix contents-of-slot-0))
                                                          contents-of-slot-0))
                (cw "First few items at index ~x0: ~x1~%" longest-slot
                    (if (< 20 len-of-longest-slot)
                        (take 20 (true-list-fix contents-of-longest-slot))
                      contents-of-longest-slot))
                (cw "Last few items at index ~x0: ~x1~%" longest-slot
                    (nthcdr (if (< 20 len-of-longest-slot) (- len-of-longest-slot 20) 0)
                            (true-list-fix contents-of-longest-slot)))
                (cw "Head symbol counts in memoization:~%")
                (cw "~X01" (summarize-symbol-count-world memo-count-world) nil)
                ;; (cw "(Longest slot entries: ~X01)~%" (and (natp longest-slot)
                ;;                                           (< longest-slot *memoization-size*) ;for guards
                ;;                                           (aref1 'memoization memoization longest-slot))
                ;;     nil)
                (cw ")~%")))
    (let* ((slot-items (aref1 'memoization memoization n))
           (num-items (len slot-items)))
      (print-memo-stats-aux (+ 1 n)
                            memoization
                            (+ total-items num-items)
                            (if (< longest-slot-len num-items)
                                n
                              longest-slot)
                            (max num-items longest-slot-len)
                            (if (< 0 num-items)
                                n
                              last-filled-slot)
                            ;; todo: avoid the strip-cars:
                            (increment-counts-in-symbol-count-world (head-function-symbols (strip-cars slot-items)) 'memo-count-world memo-count-world)))))

;; Gather and print statistics about the contents of the memoization.
;; Logically returns nil.
(defund print-memo-stats (memoization)
  (declare (xargs :guard (maybe-memoizationp memoization)
                  :guard-hints (("Goal" :in-theory (enable maybe-memoizationp
                                                           memoizationp)))))
  (if (eq nil memoization)
      (cw "(There is no memoization to print.)~%")
    (let* ((contents-of-slot-0 (aref1 'memoization memoization 0)) ;; where ground terms go
           (len-of-slot0 (len contents-of-slot-0))
           (memo-count-world (empty-symbol-count-world 'memo-count-world)))
      (print-memo-stats-aux 1
                            memoization
                            len-of-slot0 ; total-items
                            0            ; longest-slot
                            len-of-slot0 ; longest-slot-len
                            (if contents-of-slot-0 0 -1)
                            (increment-counts-in-symbol-count-world (head-function-symbols (strip-cars contents-of-slot-0))
                                                                    'memo-count-world
                                                                    memo-count-world)))))
