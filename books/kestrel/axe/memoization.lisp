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
;; where the hash of an object is the sum of the nodenums in the object modulo
;; *memoization-size*.

(include-book "tools/flag" :dir :system)
;(include-book "arrays-of-alists")
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "axe-trees")
(include-book "count-worlds")
(include-book "all-dargp")
(include-book "all-dargp-less-than")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

;; TODO: Consider using a stobj for the memoization, perhaps with a Lisp hash table.
;; TODO: Consider not memoizing things with unsimplified args? (that seemed to slow things down)
;; TODO: Consider whether to memoize rewrites of lambda applications (but not memoizing them slowed things down?)
;; TODO: Consider whether to memoize rewrites of ground terms
;; TODO: Consider using an info world for the memoization (to make it per head symbol)
;; TODO: Consider memoizing only destructor trees, not constructor trees
;; NOTE: For anything we won't memoize, we should avoid consing it onto tree-equal-to-tree in the rewriter

;maybe we should think of the memoization as part of the dag (it is just a list of equalities which mention nodenums from the dag)

(local (in-theory (disable mod)))

;; Recognize an axe-tree that is a cons
(defund tree-to-memoizep (tree)
  (declare (xargs :guard t))
  (and (axe-treep tree)
       (consp tree)))

(defthm tree-to-memoizep-when-axe-treep
  (implies (axe-treep tree)
           (equal (tree-to-memoizep tree)
                  (and (consp tree))))
  :hints (("Goal" :in-theory (e/d (tree-to-memoizep) (axe-treep)))))

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

(defthm dargp-of-lookup-equal-alt ;name clash
  (implies (and ;(alistp alist)
                (all-dargp (strip-cdrs alist))
                (lookup-equal tree alist))
           (dargp (lookup-equal tree alist)))
  :hints (("Goal" :in-theory (e/d (lookup-equal assoc-equal) (dargp)))))

(defthm dargp-less-than-of-lookup-equal-alt ;name clash
  (implies (and ;(alistp alist)
                (all-dargp-less-than (strip-cdrs alist) bound)
                (lookup-equal tree alist))
           (dargp-less-than (lookup-equal tree alist) bound))
  :hints (("Goal" :in-theory (e/d (lookup-equal) (dargp-less-than)))))

(local
 (defthm mod-bound-special
   (implies (integerp x)
            (not (< '1048575 (mod x '1048576))))))

;; TODO: Consider using fixnums here (doing the mod [or mask] operation on each addition).
(mutual-recursion
 (defun sum-of-nodenums-aux-lst (objects acc)
   (declare (xargs :guard (and (all-axe-treep objects)
                               (natp acc))
                   :verify-guards nil ;done below
                   ))
   (if (atom objects)
       acc
     (sum-of-nodenums-aux-lst (cdr objects) (sum-of-nodenums-aux (car objects) acc))))

 ;; If OBJECT is a ground-term, this should return ACC (usually 0).
 (defun sum-of-nodenums-aux (object acc)
   (declare (xargs :guard (and (axe-treep object)
                               (natp acc))))
   (if (atom object)
       (if (symbolp object)
           acc ;it's a variable
         ;;it's a nodenum
         (+ object acc))
     (if (eq 'quote (ffn-symb object))
         acc ;it's a quoted constant
       ;;it's a term:
       (sum-of-nodenums-aux-lst (fargs object) acc)))))

(make-flag sum-of-nodenums-aux)

(defthm-flag-sum-of-nodenums-aux
  (defthm integerp-of-sum-of-nodenums-aux-lst
    (implies (and (integerp acc)
                  (all-axe-treep objects))
             (integerp (sum-of-nodenums-aux-lst objects acc)))
    :flag sum-of-nodenums-aux-lst)
  (defthm integerp-of-sum-of-nodenums-aux
    (implies (and (integerp acc)
                  (axe-treep object))
             (integerp (sum-of-nodenums-aux object acc)))
    :flag sum-of-nodenums-aux))

(defthm-flag-sum-of-nodenums-aux
  (defthm natp-of-sum-of-nodenums-aux-lst
    (implies (and (natp acc)
                  (all-axe-treep objects))
             (natp (sum-of-nodenums-aux-lst objects acc)))
    :flag sum-of-nodenums-aux-lst)
  (defthm natp-of-sum-of-nodenums-aux
    (implies (and (natp acc)
                  (axe-treep object))
             (natp (sum-of-nodenums-aux object acc)))
    :flag sum-of-nodenums-aux))

(verify-guards sum-of-nodenums-aux :hints (("Goal" :in-theory (e/d (all-axe-treep) (natp)))))

(defconst *memoization-size* 1048576) ;todo: allow this to vary (may be best to keep it a power of 2)

;bozo eventually pass in the memoization length?
;this will be the memo-key
;todo: use logand with a mask instead of mod?
(defund sum-of-nodenums (object)
  (declare (xargs :guard (axe-treep object)))
  (mod (sum-of-nodenums-aux object 0)
       *memoization-size*))

(defthm natp-of-sum-of-nodenums
  (implies (axe-treep object)
           (natp (sum-of-nodenums object)))
  :hints (("Goal" :in-theory (enable sum-of-nodenums))))

(defthm sum-of-nodenums-bound
  (implies (axe-treep object)
           (<= (sum-of-nodenums object) 1048575))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable sum-of-nodenums))))

;;fixme gross to have this hard-coded
;;fixme - use this?
;;todo: consider JVM::UPDATE-NTH-LOCAL JVM::MAKE-FRAME
;(defconst *fns-not-to-memoize* '(step-state-with-pc-and-call-stack-height get-field))

;;;
;;; memoizationp
;;;

(def-typed-acl2-array2 array-of-memo-alistsp (and (alistp val) (all-dargp (strip-cdrs val))))

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
;;; add-pairs-to-memoization
;;;

;; Record the fact that all of the OBJECTS rewrote to RESULT.
;; RESULT should be a nodenum/quotep.
(defund add-pairs-to-memoization (objects result memoization)
  (declare (xargs :guard (and (trees-to-memoizep objects)
                              (dargp result)
                              (memoizationp memoization))
                  :guard-hints (("Goal" :in-theory (enable memoizationp
                                                           TREES-TO-MEMOIZEP)))))
  (if (endp objects)
      memoization
    ;;test *fns-not-to-memoize*?
    (let ((object (first objects)))
      ;;associate object with result in the memoization
      (if (not (consp object)) ;; todo: remove this check
          (er hard? 'add-pairs-to-memoization "Unexpected object: ~x0." object)
        (b* ((key (sum-of-nodenums object))
             (alist-for-key (aref1 'memoization memoization key))
             ;; (- (cw "Memoizing ~x0 -> ~x3 (~x1 items for key ~x2).~%"
             ;;        object
             ;;        (len alist-for-key)
             ;;        key
             ;;        result))
             (new-alist (acons-fast object result alist-for-key))
             (memoization (aset1 'memoization memoization key new-alist)))
          (add-pairs-to-memoization (cdr objects) result memoization))))))

(defthm memoizationp-of-add-pairs-to-memoization
  (implies (and (memoizationp memoization)
                (dargp result)
                (trees-to-memoizep objects))
           (memoizationp (add-pairs-to-memoization objects result memoization)))
  :hints (("Goal" :in-theory (e/d (add-pairs-to-memoization memoizationp trees-to-memoizep tree-to-memoizep)
                                  (dargp natp)))))

;;;
;;; lookup-in-memoization
;;;

;returns nil or a nodenum/quotep
;bozo check *fns-not-to-memoize*
;can't we sort the memoization by function symbol?
;; Object must be a function call (possibly a lambda application)
(defund lookup-in-memoization (object memoization)
  (declare (xargs :guard (and (tree-to-memoizep object)
                              (memoizationp memoization))
                  :guard-hints (("Goal" :in-theory (enable memoizationp)))))
  (let* ((key (sum-of-nodenums object))
         (alist-for-key (aref1 'memoization memoization key))
         (res (lookup-equal object alist-for-key)))
    res
    ;; (if res
    ;;     (progn$ (cw "(Memo hit for ~x0.)~%" object)
    ;;             res)
    ;;   nil)
    ))

(defthm dargp-of-lookup-in-memoization-when-memoizationp
  (implies (and (memoizationp memoization)
                (lookup-in-memoization tree memoization) ;there is a match
                (axe-treep tree))
           (dargp (lookup-in-memoization tree memoization)))
  :hints (("Goal" :in-theory (e/d (lookup-in-memoization memoizationp)
                                  (dargp)))))

;;;
;;; bounded memoizations
;;;

(def-typed-acl2-array2 array-of-bounded-memo-alistsp (and (alistp val) (all-dargp-less-than (strip-cdrs val) bound))
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
                (axe-treep tree)
                )
           (dargp-less-than (lookup-in-memoization tree memoization) bound))
  :hints (("Goal" :in-theory (e/d (LOOKUP-IN-MEMOIZATION BOUNDED-MEMOIZATIONP)
                                  (DARGP-LESS-THAN)))))

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

(defthm bounded-memoizationp-of-add-pairs-to-memoization
  (implies (and (bounded-memoizationp memoization bound)
                (dargp-less-than result bound)
                (trees-to-memoizep objects))
           (bounded-memoizationp (add-pairs-to-memoization objects result memoization) bound))
  :hints (("Goal" :in-theory (e/d (add-pairs-to-memoization bounded-memoizationp trees-to-memoizep tree-to-memoizep)
                                  (dargp-less-than natp)))))

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

;; Representations a memoization or nil (meaning no memoization).
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

;; Representations a memoization or nil (meaning no memoization).
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
                memoization)
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
        (progn$ (cw "(Memo stats:~%")
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
