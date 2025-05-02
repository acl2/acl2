; Calling STP to prove things about DAGs and terms
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

;; TODO: Consider simplifying first with the pre-stp rules (but that would make
;; this depend on a whole rewriter).

(include-book "axe-clause-utilities") ; for handle-constant-disjuncts and expressions-for-this-case
(include-book "depth-array")
(include-book "translate-dag-to-stp") ; has ttags
;(include-book "conjunctions-and-disjunctions") ; for get-axe-disjunction-from-dag-items
(include-book "make-term-into-dag-array-basic") ;for make-terms-into-dag-array-basic
(include-book "kestrel/utilities/wrap-all" :dir :system)
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "unify-tree-and-dag")
(include-book "dag-array-printing")
(include-book "worklists")
(include-book "merge-sort-less-than")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-lists" :dir :system))
(local (include-book "kestrel/utilities/make-ord" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/bv-lists/bv-arrays" :dir :system))
(local (include-book "kestrel/bv/bvlt" :dir :system))

;; We have developed a connection between the ACL2 theorem prover, on which
;; most of our tools are based, and the STP SMT solver.  This allows us to take
;; advantage of STP's highly efficient reasoning about the theory of
;; bit-vectors and arrays (which can model many commonly-used programming
;; constructs).  The process begins by applying the Axe rewriter to simplify
;; the DAG to be proved as much as possible with respect to assumptions
;; provided by the user.  It then represents the full claim to be proved as a
;; disjunction, attempting to prove that either the conclusion is true, or one
;; of the assumptions is false.  The tool must address the fact that the DAG
;; may not entirely consist of operations in STP's theory.  (STP handles
;; operators over bit-vectors, such as BVPLUS, and bit-vector arrays, such as
;; BV-ARRAY-READ.  Other operators must be abstracted away to variables of
;; types that STP can handle (possibly also booleans).  The abstracted nodes
;; become variables in the STP query, so the tool also must determine types
;; (that STP can handle) for them.  It does this using two sources of
;; information: information implied by negated disjuncts (which is safe to use
;; since if any disjunct is actually true, then it suffices to prove the entire
;; disjunction), and information determined by looking at how the terms to be
;; abstracted are used (e.g., how many bits of the term are ever used, which is
;; safe because the bit-vector operators carry explicit size parameters and
;; ``chop'' their arguments down to size before operating on them).  The
;; translation to STP also supports heuristically cutting out (abstracting)
;; nodes in the DAG deemed unlikely to contribute to the proof; it can even
;; perform a binary search on the ``cut depth'' to attempt to find an
;; appropriate abstraction level (abstract away too much and the STP goal may
;; no longer be true, abstract away too little and the solver may time out).

;; We now parse, process, and return the counter-examples found by STP.  This
;; forms the basis of our query answering capability; we pose a query to STP
;; that attempts to prove that some behavior is impossible, and it returns a
;; concrete input showing when the behavior is in fact possible.

(local (in-theory (disable state-p w
                           symbol-alistp
                           ;; for speed:
                           nth-when-not-consp-cheap
                           default-cdr
                           len-when-not-consp-cheap
                           all-natp-when-not-consp
                           nth-of-cdr
                           ;; cadr-becomes-nth-of-1 ; we want to keep the cdr because it gets the fargs
                           ;;consp-from-len-cheap
                           ;;memberp-nth-when-perm
                           ;;dargp-less-than
                           consp-from-len-cheap
                           default-car
                           all-<-when-not-consp
                           eqlable-alistp ;prevent inductions
                           )))

(local (in-theory (enable <-of-+-of-1-when-integers
                          posp
                          true-listp-of-cdr-when-dag-exprp-and-quotep
                          ceiling-in-terms-of-floor
                          true-listp-of-cdr
                          nth-of-cdr
                          car-when-alistp-iff)))

;; ;the nth-1 is to unquote
;; (defthmd bv-typep-of-maybe-get-type-of-val-of-nth-1
;;   (implies (and (bv-arg-okp arg)
;;                 (consp arg) ;it's a quotep
;;                 )
;;            (bv-typep (maybe-get-type-of-val (nth 1 arg))))
;;   :hints (("Goal" :in-theory (enable maybe-get-type-of-val bv-arg-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthmd all-<-of-keep-nodenum-dargs-when-darg-listp
;;   (implies (darg-listp x)
;;            (equal (all-< (keep-nodenum-dargs x) bound)
;;                   (bounded-darg-listp x bound)))
;;   :hints (("Goal" :in-theory (enable keep-nodenum-dargs))))

;; (local (in-theory (enable all-<-of-keep-nodenum-dargs-when-darg-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm rationalp-when-natp
    (implies (natp x)
             (rationalp x))))

;move
(local
 (defthm nat-listp-of-reverse-list
  (equal (nat-listp (reverse-list x))
         (all-natp x))
  :hints (("Goal" :in-theory (enable nat-listp reverse-list)))))

;; (local
;;   (defthmd member-equal-of-constant-when-not-equal-of-nth-0
;;     (implies (and (consp x) ; avoid loops
;;                   (not (equal a (nth 0 x))))
;;              (equal (member-equal a x)
;;                     (member-equal a (cdr x))))
;; ;  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
;;     :hints (("Goal" :in-theory (enable member-equal)))))

;todo: move and rename the non-cheap one to start with not-
(local
  (defthm not-member-equal-when-not-consp
    (implies (not (consp x))
             (not (member-equal a x)))
    :hints (("Goal" :in-theory (enable member-equal)))))

(local
  (defthmd member-equal-when-consp-iff
    (implies (consp lst) ; avoids loops
             (iff (member-equal x lst)
                  (or (equal x (car lst))
                      (member-equal x (cdr lst)))))))

;move
;make into an iff rule
(defthm assoc-equal-when-member-equal-of-strip-cars
  (implies (and (member-equal key (strip-cars alist))
                (or key
                    (alistp alist)))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable member-equal assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defthmd myquotep-when-axe-disjunctionp
  (implies (axe-disjunctionp d)
           (equal (myquotep d)
                  (or (equal (true-disjunction) d)
                      (equal (false-disjunction) d))))
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

;move
(defthmd quotep-when-axe-disjunctionp
  (implies (axe-disjunctionp d)
           (equal (quotep d)
                  (or (equal (true-disjunction) d)
                      (equal (false-disjunction) d))))
  :hints (("Goal" :in-theory (enable axe-disjunctionp))))

;move
(defthmd bounded-possibly-negated-nodenumsp-when-nat-listp
  (implies (nat-listp items)
           (equal (bounded-possibly-negated-nodenumsp items bound)
                  (all-< items bound)))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenump
                                     all-<))))

(defthm no-nodes-are-variablesp-of-merge-<
  (implies (and (no-nodes-are-variablesp l1 dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp l2 dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp acc dag-array-name dag-array dag-len))
           (no-nodes-are-variablesp (merge-< l1 l2 acc) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable merge-< revappend-becomes-append-of-reverse-list no-nodes-are-variablesp))))

(defthm no-nodes-are-variablesp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (no-nodes-are-variablesp lst dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp tail dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp acc dag-array-name dag-array dag-len)
                (<= (len tail) (len lst)))
           (no-nodes-are-variablesp (mv-nth 0 (split-list-fast-aux lst tail acc)) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (e/d (split-list-fast-aux no-nodes-are-variablesp) (natp)))))

(defthm no-nodes-are-variablesp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (no-nodes-are-variablesp lst dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp tail dag-array-name dag-array dag-len)
                (no-nodes-are-variablesp acc dag-array-name dag-array dag-len)
                (<= (len tail) (len lst)))
           (no-nodes-are-variablesp (mv-nth 1 (split-list-fast-aux lst tail acc)) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable split-list-fast-aux no-nodes-are-variablesp))))

(defthm no-nodes-are-variablesp-of-mv-nth-0-of-split-list-fast
  (implies (no-nodes-are-variablesp l dag-array-name dag-array dag-len)
           (no-nodes-are-variablesp (mv-nth 0 (split-list-fast l)) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable split-list-fast no-nodes-are-variablesp))))

(defthm no-nodes-are-variablesp-of-mv-nth-1-of-split-list-fast
  (implies (no-nodes-are-variablesp l dag-array-name dag-array dag-len)
           (no-nodes-are-variablesp (mv-nth 1 (split-list-fast l)) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable split-list-fast no-nodes-are-variablesp))))

(defthm no-nodes-are-variablesp-of-merge-sort-<
  (implies (no-nodes-are-variablesp x dag-array-name dag-array dag-len)
           (no-nodes-are-variablesp (merge-sort-< x) dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable merge-sort-< no-nodes-are-variablesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthmd equal-of-cons (equal (equal x (cons y z)) (and (consp x) (equal (car x) y) (equal (cdr x) z)))))

;move?
(defthm equal-of-car-of-get-axe-disjunction-from-dag-items-and-quote
  (implies (and (bounded-possibly-negated-nodenumsp items dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (equal (equal (car (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len)) 'quote)
                  (or (equal (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len) *t*)
                      (equal (get-axe-disjunction-from-dag-items items dag-array-name dag-array dag-len) *nil*))))
  :hints (("Goal" :use (axe-disjunctionp-of-get-axe-disjunction-from-dag-items)
           :in-theory (e/d (axe-disjunctionp possibly-negated-nodenumsp booleanp equal-of-cons) (axe-disjunctionp-of-get-axe-disjunction-from-dag-items)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defthmd bounded-axe-disjunctionp-when-bounded-possibly-negated-nodenumsp
  (implies (bounded-possibly-negated-nodenumsp disjuncts bound)
           (bounded-axe-disjunctionp disjuncts bound))
  :hints (("Goal" :in-theory (enable bounded-axe-disjunctionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; todo?
;; (local
;;  (defthm <-of--1-and-maxelem
;;   (implies (and (all-natp x)
;;                 (consp x))
;;            (< -1 (MAXELEM x)))))

;; ;dup
;; (local
;;  (defthm maxelem-bound
;;   (implies (and (all-natp x)
;;                 (consp x))
;;            (<= 0 (maxelem x)))))

;FIXME: Some functions in this file should call remove-temp-dir (think about exactly which ones), ideally using acl2-unwind-protect as well

;;;
;;; unify-tree-with-any-dag-node-no-wrap
;;;

;returns (mv success-flg matching-item extended-alist)
;; TODO: Avoid passing in dag-len?
(defund unify-tree-with-any-dag-node-no-wrap (tree nodenums-or-quoteps dag-array dag-len alist-acc)
  (declare (xargs :guard (and (axe-treep tree)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-darg-listp nodenums-or-quoteps dag-len)
                              (symbol-alistp alist-acc))))
  (if (atom nodenums-or-quoteps)
      (mv nil nil nil)
    (let ((fail-or-extended-alist (unify-tree-with-dag-node tree (first nodenums-or-quoteps) dag-array alist-acc)))
      (if (not (eq :fail fail-or-extended-alist))
          (mv t (first nodenums-or-quoteps) fail-or-extended-alist)
        (unify-tree-with-any-dag-node-no-wrap tree (rest nodenums-or-quoteps) dag-array dag-len alist-acc)))))

(local
  (defthm alistp-of-mv-nth-2-of-unify-tree-with-any-dag-node-no-wrap
    (implies (alistp alist-acc)
             (alistp (mv-nth 2 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc))))
    :hints (("Goal" :in-theory (enable unify-tree-with-any-dag-node-no-wrap)))))

(local
  (defthm darg-listp-of-strip-cdrs-of-unify-tree-with-any-dag-node-no-wrap
    (implies (and (axe-treep tree)
                  (bounded-darg-listp nodenums-or-quoteps dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (darg-listp (strip-cdrs alist-acc))
                  (symbol-alistp alist-acc))
             (darg-listp (strip-cdrs (mv-nth 2 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc)))))
    :hints (("subgoal *1/2" :cases ((consp (CAR NODENUMS-OR-QUOTEPS))))
            ("Goal" :in-theory (enable unify-tree-with-any-dag-node-no-wrap)))))

(local
  (defthm unify-tree-with-any-dag-node-no-wrap-binds-all
    (implies (and (axe-treep tree)
                  (bounded-darg-listp nodenums-or-quoteps dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (darg-listp (strip-cdrs alist-acc))
                  (symbol-alistp alist-acc)
                  (mv-nth 0 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc)))
             (subsetp-equal (axe-tree-vars tree) (strip-cars (mv-nth 2 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc)))))
    :hints (("Goal" :in-theory (enable unify-tree-with-any-dag-node-no-wrap)))))

(local
  (defthm assoc-equal-of-strip-cars-of-unify-tree-with-any-dag-node-no-wrap-binds-all
    (implies (and (member-equal var (axe-tree-vars tree))
                  (axe-treep tree)
                  (bounded-darg-listp nodenums-or-quoteps dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (darg-listp (strip-cdrs alist-acc))
                  (symbol-alistp alist-acc)
                  (mv-nth 0 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc)))
             (assoc-equal var (mv-nth 2 (unify-tree-with-any-dag-node-no-wrap tree nodenums-or-quoteps dag-array dag-len alist-acc))))
    :hints (("Goal" :use (:instance unify-tree-with-any-dag-node-no-wrap-binds-all)
             :in-theory (e/d (assoc-equal-iff-member-equal-of-strip-cars)
                             (unify-tree-with-any-dag-node-no-wrap-binds-all))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv hyps conc).
;; (See also get-hyps-and-conc.  That one can handle some nested calls implies.  Should we use it?)
(defund term-hyps-and-conc (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq 'implies (ffn-symb term))
           (eql 2 (len (fargs term)))) ;for guards
      (mv (get-conjuncts (farg1 term))
          (farg2 term))
    (mv nil ;no hyps
        term)))

(defthm pseudo-term-listp-of-mv-nth-0-of-term-hyps-and-conc
  (implies (pseudo-termp term)
           (pseudo-term-listp (mv-nth 0 (term-hyps-and-conc term))))
  :hints (("Goal" :in-theory (enable term-hyps-and-conc))))

(defthm pseudo-termp-of-mv-nth-1-of-term-hyps-and-conc
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 1 (term-hyps-and-conc term))))
  :hints (("Goal" :in-theory (enable term-hyps-and-conc))))

(defconst *default-stp-max-conflicts* 60000) ; this is the number of conflicts, not seconds

;; Here we attempt to assign bv/array/boolean types to non-pure nodes, given the information in the literals.  We seek literals of the form (not <foo>) where <foo> assigns a type to some non-pure node.  In such a case, it is sound to assume <foo> because if <foo> is false, then (not <foo>) is true, and the whole clause is true.  The kinds of <foo> that can assign a type to node <x> are:
;; (booleanp <x>)
;; (unsigned-byte-p <size> <x>)
;; ... something for array types ...
;; (equal <x> <something-which-has-been-assigned-a-type-or-is-bv/array/bool>)
;; (equal <something-which-has-been-assigned-a-type-or-is-bv/array/bool> <x>)

;multiple passes may be required (e.g., to propagate types through chains of items that are equal to each other)
;we don't assign types to bv/array/bool nodes
;what about intersecting types?  what about incompatible types?  warning or error?
;; walks through the literals and assembles a nodenum-type-alist, throwing out the literals used for that purpose (no?!)
;; the things given types by the alist need not be variables (but may be replaced by vars during translation)
;; returns (mv nodenum-type-alist non-type-literal-nodenums)
;; what should we do with array types, which might be expressed by several literals (one for the element width, one for the length, one for true-listp, etc.)?
;ffixme what about nodes which are always used in bv argument positions but aren't given types by usb literals (and similar issue for arrays)?
;; (defun known-nodenum-type-alist (literal-nodenums dag-array nodenum-type-alist-acc non-type-literal-nodenums-acc)
;;   (declare (xargs :measure (+ 1 (len literal-nodenums))))
;;   (if (endp literal-nodenums)
;;       (mv nodenum-type-alist-acc non-type-literal-nodenums-acc)
;;     (let ((nodenum (first literal-nodenums)))
;;       (mv-let (match alist)
;;               (unify-tree-with-dag-node '(not (unsigned-byte-p (:free size) (:free item))) nodenum dag-array nil)
;;               (if match
;;                   (let ((item (lookup-eq 'item alist))
;;                         (size (lookup-eq 'size alist)))
;;                     (if (and (quotep size)
;;                              (integerp item))
;;                         ;;ffixme what if there are multiple different types for the item?
;;                         (known-nodenum-type-alist (cdr literal-nodenums)
;;                                                   dag-array
;;                                                   (acons-fast item
;;                                                               (make-bv-type (unquote size))
;;                                                               nodenum-type-alist-acc)
;;                                                   non-type-literal-nodenums-acc)
;;                       ;;not of the right form:
;;                       (known-nodenum-type-alist (cdr literal-nodenums) dag-array nodenum-type-alist-acc
;;                                                 (cons nodenum non-type-literal-nodenums-acc))))
;;                 (mv-let (match alist)
;;                         (unify-tree-with-dag-node '(not (all-unsigned-byte-p (:free size) (:free item))) nodenum dag-array nil)
;;                         (let ((item (lookup-eq 'item alist))
;;                               (size (lookup-eq 'size alist)))
;;                           (if (or (not match)
;;                                   (not (quotep size))
;;                                   (not (< 0 (unquote size))) ;new
;;                                   (not (integerp item)))
;;                               ;;not of the right form:
;;                               (known-nodenum-type-alist (cdr literal-nodenums) dag-array nodenum-type-alist-acc
;;                                                         (cons nodenum non-type-literal-nodenums-acc))
;;                             ;;we've found an all-unsigned-byte-p claim (half of what we need for an array) ffixme do we need true-listp?
;;                             ;;now go see if there is a corresponding length claim
;;                             ;;it may be in either the literals already processed or the ones to come
;;                             (mv-let (found-a-len-claim nodenum-with-len-claim alist)
;;                                     (unify-tree-with-any-dag-node `(not (equal (:free len) (len ,item))) ;we instantiate item in this
;;                                                                   (append literal-nodenums non-type-literal-nodenums-acc)
;;                                                                   dag-array alist)
;;                                     (let ((len (lookup-eq 'len alist)))
;;                                       (if (or (not found-a-len-claim)
;;                                               (not (quotep len)))
;;                                           (known-nodenum-type-alist (cdr literal-nodenums) dag-array nodenum-type-alist-acc
;;                                                                     (cons nodenum non-type-literal-nodenums-acc))
;; ;we've found an unsigned-byte-p claim and a len claim:
;;                                         (prog2$ nil ;(cw "adding array type entry from nodes ~x0 and ~x1~%" nodenum nodenum-with-len-claim)
;;                                                 (known-nodenum-type-alist (remove nodenum-with-len-claim (cdr literal-nodenums))
;;                                                                           dag-array
;;                                                                           (acons-fast item
;;                                                                                       `(array ,(unquote size) ,(unquote len))
;;                                                                                       nodenum-type-alist-acc)
;;                                                                           (remove nodenum-with-len-claim non-type-literal-nodenums-acc))))))))))))))

;; maybe say 'non-obvious' instead of unknown
(defund nodenum-of-an-unknown-type-thingp (darg dag-array)
   (declare (xargs :guard (or (myquotep darg)
                              (and (natp darg)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))))
  (and (atom darg) ;makes sure it's not a quotep
       (let ((expr (aref1 'dag-array dag-array darg)))
         (or (atom expr) ;variable
             (if (quotep expr)
                 nil ; todo: what about a constant with unknown type?
               ;; todo: what if we can tighten the type from an obvious type?
               (not (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr))))))))

(defthm nodenum-of-an-unknown-type-thingp-forward-to-not-consp
  (implies (nodenum-of-an-unknown-type-thingp darg dag-array)
           (not (consp darg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable nodenum-of-an-unknown-type-thingp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;now just prints a message for incompatible types and returns (empty-type)
;Returns (mv nodenum-type-alist changep)
(defund improve-type (nodenum new-type nodenum-type-alist)
  (declare (xargs :guard (and (natp nodenum)
                              (axe-typep new-type)
                              (nodenum-type-alistp nodenum-type-alist))))
  (let ((binding (assoc nodenum nodenum-type-alist)))
    (if (not binding)
        (mv (acons nodenum new-type nodenum-type-alist)
            t ;no binding existed before, so we made a change
            )
      (let* ((type (cdr binding))
             (new-type (intersect-types type new-type)))
        (if (equal new-type type)
            (mv nodenum-type-alist nil) ;no change
          (mv (acons nodenum new-type nodenum-type-alist) ;use acons-unique?
              t ;we improved the type, so we made a change
              ))))))

(local
  (defthm alistp-of-mv-nth-0-of-improve-type
    (implies (alistp nodenum-type-alist)
             (alistp (mv-nth 0 (improve-type nodenum new-type nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable improve-type)))))

(local
  (defthm nodenum-type-alistp-of-mv-nth-0-of-improve-type
    (implies (and (nodenum-type-alistp nodenum-type-alist)
                  (natp nodenum)
                  (axe-typep new-type))
             (nodenum-type-alistp (mv-nth 0 (improve-type nodenum new-type nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable improve-type)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-0-of-improve-type
    (implies (and (nodenum-type-alistp nodenum-type-alist)
                  (natp nodenum)
                  (< nodenum dag-len)
                  (axe-typep new-type)
                  (ALL-< (STRIP-CARS NODENUM-TYPE-ALIST)
                         DAG-LEN))
             (all-< (strip-cars (mv-nth 0 (improve-type nodenum new-type nodenum-type-alist)))
                    dag-len))
    :hints (("Goal" :in-theory (enable improve-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (thm
;;  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
;;                (atom (cadr (aref1 'dag-array dag-array nodenum)))
;;                (CONSP (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))
;;                (not (EQUAL 'QUOTE
;;                      (CAR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM))))
;;                (natp nodenum))
;;           (<= 0 (cadr (aref1 'dag-array dag-array nodenum))))
;;  :hints (("Goal" :expand (PSEUDO-DAG-ARRAYP-AUX DAG-ARRAY-NAME DAG-ARRAY NODENUM)
;;           :in-theory (enable pseudo-dag-arrayp-aux BOUNDED-DAG-EXPRP))))

;; Returns (mv known-nodenum-type-alist changep).
(defund improve-known-nodenum-type-alist-with-node (nodenum ;to be assumed true
                                                    all-nodenums ;to be assumed true
                                                    dag-array
                                                    dag-len
                                                    known-nodenum-type-alist)
  (declare (xargs :guard (and (natp nodenum)
                              (true-listp all-nodenums)
                              (all-natp all-nodenums)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (all-< all-nodenums dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (e/d (nth-of-cdr posp)
                                                 (myquotep len))))))
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (variablep expr) ; provides no type info
        (mv known-nodenum-type-alist nil)
      (let ((fn (ffn-symb expr)))
        ;; todo: use CASE:
        (cond ((and (eq 'unsigned-byte-p fn) ; (unsigned-byte-p <size> <item>)
                    (eql 2 (len (dargs expr))))
               (let* ((args (dargs expr))
                      (size (first args))
                      (item (second args)))
                 (if (and (nodenum-of-an-unknown-type-thingp item dag-array) ;what if the type is obvious but not usb? - fixme what if this improves on the obvious type? i guess we'll just translate the usb in that case?
                          (darg-quoted-posp size))
                     (improve-type item (make-bv-type (unquote size)) known-nodenum-type-alist)
                   (mv known-nodenum-type-alist
                       nil))))
              ((and (eq 'booleanp fn) ; (booleanp <item>)
                    (eql 1 (len (dargs expr))))
               (let ((item (darg1 expr)))
                 (if (nodenum-of-an-unknown-type-thingp item dag-array) ;what if the type is obvious but not boolean?
                     (improve-type item (boolean-type) known-nodenum-type-alist)
                   (mv known-nodenum-type-alist
                       nil))))
              ((and (eq 'all-unsigned-byte-p fn) ; (all-unsigned-byte-p <size> <item>)
                    (eql 2 (len (dargs expr))))
               (let* ((args (dargs expr))
                      (size (first args))
                      (item (second args)))
                 ;;we've found an all-unsigned-byte-p claim (part of what we
                 ;;need for an array). now go see if there are corresponding
                 ;;length claim and true-listp claims.  fixme what if it's not
                 ;;directly a true-listp but equal to a true-listp?  fixme what
                 ;;if it's equal to something whose length we know?
                 ;;fixme write special purpose code for this?
                 (mv-let
                   (found-a-true-listp-claim nodenum-with-true-listp-claim alist)
                   (unify-tree-with-any-dag-node-no-wrap `(true-listp ,item) ;we instantiate item in this
                                                         all-nodenums
                                                         dag-array dag-len nil)
                   (declare (ignore alist nodenum-with-true-listp-claim)) ;or remove the node instead of ignoring it (but only if all the pieces are found)
                   (if (not found-a-true-listp-claim)
                       (mv known-nodenum-type-alist
                           nil)
                     (mv-let
                       (found-a-len-claim nodenum-with-len-claim alist)
                       ;; Look for a claim that the len is a constant (we look for both ways of orienting the equality)
                       (b* (((mv found-a-len-claim nodenum-with-len-claim alist)
                             (unify-tree-with-any-dag-node-no-wrap `(equal len (len ,item)) ;we instantiate item in this
                                                                   all-nodenums dag-array dag-len nil)))
                         (if found-a-len-claim
                             (mv found-a-len-claim nodenum-with-len-claim alist)
                           (unify-tree-with-any-dag-node-no-wrap `(equal (len ,item) len) ;we instantiate item in this
                                                                 all-nodenums dag-array dag-len nil)))
                       (declare (ignore nodenum-with-len-claim)) ;fffixme drop this literal? from the full list?
                       (let ((len (lookup-eq 'len alist)))       ;move down?
                         (if (and (darg-quoted-posp size)             ;move up?
                                  found-a-len-claim
                                  (darg-quoted-posp len)   ;what about 0?
                                  (< 1 (unquote len)) ;new ;todo: what about 1?
                                  (nodenum-of-an-unknown-type-thingp item dag-array) ;what if the type is known-by-looking-at-the-thing but not appropriate? ;move this test up?
                                  )
                             (improve-type item (make-bv-array-type (unquote size) (unquote len)) known-nodenum-type-alist)
                           (mv known-nodenum-type-alist
                               nil))))))))
              ;; if we know (equal x y), see if there is a type for x (either an obvious type or an entry in the alist) that is better than the type for y
              ;;and vice versa
              ;; (don't drop the literal. set the change flag only if an improvement was made (to avoid loops))
              ;; todo: add more tests for this case!
              ((and (eq 'equal fn) ; (equal <x> <y>)
                    (eql 2 (len (dargs expr))))
               (let* ((dargs (dargs expr))
                      (lhs (first dargs))
                      (rhs (second dargs))
                      ;call get-type-of-arg-safe?
                      (lhs-type (if (consp lhs) ; tests for quotep
                                    (get-type-of-val-safe (unquote lhs)) ;used to call get-type-of-val-checked, but that could crash!
                                  (get-type-of-nodenum-safe lhs 'dag-array dag-array known-nodenum-type-alist)))
                      (rhs-type (if (consp rhs) ; tests for quotep
                                    (get-type-of-val-safe (unquote rhs)) ;used to call get-type-of-val-checked, but that could crash!
                                  (get-type-of-nodenum-safe rhs 'dag-array dag-array known-nodenum-type-alist)))
                      ;;ffixme handle incompatible types
                      (new-type (intersect-types lhs-type rhs-type)))
                 (if (and (not (equal new-type lhs-type))
                          (natp lhs)) ;make sure it's a nodenum
                     (improve-type lhs new-type known-nodenum-type-alist)
                   (if (and (not (equal new-type rhs-type))
                            (natp rhs)) ;make sure it's a nodenum
                       (improve-type rhs new-type known-nodenum-type-alist)
                     ;; Could we ever improve both types?
                     (mv known-nodenum-type-alist nil)))))
              (t (mv known-nodenum-type-alist
                     nil)))))))

(local
  (defthm alistp-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-node
    (implies (alistp known-nodenum-type-alist)
             (alistp (mv-nth 0 (improve-known-nodenum-type-alist-with-node nodenum
                                                                           all-nodenums
                                                                           dag-array
                                                                           dag-len
                                                                           known-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable improve-known-nodenum-type-alist-with-node)))))

(local
  (defthm nodenum-type-alistp-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-node
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (natp nodenum)
                  (true-listp all-nodenums)
                  (all-natp all-nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (< nodenum dag-len)
                  (all-< all-nodenums dag-len)
                  )
             (nodenum-type-alistp (mv-nth 0 (improve-known-nodenum-type-alist-with-node nodenum
                                                                                        all-nodenums
                                                                                        dag-array
                                                                                        dag-len
                                                                                        known-nodenum-type-alist))))
    :hints (("Goal" :in-theory (e/d (improve-known-nodenum-type-alist-with-node car-becomes-nth-of-0) (natp))))))

; make a "bounded-nodenum-type-alistp"?
(local
  (defthm all-<-of-strip-cars-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-node
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (natp nodenum)
                  (true-listp all-nodenums)
                  (all-natp all-nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (< nodenum dag-len)
                  (all-< all-nodenums dag-len)
                  (ALL-< (STRIP-CARS KNOWN-NODENUM-TYPE-ALIST)
                         DAG-LEN))
             (all-< (strip-cars (mv-nth 0 (improve-known-nodenum-type-alist-with-node nodenum
                                                                                      all-nodenums
                                                                                      dag-array
                                                                                      dag-len
                                                                                      known-nodenum-type-alist)))
                    dag-len))
    :hints (("Goal" :in-theory (e/d (improve-known-nodenum-type-alist-with-node car-becomes-nth-of-0) (natp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv known-nodenum-type-alist change-flg)
;makes one pass through the nodes.
;fixme what about stuff like < that's not pure but has an obvious type?
(defund improve-known-nodenum-type-alist-with-nodes (nodenums ; to be assumed true
                                                     all-nodenums ; to be assumed true
                                                     dag-array dag-len known-nodenum-type-alist change-flg)
  (declare (xargs :guard (and (true-listp nodenums)
                              (all-natp nodenums)
                              (all-natp all-nodenums)
                              (true-listp all-nodenums)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< nodenums dag-len)
                              (all-< all-nodenums dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist))))
  (if (endp nodenums)
      (mv known-nodenum-type-alist change-flg)
    (let* ((nodenum (first nodenums)))
      (mv-let (known-nodenum-type-alist changep)
        (improve-known-nodenum-type-alist-with-node nodenum all-nodenums dag-array dag-len known-nodenum-type-alist)
        (improve-known-nodenum-type-alist-with-nodes (rest nodenums)
                                                     all-nodenums
                                                     dag-array
                                                     dag-len
                                                     known-nodenum-type-alist
                                                     (or changep change-flg))))))

(local
  (defthm alistp-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-nodes
    (implies (alistp known-nodenum-type-alist)
             (alistp (mv-nth 0 (improve-known-nodenum-type-alist-with-nodes nodenums all-nodenums dag-array dag-len known-nodenum-type-alist change-flg))))
    :hints (("Goal" :in-theory (enable improve-known-nodenum-type-alist-with-nodes)))))

(local
  (defthm nodenum-type-alistp-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-nodes
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (true-listp nodenums)
                  (all-natp nodenums)
                  (all-natp all-nodenums)
                  (true-listp all-nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (all-< nodenums dag-len)
                  (all-< all-nodenums dag-len))
             (nodenum-type-alistp (mv-nth 0 (improve-known-nodenum-type-alist-with-nodes nodenums all-nodenums dag-array dag-len known-nodenum-type-alist change-flg))))
    :hints (("Goal" :in-theory (enable improve-known-nodenum-type-alist-with-nodes)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-0-of-improve-known-nodenum-type-alist-with-nodes
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (true-listp nodenums)
                  (all-natp nodenums)
                  (all-natp all-nodenums)
                  (true-listp all-nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (all-< nodenums dag-len)
                  (all-< all-nodenums dag-len)
                  (ALL-< (STRIP-CARS KNOWN-NODENUM-TYPE-ALIST)
                         DAG-LEN))
             (all-< (strip-cars (mv-nth 0 (improve-known-nodenum-type-alist-with-nodes nodenums all-nodenums dag-array dag-len known-nodenum-type-alist change-flg)))
                    dag-len))
    :hints (("Goal" :in-theory (enable improve-known-nodenum-type-alist-with-nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;returns known-nodenum-type-alist
(defund build-known-nodenum-type-alist-aux (limit
                                            nodenums ;to assume true when inferring types
                                            dag-array
                                            dag-len
                                            known-nodenum-type-alist)
  (declare (xargs :guard (and (natp limit)
                              (true-listp nodenums)
                              (all-natp nodenums)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< nodenums dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist))))
  (if (zp limit) ;force termination
      (prog2$ (er hard? 'build-known-nodenum-type-alist-aux "Recursion limit reached.")
              known-nodenum-type-alist)
    (mv-let (known-nodenum-type-alist change-flg)
      (improve-known-nodenum-type-alist-with-nodes nodenums nodenums dag-array dag-len known-nodenum-type-alist nil)
      (if (not change-flg)
          known-nodenum-type-alist
        ;;something changed, so walk the disjuncts again:
        (build-known-nodenum-type-alist-aux (+ -1 limit) nodenums dag-array dag-len known-nodenum-type-alist)))))

(local
  (defthm alistp-of-build-known-nodenum-type-alist-aux
    (implies (alistp known-nodenum-type-alist)
             (alistp (build-known-nodenum-type-alist-aux limit nodenums dag-array dag-len known-nodenum-type-alist)))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist-aux)))))

;;gen this and similar ones?
(local
  (defthm nodenum-type-alistp-of-build-known-nodenum-type-alist-aux
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (natp limit)
                  (true-listp nodenums)
                  (all-natp nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (all-< nodenums dag-len))
             (nodenum-type-alistp (build-known-nodenum-type-alist-aux limit nodenums dag-array dag-len known-nodenum-type-alist)))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist-aux)))))

(local
  (defthm all-<-of-strip-cars-of-build-known-nodenum-type-alist-aux
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (natp limit)
                  (true-listp nodenums)
                  (all-natp nodenums)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (all-< nodenums dag-len)
                  (all-< (strip-cars known-nodenum-type-alist)
                         dag-len))
             (all-< (strip-cars (build-known-nodenum-type-alist-aux limit nodenums dag-array dag-len known-nodenum-type-alist))
                    dag-len))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For the purposes of extracting type information, we can assume all the
;; literals (disjuncts) are false, because if any of them is true, then the
;; whole goal is true.

;; Strip the NOTs off the disjuncts (after looking up any bare nodenums),
;; dropping any disjunct that's not a NOT (after looking up any bare nodenums).
;; todo: rename
(defund get-nodenums-of-negations-of-disjuncts (disjuncts dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len))
                  :guard-hints (("Goal" :expand ((strip-nots-from-possibly-negated-nodenums disjuncts))
                                 :in-theory (enable car-becomes-nth-of-0 strip-not-from-possibly-negated-nodenum
                                                    possibly-negated-nodenump
                                                    bounded-possibly-negated-nodenumsp
                                                    bounded-possibly-negated-nodenump)))))
  (if (endp disjuncts)
      nil
    (let* ((disjunct (first disjuncts)))
      (if (consp disjunct)       ;;it's a call of not
          (cons (farg1 disjunct) ;strip the not
                (get-nodenums-of-negations-of-disjuncts (rest disjuncts) dag-array dag-len))
        ;; it's a nodenum, so look it up:
        (let ((expr (aref1 'dag-array dag-array disjunct)))
          (if (and (call-of 'not expr)
                   (eql 1 (len (dargs expr)))
                   (natp (darg1 expr)) ;checks that the negated thing is a nodenum; error if it's a quotep? (todo: just check non-consp?)
                   )
              ;; strip the not:
              (cons (darg1 expr)
                    (get-nodenums-of-negations-of-disjuncts (rest disjuncts) dag-array dag-len))
            ;; skip this disjunct (we could assume its negation, but that will be a call of NOT, which is not helpful in determining types):
            (get-nodenums-of-negations-of-disjuncts (rest disjuncts) dag-array dag-len)))))))

(local
  (defthm all-natp-of-get-nodenums-of-negations-of-disjuncts
    (implies (possibly-negated-nodenumsp disjuncts)
             (all-natp (get-nodenums-of-negations-of-disjuncts disjuncts dag-array dag-len)))
    :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                       get-nodenums-of-negations-of-disjuncts
                                       possibly-negated-nodenump)))))

(local
  (defthm all-<-of-get-nodenums-of-negations-of-disjuncts
    (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (all-< (get-nodenums-of-negations-of-disjuncts disjuncts dag-array dag-len) dag-len))
    :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp get-nodenums-of-negations-of-disjuncts
                                       possibly-negated-nodenumsp
                                       strip-nots-from-possibly-negated-nodenums
                                       strip-not-from-possibly-negated-nodenum
                                       car-becomes-nth-of-0
                                       possibly-negated-nodenump
                                       bounded-possibly-negated-nodenumsp
                                       bounded-possibly-negated-nodenump)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns known-nodenum-type-alist, where the types in known-nodenum-type-alist are implied by the conjunction of the negations of disjuncts.
;; known-nodenum-type-alist assigns types only to nodes in the DAG without obvious types ("obvious types" are types you can tell just from looking at the nodes). fixme what if it can improve on an obvious type?!
;;All of the types computed here are known for sure; they are different from types "induced" by how a node is used (e.g., only 32-bits of x are used in (bvxor 32 x y)).
;fixme are shadowed pairs okay in this?
;does this chase chains of equalities? now it should.  test that!
 ;nodes that provide only type info get removed
;; TODO: Show that this cannot include the empty-type or the most-general-type?  Maybe this needs to be able to return an error?
(defund build-known-nodenum-type-alist (disjuncts ; each can be assumed false (else the whole disjunction is true)
                                        dag-array
                                        dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len))
                  :guard-hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum rational-listp-when-all-natp)))))
  (let* ((nodenums-to-assume (get-nodenums-of-negations-of-disjuncts disjuncts dag-array dag-len)) ;todo: what about ones that are not negated? ; todo: since the disjuncts are pnns, consider not using the dag here
         (nodenum-count (len nodenums-to-assume)))
    (build-known-nodenum-type-alist-aux (* (+ 1 nodenum-count) ;not sure what we should use here
                                           (+ 1 nodenum-count)
                                           (+ 1 nodenum-count))
                                        nodenums-to-assume
                                        dag-array
                                        dag-len
                                        nil)))

(local
  (defthm alistp-of-build-known-nodenum-type-alist
    (alistp (build-known-nodenum-type-alist disjuncts dag-array dag-len))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist)))))

(local
  (defthm nodenum-type-alistp-of-build-known-nodenum-type-alist
    (implies (and  (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                   (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (nodenum-type-alistp (build-known-nodenum-type-alist disjuncts dag-array dag-len)))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist)))))

(local
  (defthm all-<-of-strip-cars-of-build-known-nodenum-type-alist
    (implies (and  (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                   (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (all-< (strip-cars (build-known-nodenum-type-alist disjuncts dag-array dag-len)) dag-len))
    :hints (("Goal" :in-theory (enable build-known-nodenum-type-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (include-book "kestrel/bv/sbvdiv" :dir :system))
(local (include-book "kestrel/bv/sbvrem" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/sbvlt" :dir :system))

;; These theorems justify the induced types:

(thm (equal (bvchop size (bvchop size x)) (bvchop size x)))
(thm (equal (bvuminus size (bvchop size x)) (bvuminus size x)))
(thm (equal (bvnot size (bvchop size x)) (bvnot size x)))

;; First of the 2 args:
(thm (equal (bvequal size (bvchop size x) y) (bvequal size x y)))
(thm (equal (bvplus size (bvchop size x) y) (bvplus size x y)))
(thm (equal (bvminus size (bvchop size x) y) (bvminus size x y)))
(thm (equal (bvmult size (bvchop size x) y) (bvmult size x y)))
(thm (equal (bvand size (bvchop size x) y) (bvand size x y)))
(thm (equal (bvor size (bvchop size x) y) (bvor size x y)))
(thm (equal (bvxor size (bvchop size x) y) (bvxor size x y)))
(thm (equal (bvdiv size (bvchop size x) y) (bvdiv size x y)))
(thm (equal (bvmod size (bvchop size x) y) (bvmod size x y)))
(thm (implies (natp size) (equal (sbvdiv size (bvchop size x) y) (sbvdiv size x y))))
(thm (implies (natp size) (equal (sbvrem size (bvchop size x) y) (sbvrem size x y))))
(thm (equal (bvlt size (bvchop size x) y) (bvlt size x y)))
(thm (equal (bvle size (bvchop size x) y) (bvle size x y)))
(thm (implies (posp size) (equal (sbvlt size (bvchop size x) y) (sbvlt size x y))))
(thm (implies (posp size) (equal (sbvle size (bvchop size x) y) (sbvle size x y))))

;; Second of the 2 args:
(thm (equal (bvequal size x (bvchop size y)) (bvequal size x y)))
(thm (equal (bvplus size x (bvchop size y)) (bvplus size x y)))
(thm (equal (bvminus size x (bvchop size y)) (bvminus size x y)))
(thm (equal (bvmult size x (bvchop size y)) (bvmult size x y)))
(thm (equal (bvand size x (bvchop size y)) (bvand size x y)))
(thm (equal (bvor size x (bvchop size y)) (bvor size x y)))
(thm (equal (bvxor size x (bvchop size y)) (bvxor size x y)))
(thm (equal (bvdiv size x (bvchop size y)) (bvdiv size x y)))
(thm (equal (bvmod size x (bvchop size y)) (bvmod size x y)))
(thm (implies (natp size) (equal (sbvdiv size x (bvchop size y)) (sbvdiv size x y))))
(thm (implies (natp size) (equal (sbvrem size x (bvchop size y)) (sbvrem size x y))))
(thm (equal (bvlt size x (bvchop size y)) (bvlt size x y)))
(thm (equal (bvle size x (bvchop size y)) (bvle size x y)))
(thm (implies (posp size) (equal (sbvlt size x (bvchop size y)) (sbvlt size x y))))
(thm (implies (posp size) (equal (sbvle size x (bvchop size y)) (sbvle size x y))))

(thm (implies (and (natp new-size) (posp old-size)) (equal (bvsx new-size old-size x) (bvsx new-size old-size (bvchop old-size x)))))

(thm (equal (bvif size test (bvchop size then) else) (bvif size test then else)))
(thm (equal (bvif size test then (bvchop size else)) (bvif size test then else)))
(thm (equal (bvif size (bool-fix test) then else) (bvif size test then else)))

(thm (implies (natp n) (equal (getbit n (bvchop (+ 1 n) x)) (getbit n x))))

(thm (implies (and (natp high) (natp low)) (equal (slice high low (bvchop (+ 1 high) x)) (slice high low x))))

(thm (equal (bitand x (bvchop 1 y)) (bitand x y)))
(thm (equal (bitor x (bvchop 1 y)) (bitor x y)))
(thm (equal (bitxor x (bvchop 1 y)) (bitxor x y)))

(thm (equal (bitand (bvchop 1 x) y) (bitand x y)))
(thm (equal (bitor (bvchop 1 x) y) (bitor x y)))
(thm (equal (bitxor (bvchop 1 x) y) (bitxor x y)))

(thm (equal (bvcat highsize (bvchop highsize highval) lowsize lowval) (bvcat highsize highval lowsize lowval)))
(thm (equal (bvcat highsize highval lowsize (bvchop lowsize lowval)) (bvcat highsize highval lowsize lowval)))

(thm (equal (leftrotate32 amt (bvchop 32 val)) (leftrotate32 amt val)))

(thm (equal (bv-array-read element-width len (bvchop (ceiling-of-lg len) index) data) (bv-array-read element-width len index data)))
;; These 2 together justify assumung the array is a value of the right type:
(thm (implies (posp len) (equal (bv-array-read element-width len index (take len data)) (bv-array-read element-width len index data))))
(thm (equal (bv-array-read element-width len index (bvchop-list element-width data)) (bv-array-read element-width len index data)))

(thm (equal (bv-array-write element-width len (bvchop (ceiling-of-lg len) index) val data) (bv-array-write element-width len index val data)))
(thm (implies (integerp element-width) (equal (bv-array-write element-width len index (bvchop element-width val) data) (bv-array-write element-width len index val data))))
;; These 2 together justify assuming the array is a value of the right type:
(thm (implies (posp len) (equal (bv-array-write element-width len index val (take len data)) (bv-array-write element-width len index val data))))
(thm (equal (bv-array-write element-width len index val (bvchop-list element-width data)) (bv-array-write element-width len index val data)))

(thm (equal (bv-array-if element-width len (bool-fix test) a1 a2) (bv-array-if element-width len test a1 a2)))
(thm (implies (and (<= len n) (natp n)) (equal (bv-array-if element-width len test (take n a1) a2) (bv-array-if element-width len test a1 a2))))
(thm (equal (bv-array-if element-width len test (bvchop-list element-width a1) a2) (bv-array-if element-width len test a1 a2)))
(thm (implies (and (<= len n) (natp n)) (equal (bv-array-if element-width len test a1 (take n a2)) (bv-array-if element-width len test a1 a2))))
(thm (equal (bv-array-if element-width len test a1 (bvchop-list element-width a2)) (bv-array-if element-width len test a1 a2)))

(thm (equal (booland (bool-fix x) y) (booland x y)))
(thm (equal (boolor (bool-fix x) y) (boolor x y)))
(thm (equal (boolxor (bool-fix x) y) (boolxor x y)))
(thm (equal (booland x (bool-fix y)) (booland x y)))
(thm (equal (boolor x (bool-fix y)) (boolor x y)))
(thm (equal (boolxor x (bool-fix y)) (boolxor x y)))

(thm (equal (not (bool-fix x)) (not x)))

(thm (equal (boolif (bool-fix test) x y) (boolif test x y)))
(thm (equal (boolif test (bool-fix x) y) (boolif test x y)))
(thm (equal (boolif test x (bool-fix y)) (boolif test x y)))

;; Determines the type (if any) for NODENUM induced by PARENT-EXPR. For
;; example, (bvplus '32 100 200) induces a BV type of width 32 for node 100 and
;; node 200.
;; Returns an axe-type, or nil to indicate that no type could be determined.
;; If a type is returned, the NODENUM can be safely assumed to be of that type,
;; without loss of generality, with respect to its appearance in this
;; PARENT-EXPR (if it appeals in multiple parent-exprs, the types should be
;; unioned together).  That is, if X only appears in argument positions of
;; exprs that are chopped to 32 bits (see the THMs above that justify this), then
;; we can transform a proof about all Xs to a proof about Xs that are
;; bit-vectors of length 32 (imagine adding an unnecessary (bvchop
;; 32 x) around all mentions of X and then cutting out the BVCHOP term).  If x appears in
;; more than one choppable context, the call of this will have to the longest BV that it could be.

;; TODO: Ensure that parents that do not induce types via this function (like equal) cannot be translated and thus will always be chopped.

;fixme this was missing handling of the test position of bvif - check that everything translatable is handled correctly here?
;; TODO: Consider having this return an indication of a type error (e.g., node used both as an array and a BV).
;; TODO: If we are going to cut away the parent, we might want to disregard any types it induces on its children.
;; TODO: Throw a hard error if NODENUM is not one of the args of PARENT-EXPR?
(defund get-induced-type (nodenum parent-expr)
  (declare (xargs :guard (and (natp nodenum)
                              (dag-function-call-exprp parent-expr))
                  :guard-hints (("Goal" :in-theory (enable dargp-of-nth-when-darg-listp nth-of-cdr)))))
  (let ((fn (ffn-symb parent-expr))
        (dargs (dargs parent-expr)))
    (cond ((member-eq fn '(bvuminus bvchop bvnot)) ; (<fn> <size> <arg>)
           (if (and (eql 2 (len dargs))
                    (darg-quoted-posp (first dargs)) ; disallows a 0-width BV (should it?)
                    (eql nodenum (second dargs)) ;skip this check (and others like it) if the expr is guaranteed to be a parent expr?
                    )
               (make-bv-type (unquote (first dargs)))
             nil))
          ;; todo: add bvequal (once we can translate it):
          ((member-eq fn '(bvequal bvplus bvminus bvmult bvand bvor bvxor bvdiv bvmod sbvdiv sbvrem bvlt bvle sbvlt sbvle)) ; (<fn> <size> <arg1> <arg2>)
           (if (and (eql 3 (len dargs))
                    (darg-quoted-posp (first dargs)) ; posp may be needed for sbvlt/sbvle
                    ;; ok if NODENUM is both BV args:
                    (or (eql nodenum (second dargs))
                        (eql nodenum (third dargs))))
               (make-bv-type (unquote (first dargs)))
             nil))
          ((eq fn 'bvsx) ; (bvsx <new-size> <old-size> <val>)
           (if (and (eql 3 (len dargs))
                    (darg-quoted-posp (first dargs)) ;could allow natp
                    (darg-quoted-posp (second dargs)) ; todo: check that the sizes are in order?
                    (eql nodenum (third dargs)) ;skip this check (and others like it) if the expr is guaranteed to be a parent expr?
                    )
               (make-bv-type (unquote (second dargs)))
             nil))
          ((eq 'bvif fn) ; (bvif <size> <test> <then> <else>)
           (if (and (eql 4 (len dargs))
                    (darg-quoted-posp (first dargs)))
               (union-types (if (eql nodenum (second dargs))
                                (boolean-type)
                              (empty-type))
                            (if (or (eql nodenum (third dargs)) ;; can be both (rare but ok)
                                    (eql nodenum (fourth dargs)))
                                (make-bv-type (unquote (first dargs)))
                              (empty-type)))
             nil))
          ((eq fn 'getbit) ; (getbit <n> x)
           (if (and (eql 2 (len dargs))
                    (darg-quoted-natp (first dargs))
                    (eql nodenum (second dargs)))
               (make-bv-type (+ 1 (unquote (first dargs))))
             nil))
          ((eq fn 'slice) ; (slice <high> <low> x)
           (if (and (eql 3 (len dargs))
                    (darg-quoted-natp (first dargs))
                    (darg-quoted-natp (second dargs))
                    (<= (unquote (second dargs)) (unquote (first dargs)))
                    (eql nodenum (third dargs)))
               (make-bv-type (+ 1 (unquote (first dargs))))
             nil))
          ((eq fn 'bitnot) ; (bitnot <arg>)
           (if (and (eql 1 (len dargs))
                    (eql nodenum (first dargs)))
               (make-bv-type 1)
             nil))
          ((member-eq fn '(bitor bitand bitxor)) ; (<fn> <arg1> <arg2>)
           (if (and (eql 2 (len dargs))
                    ;; can be both (rare but ok):
                    (or (eql nodenum (first dargs))
                        (eql nodenum (second dargs))))
               (make-bv-type 1)
             nil))
          ((eq fn 'bvcat) ; (bvcat <highsize> <highval> <lowsize> <lowval>)
           (if (and (eql 4 (len dargs))
                    (darg-quoted-posp (first dargs))
                    (darg-quoted-posp (third dargs)))
               ;;nodenum may be one or both of the bv dargs:
               (union-types (if (eql nodenum (second dargs))
                                (make-bv-type (unquote (first dargs)))
                              (empty-type))
                            (if (eql nodenum (fourth dargs))
                                (make-bv-type (unquote (third dargs)))
                              (empty-type)))
             nil))
          ((eq fn 'leftrotate32) ; (leftrotate32 <amt> <val>)
           (if (and (eql 2 (len dargs))
                    (darg-quoted-natp (first dargs))
                    (eql nodenum (second dargs)))
               (make-bv-type 32)
             nil))
          ((eq fn 'bv-array-read) ; (bv-array-read <element-size> <len> <index> <data>)
           (if (and (eql 4 (len dargs))
                    (darg-quoted-posp (first dargs))
                    (darg-quoted-integerp (second dargs))
                    (<= 2 (unquote (second dargs))) ;new, since an array of length 1 would have a 0-bit index
                    )
               (union-types (if (eql nodenum (third dargs))
                                ;; nodenum is the index:
                                (make-bv-type (ceiling-of-lg (unquote (second dargs))))
                              (empty-type))
                            (if (eql nodenum (fourth dargs))
                                ;; nodenum is the array data:
                                ;; Since arrays with different lengths are not compatible, this type won't union well with a longer or shorter array type:
                                (make-bv-array-type (unquote (first dargs)) (unquote (second dargs)))
                              (empty-type)))
             nil))
          ((eq fn 'bv-array-write) ; (bv-array-write <element-size> <len> <index> <val> <data>)
           (if (and (eql 5 (len dargs))
                    (darg-quoted-posp (first dargs))
                    (darg-quoted-integerp (second dargs)) ; todo: what about len =1 (disallowed elsewhere)?
                    (<= 2 (unquote (second dargs))) ;new, since an array of length 1 would have a 0-bit index
                    )
               ;; if nodenum appears as an array and a BV, we'll get
               ;; most-general-type here, which will cause an error later:
               (union-types (if (eql nodenum (third dargs))
                                ;; nodenum is the index:
                                (make-bv-type (ceiling-of-lg (unquote (second dargs))))
                              (empty-type))
                            (union-types (if (eql nodenum (fourth dargs))
                                             ;; nodenum is the value:
                                             (make-bv-type (unquote (first dargs)))
                                           (empty-type))
                                         (if (eql nodenum (fifth dargs))
                                             ;; nodenum is the array data:
                                             (make-bv-array-type (unquote (first dargs)) (unquote (second dargs)))
                                           (empty-type))))
             nil))
          ((eq 'bv-array-if fn) ; (bv-array-if <element-width> <len> <test> <then> <else>)
           (if (and (eql 5 (len dargs))
                    (darg-quoted-posp (first dargs))
                    (darg-quoted-integerp (second dargs))
                    (<= 2 (unquote (second dargs))) ;new, since an array of length 1 would have a 0-bit index
                    )
               (union-types (if (eql nodenum (third dargs))
                                ;; nodenum is the test:
                                (boolean-type)
                              (empty-type))
                            (if (or (eql nodenum (fourth dargs))
                                    (eql nodenum (fifth dargs)))
                                ;; nodenum is one of the then/else branches (or both):
                                (make-bv-array-type (unquote (first dargs)) (unquote (second dargs)))
                              (empty-type)))
             nil))
          ((member-eq fn '(boolor booland boolxor)) ; (<fn> <arg1> <arg2>)
           (if (and (eql 2 (len dargs))
                    (or (eql nodenum (first dargs))
                        (eql nodenum (second dargs))))
               (boolean-type)
             nil))
          ((eq fn 'not)
           (if (and (eql 1 (len dargs))
                    (eql nodenum (first dargs)))
               (boolean-type)
             nil))
          ((eq fn 'boolif) ; (boolif <test> <then> <else>)
           (if (and (eql 3 (len dargs))
                    ;; nodenum can be any/all of the args:
                    (or (eql nodenum (first dargs))
                        (eql nodenum (second dargs))
                        (eql nodenum (third dargs))))
               (boolean-type)
             nil))
          ;; Can we do anything for an equal, given that we don't know whether
          ;; it is true or false, or if it even compares values of the same
          ;; types?
          ;; ((eq 'equal fn) ;; (equal <constant> nodenum)
          ;;  (if (and (darg-quoted-posp (first dargs)) ;ffixme what about 0???
          ;;           (eql nodenum (second dargs))
          ;;           )
          ;;      (make-bv-type (integer-length (unquote (first dargs))))
          ;;    (most-general-type)))
          ;; TTODO: handle leftrotate?, bvshl, bvshr, ...
          (t nil))))

(local
  (defthm axe-typep-of-get-induced-type
    (implies (get-induced-type nodenum parent-expr)
             (axe-typep (get-induced-type nodenum parent-expr)))
    :hints (("Goal" :in-theory (enable get-induced-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;union together all the choppable types that come from the parents
;if some parent doesn't induce a type, that parent is ignored (ffixme is that sound? presumably parents that don't induce a type won't be translated?  what about equal? unsigned-byte-p, etc.?)
;; TODO: Consider the case where we get a bad type due to a parent that will be cut out because its parents are not translatable.
(defund most-general-induced-type-aux (parent-nodenums nodenum dag-array dag-len type-acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (true-listp parent-nodenums)
                              (all-natp parent-nodenums)
                              (all-< parent-nodenums dag-len)
                              (axe-typep type-acc)
                              (natp nodenum))
                  ;; todo: use rules instead of these hints
                  :guard-hints (("Goal" :in-theory (enable bounded-dag-exprp)))))
  (if (endp parent-nodenums)
      type-acc
    (b* ((parent-nodenum (first parent-nodenums))
         (parent-expr (aref1 'dag-array dag-array parent-nodenum))
         ((when (not (and (consp parent-expr)
                          (not (eq 'quote (car parent-expr))))))
          (er hard? 'most-general-induced-type-aux "Bad parent expr: ~x0." parent-expr))
         (type-from-this-parent (get-induced-type nodenum parent-expr))
         ;; FFIXME: Consider what to do in this case:
         ;; ((when (not type-from-this-parent))
         ;;  (print-dag-array-node-and-supporters 'dag-array dag-array parent-nodenum)
         ;;  (er hard? 'most-general-induced-type-aux "No type for node ~x0 via parent ~x1 (see dag above)." nodenum parent-nodenum))
         (new-type-acc (if type-from-this-parent
                           (union-types type-from-this-parent type-acc)
                         (progn$ ; (cw "WARNING: No induced type for ~x0 in ~x1.~%" nodenum parent-expr)
                           ;; would like to say (most-general-type) here, but that caused many failures (e.g., nodenum may have parents like jvm::update-nth-local):
                           ;; If the parent can be translated, but doesn't induce a type on the child, we must put in (most-general-type) for the child unless it has an obvious type
                           ;; But EQUAL and UNSIGNED-BYTE-P both require obvious types for their children and everything else translatable induces types (todo: check this)
                           type-acc))))
      (most-general-induced-type-aux (rest parent-nodenums) nodenum dag-array dag-len new-type-acc))))

(local
  (defthm axe-typep-of-most-general-induced-type-aux
    (implies (and (axe-typep type-acc)
                  (most-general-induced-type-aux parent-nodenums nodenum dag-array dag-len type-acc))
             (axe-typep (most-general-induced-type-aux parent-nodenums nodenum dag-array dag-len type-acc)))
    :hints (("Goal" :in-theory (enable most-general-induced-type-aux)))))

;; ;the union of all the types of choppable occurrences of x
;; ;the most general type for nodenum, based on which argument positions of its parents it appears in
;; ;t would be the most general type of all (any object)
;; ;ffixme handle arrays (and booleans?)
;; (defun most-general-induced-type (parent-nodenums nodenum dag-array)
;;   (if (not (consp parent-nodenums))
;;       (most-general-type) ;think more about this case - not possible?  what if the node is the top node of a literal? would we be calling this?!
;;     (let* ((parent-nodenum (first parent-nodenums))
;;            (parent-expr (aref1 'dag-array dag-array parent-nodenum))
;;            (first-type (get-induced-type nodenum parent-expr)))
;;       (most-general-induced-type-aux (cdr parent-nodenums) nodenum dag-array first-type))))

;; ;try to figure out the type of this node (must hold for all uses of the node in the dag)
;; ;nil if we can't cut here (when would that be?) seems like if we can translate the parent we should be able to cut one of its children - unless maybe the parent is 'equal??
;; ;ffixme have this support booleans?
;; ;fixme consider if node X is used as both a bit vector and an array - maybe that's a case we can't translate (or split into cases based on what it is..)...
;; ;fixme compare to get-type-of-nodenum-checked
;; (defun type-of-node-if-we-cut (nodenum nodenum-type-alist-from-literals dag-array dag-parent-array)
;;   ;;check whether another literal gives the node a type:
;;   (let ((match (lookup-eq nodenum nodenum-type-alist-from-literals)))
;;     (if (and match
;;              ;;drop these checks?:
;;              (or (bv-typep match)
;;                  (and (bv-array-typep match)
;;                       (natp (bv-array-type-element-width match)) ;posp?
;;                       (natp (bv-array-type-len match)) ;posp?
;;                       )))
;;         match
;;       ;;check whether all the parents mention the node in BV positions:
;;       (let* ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum))
;;              (type (most-general-induced-type parent-nodenums nodenum dag-array)))
;;         (if (bv-typep type) ;ffixme what about arrays? maybe even booleans would be okay?
;;             type
;;           nil)))))

;; ;; todo: since this never fires, drop this check (perhaps once the pure dag checking is strengthened)
;; (defund can-translate-bvif-args (dargs)
;;   (declare (xargs :guard (darg-listp dargs)))
;;   (if (and (= (len dargs) 4)    ;optimize?
;;            (myquotep (first dargs)) ; drop?
;;            (darg-quoted-posp (first dargs)) ;used to allow 0 ;fixme print a warning in that case?
;;            ;; If the arg is a constant, it must be a quoted natp (not something like ':irrelevant):
;;            ;; todo: call bv-arg-okp here (but note the guard):
;;            (if (consp (third dargs))     ;checks for quotep
;;                (and (myquotep (third dargs)) ;for guards
;;                     (natp (unquote (third dargs))))
;;              t)
;;            (if (consp (fourth dargs))     ;checks for quotep
;;                (and (myquotep (fourth dargs)) ;for guards
;;                     (natp (unquote (fourth dargs))))
;;              t))
;;       t
;;     (er hard? 'can-translate-bvif-args "Bad BVIF args: ~x0." dargs)))

;; When translating to STP, there are several types of nodes;
;; nodes where we know the return type and can always translate (e.g., constants; (bvxor 32 .. ..) - args can be chopped)
;; nodes where we know the return type and can sometimes translate (e.g., equal, unsigned-byte-p - arg types must be known)
;; nodes where we know the return type but can't translate (e.g., < - can replace with a boolean variable)
;; nodes where we don't know the return type and can't translate (e.g., varaiables, calls to foo - but assumptions may tell us the type)
; If a node whose type we don't know (not obvious, not in the known-type-alist) appears sometimes as a choppable arg (e.g., to XOR) and sometimes as an arg to equal (cannot chop), we'll use the induced type (the largest type of all the choppable uses of the term) and the equal will just have to be made into a boolean variable.
;
;ffixme other possibilities:
;; leftrotate bvshl bvshr
;move this to the same file as the translation..
;should this really check the types of the args?
;exhibit the foo-of-bvchop theorems to justify this (see above).  todo: ensure completeness of the set of theorems above.
;fixme check that constant arguments are of the right type?  e.g., that we don't call bvmod of 'x... -- done now?
;; TODO: Can we assume that the arity of the call (fn applied to args) is correct?
;fffixme think this through! check the types of the operands (for whether they can be translated and are compatible?)?! maybe just check constants?
;; Note that this does not handle EQUAL, as it is treated separately.
;; todo: check more?
;; TODO: Consider printing a warning if a BV op with a size argument of 0 arises.
;; TODO: Compare this to pure-fn-call-exprp (currently, this takes the dag-array for checking bv-array operations -- why?)
;; todo: add bvequal, once we can translate it
(defund can-always-translate-expr-to-stp (fn args dag-array-name dag-array dag-len known-nodenum-type-alist print)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (symbolp fn)
                              (bounded-darg-listp args dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist))
                  :guard-hints (("Goal" :in-theory (enable))))
           (ignore dag-len))
  (case fn
    (not (and (= 1 (len args))
              (boolean-arg-okp (first args))))
    ((booland boolor) (and (= 2 (len args))
                           (boolean-arg-okp (first args))
                           (boolean-arg-okp (second args))))
    (boolif (and (= 3 (len args))
                 (boolean-arg-okp (first args))
                 (boolean-arg-okp (second args))
                 (boolean-arg-okp (third args))))
    (bitnot (and (= 1 (len args))
                 (bv-arg-okp (first args))))
    ((bitand bitor bitxor) (and (= 2 (len args))
                                (bv-arg-okp (first args))
                                (bv-arg-okp (second args))))
    ((bvchop bvnot bvuminus) ; (<fn> <size> <x>)
     (and (= 2 (len args))
          (darg-quoted-posp (first args))
          (bv-arg-okp (second args))))
    (getbit (and (= 2 (len args))
                 (darg-quoted-natp (first args))
                 (bv-arg-okp (second args))))
    (slice (and (= 3 (len args))
                (darg-quoted-natp (first args))
                (darg-quoted-natp (second args))
                (<= (unquote (second args))
                    (unquote (first args)))
                (bv-arg-okp (third args))))
    ((bvequal
       bvand bvor bvxor
       bvplus bvminus bvmult
       bvdiv bvmod
       sbvdiv sbvrem
       bvlt bvle
       sbvlt sbvle)
     (and (= 3 (len args))
          (darg-quoted-posp (first args))
          (bv-arg-okp (second args))
          (bv-arg-okp (third args))))
    (bvcat (and (= 4 (len args))
                (darg-quoted-posp (first args))
                (bv-arg-okp (second args))
                (darg-quoted-posp (third args))
                (bv-arg-okp (fourth args))))
    (bvsx (and (= 3 (len args))
               (darg-quoted-posp (first args))
               (darg-quoted-posp (second args))
               ;; todo: disallow = ?
               (<= (unquote (second args))
                   (unquote (first args)))
               (bv-arg-okp (third args))))
    ((bvif) (and (= 4 (len args)) ; (bvif <size> <test> <then> <else>)
                 (darg-quoted-posp (first args))
                 (boolean-arg-okp (second args))
                 (bv-arg-okp (third args))
                 (bv-arg-okp (fourth args))))
    ;; we can translate (leftrotate32 amt val) but only if AMT is a constant:
    (leftrotate32 (and (= 2 (len args))
                       (darg-quoted-natp (first args)) ;now allows 0 (todo: test it)
                       ;;(< (unquote (first args)) 32)
                       (bv-arg-okp (second args))
                       ))
    ;; todo: clean these up:
    (bv-array-read ; (bv-array-read <element-width> <len> <index> <data>)  ;new (ffixme make sure these get translated right: consider constant array issues):
      (if (and (= 4 (len args))               ;todo: speed up checks like this?
               (darg-quoted-posp (first args)) ; disallows 0 width
               (darg-quoted-integerp (second args))
               (<= 2 (unquote (second args))) ;an array of length 1 would have 0 index bits
               )
          (let* ((data-arg (fourth args))
                 (type-of-data (get-type-of-arg-safe data-arg dag-array-name dag-array known-nodenum-type-alist)))
            (if (and (bv-array-typep type-of-data)
                     (= (bv-array-type-len type-of-data) (unquote (second args))))
                t
              (prog2$ (and ;(eq :verbose print)
                        (cw "(WARNING: Not translating bv-array-read expr ~x0.  The required length is ~x1 but the array argument, ~x2, has type ~x3.)~%"
                            (cons fn args)
                            (unquote (second args))
                            (if (quotep data-arg) data-arg (aref1 dag-array-name dag-array data-arg))
                            type-of-data))
                      nil)))
        (prog2$ (and (eq :verbose print)
                     (cw "(WARNING: Not translating bv-array-read expr ~x0.)~%" (cons fn args)))
                nil)))
;fixme add a case here that checks the array argument type like we do just above for read:
    (bv-array-write ; (bv-array-write <element-size> <len> <index> <val> <data>) ;new (ffixme make sure these get translated right - consider constant array issues):
     (if (and (= 5 (len args))
              (darg-quoted-posp (first args)) ; disallows 0 width
              (darg-quoted-integerp (second args))
              (<= 2 (unquote (second args))) ;an array of length 1 would have 0 index bits..
              )
         t
       (prog2$ (and (eq :verbose print)
                    (cw "(WARNING: Not translating bv-array-write expr ~x0.)~%" (cons fn args)))
               nil)))
    (bv-array-if ; (bv-array-if <element-size> <len> <test> <array1> <array2>) ; very new (ffixme make sure these get translated right - consider constant array issues):
     (if (and (= 5 (len args))
              (darg-quoted-posp (first args)) ; disallows 0 width
              (darg-quoted-integerp (second args))
              (<= 2 (unquote (second args))) ;an array of length 1 would have 0 index bits..
              )
         (let ((type (make-bv-array-type (unquote (first args)) (unquote (second args)))))
           ;; The types of the 'then' and 'else' branches must be exactly the type of the BV-ARRAY-IF:
           (and (equal type (get-type-of-arg-checked (fourth args) dag-array-name dag-array known-nodenum-type-alist))
                (equal type (get-type-of-arg-checked (fifth args) dag-array-name dag-array known-nodenum-type-alist)))) ;todo: what about implicit padding of constant arrays?
       (prog2$ (and (eq :verbose print)
                    (cw "(WARNING: Not translating bv-array-if expr ~x0.)~%" (cons fn args)))
               nil)))
    ;; (equal (let ((arg1 (first args))
    ;;                      (arg2 (second args)))
    ;;                  (and (or (not (consp arg1))
    ;;                           (let ((farg1 (unquote arg1)))
    ;;                             ;;if it's a constant, it must be a natural, a boolean, or an array
    ;;                             (or (natp arg1)
    ;;                                 (booleanp arg1)
    ;;                                 (and (consp arg1) (all-natp arg1)))))
    ;;                       (or (not (consp arg2))
    ;;                           (let ((farg2 (unquote arg2)))
    ;;                             ;;if it's a constant, it must be a natural, a boolean, or an array
    ;;                             (or (natp arg2)
    ;;                                 (booleanp arg2)
    ;;                                 (and (consp arg2) (all-natp arg2))))))))
    (otherwise nil)))

;; Safety check: If no type is induced by a parent, we must not translate that parent.
;; todo: also need to handle EQUAL and UNSIGNED-BYTE-P.
(thm
  (implies (and (dag-function-call-exprp parent-expr)
                (not (get-induced-type nodenum parent-expr))
                (member-equal nodenum (dargs parent-expr))
                (natp nodenum))
           (not (can-always-translate-expr-to-stp (ffn-symb parent-expr)
                                                  (dargs parent-expr)
                                                  'dag-array dag-array dag-len known-nodenum-type-alist print)))
  :hints (("Goal" :in-theory (enable get-induced-type can-always-translate-expr-to-stp
                                     darg-quoted-posp darg-quoted-natp
                                     ;; member-equal-of-constant-when-not-equal-of-nth-0
                                     consp-of-cdr
                                     member-equal-of-cons ; applies to constant lists
                                     member-equal-when-consp-iff))))

(defthm equal-of-0-and-make-bv-type
  (equal (equal 0 (make-bv-type width))
         (equal 0 width)))

;; Sanity check: Everything we can translate has an obvious type, and it is not a BV type of width 0 (todo: also handle EQUAL and UNSIGNED-BYTE-P):
(thm
  (implies (and (can-always-translate-expr-to-stp fn dargs dag-array-name dag-array dag-len known-nodenum-type-alist print)
                (darg-listp dargs))
           (and (maybe-get-type-of-function-call fn dargs)
                (not (equal (make-bv-type 0)
                            (maybe-get-type-of-function-call fn dargs)))))
  :hints (("Goal" :in-theory (enable can-always-translate-expr-to-stp maybe-get-type-of-function-call maybe-get-type-of-bv-function-call member-equal
                                     unquote-if-possible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Select a type for NODENUM.  Returns (mv erp type).
;;note: this will only be called when its expr doesn't have an obvious type
;;nodenum must either have a known type or be used in at least one choppable context
;; TODO: would using an array be faster here?
(defund type-for-cut-nodenum (nodenum
                              known-nodenum-type-alist
                              dag-array
                              dag-parent-array
                              dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (< nodenum dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array)))))
  (let* ((result (assoc nodenum known-nodenum-type-alist)))
    (if result
        (let ((type (cdr result))) ;fixme what if the most-general-induced-type-aux might return a stronger type?
          (if (most-general-typep type) ;can this happen?
              (prog2$ (er hard? 'type-for-cut-nodenum "incompatible types for use of node ~x0" nodenum)
                      (mv (erp-t) type))
            (if (empty-typep type) ;can this happen?
                (let ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum)))
                  (progn$ ;; (print-array 'dag-array dag-array (+ 1 (maxelem parent-nodenums))) ;; todo: put back but consider guards
                   (cw "parent-nodenums: ~x0~%" parent-nodenums)
                   (er hard? 'type-for-cut-nodenum "expected an induced type from a choppable use for node ~x0" nodenum) ;is this message still right?
                   (mv (erp-t)
                       (most-general-type) ;;should be safe
                       )))
              (mv (erp-nil) type))))
      (b* ((parent-nodenums (aref1 'dag-parent-array dag-parent-array nodenum))
           (type (most-general-induced-type-aux parent-nodenums nodenum dag-array dag-len (empty-type)))
           ((when (not type)) ;print a message?
            (mv :bad-type nil)))
        (if (most-general-typep type)
            (prog2$ (er hard? 'type-for-cut-nodenum "No good induced type for node ~x0" nodenum)
                    (mv (erp-t) type))
          (if (empty-typep type)
              (progn$ ;; (print-array 'dag-array dag-array (+ 1 (maxelem parent-nodenums))) ;; todo: put back but consider guards
               (cw "parent-nodenums: ~x0~%" parent-nodenums)
               (er hard? 'type-for-cut-nodenum "expected an induced type from a choppable use for node ~x0, which is ~x1" nodenum (aref1 'dag-array dag-array nodenum)) ;is this message still right?
               (mv (erp-t)
                   (most-general-type) ;;should be safe
                   ))
            (mv (erp-nil) type)))))))


;; should be a bv, array, or boolean type
(local
  (defthm axe-typep-of-mv-nth-1-of-type-for-cut-nodenum
    (implies (and (not (mv-nth 0 (type-for-cut-nodenum nodenum known-nodenum-type-alist dag-array dag-parent-array dag-len))) ;drop?
                  (nodenum-type-alistp known-nodenum-type-alist)
                  (type-for-cut-nodenum nodenum known-nodenum-type-alist dag-array dag-parent-array dag-len))
             (axe-typep (mv-nth 1 (type-for-cut-nodenum nodenum known-nodenum-type-alist dag-array dag-parent-array dag-len))))
    :hints (("Goal" :in-theory (enable type-for-cut-nodenum)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns either nil (no node is given an empty type) or the nodenum of a node given an empty type.
(defund node-given-empty-type (known-nodenum-type-alist)
  (declare (xargs :guard (nodenum-type-alistp known-nodenum-type-alist)))
  (if (endp known-nodenum-type-alist)
      nil
    (let* ((entry (first known-nodenum-type-alist))
           (type (cdr entry)))
      (if (empty-typep type)
          (car entry)
        (node-given-empty-type (rest known-nodenum-type-alist))))))

(local
  (defthm node-given-empty-type-type
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (node-given-empty-type known-nodenum-type-alist))
             (and (integerp (node-given-empty-type known-nodenum-type-alist))
                  (<= 0 (node-given-empty-type known-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable node-given-empty-type nodenum-type-alistp)))))

(local
  (defthm <-of-node-given-empty-type
    (implies (and (all-< (strip-cars known-nodenum-type-alist) n)
                  (nodenum-type-alistp known-nodenum-type-alist)
                  (node-given-empty-type known-nodenum-type-alist))
             (< (node-given-empty-type known-nodenum-type-alist) n))
    :hints (("Goal" :in-theory (enable node-given-empty-type nodenum-type-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: compare to gather-nodes-to-translate-up-to-depth
;; Returns (mv erp nodenums-to-translate cut-nodenum-type-alist handled-node-array) ;the accumulators are extended
;; fixme: look for type mismatches..
;; todo: combine some recursive calls in this function?
;; When we decide to cut at a node (either because we can't translate it or we've hit the depth limit), we have to select a type for it.
;; TODO: Consider returning an error if a bad arity is found.
(defund process-nodenums-for-translation (worklist ;a list of nodenums to handle (each of these must either have an obvious type, a known-type, or be used in at least one choppable context)
                                          depth-limit ;a natural, or nil for no limit (in which case depth-array is meaningless)
                                          depth-array ; todo: what nodes have entries in this?
                                          handled-node-array
                                          dag-array dag-len dag-parent-array known-nodenum-type-alist
                                          ;;these are accumulators:
                                          nodenums-to-translate ; every node already in this list should have its flags set in handled-node-array (so we avoid duplicates)
                                          cut-nodenum-type-alist)
  (declare (xargs :guard (and (nat-listp worklist)
                              (or (natp depth-limit)
                                  (null depth-limit))
                              (implies depth-limit (array1p 'depth-array depth-array))
                              (if depth-limit (all-< worklist (alen1 'depth-array depth-array)) t) ;todo: and it contains rationals
                              (array1p 'handled-node-array handled-node-array)
                              (all-< worklist (alen1 'handled-node-array handled-node-array))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< worklist dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (all-natp nodenums-to-translate)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  ;; The measure is, first the number of unhandled nodes, then, if unchanged, check the length of the worklist.
                  :measure (make-ord 1
                                     (+ 1 ;coeff must be positive
                                        (if (not (natp (alen1 'handled-node-array handled-node-array)))
                                            0
                                          (+ 1 (- (alen1 'handled-node-array handled-node-array)
                                                  (num-handled-nodes 'handled-node-array handled-node-array)))))
                                     (len worklist))
                  :guard-hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) (MYQUOTEP DARGP))
                                 :do-not '(generalize eliminate-destructors)))))
  (if (or (endp worklist)
          (not (mbt (and (array1p 'handled-node-array handled-node-array)
                         (nat-listp worklist)
                         (all-< worklist (alen1 'handled-node-array handled-node-array))))))
      (mv (erp-nil) nodenums-to-translate cut-nodenum-type-alist handled-node-array)
    (let* ((nodenum (first worklist)))
      (if (aref1 'handled-node-array handled-node-array nodenum)
          ;;we've already handled this node, so skip it:
          (process-nodenums-for-translation (rest worklist) depth-limit depth-array handled-node-array
                                            dag-array dag-len dag-parent-array
                                            known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist)
        (let ((expr (aref1 'dag-array dag-array nodenum)))
          (if (atom expr) ;;variable, we'll definitely cut:
              (b* (((mv erp type-for-cut-nodenum) (type-for-cut-nodenum nodenum known-nodenum-type-alist dag-array dag-parent-array dag-len))
                   ((when erp) (mv erp nodenums-to-translate cut-nodenum-type-alist handled-node-array)))
                (process-nodenums-for-translation (rest worklist) depth-limit depth-array
                                                  (aset1 'handled-node-array handled-node-array nodenum t)
                                                  dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                  nodenums-to-translate
                                                  (acons nodenum type-for-cut-nodenum cut-nodenum-type-alist)))
            (let ((fn (ffn-symb expr)))
              (if (eq 'quote fn)
                  ;; a quoted constant; we always translate (could cutting out a constant ever be good?  maybe a constant array?)
                  ;; TODO: Do we know that the constant is of the right type?
                  (process-nodenums-for-translation (rest worklist) depth-limit depth-array
                                                    (aset1 'handled-node-array handled-node-array nodenum t)
                                                    dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                    (cons nodenum nodenums-to-translate)
                                                    ;;todo: add a type here?:
                                                    cut-nodenum-type-alist)
                ;; Function Call:
                (let* ((args (dargs expr)) ;rename to dargs
                       (translatep
                         (cond ((and depth-limit (< depth-limit (rfix (aref1 'depth-array depth-array nodenum)))) ;todo: drop the rfix (need to know that the depth-array contains numbers)
                                ;;node is too deep, so cut:
                                nil)
                               ;; todo: always cut certain operators, like bvmult?
                               ((can-always-translate-expr-to-stp fn args 'dag-array dag-array dag-len known-nodenum-type-alist t)
                                t)
                               ;; Special case for EQUAL (todo: add typed versions of equal and get rid of this?):
                               ((eq 'equal fn)
                                (and (= 2 (len args))
                                     (let* ((lhs (first args)) ; a nodenum or quotep
                                            (rhs (second args)) ; a nodenum or quotep
                                            ;; These 2 types are either obvious or assumed (not induced):
                                            ;;these do not include types from cut-nodenum-alist -- it wouldn't be sound to use those types (they could be induced types that assume this equality will be cut out)?
                                            (lhs-type (maybe-get-type-of-arg lhs dag-array known-nodenum-type-alist)) ;a type or nil for unknown
                                            (rhs-type (maybe-get-type-of-arg rhs dag-array known-nodenum-type-alist)) ;a type or nil for unknown
                                            )
                                       (and lhs-type
                                            rhs-type
                                            (or (and (bv-typep lhs-type) (bv-typep rhs-type))
                                                (and (boolean-typep lhs-type) (boolean-typep rhs-type))
                                                (and (bv-array-typep lhs-type)
                                                     (bv-array-typep rhs-type)
                                                     (<= 2 (bv-array-type-len lhs-type)) ;arrays of length 1 require 0 index bits and so are not supported
                                                     (<= 2 (bv-array-type-len rhs-type)) ;arrays of length 1 require 0 index bits and so are not supported
                                                     ;; todo: think about when this is not true (see defthm-stp-tests):
                                                     (equal (bv-array-type-len lhs-type) (bv-array-type-len rhs-type)) ; else we can't translate it (todo: or we could translate it to false!)
                                                     ))))))
                               ;; Special case for UNSIGNED-BYTE-P (todo: can we get rid of this?):
                               ((eq 'unsigned-byte-p fn) ; (unsigned-byte-p <size> <x>)
                                (and (= 2 (len args))
                                     (darg-quoted-posp (first args)) ;allow 0?
                                     (let* ((arg2 (second args)) ;could this be a quotep?
                                            (arg2-type (maybe-get-type-of-arg arg2 dag-array known-nodenum-type-alist)))
                                       (bv-typep arg2-type) ;error if not?
                                       )))
                               (t nil))))
                  (if translatep
                      (process-nodenums-for-translation (append-nodenum-dargs args (rest worklist)) ; perhaps causes the children to be translated as well
                                                        depth-limit depth-array
                                                        (aset1 'handled-node-array handled-node-array nodenum t)
                                                        dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                        (cons nodenum nodenums-to-translate)
                                                        cut-nodenum-type-alist)
                    ;; Cut:
                    (b* ((obvious-type (maybe-get-type-of-function-call fn args))
                         ((when (equal obvious-type (make-bv-type 0)))
                          (cw "ERROR: Encountered a BV node of width 0: ~x0." expr)
                          (mv :bv-of-width-0 nodenums-to-translate cut-nodenum-type-alist handled-node-array))
                         ;;ffixme what if there is a better known type or induced type?
                         ((mv erp type-for-cut-nodenum)
                          (if obvious-type
                              (mv (erp-nil) obvious-type)
                            (type-for-cut-nodenum nodenum known-nodenum-type-alist dag-array dag-parent-array dag-len)))
                         ((when erp) (mv erp nodenums-to-translate cut-nodenum-type-alist handled-node-array)))
                      (process-nodenums-for-translation (rest worklist) ; does not add the children, since we're cutting
                                                        depth-limit depth-array
                                                        (aset1 'handled-node-array handled-node-array nodenum t)
                                                        dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate
                                                        (acons nodenum type-for-cut-nodenum cut-nodenum-type-alist)))))))))))))

(local
  (defthm all-natp-of-mv-nth-1-of-process-nodenums-for-translation
    (implies (all-natp nodenums-to-translate)
             (all-natp (mv-nth 1 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm true-listp-of-mv-nth-1-of-process-nodenums-for-translation
    (implies (true-listp nodenums-to-translate)
             (true-listp (mv-nth 1 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm no-nodes-are-variablesp-of-mv-nth-1-of-process-nodenums-for-translation
    (implies (no-nodes-are-variablesp nodenums-to-translate 'dag-array dag-array dag-len)
             (no-nodes-are-variablesp (mv-nth 1 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))
                                      'dag-array dag-array dag-len))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation no-nodes-are-variablesp)))))

(local
  (defthm all-<-of-mv-nth-1-of-process-nodenums-for-translation
    (implies (and (all-< nodenums-to-translate dag-len)
                  (all-< worklist dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (all-< (mv-nth 1 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))
                    dag-len))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm nodenum-type-alistp-of-mv-nth-2-of-process-nodenums-for-translation
    (implies (and (nodenum-type-alistp cut-nodenum-type-alist)
                  (nodenum-type-alistp known-nodenum-type-alist))
             (nodenum-type-alistp (mv-nth 2 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-2-of-process-nodenums-for-translation
    (implies (and (all-< worklist dag-len)
                  (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                  (all-< (strip-cars known-nodenum-type-alist) dag-len)
;                (nat-listp worklist)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (all-< (strip-cars (mv-nth 2 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist)))
                    dag-len))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm alen1-of-mv-nth-3-of-process-nodenums-for-translation
    (equal (alen1 'handled-node-array (mv-nth 3 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist)))
           (alen1 'handled-node-array handled-node-array))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

(local
  (defthm array1p-of-mv-nth-3-of-process-nodenums-for-translation
    (implies (array1p 'handled-node-array handled-node-array)
             (array1p 'handled-node-array (mv-nth 3 (process-nodenums-for-translation worklist depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-nodenums-for-translation)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walk through the disjuncts, processing each one.  We strip the negation, if present, and analyze the core of the disjunct.  If the disjunct isn't a call of a known-boolean, we drop it.
;;otherwise, we process it top down.  for each node processed we can tell by looking at it what its type is (really?), and we have to decide whether to make a variable of that type, or translate the node (if the argument types are okay).
;; Returns (mv erp disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)
;;TODO: Think about something like this: (prove-with-stp '(+ 1 x)).  Why is the query false instead of a single boolean var?  Because non-known-booleans get dropped here.  Is that necessary at the top level?
;; TODO: Can we do it all in one worklist pass (call to process-nodenums-for-translation) instead of one for each disjunct?
;; TODO: If the disjunct is negated, that can induce a boolean type...  Perhaps so can appearing at the top-level of the clause.  But make sure the disjunct doesn't appear in any non-boolean context..
(defund process-disjuncts-for-translation (disjuncts ; a list of possibly-negated-nodenums
                                           depth-limit ;a natural, or nil for no limit (in which case depth-array is meaningless)
                                           depth-array
                                           handled-node-array ; tells us whether we've already processed (decided whether to cut or translate) each node
                                           dag-array dag-len dag-parent-array
                                           known-nodenum-type-alist
                                           ;;these are accumulators:
                                           disjuncts-to-include-in-query
                                           nodenums-to-translate
                                           cut-nodenum-type-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (or (natp depth-limit)
                                  (null depth-limit))
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (possibly-negated-nodenumsp disjuncts-to-include-in-query)
                              (all-natp nodenums-to-translate)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (array1p 'handled-node-array handled-node-array)
                              (all-< (strip-nots-from-possibly-negated-nodenums disjuncts) (alen1 'handled-node-array handled-node-array))
                              (implies depth-limit (array1p 'depth-array depth-array))
                              (if depth-limit (all-< (strip-nots-from-possibly-negated-nodenums disjuncts) (alen1 'depth-array depth-array)) t)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              ;;todo: more?
                              )
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :expand (;(possibly-negated-nodenumsp disjuncts)
                                          (strip-nots-from-possibly-negated-nodenums disjuncts)
                                          )))))
  (if (endp disjuncts)
      (mv (erp-nil) disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)
    (let* ((disjunct (first disjuncts))
           (disjunct-core (strip-not-from-possibly-negated-nodenum disjunct)) ;a nodenum ; todo: what about a nodenum of a NOT?
           (process-this-disjunctp
             ;; todo: improve the messages here (about "possibly ..")
            (let ((known-type-match (assoc disjunct-core known-nodenum-type-alist)))
              (if known-type-match
                  (let ((type (cdr known-type-match)))
                    (if (boolean-typep type)
                        t
                      (prog2$ (cw "TYPE ERROR: Disjunct (~x0) is given a type other than BOOLEAN in the known-nodenum-type-alist (possibly after stripping a not).~%" disjunct-core)
                              nil)))
                ;;no type from the alist, so check the expr for an obvious type (todo: would it be faster to do this first?):
                (let ((expr (aref1 'dag-array dag-array disjunct-core)))
                  (if (atom expr) ;variable
                      (prog2$ (cw "Dropping a disjunct that is a (possibly negated) variable: ~x0.~%" expr)
                              nil)
                    (if (call-of 'quote expr)
                        (prog2$ (cw "Dropping a disjunct that is the constant ~x0.~%" expr) ; can this happen?
                                nil)
                      (if (boolean-typep (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)))
                          t
                        (prog2$ (cw "Dropping a disjunct (node ~x0, possibly after stripping a not) that is a call to ~x1 (not a known boolean).~%" disjunct-core (ffn-symb expr))
                                nil)))))))))
      (if process-this-disjunctp
          (b* (;; nodenums-to-translate and cut-nodenum-type-alist get extended, and more nodes are marked in the handled-node-array:
               ((mv erp nodenums-to-translate cut-nodenum-type-alist handled-node-array)
                (process-nodenums-for-translation (list disjunct-core)
                                                  depth-limit
                                                  depth-array
                                                  handled-node-array
                                                  dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                  nodenums-to-translate cut-nodenum-type-alist))
               ((when erp) (mv erp disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)))
            (process-disjuncts-for-translation (rest disjuncts) depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                               (cons disjunct disjuncts-to-include-in-query) ;we can include this disjunct
                                               nodenums-to-translate cut-nodenum-type-alist))
        ;;drop this disjunct (TODO: Introduce a boolean var?)
        (process-disjuncts-for-translation (rest disjuncts) depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                           disjuncts-to-include-in-query ;don't add the disjunct
                                           nodenums-to-translate cut-nodenum-type-alist)))))

(local
  (defthm possibly-negated-nodenumsp-of-mv-nth-1-of-process-disjuncts-for-translation
    (implies (and (possibly-negated-nodenumsp disjuncts-to-include-in-query)
                  (possibly-negated-nodenumsp disjuncts))
             (possibly-negated-nodenumsp (mv-nth 1 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                                      disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation)))))

(local
  (defthm true-listp-of-mv-nth-2-of-process-disjuncts-for-translation
    (implies (true-listp nodenums-to-translate)
             (true-listp (mv-nth 2 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                      disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation)))))

(local
  (defthm all-natp-of-mv-nth-2-of-process-disjuncts-for-translation
    (implies (all-natp nodenums-to-translate)
             (all-natp (mv-nth 2 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                    disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation)))))

(local
  (defthm no-nodes-are-variablesp-of-mv-nth-2-of-process-disjuncts-for-translation
    (implies (no-nodes-are-variablesp nodenums-to-translate 'dag-array dag-array dag-len)
             (no-nodes-are-variablesp (mv-nth 2 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                                   disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))
                                      'dag-array dag-array dag-len))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation)))))

(local
  (defthm all-<-of-mv-nth-2-of-process-disjuncts-for-translation
    (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len) ;(all-< (strip-nots-from-possibly-negated-nodenums disjuncts) dag-len)
                  (all-< nodenums-to-translate dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (all-< (mv-nth 2 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                 disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))
                    dag-len))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation strip-nots-from-possibly-negated-nodenums)))))

(local
  (defthm bounded-possibly-negated-nodenumsp-of-mv-nth-1-of-process-disjuncts-for-translation
    (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                  (bounded-possibly-negated-nodenumsp disjuncts-to-include-in-query dag-len)
                  (all-< nodenums-to-translate dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (bounded-possibly-negated-nodenumsp (mv-nth 1 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                                              disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))
                                                 dag-len))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation strip-nots-from-possibly-negated-nodenums)))))

(local
  (defthm nodenum-type-alistp-of-mv-nth-3-of-process-disjuncts-for-translation
    (implies (and (nodenum-type-alistp cut-nodenum-type-alist)
                  (nodenum-type-alistp known-nodenum-type-alist))
             (nodenum-type-alistp (mv-nth 3 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                               disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist))))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-3-of-process-disjuncts-for-translation
    (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len) ;(all-< (strip-nots-from-possibly-negated-nodenums disjuncts) dag-len)
                  (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                  (all-< (strip-cars known-nodenum-type-alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  )
             (all-< (strip-cars (mv-nth 3 (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                                             disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)))
                    dag-len))
    :hints (("Goal" :in-theory (enable process-disjuncts-for-translation strip-nots-from-possibly-negated-nodenums)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
;; This cuts out any stuff we can't translate, or any stuff that's too deep:
(defund prove-disjunction-with-stp-at-depth (depth-limit ;a natural, or nil for no limit (in which case depth-array is meaningless)
                                             disjuncts ; possibly-negated-nodenums
                                             depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                             base-filename
                                             print max-conflicts counterexamplep print-cex-as-signedp state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (or (natp depth-limit) (equal nil depth-limit))
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (implies depth-limit (array1p 'depth-array depth-array))
                              (if depth-limit (all-< (strip-nots-from-possibly-negated-nodenums disjuncts) (alen1 'depth-array depth-array)) t)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (all-< (strip-cars known-nodenum-type-alist) dag-len)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts) (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (e/d (integer-listp-when-nat-listp) (natp))))))
  (b* (;; Array to track which nodes we've considered as we go through the disjuncts (disjuncts may have nodes in common):
       (handled-node-array (make-empty-array 'handled-node-array (+ 1 (max-nodenum-in-possibly-negated-nodenums disjuncts))))
       ;; Decide which disjuncts to include in the query and which nodes under them to translate / cut:
       ;; TODO: What if a node is shallow in one disjunct and deep in another?  How should we treat it?
       ((mv erp disjuncts-to-include-in-query nodenums-to-translate cut-nodenum-type-alist)
        (process-disjuncts-for-translation disjuncts depth-limit depth-array handled-node-array
                                           dag-array dag-len dag-parent-array
                                           known-nodenum-type-alist
                                           nil ;initial disjunct-nodenums-to-include-in-query
                                           nil ;initial nodenums-to-translate
                                           nil ;initial cut-nodenum-type-alist
                                           ))
       ((when erp) (mv :error state))
       (- (and (eq print :verbose)
               (cw "disjuncts in query: ~x0.~% cut-nodenum-type-alist: ~x1. ~%" disjuncts-to-include-in-query cut-nodenum-type-alist)))
       ((when (not (consp disjuncts-to-include-in-query)))
        (cw "Note: No disjuncts. Not calling STP.~%")
        (mv :invalid state)))
    ;;won't the disjuncts be the same for every depth?
    (prove-query-with-stp (translate-disjunction disjuncts-to-include-in-query)
                          (if depth-limit (concatenate 'string "at depth " (nat-to-string depth-limit)) "on uncut goal")
                          'dag-array dag-array dag-len
                          (reverse (merge-sort-< nodenums-to-translate)) ;make a merge-sort-> ??
                          nil ; extra-asserts ; todo: do need any?
                          (concatenate 'string base-filename (if depth-limit (concatenate 'string  "-depth-" (nat-to-string depth-limit)) "-uncut"))
                          cut-nodenum-type-alist
                          print
                          max-conflicts
                          nil ;initial constant-array-info
                          counterexamplep
                          print-cex-as-signedp
                          state)))

(local
  (defthm counterexamplep-of-cadr-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth
    (implies (and (equal :counterexample (car (mv-nth 0 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state))))
                  (nodenum-type-alistp known-nodenum-type-alist))
             (counterexamplep (cadr (mv-nth 0 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))))
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depth)))))

(local
  (defthm stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth
    (implies (nodenum-type-alistp known-nodenum-type-alist)
             (stp-resultp (mv-nth 0 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state))))
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depth)))))

(local
  (defthm bounded-stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth
    (implies (and (nodenum-type-alistp known-nodenum-type-alist)
                  (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                  (all-< (strip-cars known-nodenum-type-alist) dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len))
             (bounded-stp-resultp (mv-nth 0 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state))
                                  dag-len))
    :otf-flg t
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depth)))))

(local
  (defthm w-of-mv-nth-1-of-prove-disjunction-with-stp-at-depth
    (equal (w (mv-nth 1 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
           (w state))
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depth)))))

(local
  (defthm state-p-of-mv-nth-1-of-prove-disjunction-with-stp-at-depth
    (implies (state-p state)
             (state-p (mv-nth 1 (prove-disjunction-with-stp-at-depth depth-limit disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist base-filename print max-conflicts counterexamplep print-cex-as-signedp state))))
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;binary search the range [min-depth, max-depth] to try to find a cut depth at which STP says valid
;Returns (mv result state) where RESULT is :error, :valid, :invalid, or :timedout.
;terminates because the difference in depths decreases
(defund prove-disjunction-with-stp-at-depths (min-depth
                                              max-depth
                                              depth-array
                                              known-nodenum-type-alist
                                              disjuncts ; possibly-negated-nodenums
                                              dag-array ;must be named 'dag-array
                                              dag-len
                                              dag-parent-array ;must be named 'dag-parent-array
                                              base-filename    ;a string
                                              print
                                              max-conflicts ;a number of conflicts, or nil for no max
                                              counterexamplep
                                              print-cex-as-signedp
                                              state)
  (declare (xargs :guard (and (posp min-depth)
                              (natp max-depth)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nodenum-type-alistp known-nodenum-type-alist)
                              (all-< (strip-cars known-nodenum-type-alist) dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (array1p 'depth-array depth-array)
                              (all-< (strip-nots-from-possibly-negated-nodenums disjuncts)
                                     (alen1 'depth-array depth-array))
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts) (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state
                  :measure (nfix (+ 1 (- max-depth min-depth)))
                  :hints (("Goal" :in-theory (e/d (natp)
                                                  (ceiling-in-terms-of-floor ;disable?
                                                   ))))
                  :guard-hints (("Goal" :in-theory (e/d (natp)
                                                        (ceiling-in-terms-of-floor))))))
  (if (or (not (mbt (natp min-depth)))
          (not (natp max-depth))
          (< max-depth min-depth))
      (prog2$ (cw "No more depths to try.~%")
              (mv *timedout* ;ttodo: think about this.  should we ever instead say 'invalid'?  maybe we don't even call this function if the whole goal didn't time out?
                  state))
    (b* ((depth (ceiling (/ (+ min-depth max-depth) 2) 1)) ;take the average (could round down instead..)
         ((mv result state)
          ;; This cuts out any stuff we can't translate, or any stuff that's too deep:
          (prove-disjunction-with-stp-at-depth depth disjuncts depth-array dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                    base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
      (if (eq result *error*)
          (mv *error* state)
        (if (eq result *valid*)
            (mv *valid* state)
          (if (eq result *timedout*)
              ;; STP timed out, so don't try any deeper depths (they will probably time-out too). recur on the range of shallower depths
              (prove-disjunction-with-stp-at-depths min-depth (+ -1 depth) depth-array known-nodenum-type-alist disjuncts
                                                   dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)
            (progn$
             ;; STP said invalid or gave a counterexample, so don't try any shallower depths (they will also be invalid). recur on the range of deeper depths
             ;; TODO: Use the counterexample here (check whether possible or certain?)?
             (prove-disjunction-with-stp-at-depths (+ 1 depth) max-depth depth-array known-nodenum-type-alist disjuncts
                                                  dag-array dag-len dag-parent-array
                                                  base-filename print max-conflicts
                                                  counterexamplep print-cex-as-signedp state))))))))

(local
  (defthm w-of-mv-nth-1-of-prove-disjunction-with-stp-at-depths
    (equal (w (mv-nth 1 (prove-disjunction-with-stp-at-depths min-depth max-depth depth-array known-nodenum-type-alist disjuncts dag-array dag-len
                                                                   dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
           (w state))
    :hints (("Goal" :in-theory (enable prove-disjunction-with-stp-at-depths)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: move this to the translate-dag-to-stp book?
;; Attempt to prove that the disjunction of DISJUNCTS is non-nil.  Works by cutting out non-(bv/array/bool) stuff and calling STP.  Also uses heuristic cuts.
;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
;; TODO: the cutting could look at shared nodes (don't cut above the shared node frontier)?
(defund prove-disjunction-with-stp (disjuncts ; possibly-negated nodenums, can't be empty
                                    dag-array ;must be named 'dag-array (todo: generalize?)
                                    dag-len
                                    dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
                                    base-filename
                                    print
                                    max-conflicts ;a number of conflicts, or nil for no max
                                    counterexamplep ;perhaps this should always be t?
                                    print-cex-as-signedp
                                    state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                              (consp disjuncts)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (e/d (;all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-disjunctionp ; for the call of build-known-nodenum-type-alist
                                                         myquotep-when-axe-disjunctionp
                                                         quotep-when-axe-disjunctionp)
                                                        (myquotep
                                                         quotep))))))
  (b* (;; ((when (not (consp disjuncts))) ; not possible?
       ;;  (cw "(No disjuncts, so no point in calling STP.)~%")
       ;;  (mv *invalid* state))
       ;; Dig out individual disjuncts (this only preserves IFF):
       ;; This may be needed to get the most precise type info:
       (disjunction (get-axe-disjunction-from-dag-items disjuncts 'dag-array dag-array dag-len))
       ((when (disjunction-is-truep disjunction))
        (prog2$ (cw "(Note: Disjunction is obviously true. Proved it.)~%")
                (mv *valid* state)))
       ((when (disjunction-is-falsep disjunction))
        (prog2$ (cw "(Note: Disjunction is obviously false. Failed to prove it.)~%")
                (mv *invalid* state)))
       (disjuncts disjunction) ;; these are possibly-negated nodenums

       ;;Here we attempt to assign types to nodes in the DAG that lack obvious
       ;;types ("obvious types" are types you can tell just from looking at the
       ;;nodes's expressions).  To do so, we assume that all the disjuncts are
       ;;false.  This is safe, because if any disjunct is true, so is the entire
       ;;clause.

       ;;All of the types computed here are known for sure; they are different from types on a term "induced" by how the term is used (e.g., only 32-bits of x are used in (bvxor 32 x y)).
       ;; todo: think about the ramifications of doing this before calculating the depths
       (known-nodenum-type-alist ; todo: optimize by using an array instead of an alist?
         (build-known-nodenum-type-alist disjuncts dag-array dag-len))
       (- (and (eq :verbose print)
               (cw "known-nodenum-type-alist: ~x0.~%" known-nodenum-type-alist)))
       ;; Check for contradictions in the type info:
       (maybe-node-given-empty-type (node-given-empty-type known-nodenum-type-alist)) ; we could compute this as we build the alist
       ((when maybe-node-given-empty-type) ;move this test up before we print?
        ;; We assumed the negations of the disjuncts and got a contradiction (about types), so they can't all be false:
        (cw "(WARNING: Goal is true due to type mismatch on:~%")
        (print-dag-array-node-and-supporters 'dag-array dag-array maybe-node-given-empty-type)
        (cw ")~%")
        (mv *valid* state))
       (- (and (print-level-at-least-tp print) (cw "(Calling STP (perhaps at several depths) on ~s0.~%" base-filename)))
       (- (and (eq :verbose print) ; todo: improve printing
               (prog2$ (cw "Disjuncts:~% ~x0~%This case: ~x1~%Full disjuncts:~%"
                           disjuncts
                           (expressions-for-this-case disjuncts dag-array dag-len) ;call print-list on this?
                           )
                       (print-dag-array-node-and-supporters-lst (strip-nots-from-possibly-negated-nodenums disjuncts) 'dag-array dag-array))))
       ;; First try without heuristic cuts (untranslatable things will still be cut out):
       ((mv result state)
        (prove-disjunction-with-stp-at-depth nil ;no depth limit
                                                  disjuncts
                                                  nil ;fake depth-array
                                                  dag-array dag-len dag-parent-array known-nodenum-type-alist
                                                  base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
    (if (eq result *error*)
        (mv *error* state)
      (if (eq result *valid*)
          (prog2$ (and (print-level-at-least-tp print) (cw "STP proved the uncut goal ~s0.)~%" base-filename))
                  (mv *valid* state))
        (if (eq result *invalid*)
            ;; The goal is invalid.  Since we didn't cut anything out, the only thing to do is give up (any cut goals would be more general and would also be invalid)
            (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename))
                    (mv *invalid* state))
          (if (call-of *counterexample* result) ;TODO: Pass this back!
              ;; The goal is invalid.  Since we didn't cut anything out, the only thing to do is give up (any cut goals would be more general and would also be invalid)
              (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename))
                      (mv result state))
            (if (call-of *possible-counterexample* result) ;TODO: Pass this back?
                ;; The goal is invalid.  Since we didn't cut anything out, the only thing to do is give up (any cut goals would be more general and would also be invalid)
                (prog2$ (and (print-level-at-least-tp print) (cw "Giving up because the uncut goal ~s0 is invalid.)~%" base-filename)) ; todo: what if untranslatable stuff was cut out that makes the goal valid?
                        (mv result state))
              (if (eq result *timedout*)
                  ;; STP timed out on the uncut case.  Now binary search for the right depth:
                  ;; TTODO: Start with max-depth minus 1 since we've already timed out on the full proof!?
                  (b* (((mv depth-array max-depth)
                        (make-depth-array-for-nodes (strip-nots-from-possibly-negated-nodenums disjuncts) ;todo: avoid consing this up?
                                                    'dag-array dag-array dag-len))
                       ((mv result state)
                        (prove-disjunction-with-stp-at-depths 1 max-depth depth-array known-nodenum-type-alist disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
                    ;;todo: move printing to sub-function?
                    (if (eq result *error*)
                        (mv *error* state)
                      (if (eq result *valid*)
                          (prog2$ (and (print-level-at-least-tp print) (cw "STP proved ~s0.)~%" base-filename))
                                  (mv *valid* state))
                        (if (eq result *invalid*) ;TODO: is this possible?
                            (prog2$ (and (print-level-at-least-tp print) (cw "STP failed to find a depth at which ~s0 would be valid.)~%" base-filename))
                                    (mv *invalid* state))
                          (prog2$ (and (print-level-at-least-tp print) (cw "STP failed to find a depth at which ~s0 would be valid.)~%" base-filename))
                                  (mv *timedout* state))))))
                ;;todo: prove this can't happen:
                (mv (er hard? 'prove-disjunction-with-stp "Bad result, ~x0, from prove-disjunction-with-stp-at-depth." result)
                    state)))))))))

(defthm stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp
  (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (stp-resultp (mv-nth 0 (prove-disjunction-with-stp disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state))))
  :hints (("Goal"
           :use (:instance stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth
                           (known-nodenum-type-alist (build-known-nodenum-type-alist (get-axe-disjunction-from-dag-items disjuncts 'dag-array
                                                                                                                         dag-array dag-len)
                                                                                     dag-array dag-len))

                           (depth-array nil)
                           (disjuncts (get-axe-disjunction-from-dag-items disjuncts 'dag-array
                                                                          dag-array dag-len))
                           (depth-limit nil))
           :in-theory (e/d (prove-disjunction-with-stp stp-resultp) (stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth)))))

(defthm bounded-stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp
  (implies (and (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (bounded-stp-resultp (mv-nth 0 (prove-disjunction-with-stp disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state))
                                dag-len))
  :hints (("Goal"
           :use (:instance bounded-stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth
                           (known-nodenum-type-alist (build-known-nodenum-type-alist (get-axe-disjunction-from-dag-items disjuncts 'dag-array
                                                                                                                         dag-array dag-len)
                                                                                     dag-array dag-len))

                           (depth-array nil)
                           (disjuncts (get-axe-disjunction-from-dag-items disjuncts 'dag-array
                                                                          dag-array dag-len))
                           (depth-limit nil))
           :in-theory (e/d (prove-disjunction-with-stp bounded-stp-resultp) (bounded-stp-resultp-of-mv-nth-0-of-prove-disjunction-with-stp-at-depth)))))

(defthm counterexamplep-of-cadr-of-mv-nth-0-of-prove-disjunction-with-stp
  (implies (and (equal :counterexample (car (mv-nth 0 (prove-disjunction-with-stp disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state))))
                (bounded-possibly-negated-nodenumsp disjuncts dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (counterexamplep (cadr (mv-nth 0 (prove-disjunction-with-stp disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))))
  :hints (("Goal" :in-theory (enable prove-disjunction-with-stp))))

(defthm w-of-mv-nth-1-of-prove-disjunction-with-stp
  (equal (w (mv-nth 1 (prove-disjunction-with-stp disjuncts dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
         (w state))
  :hints (("Goal" :in-theory (enable prove-disjunction-with-stp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove that the HYPS imply the CONC.
;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
(defund prove-implication-with-stp (hyps ; possibly-negated-nodenums
                                    conc ; a possibly-negated-nodenum
                                    dag-array ;must be named 'dag-array (todo: generalize?)
                                    dag-len
                                    dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
                                    base-filename
                                    print
                                    max-conflicts ;a number of conflicts, or nil for no max
                                    counterexamplep
                                    print-cex-as-signedp
                                    state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-possibly-negated-nodenump conc dag-len)
                              (bounded-possibly-negated-nodenumsp hyps dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp))
                  :stobjs state))
  ;; we prove (or (not <hyp1>) (not <hyp2>) ... (not <hypn>) conc):
  (prove-disjunction-with-stp (cons conc (negate-possibly-negated-nodenums hyps)) ; todo: avoid double negation if one of the hyps is a nodenum whose expr is a call of NOT?
                              dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state))

(local
  (defthm w-of-mv-nth-1-of-prove-implication-with-stp
    (equal (w (mv-nth 1 (prove-implication-with-stp hyps conc dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state)))
           (w state))
    :hints (("Goal" :in-theory (enable prove-implication-with-stp)))))

(defthm bounded-stp-resultp-of-mv-nth-0-of-prove-implication-with-stp
  (implies (and (bounded-possibly-negated-nodenump conc dag-len)
                (bounded-possibly-negated-nodenumsp hyps dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (bounded-stp-resultp (mv-nth 0 (prove-implication-with-stp hyps conc dag-array dag-len dag-parent-array base-filename print max-conflicts counterexamplep print-cex-as-signedp state))
                                dag-len))
  :hints (("Goal" :in-theory (e/d (prove-implication-with-stp) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to establish that the darg is either known to be true or known to be false.
;; Returns (mv erp result state), where result is :true (meaning non-nil), :false, or :unknown.
;; TODO: Also use rewriting?  See also try-to-resolve-test.
;; TODO: Generalize the printing, which refers to the darg here as a "test".
(defund try-to-resolve-darg-with-stp (darg
                                      assumptions ; possibly-negated-nodenums
                                      dag-array ;must be named 'dag-array (todo: generalize?)
                                      dag-len
                                      dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
                                      base-filename
                                      print
                                      max-conflicts ;a number of conflicts, or nil for no max
                                      ;; counterexamplep
                                      state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (dargp-less-than darg dag-len)
                              (bounded-possibly-negated-nodenumsp assumptions dag-len)
                              (stringp base-filename)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :stobjs state))
  (b* (((when (consp darg)) ; test for quotep
        (if (unquote darg)
            (mv (erp-nil) :true state)
          (mv (erp-nil) :false state)))
       (nodenum darg) ; darg is a nodenum
       (- (and (print-level-at-least-tp print) (cw "(Attempting to resolve test with STP using ~x0 assumptions.~%" (len assumptions))))
       ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first (e.g., by running a test).
       (- (and (print-level-at-least-tp print) (cw "(Attempting to prove test true with STP:~%")))
       ((mv true-result state)
        (prove-implication-with-stp assumptions
                                    nodenum
                                    dag-array dag-len dag-parent-array
                                    base-filename print max-conflicts
                                    nil      ; counterexamplep
                                    nil      ; print-cex-as-signedp
                                    state))
       ((when (eq *error* true-result))
        (prog2$ (er hard? 'try-to-resolve-darg-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* true-result)) ;; STP proved the test
        (prog2$ (and (print-level-at-least-tp print) (cw "STP proved the test true.))~%"))
                (mv (erp-nil) :true state)))
       (- (and (print-level-at-least-tp print) (cw "STP failed to prove the test true (~x0).)~%" true-result)))
       (- (and (print-level-at-least-tp print) (cw "(Attempting to prove test false with STP:~%")))
       ((mv false-result state)
        (prove-implication-with-stp assumptions
                                    `(not ,nodenum)
                                    dag-array dag-len dag-parent-array
                                    base-filename print max-conflicts
                                    nil      ;counterexamplep
                                    nil      ; print-cex-as-signedp
                                    state))
       ((when (eq *error* false-result))
        (prog2$ (er hard? 'try-to-resolve-darg-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* false-result)) ;; STP proved the negation of the test
        (prog2$ (and (print-level-at-least-tp print) (cw "STP proved the test false (~x0).))~%" false-result))
                (mv (erp-nil) :false state)))
       (- (and (print-level-at-least-tp print) (cw "STP did not resolve the test.))~%"))))
    (mv (erp-nil) :unknown state)))

(defthm w-of-mv-nth-2-of-try-to-resolve-darg-with-stp
  (equal (w (mv-nth 2 (try-to-resolve-darg-with-stp dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
         (w state))
  :hints (("Goal" :in-theory (enable try-to-resolve-darg-with-stp))))

;; ;; Returns (mv erp result state) where RESULT is :true (meaning non-nil), :false, or :unknown
;; ;; Never used!  Similar to try-to-resolve-darg-with-stp.
;; (defund try-to-resolve-test-with-stp (test       ; a nodenum
;;                                       assumptions ; possibly-negated-nodenums
;;                                       dag-array ;must be named 'dag-array (todo: generalize?)
;;                                       dag-len
;;                                       dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
;;                                       base-filename
;;                                       print
;;                                       max-conflicts ;a number of conflicts, or nil for no max
;;                                       ;;counterexamplep
;;                                       state)
;;   (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
;;                               (natp test)
;;                               (< test dag-len)
;;                               (bounded-possibly-negated-nodenumsp assumptions dag-len)
;;                               (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
;;                               (equal (alen1 'dag-parent-array dag-parent-array)
;;                                      (alen1 'dag-array dag-array))
;;                               (stringp base-filename)
;;                               (print-levelp print)
;;                               (or (null max-conflicts)
;;                                   (natp max-conflicts))
;;                               ;; (booleanp counterexamplep)
;;                               )
;;                   :stobjs state))
;;   (b* (((mv true-result state) (prove-implication-with-stp assumptions
;;                                                            test
;;                                                            dag-array dag-len dag-parent-array
;;                                                            base-filename print max-conflicts
;;                                                            nil ; counterexamplep (todo: maybe use and return)
;;                                                            nil ; print-cex-as-signedp
;;                                                            state))
;;        ((when (eq :error true-result)) (mv :error-proving-implication :unknown state))
;;        ((when (eq :valid true-result)) (mv (erp-nil) :true state))
;;        ((mv false-result state) (prove-implication-with-stp assumptions
;;                                                             `(not, test)
;;                                                             dag-array dag-len dag-parent-array
;;                                                             base-filename print max-conflicts
;;                                                             nil ; counterexamplep (todo: maybe use and return)
;;                                                             nil ; print-cex-as-signedp
;;                                                             state))
;;        ((when (eq :error false-result)) (mv :error-proving-implication :unknown state))
;;        ((when (eq :valid false-result)) (mv (erp-nil) :false state)))
;;     (mv (erp-nil) :unknown state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Functions below this point deal with terms rather than dags:

;; Attempt to use STP to prove the disjunction of the terms in CLAUSE.
;Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
;todo: pass in other options?
;todo: have this print balanced parens
;todo: exploit boolean structure in the hyps (and conc?)
;todo?: deprecate in favor of a version that just takes a single term (note that we may need to look into the boolean structure of the term to get assumptions that tell us the types of things?)
;; Could put 'term' in the name.
(defund prove-clause-with-stp (clause counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp-when-nat-listp)))))
  (b* (;; Handle an empty clause:
       ((when (not clause))
        (cw "(Note: Cannot prove the empty clause.)~%")
        (mv *invalid* state))
       ;; Merge all the disjuncts in the clause into a single DAG:
       ;; TODO: for NOTs, avoid adding the NOT node to the DAG (prove-disjunction-with-stp can take negated nodenums)
       ((mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array & &)
        (make-terms-into-dag-array-basic clause 'dag-array 'dag-parent-array nil))
       ((when erp) (mv *error* state)) ;todo: consider passing back the erp in the standard way
       ;; TODO: Apply the pre-stp-rules here, using the basic clause rewriter
       ;; Handle any disjuncts that are constants:
       ((mv provedp nodenums)
        (handle-constant-disjuncts nodenums-or-quoteps nil)))
    (if provedp
        (prog2$ (cw "(Note: Proved the clause because of a constant disjunct.)~%")
                (mv *valid* state))
      (if (not nodenums)
          (prog2$ (cw "(FAILED: Failed to prove the clause because all disjuncts are nil constants.)~%")
                  (mv *invalid* state))
        (prove-disjunction-with-stp nodenums
                                    dag-array ;must be named 'dag-array
                                    dag-len
                                    dag-parent-array ;must be named 'dag-parent-array
                                    base-filename
                                    print
                                    max-conflicts
                                    counterexamplep
                                    print-cex-as-signedp
                                    state)))))

(defthm w-of-mv-nth-1-of-prove-clause-with-stp
  (equal (w (mv-nth 1 (prove-clause-with-stp clause counterexamplep print-cex-as-signedp max-conflicts print base-filename state)))
         (w state))
  :hints (("Goal" :in-theory (enable prove-clause-with-stp))))

;; would say bounded-stp-resultp but what would the bound be?
(defthm stp-resultp-of-mv-nth-0-of-prove-clause-with-stp
  (implies (pseudo-term-listp clause)
           (stp-resultp (mv-nth 0 (prove-clause-with-stp clause counterexamplep print-cex-as-signedp max-conflicts print base-filename state))))
  :hints (("Goal" :in-theory (enable prove-clause-with-stp bounded-possibly-negated-nodenumsp-when-nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Attempts to use STP to prove CONC assuming HYPS.
;; ;Returns (mv result state) where RESULT is :error, :valid, :invalid,
;; :timedout, (:counterexample <counterexample>), or (:possible-counterexample
;; <counterexample>).
(defund prove-term-implication-with-stp (conc hyps counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
  (declare (xargs :guard (and (pseudo-termp conc)
                              (pseudo-term-listp hyps)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state))
  (b* ((negated-hyps (wrap-all 'not hyps)) ;inefficient - TODO: remove double negation?
       (clause (cons conc negated-hyps)))
    (prove-clause-with-stp clause counterexamplep print-cex-as-signedp max-conflicts print base-filename state)))

(defthm w-of-mv-nth-1-of-prove-term-implication-with-stp
  (equal (w (mv-nth 1 (prove-term-implication-with-stp conc hyps counterexamplep print-cex-as-signedp max-conflicts print base-filename state)))
         (w state))
  :hints (("Goal" :in-theory (enable prove-term-implication-with-stp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splits TERM into hyps and a conclusion when possible.
;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
(defund prove-term-with-stp (term counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (print-levelp print)
                              (stringp base-filename))
                  :stobjs state))
  (b* (((mv hyps conc) (term-hyps-and-conc term))) ;split term into hyps and conclusion
    (prove-term-implication-with-stp conc hyps counterexamplep print-cex-as-signedp max-conflicts print base-filename state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version avoids imposing invariant-risk on callers, because it has a guard that is just a stobj recognizer.
;Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
(defund prove-term-with-stp-unguarded (term counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
  (declare (xargs :stobjs state))
  (if (and (pseudo-termp term)
           (booleanp counterexamplep)
           (booleanp print-cex-as-signedp)
           (or (null max-conflicts)
               (natp max-conflicts))
           (print-levelp print)
           (stringp base-filename))
      (prove-term-with-stp term counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
    (prog2$ (er hard? 'prove-term-with-stp-unguarded "Bad input.")
            (mv :error state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
(defund translate-and-prove-term-with-stp (term counterexamplep print-cex-as-signedp max-conflicts print base-filename state)
  (declare (xargs :guard (and ;; term is untranslated
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (print-levelp print)
                              (stringp base-filename))
                  :mode :program ;because of translate-term
                  :stobjs state))
  (prove-term-with-stp-unguarded (translate-term term 'translate-and-prove-term-with-stp (w state))
                                 counterexamplep print-cex-as-signedp max-conflicts print base-filename state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv result state) where RESULT is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
;TODO: Deprecate in favor of defthm-stp?  We could make a thm-stp too.
;TODO: Allow a name to be passed in
(defmacro prove-with-stp (term
                          &key
                          (counterexample 't)
                          (print-cex-as-signedp 'nil)
                          (max-conflicts '*default-stp-max-conflicts*)
                          (print 'nil))
  `(translate-and-prove-term-with-stp ,term ',counterexample ',print-cex-as-signedp ,max-conflicts ',print
                                      "USER-QUERY"
                                      state))
