; A tool to make an Axe Rewriter for a given application
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains the tool make-rewriter-simple, which creates custom
;; rewriters.  When calling it, the user indicates an evaluator to use for
;; ground terms, an evaluator to use for syntaxp functions, and an evaluator to
;; use for bind-free functions.

;; The generated rewriter is a simple variant of the Axe Rewriter (no
;; work-hard, no calling the prover or stp, no simplify-xors).

;; If you have rules that contain work-hard hyps, consider passing in work-hard as a rule, to expand it.

;; Consider doing (set-evisc-tuple t :iprint nil :sites :gag-mode) when working with
;; calls to make-rewriter-simple, to prevent printing of enormous induction
;; schemes.

;; TODO: add a function to simplify a dag.

(include-book "rewriter-common")
(include-book "supporting-nodes") ; for drop-non-supporters-array
(include-book "make-node-replacement-alist")
(include-book "node-replacement-array2")
(include-book "refined-assumption-alists")
(include-book "rewriter-support") ;make local? but may be needed by the generated rewriters
(include-book "tries")
(include-book "rule-limits")
(include-book "rule-alists") ; for get-rules-for-fn
(include-book "make-substitution-code-simple")
(include-book "make-instantiation-code-simple")
(include-book "make-instantiation-code-simple-free-vars")
(include-book "make-instantiation-code-simple-no-free-vars")
(include-book "dag-array-builders")
(include-book "memoization")
(include-book "dag-array-printing2")
(include-book "unify-tree-and-dag")
(include-book "unify-term-and-dag-fast")
(include-book "hit-counts")
(include-book "dag-to-term")
(include-book "kestrel/utilities/defconst-computed" :dir :system) ;not strictly needed
;(include-book "def-dag-builder-theorems")
(include-book "kestrel/utilities/all-vars-in-term-bound-in-alistp" :dir :system)
(include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system) ;drop?
(include-book "kestrel/alists-light/strip-cdrs" :dir :system) ;need strip-cdrs-of-append for the generated proofs
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(defthm trees-to-memoizep-of-cons-if-not-equal-car
  (equal (trees-to-memoizep (cons-if-not-equal-car tree trees))
         (and (tree-to-memoizep tree)
              (trees-to-memoizep trees)))
  :hints (("Goal" :in-theory (enable cons-if-not-equal-car))))

(DEFTHMd <-OF-+-OF-1-WHEN-natps
  (IMPLIES (AND (SYNTAXP (NOT (QUOTEP Y)))
                (natp X)
                (natp Y))
           (EQUAL (< X (+ 1 Y)) (<= X Y))))

(defthm <-of-if-arg2
  (equal (< x (if test y z))
         (if test
             (< x y)
           (< x z))))

(defthmd <=-trans
  (implies (and (<= x free)
                (<= free y))
           (<= x y)))

(defthmd <=-trans-2
  (implies (and (<= free y)
                (<= x free))
           (<= x y)))

;dup?
(defthm not-equal-self
  (not (< x x)))

;; Can't be local
(defun simplify-trees-and-add-to-dag-induct (trees count)
  (declare (xargs :measure (len trees)))
  (if (or (not (mbt (natp count)))
          (= 0 count))
      (list trees count)
    (if (atom trees)
        (list trees count)
      (simplify-trees-and-add-to-dag-induct (rest trees) (+ -1 count)))))

(defthm all-dargp-of-reverse-list
  (equal (all-dargp (reverse-list x))
         (all-dargp x))
  :hints (("Goal" :in-theory (enable all-dargp))))

;dup.  needed for proofs of the generated functions
(defthm symbol-listp-of-append2
  (equal (symbol-listp (append x y))
         (and (symbol-listp (true-list-fix x))
              (symbol-listp y)))
  :hints (("Goal" :in-theory (enable append symbol-listp true-list-fix))))

;gen
(defthm PSEUDO-DAG-ARRAYP-of-+-of-1-and-LARGEST-NON-QUOTEP-of-car
  (implies (and (DARGP-LESS-THAN-LIST-LISTP ASSUMPTION-ARG-LISTS DAG-LEN)
                (consp ASSUMPTION-ARG-LISTS)
                (PSEUDO-DAG-ARRAYP 'DAG-ARRAY DAG-ARRAY dag-len))
           (PSEUDO-DAG-ARRAYP
            'DAG-ARRAY
            DAG-ARRAY
            (BINARY-+ '1
                      (LARGEST-NON-QUOTEP (CAR ASSUMPTION-ARG-LISTS))))))

(defthmd true-list-of-car-when-DARGP-LESS-THAN-LIST-LISTP
  (implies (and (DARGP-LESS-THAN-LIST-LISTP ASSUMPTION-ARG-LISTS DAG-LEN)
                (consp ASSUMPTION-ARG-LISTS))
           (TRUE-LISTP (CAR ASSUMPTION-ARG-LISTS))))

(defthmd all-myquote-or-natp-of-car-when-dargp-less-than-list-listp
  (implies (and (dargp-less-than-list-listp assumption-arg-lists dag-len)
                (consp assumption-arg-lists))
           (all-dargp (car assumption-arg-lists))))

(defthmd symbolp-when-member-equal
  (implies (and (member-equal x free)
                (symbol-listp free))
           (symbolp x)))

(defthmd not-equal-when-member-equal
  (implies (and (syntaxp (quotep y))
                (member-equal x vals)
                (syntaxp (quotep vals))
                (not (member-equal y vals)))
           (not (equal x y))))

(defthmd not-equal-when-member-equal-alt
  (implies (and (syntaxp (quotep y))
                (member-equal x vals)
                (syntaxp (quotep vals))
                (not (member-equal y vals)))
           (not (equal y x))))

;why is this needed?  the hyp is not being rewritten right during backchaining
(defthmd max-key-hack
  (equal (if (consp alist) x (< y (max-key alist z)))
         (if (consp alist) x (< y z))))

(defthmd max-key-hack-2
  (equal (if (consp alist) x (< (max-key alist z) y))
         (if (consp alist) x (< z y))))

;; since we may have rules about natp
(defthmd integerp-when-natp
  (implies (natp x)
           (integerp x)))

;; How we use the refined-assumption-alist:
;; 1. To bind free vars in a hyp (calling lookup-eq on the fn and unifying the hyp's args against each arglist).
;; 2. To check if a rewritten hyp is known to be non-nil (calling nodenum-equal-to-refined-assumptionp on its nodenum).
;; TODO: Only do this for non-predicates, since predicates should already be replaced by t if they are non-nil.
;; 3. To check whether a simplified IF test is known to be non-nil (calling nodenum-equal-to-refined-assumptionp on its nodenum).
;; TODO: Only do this for non-predicates, since predicates should already be replaced by t if they are non-nil.
;; TODO: For uses 2 and 3, it would be better to use a structure indexed by nodenum.

;; OLD:
;; How we use the equality-assumption-alist:
;; 1. To replace a term that is a var (calling replace-var-using-equality-assumption-alist).  This may be rare.
;;  TODO: Could this be handled using node-replacement-alist instead, letting us eliminate the :var case?
;; 2. To replace a (simplified) term that is a function call (calling replace-fun-call-using-equality-assumption-alist).

;; How we use the node-replacement-array:
;; OLD: To replace a tree that is a nodenum
;; 1. To replace a var (calling lookup-in-node-replacement-array on its nodenum after we add the node to the dag).
;; 2. To replace a simplified function call (calling lookup-in-node-replacement-array on its nodenum after we add the node to the dag).
;; Advantages: Lookup is very fast
;; Disadvantages: The thing being looked up must already be in the dag.
;; TODO: Make this an array indexed by nodenum?  But consider how quickly we can add and remove pairs when rewriting individual nodes...

;; TODO: Consider whether to look up unsimplified assumptions.
;; TODO: Consider whether to simplify the RHSes of assumptions (at start, or when used).

(defun make-rewriter-simple-fn (suffix ;; gets added to generated names
                                evaluator-base-name
                                eval-axe-syntaxp-expr-name
                                eval-axe-bind-free-function-application-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name)
                              (symbolp eval-axe-syntaxp-expr-name)
                              (symbolp eval-axe-bind-free-function-application-name))))
  (let* ((apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args))
         (my-sublis-var-and-eval-name (pack$ 'my-sublis-var-and-eval- suffix)) ; keep in sync with the name generated by make-substitution-code-simple
         ;; (instantiate-hyp-name (pack$ 'instantiate-hyp- suffix)) ; keep in sync with the name generated by make-substitution-code-simple
         (instantiate-hyp-free-vars-name (pack$ 'instantiate-hyp- suffix '-free-vars)) ; keep in sync with the name generated by make-substitution-code-simple-free-vars
         (instantiate-hyp-no-free-vars-name (pack$ 'instantiate-hyp- suffix '-no-free-vars)) ; keep in sync with the name generated by make-substitution-code-simple-no-free-vars
         ;; functions in the main mutual recursion:
        (relieve-free-var-hyp-and-all-others-name (pack$ 'relieve-free-var-hyp-and-all-others- suffix))
        (relieve-rule-hyps-name (pack$ 'relieve-rule-hyps- suffix))
        (try-to-apply-rules-name (pack$ 'try-to-apply-rules- suffix))
        (simplify-trees-and-add-to-dag-name (pack$ 'simplify-trees-and-add-to-dag- suffix))
        (simplify-if-tree-and-add-to-dag3-name (pack$ 'simplify-if-tree-and-add-to-dag3- suffix))
        (simplify-if-tree-and-add-to-dag2-name (pack$ 'simplify-if-tree-and-add-to-dag2- suffix))
        (simplify-if-tree-and-add-to-dag1-name (pack$ 'simplify-if-tree-and-add-to-dag1- suffix))
        (simplify-boolif-tree-and-add-to-dag2-name (pack$ 'simplify-boolif-tree-and-add-to-dag2- suffix))
        (simplify-boolif-tree-and-add-to-dag1-name (pack$ 'simplify-boolif-tree-and-add-to-dag1- suffix))
        (simplify-bvif-tree-and-add-to-dag3-name (pack$ 'simplify-bvif-tree-and-add-to-dag3- suffix))
        (simplify-bvif-tree-and-add-to-dag2-name (pack$ 'simplify-bvif-tree-and-add-to-dag2- suffix))
        (simplify-bvif-tree-and-add-to-dag1-name (pack$ 'simplify-bvif-tree-and-add-to-dag1- suffix))
        (simplify-tree-and-add-to-dag-name (pack$ 'simplify-tree-and-add-to-dag- suffix))
        (simplify-fun-call-and-add-to-dag-name (pack$ 'simplify-fun-call-and-add-to-dag- suffix))

        ;; Keep these in sync with the formals of each function:

        (call-of-relieve-free-var-hyp-and-all-others `(,relieve-free-var-hyp-and-all-others-name
                                                       assumption-arg-lists
                                                       hyp-args
                                                       hyp-num
                                                       other-hyps
                                                       alist
                                                       rule-symbol
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                       rewriter-rule-alist
                                                       refined-assumption-alist
                                                       node-replacement-array-num-valid-nodes
                                                       print interpreted-function-alist known-booleans monitored-symbols count))

        (call-of-relieve-rule-hyps `(,relieve-rule-hyps-name hyps hyp-num alist rule-symbol
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                             rewriter-rule-alist
                                                             refined-assumption-alist
                                                             node-replacement-array-num-valid-nodes
                                                             print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-try-to-apply-rules `(,try-to-apply-rules-name stored-rules
                                                               rewriter-rule-alist
                                                               args-to-match
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                               refined-assumption-alist
                                                               node-replacement-array-num-valid-nodes
                                                               print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-trees-and-add-to-dag `(,simplify-trees-and-add-to-dag-name
                                                 trees
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                 rewriter-rule-alist
                                                 refined-assumption-alist
                                                 node-replacement-array-num-valid-nodes
                                                 print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-if-tree-and-add-to-dag3 `(,simplify-if-tree-and-add-to-dag3-name fn
                                                                                           simplified-test
                                                                                           simplified-thenpart
                                                                                           elsepart
                                                                                           tree
                                                                                           trees-equal-to-tree
                                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                                           rewriter-rule-alist
                                                                                           refined-assumption-alist
                                                                                           node-replacement-array-num-valid-nodes
                                                                                           print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-if-tree-and-add-to-dag2 `(,simplify-if-tree-and-add-to-dag2-name fn
                                                                                           simplified-test
                                                                                           thenpart
                                                                                           elsepart
                                                                                           tree
                                                                                           trees-equal-to-tree
                                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                                           rewriter-rule-alist
                                                                                           refined-assumption-alist
                                                                                           node-replacement-array-num-valid-nodes
                                                                                           print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-if-tree-and-add-to-dag1 `(,simplify-if-tree-and-add-to-dag1-name
                                                    tree
                                                    trees-equal-to-tree
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                    rewriter-rule-alist
                                                    refined-assumption-alist
                                                    node-replacement-array-num-valid-nodes
                                                    print interpreted-function-alist known-booleans monitored-symbols count))

        (call-of-simplify-boolif-tree-and-add-to-dag2 `(,simplify-boolif-tree-and-add-to-dag2-name
                                                        simplified-test
                                                        args
                                                        tree
                                                        trees-equal-to-tree
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count))

        (call-of-simplify-boolif-tree-and-add-to-dag1 `(,simplify-boolif-tree-and-add-to-dag1-name
                                                        args
                                                        tree
                                                        trees-equal-to-tree
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count))

        (call-of-simplify-bvif-tree-and-add-to-dag2 `(,simplify-bvif-tree-and-add-to-dag2-name
                                                      simplified-test
                                                      args
                                                      tree
                                                      trees-equal-to-tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist
                                                      node-replacement-array-num-valid-nodes
                                                      print interpreted-function-alist known-booleans monitored-symbols count))

        (call-of-simplify-bvif-tree-and-add-to-dag1 `(,simplify-bvif-tree-and-add-to-dag1-name
                                                      args
                                                      tree
                                                      trees-equal-to-tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist
                                                      node-replacement-array-num-valid-nodes
                                                      print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-bvif-tree-and-add-to-dag3 `(,simplify-bvif-tree-and-add-to-dag3-name
                                                      size-result
                                                      simplified-test
                                                      simplified-thenpart
                                                      elsepart
                                                      tree
                                                      trees-equal-to-tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist
                                                      node-replacement-array-num-valid-nodes
                                                      print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-tree-and-add-to-dag `(,simplify-tree-and-add-to-dag-name
                                                tree
                                                trees-equal-to-tree
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                rewriter-rule-alist
                                                refined-assumption-alist
                                                node-replacement-array-num-valid-nodes
                                                print interpreted-function-alist known-booleans monitored-symbols count))
        (call-of-simplify-fun-call-and-add-to-dag `(,simplify-fun-call-and-add-to-dag-name
                                                    fn
                                                    args
                                                    trees-equal-to-tree
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                    rewriter-rule-alist
                                                    refined-assumption-alist
                                                    node-replacement-array-num-valid-nodes
                                                    print interpreted-function-alist known-booleans monitored-symbols count))

        ;; functions after the main mutual recursion:
        (simplify-term-name (pack$ 'simplify-term- suffix))
        (simp-term-name (pack$ 'simp-term- suffix))
        (simp-terms-name (pack$ 'simp-terms- suffix))
        )
    `(encapsulate ()

       (local (include-book "kestrel/lists-light/cdr" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/lists-light/nth" :dir :system))
       (local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

       (local (in-theory (disable wf-dagp wf-dagp-expander
                                  default-car
                                  default-cdr
                                  axe-treep
                                  axe-treep-when-pseudo-termp
                                  ;; member-of-cons
                                  ;; SUBSETP-CAR-MEMBER
                                  ;;SUBSETP-CONS-2
                                  ALL-AXE-TREEP PSEUDO-TERM-LISTP
                                  DEFAULT-+-1
                                  DEFAULT-+-2
                                  SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP
                                  symbol-listp
                                  symbol-alistp axe-rule-hyp-listp
                                  EQLABLE-ALISTP ;prevent inductions
                                  member-equal ; prevent case splitting
                                  )))

       (local (in-theory (enable ;;consp-of-assoc-equal-when-node-replacement-alistp
                          ;;dargp-of-cdr-of-assoc-equal-when-node-replacement-alistp
                          ;;dargp-less-than-of-cdr-of-assoc-equal-when-node-replacement-alistp
                          ;;myquotep-of-cdr-of-assoc-equal-when-node-replacement-alistp
                          ;;natp-of-cdr-of-assoc-equal-when-node-replacement-alistp
                          )))

       ;; Make a version of my-sublis-var-and-eval:
       (make-substitution-code-simple ,suffix ,evaluator-base-name)

       ;; Make versions of instantiate-hyp, etc.
       (make-instantiation-code-simple ,suffix ,evaluator-base-name)
       (make-instantiation-code-simple-free-vars ,suffix ,evaluator-base-name)
       (make-instantiation-code-simple-no-free-vars ,suffix ,evaluator-base-name)

       ;;
       ;; The main mutual recursion:
       ;;

       ;; TODO: Is the stuff in the dag assumed to be simplified, or not?  Some of those nodes may come from assumptions or even context.

       ;; TODO: It may be possible to avoid checking the count in some functions by using a more complicated measure.

       (mutual-recursion

        ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array), where extended-alist is irrelevant if hyps-relievedp is nil
        ;; keeps trying ASSUMPTION-ARG-LISTS until it finds a match for HYP-ARGS (thus binding some free vars) for which it can relieve all the OTHER-HYPS (using those variable bindings)
        (defund ,relieve-free-var-hyp-and-all-others-name (assumption-arg-lists ;these are lists of nodenums/quoteps for calls of fn that we can assume (where fn is the top function symbol of the hyp)
                                                           hyp-args ;partially instantiated; any vars that remain must match the assumption
                                                           hyp-num ; only used for printing, we could drop this for speed?
                                                           other-hyps
                                                           alist
                                                           rule-symbol
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                           rewriter-rule-alist
                                                           refined-assumption-alist ;we need to keep the whole alist in addition to walking down the entry for the current fn
                                                           node-replacement-array-num-valid-nodes
                                                           print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (type (integer 1 *) hyp-num) ;; restrict to a fixnum?
                   (type symbol rule-symbol)
                   (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (all-axe-treep hyp-args)
                                      (true-listp hyp-args)
                                      (symbol-listp monitored-symbols)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp known-booleans)
                                      (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                      (info-worldp info)
                                      (symbol-alistp alist)
                                      (all-dargp-less-than (strip-cdrs alist) dag-len)
                                      (axe-rule-hyp-listp other-hyps)
                                      (dargp-less-than-list-listp assumption-arg-lists dag-len)
                                      (rule-alistp rewriter-rule-alist)
                                      (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                      (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                      (maybe-bounded-memoizationp memoization dag-len)
                                      (triesp tries)
                                      (rule-limitsp limits))
                          :measure (nfix count)
                          :guard-debug t ;todo
                          :verify-guards nil ;see below
                          ))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (if (endp assumption-arg-lists)
                ;; failed to relieve the hyp:
                (prog2$ (and (member-eq rule-symbol monitored-symbols)
                             (cw "(Failed to relieve free vars in hyp ~x0 of rule ~x1.)~%" hyp-num rule-symbol))
                        (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
              (b* ((arg-list (first assumption-arg-lists)) ;; args of this assumption
                   (fail-or-extended-alist (unify-trees-with-dag-nodes hyp-args arg-list dag-array alist)))
                (if (eq :fail fail-or-extended-alist)
                    ;;this assumption didn't match:
                    (,relieve-free-var-hyp-and-all-others-name (rest assumption-arg-lists)
                                                               hyp-args hyp-num other-hyps
                                                               alist rule-symbol
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                               rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                               interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                  ;; the assumption matched, so try to relieve the rest of the hyps using the resulting extension of ALIST:
                  (mv-let (erp other-hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                    (,relieve-rule-hyps-name other-hyps (+ 1 hyp-num)
                                             fail-or-extended-alist ;ASSUMPTION bound some free vars
                                             rule-symbol
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                              rewriter-rule-alist
                                             refined-assumption-alist
                                             node-replacement-array-num-valid-nodes print
                                             interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                    (if erp
                        (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                      (if other-hyps-relievedp
                          (mv (erp-nil) t extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                        ;;this assumption matched, but we couldn't relieve the rest of the hyps:
                        (,relieve-free-var-hyp-and-all-others-name (rest assumption-arg-lists)
                                                                   hyp-args hyp-num other-hyps
                                                                   alist ;the original alist
                                                                   rule-symbol
                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                    rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                   interpreted-function-alist known-booleans monitored-symbols (+ -1 count))))))))))

        ;; ALIST is the substitution alist so far (it maps vars in the rule to nodenums and quoteps). If alist doesn't bind all the variables in the
        ;; HYP, we'll search for free variable matches in REFINED-ASSUMPTION-ALIST.
        ;; Relieving the hyp through rewriting may cause more nodes to be added to the DAG and more things to be added to memoization, info, and tries.
        ;; BOZO precompute the list of vars in the hyp?  or maybe just the ones that need to be bound in the alist?
        ;; Returns (mv erp hyps-relievedp alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array), where alist is irrelevant if hyps-relievedp is nil.
        ;; Otherwise, the alist returned may have been extended by the binding of free vars.
        (defund ,relieve-rule-hyps-name (hyps hyp-num alist rule-symbol
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                              rewriter-rule-alist
                                              refined-assumption-alist
                                              node-replacement-array-num-valid-nodes
                                              print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (type (integer 1 *) hyp-num) ;; restrict to a fixnum?
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (axe-rule-hyp-listp hyps)
                                (symbol-alistp alist)
                                (all-dargp-less-than (strip-cdrs alist) dag-len)
                                (symbolp rule-symbol)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (info-worldp info)
                                (triesp tries)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (symbol-listp monitored-symbols)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (if (endp hyps)
                ;; all hyps relieved:
                (mv (erp-nil) t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
              (b* ((hyp (first hyps))
                   (fn (ffn-symb hyp)) ;; all hyps are conses
                   (- (and (eq :verbose2 print)
                           (cw "Relieving hyp: ~x0 with alist ~x1.~%" hyp alist))))
                ;; todo: consider using CASE here:
                (if (eq :axe-syntaxp fn)
                    (let* ((syntaxp-expr (cdr hyp)) ;; strip off the AXE-SYNTAXP
                           (result (and (all-vars-in-term-bound-in-alistp syntaxp-expr alist) ; TODO: remove this check, since it should be guaranteed statically!  need a better guards in the alist wrt future hyps
                                        (,eval-axe-syntaxp-expr-name syntaxp-expr alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                                        )))
                      (if result
                          ;;this hyp counts as relieved
                          (,relieve-rule-hyps-name (rest hyps) (+ 1 hyp-num) alist rule-symbol
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                   rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                   interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                        (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                     ;;is it worth printing in this case?
                                     (progn$ (cw "(Failed to relieve axe-syntaxp hyp: ~x0 for ~x1.)~%" hyp rule-symbol)
                                             ;; (cw "(Alist: ~x0)~%" alist)
                                             ;; (cw "(DAG:~%")
                                             ;; (print-array2 'dag-array dag-array dag-len)
                                             ;; (cw ")~%")
                                             ))
                                (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))))
                  (if (eq :axe-bind-free fn)
                      ;; To evaluate the axe-bind-free hyp, we use alist, which binds vars to their nodenums or quoteps.
                      ;;The soundness of Axe should not depend on what an axe-bind-free function does; thus we cannot pass alist to such a function and trust it to faithfully extend it.  Nor can we trust it to extend the dag without changing any existing nodes. TODO: What if the axe-bind-free function gives back a result that is not even well-formed?
                      ;;TODO: It might be nice to be able to pass in the assumptions to the axe-bind-free-function? e.g., for finding usbp facts.
                      (let* ((bind-free-expr (cadr hyp)) ;; strip off the AXE-BIND-FREE
                             (result (and (all-vars-in-terms-bound-in-alistp (fargs bind-free-expr) alist) ; TODO: remove this check, since it should be guaranteed statically!  need a better guards in the alist wrt future hyps
                                          (,eval-axe-bind-free-function-application-name (ffn-symb bind-free-expr) (fargs bind-free-expr) alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                                          )))
                        (if result ;; nil to indicate failure, or an alist whose keys should be exactly (cddr hyp)
                            (let ((vars-to-bind (cddr hyp)))
                              (if (not (axe-bind-free-result-okayp result vars-to-bind dag-len))
                                  (mv (erp-t)
                                      (er hard? ',relieve-rule-hyps-name "Bind free hyp ~x0 for rule ~x1 returned ~x2, but this is not a well-formed alist that binds ~x3." hyp rule-symbol result vars-to-bind)
                                      alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                                ;; this hyp counts as relieved:
                                (,relieve-rule-hyps-name (rest hyps) (+ 1 hyp-num)
                                                         (append result alist) ;; guaranteed to be disjoint given the analysis done when the rule was made and the call of axe-bind-free-result-okayp above
                                                         rule-symbol
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                         rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                         interpreted-function-alist known-booleans monitored-symbols (+ -1 count))))
                          ;; failed to relieve the axe-bind-free hyp:
                          (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                       (cw "(Failed to relieve axe-bind-free hyp: ~x0 for ~x1.)~%" hyp rule-symbol))
                                  (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))))
                    (if (eq :free-vars fn) ;can't be a work-hard since there are free vars
                        (b* ((instantiated-hyp (,instantiate-hyp-free-vars-name (cdr hyp) ;strip the :free-vars
                                                                                alist interpreted-function-alist))
                             ((when (eq 'quote (ffn-symb instantiated-hyp))) ;todo: this should not happen since there are free vars (unless perhaps we give special treatment to IFs)
                              (er hard? ',relieve-rule-hyps-name "ERROR: Instantiating a hyp with free vars produced a constant.")
                              (mv :error-instantiating nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                          ;; Some free vars remain in the instantiated-hyp, so we search the REFINED-ASSUMPTIONS for matches to bind them:
                          ;; fffixme search node-replacement-array too? or make sure all the context info gets put into REFINED-ASSUMPTIONS?
                          ;; The refined-assumptions have been refined so that (equal (pred x) t) becomes (pred x) for better matching.
                          ;; TODO: Should we simplify the terms to which the free vars were bound (in case the assumptions are not simplified)?
                          (,relieve-free-var-hyp-and-all-others-name (lookup-eq (ffn-symb instantiated-hyp) refined-assumption-alist)
                                                                     (fargs instantiated-hyp)
                                                                     hyp-num
                                                                     (rest hyps)
                                                                     alist rule-symbol
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                     rewriter-rule-alist
                                                                     refined-assumption-alist
                                                                     node-replacement-array-num-valid-nodes print
                                                                     interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                      ;; HYP is not a call to axe-syntaxp or axe-bind-free or :free-vars:
                      ;; First, we substitute in for all the vars in HYP (this also evaluates what it can):
                      (b* ((instantiated-hyp (,instantiate-hyp-no-free-vars-name hyp alist interpreted-function-alist)))
                        ;; instantiated-hyp is now fully instantiated.  It is an axe-tree with leaves that are quoteps and nodenums (from vars already bound):
                        (if (fquotep instantiated-hyp) ;; we know the instantiated-hyp is a cons, because hyp is
                            ;; The instantiated-hyp is a quoted constant:
                            (if (unquote instantiated-hyp)
                                ;; The instantiated-hyp is a non-nil constant, so it counts as relieved:
                                (,relieve-rule-hyps-name (rest hyps)
                                                         (+ 1 hyp-num)
                                                         alist
                                                         rule-symbol
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                         rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                         interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                              ;; The instantiated-hyp is 'nil, so it failed to be relieved:
                              (progn$ (and (member-eq rule-symbol monitored-symbols)
                                           ;; We don't print much here, because a hyp that turns out to be nil (as opposed to some term for which we need a rewrite rule) is not very interesting.
                                           (cw "(Failed to relieve hyp ~x0 for ~x1.~% Reason: Instantiated to nil.~%" hyp rule-symbol))
                                      (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                          ;; There are no free vars, so we try to relieve the (fully-instantiated) hyp by simplifying it:
                          (b* ((old-try-count tries)
                               ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                                ;; TODO: This tests whether atoms in the instiantiated-hyp are vars, but that seems wasteful because the hyp is fully instantiated):
                                ;; bozo do we really want to add stupid natp hyps, etc. to the memoization? what about ground terms (most of them will have been evaluated above)?
                                ;; TODO: Consider not instantiating the hyp but rather simplifying it wrt an alist:
                                (,simplify-tree-and-add-to-dag-name instantiated-hyp
                                                                    nil ;nothing is yet known to be equal to instantiated-hyp
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                    rewriter-rule-alist
                                                                    refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                    interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                               ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                            (if (consp new-nodenum-or-quotep) ;tests for quotep
                                (if (unquote new-nodenum-or-quotep) ;the unquoted value is non-nil:
                                    (prog2$ (and old-try-count
                                                 print
                                                 (or (eq :verbose print) (eq :verbose2 print))
                                                 (< 100 (sub-tries tries old-try-count))
                                                 (cw " (~x1 tries used ~x0:~x2 (rewrote to true).)~%" rule-symbol (sub-tries tries old-try-count) hyp-num))
                                            ;;hyp rewrote to a non-nil constant and so counts as relieved:
                                            (,relieve-rule-hyps-name (rest hyps)
                                                                     (+ 1 hyp-num)
                                                                     alist
                                                                     rule-symbol
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                     rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                     interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                                  ;;hyp rewrote to 'nil
                                  (progn$ (and old-try-count
                                               print
                                               (or (eq :verbose print) (eq :verbose2 print))
                                               (< 100 (sub-tries tries old-try-count))
                                               (cw "(~x1 tries wasted ~x0:~x2 (rewrote to NIL))~%" rule-symbol (sub-tries tries old-try-count) hyp-num))
                                          (and (member-eq rule-symbol monitored-symbols)
                                               ;; We don't print much here, because a hyp that turns out to be nil (as opposed to some term for which we need a rewrite rule) is not very interesting.
                                               (cw "(Failed to relieve hyp ~x0 for ~x1.~% Reason: Rewrote to nil.~%" hyp rule-symbol))
                                          (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                              ;;hyp didn't rewrite to a constant (new-nodenum-or-quotep is a node number):
                              ;; Check whether the rewritten hyp is one of the known assumptions (todo: would be better to rewrite it using IFF).  TODO: Do the other versions of the rewriter/prover do something like this?
                              (if (nodenum-equal-to-refined-assumptionp new-nodenum-or-quotep refined-assumption-alist dag-array) ;todo: only do this if the hyp is not a known-boolean?
                                  (prog2$ (and old-try-count
                                               print
                                               (or (eq :verbose print) (eq :verbose2 print))
                                               (< 100 (sub-tries tries old-try-count))
                                               (cw " (~x1 tries used ~x0:~x2 (rewrote to true).)~%" rule-symbol (sub-tries tries old-try-count) hyp-num))
                                          ;;hyp rewrote to a known assumption and so counts as relieved:
                                          (,relieve-rule-hyps-name (rest hyps)
                                                                   (+ 1 hyp-num)
                                                                   alist
                                                                   rule-symbol
                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                   rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                   interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                                ;; Failed to relieve the hyp:
                                (progn$ (and old-try-count
                                             print
                                             (or (eq :verbose print) (eq :verbose2 print))
                                             (< 100 (sub-tries tries old-try-count))
                                             (cw "(~x1 tries wasted: ~x0:~x2 (non-constant result))~%" rule-symbol (sub-tries tries old-try-count) hyp-num))
                                        (and (member-eq rule-symbol monitored-symbols)
                                             (progn$ (cw "(Failed to relieve hyp ~x0 of rule ~x1.~%" hyp rule-symbol)
                                                     (cw "Reason: Rewrote to:~%")
                                                     (print-dag-node-nicely new-nodenum-or-quotep 'dag-array dag-array dag-len 200)
                                                     (cw "(Alist: ~x0)~%(Refined assumption alist: ~x1)~%" alist refined-assumption-alist )
                                                     ;;print these better?:
                                                     ;;(cw "(node-replacement-array: ~x0)~%" node-replacement-array)
                                                     (cw "(DAG:~%")
                                                     (print-array2 'dag-array dag-array dag-len)
                                                     (cw "))~%")))
                                        (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))))))))))))))

        ;; Returns (mv erp instantiated-rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        (defund ,try-to-apply-rules-name (stored-rules ;the list of rules for the fn in question
                                          rewriter-rule-alist
                                          args-to-match
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                          refined-assumption-alist
                                          node-replacement-array-num-valid-nodes
                                          print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (true-listp args-to-match)
                                      (all-dargp-less-than args-to-match dag-len)
                                      (true-listp stored-rules)
                                      (all-stored-axe-rulep stored-rules)
                                      (symbol-listp monitored-symbols)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp known-booleans)
                                      (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                      (info-worldp info)
                                      (rule-alistp rewriter-rule-alist)
                                      (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                      (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                      (maybe-bounded-memoizationp memoization dag-len)
                                      (triesp tries)
                                      (rule-limitsp limits))
                          :measure (nfix count)))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (if (endp stored-rules) ;no rule fired
                (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
              (b* ((stored-rule (first stored-rules))
                   ((when (and limits (limit-reachedp stored-rule limits print)))
                    ;; the limit for this rule is reached, so try the next rule:
                    (,try-to-apply-rules-name
                     (rest stored-rules) rewriter-rule-alist args-to-match
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                     refined-assumption-alist
                     node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                     (+ -1 count)))
                   (tries (and tries (increment-tries tries)))
                   ;; Try to match the args-to-match with the args of the LHS of the rule:
                   (alist-or-fail (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule) args-to-match dag-array dag-len)))
                (if (eq :fail alist-or-fail)
                    ;; the rule didn't match, so try the next rule:
                    (,try-to-apply-rules-name
                     (rest stored-rules) rewriter-rule-alist args-to-match
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                     refined-assumption-alist
                     node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                     (+ -1 count))
                  ;; The rule matched, so try to relieve its hyps:
                  (b* ((- (and (eq print ':verbose2)
                               (cw "(Trying to apply ~x0.~%" (stored-rule-symbol stored-rule))))
                       (hyps (stored-rule-hyps stored-rule))
                       ((mv erp hyps-relievedp alist ; may get extended by the binding of free vars
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                        (if hyps
                            (let ((rule-symbol (stored-rule-symbol stored-rule))) ;delay extracting this? not always needed?
                              (,relieve-rule-hyps-name hyps
                                                       1 ;initial hyp number
                                                       alist-or-fail
                                                       rule-symbol
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                          ;;if there are no hyps, don't even bother: BOZO inefficient?:
                          (mv (erp-nil) t alist-or-fail dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                    (if hyps-relievedp
                        ;; the hyps were relieved, so instantiate the RHS:
                        (prog2$ (and (eq print ':verbose2)
                                     (cw "Rewriting with ~x0.)~%" (stored-rule-symbol stored-rule)))
                                (mv (erp-nil)
                                    ;; could use a faster version where we know there are no free vars:
                                    (,my-sublis-var-and-eval-name alist (stored-rule-rhs stored-rule) interpreted-function-alist)
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    memoization
                                    ;;no need to assemble the info if we are not going to print it
                                    (and info (increment-hit-count-in-info-world (stored-rule-symbol stored-rule) info))
                                    tries
                                    (and limits (decrement-rule-limit stored-rule limits))
                                    node-replacement-array))
                      ;;failed to relieve the hyps, so try the next rule:
                      (prog2$ (and (eq print :verbose2)
                                   (cw "Failed to apply rule ~x0.)~%" (stored-rule-symbol stored-rule)))
                              (,try-to-apply-rules-name
                               (cdr stored-rules)
                               rewriter-rule-alist args-to-match
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                               refined-assumption-alist node-replacement-array-num-valid-nodes print
                               interpreted-function-alist known-booleans monitored-symbols
                               (+ -1 count))))))))))

        ;;simplify all the trees in trees and add to the DAG
        ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;;if the items in trees are already all nodenums or quoted constants this doesn't re-cons-up the list
        (defund ,simplify-trees-and-add-to-dag-name (trees
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                     rewriter-rule-alist
                                                     refined-assumption-alist
                                                     node-replacement-array-num-valid-nodes
                                                     print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (nfix count)
                          :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (true-listp trees)
                                      (all-axe-treep trees)
                                      (all-bounded-axe-treep trees dag-len)
                                      (symbol-listp monitored-symbols)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp known-booleans)
                                      (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                      (info-worldp info)
                                      (rule-alistp rewriter-rule-alist)
                                      (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                      (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                      (maybe-bounded-memoizationp memoization dag-len)
                                      (triesp tries)
                                      (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (if (atom trees)
                (mv (erp-nil) trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
              (b* ((first-tree (first trees))
                   (rest (rest trees))
                   ;; why do we handle the rest first?
                   ((mv erp rest-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                    (,simplify-trees-and-add-to-dag-name rest
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                         rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes
                                                          print interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                   ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                   ((mv erp first-tree-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                    (,simplify-tree-and-add-to-dag-name first-tree
                                                        nil ;; nothing is yet known equal to first-tree
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist refined-assumption-alist
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                   ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                (mv (erp-nil)
                    (cons-with-hint first-tree-result rest-result trees)
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))))

        ;; Helper function for rewriting a tree that is an IF or MYIF.  This is separate just to keep the main function small.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; Note that this function does not return node-replacement-array-num-valid-nodes since no nodes have been assumed that are relevant to the caller.
        ;; TODO: Are all elements in the array beyond node-replacement-array-num-valid-nodes nil?
        (defund ,simplify-if-tree-and-add-to-dag3-name (fn
                                                        simplified-test ; a nodenum
                                                        simplified-thenpart
                                                        elsepart
                                                        tree
                                                        trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist ; for free variable matching, mentions nodenums in dag-array
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (nfix count)
                          :guard (and (member-eq fn '(if myif))
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (natp simplified-test)
                                      (< simplified-test dag-len)
                                      (dargp-less-than simplified-thenpart dag-len)
                                      (axe-treep elsepart)
                                      (bounded-axe-treep elsepart dag-len)
                                      (consp tree)
                                      (axe-treep tree)
                                      (symbol-listp monitored-symbols)
                                      (trees-to-memoizep trees-equal-to-tree)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp known-booleans)
                                      (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                      (info-worldp info)
                                      (rule-alistp rewriter-rule-alist)
                                      (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                      (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                      (maybe-bounded-memoizationp memoization dag-len)
                                      (triesp tries)
                                      (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (;; Assume the test false:
                 ((mv node-replacement-array node-replacement-array-num-valid-nodes)
                  (if memoization ;can't use context it if we are memoizing:
                      (mv node-replacement-array node-replacement-array-num-valid-nodes)
                    (assume-nodenum-false-in-node-replacement-array simplified-test dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))
                 ((mv erp elsepart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name elsepart
                                                      nil ;no trees are yet known equal to the else branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                 ;; Clear test assumption. node-replacement-array should then be
                 ;; like it was before we set it (except perhaps longer), since
                 ;; if there was a replacement for this node, rewriting would
                 ;; have used it):
                 ((mv node-replacement-array node-replacement-array-num-valid-nodes)
                  (if memoization ;can't use context it if we are memoizing:
                      (mv node-replacement-array node-replacement-array-num-valid-nodes)
                    (unassume-nodenum-false-in-node-replacement-array simplified-test dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
              ;;this function takes simplified args and does not handle ifs specially (or else things might loop):
              (,simplify-fun-call-and-add-to-dag-name fn (list simplified-test simplified-thenpart elsepart-result)
                                                      (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))))

        ;; Helper function for rewriting a tree that is an IF or MYIF.  This is separate just to keep the main function small.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; Note that this function does not return node-replacement-array-num-valid-nodes since no nodes have been assumed that are relevant to the caller.
        (defund ,simplify-if-tree-and-add-to-dag2-name (fn
                                                        simplified-test ; a nodenum
                                                        thenpart
                                                        elsepart
                                                        tree
                                                        trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist ; for free variable matching, mentions nodenums in dag-array
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (nfix count)
                          :guard (and (member-eq fn '(if myif))
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (natp simplified-test)
                                      (< simplified-test dag-len)
                                      (axe-treep thenpart)
                                      (bounded-axe-treep thenpart dag-len)
                                      (axe-treep elsepart)
                                      (bounded-axe-treep elsepart dag-len)
                                      (consp tree)
                                      (axe-treep tree)
                                      (symbol-listp monitored-symbols)
                                      (trees-to-memoizep trees-equal-to-tree)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp known-booleans)
                                      (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                      (info-worldp info)
                                      (rule-alistp rewriter-rule-alist)
                                      (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                      (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                      (maybe-bounded-memoizationp memoization dag-len)
                                      (triesp tries)
                                      (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (;; Assume the test true
                 ((mv node-replacement-array node-replacement-array-num-valid-nodes)
                  (if memoization ;can't use context it if we are memoizing:
                      (mv node-replacement-array node-replacement-array-num-valid-nodes)
                    (assume-nodenum-true-in-node-replacement-array simplified-test dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))
                 ;; Rewrite the then-branch:
                 ((mv erp simplified-thenpart dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name thenpart
                                                      nil ;no trees are yet known equal to the then branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                 ;; Clear test assumption. node-replacement-array should then be
                 ;; like it was before we set it (except perhaps longer), since
                 ;; if there was a replacement for this node, rewriting would
                 ;; have used it):
                 ((mv node-replacement-array node-replacement-array-num-valid-nodes)
                  (if memoization ;can't use context it if we are memoizing:
                      (mv node-replacement-array node-replacement-array-num-valid-nodes)
                    (unassume-nodenum-true-in-node-replacement-array simplified-test dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
              (,simplify-if-tree-and-add-to-dag3-name fn
                                                      simplified-test ; a nodenum
                                                      simplified-thenpart ; a nodenum or quotep
                                                      elsepart
                                                      tree
                                                      trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist ; for free variable matching, mentions nodenums in dag-array
                                                      node-replacement-array-num-valid-nodes
                                                      print interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))))

        ;; Rewrite a tree that is an IF or MYIF.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; This is separate just to keep the main function small.
        (defund ,simplify-if-tree-and-add-to-dag1-name (tree
                                                        trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist ; for free variable matching, mentions nodenums in dag-array
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (axe-treep tree)
                                (bounded-axe-treep tree dag-len) ;todo: should imply axe-treep
                                (consp tree)
                                (member-eq (ffn-symb tree) '(if myif))
                                (= 3 (len (fargs tree)))
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)  ;todo: name these 3?
                                (natp node-replacement-array-num-valid-nodes)
                                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            ;; First, try to resolve the test (fixme would like to do this in an iff context):
            (b* ((args (fargs tree))
                 (test (first args))
                 ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (b* (((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                        (,simplify-tree-and-add-to-dag-name test
                                                            nil ;no trees are yet known equal to the test
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist node-replacement-array-num-valid-nodes
                                                            print interpreted-function-alist known-booleans monitored-symbols
                                                            (+ -1 count)))
                       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                    (if (consp simplified-test) ; tests for quotep
                        ;; test simplified to a constant:
                        (mv (erp-nil) simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                      ;; simplified-test is a nodenum.  Now try looking it up in the refined-assumption-alist:
                      ;; TODO: Do this also for the other kinds of IF below
                      (if (nodenum-equal-to-refined-assumptionp simplified-test refined-assumption-alist dag-array)  ;todo: only do this if the hyp is not a known-boolean?
                          ;; Since the test is known to be true from the refined-assumption-alist, it's as if it rewrote to 't (even though it may not be a predicate, IF/MYIF only looks at whether it is nil):
                          (mv (erp-nil) *t* dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                        ;; Failed to resolve the test:
                        (mv (erp-nil) simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
              (if (consp simplified-test)
                  ;; Rewrite either the then-branch or the else-branch, according to whether the test simplified to nil:
                  (,simplify-tree-and-add-to-dag-name (if (unquote simplified-test) (second args) (third args))
                                                      (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count))
                ;; Failed to resolve the test:
                (progn$
                 ;; If this gets printed too often for known predicates, we can preprocess such things:
                 (and (equal test (second args)) (cw "Unresolved IF test with test same as then-branch (from an OR?): ~x0.~%" test))
                 (,simplify-if-tree-and-add-to-dag2-name (ffn-symb tree) ; if or myif
                                                         simplified-test
                                                         (second args) ;"then" branch
                                                         (third args) ;"else" branch
                                                         tree
                                                         trees-equal-to-tree
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                         rewriter-rule-alist
                                                         refined-assumption-alist
                                                         node-replacement-array-num-valid-nodes
                                                         print
                                                         interpreted-function-alist known-booleans monitored-symbols
                                                         (+ -1 count)))))))

        ;; Continue rewriting a tree that is an BOOLIF.  This is separate just to keep the main function small.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        (defund ,simplify-boolif-tree-and-add-to-dag2-name (simplified-test
                                                            args ;the args of the call to boolif
                                                            tree
                                                            trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist
                                                            node-replacement-array-num-valid-nodes
                                                            print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (natp simplified-test)
                                (< simplified-test dag-len)
                                (all-axe-treep args)
                                (all-bounded-axe-treep args dag-len)
                                (= 3 (len args))
                                (consp tree)
                                (axe-treep tree)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (;; Simplify the "then" branch:
                 ((mv erp simplified-thenpart dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name (second args) ;"then" branch
                                                      nil ;no trees are yet known equal to the then branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                 ;; Simplify the "else" branch:
                 ((mv erp simplified-elsepart dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name (third args) ;"else" branch
                                                      nil ;no trees are yet known equal to the else branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
              ;; Try to apply rules to the call of boolif on simplified args:
              (,simplify-fun-call-and-add-to-dag-name 'boolif (list simplified-test simplified-thenpart simplified-elsepart)
                                                      (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))))

        ;; Rewrite a tree that is an BOOLIF.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; This is separate just to keep the main function small
        (defund ,simplify-boolif-tree-and-add-to-dag1-name (args ;the args of the call to boolif
                                                            tree
                                                            trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist
                                                            node-replacement-array-num-valid-nodes
                                                            print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (all-axe-treep args)
                                (all-bounded-axe-treep args dag-len)
                                (= 3 (len args))
                                (consp tree)
                                (axe-treep tree)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (;; First, try to resolve the if-test:
                 ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name (first args) ;the if-test
                                                      nil ;no trees are yet known equal to the test
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
              (if (consp simplified-test) ; tests for quotep
                  (if (unquote simplified-test)
                      ;;test rewrote to non-nil:
                      (,simplify-tree-and-add-to-dag-name `(bool-fix$inline ,(second args)) ;the "then" branch
                                                          (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          rewriter-rule-alist
                                                          refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                          (+ -1 count))
                    ;;test rewrote to nil:
                    (,simplify-tree-and-add-to-dag-name `(bool-fix$inline ,(third args)) ;the "else" branch
                                                        (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                        (+ -1 count)))
                (,simplify-boolif-tree-and-add-to-dag2-name simplified-test
                                                            args
                                                            tree trees-equal-to-tree
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist
                                                            node-replacement-array-num-valid-nodes
                                                            print
                                                            interpreted-function-alist known-booleans monitored-symbols
                                                            (+ -1 count))))))

        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; This is separate just to keep the proofs tractable (avoid too many sequential rewriter calls in one function).
        (defund ,simplify-bvif-tree-and-add-to-dag3-name (size-result
                                                          simplified-test
                                                          simplified-thenpart
                                                          elsepart
                                                          tree ;original bvif tree (bvif applied to the args, except the test is unsimplified)
                                                          trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          rewriter-rule-alist
                                                          refined-assumption-alist
                                                          node-replacement-array-num-valid-nodes
                                                          print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (dargp-less-than size-result dag-len)
                                (natp simplified-test)
                                (< simplified-test dag-len)
                                (dargp-less-than simplified-thenpart dag-len)
                                (axe-treep elsepart)
                                (bounded-axe-treep elsepart dag-len)
                                (consp tree)
                                (axe-treep tree)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (((mv erp elsepart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name elsepart ;"else" branch
                                                      nil ;no trees are yet known equal to the else branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
              (,simplify-fun-call-and-add-to-dag-name 'bvif (list size-result simplified-test simplified-thenpart elsepart-result)
                                                      (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))))

        ;; Rewrite a call of 'BVIF on ARGS.  This is for the case where we cannot rewrite the test
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; This is separate just to keep the proofs tractable (avoid too many sequential rewriter calls in one function).
        (defund ,simplify-bvif-tree-and-add-to-dag2-name (simplified-test
                                                          args
                                                          tree ;original bvif tree (bvif applied to the args, except the test is unsimplified)
                                                          trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          rewriter-rule-alist
                                                          refined-assumption-alist
                                                          node-replacement-array-num-valid-nodes
                                                          print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (natp simplified-test)
                                (< simplified-test dag-len)
                                (all-axe-treep args)
                                (all-bounded-axe-treep args dag-len)
                                (true-listp args)
                                (= 4 (len args))
                                (consp tree)
                                (axe-treep tree)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* (((mv erp size-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name (first args) ;size param
                                                      nil ;no trees are yet known equal to the the size param
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                 ((mv erp simplified-thenpart dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,simplify-tree-and-add-to-dag-name (third args) ;"then" branch
                                                      nil ;no trees are yet known equal to the then branch
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                      rewriter-rule-alist
                                                      refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                      (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
              (,simplify-bvif-tree-and-add-to-dag3-name size-result
                                                        simplified-test
                                                        simplified-thenpart
                                                        (fourth args) ;"else" branch
                                                        tree ;original bvif tree (bvif applied to the args, except the test is unsimplified)
                                                        trees-equal-to-tree
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist
                                                        node-replacement-array-num-valid-nodes
                                                        print
                                                        interpreted-function-alist known-booleans monitored-symbols
                                                        (+ -1 count)))))

        ;; Rewrite a call of 'BVIF on ARGS.
        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; This is separate just to keep the main function small
        (defund ,simplify-bvif-tree-and-add-to-dag1-name (args
                                                          tree ;bvif applied to the args
                                                          trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          rewriter-rule-alist
                                                          refined-assumption-alist
                                                          node-replacement-array-num-valid-nodes
                                                          print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (all-axe-treep args)
                                (all-bounded-axe-treep args dag-len)
                                (true-listp args)
                                (= 4 (len args))
                                (consp tree)
                                (axe-treep tree)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            ;; First, try to resolve the if-test:
            (mv-let (erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
              (,simplify-tree-and-add-to-dag-name (second args) ;the if-test
                                                  nil ;no trees are yet known equal to the test
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                  rewriter-rule-alist
                                                  refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
              (if erp
                  (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                (if (quotep simplified-test)
                    (if (unquote simplified-test)
                        ;;test rewrote to non-nil:
                        ;;todo: do better here?
                        (,simplify-tree-and-add-to-dag-name `(bvchop  ;$inline
                                                              ,(first args) ; size arg
                                                              ,(third args)) ; "then" branch
                                                            (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                            (+ -1 count))
                      ;;test rewrote to nil:
                      ;;todo: do better here?
                      (,simplify-tree-and-add-to-dag-name `(bvchop  ;$inline
                                                            ,(first args) ; size arg
                                                            ,(fourth args)) ; "else" branch
                                                          (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          rewriter-rule-alist
                                                          refined-assumption-alist node-replacement-array-num-valid-nodes print interpreted-function-alist known-booleans monitored-symbols
                                                          (+ -1 count)))
                  ;;couldn't resolve the if-test:
                  (,simplify-bvif-tree-and-add-to-dag2-name simplified-test
                                                            args
                                                            tree trees-equal-to-tree
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist
                                                            node-replacement-array-num-valid-nodes
                                                            print
                                                            interpreted-function-alist known-booleans monitored-symbols
                                                            (+ -1 count)))))))

        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; Rewrite TREE repeatedly using REWRITER-RULE-ALIST and REFINED-ASSUMPTION-ALIST and add the result to the DAG-ARRAY, returning a nodenum or a quotep.
        ;; TREE is a term with nodenums and quoteps and variables at the leaves.
        ;; TREES-EQUAL-TO-TREE is a list of terms (not vars) equal to TREE (at the bottom is the original term we are rewriting)- when we get the final result, all these terms will be equal to it - BOZO option to turn this off?

        ;;  BOZO can we just keep rewrite-stack empty if we're not doing it for real?

        ;; BOZO I forget, why would we ever not memoize??  i guess when we know there are no repeated subterms in the tree? could precompute that info for the RHS of each rule...  ;also, memoization may be unsound if we use internal ITE contexts to rewrite - unless we track that info in the memoization
        ;; could still memoize when rewriting a given node..
        ;; be sure we always handle lambdas early, in case one is hiding an if - bozo - skip this for now?

        ;; MEMOIZATION maps functions call exprs (nothing else??) over nodenums and constants (not vars) to the nodenums or quoteps to which they simplify - no, let memoization map any tree!
        ;; memoization can be thought of as part of the DAG (all nodenums mentioned in memoization must be part of the DAG)

        ;; i guess depth2 isn't just the depth of the rewrite stack, since we only use the rewrite-stack if we are adding nodes for real
        ;; but we may always want depth2 to prevent super deep rewrites during backchaining?  maybe we do want the rewrite stack during backchaining too?
        ;; old: depth2 is the depth of rewrite-stack? we could alternate depths and values on that stack?

        ;;leaves nodes below dag-len untouched..
        ;;BOZO could put in simple loop checking (if the first element of trees-equal-to-tree is tree itself) - or check the first few elements..
        ;;but then we'd be using trees-equal-to-tree in a non-memoizing context
;had to make this a flag function for tail calls to be removed
;fixme the dispatch here requires that there not be a function named nil; enforce that in interpreted-function-alists?
        (defund ,simplify-tree-and-add-to-dag-name (tree
                                                    trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                    rewriter-rule-alist
                                                    refined-assumption-alist
                                                    node-replacement-array-num-valid-nodes
                                                    print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (axe-treep tree)
                                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (bounded-axe-treep tree dag-len)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (if (atom tree)
                (if (symbolp tree)
                    ;; It's a variable (this case may be very rare; can we eliminate it by pre-handling vars in the initial term?):
                    (b* ( ;; Add it to the DAG:
                         ((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          (add-variable-to-dag-array tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                         ;; See if the resulting node is known to be equal to something:
                         (replacement-match (lookup-in-node-replacement-array nodenum node-replacement-array node-replacement-array-num-valid-nodes))
                         (new-nodenum-or-quotep (if replacement-match
                                                    ;; the node was replaced with something equal to it, using an assumption:
                                                    replacement-match
                                                  ;; not replaced:
                                                  nodenum)))
                      (mv (erp-nil)
                          new-nodenum-or-quotep
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          (and memoization
                               (add-pairs-to-memoization trees-equal-to-tree ;the items ; TODO: Should we include TREE itself?
                                                         new-nodenum-or-quotep ;the nodenum-or-quotep they are all equal to
                                                         memoization))
                          info tries limits node-replacement-array))
                  ;; TREE is a nodenum (because it's an atom but not a symbol): fixme use equalities?
;ffffixme, this assumes that nodes in the dag are already rewritten.  but what if this nodenum came from a node-equality assumption? in that case, it may not be rewritten! should we simplify the cdrs of node-replacement-array-num-valid-nodes once at the beginning?  also think about  (they are terms so the cdr gets simplified each time an equality fires, but maybe they get simplified over and over).
                  ;; First, see if the nodenum is mapped to anything in the node-replacement-array-num-valid-nodes:
                  (let* ((replacement-match nil ;(assoc-in-node-replacement-array-num-valid-nodes tree node-replacement-array-num-valid-nodes)
                                            )
                         (tree (if (and replacement-match
                                        ;; This is new (8/10/15), so to be safe we only do it if the result is a constant (I am worried about loops):
                                        (quotep (cdr replacement-match)))
                                   (cdr replacement-match)
                                 ;; No match found in the node-replacement-alist, so just use tree:
                                 tree)))
                    (mv (erp-nil)
                        tree
                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                        (if (and memoization
                                 trees-equal-to-tree)
                            (add-pairs-to-memoization trees-equal-to-tree ;the items (don't include expr itself, since its a nodenum)
                                                      tree ;the nodenum/quotep they are all equal to
                                                      memoization)
                          memoization)
                        info tries limits node-replacement-array)))
              ;; TREE is a cons:
              (let ((fn (ffn-symb tree)))
                (if (eq 'quote fn)
                    ;; TREE is a quoted constant:
                    (mv (erp-nil)
                        tree ;;return the quoted constant
                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                        (if (and memoization
                                 trees-equal-to-tree)
                            (add-pairs-to-memoization trees-equal-to-tree ;the items (don't include expr itself, since its a quoted constant)
                                                      tree ;the constant they are all equal to
                                                      memoization)
                          memoization)
                        info tries limits node-replacement-array)
                  ;; TREE is a function call:
                  ;;Try looking it up in memoization (note that the args are not yet simplified):
                  (let ((memo-match (and memoization (lookup-in-memoization tree memoization))))
                    (if memo-match
                        (mv (erp-nil)
                            memo-match
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                            (add-pairs-to-memoization trees-equal-to-tree
                                                      memo-match ;the nodenum or quotep they are all equal to
                                                      memoization)
                            info tries limits node-replacement-array)
                      ;; Handle the various kinds of if:
                      (if (and (member-eq fn '(if myif))
                               ;; optimize?:
                               (= 3 (len (fargs tree))))
                          (,simplify-if-tree-and-add-to-dag1-name tree trees-equal-to-tree
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                  rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes
                                                                   print interpreted-function-alist known-booleans monitored-symbols
                                                                  (+ -1 count) ;could perhaps be avoided with a more complex measure
                                                                  )
                        (if (and (eq 'boolif fn)
                                 ;; optimize?:
                                 (= 3 (len (fargs tree))))
                            (,simplify-boolif-tree-and-add-to-dag1-name (fargs tree)
                                                                        tree trees-equal-to-tree
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                        rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes
                                                                         print interpreted-function-alist known-booleans monitored-symbols
                                                                        (+ -1 count) ;could perhaps be avoided with a more complex measure
                                                                        )
                          (if (and (eq 'bvif fn)
                                   ;; optimize?:
                                   (= 4 (len (fargs tree))))
                              (,simplify-bvif-tree-and-add-to-dag1-name (fargs tree)
                                                                        tree trees-equal-to-tree
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                        rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes
                                                                         print interpreted-function-alist known-booleans monitored-symbols
                                                                        (+ -1 count) ;could perhaps be avoided with a more complex measure
                                                                        )
                            ;;It wasn't any kind of IF:
                            (b* ((args (fargs tree))
                                 ;; We are simplifying a call of FN on ARGS, where the ARGS are axe-trees.
                                 ;; First we simplify the args:
                                 ;;ffixme should we simplify the args earlier? e.g., before looking the term up in the memoization?
                                 ;; FN might be a lambda.
                                 ;; fixme might it be possible to not check for ground-terms because we never build them -- think about where terms might come from other than my-sublis-var, which we could change to not build ground terms (of functions we know about)
                                 ;; ffixme maybe we should try to apply rules here (maybe outside-in rules) instead of rewriting the args
                                 ;; fixme could pass in a flag for the common case where the args are known to be already simplified (b/c the tree is a dag node?)
                                 (- (and (eq :verbose2 print) (cw "(Rewriting args of ~x0:~%" fn)))
                                 ((mv erp args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                                  (,simplify-trees-and-add-to-dag-name args
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                       rewriter-rule-alist refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                       interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                                 (- (and (eq :verbose2 print) (cw "Done rewriting args.)~%")))
                                 ;;ARGS is now a list of nodenums and quoteps.
                                 ;;Now we simplify FN applied to (the simplified) ARGS:
                                 )
                              (if (consp fn) ;;tests for lambda
                                  ;; It's a lambda, so we beta-reduce and simplify the result:
                                  ;; note that we don't look up lambdas in the assumptions (this is consistent with simplifying first)
                                  (let* ((formals (second fn))
                                         (body (third fn))
                                         ;;BOZO could optimize this pattern: (my-sublis-... (pairlis$-fast formals args) body)
                                         (new-expr (,my-sublis-var-and-eval-name (pairlis$-fast formals args) body interpreted-function-alist)))
                                    ;;simplify the result of beta-reducing:
                                    (,simplify-tree-and-add-to-dag-name new-expr
                                                                        (cons tree trees-equal-to-tree) ;we memoize the lambda
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                        rewriter-rule-alist
                                                                        refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                                        interpreted-function-alist known-booleans monitored-symbols (+ -1 count)))
                                ;; not a lambda:
                                (b* ( ;; handle possible ground term by evaluating:
                                     ;; TODO: Think about how it is possible to even have a ground term here
                                     ((mv erp evaluatedp val)
                                      (if (not (all-consp args)) ;; test for args being quoted constants
                                          ;; not a ground term:
                                          (mv (erp-nil) nil nil)
                                        ;; ground term, so try to evaluate:
                                        (b* (((mv erp val)
                                              (,apply-axe-evaluator-to-quoted-args-name fn args interpreted-function-alist)))
                                          (if erp
                                              (if (eq :unknown-function erp)
                                                  (mv (erp-nil) nil nil) ;no error, but it didn't produce a value (todo: print a warning?)
                                                ;; anything else non-nil is a true error:
                                                (mv erp nil nil))
                                            ;; normal case:
                                            (mv (erp-nil) t val)))))
                                     ;; I suppose we could suppress any evaluator error here if we choose to (might be a bit faster)?
                                     ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)))
                                  (if evaluatedp
                                      (let ((quoted-val (enquote val)))
                                        (mv (erp-nil)
                                            quoted-val
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            (and memoization
                                                 ;;we memoize the ground term (should we? could use a separate memoization for ground terms)
                                                 (add-pairs-to-memoization (cons ;we could avoid this cons
                                                                            tree ;; the original tree, with unsimplified args (might be ground)
                                                                            ;; should we include here fn applied to args (the simplified args)?
                                                                            trees-equal-to-tree)
                                                                           quoted-val ;the quoted constant they are all equal to
                                                                           memoization))
                                            info tries limits node-replacement-array))
                                    ;; Otherwise, simplify the non-lambda FN applied to the simplified args:
                                    ;; TODO: Perhaps pass in the original expr for use by cons-with-hint:
                                    (,simplify-fun-call-and-add-to-dag-name fn args
                                                                            (cons tree trees-equal-to-tree) ;the thing we are rewriting is equal to tree
                                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                            rewriter-rule-alist
                                                                            refined-assumption-alist node-replacement-array-num-valid-nodes
                                                                            print
                                                                            interpreted-function-alist known-booleans monitored-symbols
                                                                            (+ -1 count))))))))))))))))

        ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array).
        ;; No special handling if FN is an if (of any type).
        (defund ,simplify-fun-call-and-add-to-dag-name (fn ;;a function symbol
                                                        args ;these are simplified (so these are nodenums or quoteps)
                                                        trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization) ;todo: rename
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                        rewriter-rule-alist
                                                        refined-assumption-alist
                                                        node-replacement-array-num-valid-nodes
                                                        print interpreted-function-alist known-booleans monitored-symbols count)
          (declare (type (unsigned-byte 60) count)
                   (xargs
                    :measure (nfix count)
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (symbolp fn)
                                (not (equal 'quote fn))
                                (true-listp args)
                                (all-dargp-less-than args dag-len)
                                (symbol-listp monitored-symbols)
                                (trees-to-memoizep trees-equal-to-tree)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp known-booleans)
                                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                                (info-worldp info)
                                (rule-alistp rewriter-rule-alist)
                                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                                (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                                (maybe-bounded-memoizationp memoization dag-len)
                                (triesp tries)
                                (rule-limitsp limits))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
            (b* ((expr (cons fn args)) ;todo: use below
                 ;;Try looking it up in the memoization (note that the args are now simplified):
                 (memo-match (and memoization (lookup-in-memoization expr memoization))))
              (if memo-match
                  (mv (erp-nil)
                      memo-match
                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      (add-pairs-to-memoization trees-equal-to-tree
                                                memo-match ;the nodenum or quotep they are all equal to
                                                memoization)
                      info tries limits node-replacement-array)
                ;; Next, try to apply rules:
                (mv-let
                  (erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                  (,try-to-apply-rules-name (get-rules-for-fn fn rewriter-rule-alist)
                                            rewriter-rule-alist args
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                            refined-assumption-alist node-replacement-array-num-valid-nodes print
                                            interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                  (if erp
                      (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
                    (if rhs-or-nil
                        ;;A rule fired, so simplify the instantiated right-hand-side:
                        ;; This is a tail call, which allows long chains of rewrites:
                        (,simplify-tree-and-add-to-dag-name rhs-or-nil
                                                            ;;in the common case in which simplifying the args had no effect, the car of trees-equal-to-tree will be the same as (cons fn args), so don't add it twice
                                                            (cons-if-not-equal-car expr ;could save this and similar conses in the function
                                                                                   trees-equal-to-tree)
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            rewriter-rule-alist
                                                            refined-assumption-alist node-replacement-array-num-valid-nodes print
                                                            interpreted-function-alist known-booleans monitored-symbols (+ -1 count))
                      ;; No rule fired, so no simplification can be done.  Add the node to the dag:
                      (b* (((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                            (add-function-call-expr-to-dag-array
                             fn args ;(if any-arg-was-simplifiedp (cons fn args) tree) ;could put back the any-arg-was-simplifiedp trick to save this cons
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                             ;;1000 ; the print-interval ;todo: consider putting back some printing like that done by add-function-call-expr-to-dag-array-with-memo
                             ;;print
                             ))
                           ((when erp) (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
                           ;; See if the nodenum returned is equated to anything:
                           (replacement-match (lookup-in-node-replacement-array nodenum node-replacement-array node-replacement-array-num-valid-nodes))
                           (new-nodenum-or-quotep (if replacement-match
                                                      ;; the node was replaced with something equal to it, using an assumption:
                                                      replacement-match ; not rewritten.  We could rewrite all such items (that replacements can introduce) outside the main clique
                                                    ;; not replaced:
                                                    nodenum)))
                        (mv (erp-nil)
                            new-nodenum-or-quotep
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                            (and memoization
                                 (add-pairs-to-memoization (cons-if-not-equal-car expr trees-equal-to-tree) ; might be the same as tree if the args aren't simplified?) well, each arg should be simplified and memoed.
                                                           new-nodenum-or-quotep ;the nodenum-or-quotep they are all equal to
                                                           memoization))
                            info tries limits node-replacement-array)))))))))
        ) ;end mutual-recursion

       ;; Theorems about when the count reaches 0:
       (progn
         (defthm ,(pack$ 'relieve-free-var-hyp-and-all-others- suffix '-of-0)
           (equal ,(subst 0 'count call-of-relieve-free-var-hyp-and-all-others)
                  (mv :count-exceeded nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-relieve-free-var-hyp-and-all-others)))))

         (defthm ,(pack$ 'relieve-rule-hyps- suffix '-of-0)
           (equal ,(subst 0 'count call-of-relieve-rule-hyps)
                  (mv :count-exceeded t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-relieve-rule-hyps)))))

         (defthm ,(pack$ 'try-to-apply-rules- suffix '-of-0)
           (equal ,(subst 0 'count call-of-try-to-apply-rules)
                  (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-try-to-apply-rules)))))

         (defthm ,(pack$ 'simplify-trees-and-add-to-dag- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-trees-and-add-to-dag)
                  (mv :count-exceeded trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-trees-and-add-to-dag)))))

         (defthm ,(pack$ 'simplify-fun-call-and-add-to-dag- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-fun-call-and-add-to-dag)
                  (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-fun-call-and-add-to-dag)))))

         (defthm ,(pack$ 'simplify-tree-and-add-to-dag- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-tree-and-add-to-dag)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-tree-and-add-to-dag)))))

         (defthm ,(pack$ 'simplify-if-tree-and-add-to-dag1- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-if-tree-and-add-to-dag1)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-if-tree-and-add-to-dag1)))))

         (defthm ,(pack$ 'simplify-if-tree-and-add-to-dag2- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-if-tree-and-add-to-dag2)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-if-tree-and-add-to-dag2)))))

         (defthm ,(pack$ 'simplify-if-tree-and-add-to-dag3- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-if-tree-and-add-to-dag3)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-if-tree-and-add-to-dag3)))))

         (defthm ,(pack$ 'simplify-boolif-tree-and-add-to-dag1- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-boolif-tree-and-add-to-dag1)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-boolif-tree-and-add-to-dag1)))))

         (defthm ,(pack$ 'simplify-boolif-tree-and-add-to-dag2- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-boolif-tree-and-add-to-dag2)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-boolif-tree-and-add-to-dag2)))))

         (defthm ,(pack$ 'simplify-bvif-tree-and-add-to-dag1- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-bvif-tree-and-add-to-dag1)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-bvif-tree-and-add-to-dag1)))))

         (defthm ,(pack$ 'simplify-bvif-tree-and-add-to-dag2- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-bvif-tree-and-add-to-dag2)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-bvif-tree-and-add-to-dag2)))))

         (defthm ,(pack$ 'simplify-bvif-tree-and-add-to-dag3- suffix '-of-0)
           (equal ,(subst 0 'count call-of-simplify-bvif-tree-and-add-to-dag3)
                  (mv :count-exceeded dag-len dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array))
           :hints (("Goal" :expand ((:free (count) ,call-of-simplify-bvif-tree-and-add-to-dag3)))))
         ) ;end progn

       ;; This may speed things up a bit:
       ;; (defun quick-and-dirty-srs-off (cl1 ac)
       ;;   (declare (ignore cl1 ac)
       ;;            (xargs :mode :logic :guard t))
       ;;   nil)
       ;; (defattach-system quick-and-dirty-srs quick-and-dirty-srs-off)

       (make-flag ,simplify-tree-and-add-to-dag-name)

       (defthm ,(pack$ 'len-of-mv-nth-1-of-simplify-trees-and-add-to-dag- suffix)
         (equal (len (mv-nth 1 ,call-of-simplify-trees-and-add-to-dag))
                (len trees))
         :hints (("Goal" :expand ((:free (count) ,call-of-simplify-trees-and-add-to-dag))
                  :induct (simplify-trees-and-add-to-dag-induct trees count)
                  :in-theory (e/d ((:i len)) ( ;LEN-OF-CDR
                                              )))))

       ;; Everything returns an info-world:
       (,(pack$ 'defthm-flag-simplify-tree-and-add-to-dag- suffix)
         (defthm ,(pack$ 'info-worldp-of-mv-nth-9-of-relieve-free-var-hyp-and-all-others- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 9 ,call-of-relieve-free-var-hyp-and-all-others)))

           :flag ,relieve-free-var-hyp-and-all-others-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-9-of-relieve-rule-hyps- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 9 ,call-of-relieve-rule-hyps)))
           :flag ,relieve-rule-hyps-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-try-to-apply-rules- suffix)
           (implies (and (all-stored-axe-rulep stored-rules)
                         (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-try-to-apply-rules)))
           :flag ,try-to-apply-rules-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-trees-and-add-to-dag- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-trees-and-add-to-dag)))
           :flag ,simplify-trees-and-add-to-dag-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-if-tree-and-add-to-dag3- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-if-tree-and-add-to-dag3)))
           :flag ,simplify-if-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-if-tree-and-add-to-dag2- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-if-tree-and-add-to-dag2)))
           :flag ,simplify-if-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-if-tree-and-add-to-dag1- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-if-tree-and-add-to-dag1)))
           :flag ,simplify-if-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-boolif-tree-and-add-to-dag2- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
           :flag ,simplify-boolif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-boolif-tree-and-add-to-dag1- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
           :flag ,simplify-boolif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-bvif-tree-and-add-to-dag3- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
           :flag ,simplify-bvif-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-bvif-tree-and-add-to-dag2- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
           :flag ,simplify-bvif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-bvif-tree-and-add-to-dag1- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
           :flag ,simplify-bvif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-tree-and-add-to-dag- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-tree-and-add-to-dag)))
           :flag ,simplify-tree-and-add-to-dag-name)

         (defthm ,(pack$ 'info-worldp-of-mv-nth-8-of-simplify-fun-call-and-add-to-dag- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (info-worldp info))
                    (info-worldp (mv-nth 8 ,call-of-simplify-fun-call-and-add-to-dag))
                    )
           :flag ,simplify-fun-call-and-add-to-dag-name)

         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (;TAKE-WHEN-<=-OF-LEN
                                   len-of-cadar-when-axe-treep
                                   pseudo-termp-of-cadddr-when-axe-treep
                                   axe-bind-free-result-okayp-rewrite
                                   symbol-alistp-when-alistp
                                   true-listp-of-cdr)
                                  (dargp-less-than
                                   natp
                                   quotep
                                   myquotep))
                  :expand ((:free (memoization count other-hyps alist)
                                  ,call-of-relieve-free-var-hyp-and-all-others)
                           (:free (memoization count)
                                  ,call-of-relieve-rule-hyps)
                           (:free (memoization)
                                  (,RELIEVE-RULE-HYPS-NAME nil HYP-NUM ALIST RULE-SYMBOL
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            REWRITER-RULE-ALIST
                                                            REFINED-ASSUMPTION-ALIST
                                                            NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                           PRINT
                                                           INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  (,SIMPLIFY-TREES-AND-ADD-TO-DAG-NAME NIL
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                       REWRITER-RULE-ALIST
                                                                       REFINED-ASSUMPTION-ALIST
                                                                       NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                                        PRINT
                                                                       INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  ,call-of-simplify-trees-and-add-to-dag)
                           (:free (memoization limits info tries count)
                                  ,call-of-try-to-apply-rules)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag1)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag2)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag3)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag2)
                           (:free (MEMOIZATION count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-tree-and-add-to-dag)
                           (:free (MEMOIZATION count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-fun-call-and-add-to-dag)
                           (:free (MEMOIZATION count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag2)
                           (:free (MEMOIZATION count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag3)
                           (axe-rule-hyp-listp hyps)))))

       ;; The rule-limits returned are ok:
       (,(pack$ 'defthm-flag-simplify-tree-and-add-to-dag- suffix)
         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-11-of-relieve-free-var-hyp-and-all-others- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 11 ,call-of-relieve-free-var-hyp-and-all-others)))
           :flag ,relieve-free-var-hyp-and-all-others-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-11-of-relieve-rule-hyps- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 11 ,call-of-relieve-rule-hyps)))
           :flag ,relieve-rule-hyps-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-try-to-apply-rules- suffix)
           (implies (and
                     (all-stored-axe-rulep stored-rules)
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-try-to-apply-rules)))
           :flag ,try-to-apply-rules-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-trees-and-add-to-dag- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-trees-and-add-to-dag)))
           :flag ,simplify-trees-and-add-to-dag-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-if-tree-and-add-to-dag3- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-if-tree-and-add-to-dag3)))
           :flag ,simplify-if-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-if-tree-and-add-to-dag2- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-if-tree-and-add-to-dag2)))
           :flag ,simplify-if-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-if-tree-and-add-to-dag1- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-if-tree-and-add-to-dag1)))
           :flag ,simplify-if-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-boolif-tree-and-add-to-dag2- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
           :flag ,simplify-boolif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-boolif-tree-and-add-to-dag1- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
           :flag ,simplify-boolif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-bvif-tree-and-add-to-dag3- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
           :flag ,simplify-bvif-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-bvif-tree-and-add-to-dag2- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
           :flag ,simplify-bvif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-bvif-tree-and-add-to-dag1- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
           :flag ,simplify-bvif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-tree-and-add-to-dag- suffix)
           (implies (and
                     (rule-alistp rewriter-rule-alist)
                     (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-tree-and-add-to-dag)))
           :flag ,simplify-tree-and-add-to-dag-name)

         (defthm ,(pack$ 'rule-limitsp-of-mv-nth-10-of-simplify-fun-call-and-add-to-dag- suffix)
           (implies (and (rule-alistp rewriter-rule-alist)
                         (rule-limitsp limits))
                    (rule-limitsp (mv-nth 10 ,call-of-simplify-fun-call-and-add-to-dag)))
           :flag ,simplify-fun-call-and-add-to-dag-name)

         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (;TAKE-WHEN-<=-OF-LEN
                                   len-of-cadar-when-axe-treep
                                   pseudo-termp-of-cadddr-when-axe-treep
                                   axe-bind-free-result-okayp-rewrite
                                   symbol-alistp-when-alistp
                                   true-listp-of-cdr)
                                  (dargp-less-than
                                   natp
                                   quotep
                                   myquotep
                                   ))
                  :expand ((:free (memoization count other-hyps alist)
                                  ,call-of-relieve-free-var-hyp-and-all-others)
                           (:free (memoization count)
                                  ,call-of-relieve-rule-hyps)
                           (:free (memoization)
                                  (,RELIEVE-RULE-HYPS-NAME nil HYP-NUM ALIST RULE-SYMBOL
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            REWRITER-RULE-ALIST
                                                           REFINED-ASSUMPTION-ALIST

                                                           NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                           PRINT
                                                           INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  (,SIMPLIFY-TREES-AND-ADD-TO-DAG-NAME NIL
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                       REWRITER-RULE-ALIST
                                                                       REFINED-ASSUMPTION-ALIST

                                                                       NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                                        PRINT
                                                                       INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  ,call-of-simplify-trees-and-add-to-dag)
                           (:free (memoization limits info tries count)
                                  ,call-of-try-to-apply-rules)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag1)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag2)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag3)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag2)
                           (:free (memoization count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-tree-and-add-to-dag)
                           (:free (memoization count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-fun-call-and-add-to-dag)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag2)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag3)
                           (axe-rule-hyp-listp hyps)))))

       ;; The tries returned are ok:
       (,(pack$ 'defthm-flag-simplify-tree-and-add-to-dag- suffix)
         (defthm ,(pack$ 'triesp-of-mv-nth-10-of-relieve-free-var-hyp-and-all-others- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 10 ,call-of-relieve-free-var-hyp-and-all-others)))
           :flag ,relieve-free-var-hyp-and-all-others-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-10-of-relieve-rule-hyps- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 10 ,call-of-relieve-rule-hyps)))
           :flag ,relieve-rule-hyps-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-try-to-apply-rules- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-try-to-apply-rules)))
           :flag ,try-to-apply-rules-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-trees-and-add-to-dag- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-trees-and-add-to-dag)))
           :flag ,simplify-trees-and-add-to-dag-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-if-tree-and-add-to-dag3- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-if-tree-and-add-to-dag3)))
           :flag ,simplify-if-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-if-tree-and-add-to-dag2- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-if-tree-and-add-to-dag2)))
           :flag ,simplify-if-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-if-tree-and-add-to-dag1- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-if-tree-and-add-to-dag1)))
           :flag ,simplify-if-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-boolif-tree-and-add-to-dag2- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
           :flag ,simplify-boolif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-boolif-tree-and-add-to-dag1- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
           :flag ,simplify-boolif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-bvif-tree-and-add-to-dag3- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
           :flag ,simplify-bvif-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-bvif-tree-and-add-to-dag2- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
           :flag ,simplify-bvif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-bvif-tree-and-add-to-dag1- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
           :flag ,simplify-bvif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-tree-and-add-to-dag- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-tree-and-add-to-dag)))
           :flag ,simplify-tree-and-add-to-dag-name)

         (defthm ,(pack$ 'triesp-of-mv-nth-9-of-simplify-fun-call-and-add-to-dag- suffix)
           (implies (triesp tries)
                    (triesp (mv-nth 9 ,call-of-simplify-fun-call-and-add-to-dag)))
           :flag ,simplify-fun-call-and-add-to-dag-name)

         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (;TAKE-WHEN-<=-OF-LEN
                                   len-of-cadar-when-axe-treep
                                   pseudo-termp-of-cadddr-when-axe-treep
                                   axe-bind-free-result-okayp-rewrite
                                   symbol-alistp-when-alistp
                                   true-listp-of-cdr)
                                  (dargp-less-than
                                   natp
                                   quotep
                                   myquotep
                                   ))
                  :expand ((:free (memoization count other-hyps alist)
                                  ,call-of-relieve-free-var-hyp-and-all-others)
                           (:free (memoization count)
                                  ,call-of-relieve-rule-hyps)
                           (:free (memoization)
                                  (,RELIEVE-RULE-HYPS-NAME nil HYP-NUM ALIST RULE-SYMBOL
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            REWRITER-RULE-ALIST
                                                           REFINED-ASSUMPTION-ALIST

                                                           NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                           PRINT
                                                           INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  (,SIMPLIFY-TREES-AND-ADD-TO-DAG-NAME NIL
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                       REWRITER-RULE-ALIST
                                                                       REFINED-ASSUMPTION-ALIST

                                                                       NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                                        PRINT
                                                                       INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization count)
                                  ,call-of-simplify-trees-and-add-to-dag)
                           (:free (memoization limits info tries count)
                                  ,call-of-try-to-apply-rules)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag1)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag2)
                           (:free (memoization fn count)
                                  ,call-of-simplify-if-tree-and-add-to-dag3)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag1)
                           (:free (memoization count)
                                  ,call-of-simplify-boolif-tree-and-add-to-dag2)
                           (:free (memoization count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-tree-and-add-to-dag)
                           (:free (memoization count TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-fun-call-and-add-to-dag)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag2)
                           (:free (memoization count)
                                  ,call-of-simplify-bvif-tree-and-add-to-dag3)
                           (AXE-RULE-HYP-LISTP HYPS)))))

       ;; main theorems about the mutual-recursion:
       (,(pack$ 'defthm-flag-simplify-tree-and-add-to-dag- suffix)
         (defthm ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-relieve-free-var-hyp-and-all-others))
                         (all-axe-treep hyp-args)
                         (true-listp hyp-args)
                         (axe-rule-hyp-listp other-hyps)
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                         (symbol-alistp alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len)
                         (dargp-less-than-list-listp assumption-arg-lists dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 3 ,call-of-relieve-free-var-hyp-and-all-others)
                                  (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others)
                                  'dag-parent-array
                                  (mv-nth 5 ,call-of-relieve-free-var-hyp-and-all-others)
                                  (mv-nth 6 ,call-of-relieve-free-var-hyp-and-all-others)
                                  (mv-nth 7 ,call-of-relieve-free-var-hyp-and-all-others))
                         (<= dag-len (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others))
                         (maybe-bounded-memoizationp (mv-nth 8 ,call-of-relieve-free-var-hyp-and-all-others)
                                                     (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others))
                         (symbol-alistp (mv-nth 2 ,call-of-relieve-free-var-hyp-and-all-others))
                         (all-dargp-less-than (strip-cdrs (mv-nth 2 ,call-of-relieve-free-var-hyp-and-all-others))
                                                         (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 12 ,call-of-relieve-free-var-hyp-and-all-others)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 12 ,call-of-relieve-free-var-hyp-and-all-others)
                                                          (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others))))
           :flag ,relieve-free-var-hyp-and-all-others-name)

         (defthm ,(pack$ 'theorem-for-relieve-rule-hyps- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (axe-rule-hyp-listp hyps)
                         (not (mv-nth 0 ,call-of-relieve-rule-hyps))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                         (symbol-alistp alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 3 ,call-of-relieve-rule-hyps)
                                  (mv-nth 4 ,call-of-relieve-rule-hyps)
                                  'dag-parent-array
                                  (mv-nth 5 ,call-of-relieve-rule-hyps)
                                  (mv-nth 6 ,call-of-relieve-rule-hyps)
                                  (mv-nth 7 ,call-of-relieve-rule-hyps))
                         (<= dag-len (mv-nth 4 ,call-of-relieve-rule-hyps))
                         (maybe-bounded-memoizationp (mv-nth 8 ,call-of-relieve-rule-hyps)
                                               (mv-nth 4 ,call-of-relieve-rule-hyps))
                         (symbol-alistp (mv-nth 2 ,call-of-relieve-rule-hyps))
                         (all-dargp-less-than (strip-cdrs (mv-nth 2 ,call-of-relieve-rule-hyps))
                                                         (mv-nth 4 ,call-of-relieve-rule-hyps))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 12 ,call-of-relieve-rule-hyps)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 12 ,call-of-relieve-rule-hyps)
                                                          (mv-nth 4 ,call-of-relieve-rule-hyps))))
           :flag ,relieve-rule-hyps-name)

         (defthm ,(pack$ 'theorem-for-try-to-apply-rules- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-dargp-less-than args-to-match dag-len)
                         (not (mv-nth 0 ,call-of-try-to-apply-rules))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (all-stored-axe-rulep stored-rules)
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (axe-treep (mv-nth 1 ,call-of-try-to-apply-rules))
                         (bounded-axe-treep (mv-nth 1 ,call-of-try-to-apply-rules)
                                            (mv-nth 3 ,call-of-try-to-apply-rules))
                         (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-try-to-apply-rules)
                                  (mv-nth 3 ,call-of-try-to-apply-rules)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-try-to-apply-rules)
                                  (mv-nth 5 ,call-of-try-to-apply-rules)
                                  (mv-nth 6 ,call-of-try-to-apply-rules))
                         (<= dag-len (mv-nth 3 ,call-of-try-to-apply-rules))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-try-to-apply-rules)
                                               (mv-nth 3 ,call-of-try-to-apply-rules))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-try-to-apply-rules)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-try-to-apply-rules)
                                                          (mv-nth 3 ,call-of-try-to-apply-rules))))
           :flag ,try-to-apply-rules-name)

         (defthm ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-axe-treep trees)
                         (true-listp trees)
                         (all-bounded-axe-treep trees dag-len)
                         (not (mv-nth 0 ,call-of-simplify-trees-and-add-to-dag))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-trees-and-add-to-dag)
                                  (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-trees-and-add-to-dag)
                                  (mv-nth 5 ,call-of-simplify-trees-and-add-to-dag)
                                  (mv-nth 6 ,call-of-simplify-trees-and-add-to-dag))
                         (true-listp (mv-nth 1 ,call-of-simplify-trees-and-add-to-dag))
                         (all-dargp-less-than (mv-nth 1 ,call-of-simplify-trees-and-add-to-dag)
                                                         (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag))
                         ;; implied by the above
                         (all-dargp (mv-nth 1 ,call-of-simplify-trees-and-add-to-dag))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-trees-and-add-to-dag)
                                                     (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-trees-and-add-to-dag)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-trees-and-add-to-dag)
                                                          (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag))))
           :flag ,simplify-trees-and-add-to-dag-name)

         (defthm ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix)
           (implies (and (member-eq fn '(if myif))
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (dargp-less-than simplified-thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         ;; (all-bounded-axe-treep trees-equal-to-tree dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-if-tree-and-add-to-dag3)
                                  (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-if-tree-and-add-to-dag3)
                                  (mv-nth 5 ,call-of-simplify-if-tree-and-add-to-dag3)
                                  (mv-nth 6 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-if-tree-and-add-to-dag3)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-if-tree-and-add-to-dag3)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag3)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag3)
                                                          (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3))))
           :flag ,simplify-if-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix)
           (implies (and (member-eq fn '(if myif))
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (axe-treep thenpart)
                         (bounded-axe-treep thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         ;; (all-bounded-axe-treep trees-equal-to-tree dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-if-tree-and-add-to-dag2)
                                  (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-if-tree-and-add-to-dag2)
                                  (mv-nth 5 ,call-of-simplify-if-tree-and-add-to-dag2)
                                  (mv-nth 6 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-if-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-if-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag2)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag2)
                                                          (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2))))
           :flag ,simplify-if-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix)
           (implies (and (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (consp tree)
                         (member-eq (ffn-symb tree) '(if myif))
                         (= 3 (len (fargs tree)))
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-if-tree-and-add-to-dag1)
                                  (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-if-tree-and-add-to-dag1)
                                  (mv-nth 5 ,call-of-simplify-if-tree-and-add-to-dag1)
                                  (mv-nth 6 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-if-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-if-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag1)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag1)
                                                          (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1))))
           :flag ,simplify-if-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)
           (implies (and (natp simplified-test)
                         (< simplified-test dag-len)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (equal (len args) 3)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                  (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                  (mv-nth 5 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                  (mv-nth 6 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                                                          (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2))))
           :flag ,simplify-boolif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)
           (implies (and (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (equal (len args) 3)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                  (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                  (mv-nth 5 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                  (mv-nth 6 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (<= dag-len (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                                                          (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1))))
           :flag ,simplify-boolif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (dargp-less-than size-result dag-len)
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (dargp-less-than simplified-thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                  (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                  (mv-nth 5 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                  (mv-nth 6 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (<= dag-len (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                                                          (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3))))
           :flag ,simplify-bvif-tree-and-add-to-dag3-name)

         (defthm ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (equal (len args) 4)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                  (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                  (mv-nth 5 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                  (mv-nth 6 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (<= dag-len (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                                                          (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2))))
           :flag ,simplify-bvif-tree-and-add-to-dag2-name)

         (defthm ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (equal (len args) 4)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                  (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                  (mv-nth 5 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                  (mv-nth 6 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                                     (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                                                          (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1))))
           :flag ,simplify-bvif-tree-and-add-to-dag1-name)

         (defthm ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)
           (implies (and (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-tree-and-add-to-dag)
                                  (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-tree-and-add-to-dag)
                                  (mv-nth 5 ,call-of-simplify-tree-and-add-to-dag)
                                  (mv-nth 6 ,call-of-simplify-tree-and-add-to-dag))
                         (dargp-less-than (mv-nth 1 ,call-of-simplify-tree-and-add-to-dag)
                                                     (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-tree-and-add-to-dag)
                                                     (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-tree-and-add-to-dag)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-tree-and-add-to-dag)
                                                          (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag))))
           :flag ,simplify-tree-and-add-to-dag-name)

         (defthm ,(pack$ 'theorem-for-simplify-fun-call-and-add-to-dag- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (symbolp fn)
                         (not (equal 'quote fn))
                         (true-listp args)
                         (all-dargp-less-than args dag-len)
                         (not (mv-nth 0 ,call-of-simplify-fun-call-and-add-to-dag))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (and (wf-dagp 'dag-array
                                  (mv-nth 2 ,call-of-simplify-fun-call-and-add-to-dag)
                                  (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag)
                                  'dag-parent-array
                                  (mv-nth 4 ,call-of-simplify-fun-call-and-add-to-dag)
                                  (mv-nth 5 ,call-of-simplify-fun-call-and-add-to-dag)
                                  (mv-nth 6 ,call-of-simplify-fun-call-and-add-to-dag))
                         (DARGP-LESS-THAN (mv-nth 1 ,call-of-simplify-fun-call-and-add-to-dag)
                                                     (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag))
                         (<= dag-len
                             (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag))
                         (maybe-bounded-memoizationp (mv-nth 7 ,call-of-simplify-fun-call-and-add-to-dag)
                                               (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag))
                         (<= (alen1 'node-replacement-array node-replacement-array)
                             (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-fun-call-and-add-to-dag)))
                         (bounded-node-replacement-arrayp 'node-replacement-array
                                                          (mv-nth 11 ,call-of-simplify-fun-call-and-add-to-dag)
                                                          (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag))))
           :flag ,simplify-fun-call-and-add-to-dag-name)

         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (;TAKE-WHEN-<=-OF-LEN
                                   len-of-cadar-when-axe-treep
                                   pseudo-termp-of-cadddr-when-axe-treep
                                   axe-bind-free-result-okayp-rewrite
                                   symbol-alistp-when-alistp
                                   true-listp-of-cdr
                                   symbolp-when-member-equal
                                   not-equal-when-member-equal
                                   not-equal-when-member-equal-alt
                                   <=-trans
                                   <=-trans-2)
                                  (dargp-less-than
                                   natp
                                   quotep
                                   myquotep))
                  :expand ((:free (memoization ;count
                                   other-hyps alist)
                                  ,call-of-relieve-free-var-hyp-and-all-others)
                           (:free (memoization ;count
                                   )
                                  ,call-of-relieve-rule-hyps)
                           (:free (memoization)
                                  (,RELIEVE-RULE-HYPS-NAME nil HYP-NUM ALIST RULE-SYMBOL
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                            REWRITER-RULE-ALIST
                                                           REFINED-ASSUMPTION-ALIST

                                                           NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                           PRINT
                                                           INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization ;count
                                   )
                                  (,SIMPLIFY-TREES-AND-ADD-TO-DAG-NAME NIL
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                       REWRITER-RULE-ALIST
                                                                       REFINED-ASSUMPTION-ALIST

                                                                       NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                                        PRINT
                                                                       INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-trees-and-add-to-dag)
                           (:free (memoization limits info tries ;count
                                               )
                                  ,call-of-try-to-apply-rules)
                           (:free (memoization fn ;count
                                               )
                                  ,call-of-simplify-if-tree-and-add-to-dag1)
                           (:free (memoization fn ;count
                                               )
                                  ,call-of-simplify-if-tree-and-add-to-dag2)
                           (:free (memoization fn ;count
                                               )
                                  ,call-of-simplify-if-tree-and-add-to-dag3)
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-bvif-tree-and-add-to-dag1)
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-boolif-tree-and-add-to-dag1)
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-boolif-tree-and-add-to-dag2)
                           (:free (memoization ;count
                                   TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-tree-and-add-to-dag)
                           (:free (memoization ;count
                                   TREES-EQUAL-TO-TREE)
                                  ,call-of-simplify-fun-call-and-add-to-dag)
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-bvif-tree-and-add-to-dag2)
                           (:free (memoization ;count
                                   )
                                  ,call-of-simplify-bvif-tree-and-add-to-dag3)
                           (axe-rule-hyp-listp hyps)))))

       ;; Now we prove some facts that follow from the main theorem proved about the
       ;; mutual-recursion (e.g., weaker claims that are sometimes needed, or claims
       ;; phrased in a better way for rewriting):

       (defthm ,(pack$ 'bound-theorem-for-relieve-free-var-hyp-and-all-others- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-relieve-free-var-hyp-and-all-others))
                       (all-axe-treep hyp-args)
                       (true-listp hyp-args)
                       (axe-rule-hyp-listp other-hyps)
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (symbol-alistp alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len)
                       (dargp-less-than-list-listp assumption-arg-lists dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-relieve-rule-hyps- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (axe-rule-hyp-listp hyps)
                       (not (mv-nth 0 ,call-of-relieve-rule-hyps))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (symbol-alistp alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len)
                       (<= x dag-len))
                  (and
                   (<= x (mv-nth 4 ,call-of-relieve-rule-hyps))
                   (all-dargp (strip-cdrs (mv-nth 2 ,call-of-relieve-rule-hyps)))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-rule-hyps- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-relieve-rule-hyps- suffix)))))

       (defthm ,(pack$ 'corollary-theorem-for-relieve-rule-hyps- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (axe-rule-hyp-listp hyps)
                       (not (mv-nth 0 ,call-of-relieve-rule-hyps))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (symbol-alistp alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len))
                  (all-dargp (strip-cdrs (mv-nth 2 ,call-of-relieve-rule-hyps))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-rule-hyps- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-relieve-rule-hyps- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-try-to-apply-rules- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       (not (mv-nth 0 ,call-of-try-to-apply-rules))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-try-to-apply-rules)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-try-to-apply-rules- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-try-to-apply-rules- suffix)))))

       (defthm ,(pack$ 'corollary-theorem-for-try-to-apply-rules- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       (not (mv-nth 0 ,call-of-try-to-apply-rules))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (and (maybe-memoizationp (mv-nth 7 ,call-of-try-to-apply-rules))
                       (equal (alen1 'dag-parent-array (mv-nth 4 ,call-of-try-to-apply-rules))
                              (alen1 'dag-array (mv-nth 2 ,call-of-try-to-apply-rules)))
                       (dag-constant-alistp (mv-nth 5 ,call-of-try-to-apply-rules))
                       (bounded-dag-parent-arrayp 'dag-parent-array
                                                  (mv-nth 4 ,call-of-try-to-apply-rules)
                                                  (mv-nth 3 ,call-of-try-to-apply-rules))
                       (dag-parent-arrayp 'dag-parent-array (mv-nth 4 ,call-of-try-to-apply-rules))
                       (pseudo-dag-arrayp 'dag-array
                                          (mv-nth 2 ,call-of-try-to-apply-rules)
                                          (mv-nth 3 ,call-of-try-to-apply-rules))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-try-to-apply-rules- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-try-to-apply-rules- suffix)))))

       (defthm ,(pack$ 'pseudo-dag-arrayp-of-mv-nth-2-of-try-to-apply-rules- suffix)
         (implies (and (<= n (mv-nth 3 ,call-of-try-to-apply-rules))
                       (natp n)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       (not (mv-nth 0 ,call-of-try-to-apply-rules))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (PSEUDO-DAG-ARRAYP 'DAG-ARRAY
                                     (MV-NTH 2
                                             ,call-of-try-to-apply-rules)
                                     n))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-try-to-apply-rules- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-try-to-apply-rules- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-trees-and-add-to-dag- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-axe-treep trees)
                       (true-listp trees)
                       (all-bounded-axe-treep trees dag-len)
                       (not (mv-nth 0 ,call-of-simplify-trees-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x
                      (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'corollary-theorem-for-simplify-trees-and-add-to-dag- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-axe-treep trees)
                       (true-listp trees)
                       (all-bounded-axe-treep trees dag-len)
                       (not (mv-nth 0 ,call-of-simplify-trees-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (maybe-memoizationp (mv-nth 7 ,call-of-simplify-trees-and-add-to-dag)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-if-tree-and-add-to-dag3- suffix)
         (implies (and (member-eq fn '(if myif))
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (dargp-less-than simplified-thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag3))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       ;; (all-bounded-axe-treep trees-equal-to-tree dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-if-tree-and-add-to-dag2- suffix)
         (implies (and (member-eq fn '(if myif))
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (axe-treep thenpart)
                       (bounded-axe-treep thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       ;; (all-bounded-axe-treep trees-equal-to-tree dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-if-tree-and-add-to-dag1- suffix)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (member-eq (ffn-symb tree) '(if myif))
                       (= 3 (len (fargs tree)))
                       (symbol-listp monitored-symbols)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)

                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x
                      (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)
         (implies (and (natp simplified-test)
                       (< simplified-test dag-len)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (equal (len args) 3)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)
         (implies (and (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (equal (len args) 3)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (dargp-less-than size-result dag-len)
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (dargp-less-than simplified-thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (equal (len args) 4)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x
                      (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (equal (len args) 4)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len)
                       )
                  (<= x
                      (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'corollary-theorem-for-simplify-tree-and-add-to-dag- suffix)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (and (pseudo-dag-arrayp 'dag-array (mv-nth '2 ,call-of-simplify-tree-and-add-to-dag) (mv-nth '3 ,call-of-simplify-tree-and-add-to-dag))
                       (array1p 'dag-array (mv-nth 2 ,call-of-simplify-tree-and-add-to-dag))
                       (<= (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag)
                           (alen1 'dag-array (mv-nth 2 ,call-of-simplify-tree-and-add-to-dag)))
                       (maybe-memoizationp (mv-nth 7 ,call-of-simplify-tree-and-add-to-dag))
                       (dargp (mv-nth 1 ,call-of-simplify-tree-and-add-to-dag))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'pseudo-dag-arrayp-of-mv-nth-2-of- simplify-tree-and-add-to-dag-name)
         (implies (and (natp len)
                       (<= len
                           (MV-NTH '3
                                   ,call-of-simplify-tree-and-add-to-dag))
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (PSEUDO-DAG-ARRAYP
                   'DAG-ARRAY
                   (MV-NTH '2
                           ,call-of-simplify-tree-and-add-to-dag)
                   len))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       (defthm ,(pack$ '<-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
         (implies (and ;(natp bound)
                   (<= (MV-NTH '3
                               ,call-of-simplify-tree-and-add-to-dag)
                       bound)
                   (not (consp (MV-NTH '1
                                       ,call-of-simplify-tree-and-add-to-dag)))
                   (axe-treep tree)
                   (bounded-axe-treep tree dag-len)
                   (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                   (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                   (maybe-bounded-memoizationp memoization dag-len)
                   (trees-to-memoizep trees-equal-to-tree)
                   (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                   (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                   (rule-alistp rewriter-rule-alist)
                   (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (< (MV-NTH '1 ,call-of-simplify-tree-and-add-to-dag)
                     bound))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'dargp-less-than-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
         (implies (and (<= (MV-NTH '3
                               ,call-of-simplify-tree-and-add-to-dag)
                           bound)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (DARGP-LESS-THAN (MV-NTH '1
                                                      ,call-of-simplify-tree-and-add-to-dag)
                                              bound))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'dargp-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (dargp (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)
                                      ,(pack$ 'dargp-less-than-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)))))

       ;; Use consp as the normal form
       (defthm ,(pack$ 'natp-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (equal (natp (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag))
                         (not (consp (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag)))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)
                                      ,(pack$ 'dargp-less-than-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ,(pack$ 'dargp-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)))))

       ;; Use consp as the normal form
       (defthm ,(pack$ 'myquotep-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (equal (myquotep (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag))
                         (consp (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)
                                      ,(pack$ 'dargp-less-than-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ,(pack$ 'dargp-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ))))

       ;; Use consp as the normal form
       (defthm ,(pack$ 'equal-of-car-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name '-and-quote)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (equal (equal (car (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag)) 'quote)
                         (consp (mv-nth '1 ,call-of-simplify-tree-and-add-to-dag))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)
                                      ,(pack$ 'dargp-less-than-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ,(pack$ 'dargp-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ,(pack$ 'myquotep-of-mv-nth-1-of- simplify-tree-and-add-to-dag-name)
                                      ))))

       (defthm ,(pack$ 'bound-theorem-for-simplify-tree-and-add-to-dag- suffix)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x dag-len))
                  (<= x
                      (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'maybe-memoizationp-of-mv-nth-7-of- simplify-fun-call-and-add-to-dag-name)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (symbolp fn)
                       (not (equal 'quote fn))
                       (true-listp args)
                       (all-dargp-less-than args dag-len)
                       (not (mv-nth 0 ,call-of-simplify-fun-call-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes)
                       (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                  (maybe-memoizationp (mv-nth 7 ,call-of-simplify-fun-call-and-add-to-dag)))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-fun-call-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-fun-call-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-relieve-free-var-hyp-and-all-others- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-relieve-free-var-hyp-and-all-others))
                       (all-axe-treep hyp-args)
                       (true-listp hyp-args)
                       (axe-rule-hyp-listp other-hyps)
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (symbol-alistp alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len)
                       (dargp-less-than-list-listp assumption-arg-lists dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 12 ,call-of-relieve-free-var-hyp-and-all-others))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-relieve-rule-hyps- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (axe-rule-hyp-listp hyps)
                       (not (mv-nth 0 ,call-of-relieve-rule-hyps))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (symbol-alistp alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 12 ,call-of-relieve-rule-hyps))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-rule-hyps- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-relieve-rule-hyps- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-try-to-apply-rules- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       (not (mv-nth 0 ,call-of-try-to-apply-rules))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-try-to-apply-rules))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-try-to-apply-rules- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-try-to-apply-rules- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-trees-and-add-to-dag- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-axe-treep trees)
                       (true-listp trees)
                       (all-bounded-axe-treep trees dag-len)
                       (not (mv-nth 0 ,call-of-simplify-trees-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-trees-and-add-to-dag))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-if-tree-and-add-to-dag3- suffix)
         (implies (and (or (equal fn 'if)
                           (equal fn 'myif))
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (dargp-less-than simplified-thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag3))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag3))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-if-tree-and-add-to-dag2- suffix)
         (implies (and (or (equal fn 'if)
                           (equal fn 'myif))
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (axe-treep thenpart)
                       (bounded-axe-treep thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag2))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-if-tree-and-add-to-dag1- suffix)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (consp tree)
                       (or (eq (ffn-symb tree) 'if)
                           (eq (ffn-symb tree) 'myif))
                       (= 3 (len (fargs tree)))
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag1))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)
         (implies (and (natp simplified-test)
                       (< simplified-test dag-len)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (equal (len args) 3)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag2))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)
         (implies (and (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (equal (len args) 3)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag1))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (dargp-less-than size-result dag-len)
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (dargp-less-than simplified-thenpart dag-len)
                       (axe-treep elsepart)
                       (bounded-axe-treep elsepart dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag3))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (natp simplified-test)
                       (< simplified-test dag-len)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (equal (len args) 4)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag2))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-axe-treep args)
                       (all-bounded-axe-treep args dag-len)
                       (consp tree)
                       (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (equal (len args) 4)
                       (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag1))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)))))

       (defthm ,(pack$ 'node-replacement-array-bound-theorem-for-simplify-tree-and-add-to-dag- suffix)
         (implies (and (axe-treep tree)
                       (bounded-axe-treep tree dag-len)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                       (maybe-bounded-memoizationp memoization dag-len)
                       (trees-to-memoizep trees-equal-to-tree)
                       (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                       (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                       (rule-alistp rewriter-rule-alist)
                       (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                       (<= x (alen1 'node-replacement-array node-replacement-array)))
                  (<= x (alen1 'node-replacement-array (mv-nth 11 ,call-of-simplify-tree-and-add-to-dag))))
         :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                  :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))

       ;; This next batch shows that node-replacement-arrayp always holds (we known from above that bounded-node-replacement-arrayp holds):
       (progn
         (defthm ,(pack$ 'node-replacement-arrayp-of-relieve-free-var-hyp-and-all-others- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-relieve-free-var-hyp-and-all-others))
                         (all-axe-treep hyp-args)
                         (true-listp hyp-args)
                         (axe-rule-hyp-listp other-hyps)
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                         (symbol-alistp alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len)
                         (dargp-less-than-list-listp assumption-arg-lists dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 12 ,call-of-relieve-free-var-hyp-and-all-others)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-relieve-free-var-hyp-and-all-others- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-relieve-rule-hyps- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (axe-rule-hyp-listp hyps)
                         (not (mv-nth 0 ,call-of-relieve-rule-hyps))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                         (symbol-alistp alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 12 ,call-of-relieve-rule-hyps)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-relieve-rule-hyps- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-relieve-rule-hyps- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-try-to-apply-rules- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-dargp-less-than args-to-match dag-len)
                         (not (mv-nth 0 ,call-of-try-to-apply-rules))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (all-stored-axe-rulep stored-rules)
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-try-to-apply-rules)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-try-to-apply-rules- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-try-to-apply-rules- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-trees-and-add-to-dag- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-axe-treep trees)
                         (true-listp trees)
                         (all-bounded-axe-treep trees dag-len)
                         (not (mv-nth 0 ,call-of-simplify-trees-and-add-to-dag))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-trees-and-add-to-dag)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-trees-and-add-to-dag- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-if-tree-and-add-to-dag3- suffix)
           (implies (and (or (equal fn 'if)
                             (equal fn 'myif))
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (dargp-less-than simplified-thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag3)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag3- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-if-tree-and-add-to-dag2- suffix)
           (implies (and (or (equal fn 'if)
                             (equal fn 'myif))
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (axe-treep thenpart)
                         (bounded-axe-treep thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag2)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag2- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-if-tree-and-add-to-dag1- suffix)
           (implies (and (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (consp tree)
                         (or (eq (ffn-symb tree) 'if)
                             (eq (ffn-symb tree) 'myif))
                         (= 3 (len (fargs tree)))
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-if-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-if-tree-and-add-to-dag1)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-if-tree-and-add-to-dag1- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-boolif-tree-and-add-to-dag2- suffix)
           (implies (and (natp simplified-test)
                         (< simplified-test dag-len)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (equal (len args) 3)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag2- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-boolif-tree-and-add-to-dag1- suffix)
           (implies (and (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (equal (len args) 3)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-boolif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-boolif-tree-and-add-to-dag1- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-bvif-tree-and-add-to-dag3- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (dargp-less-than size-result dag-len)
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (dargp-less-than simplified-thenpart dag-len)
                         (axe-treep elsepart)
                         (bounded-axe-treep elsepart dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag3))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag3- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-bvif-tree-and-add-to-dag2- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp simplified-test)
                         (< simplified-test dag-len)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (equal (len args) 4)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag2))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag2- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-bvif-tree-and-add-to-dag1- suffix)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-axe-treep args)
                         (all-bounded-axe-treep args dag-len)
                         (consp tree)
                         (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (equal (len args) 4)
                         (not (mv-nth 0 ,call-of-simplify-bvif-tree-and-add-to-dag1))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-bvif-tree-and-add-to-dag1- suffix)))))

         (defthm ,(pack$ 'node-replacement-arrayp-of-simplify-tree-and-add-to-dag- suffix)
           (implies (and (axe-treep tree)
                         (bounded-axe-treep tree dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (not (mv-nth 0 ,call-of-simplify-tree-and-add-to-dag))
                         (maybe-bounded-memoizationp memoization dag-len)
                         (trees-to-memoizep trees-equal-to-tree)
                         (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                         (natp node-replacement-array-num-valid-nodes) (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                         (rule-alistp rewriter-rule-alist)
                         (bounded-refined-assumption-alistp refined-assumption-alist dag-len))
                    (node-replacement-arrayp 'node-replacement-array (mv-nth 11 ,call-of-simplify-tree-and-add-to-dag)))
           :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
                    :in-theory (disable ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))
         )


       ;; ;todo: more like this.  or just add to the corollary theorems above?
       ;; (def-dag-builder-theorems
       ;;   (,simplify-tree-and-add-to-dag-name tree trees-equal-to-tree dag-array dag-len dag-parent-array
       ;;                                 dag-constant-alist dag-variable-alist memoization info tries limits
       ;;                                 rewriter-rule-alist
       ;;                                 refined-assumption-alist
       ;;
       ;;                                 node-replacement-array-num-valid-nodes
       ;;                                 print
       ;;                                 interpreted-function-alist
       ;;                                 monitored-symbols count)
       ;;   (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array)
       ;;   :hyps ((axe-treep tree)
       ;;          (bounded-axe-treep tree dag-len)
       ;;          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
       ;;          (not (mv-nth 0 (,simplify-tree-and-add-to-dag-name
       ;;                          tree trees-equal-to-tree dag-array dag-len dag-parent-array
       ;;                          dag-constant-alist dag-variable-alist memoization info tries limits
       ;;                          rewriter-rule-alist
       ;;                          refined-assumption-alist
       ;;
       ;;                          node-replacement-array-num-valid-nodes
       ;;                          print
       ;;                          interpreted-function-alist
       ;;                          monitored-symbols count)))
       ;;
       ;;          (maybe-bounded-memoizationp memoization dag-len)
       ;;          (trees-to-memoizep trees-equal-to-tree)
       ;;
       ;;          (alistp node-replacement-array-num-valid-nodes)
       ;;          (all-dargp-less-than (strip-cdrs node-replacement-array-num-valid-nodes) dag-len)
       ;;          (rule-alistp rewriter-rule-alist)
       ;;          (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
       ;;          )
       ;;   :hyps-everywhere t
       ;;   :dag-array-name 'dag-array
       ;;   :dag-parent-array-name 'dag-parent-array
       ;;   :hints (("Goal" :use (:instance ,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix))
       ;;            :in-theory (e/d (WF-DAGP) (,(pack$ 'theorem-for-simplify-tree-and-add-to-dag- suffix)))))
       ;;   )

       ;; Show that the dag-len is always a natp:
       (,(pack$ 'defthm-flag-simplify-tree-and-add-to-dag- suffix)
        (defthm ,(pack$ 'natp-of-mv-nth-4-of-relieve-free-var-hyp-and-all-others- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 4 ,call-of-relieve-free-var-hyp-and-all-others)))
          :rule-classes (:rewrite :type-prescription) :flag ,relieve-free-var-hyp-and-all-others-name)

        (defthm ,(pack$ 'natp-of-mv-nth-4-of-relieve-rule-hyps- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 4 ,call-of-relieve-rule-hyps)))
          :rule-classes (:rewrite :type-prescription) :flag ,relieve-rule-hyps-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-try-to-apply-rules- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-try-to-apply-rules)))
          :rule-classes (:rewrite :type-prescription) :flag ,try-to-apply-rules-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-trees-and-add-to-dag- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-trees-and-add-to-dag)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-trees-and-add-to-dag-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-if-tree-and-add-to-dag3- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag3)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-if-tree-and-add-to-dag3-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-if-tree-and-add-to-dag2- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag2)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-if-tree-and-add-to-dag2-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-if-tree-and-add-to-dag1- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-if-tree-and-add-to-dag1)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-if-tree-and-add-to-dag1-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-boolif-tree-and-add-to-dag2- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag2)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-boolif-tree-and-add-to-dag2-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-boolif-tree-and-add-to-dag1- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-boolif-tree-and-add-to-dag1)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-boolif-tree-and-add-to-dag1-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-bvif-tree-and-add-to-dag3- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag3)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-bvif-tree-and-add-to-dag3-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-bvif-tree-and-add-to-dag2- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag2)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-bvif-tree-and-add-to-dag2-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-bvif-tree-and-add-to-dag- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-bvif-tree-and-add-to-dag1)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-bvif-tree-and-add-to-dag1-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-tree-and-add-to-dag- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-tree-and-add-to-dag)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-tree-and-add-to-dag-name)

        (defthm ,(pack$ 'natp-of-mv-nth-3-of-simplify-fun-call-and-add-to-dag- suffix)
          (implies (natp dag-len)
                   (natp (mv-nth 3 ,call-of-simplify-fun-call-and-add-to-dag)))
          :rule-classes (:rewrite :type-prescription) :flag ,simplify-fun-call-and-add-to-dag-name)

        :hints (("Goal" :do-not '(generalize eliminate-destructors)
                 :in-theory (e/d (;TAKE-WHEN-<=-OF-LEN
                                  len-of-cadar-when-axe-treep
                                  pseudo-termp-of-cadddr-when-axe-treep
                                  axe-bind-free-result-okayp-rewrite
                                  symbol-alistp-when-alistp
                                  true-listp-of-cdr)
                                 (dargp-less-than
                                  natp
                                  quotep
                                  myquotep))
                 :expand ((:free (memoization count other-hyps alist)
                                 ,call-of-relieve-free-var-hyp-and-all-others)
                          (:free (memoization count)
                                 ,call-of-relieve-rule-hyps)
                          (:free (memoization)
                                 (,RELIEVE-RULE-HYPS-NAME nil HYP-NUM ALIST RULE-SYMBOL
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                          REWRITER-RULE-ALIST
                                                          REFINED-ASSUMPTION-ALIST
                                                          NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                          PRINT
                                                          INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                          (:free (memoization count)
                                 (,SIMPLIFY-TREES-AND-ADD-TO-DAG-NAME NIL
                                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits node-replacement-array
                                                                      REWRITER-RULE-ALIST
                                                                      REFINED-ASSUMPTION-ALIST
                                                                      NODE-REPLACEMENT-ARRAY-NUM-VALID-NODES
                                                                      PRINT
                                                                      INTERPRETED-FUNCTION-ALIST known-booleans MONITORED-SYMBOLS COUNT))
                          (:free (memoization count)
                                 ,call-of-simplify-trees-and-add-to-dag)
                          (:free (memoization limits info tries count)
                                 ,call-of-try-to-apply-rules)
                          (:free (memoization fn count)
                                 ,call-of-simplify-if-tree-and-add-to-dag1)
                          (:free (memoization fn count)
                                 ,call-of-simplify-if-tree-and-add-to-dag2)
                          (:free (memoization fn count)
                                 ,call-of-simplify-if-tree-and-add-to-dag3)
                          (:free (memoization count)
                                 ,call-of-simplify-bvif-tree-and-add-to-dag1)
                          (:free (memoization count)
                                 ,call-of-simplify-boolif-tree-and-add-to-dag1)
                          (:free (memoization count)
                                 ,call-of-simplify-boolif-tree-and-add-to-dag2)
                          (:free (memoization count TREES-EQUAL-TO-TREE)
                                 ,call-of-simplify-tree-and-add-to-dag)
                          (:free (memoization count TREES-EQUAL-TO-TREE)
                                 ,call-of-simplify-fun-call-and-add-to-dag)
                          (:free (memoization count)
                                 ,call-of-simplify-bvif-tree-and-add-to-dag2)
                          (:free (memoization count)
                                 ,call-of-simplify-bvif-tree-and-add-to-dag3)
                          (axe-rule-hyp-listp hyps)))))

       (verify-guards ,relieve-free-var-hyp-and-all-others-name
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :expand ((AXE-BIND-FREE-FUNCTION-APPLICATIONP (NTH 1 (CAR HYPS)))
                           (AXE-RULE-HYP-LISTP HYPS)
                           (AXE-TREEP TREE)
                           (MYQUOTEP TREE)
                           (QUOTEP TREE))
                  :in-theory (e/d (true-list-of-car-when-DARGP-LESS-THAN-LIST-LISTP
                                   all-myquote-or-natp-of-car-when-dargp-less-than-list-listp
                                   ALL-MYQUOTEP-when-ALL-dargp
                                   axe-bind-free-result-okayp-rewrite
                                   AXE-RULE-HYPP
                                   INTEGERP-WHEN-DARGP
                                   <=-of-0-WHEN-DARGP
                                   <-WHEN-DARGP-less-than
                                   len-when-dargp
                                   natp-WHEN-DARGP
                                   quotep-when-dargp
                                   <-of--1-when-dargp
                                   integerp-of-if
                                   <-of--0-when-dargp
                                   NATP-OF-+-OF-1
                                   <-OF-+-OF-1-WHEN-INTEGERS
                                   ;;SYMBOL-ALISTP-WHEN-ALISTP
                                   cadr-becomes-nth-of-1
                                   memoizationp-when-maybe-memoizationp
                                   tree-to-memoizep ;todo
                                   <=-trans ;drop?
                                   symbolp-when-member-equal)
                                  (dargp
                                   dargp-less-than
                                   natp
                                   quotep
                                   myquotep
                                   nth-of-cdr
                                   cadr-becomes-nth-of-1)))
                 ;;(and stable-under-simplificationp '(:cases (memoizep)))
                 ))

       ;; Simplify a term and return an equivalent DAG.  Returns (mv erp dag-or-quotep).
       ;; TODO: add support for multiple rule-alists.
       (defund ,simplify-term-name (term
                                    assumptions
                                    rule-alist
                                    interpreted-function-alist
                                    monitored-symbols
                                    memoizep
                                    ;; todo: add context array and other args?
                                    count-hitsp
                                    wrld)
         (declare (xargs :guard (and (pseudo-termp term)
                                     (pseudo-term-listp assumptions)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (symbol-listp monitored-symbols)
                                     (booleanp memoizep)
                                     (booleanp count-hitsp)
                                     (plist-worldp wrld))
                         :guard-hints (("Goal" :in-theory (e/d (natp-when-dargp
                                                                natp-of-+-of-1
                                                                <-of-+-of-1-when-integers
                                                                <-OF-+-OF-1-WHEN-natps
                                                                ;; integerp-when-dargp ;caused problems when natp is known
                                                                axe-treep-when-pseudo-termp
                                                                dargp-when-natp)
                                                               (natp
                                                                NATP-WHEN-DARGP ;caused problems when natp is known
                                                                ))))))
         ;; Could create a variant of ,simplify-tree-and-add-to-dag-name that is restricted to terms:
         (b* ((dag-array (make-empty-array 'dag-array 1000000)) ;todo: make this size adjustable
              (dag-parent-array (make-empty-array 'dag-parent-array 1000000)) ;todo: make this size adjustable
              ;; Create the refined-assumption-alist and add nodes it refers to to the DAG:
              ((mv erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (refine-assumptions-and-add-to-dag-array assumptions
                                                        'dag-array dag-array
                                                        0 ;dag-len
                                                        'dag-parent-array dag-parent-array
                                                        nil ;;dag-constant-alist
                                                        nil ;;dag-variable-alist
                                                        (known-booleans wrld)))
              ((when erp) (mv erp nil))
              ;; TODO: Combine this with the above:
              ((mv erp node-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (make-node-replacement-alist-and-add-to-dag-array assumptions
                                                                 'dag-array ;todo: make a specialized version?
                                                                 dag-array dag-len
                                                                 'dag-parent-array ;todo: make a specialized version?
                                                                 dag-parent-array dag-constant-alist dag-variable-alist
                                                                 wrld))
              ((when erp) (mv erp nil))
              (node-replacement-array (make-into-array 'node-replacement-array node-replacement-alist))
              (node-replacement-array-num-valid-nodes (+ 1 (max-key node-replacement-alist 0))) ;todo: optimize if no assumptions?  the array len of 0 will prevent any lookup
              ((when erp) (mv erp nil))
              ((mv erp
                   new-nodenum-or-quotep
                   dag-array
                   & & & & ; dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   memoization
                   info
                   &                                          ; tries
                   &                                          ; limits
                   & ; node-replacement-array
                   )
               ;; TODO: Make a version that recurs over the structure of TERM
               ;; and then restrict simplify-tree-and-add-to-dag... to terms
               ;; that don't contain vars.
               (,simplify-tree-and-add-to-dag-name term
                                                   nil ;trees-equal-to-tree
                                                   dag-array
                                                   dag-len
                                                   dag-parent-array
                                                   dag-constant-alist
                                                   dag-variable-alist
                                                   (if memoizep
                                                       (empty-memoization)
                                                     ;; not memoizing:
                                                     nil)
                                                   (if count-hitsp
                                                       (empty-info-world)
                                                     nil ;means no hit counting
                                                     )
                                                   0 ; tries
                                                   nil ; limits
                                                   node-replacement-array
                                                   rule-alist
                                                   refined-assumption-alist
                                                   node-replacement-array-num-valid-nodes
                                                   nil ;print
                                                   interpreted-function-alist
                                                   (known-booleans wrld) ;skip if memoizing since we can't use contexts?
                                                   monitored-symbols
                                                   1000000000 ;count
                                                   ))
              ((when erp) (mv erp nil))
              (- (and count-hitsp
                      (print-hit-counts t info (rules-from-rule-alist rule-alist))))
              (- (and nil ;; change to t to print info on the memoization
                      memoization
                      (print-memo-stats memoization)))
              ;; TODO: Print the hit info
              )
           (if (consp new-nodenum-or-quotep) ;check for quotep
               (mv (erp-nil) new-nodenum-or-quotep)
             (mv (erp-nil) (drop-non-supporters-array 'dag-array dag-array new-nodenum-or-quotep nil)))))

       (defthm ,(pack$ 'type-of-mv-nth-1-of- simplify-term-name)
         (implies (and (not (mv-nth 0 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))) ; no error
                   (pseudo-termp term)
                   (pseudo-term-listp assumptions)
                   (rule-alistp rule-alist)
                   (interpreted-function-alistp interpreted-function-alist)
                   (symbol-listp monitored-symbols)
                   (booleanp memoizep)
                   (booleanp count-hitsp)
                   (plist-worldp wrld))
                  (or (myquotep (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld)))
                      (pseudo-dagp (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld)))))
         :rule-classes nil
         :hints (("Goal" :in-theory (e/d (,simplify-term-name
                                          axe-treep-when-pseudo-termp
                                          natp-of-+-of-1
                                          natp-of-max-key-2
                                          <-of-if-arg1
                                          max-key-hack
                                          max-key-hack-2
                                          <-OF-+-OF-1-WHEN-INTEGERS
                                          integerp-when-natp)
                                         (natp)))))

       (defthm ,(pack$ 'pseudo-dagp-of-mv-nth-1-of- simplify-term-name)
         (implies (and (not (mv-nth 0 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))) ; no error
                       (not (quotep (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld)))) ;not a constant
                       (pseudo-termp term)
                       (pseudo-term-listp assumptions)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (booleanp memoizep)
                       (booleanp count-hitsp)
                       (plist-worldp wrld))
                  (pseudo-dagp (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of-mv-nth-1-of- simplify-term-name)))))

       ;; (defthm ,(pack$ 'weak-dagp-of-mv-nth-1-of- simplify-term-name)
       ;;   (implies (and (not (mv-nth 0 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld)))
       ;;                 (not (quotep (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))))
       ;;                 (pseudo-termp term)
       ;;                 (pseudo-term-listp assumptions)
       ;;                 (rule-alistp rule-alist)
       ;;                 (interpreted-function-alistp interpreted-function-alist)
       ;;                 (symbol-listp monitored-symbols)
       ;;                 (booleanp memoizep)
       ;;                 (booleanp count-hitsp)
       ;;                 (plist-worldp wrld))
       ;;            (weak-dagp (mv-nth 1 (,simplify-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))))
       ;;   :hints (("Goal" :use (:instance ,(pack$ 'pseudo-dagp-of-mv-nth-1-of- simplify-term-name))
       ;;            :in-theory (disable ,(pack$ 'pseudo-dagp-of-mv-nth-1-of- simplify-term-name)))))

       ;; Simplify a term and return a term (not a DAG).  Returns (mv erp term).
       (defund ,simp-term-name (term
                                assumptions
                                rule-alist
                                interpreted-function-alist
                                monitored-symbols
                                memoizep
                                ;; todo: add context array and other args?
                                count-hitsp
                                wrld)
         (declare (xargs :guard (and (pseudo-termp term)
                                     (pseudo-term-listp assumptions)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (symbol-listp monitored-symbols)
                                     (booleanp memoizep)
                                     (booleanp count-hitsp)
                                     (plist-worldp wrld))))
         (b* (((mv erp dag) (,simplify-term-name term
                                                 assumptions
                                                 rule-alist
                                                 interpreted-function-alist
                                                 monitored-symbols
                                                 memoizep
                                                 ;; todo: add context array and other args?
                                                 count-hitsp
                                                 wrld))
              ((when erp) (mv erp nil)))
           (mv (erp-nil) (if (quotep dag)
                             dag
                           (dag-to-term dag)))))

       (defthm ,(pack$ 'pseudo-termp-of-mv-nth-1-of- simp-term-name)
         (implies (and (pseudo-termp term)
                       (pseudo-term-listp assumptions)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (booleanp memoizep)
                       (booleanp count-hitsp)
                       (plist-worldp wrld))
                  (pseudo-termp (mv-nth 1 (,simp-term-name term assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of-mv-nth-1-of- simplify-term-name))
                  :in-theory (e/d (,simp-term-name) (,(pack$ 'pseudo-dagp-of-mv-nth-1-of- simplify-term-name))))))

       ;; Simplify a list of terms, returning a list of the simplified terms
       ;; (not DAGs).  Returns (mv erp terms).
       (defun ,simp-terms-name (terms
                                assumptions
                                rule-alist
                                interpreted-function-alist
                                monitored-symbols
                                memoizep
                                ;; todo: add context array and other args?
                                count-hitsp
                                wrld)
         (declare (xargs :guard (and (pseudo-term-listp terms)
                                     (pseudo-term-listp assumptions)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (symbol-listp monitored-symbols)
                                     (booleanp memoizep)
                                     (booleanp count-hitsp)
                                     (plist-worldp wrld))))
         (if (endp terms)
             (mv (erp-nil) nil)
           (b* (((mv erp first-res)
                 (,simp-term-name (first terms)
                                  assumptions
                                  rule-alist
                                  nil
                                  nil
                                  nil
                                  t
                                  wrld))
                ((when erp) (mv erp nil))
                ((mv erp rest-res)
                 (,simp-terms-name (rest terms)
                                   assumptions
                                   rule-alist
                                   interpreted-function-alist
                                   monitored-symbols
                                   memoizep
                                   count-hitsp
                                   wrld))
                ((when erp) (mv erp nil)))
             (mv (erp-nil)
                 (cons first-res rest-res)))))

       (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- simp-terms-name)
         (true-listp (mv-nth 1 (,simp-terms-name terms assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld)))
         :rule-classes :type-prescription
         :hints (("Goal" :in-theory (enable ,simp-terms-name))))

       (defthm ,(pack$ 'pseudo-term-listp-of-mv-nth-1-of- simp-terms-name)
         (implies (and (pseudo-term-listp terms)
                       (pseudo-term-listp assumptions)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (booleanp memoizep)
                       (booleanp count-hitsp)
                       (plist-worldp wrld))
                  (pseudo-term-listp (mv-nth 1 (,simp-terms-name terms assumptions rule-alist interpreted-function-alist monitored-symbols memoizep count-hitsp wrld))))
         :hints (("Goal" :in-theory (enable ,simp-terms-name))))
       )))

(defmacro make-rewriter-simple (suffix
                                evaluator-base-name
                                eval-axe-syntaxp-expr-name
                                eval-axe-bind-free-function-application-name)
  (make-rewriter-simple-fn suffix
                           evaluator-base-name
                           eval-axe-syntaxp-expr-name
                           eval-axe-bind-free-function-application-name))
