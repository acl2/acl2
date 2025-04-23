; A tool to make an Axe Prover for a given purpose
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

;; This tool generates custom Axe Provers.  Each generated prover can use a
;; different evaluator, syntaxp-evaluator, and bind-free-evaluator and can have
;; its own set of default-global-rules.

;; Currently, these provers do not use STP, do not support work-hard, do not
;; handle DAGs embedded inside terms.

;; See also the legacy prover in prover.lisp.  Unlike this book, that one
;; depends on skip-proofs!

;; TODO: implement backchain limits, polarities, improve handling of equivs

;; TODO: use faster tests than equal in some places below?

;; TODO: Consider making splitting just another tactic (but then a tactic must be able to produce a list of problems).

;; TODO: Add a :cases tactic

;; TODO: Add a :stp tactic

;; TODO: Add a :sweep-and-merge tactic

;; TODO: Consider having this, or at least the rewriter part, use stobjs (rewrite-stobj, rewrite-stobj2) like make-rewriter-simple.lisp.

;; Consider doing (set-evisc-tuple t :iprint nil :sites :gag-mode) when working
;; with calls to make-prover-simple, to prevent printing of enormous induction
;; schemes.

(include-book "prover-common")
(include-book "splitting")
(include-book "elim")
;; (include-book "substitute-vars")
(include-book "substitute-vars2")
(include-book "get-disjuncts")
(include-book "rule-alists")
(include-book "interpreted-function-alists") ; for interpreted-function-alist-completep
(include-book "make-implication-dag")
(include-book "elaborate-rule-items")
(include-book "axe-clause-utilities")
(include-book "kestrel/utilities/defconst-computed" :dir :system)
(include-book "kestrel/utilities/equal" :dir :system) ; for equal-same
(include-book "kestrel/utilities/doublets2" :dir :system)
(include-book "axe-bind-free-result-okayp")
(include-book "rewriter-common") ; for alist-suitable-for-hypsp-of-unify-terms-and-dag-items-fast-when-stored-axe-rulep
(include-book "kestrel/utilities/rational-printing" :dir :system)
;(include-book "contexts") ;for max-nodenum-in-context
(include-book "unify-term-and-dag-fast")
(include-book "hit-counts")
(include-book "get-args-not-done")
(include-book "tries")
;(include-book "result-array")
(include-book "result-alist")
(include-book "alist-suitable-for-hypsp")
(include-book "make-sublis-var-and-eval-simple")
(include-book "make-subcor-var-and-eval-simple")
;; (include-book "make-instantiation-code-simple")
(include-book "make-instantiation-code-simple-free-vars")
(include-book "make-instantiation-code-simple-no-free-vars2")
(include-book "match-hyp-with-nodenum-to-assume-false")
(include-book "dag-or-term-to-dag-basic") ;todo: gen?
;(include-book "merge-tree-into-dag-array-basic") ;for merge-trees-into-dag-array-basic ;todo: gen?
;(include-book "kestrel/utilities/all-vars-in-term-bound-in-alistp" :dir :system)
(include-book "make-assumption-array")
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/terms-light/sublis-var-simple-proofs" :dir :system))

;move
(defthm symbol-doublet-listp-forward-to-alistp
  (implies (symbol-doublet-listp x)
           (alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-doublet-listp alistp))))

(defthm symbol-doublet-listp-forward-to-doublet-listp
  (implies (symbol-doublet-listp x)
           (doublet-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-doublet-listp alistp))))

(defthm symbol-doublet-listp-forward-to-symbol-listp-of-strip-cars
  (implies (symbol-doublet-listp x)
           (symbol-listp (strip-cars x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-doublet-listp alistp))))

(defthm symbol-doublet-listp-forward-to-all->=-len-of-2
  (implies (symbol-doublet-listp x)
           (all->=-len x 2))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-doublet-listp alistp))))

(defthm symbol-alistp-of-doublets-to-alist
  (equal (symbol-alistp (doublets-to-alist doublets))
         (symbol-listp (strip-cars doublets))))

(defthm symbol-term-alistp-of-doublets-to-alist
  (equal (symbol-term-alistp (doublets-to-alist doublets))
         (and (symbol-listp (strip-cars doublets))
              (pseudo-term-listp (strip-cadrs doublets)))))

(defthm axe-tree-listp-of-non-negated-nodenums-in-context-when-contextp
  (implies (and (contextp x)
                (not (equal :false x)))
           (axe-tree-listp (non-negated-nodenums-in-context x)))
  :hints (("Goal" :in-theory (e/d (non-negated-nodenums-in-context
                                     contextp
                                     natp-of-car-when-possibly-negated-nodenumsp)
                                  (natp)))))

(defthmd <-of--1-when-natp
  (implies (natp x)
           (not (< x -1))))

;move
(defthm nat-listp-when-all-natp
  (implies (all-natp x)
           (equal (nat-listp x)
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable nat-listp all-natp true-listp))))

;; (defthmd true-listp-when-nat-listp
;;   (implies (nat-listp x)
;;            (true-listp x)))

;; ;also in merge-sort
;; (defthmd len-of-cdr-better-for-axe-prover
;;   (equal (len (cdr x))
;;          (if (equal 0 (len x))
;;              0 (+ -1 (len x)))))

;; ;also in merge-sort
;; (defthmd consp-when-len-equal-for-axe-prover
;;   (implies (and (equal (len x) free)
;;                 (syntaxp (quotep free)))
;;            (equal (consp x) (< 0 free)))
;;   :hints (("Goal" :in-theory (e/d ((:i len)) ( ;len-of-cdr
;;                                               )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd axe-treep-of-cadr
  (implies (and (axe-treep tree)
                (symbolp (car tree))
                (not (equal 'quote (car tree))))
           (axe-treep (cadr tree)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd axe-treep-of-caddr
  (implies (and (axe-treep tree)
                (symbolp (car tree))
                (not (equal 'quote (car tree))))
           (axe-treep (caddr tree)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd axe-treep-of-cadddr
  (implies (and (axe-treep tree)
                (symbolp (car tree))
                (not (equal 'quote (car tree))))
           (axe-treep (cadddr tree)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthm symbolp-when-member-equal
  (implies (and (member-equal x free)
                (symbol-listp free))
           (symbolp x)))

(defthmd not-equal-of-quote-when-member-equal
  (implies (and (member-equal x free)
                (not (member-equal 'quote free)))
           (not (equal 'quote x))))

;; (defthm lookup-arg-in-result-array-when-not-get-args-not-done
;;   (implies (and (not (get-args-not-done args result-array-name result-array acc untagged-foundp)) ;all args are done
;; ;               (not (consp arg))
;;                 (member-equal arg args)
;;                 ;; (OR (CONSP ARG)
;;                 ;;     (< ARG
;;                 ;;        (ALEN1 RESULT-ARRAY-NAME RESULT-ARRAY)))
;;                 )
;;            (lookup-arg-in-result-array arg result-array-name result-array))
;;   :hints (("Goal" :in-theory (enable get-args-not-done
;;                                      lookup-arg-in-result-array))))

;; (defthm darg-listp-of-lookup-args-in-result-array
;;   (implies (and (not (get-args-not-done args result-array-name result-array acc untagged-foundp)) ;; all args are done
;;                 (result-arrayp result-array-name result-array bound)
;;                 (bounded-darg-listp args (alen1 result-array-name result-array)))
;;            (darg-listp (lookup-args-in-result-array args result-array-name result-array)))
;;   :hints (("Goal" :in-theory (e/d (GET-ARGS-NOT-DONE lookup-args-in-result-array) (dargp)))))

;; (defthm bounded-darg-listp-of-lookup-args-in-result-array
;;   (implies (and (not (get-args-not-done args2 result-array-name result-array acc untagged-foundp)) ;; all args are done
;;                 (subsetp-equal args args2)
;;                 (result-arrayp result-array-name result-array bound)
;;                 (bounded-darg-listp args (alen1 result-array-name result-array)))
;;            (bounded-darg-listp (lookup-args-in-result-array args result-array-name result-array) bound))
;;   :hints (("Goal" :in-theory (e/d (get-args-not-done lookup-args-in-result-array) (dargp)))))

;; Rules used when admitting the generated prover
(defconst *make-prover-simple-rules*
  '((:COMPOUND-RECOGNIZER AXE-TREEP-COMPOUND-RECOGNIZER)
    (:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
    (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
    (:CONGRUENCE IFF-IMPLIES-EQUAL-NOT)
    ;; (:CONGRUENCE PERM-IMPLIES-EQUAL-BOUNDED-DARG-LISTP-1)
    (:DEFINITION =)
    (:DEFINITION AXE-TREE-LISTP)
    ;;(:DEFINITION AXE-RULE-HYP-LISTP)
    (:DEFINITION ENDP)
    (:DEFINITION EQ)
    (:DEFINITION FIX)
    (:DEFINITION LENGTH)
    (:DEFINITION MAX)
    ;;    (:DEFINITION MEMBER-EQUAL) ;cases case splits?
    symbolp-when-member-equal
    not-equal-of-quote-when-member-equal
    axe-treep-of-cadr
    axe-treep-of-caddr
    axe-treep-of-cadddr
    ;;(:DEFINITION MV-NTH)
    (:DEFINITION NOT)
    (:DEFINITION NULL)
    (:DEFINITION PSEUDO-TERMP)
    ;;(:DEFINITION SYMBOL-LISTP)
    (:DEFINITION SYNP)
    (:EXECUTABLE-COUNTERPART <)
    (:EXECUTABLE-COUNTERPART =)
    (:EXECUTABLE-COUNTERPART ACL2-NUMBERP)
    (:EXECUTABLE-COUNTERPART ALL-<)
    (:EXECUTABLE-COUNTERPART AXE-TREE-LISTP)
    (:EXECUTABLE-COUNTERPART ALL-NATP)
    (:EXECUTABLE-COUNTERPART stored-axe-rule-listp)
    (:EXECUTABLE-COUNTERPART ASSOC-KEYWORD)
    (:EXECUTABLE-COUNTERPART AXE-RULE-HYP-LISTP)
    (:EXECUTABLE-COUNTERPART AXE-TREEP)
    (:EXECUTABLE-COUNTERPART BINARY-+)
    (:EXECUTABLE-COUNTERPART CAR)
    (:EXECUTABLE-COUNTERPART CDR)
    (:EXECUTABLE-COUNTERPART CONS)
    (:EXECUTABLE-COUNTERPART CONSP)
    (:EXECUTABLE-COUNTERPART EQ)
    (:EXECUTABLE-COUNTERPART EQUAL)
    (:EXECUTABLE-COUNTERPART FORCE)
    (:EXECUTABLE-COUNTERPART IF)
    (:EXECUTABLE-COUNTERPART INCREMENT-TRIES$INLINE)
    (:EXECUTABLE-COUNTERPART HIT-COUNTSP)
    (:EXECUTABLE-COUNTERPART KEYWORD-VALUE-LISTP)
    (:EXECUTABLE-COUNTERPART LEN)
    (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
    (:EXECUTABLE-COUNTERPART MV-NTH)
    (:EXECUTABLE-COUNTERPART NAT-LISTP)
    (:EXECUTABLE-COUNTERPART NATP)
    (:EXECUTABLE-COUNTERPART NOT)
    (:EXECUTABLE-COUNTERPART PSEUDO-TERM-LISTP)
    (:EXECUTABLE-COUNTERPART PSEUDO-TERMP)
    (:EXECUTABLE-COUNTERPART RATIONAL-LISTP)
    (:EXECUTABLE-COUNTERPART STRIP-CDRS)
    (:EXECUTABLE-COUNTERPART SYMBOL-ALISTP)
    (:EXECUTABLE-COUNTERPART SYMBOL-LISTP)
    (:EXECUTABLE-COUNTERPART SYMBOLP)
    (:EXECUTABLE-COUNTERPART TRIESP)
    (:EXECUTABLE-COUNTERPART TRUE-LISTP)
    (:EXECUTABLE-COUNTERPART UNARY--)
    (:EXECUTABLE-COUNTERPART ZP)
    (:forward-chaining nat-listp-forward-to-true-listp)
    (:forward-chaining nat-listp-forward-to-rational-listp)
    ;;(:FORWARD-CHAINING ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING ARRAY1P-FORWARD)
    (:FORWARD-CHAINING ARRAY1P-FORWARD-TO-<=-OF-ALEN1)
    (:FORWARD-CHAINING AXE-RULE-HYP-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING axe-tree-listp-forward-to-true-listp)
    (:forward-chaining bounded-axe-tree-listp-forward-to-axe-tree-listp)
    (:FORWARD-CHAINING BOUNDED-DAG-CONSTANT-ALISTP-FORWARD-TO-DAG-CONSTANT-ALISTP)
    (:FORWARD-CHAINING BOUNDED-DAG-PARENT-ARRAYP-FORWARD-TO-BOUNDED-DAG-PARENT-ARRAYP)
    (:FORWARD-CHAINING BOUNDED-DAG-VARIABLE-ALISTP-FORWARD-TO-DAG-VARIABLE-ALISTP)
    (:FORWARD-CHAINING BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
    (:FORWARD-CHAINING CONSP-ASSOC-EQUAL)
    (:FORWARD-CHAINING CONSP-FORWARD-TO-LEN-BOUND)
    (:FORWARD-CHAINING DAG-CONSTANT-ALISTP-FORWARD-TO-ALISTP)
    (:FORWARD-CHAINING DAG-PARENT-ARRAYP-FORWARD-TO-ARRAY1P)
    (:FORWARD-CHAINING DAG-VARIABLE-ALISTP-FORWARD-SYMBOL-ALISTP)
    (:FORWARD-CHAINING DAG-VARIABLE-ALISTP-FORWARD-TO-NAT-LISTP-OF-STRIP-CDRS)
    (:FORWARD-CHAINING EQLABLE-ALISTP-FORWARD-TO-ALISTP)
    ;;(:FORWARD-CHAINING INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP)
    (:FORWARD-CHAINING INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-ALISTP)
    (:FORWARD-CHAINING INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-SYMBOL-ALISTP)
    (:FORWARD-CHAINING KEYWORD-VALUE-LISTP-ASSOC-KEYWORD)
    (:FORWARD-CHAINING KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING MYQUOTEP-FORWARD-TO-CONSP)
    (:FORWARD-CHAINING NAT-LISTP-FORWARD-TO-INTEGER-LISTP)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-CHAINING)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-CHAINING-ANOTHER)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-TO-<=-OF-ALEN1)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-TO-NATP-ARG3)
    ;;(:FORWARD-CHAINING RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP)
    (:FORWARD-CHAINING SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
    (:FORWARD-CHAINING SYMBOL-ALISTP-FORWARD-TO-aLISTP)
; Matt K. mod, 7/15/2022: SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP is being removed,
; but its effect follows from the three I've added just below the next line.
;   (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-EQLABLE-LISTP)
    (:FORWARD-CHAINING EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP)
    (:FORWARD-CHAINING ATOM-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING WF-DAGP-FORWARD)
    (:FORWARD-CHAINING WF-DAGP-FORWARD-TO-<=-OF-LEN)
    (:LINEAR BOUND-ON-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-3)
    (:REWRITE fold-consts-in-+)
    (:REWRITE <-OF-+-OF-1-STRENGTHEN-2)
    (:REWRITE <-OF--1-WHEN-NATP)
    (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP)
    (:REWRITE ALL-<-OF-CDR)
    (:REWRITE ALL-<-OF-NIL)
    (:REWRITE ALL-<-TRANSITIVE)
    (:REWRITE ALL-<-TRANSITIVE-FREE)
    (:REWRITE ALL-<-TRANSITIVE-FREE-2)
    (:REWRITE AXE-TREE-LISTP-OF-CDR)
    (:REWRITE AXE-TREE-LISTP-OF-CDR-2)
    (:REWRITE BOUNDED-AXE-TREE-LISTP-MONO)
    (:REWRITE BOUNDED-AXE-TREE-LISTP-OF-CDR)
    (:REWRITE BOUNDED-AXE-TREE-LISTP-OF-CDR-2)
    (:REWRITE BOUNDED-AXE-TREE-LISTP-OF-CONS)
    (:REWRITE BOUNDED-AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP)
    (:rewrite bounded-darg-listp-when-not-consp)
    (:REWRITE BOUNDED-DARG-LISTP-MONOTONE)
    (:REWRITE BOUNDED-DARG-LISTP-OF-APPEND)
    (:REWRITE BOUNDED-DARG-LISTP-OF-CONS)
    (:REWRITE bounded-darg-listp-of-strip-cdrs-of-match-hyp-with-nodenum-to-assume-false)
    (:REWRITE BOUNDED-DARG-LISTP-OF-STRIP-CDRS-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<)
    (:REWRITE DARG-LISTP-OF-STRIP-CDRS-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE DARG-LISTP-WHEN-BOUNDED-DARG-LISTP)
    ;; drop some of these all-natp rules?
    (:REWRITE ALL-NATP-OF-CDR)
    (:REWRITE ALL-NATP-WHEN-NAT-LISTP)
    (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP)
    (:REWRITE NAT-listp-OF-CDR)
    (:REWRITE NAT-listP-WHEN-NOT-CONSP-CHEAP)
    (:REWRITE STORED-AXE-RULE-LISTP-OF-CDR)
    (:REWRITE stored-axe-rule-listp-of-get-rules-for-fn)
    (:REWRITE AXE-BIND-FREE-RESULT-OKAYP-REWRITE)
    (:REWRITE AXE-RULE-HYP-LISTP-OF-CDR)
    (:REWRITE AXE-RULE-HYP-LISTP-OF-STORED-RULE-HYPS)
    (:REWRITE AXE-RULE-HYPP-WHEN-AXE-BIND-FREE)
    (:REWRITE AXE-RULE-HYPP-WHEN-SIMPLE)
    (:REWRITE AXE-RULE-HYPP-WHEN-free-vars)
    (:REWRITE AXE-RULE-HYPP-WHEN-axe-binding-hyp)
    (:REWRITE AXE-TREEP-OF-CAR)
    (:rewrite axe-treep-of-car-when-bounded-axe-tree-listp)
    (:REWRITE AXE-TREEP-OF-CONS-STRONG)
    ;; (:REWRITE AXE-TREEP-OF-SUBLIS-VAR-AND-EVAL-BASIC)
    ;; (:REWRITE AXE-TREEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP)
    (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP)
    (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP)
    (:REWRITE BOUND-ON-MV-NTH-3-AND-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-ALT)
    (:REWRITE BOUNDED-AXE-TREEP-MONO)
    (:REWRITE BOUNDED-AXE-TREEP-OF-CAR)
    (:REWRITE BOUNDED-AXE-TREEP-OF-CONS)
    ;; (:REWRITE BOUNDED-AXE-TREEP-OF-SUBLIS-VAR-AND-EVAL-BASIC)
    ;; (:REWRITE BOUNDED-AXE-TREEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:REWRITE BOUNDED-AXE-TREEP-WHEN-NATP-STRONG)
    (:REWRITE BOUNDED-AXE-TREEP-WHEN-PSEUDO-TERMP)
    (:REWRITE BOUNDED-DAG-CONSTANT-ALISTP-MONOTONE)
    (:REWRITE BOUNDED-DAG-VARIABLE-ALISTP-MONOTONE)
    (:REWRITE BOUNDED-INTEGER-ALISTP-WHEN-BOUNDED-INTEGER-ALISTP)
    (:REWRITE CAR-CONS)
    (:REWRITE CDR-CONS)
    (:REWRITE COMMUTATIVITY-OF-+)
    (:REWRITE CONSP-FROM-LEN-CHEAP)
    (:REWRITE DAG-VARIABLE-ALISTP-FORWARD-TO-ALIST)
    (:REWRITE DARGP-LESS-THAN-MONO)
    (:REWRITE DARGP-LESS-THAN-OF-LIST-OF-QUOTE)
    ;; (:REWRITE DARGP-LESS-THAN-OF-MAYBE-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER-GEN)
    (:REWRITE DARGP-LESS-THAN-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-GEN)
    (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-MYQUOTEP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP)
    (:rewrite DARGP-LESS-THAN-OF-MAYBE-REPLACE-NODENUM-USING-ASSUMPTION-ARRAY)
    (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT)
    (:REWRITE EQUAL-OF-LEN-AND-0)
    (:REWRITE HIT-COUNTSP-OF-maybe-INCREMENT-HIT-COUNT)
    (:REWRITE INTEGER-LISTP-WHEN-ALL-NATP)
    (:REWRITE INTEGER-LISTP-WHEN-nat-listp)
    (:REWRITE LEN-OF-CDR)
    (:REWRITE LEN-OF-CONS)
    (:REWRITE LEN-OF-LAMBDA-FORMALS-WHEN-AXE-TREEP)
    (:REWRITE LOOKUP-EQ-BECOMES-LOOKUP-EQUAL)
    (:REWRITE MAXELEM-OF-CONS)
    ;; (:REWRITE MV-NTH-6-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:REWRITE MV-NTH-OF-CONS-safe)
    ;; (:REWRITE MYQUOTEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:REWRITE NAT-LISTP-WHEN-ALL-NATP)
    (:REWRITE NATP-OF-+-OF-1-ALT)
    (:REWRITE NATP-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:REWRITE NOT-<-OF-+-1-AND-MAXELEM)
    (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP)
    (:REWRITE PERM-OF-APPEND)
    (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE)
    (:REWRITE PSEUDO-DAG-ARRAYP-OF-MV-NTH-2-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-GEN)
    (:REWRITE PSEUDO-TERM-LISTP-OF-STORED-RULE-LHS-ARGS)
    (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-WHEN-AXE-TREEP)
    (:REWRITE PSEUDO-TERMP-OF-STORED-RULE-RHS)
    (:rewrite strip-cdrs-of-acons)
    (:REWRITE STRIP-CDRS-OF-APPEND)
    (:REWRITE STRIP-CDRS-OF-PAIRLIS$2)
    (:REWRITE SYMBOL-ALISTP-OF-acons)
    (:REWRITE SYMBOL-ALISTP-OF-APPEND)
    (:REWRITE SYMBOL-ALISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC)
    (:REWRITE SYMBOL-ALISTP-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE)
    (:REWRITE SYMBOL-ALISTP-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE SYMBOL-LISTP-OF-CDR)
    (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP)
    (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP)
    (:REWRITE SYMBOLP-OF-STORED-RULE-SYMBOL)
    (:REWRITE TRIESP-OF-INCREMENT-TRIES)
    (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP)
    (:REWRITE stored-axe-rulep-of-car)
    (:REWRITE WF-DAGP-AFTER-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP)
    (:TYPE-PRESCRIPTION posp-of-alen1)
    (:TYPE-PRESCRIPTION ALISTP)
    (:TYPE-PRESCRIPTION ALL-<)
    (:TYPE-PRESCRIPTION AXE-TREE-LISTP)
    (:TYPE-PRESCRIPTION BOUNDED-AXE-TREE-LISTP)
    (:TYPE-PRESCRIPTION ALL-CONSP)
    (:TYPE-PRESCRIPTION BOUNDED-DARG-LISTP)
    (:TYPE-PRESCRIPTION STORED-AXE-RULE-LISTP)
    (:TYPE-PRESCRIPTION ARRAY1P)
    (:TYPE-PRESCRIPTION ASSOC-KEYWORD)
    (:TYPE-PRESCRIPTION SIMPLE-PROVER-OPTIONSP)
    (:TYPE-PRESCRIPTION AXE-RULE-HYP-LISTP)
    (:TYPE-PRESCRIPTION AXE-RULE-HYPP)
    (:TYPE-PRESCRIPTION AXE-TREEP)
    (:TYPE-PRESCRIPTION BOUNDED-AXE-TREEP)
    (:TYPE-PRESCRIPTION BOUNDED-DAG-CONSTANT-ALISTP)
    (:TYPE-PRESCRIPTION BOUNDED-DAG-PARENT-ARRAYP)
    (:TYPE-PRESCRIPTION BOUNDED-DAG-VARIABLE-ALISTP)
    (:TYPE-PRESCRIPTION BOUNDED-INTEGER-ALISTP)
    (:TYPE-PRESCRIPTION DAG-CONSTANT-ALISTP)
    (:TYPE-PRESCRIPTION DAG-PARENT-ARRAYP)
    (:TYPE-PRESCRIPTION DAG-VARIABLE-ALISTP)
    (:TYPE-PRESCRIPTION DARGP-LESS-THAN)
    (:TYPE-PRESCRIPTION EQLABLE-ALISTP)
    (:TYPE-PRESCRIPTION EQUIV-ALISTP)
    (:TYPE-PRESCRIPTION HIT-COUNTSP)
    (:TYPE-PRESCRIPTION INTEGER-LISTP)
    (:TYPE-PRESCRIPTION INTERPRETED-FUNCTION-ALISTP)
    (:TYPE-PRESCRIPTION KEYWORD-VALUE-LISTP)
    (:TYPE-PRESCRIPTION LEN)
    (:TYPE-PRESCRIPTION LENGTH)
    (:TYPE-PRESCRIPTION MYQUOTEP)
    (:TYPE-PRESCRIPTION NAT-LISTP)
    (:TYPE-PRESCRIPTION NATP-OF-CAR-WHEN-NAT-LISTP-TYPE)
    (:TYPE-PRESCRIPTION NATP-OF-MAXELEM-2)
    (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-type)
    (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP)
    (:TYPE-PRESCRIPTION PSEUDO-TERMP)
    (:TYPE-PRESCRIPTION RATIONAL-LISTP)
    ;; (:TYPE-PRESCRIPTION REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:TYPE-PRESCRIPTION RULE-ALISTP)
    (:TYPE-PRESCRIPTION STRIP-CDRS)
    (:TYPE-PRESCRIPTION SYMBOL-ALISTP)
    (:TYPE-PRESCRIPTION SYMBOL-LISTP)
    (:TYPE-PRESCRIPTION TRIESP)
    (:TYPE-PRESCRIPTION TRUE-LISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC)
    (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE-type)
    (:rewrite TRUE-LISTP-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE)
    (:TYPE-PRESCRIPTION WF-DAGP)
    equivp-forward-to-symbolp
    equivp-of-car-when-equiv-listp
    (:e equivp)
    (:e equiv-listp)
    (:t equivp)
    (:t equiv-listp)
    equiv-listp-of-cdr
    equiv-listp-of-get-equivs
    subsetp-equal-of-free-vars-in-term-of-car-and-strip-cars-when-normal
    ;all-vars-in-terms-bound-in-alistp-correct
    ;all-vars-in-term-bound-in-alistp-correct
    ))

(defconst *default-axe-prover-rules*
  '(implies equal-same))

(defconst-computed-erp-and-val *default-axe-prover-rule-alists*
  (make-rule-alists (list *default-axe-prover-rules*) (w state)))

;; Union X into every element of Y
(defund union-eq-with-all (x y)
  (declare (xargs :guard (and (symbol-listp x)
                              (symbol-list-listp y))))
  (if (endp y)
      nil
    (cons (union-eq x (first y))
          (union-eq-with-all x (rest y)))))

(defthmd symbol-list-listp-of-union-eq-with-all
  (implies (and (symbol-listp x)
                (symbol-list-listp y))
           (symbol-list-listp (union-eq-with-all x y)))
  :hints (("Goal" :in-theory (enable union-eq-with-all))))

(defthmd not-member-equal-of-car-when-not-intersection-equal
  (implies (and (not (intersection-equal x y))
                (consp x))
           (not (member-equal (car x) y))))

(mutual-recursion
 (defund simple-prover-tacticp (x)
   (declare (xargs :guard t
                   :ruler-extenders :all))
   (or (eq x :rewrite)       ; rewrite all literals once
       (eq x :rewrite-top)   ; rewrite all literals once, only lits whose top nodes match rules
       (eq x :subst)         ; substitute vars
       (eq x :elim)          ; eliminate tuples
       (and (consp x) ; apply the given tactics in sequence
            (eq :seq (car x))
            (simple-prover-tactic-listp (fargs x)))
       (and (consp x)
            (eq :rep (car x)) ; repeatedly apply the given tactics in sequence, until nothing changes
            (simple-prover-tactic-listp (fargs x)))))
 (defund simple-prover-tactic-listp (x)
   (declare (xargs :guard t))
   (if (atom x)
       (null x)
     (and (simple-prover-tacticp (first x))
          (simple-prover-tactic-listp (rest x))))))

(defthm simple-prover-tactic-listp-of-cdr-when-rep
  (implies (and (equal :rep (car tactic))
                (simple-prover-tacticp tactic))
           (simple-prover-tactic-listp (cdr tactic)))
  :hints (("Goal" :in-theory (enable simple-prover-tacticp))))

(defthm simple-prover-tactic-listp-of-cdr-when-seq
  (implies (and (equal :seq (car tactic))
                (simple-prover-tacticp tactic))
           (simple-prover-tactic-listp (cdr tactic)))
  :hints (("Goal" :in-theory (enable simple-prover-tacticp))))

(defthm simple-prover-tactic-listp-of-cdr-when-simple-prover-tactic-listp
  (implies (simple-prover-tactic-listp tactics)
           (simple-prover-tactic-listp (cdr tactics)))
  :hints (("Goal" :in-theory (enable simple-prover-tactic-listp))))

;; A hint representing a single theorem instance to use.
;; Recognize <symbol> or (:instance <symbol> ... subst ...).
(defund axe-use-instancep (instance)
  (declare (xargs :guard t))
  (or (and (symbolp instance) ; theorem name with no subst
           (not (keywordp instance)) ; can't be :instance
           )
      (and (true-listp instance)
           (<= 2 (len instance))
           (eq :instance (first instance))
           (symbolp (second instance)) ; theorem name
           (symbol-doublet-listp (rest (rest instance))) ; the subst
           (pseudo-term-listp (strip-cadrs (rest (rest instance))))
           )))

(defund axe-use-instance-subst (instance)
  (declare (xargs :guard (axe-use-instancep instance)
                  :guard-hints (("Goal" :in-theory (enable axe-use-instancep)))))
  (if (consp instance)
      (rest (rest instance))
    nil))

(defthm symbol-listp-of-strip-cars-of-axe-use-instance-subst
  (implies (axe-use-instancep instance)
           (symbol-listp (strip-cars (axe-use-instance-subst instance))))
  :hints (("Goal" :in-theory (enable axe-use-instance-subst axe-use-instancep))))

(defthm pseudo-term-listp-of-strip-cadrs-of-axe-use-instance-subst
  (implies (axe-use-instancep instance)
           (pseudo-term-listp (strip-cadrs (axe-use-instance-subst instance))))
  :hints (("Goal" :in-theory (enable axe-use-instance-subst axe-use-instancep))))

(defthm doublet-listp-of-axe-use-instance-subst
  (implies (axe-use-instancep instance)
           (doublet-listp (axe-use-instance-subst instance)))
  :hints (("Goal" :in-theory (enable axe-use-instance-subst axe-use-instancep))))

(defthm alistp-of-axe-use-instance-subst
  (implies (axe-use-instancep instance)
           (alistp (axe-use-instance-subst instance)))
  :hints (("Goal" :in-theory (enable axe-use-instance-subst axe-use-instancep))))

(defthm all->=-len-of-axe-use-instance-subst
  (implies (axe-use-instancep instance)
           (all->=-len (axe-use-instance-subst instance) 2))
  :hints (("Goal" :in-theory (enable axe-use-instance-subst axe-use-instancep))))


;; A hint representing a list of theorem instances to use.
(defund axe-use-instance-listp (instances)
  (declare (xargs :guard t))
  (if (not (consp instances))
      (null instances)
    (and (axe-use-instancep (first instances))
         (axe-use-instance-listp (rest instances)))))

;; Only nil is both a use instance and a list of use instances.
(thm
 (implies (not (equal x nil))
          (not (and (axe-use-instancep x)
                    (axe-use-instance-listp x))))
 :hints (("Goal" :in-theory (enable AXE-USE-INSTANCE-LISTP
                                    axe-use-instancep))))

(defthm axe-use-instancep-of-car
  (implies (and (axe-use-instance-listp instances)
                ;; (consp instances)
                )
           (axe-use-instancep (car instances)))
  :hints (("Goal" :in-theory (enable axe-use-instance-listp))))

(defthm axe-use-instance-listp-of-cdr
  (implies (axe-use-instance-listp instances)
           (axe-use-instance-listp (cdr instances)))
  :hints (("Goal" :in-theory (enable axe-use-instance-listp))))

(defund axe-use-hintp (hint)
  (declare (xargs :guard t))
  (or (axe-use-instancep hint)
      (axe-use-instance-listp hint)))

;; Turns a single instance into a list of instances
(defund desugar-axe-use-hint (hint)
  (declare (xargs :guard (axe-use-hintp hint)))
  (if (null hint)
      hint
    (if (axe-use-instancep hint)
        (list hint)
      hint)))

(defthm axe-use-instance-listp-of-desugar-axe-use-hint
  (implies (axe-use-hintp hint)
           (axe-use-instance-listp (desugar-axe-use-hint hint)))
  :hints (("Goal" :in-theory (enable desugar-axe-use-hint axe-use-hintp axe-use-instance-listp))))

;; Returns (mv erp new-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund apply-axe-use-instances (axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc)
  (declare (xargs :guard (and (axe-use-instance-listp axe-use-instances)
                              (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbol-listp clause-vars)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :expand (AXE-USE-INSTANCE-LISTP AXE-USE-INSTANCES)
                                 :in-theory (e/d ((:d axe-use-instance-listp) AXE-USE-INSTANCEP)
                                                 (doublets-to-alist strip-cars strip-cadrs symbol-listp symbol-doublet-listp
                                                                    PSEUDO-TERMP))))))
  (if (endp axe-use-instances)
      (mv (erp-nil) new-nodenums-acc dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (b* ((axe-use-instance (first axe-use-instances)) ;; either <symbol> or (:instance <symbol> ... subst ...)
         (theorem-name (if (consp axe-use-instance) (second axe-use-instance) axe-use-instance))
         (subst-doublets (if (consp axe-use-instance) (axe-use-instance-subst axe-use-instance) nil))
         (subst-vars (strip-cars subst-doublets))
         (theorem-body (defthm-body theorem-name wrld)) ; for now at least, this can't be a definition name
         (theorem-vars (free-vars-in-term theorem-body))
         ((when (not (subsetp-equal subst-vars theorem-vars)))
          (er hard? 'apply-axe-use-instances "Axe :use instance ~x0 has vars, ~x1, not in the theorem body, ~x2." axe-use-instance (set-difference-eq subst-vars theorem-vars) theorem-body)
          (mv (erp-t) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         (new-vars (append (set-difference-eq theorem-vars subst-vars) ; vars not substituted
                           (free-vars-in-terms (strip-cadrs subst-doublets))))
         ((when (not (subsetp-eq new-vars clause-vars)))
          (er hard? 'apply-axe-use-instances "Axe :use instance ~x0 introduces vars, ~x1, not in the clause." axe-use-instance (set-difference-eq new-vars clause-vars))
          (mv (erp-t) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ;; TODO: Check arities in the subst?
         ;; Now negate the theorem-body because we assume literal nodenums false:
         (negated-instantiated-body (sublis-var-simple (doublets-to-alist subst-doublets) `(not ,theorem-body)))
         ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          ;; todo: allow using another evaluator?
          (merge-term-into-dag-array-basic negated-instantiated-body
                                           nil ; could optimize using the fact that we know this is nil and all vars are already present
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                           nil ; todo
                                           ))
         ((when erp)
          (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ((when (consp new-nodenum-or-quotep)) ; check for quotep
          (er hard? 'apply-axe-use-instances "Axe :use instance ~x0 resulted in the constant term ~x1." axe-use-instance new-nodenum-or-quotep)
          (mv (erp-t) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
      (apply-axe-use-instances (rest axe-use-instances)
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                               clause-vars
                               wrld
                               (cons new-nodenum-or-quotep new-nodenums-acc)))))

(defthmd apply-axe-use-instances-return-type
  (mv-let (erp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
    (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc)
    (implies (and (not erp)
                  (nat-listp new-nodenums-acc)
                  (all-< new-nodenums-acc dag-len)
                  (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  (axe-use-instance-listp axe-use-instances))
             (and (nat-listp new-literal-nodenums)
                  (all-< new-literal-nodenums new-dag-len)
                  (bounded-darg-listp new-literal-nodenums new-dag-len)
                  (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))))
  :hints (("Goal" :expand (axe-use-instance-listp axe-use-instances)
           :induct t
           :in-theory (e/d (apply-axe-use-instances)
                           (pseudo-termp)))))

;; ;drop?
;; (defthmd apply-axe-use-instances-bound
;;   (mv-let (erp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
;;     (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc)
;;     (declare (ignore new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
;;     (implies (and (<= new-dag-len bound)
;;                   (not erp)
;;                   (nat-listp new-nodenums-acc)
;;                   (all-< new-nodenums-acc dag-len)
;;                   (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                   (axe-use-instance-listp axe-use-instances))
;;              (bounded-darg-listp new-literal-nodenums bound)))
;;   :hints (("Goal" :use (:instance apply-axe-use-instances-return-type)
;;            :in-theory (disable apply-axe-use-instances-return-type))))

;; the dag can't get smaller
(defthmd <=-of-mv-nth-3-of-apply-axe-use-instances
  (implies (and (not (mv-nth 0 (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc))) ; no error
                (nat-listp new-nodenums-acc)
                (all-< new-nodenums-acc dag-len)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (axe-use-instance-listp axe-use-instances))
           (<= dag-len (mv-nth 3 (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (apply-axe-use-instances) (pseudo-termp)))))

;; (defthmd integerp-mv-nth-3-of-apply-axe-use-instances
;;   (implies (integerp dag-len)
;;            (integerp (mv-nth 3 (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc))))
;;   :hints (("Goal" :in-theory (e/d (apply-axe-use-instances integerp-when-natp) (pseudo-termp
;;                                                                                 perm-implies-equal-subsetp-equal-1 ; why?
;;                                                                                 )))))

(defthmd natp-mv-nth-3-of-apply-axe-use-instances
  (implies (natp dag-len)
           (natp (mv-nth 3 (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist clause-vars wrld new-nodenums-acc))))
  :hints (("Goal" :in-theory (e/d (apply-axe-use-instances)
                                  (pseudo-termp
                                   perm-implies-equal-subsetp-equal-1 ; why?
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defund some-rule-matches-nodep (stored-rules dargs dag-array dag-len)
;;   (declare (xargs :guard  (and (true-listp stored-rules)
;;                                (all-stored-axe-rulep stored-rules)
;;                                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
;;                                (bounded-darg-listp dargs dag-len))))
;;   (if (endp stored-rules)
;;       nil ; no rule matched
;;     (let* ((stored-rule (first stored-rules))
;;            (res (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule) dargs dag-array dag-len)))
;;       (if (eq :fail res)
;;           ;; keep looking:
;;           (some-rule-matches-nodep (rest stored-rules) dargs dag-array dag-len)
;;         ;; The rule matched (but of course we don't know whether its hyps will
;;         ;; be relieved when we get to that):
;;         t))))

;; ;; Determines whether some rule from the RULE-ALIST matches the top expression
;; ;; in the literal at NODENNUM (except we strip a not if needed, to get to the
;; ;; interesting part of the literal).  Just a heuristic.
;; (defund literal-matches-some-rulep (nodenum dag-array dag-len rule-alist)
;;   (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
;;                               (natp nodenum)
;;                               (< nodenum dag-len)
;;                               (rule-alistp rule-alist))))
;;   (b* (;; Try to extract the function symbol and args for the top node (stripping a not if present):
;;        ((mv fun-callp fn dargs)
;;         (let ((expr (aref1 'dag-array dag-array nodenum)))
;;           (if (or (variablep expr)
;;                   (quotep expr))
;;               (mv nil nil nil) ; no rule matches a constant or variable
;;             ;; it's a function call, but we might need to strip a not:
;;             (if (and (eq 'not (ffn-symb expr))
;;                      (consp (dargs expr)) ; for the guard proof
;;                      (not (consp (darg1 expr))) ; ensures it's a nodenum
;;                      )
;;                 ;; Strip the not:
;;                 (let* ((expr (aref1 'dag-array dag-array (darg1 expr))))
;;                   (if (or (variablep expr)
;;                           (quotep expr))
;;                       (mv nil nil nil) ; no rule matches a constant or variable
;;                     (mv t (ffn-symb expr) (dargs expr))))
;;               ;; not a call of not:
;;               (mv t (ffn-symb expr) (dargs expr))))))
;;        ((when (not fun-callp)) nil)
;;        ;; it's a function call:
;;        (stored-rules (get-rules-for-fn fn rule-alist)))
;;     (some-rule-matches-nodep stored-rules dargs dag-array dag-len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-prover-simple-fn (suffix ;; gets added to generated names
                              evaluator-suffix
                              syntaxp-evaluator-suffix
                              bind-free-evaluator-suffix
                              default-global-rules)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-suffix)
                              (symbolp syntaxp-evaluator-suffix)
                              (symbolp bind-free-evaluator-suffix)
                              ;; default-global-rules can be any form (untranslated)
                              )))
  (let* ((evaluator-base-name (pack$ 'axe-evaluator- evaluator-suffix))
         (eval-axe-syntaxp-expr-fn (pack$ 'eval-axe-syntaxp-expr- syntaxp-evaluator-suffix)) ; keep in sync with make-axe-syntaxp-evaluator.lisp
         (eval-axe-bind-free-function-application-fn (pack$ 'eval-axe-bind-free-function-application- bind-free-evaluator-suffix)) ; keep in sync with make-axe-bind-free-evaluator.lisp
         (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args))
         (sublis-var-and-eval-name (pack$ 'sublis-var-and-eval- suffix)) ; keep in sync with the name generated by make-sublis-var-and-eval-simple
         (subcor-var-and-eval-name (pack$ 'subcor-var-and-eval- suffix)) ; keep in sync with the name generated by make-subcor-var-and-eval-simple
         ;; (instantiate-hyp-name (pack$ 'instantiate-hyp- suffix)) ; keep in sync with the name generated by make-instantiation-code-simple
         (instantiate-hyp-free-vars-name (pack$ 'instantiate-hyp- suffix '-free-vars)) ; keep in sync with the name generated by make-instantiation-code-simple-free-vars
         (instantiate-hyp-no-free-vars-name (pack$ 'instantiate-hyp- suffix '-no-free-vars2)) ; keep in sync with the name generated by make-instantiation-code-simple-no-free-vars2
         ;; functions in the main mutual recursion:
         ;; TODO: Should these names say, e.g., "prover-basic" instead of "basic-prover"?
         (relieve-free-var-hyp-and-all-others-name (pack$ 'relieve-free-var-hyp-and-all-others-for- suffix '-prover))
         (relieve-rule-hyps-name (pack$ 'relieve-rule-hyps-for- suffix '-prover))
         (try-to-apply-rules-name (pack$ 'try-to-apply-rules-for- suffix '-prover))
         (simplify-if-tree-name (pack$ 'simplify-if-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-boolif-tree-name (pack$ 'simplify-boolif-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-fun-call-name (pack$ 'simplify-fun-call-and-add-to-dag-for- suffix '-prover))
         (simplify-tree-name (pack$ 'simplify-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-trees-name (pack$ 'simplify-trees-and-add-to-dag-for- suffix '-prover))
         (rewrite-nodes-name (pack$ 'rewrite-nodes-for- suffix '-prover))
         (rewrite-single-node-name (pack$ 'rewrite-single-node-for- suffix '-prover))
         (rewrite-literal-name (pack$ 'rewrite-literal-for- suffix '-prover))
         (rewrite-literals-name (pack$ 'rewrite-literals-for- suffix '-prover))
         (rewrite-clause-name (pack$ 'rewrite-clause-for- suffix '-prover))
         (apply-tactic-name (pack$ 'apply-tactic-for- suffix '-prover))
         (apply-rep-tactic-name (pack$ 'apply-rep-tactic-for- suffix '-prover))
         (apply-tactics-name (pack$ 'apply-tactics-for- suffix '-prover))
         ;(rewrite-subst-and-elim-with-rule-alist-name (pack$ 'rewrite-subst-and-elim-with-rule-alist-for- suffix '-prover))
         (apply-tactic-for-rule-alists-name (pack$ 'apply-tactics-for-rule-alists-for- suffix '-prover))
         (prove-case-name (pack$ 'prove-case-with- suffix '-prover))
         (prove-disjunction-name (pack$ 'prove-disjunction-with- suffix '-prover))
         (prove-true-case-name (pack$ 'prove-true-case-with- suffix '-prover))
         (prove-false-case-name (pack$ 'prove-false-case-with- suffix '-prover))
         (prove-or-split-case-name (pack$ 'prove-or-split-case-with- suffix '-prover))
         ;; (prove-dag-name (pack$ 'prove-dag-with- suffix '-prover))
         (prove-clause-name (pack$ 'prove-clause-with- suffix '-prover))
         (prove-implication-name (pack$ 'prove-implication-with- suffix '-prover)) ;a macro
         (prove-implication-fn-name (pack$ 'prove-implication-with- suffix '-prover-fn))
         (prove-dag-implication-name (pack$ 'prove-dag-implication-with- suffix '-prover))
         (clause-processor-name (pack$ 'prover- suffix '-clause-processor))

         ;; Keep these in sync with the formals of each function:

         (call-of-relieve-free-var-hyp-and-all-others `(,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false-to-walk-down1
                                                                                                  nodenums-to-assume-false-to-walk-down2
                                                                                                  hyp hyp-num other-hyps alist rule-symbol
                                                                                                  dag-array dag-len dag-parent-array
                                                                                                  dag-constant-alist dag-variable-alist
                                                                                                  equiv-alist rule-alist
                                                                                                  nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print
                                                                                                  hit-counts tries interpreted-function-alist
                                                                                                  monitored-symbols
                                                                                                  embedded-dag-depth case-designator
                                                                                                  prover-depth options count))
         (call-of-relieve-rule-hyps `(,relieve-rule-hyps-name hyps hyp-num alist rule-symbol
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              equiv-alist rule-alist
                                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print
                                                              hit-counts tries interpreted-function-alist
                                                              monitored-symbols
                                                              embedded-dag-depth case-designator
                                                              prover-depth options count))

         (call-of-try-to-apply-rules `(,try-to-apply-rules-name stored-rules rule-alist args-to-match
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                equiv-alist print
                                                                hit-counts tries interpreted-function-alist
                                                                monitored-symbols
                                                                embedded-dag-depth case-designator
                                                                prover-depth options count))
         (call-of-simplify-if-tree `(,simplify-if-tree-name tree
                                                            equiv dag-array dag-len dag-parent-array
                                                            dag-constant-alist dag-variable-alist
                                                            rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                            equiv-alist print
                                                            hit-counts tries interpreted-function-alist
                                                            monitored-symbols
                                                            embedded-dag-depth case-designator
                                                            prover-depth options count))
         (call-of-simplify-boolif-tree `(,simplify-boolif-tree-name tree
                                                            equiv dag-array dag-len dag-parent-array
                                                            dag-constant-alist dag-variable-alist
                                                            rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                            equiv-alist print
                                                            hit-counts tries interpreted-function-alist
                                                            monitored-symbols
                                                            embedded-dag-depth case-designator
                                                            prover-depth options count))
         (call-of-simplify-fun-call `(,simplify-fun-call-name fn args
                                                              equiv dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                              equiv-alist print
                                                              hit-counts tries interpreted-function-alist
                                                              monitored-symbols
                                                              embedded-dag-depth case-designator
                                                              prover-depth options count))
         (call-of-simplify-tree `(,simplify-tree-name tree
                                                      equiv dag-array dag-len dag-parent-array
                                                      dag-constant-alist dag-variable-alist
                                                      rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                      equiv-alist print
                                                      hit-counts tries interpreted-function-alist
                                                      monitored-symbols
                                                      embedded-dag-depth case-designator
                                                      prover-depth options count))

         (call-of-simplify-trees `(,simplify-trees-name trees equivs
                                                        dag-array dag-len dag-parent-array
                                                        dag-constant-alist dag-variable-alist
                                                        rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                        equiv-alist print
                                                        hit-counts tries interpreted-function-alist
                                                        monitored-symbols
                                                        embedded-dag-depth case-designator
                                                        prover-depth options count))
         )

    `(progn
       (encapsulate ()
         (local (include-book "kestrel/lists-light/nth" :dir :system))
         (local (include-book "kestrel/lists-light/remove-equal" :dir :system))
         (local (include-book "kestrel/lists-light/len" :dir :system))
         (local (include-book "kestrel/lists-light/reverse" :dir :system))
         (local (include-book "kestrel/lists-light/last" :dir :system))
         (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
         (local (include-book "kestrel/lists-light/take" :dir :system))
         (local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
         (local (include-book "kestrel/lists-light/cons" :dir :system)) ; for true-listp-of-cons
         (local (include-book "kestrel/lists-light/intersection-equal" :dir :system)) ;for intersection-equal-of-cons-arg2-iff
         (local (include-book "kestrel/lists-light/member-equal" :dir :system)) ; for member-equal-of-nth-same
         (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system)) ;for SUBSETP-EQUAL-OF-CDR-ARG1 and SUBSETP-EQUAL-SELF
         (local (include-book "kestrel/lists-light/cdr" :dir :system)) ; for cdr-iff
         (local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
         (local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
         (local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
         (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
         (local (include-book "kestrel/arithmetic-light/natp" :dir :system))
         (local (include-book "kestrel/arithmetic-light/types" :dir :system))
         (local (include-book "kestrel/utilities/acl2-count" :dir :system))
         (local (include-book "kestrel/utilities/get-cpu-time" :dir :system))
         (local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
         (local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
         (local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system)) ; reduce?
         (local (include-book "kestrel/utilities/mv-nth" :dir :system))

         (set-inhibit-warnings "double-rewrite") ; todo: think about these

         ;;(local (in-theory (disable CADR-BECOMES-NTH-OF-1))) ;need better acl2-count rules about nth (maybe when we know the length...)

         ;;for speed:
         (local (in-theory (disable
                             weak-dagp-aux
                             ;;consp-from-len-cheap
                             default-car
                             <-of-nth-and-alen1 ;todo
                             dag-exprp
                             ;;list::nth-with-large-index
                             ;;list::nth-with-large-index-2
                             nat-listp
                             rational-listp
                             ;;AXE-TREE-LISTP ;try
                             (:FORWARD-CHAINING ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP)
                             (:FORWARD-CHAINING INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP)
                             (:FORWARD-CHAINING NAT-LISTP-FORWARD-TO-INTEGER-LISTP)
                             (:FORWARD-CHAINING RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP)
                             member-equal
;all-natp-when-not-consp
                             all-<-when-not-consp
                             darg-listp-when-not-consp
                             acl2-count ;yuck
                             SYMBOL-ALISTP ;move
                             SYMBOL-LISTP  ; prevent inductions
                             dag-function-call-exprp-redef
;axe-treep
                             axe-treep-of-cadr axe-treep-of-caddr axe-treep-of-cadddr
                             state-p
                             alistp
                             mv-nth)))

         (local (in-theory (enable natp-of-+-of-1-alt
                                   natp-of-car-when-bounded-darg-listp-gen
                                   nat-listp-forward-to-true-listp
                                   nat-listp-forward-to-rational-listp
                                   symbol-list-listp-of-union-eq-with-all
                                   apply-axe-use-instances-return-type
;apply-axe-use-instances-bound
                                   <=-of-mv-nth-3-of-apply-axe-use-instances
                                   natp-mv-nth-3-of-apply-axe-use-instances)))

         ;; Make versions of sublis-var-and-eval and subcor-var-and-eval:
         (make-sublis-var-and-eval-simple ,suffix ,evaluator-base-name)
         (make-subcor-var-and-eval-simple ,suffix ,evaluator-base-name)

         ;; Make versions of instantiate-hyp, etc.:
         ;; (make-instantiation-code-simple ,suffix ,evaluator-base-name)
         (make-instantiation-code-simple-free-vars ,suffix ,evaluator-base-name)
         (make-instantiation-code-simple-no-free-vars2 ,suffix ,evaluator-base-name)

         ;;(in-theory (disable car-becomes-nth-of-0)) ;move to arrays-axe

         ;;
         ;; The main mutual recursion for the rewriting tactics:
         ;;

         ;; The PROVER-DEPTH argument ensures that multiple simultaneous result arrays
         ;; don't have the same name.  It also indicates whether we can change existing
         ;; nodes (depth 0) or not (any other depth).

         (mutual-recursion

           ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           ;; Looks through the nodenums-to-assume-false-to-walk-down, trying to find a known fact that can be used to
           ;; instantiate the free vars in HYP.  If found, extends the alist to bind those free vars and then tries to
           ;; relieve all the OTHER-HYPS.
           (defund ,relieve-free-var-hyp-and-all-others-name (nodenums-to-assume-false-to-walk-down1 ; these are kept separare to avoid an expensive append
                                                              nodenums-to-assume-false-to-walk-down2
                                                              hyp ;partly instantiated
                                                              hyp-num
                                                              other-hyps
                                                              alist
                                                              rule-symbol
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              equiv-alist rule-alist
                                                              nodenums-to-assume-false1 ;we keep the whole list as well as walking down it
                                                              nodenums-to-assume-false2 ;we keep the whole list as well as walking down it
                                                              assumption-array assumption-array-num-valid-nodes
                                                              print
                                                              hit-counts tries interpreted-function-alist monitored-symbols
                                                              embedded-dag-depth ;used for the renaming-array-for-merge-embedded-dag
                                                              case-designator prover-depth options count)
             (declare (xargs
                        :verify-guards nil ; done below
                        :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                    (symbol-alistp alist)
                                    (bounded-darg-listp (strip-cdrs alist) dag-len)
                                    (nat-listp nodenums-to-assume-false-to-walk-down1)
                                    (all-< nodenums-to-assume-false-to-walk-down1 dag-len)
                                    (nat-listp nodenums-to-assume-false-to-walk-down2)
                                    (all-< nodenums-to-assume-false-to-walk-down2 dag-len)
                                    (axe-treep hyp)
                                    (consp hyp) ;; hyp cannot be a var
                                    (not (eq 'quote (ffn-symb hyp))) ;; hyp cannot be a quotep
                                    (natp hyp-num)
                                    (axe-rule-hyp-listp other-hyps)
                                    (alist-suitable-for-hyp-tree-and-hypsp alist hyp other-hyps)
                                    (symbolp rule-symbol)
                                    (equiv-alistp equiv-alist)
                                    (rule-alistp rule-alist)
                                    (nat-listp nodenums-to-assume-false1)
                                    (all-< nodenums-to-assume-false1 dag-len)
                                    (nat-listp nodenums-to-assume-false2)
                                    (all-< nodenums-to-assume-false2 dag-len)
                                    (assumption-arrayp 'assumption-array assumption-array)
                                    (natp assumption-array-num-valid-nodes)
                                    (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                    ;; print
                                    (hit-countsp hit-counts)
                                    (triesp tries)
                                    (interpreted-function-alistp interpreted-function-alist)
                                    (symbol-listp monitored-symbols)
                                    (natp embedded-dag-depth) ;can we just use the prover depth?
                                    (stringp case-designator)
                                    (natp prover-depth)
                                    (simple-prover-optionsp options) ;; TODO: Not currently used.  Disallow :no-stp?
                                    )
                        :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (or (and (endp nodenums-to-assume-false-to-walk-down1)
                          (endp nodenums-to-assume-false-to-walk-down2))
                     (zp-fast count))
                 ;;failed to relieve the hyps:
                 (mv (erp-nil) ;we could return an error of :count-exceeded here if (zp-fast count), but that might be slower
                     nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (b* (;; Decide which list to take from:
                    ((mv nodenum-to-assume-false nodenums-to-assume-false-to-walk-down1 nodenums-to-assume-false-to-walk-down2)
                     (if (consp nodenums-to-assume-false-to-walk-down1)
                         ;; take from list1:
                         (mv (first nodenums-to-assume-false-to-walk-down1) (rest nodenums-to-assume-false-to-walk-down1) nodenums-to-assume-false-to-walk-down2)
                       ;; take from list2:
                       (mv (first nodenums-to-assume-false-to-walk-down2) nodenums-to-assume-false-to-walk-down1 (rest nodenums-to-assume-false-to-walk-down2))))
                    (fail-or-alist-for-free-vars
                      ;; TODO: Make 2 versions of this, according to whether HYP is a call of NOT:
                      (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len) ;fixme this could extend the alist
                      ))
                 (if (not (eq :fail fail-or-alist-for-free-vars))
                     (b* ((new-alist (append fail-or-alist-for-free-vars alist)) ;skip this append?
                          ;; Try to relieve all the other-hyps using the new-alist:
                          ((mv erp other-hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                           (,relieve-rule-hyps-name other-hyps
                                                    (+ 1 hyp-num)
                                                    new-alist
                                                    rule-symbol
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    equiv-alist rule-alist
                                                    nodenums-to-assume-false1 nodenums-to-assume-false2
                                                    assumption-array assumption-array-num-valid-nodes
                                                    print hit-counts tries interpreted-function-alist
                                                    monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                          ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                       (if other-hyps-relievedp
                           ;; This hyp, and all the other ones, were relieved:
                           (mv (erp-nil) t extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         ;;this nodenum-to-assume-false matches, but we couldn't relieve the rest of the hyps:
                         (,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false-to-walk-down1 nodenums-to-assume-false-to-walk-down2
                                                                    hyp hyp-num other-hyps
                                                                    alist ;the original alist
                                                                    rule-symbol
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                    equiv-alist rule-alist
                                                                    nodenums-to-assume-false1 nodenums-to-assume-false2
                                                                    assumption-array assumption-array-num-valid-nodes
                                                                    print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))))
                   ;;this nodenum-to-assume-false didn't match:
                   (,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false-to-walk-down1 nodenums-to-assume-false-to-walk-down2
                                                              hyp hyp-num other-hyps
                                                              alist
                                                              rule-symbol
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              equiv-alist rule-alist
                                                              nodenums-to-assume-false1 nodenums-to-assume-false2
                                                              assumption-array assumption-array-num-valid-nodes
                                                              print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))))))

           ;; ;print something like this:?
           ;;                               (prog2$
           ;;                                (and (member-eq rule-symbol monitored-symbols)
           ;;                                     (progn$ (cw "(Failed.  Reason: Failed to match free var in hyp (number ~x0): ~x1 for ~x2." hyp-num hyp rule-symbol)
           ;;                                             (cw "(Assumptions (to assume false):~%")
           ;; ;this can be big (print it just once per literal?)
           ;;                                             (if (eq print :verbose) (print-dag-array-node-and-supporters-lst nodenums-to-assume-false 'dag-array dag-array) (cw ":elided"))
           ;;                                             ;;fixme print the  part of the dag array that supports the hyp??
           ;;                                             (cw ")~%Alist: ~x0~%)~%" alist)))


           ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
           ;; alist maps vars to nodenums or quoteps (not terms?)
           (defund ,relieve-rule-hyps-name (hyps ;the hyps of the rule (not yet instantiated ; trees over vars and quoteps)
                                            hyp-num
                                            alist ;binds variables to nodenums or quoteps
                                            rule-symbol
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            equiv-alist rule-alist
                                            nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                            print hit-counts tries interpreted-function-alist
                                            monitored-symbols embedded-dag-depth
                                            case-designator
                                            prover-depth options count)
             (declare (xargs :guard (and (axe-rule-hyp-listp hyps)
                                         (natp hyp-num)
                                         (symbol-alistp alist)
                                         (alist-suitable-for-hypsp alist hyps)
                                         (symbolp rule-symbol)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (bounded-darg-listp (strip-cdrs alist) dag-len)
                                         (equiv-alistp equiv-alist)
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (if (endp hyps)
                   ;; all hyps relieved:
                   (mv (erp-nil) t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 (b* ((hyp (first hyps)) ;known to be a non-lambda function call
                      (fn (ffn-symb hyp))
                      (- (and (member-eq print '(:verbose! :verbose)) (cw " Relieving hyp: ~x0 with alist ~x1.~%" hyp alist))))
                   (if (eq :axe-syntaxp fn)
                       (let* ((syntaxp-expr (cdr hyp)) ;; strip off the :AXE-SYNTAXP; dag-array formals have been removed from the calls in this
                              (result (and ;(all-vars-in-term-bound-in-alistp syntaxp-expr alist) ; TODO: remove this check, since it should be guaranteed statically!
                                        (,eval-axe-syntaxp-expr-fn syntaxp-expr alist dag-array))))
                         (if result
                             (,relieve-rule-hyps-name
                              (rest hyps) (+ 1 hyp-num) alist rule-symbol ;alist may have been extended by a hyp with free vars
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                              equiv-alist rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                              prover-depth options (+ -1 count))
                           (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                        (cw "(Failed. Reason: Failed to relieve axe-syntaxp hyp ~x0 for ~x1.)~%" syntaxp-expr rule-symbol))
                                   (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))
                     (if (eq :axe-bind-free fn)
                         (let* ((bind-free-expr (cadr hyp)) ;; strip off the :AXE-BIND-FREE
                                (result (and ;(all-vars-in-terms-bound-in-alistp (fargs bind-free-expr) alist) ; TODO: remove this check, since it should be guaranteed statically!
                                          (,eval-axe-bind-free-function-application-fn (ffn-symb bind-free-expr) (fargs bind-free-expr) alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                                          )))
                           (if result ;; nil to indicate failure, or an alist whose keys should be exactly (cddr hyp)
                               (let ((vars-to-bind (cddr hyp)))
                                 (if (not (axe-bind-free-result-okayp result vars-to-bind dag-len))
                                     (mv (erp-t)
                                         (er hard? ',relieve-rule-hyps-name "Bind free hyp ~x0 for rule ~x1 returned ~x2, but this is not a well-formed alist that binds ~x3." hyp rule-symbol result vars-to-bind)
                                         alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                   ;; this hyp counts as relieved:
                                   (,relieve-rule-hyps-name (rest hyps) (+ 1 hyp-num)
                                                            (append result alist) ;; guaranteed to be disjoint given the analysis done when the rule was made and the call of axe-bind-free-result-okayp above
                                                            rule-symbol dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            equiv-alist rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                            prover-depth options (+ -1 count))))
                             ;; failed to relieve the axe-bind-free hyp:
                             (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                          (cw "(Failed.  Reason: Failed to relieve axe-bind-free hyp ~x0 for ~x1.)~%" bind-free-expr rule-symbol))
                                     (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))
                       (if (eq :free-vars fn)
                           ;; HYP has free vars (also, any work-hard has been dropped):
                           ;; TODO: avoid instantiating it (just do the matching using the alist)?
                           (b* ((instantiated-hyp (,instantiate-hyp-free-vars-name (cdr hyp) ;strip the :free-vars
                                                                                   alist interpreted-function-alist))
                                ((when (eq 'quote (ffn-symb instantiated-hyp))) ;todo: this should not happen since there are free vars (unless perhaps we give special treatment to IFs)
                                 (er hard? ',relieve-rule-hyps-name "ERROR: Instantiating a hyp with free vars produced a constant.")
                                 (mv :error-instantiating nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                             ;; INSTANTIATED-HYP is now a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars.
                             ;; ALIST doesn't bind all the variables in the HYP, so we'll search for free variable matches in and NODENUMS-TO-ASSUME-FALSE1 NODENUMS-TO-ASSUME-FALSE2:
                             (,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false1 nodenums-to-assume-false2
                                                                        instantiated-hyp hyp-num
                                                                        (rest hyps)
                                                                        alist rule-symbol
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                        equiv-alist rule-alist
                                                                        nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print
                                                                        hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                         (if (eq :axe-binding-hyp fn) ; (:axe-binding-hyp <var> . <expr>)
                             (b* ((var (cadr hyp))
                                  (expr (cddr hyp))
                                  ;; First, we substitute for all the free vars in expr:
                                  (instantiated-expr (,instantiate-hyp-no-free-vars-name expr alist interpreted-function-alist))
                                  ;; Now instantiated-hyp is an axe-tree with leaves that are quoteps and nodenums.
                                  ;; TODO: Consider adding a special case here to check whether the hyp is a constant (may be very common)?
                                  ;; Now rewrite the instantianted expr:
                                  (old-try-count tries)
                                  ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                   (,simplify-tree-name instantiated-expr
                                                        'equal ; can't use iff
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        rule-alist
                                                        nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print
                                                        hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                        prover-depth options (+ -1 count)))
                                  ((when erp) (mv erp
                                                  nil ;hyps-relievedp
                                                  nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                                  (- (and old-try-count
                                          (let ((try-diff (subtract-tries tries old-try-count)))
                                            (and (< 100 try-diff) (cw " (~x0 tries used ~x1:~x2.)~%" try-diff rule-symbol hyp-num))))))
                               ;; A binding hyp always counts as relieved:
                               (,relieve-rule-hyps-name (rest hyps) (+ 1 hyp-num)
                                                        (acons var new-nodenum-or-quotep alist) ; bind the var to the rewritten term
                                                        rule-symbol
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        equiv-alist rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                           ;; HYP is normal:
                           ;; TODO: Strip a work-hard?
                           ;; First, we substitute in for all the vars in HYP:
                           (b* ((instantiated-hyp (,instantiate-hyp-no-free-vars-name hyp alist interpreted-function-alist))
                                ;; todo: consider checking for quotep here
                                ;; INSTANTIATED-HYP is now a tree with leaves that are quoteps and nodenums (from vars already bound).
                                ;; No more free vars remain in the hyp, so we try to relieve the fully instantiated hyp:
                                (old-try-count tries)
                                ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                 ;;try to relieve through rewriting (this tests atom hyps for symbolp even though i think that's impossible - but should be rare):
                                 (,simplify-tree-name instantiated-hyp
                                                      'iff
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      rule-alist
                                                      nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print
                                                      hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                      prover-depth options (+ -1 count)))
                                ((when erp) (mv erp
                                                nil ;hyps-relievedp
                                                nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                                (try-diff (and old-try-count (subtract-tries tries old-try-count))))
                             (if (consp new-nodenum-or-quotep) ;tests for quotep
                                 (if (unquote new-nodenum-or-quotep) ;hyp rewrote to a non-nil constant:
                                     (prog2$ (and old-try-count (< 100 try-diff) (cw "(~x0 tries used(p) ~x1:~x2)~%" try-diff rule-symbol hyp-num))
                                             (,relieve-rule-hyps-name
                                              (rest hyps) (+ 1 hyp-num) alist rule-symbol ;alist may have been extended by a hyp with free vars
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              equiv-alist rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                                   ;;hyp rewrote to *nil* :
                                   (progn$
                                     (and old-try-count print (< 100 try-diff) (cw "(~x1 tries wasted(p) ~x0:~x2 (rewrote to NIL))~%" rule-symbol try-diff hyp-num))
                                     (and (member-eq rule-symbol monitored-symbols)
                                          (cw "(Failed to relieve hyp ~x0 for ~x1.~% Reason: Rewrote to nil.~%Alist: ~x2.~%Assumptions1 (to assume false):~%~x3~%Assumptions2 (to assume false):~%~x4~%DAG:~x5)~%"
                                              hyp
                                              rule-symbol
                                              alist
                                              nodenums-to-assume-false1
                                              nodenums-to-assume-false2
                                              :elided ;;todo: print dag-array? ;could print only the part of the dag below the maxnodenum in alist? can this stack overflow?
                                              ))
                                     (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                               ;;hyp didn't rewrite to a constant:
                               (prog2$
                                 (and old-try-count print (< 100 try-diff) (cw "(~x1 tries wasted(p): ~x0:~x2 (non-constant result))~%" rule-symbol try-diff hyp-num))
                                 ;; Give up:
                                 (prog2$ ;todo: improve this printing?
                                   (and (member-eq rule-symbol monitored-symbols)
                                        (progn$ (cw "(Failed to relieve hyp ~x0, namely, ~x1, for ~x2. " hyp-num hyp rule-symbol)
                                                (cw "Reason: Rewrote to:~%")
                                                (print-dag-array-node-and-supporters 'dag-array dag-array new-nodenum-or-quotep)
                                                (cw "Alist: ~x0.~%(Assumptions (to assume false 1):~%" alist)
                                                (print-dag-array-node-and-supporters-lst nodenums-to-assume-false1 'dag-array dag-array)
                                                (cw ")~%")
                                                (cw "(Assumptions (to assume false 2):~%")
                                                (print-dag-array-node-and-supporters-lst nodenums-to-assume-false2 'dag-array dag-array)
                                                (cw "))~%") ;;(cw "Alist: ~x0.~%Assumptions (to assume false): ~x1~%DAG:~x2)~%" alist nodenums-to-assume-false dag-array)
                                                ))
                                   (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))))))))))))

           ;; returns (mv erp new-rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
           ;; where if new-rhs-or-nil is nil, no rule applied. otherwise, new-rhs-or-nil is a tree with nodenums and quoteps at the leaves (what about free vars?  should free vars in the RHS be an error?)
           (defund ,try-to-apply-rules-name (stored-rules
                                             rule-alist
                                             args-to-match ;a list of nodenums and/or quoteps
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                             equiv-alist print hit-counts tries
                                             interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
             (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (stored-axe-rule-listp stored-rules)
                                         (rule-alistp rule-alist)
                                         (bounded-darg-listp args-to-match dag-len)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (or (endp stored-rules) ;no rule fired:
                     (zp-fast count)
                     )
                 (mv (erp-nil) ;we could return an error of :count-exceeded here if (zp-fast count), but that might be slower
                     nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (let* ((stored-rule (first stored-rules))
                      (tries (increment-tries tries))
                      ;;binds variables to nodenums or quoteps:
                      (alist-or-fail (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule)
                                                                     args-to-match
                                                                     dag-array
                                                                     dag-len)))
                 (if (eq :fail alist-or-fail)
                     ;; the rule didn't match, so try the next rule:
                     (,try-to-apply-rules-name (rest stored-rules) rule-alist args-to-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                               equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                   ;; The rule matched. now try to relieve its hyps:
                   (b* ((- (and (member-eq print '(:verbose :verbose!))
                                (cw "(Trying: ~x0. Alist: ~x1~%"
                                    (stored-rule-symbol stored-rule)
                                    (reverse alist-or-fail) ;nicer to read if reversed
                                    )))
                        (hyps (stored-rule-hyps stored-rule))
                        ;;binding free vars might extend the alist:
                        ;;the dag may have been extended:
                        ((mv erp hyps-relievedp alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         (if hyps
                             (,relieve-rule-hyps-name
                              hyps 1 alist-or-fail
                              (stored-rule-symbol stored-rule)
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                              equiv-alist rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                           ;;if there are no hyps, don't even bother: BOZO inefficient?:
;perhaps if we failed to relieve the hyp we should use the old value of hit-counts and/or tries?
                           (mv (erp-nil) t alist-or-fail dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                     (if hyps-relievedp
                         ;; instantiate the RHS:
                         ;; todo: could use a faster version where we know there are no free vars (we know that all vars in RHS are already bound in ALIST):
                         (let ((rhs (,sublis-var-and-eval-name alist (stored-rule-rhs stored-rule) interpreted-function-alist)))
                           (prog2$ (and (member-eq print '(:verbose! :verbose))
                                        (cw "Rewriting with ~x0. RHS: ~x1.)~%"
                                            (stored-rule-symbol stored-rule)
                                            rhs))
                                   (mv (erp-nil)
                                       rhs
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       (maybe-increment-hit-count (stored-rule-symbol stored-rule) hit-counts)
                                       tries)))
                       ;;failed to relieve the hyps, so try the next rule
                       (prog2$ (and (member-eq print '(:verbose! :verbose))
                                    (cw "Failed to apply rule ~x0.)~%" (stored-rule-symbol stored-rule)))
                               (,try-to-apply-rules-name
                                (rest stored-rules)
                                rule-alist args-to-match
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes  equiv-alist print
                                hit-counts ;(cons (cons :fail (rule-symbol rule)) hit-counts)
                                tries
                                interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))))

           ;;  ;;new!
           ;;  ;;this also simplifies as it goes!
           ;; ;ffixme check that interpreted functions are consistent?!
           ;; ;can this add ifns to the alist?
           ;;  ;;returns (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
           ;;  (defund merge-embedded-dag-into-dag-for-basic-prover (rev-dag
           ;;                                                     renaming-array-name
           ;;                                                     renaming-array2 ;associates nodenums in the embedded dag with the nodenums (or quoteps) they rewrote to in the main dag
           ;;                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                     embedded-dag-var-alist ;associates vars in the embedded dag with their nodenums (or quoteps) in the main dag
           ;;                                                     rule-alist
           ;;                                                     nodenums-to-assume-false ;equality-assumptions
           ;;                                                     equiv-alist
           ;;                                                     print
           ;;                                                     hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count state)
           ;;    (declare (xargs :stobjs state
           ;;                    :guard (and (weak-dagp-aux rev-dag)
           ;;                                (if (consp rev-dag)
           ;;                                    (renaming-arrayp renaming-array-name renaming-array2 (+ 1 (maxelem (strip-cars rev-dag))))
           ;;                                  t)
           ;;                                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
           ;;                                (symbol-alistp embedded-dag-var-alist) ;strengthen
           ;;                                (rule-alistp rule-alist)
           ;;                                (nat-listp nodenums-to-assume-false)
           ;;                                (all-< nodenums-to-assume-false dag-len)
           ;;                                (equiv-alistp equiv-alist)
           ;;                                ;; print
           ;;                                (hit-countsp hit-counts)
           ;;                                (triesp tries)
           ;;                                (interpreted-function-alistp interpreted-function-alist)
           ;;                                (symbol-listp monitored-symbols)
           ;;                                (natp embedded-dag-depth) ;can we just use the prover depth?
           ;;                                (stringp case-designator)

           ;;                                (natp prover-depth)
           ;;                                (simple-prover-optionsp options))
           ;;                    :measure (+ 1 (nfix count)))
           ;;             (type (unsigned-byte 59) count))
           ;;    (if (zp-fast count)
           ;;        (mv :count-exceeded renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
           ;;      (if (endp rev-dag)
           ;;          (mv (erp-nil) renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
           ;;        (let* ((entry (car rev-dag))
           ;;               (nodenum (car entry))
           ;;               (expr (cdr entry)))
           ;;          (if (atom expr) ;variable
           ;;              (let ((new-nodenum (lookup-eq-safe2 expr embedded-dag-var-alist 'merge-embedded-dag-into-dag-for-basic-prover))) ;drop the -safe?
           ;;                (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
           ;;                                                            renaming-array-name
           ;;                                                            (aset1 renaming-array-name renaming-array2 nodenum new-nodenum)
           ;;                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                            embedded-dag-var-alist
           ;;                                                            rule-alist
           ;;                                                            nodenums-to-assume-false ;equality-assumptions
           ;;                                                            equiv-alist
           ;;                                                            print
           ;;                                                            hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state))
           ;;            (if (quotep expr)
           ;;                (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
           ;;                                                            renaming-array-name
           ;;                                                            (aset1 renaming-array-name renaming-array2 nodenum expr)
           ;;                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                            embedded-dag-var-alist
           ;;                                                            rule-alist
           ;;                                                            nodenums-to-assume-false ;equality-assumptions
           ;;                                                            equiv-alist
           ;;                                                            print
           ;;                                                            hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state)
           ;;              ;;function call:
           ;;              ;;first fixup the call to be about nodenums in the main dag:
           ;;              (let* ((fn (ffn-symb expr))
           ;;                     (args (dargs expr))
           ;;                     (args (rename-dargs args renaming-array-name renaming-array2))
           ;;                     (expr (cons fn args)))
           ;;                ;;then simplify it:
           ;;                (mv-let (erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
           ;;                  ;;fffixme this can create a new renaming-array2 which can lead to slow-array warnings... <-- old comment?
           ;;                  (,simplify-tree-name expr
           ;;                                                               'equal ;fixme?
           ;;                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                               rule-alist
           ;;                                                               ;;nil ;;trees-equal-to-tree
           ;;                                                               nodenums-to-assume-false ;equality-assumptions
           ;;                                                               equiv-alist
           ;;                                                               print
           ;;                                                               hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state)
           ;;                  (if erp
           ;;                      (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
           ;;                    (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
           ;;                                                                renaming-array-name
           ;;                                                                (aset1 renaming-array-name renaming-array2 nodenum new-nodenum-or-quotep)
           ;;                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                                embedded-dag-var-alist
           ;;                                                                rule-alist
           ;;                                                                nodenums-to-assume-false ;equality-assumptions
           ;;                                                                equiv-alist print
           ;;                                                                hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state))))))))))

           ;; Simplify a call of IF or MYIF.  Simplify the test first and, if we can resolve it, only simplify the appropriate branch.
           ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           (defund ,simplify-if-tree-name (tree
                                           equiv
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist
                                           nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                           equiv-alist ;don't pass this around?
                                           print
                                           hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
             (declare (xargs :guard (and (axe-treep tree)
                                         (equivp equiv)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (bounded-axe-treep tree dag-len)
                                         (consp tree) ;; this case
                                         (member-eq (ffn-symb tree) '(if myif)) ;; this case
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (b* ((args (fargs tree))
                    ((when (not (= 3 (len args)))) ;optimize?
                     (mv :bad-arity nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                    ;; First, try to resolve the if-test:
                    ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                     (,simplify-tree-name (first args) ;the test
                                          'iff ;can rewrite the test in a propositional context
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth
                                          case-designator prover-depth options (+ -1 count)))
                    ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                 (if (consp simplified-test) ;tests for quotep
                     ;; The test was resolved, so just simplify the appropriate branch:
                     (,simplify-tree-name (if (unquote simplified-test)
                                              (second args) ;then branch
                                            (third args)    ;else branch
                                            )
                                          equiv ;use the same equiv
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                          embedded-dag-depth case-designator prover-depth options (+ -1 count))
                   ;; The test was not resolved, so we must rewrite both branches: ;; todo: just call simplify-tree twice here?
                   (b* (((mv erp simplified-other-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         (,simplify-trees-name (rest args)
                                               '(equal equal) ;;equiv-lst ;todo: use the same equiv as for the whole term?
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                               equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                     (,simplify-fun-call-name (ffn-symb tree)
                                              (cons simplified-test simplified-other-args)
                                              equiv
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alist
                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                              equiv-alist
                                              print
                                              hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))

           ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           (defund ,simplify-boolif-tree-name (tree ;pass less?
                                               equiv
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist
                                               nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                               equiv-alist ;don't pass this around?
                                               print
                                               hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
             (declare (xargs :guard (and (axe-treep tree)
                                         (equivp equiv)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (bounded-axe-treep tree dag-len)
                                         (consp tree)              ;; this case
                                         (eq (ffn-symb tree) 'boolif) ;; this case
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (b* ((args (fargs tree))
                    ((when (not (= 3 (len args)))) ;optimize?
                     (mv :bad-arity nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                    ;; First, try to resolve the if-test:
                    ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                     (,simplify-tree-name (first args) ;the test
                                          'iff ;can rewrite the test in a propositional context
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth
                                          case-designator prover-depth options (+ -1 count)))
                    ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                 (if (consp simplified-test) ;tests for quotep
                     ;; The test was resolved, so just simplify the appropriate branch:
                     ;; TODO: Drop the bool-fix calls if the EQUIV is IFF?
                     (,simplify-tree-name (if (unquote simplified-test)
                                              `(bool-fix$inline ,(second args)) ;then branch
                                            `(bool-fix$inline ,(third args)) ;else branch
                                            )
                                          equiv ;use the same equiv, todo: consider using IFF here
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                          embedded-dag-depth case-designator prover-depth options (+ -1 count))
                   ;; The test was not resolved, so we must rewrite both branches: ;; todo: just call simplify-tree twice here?
                   (b* (((mv erp simplified-other-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         (,simplify-trees-name (rest args)
                                               '(equal equal) ;;equiv-lst ;todo: use '(iff iff) here, or try the same equiv as for the whole term?
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                               equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                     (,simplify-fun-call-name 'boolif
                                              (cons simplified-test simplified-other-args)
                                              equiv
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alist
                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                              equiv-alist
                                              print
                                              hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))

           ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           ;; Takes a FN and simplified ARGS.  No special handling for IFs, lambdas, or ground terms.
           (defund ,simplify-fun-call-name (fn ; a function symbol
                                            args ; the simplified args
                                            equiv
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist
                                            nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                            equiv-alist ;don't pass this around?
                                            print
                                            hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
             (declare (xargs :guard (and (symbolp fn)
                                         (not (equal 'quote fn))
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (bounded-darg-listp args dag-len)
                                         (equivp equiv)
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (b* (;; Try to apply rules:
                    ((mv erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                     (,try-to-apply-rules-name
                      (get-rules-for-fn fn rule-alist)
                      rule-alist args
                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                    ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                 (if rhs-or-nil
                     ;; A rule fired, so rewrite the instantiated RHS:
                     ;; TODO: should try-to-apply-rules-name make this call directly?  if so, what should it do in case of failure?
                     (,simplify-tree-name
                      rhs-or-nil
                      equiv ;; was: 'equal
                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist
                      print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                   ;; No rule fired, so no simplification can be done.  This node is ready to add to the dag:
                   (b* ((- (and (member-eq print '(:verbose! :verbose)) (cw "(Making ~x0 term with args: ~x1.)~%" fn args)))
                        ((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                         ;; todo: perhaps inline this:
                         (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                        ((when erp) (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                     ;; Finally, see if the node can be replaced by something using the assumptions.  Note that this uses
                     ;; the simplified args, so assumptions not in normal form may have no effect.
                     (mv (erp-nil)
                         ;; (maybe-replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array) ;currently, this can only replace it with a constant?
                         (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))

           ;; Rewrite TREE repeatedly using RULE-ALIST and NODENUMS-TO-ASSUME-FALSE1/NODENUMS-TO-ASSUME-FALSE2 and add the result to the dag, returning a nodenum or a quotep.
           ;; TREE has nodenums and quoteps and variables (really? yes, from when we call this on a worklist of nodes) at the leaves.
           ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           ;; be sure we always handle lambdas early, in case one is hiding an if - fixme - skip this for now?
           (defund ,simplify-tree-name (tree ;should be variable-free, but it would take some work to prove that
                                        equiv
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alist
                                        nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                        equiv-alist ;don't pass this around?
                                        print
                                        hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
             (declare (xargs :guard (and (axe-treep tree)
                                         (equivp equiv)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (bounded-axe-treep tree dag-len)
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (if (atom tree)
                   (if (symbolp tree) ;; TODO: Prove that this case is impossible.
                       (progn$ ;;nil ;;(cw "Rewriting the variable ~x0" tree) ;new!
                         (er hard? ',simplify-tree-name "rewriting the var ~x0" tree)
                         (mv :unexpected-var nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         ;;                      ;; It's a variable:  todo: perhaps add it first and then use assumptions?
                         ;;                      ;; First try looking it up in the assumptions (fixme make special version of rewrite-term-using-assumptions-for-basic-prover for a variable?):
                         ;;                      (let ((assumption-match (replace-term-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array print)))
                         ;;                        (if assumption-match
                         ;;                            ;; We replace the variable with something it's equated to in nodenums-to-assume-false.
                         ;;                            ;; We don't rewrite the result (by the second pass, nodenums-to-assume-false will be simplified - and maybe we should always do that?)
                         ;; ;fixme what if there is a chain of equalities to follow?
                         ;;                            (mv nil assumption-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                         ;;                          ;; no match, so we just add the variable to the DAG:
                         ;;                          ;;make this a macro? this one might be rare..  same for other adding to dag operations?
                         ;;                          (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-variable-alist) ;fixme simplify nodenum?
                         ;;                            (add-variable-to-dag-array tree dag-array dag-len dag-parent-array dag-variable-alist)
                         ;;                            (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))
                         )
                     ;; TREE is a nodenum (because it's an atom but not a symbol): TODO: Do we ever need to try to replace
                     ;; the nodenum using assumptions?  That is, can we assume that nodenums in TREE are simplified?
                     ;; Probably nodes in trees are usually simplified, because they support the arguments of some function
                     ;; call or lambda application being rewritten, and the args are usually simplified first.  But maybe
                     ;; not always, if the nodes come from binding free vars using assumptions, or (perhaps) from
                     ;; axe-bind-free functions (but probably those only return children of nodes already in the alist).
                     ;; But, if the node here is not simplified, do we really want to start examining its supporters?
                     ;; Another consideration could be if the node was not simplified under the right equiv.
                     ;; Doing just this caused some tests to fail, though they may be provable via other means soon to be implemented:
                     ;;(mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)

                     ;; old:
                     ;; (let ((assumption-match (replace-nodenum-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array)))
                     ;;   (if assumption-match ;;TODO: We know (for now) that this must be a constant
                     ;;       (prog2$ nil ;;fffixme don't simplify here, since nodenums-to-assume-false will be simplified after the 1st pass (what about chains of equalities)?
                     ;;               (,simplify-tree-name assumption-match
                     ;;                                    equiv dag-array dag-len dag-parent-array dag-constant-alist
                     ;;                                    dag-variable-alist
                     ;;                                    rule-alist nodenums-to-assume-false  equiv-alist print
                     ;;                                    hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                     ;;     (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                     (mv (erp-nil)
                         ;;(maybe-replace-nodenum-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array)
                         (maybe-replace-nodenum-using-assumption-array tree equiv assumption-array assumption-array-num-valid-nodes print)
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                 ;; TREE is not an atom:
                 (let ((fn (ffn-symb tree)))
                   (case fn
                     (quote ;; TREE is a quoted constant, so return it:
                       (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                     ((if myif)
                      (,simplify-if-tree-name tree
                                              equiv
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alist
                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                              equiv-alist ;don't pass this around?
                                              print
                                              hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                     (boolif
                       (,simplify-boolif-tree-name tree
                                                   equiv
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   rule-alist
                                                   nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                   equiv-alist ;don't pass this around?
                                                   print
                                                   hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                     ;; TODO: Consider adding back special handling for bvif, booland, and boolor (see below), but do it in separate functions
                     (t ;; TREE is a function call. fn may be a lambda or a short-circuit-function (if/myif/boolif/bvif/booland/boolor):
                       ;; (let ((args (fargs tree)))
                       ;; ;;Rewrite the args, *except* if it's a short-circuit function, we may be able to avoid rewriting them all and instead just return a new term to rewrite (will that new term ever be a constant?).
                       ;; (mv-let
                       ;;   (erp short-circuitp term-or-rewritten-args ;if short-circuitp is non-nil, then this is a term equal to fn applied to args, else it's a list of rewritten args
                       ;;        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;   (if (eq 'bvif fn) ;;(bvif size test thenpart elsepart)
                       ;;       ;; First, try to resolve the if-test:
                       ;;       (mv-let (erp test-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;         (,simplify-tree-name (second args) ;the test
                       ;;                              'iff ;can rewrite the test in a propositional context
                       ;;                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                              rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                       ;;                              embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;         (if erp
                       ;;             (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;           (if (consp test-result) ;tests for quotep
                       ;;               (mv (erp-nil)
                       ;;                   t ;; did short-circuit
                       ;;                   (if (unquote test-result)
                       ;;                       `(bvchop ;$inline
                       ;;                         ,(first args) ,(third args)) ;then branch
                       ;;                     `(bvchop ;$inline
                       ;;                       ,(first args) ,(fourth args))) ;else branch
                       ;;                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;             ;;didn't resolve the test; must rewrite the other arguments:
                       ;;             (mv-let (erp other-arg-results dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;               (,simplify-trees-name (cons (first args) ;the size
                       ;;                                           (cddr args) ;then part and else part
                       ;;                                           )
                       ;;                                     '(equal equal equal) ;;equiv-lst
                       ;;                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                     rule-alist nodenums-to-assume-false
                       ;;                                     equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;               (if erp
                       ;;                   (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                 (mv (erp-nil) nil ;did not short-circuit
                       ;;                     (cons (first other-arg-results)
                       ;;                           (cons test-result
                       ;;                                 (cdr other-arg-results)))
                       ;;                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))
                       ;;     (if (eq 'booland fn) ;;(booland arg1 arg2)
                       ;;         ;; First, rewrite arg1:
                       ;;         (mv-let (erp arg1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;           (,simplify-tree-name (first args)
                       ;;                                'iff ;can rewrite the arg in a propositional context
                       ;;                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist
                       ;;                                monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;           (if erp
                       ;;               (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;             (if (equal *nil* arg1-result)
                       ;;                 (mv (erp-nil)
                       ;;                     t       ;; did short-circuit
                       ;;                     *nil*   ;; (booland nil x) = nil
                       ;;                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;               ;;arg1 didn't rewrite to nil (fixme could handle if it rewrote to t); must rewrite the other argument:
                       ;;               (mv-let (erp arg2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                 (,simplify-tree-name (second args)
                       ;;                                      'iff ;can rewrite the arg in a propositional context
                       ;;                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                      rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist
                       ;;                                      monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;                 (if erp
                       ;;                     (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                   (mv (erp-nil)
                       ;;                       nil ;did not short-circuit
                       ;;                       (list arg1-result arg2-result)
                       ;;                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))
                       ;;       (if (eq 'boolor fn) ;;(boolor arg1 arg2)
                       ;;           ;; First, rewrite arg1
                       ;;           (mv-let (erp arg1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;             (,simplify-tree-name (first args)
                       ;;                                  'iff ;can rewrite the arg in a propositional context
                       ;;                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                  rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist
                       ;;                                  monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;             (if erp
                       ;;                 (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;               (if (and (consp arg1-result) (unquote arg1-result)) ;checks for a non-nil constant
                       ;;                   (mv (erp-nil)
                       ;;                       t     ;; did short-circuit
                       ;;                       *t* ;boolor of a non-nil value is t
                       ;;                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                 ;;arg1 didn't rewrite to a non-nil constant (fixme could handle if it rewrote to nil); must rewrite the other argument:
                       ;;                 (mv-let (erp arg2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                   (,simplify-tree-name (second args)
                       ;;                                        'iff ;can rewrite the arg in a propositional context
                       ;;                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                        rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist
                       ;;                                        monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;                   (if erp
                       ;;                       (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;                     (mv (erp-nil)
                       ;;                         nil ;did not short-circuit
                       ;;                         (list arg1-result arg2-result)
                       ;;                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))
                       ;;         ;;not a short-circuit-function:
                       ;;         (mv-let (erp arg-results dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;           (,simplify-trees-name args
                       ;;                                 (get-equivs equiv fn equiv-alist)
                       ;;                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                                 rule-alist nodenums-to-assume-false
                       ;;                                 equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;           (if erp
                       ;;               (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;             (mv (erp-nil)
                       ;;                 nil ;did not short-circuit
                       ;;                 arg-results
                       ;;                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))
                       ;; (if erp
                       ;;     (mv erp tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       ;;   (if short-circuitp
                       ;;       ;;just simplify the term returned from short-circuit rewriting:
                       ;;       (,simplify-tree-name term-or-rewritten-args
                       ;;                            equiv ;use the same equiv
                       ;;                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                            rule-alist nodenums-to-assume-false equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                       ;;                            embedded-dag-depth case-designator prover-depth options (+ -1 count))
                       ;;Rewrite the args:
                       (b* ((args (fargs tree))
                            (equivs (let ((equivs (get-equivs equiv fn equiv-alist)))
                                      (if equivs
                                          equivs
                                        :equal ;means use 'equal for all equivs
                                        )))
                            ;; we could avoid this check if we know that arities were right:
                            ((when (and (not (equal :equal equivs)) ;todo: is this possible?
                                        (not (= (len equivs) (len args)))))
                             (mv :bad-equivs nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                            ((mv erp simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                             (,simplify-trees-name args
                                                   equivs
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                   equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                            ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                         ;; Now we simplify the function applied to the simplified args:
                         (if (consp fn) ;;tests for lambda
                             ;; It's a lambda, so we beta-reduce and simplify the result:
                             ;; note that we don't look up lambdas in the nodenums-to-assume-false (this is consistent with simplifying first).  actually, we only use the nodenums-to-assume-false for free var matching now.
                             (let* ((formals (second fn))
                                    (body (third fn))
                                    (new-expr (,subcor-var-and-eval-name formals simplified-args body interpreted-function-alist)))
                               (,simplify-tree-name new-expr
                                                    equiv ; was: 'equal
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    rule-alist
                                                    nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes  equiv-alist print
                                                    hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                           ;; Handle ground terms:
                           ;; TODO: Think about how it is possible to even have a ground term here
                           (b* (((mv erp evaluatedp val)
                                 (if (not (all-consp simplified-args)) ;; test for args being quoted constants
                                     ;; not a ground term:
                                     (mv (erp-nil) nil nil)
                                   ;; ground term, so try to evaluate:
                                   (b* (((mv erp val)
                                         (,apply-axe-evaluator-to-quoted-args-name fn simplified-args interpreted-function-alist)))
                                     (if erp
                                         (if (call-of :unknown-function erp)
                                             (mv (erp-nil) nil nil) ;no error, but it didn't produce a value (todo: print a warning?)
                                           ;; anything else non-nil is a true error:
                                           (mv erp nil nil))
                                       ;; normal case, evaluation worked:
                                       (mv (erp-nil) t val)))))
                                ;; I suppose we could suppress any evaluator error here if we choose to (might be a bit faster)?
                                ((when erp) (mv erp tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                             (if evaluatedp
                                 (mv (erp-nil)
                                     (enquote val)
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     hit-counts tries)
                               ;; It wasn't a ground term (that we can evaluate).
                               (,simplify-fun-call-name fn
                                                        simplified-args
                                                        equiv
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        rule-alist
                                                        nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                        equiv-alist ;don't pass this around?
                                                        print
                                                        hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))))))))))))

           ;; Simplify all the trees in TREES and add to the DAG.
           ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
           ;; If the items in TREES are already all nodenums or quoted constants, this doesn't re-cons-up the list.
           ;; (not tail-recursive, btw.)
           (defund ,simplify-trees-name (trees
                                         equivs
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rule-alist
                                         nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                         equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                         embedded-dag-depth case-designator prover-depth
                                         options count)
             (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         ;; TODO: Consider using nil for the equivs in any case where we can't do better that equal (no entry in the equiv-alist, or even when the remaining args of the call don't need to be treated specially):
                                         (or (eq :equal equivs) ;means use 'equal for all the equivs
                                             (and (equiv-listp equivs)
                                                  (equal (len equivs) (len trees))))
                                         (bounded-axe-tree-listp trees dag-len)
                                         (rule-alistp rule-alist)
                                         (nat-listp nodenums-to-assume-false1)
                                         (all-< nodenums-to-assume-false1 dag-len)
                                         (nat-listp nodenums-to-assume-false2)
                                         (all-< nodenums-to-assume-false2 dag-len)
                                         (assumption-arrayp 'assumption-array assumption-array)
                                         (natp assumption-array-num-valid-nodes)
                                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                         (equiv-alistp equiv-alist)
                                         ;; print
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (symbol-listp monitored-symbols)
                                         (natp embedded-dag-depth) ;can we just use the prover depth?
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (simple-prover-optionsp options))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (if (endp trees)
                   (mv (erp-nil) trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 (b* (;; this simplifies the arguments in reverse order (TODO: why?)
                      ((mv erp rest-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       (,simplify-trees-name (rest trees)
                                             (if (eq :equal equivs) :equal (rest equivs))
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes  equiv-alist print hit-counts tries interpreted-function-alist
                                             monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                      ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                      ((mv erp first-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                       (,simplify-tree-name (first trees)
                                            (if (eq :equal equivs) 'equal (first equivs))
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                            embedded-dag-depth
                                            case-designator prover-depth options (+ -1 count)))
                      ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                   (mv (erp-nil)
                       (cons-with-hint first-result rest-result trees)
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))))

           ;;           (mv-let (rewritten-if-test ;if this is non-nil, tree is an if (or related thing) and this is what the test rewrote to
           ;;                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
           ;;                   (if (or (eq 'if fn)
           ;;                           (eq 'myif fn)
           ;;                           (eq 'boolif fn)) ; BBOZO (what about bvif? - the test in a BVIF is a different arg)
           ;; ;fffffixme if it's a boolif we need to bool-fix$inline the result?!
           ;;                       ;; TREE is an if (or related thing):
           ;;                       (let ((test (fargn tree 1))
           ;;                             ;;(thenpart (fargn tree 2))
           ;;                             ;;(elsepart (fargn tree 3))
           ;;                             )
           ;;                         ;; First, try to resolve the if-test:
           ;;                         (,simplify-tree-name test
           ;;                                                                      'iff
           ;;                                                                      dag-array dag-len dag-parent-array
           ;;                                                                      dag-constant-alist dag-variable-alist
           ;;                                                                      rule-alist
           ;;                                                                      nodenums-to-assume-false  equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth
           ;;                                                                      options (+ -1 count)))
           ;;                     ;;it's not an IF, so we didn't even attempt to resolve an IF test:
           ;;                     (mv nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
           ;;                   (if rewritten-if-test ;we resolved the test
           ;;                       ;; The test rewrote to a constant, so TREE is equal to its "then" branch or its "else" branch:
           ;;                       (,simplify-tree-name (if (unquote rewritten-if-test)
           ;;                                                                        (fargn tree 2) ;;thenpart
           ;;                                                                      (fargn tree 3) ;;elsepart
           ;;                                                                      )
           ;;                                                                    equiv ;; was: 'equal
           ;;                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                                    rule-alist
           ;;                                                                    nodenums-to-assume-false  equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count))
           ;; ;could not resolve the if test to a constant (treat it like a regular function symbol, but reuse the rewritten test:

           ;;                     (let ((args (fargs tree)))
           ;;                       ;; We are simplifying a call to FN on ARGS, where ARGS are trees.
           ;;                       ;; FN might be a lambda.
           ;;                       ;; FN might be IF/etc for which we couldn't resolve the test.
           ;;                       ;; bozo might it be possible to not check for ground-terms because we never build them -- think about where terms might come from other than sublis-var-simple which we could change to not build ground terms (of functions we know about)
           ;;                       ;; First we simplify the args:
           ;;                       ;; ffixme maybe we should try to apply rules here (maybe outside-in rules) instead of rewriting the args
           ;;                       ;;fixme could pass in a flag for the common case where the args are known to be already simplified (b/c the tree is a dag node?) - but are they simplified in this context?
           ;;                       (mv-let (args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries changed-anything-flg)
           ;;                               (if rewritten-if-test
           ;;                                   ;;don't rewrite the if-test again!
           ;;                                   (mv-let
           ;;                                    (nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                                         hit-counts tries changed-anything-flg)
           ;;                                    (,simplify-trees-name
           ;;                                     (cdr args) ;skip the if-test
           ;;                                     (cdr (get-equivs equiv fn equiv-alist)) ;lookup what equivs to use for the arguments ;;;;forgot the cdr on this line!
           ;;                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rule-alist
           ;;                                     nodenums-to-assume-false  equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count))
           ;;                                    (mv (cons rewritten-if-test nodenums-or-quoteps)
           ;;                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
           ;;                                        hit-counts tries changed-anything-flg))
           ;;                                 ;;rewrite all the args:
           ;;                                 (,simplify-trees-name
           ;;                                  args
           ;;                                  (get-equivs equiv fn equiv-alist) ;lookup what equivs to use for the arguments
           ;;                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rule-alist
           ;;                                  nodenums-to-assume-false  equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count)))
           ;;                               (declare (ignore changed-anything-flg)) ;could pass in tree and below check this flag to decide whether to use tree or cons fn onto the simplified args...
           ;;                               ))))))))

           ) ;end mutual-recursion for Axe Prover

         ;; TODO: Why is this so slow?
         (make-flag ,relieve-free-var-hyp-and-all-others-name)

         ;; The main return type theorem (see also corollaries below):
         (,(pack$ 'defthm-flag- relieve-free-var-hyp-and-all-others-name)
          (DEFTHM ,(pack$ RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS-name '-return-type)
            (IMPLIES (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (bounded-darg-listp (strip-cdrs alist) dag-len)
                          (alist-suitable-for-hyp-tree-and-hypsp alist hyp other-hyps)
                          (nat-listp nodenums-to-assume-false-to-walk-down1)
                          (all-< nodenums-to-assume-false-to-walk-down1 dag-len)
                          (nat-listp nodenums-to-assume-false-to-walk-down2)
                          (all-< nodenums-to-assume-false-to-walk-down2 dag-len)
                          (axe-treep hyp)
                          (consp hyp)
                          (not (eq 'quote (ffn-symb hyp)))
                          (natp hyp-num)
                          (axe-rule-hyp-listp other-hyps)
                          (symbol-alistp alist)
                          (symbolp rule-symbol)
                          (equiv-alistp equiv-alist)
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth)
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS
                       (declare (ignore HYPS-RELIEVEDP))
                       (implies (not erp)
                                (and (symbol-alistp extended-alist)
                                     (bounded-darg-listp (strip-cdrs extended-alist) new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS-name)
          (DEFTHM ,(pack$ RELIEVE-rule-HYPS-name '-return-type)
            (IMPLIES (and (axe-rule-hyp-listp hyps)
                          (alist-suitable-for-hypsp alist hyps)
                          (natp hyp-num)
                          (symbol-alistp alist)
                          (symbolp rule-symbol)
                          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (bounded-darg-listp (strip-cdrs alist) dag-len)
                          (equiv-alistp equiv-alist)
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-relieve-rule-hyps
                       (declare (ignore HYPS-RELIEVEDP))
                       (implies (not erp)
                                (and (symbol-alistp extended-alist)
                                     (bounded-darg-listp (strip-cdrs extended-alist) new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,RELIEVE-rule-HYPS-name)
          (DEFTHM ,(pack$ TRY-TO-APPLY-RULES-name '-return-type)
            (IMPLIES (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (stored-axe-rule-listp stored-rules)
                          (rule-alistp rule-alist)
                          (bounded-darg-listp args-to-match dag-len)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-try-to-apply-rules
                       (implies (not erp)
                                (and (or (and (axe-treep new-rhs-or-nil) ;todo: variable-free?
                                              (bounded-axe-treep new-rhs-or-nil new-dag-len))
                                         (null new-rhs-or-nil))
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,TRY-TO-APPLY-RULES-name)
          (DEFTHM ,(pack$ SIMPLIFY-if-TREE-name '-return-type)
            (IMPLIES (and (axe-treep tree)
                          (equivp equiv)
                          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (bounded-axe-treep tree dag-len)
                          ;; (consp tree) ;; this case
                          (member-eq (ffn-symb tree) '(if myif)) ;; this case
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-simplify-if-tree
                       (implies (not erp)
                                (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,SIMPLIFY-if-TREE-name)
          (DEFTHM ,(pack$ SIMPLIFY-boolif-TREE-name '-return-type)
            (IMPLIES (and (axe-treep tree)
                          (equivp equiv)
                          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (bounded-axe-treep tree dag-len)
                          ;; (consp tree)                              ;; this case
                          (eq (ffn-symb tree) 'boolif) ;; this case
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-simplify-boolif-tree
                       (implies (not erp)
                                (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,SIMPLIFY-boolif-TREE-name)
          (DEFTHM ,(pack$ SIMPLIFY-fun-call-name '-return-type)
            (IMPLIES (and (symbolp fn)
                          (not (equal 'quote fn))
                          (bounded-darg-listp args dag-len)
                          (equivp equiv)
                          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth)
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-simplify-fun-call
                       (implies (not erp)
                                (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,SIMPLIFY-fun-call-name)
          (DEFTHM ,(pack$ SIMPLIFY-TREE-name '-return-type)
            (IMPLIES (and (axe-treep tree)
                          (equivp equiv)
                          (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (bounded-axe-treep tree dag-len)
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-simplify-tree
                       (implies (not erp)
                                (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,SIMPLIFY-TREE-name)
          (DEFTHM ,(pack$ SIMPLIFY-TREES-name '-return-type)
            (IMPLIES (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (or (eq :equal equivs) ;means use 'equal for all the equivs
                              (and (equiv-listp equivs)
                                   (equal (len equivs) (len trees))))
                          (bounded-axe-tree-listp trees dag-len)
                          (rule-alistp rule-alist)
                          (nat-listp nodenums-to-assume-false1)
                          (all-< nodenums-to-assume-false1 dag-len)
                          (nat-listp nodenums-to-assume-false2)
                          (all-< nodenums-to-assume-false2 dag-len)
                          (assumption-arrayp 'assumption-array assumption-array)
                          (natp assumption-array-num-valid-nodes)
                          (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                          (equiv-alistp equiv-alist)
                          ;; print
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (interpreted-function-alistp interpreted-function-alist)
                          (symbol-listp monitored-symbols)
                          (natp embedded-dag-depth) ;can we just use the prover depth?
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (simple-prover-optionsp options)
                          )
                     (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                       ,call-of-simplify-trees
                       (implies (not erp)
                                (and (bounded-darg-listp nodenums-or-quoteps new-dag-len)
                                     (true-listp nodenums-or-quoteps)
                                     (equal (len nodenums-or-quoteps)
                                            (len trees))
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (<= dag-len new-dag-len)
                                     (hit-countsp hit-counts)
                                     (triesp tries)))))
            :FLAG ,SIMPLIFY-TREES-name)
          :hints (("Goal" :expand (,call-of-simplify-trees
                                   ,call-of-simplify-if-tree
                                   ,call-of-simplify-boolif-tree
                                   ,call-of-simplify-tree
                                   ,call-of-simplify-fun-call
                                   ,call-of-relieve-rule-hyps
                                   (:free (other-hyps) ,call-of-relieve-free-var-hyp-and-all-others)
                                   (:free (hit-counts tries) ,call-of-try-to-apply-rules)
                                   (,relieve-rule-hyps-name nil ; note the nil
                                                            hyp-num
                                                            alist
                                                            rule-symbol
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            equiv-alist rule-alist
                                                            nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                            print hit-counts tries interpreted-function-alist
                                                            monitored-symbols embedded-dag-depth
                                                            case-designator
                                                            prover-depth options count)
                                   (,relieve-free-var-hyp-and-all-others-name nil ; note the nil
                                                                              nil ; note the nil
                                                                              hyp
                                                                              hyp-num
                                                                              other-hyps
                                                                              alist rule-symbol
                                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                              equiv-alist rule-alist
                                                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                              print
                                                                              hit-counts tries interpreted-function-alist monitored-symbols
                                                                              embedded-dag-depth
                                                                              case-designator prover-depth options count)
                                   (,simplify-trees-name nil ;note the nil
                                                         equivs
                                                         dag-array dag-len dag-parent-array
                                                         dag-constant-alist dag-variable-alist
                                                         rule-alist nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                         equiv-alist print
                                                         hit-counts tries interpreted-function-alist
                                                         monitored-symbols
                                                         embedded-dag-depth case-designator
                                                         prover-depth options count)
                                   (,try-to-apply-rules-name nil ; note the nil
                                                             rule-alist
                                                             args-to-match
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes equiv-alist print hit-counts tries
                                                             interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
                                   (axe-rule-hyp-listp hyps))
                   :do-not '(generalize eliminate-destructors)
                   :in-theory '((:definition ,relieve-free-var-hyp-and-all-others-name)
                                (:definition ,relieve-rule-hyps-name)
                                (:definition ,simplify-boolif-tree-name)
                                (:definition ,simplify-fun-call-name)
                                (:definition ,simplify-if-tree-name)
                                (:definition ,simplify-tree-name)
                                (:definition ,simplify-trees-name)
                                (:definition ,try-to-apply-rules-name)
                                (:rewrite ,(pack$ 'flag-relieve-free-var-hyp-and-all-others-for- suffix '-prover-equivalences))
                                (:induction ,(pack$ 'flag-relieve-free-var-hyp-and-all-others-for- suffix '-prover))
                                ,(pack$ 'axe-treep-of- sublis-var-and-eval-name)
                                ,(pack$ 'axe-treep-of- subcor-var-and-eval-name)
                                ,(pack$ 'bounded-axe-treep-of- sublis-var-and-eval-name)
                                ,(pack$ 'bounded-axe-treep-of- subcor-var-and-eval-name)
                                ;; ,(pack$ 'axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
                                ;; ,(pack$ 'bounded-axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
                                ;; ,(pack$ 'consp-of-mv-nth-0-of- instantiate-hyp-name)
                                ;; ,(pack$ 'not-equal-of-quote-and-car-of-mv-nth-0-of- instantiate-hyp-name)
                                ;; ,(pack$ 'axe-tree-listp-of-cdr-of-mv-nth-0-of- instantiate-hyp-name)
                                ;; rules about the free-vars verion:
                                ,(pack$ 'axe-treep-of- instantiate-hyp-free-vars-name)
                                ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-free-vars-name)
                                ,(pack$ 'consp-of- instantiate-hyp-free-vars-name)
                                ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-free-vars-name)
                                ;; rules about the no-free-vars verion:
                                ,(pack$ 'axe-treep-of- instantiate-hyp-no-free-vars-name)
                                ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-no-free-vars-name)
                                ,(pack$ 'consp-of- instantiate-hyp-no-free-vars-name)
                                ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-no-free-vars-name)
                                ,@*make-prover-simple-rules*
                                alist-suitable-for-hypsp-of-unify-terms-and-dag-items-fast-when-stored-axe-rulep
                                alist-suitable-for-hypsp-when-axe-sytaxp-car
                                alist-suitable-for-hypsp-of-append-and-cdr-when-axe-bind-free
                                alist-suitable-for-hypsp-of-append-and-cdr-when-free-vars
                                alist-suitable-for-hypsp-after-matching
                                alist-suitable-for-hypsp-of-cdr-of-car-when-normal
                                alist-suitable-for-hyp-tree-and-hypsp-after-instantiating
                                subsetp-equal-of-free-vars-in-terms-of-fargs-of-cadr-of-car-when-axe-binding-hyp
                                alist-suitable-for-hypsp-of-append-and-cdr-when-axe-binding-hyp
                                subsetp-equal-of-free-vars-in-terms-of-fargs-of-cadr-of-car-when-axe-bind-free
                                ,(pack$ 'axe-tree-vars-of- instantiate-hyp-free-vars-name))
                   ;; :in-theory (e/d (bounded-axe-treep-when-natp-strong
                   ;;                  <-OF-+-OF-1-STRENGTHEN-2
                   ;;                  ;;<-OF-+-OF-1-WHEN-INTEGERS
                   ;;                  len-of-lambda-formals-when-axe-treep
                   ;;                  pseudo-termp-of-lambda-body-when-axe-treep
                   ;;                  axe-bind-free-result-okayp-rewrite
                   ;;                  <-of--1-when-natp
                   ;;                  len-of-cdr-better-for-axe-prover
                   ;;                  consp-when-len-equal-for-axe-prover
                   ;;                  member-equal ;todo
                   ;;                  )
                   ;;                 (myquotep mv-nth
                   ;;                  natp
                   ;;                  ; member-equal ;todo
                   ;;                  ))
                   )))

         (defthm ,(pack$ relieve-rule-hyps-name '-return-type-corollary)
           (implies (and (axe-rule-hyp-listp hyps)
                         (alist-suitable-for-hypsp alist hyps)
                         (natp hyp-num)
                         (symbol-alistp alist)
                         (symbolp rule-symbol)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-darg-listp (strip-cdrs alist) dag-len)
                         (equiv-alistp equiv-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         ;; print
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-relieve-rule-hyps
                      (declare (ignore hyps-relievedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (darg-listp (strip-cdrs extended-alist)))))
           :hints (("Goal" :use (:instance ,(pack$ relieve-rule-hyps-name '-return-type))
                    :in-theory (disable ,(pack$ relieve-rule-hyps-name '-return-type)))))

         (defthm ,(pack$ try-to-apply-rules-name '-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (stored-axe-rule-listp stored-rules)
                         (rule-alistp rule-alist)
                         (bounded-darg-listp args-to-match dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-try-to-apply-rules
                      (declare (ignore new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (and (implies new-rhs-or-nil
                                             (and (axe-treep new-rhs-or-nil) ;todo: variable-free?
                                                  (bounded-axe-treep new-rhs-or-nil new-dag-len)))
                                    (equal (alen1 'dag-parent-array new-dag-parent-array)
                                           (alen1 'dag-array new-dag-array))
                                    (dag-constant-alistp new-dag-constant-alist)
                                    (implies (and (<= n new-dag-len)
                                                  (natp n))
                                             (pseudo-dag-arrayp 'dag-array new-dag-array n))
                                    (implies (and (<= new-dag-len n)
                                                  (natp n))
                                             (bounded-dag-parent-arrayp 'dag-parent-array new-dag-parent-array n))
                                    (dag-parent-arrayp 'dag-parent-array new-dag-parent-array)
                                    (natp new-dag-len)))))
           :hints (("Goal" :use (:instance ,(pack$ try-to-apply-rules-name '-return-type))
                    :in-theory (disable ,(pack$ try-to-apply-rules-name '-return-type)))))

         (defthm ,(pack$ try-to-apply-rules-name '-return-type-corollary-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (stored-axe-rule-listp stored-rules)
                         (rule-alistp rule-alist)
                         (bounded-darg-listp args-to-match dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-try-to-apply-rules
                      (declare (ignore new-rhs-or-nil new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ try-to-apply-rules-name '-return-type))
                    :in-theory (disable ,(pack$ try-to-apply-rules-name '-return-type)))))

         (defthm ,(pack$ simplify-tree-name '-return-type-corollary)
           (implies (and (axe-treep tree)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-treep tree dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         ;; print
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-tree
                      (declare (ignore new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (and (implies (and (<= n new-dag-len)
                                                  (natp n))
                                             (pseudo-dag-arrayp 'dag-array new-dag-array n))
                                    (implies (and (not (consp new-nodenum-or-quotep)) ;it's a nodenum
                                                  (<= new-dag-len n)
                                                  (natp n))
                                             (< new-nodenum-or-quotep n))
                                    (implies (not (consp new-nodenum-or-quotep)) ;it's a nodenum
                                             (natp new-nodenum-or-quotep))
                                    ;; use consp as the normal form:
                                    (equal (consp (cdr new-nodenum-or-quotep))
                                           (consp new-nodenum-or-quotep))
                                    (natp new-dag-len)
                                    ))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-tree-name '-return-type))
                    :in-theory (e/d (wf-dagp dargp-less-than)
                                    (,(pack$ simplify-tree-name '-return-type))))))

         (defthm ,(pack$ simplify-tree-name '-return-type-corollary-linear)
           (implies (and (axe-treep tree)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-treep tree dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         ;; print
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-tree
                      (declare (ignore new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (and (<= dag-len new-dag-len)
                                    (implies (not (consp new-nodenum-or-quotep))
                                             (< new-nodenum-or-quotep new-dag-len))))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ simplify-tree-name '-return-type))
                    :in-theory (e/d (wf-dagp dargp-less-than)
                                    (,(pack$ simplify-tree-name '-return-type))))))

         (defthm ,(pack$ simplify-trees-name '-return-type-corollary)
           (implies (and (or (eq :equal equivs) ;means use 'equal for all the equivs
                             (and (equiv-listp equivs)
                                  (equal (len equivs) (len trees))))
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-tree-listp trees dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-trees
                      (declare (ignore new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (and (darg-listp nodenums-or-quoteps)
                                    ;;(true-listp nodenums-or-quoteps)
                                    (equal (all-myquotep nodenums-or-quoteps)
                                           (all-consp nodenums-or-quoteps))
                                    ))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-trees-name '-return-type))
                    :in-theory (e/d (all-myquotep-when-darg-listp) (,(pack$ simplify-trees-name '-return-type))))))

         (defthm ,(pack$ simplify-trees-name '-return-type-corollary-linear)
           (implies (and (or (eq :equal equivs) ;means use 'equal for all the equivs
                             (and (equiv-listp equivs)
                                  (equal (len equivs) (len trees))))
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-tree-listp trees dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-trees
                      (declare (ignore nodenums-or-quoteps new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ simplify-trees-name '-return-type))
                    :in-theory (e/d (all-myquotep-when-darg-listp) (,(pack$ simplify-trees-name '-return-type))))))

         (defthm ,(pack$ simplify-fun-call-name '-return-type-corollary-linear)
           (implies (and (symbolp fn)
                         (not (equal 'quote fn))
                         (bounded-darg-listp args dag-len)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-fun-call
                      (declare (ignore nodenum-or-quotep new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ simplify-fun-call-name '-return-type))
                    :in-theory (disable ,(pack$ simplify-fun-call-name '-return-type)))))

         (defthm ,(pack$ simplify-fun-call-name '-return-type-corollary-dargp)
           (implies (and (symbolp fn)
                         (not (equal 'quote fn))
                         (bounded-darg-listp args dag-len)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-fun-call
                      (declare (ignore new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (dargp nodenum-or-quotep))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-fun-call-name '-return-type))
                    :in-theory (disable ,(pack$ simplify-fun-call-name '-return-type)))))

         (defthm ,(pack$ simplify-fun-call-name '-return-type-corollary-array-lengths)
           (implies (and (symbolp fn)
                         (not (equal 'quote fn))
                         (bounded-darg-listp args dag-len)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-fun-call
                      (declare (ignore nodenum-or-quotep new-dag-len new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (equal (alen1 'dag-parent-array new-dag-parent-array)
                                      (alen1 'dag-array new-dag-array)))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-fun-call-name '-return-type))
                    :in-theory (disable ,(pack$ simplify-fun-call-name '-return-type)))))

         ;; not used much
         (defthm ,(pack$ simplify-fun-call-name '-return-type-corollary)
           (implies (and (symbolp fn)
                         (not (equal 'quote fn))
                         (bounded-darg-listp args dag-len)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-fun-call
                      (declare (ignore nodenum-or-quotep new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (and (dag-constant-alistp new-dag-constant-alist)
                                    (pseudo-dag-arrayp 'dag-array new-dag-array new-dag-len)
                                    (bounded-dag-parent-arrayp 'dag-parent-array new-dag-parent-array new-dag-len)
                                    (bounded-dag-constant-alistp new-dag-constant-alist new-dag-len)
                                    (natp new-dag-len)))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-fun-call-name '-return-type))
                    :in-theory (e/d (dargp-less-than) (,(pack$ simplify-fun-call-name '-return-type))))))

         (defthm ,(pack$ simplify-fun-call-name '-return-type-corollary-when-nodenum)
           (implies (and (symbolp fn)
                         (not (equal 'quote fn))
                         (bounded-darg-listp args dag-len)
                         (equivp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equiv-alistp equiv-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      ,call-of-simplify-fun-call
                      (declare (ignore new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (and (not erp)
                                    (not (consp nodenum-or-quotep)) ; this case
                                    )
                               (and (< nodenum-or-quotep new-dag-len)
                                    (< nodenum-or-quotep (alen1 'dag-array new-dag-array))))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-fun-call-name '-return-type))
                    :in-theory (e/d (dargp-less-than wf-dagp)
                                    (,(pack$ simplify-fun-call-name '-return-type)
                                     ,(pack$ simplify-fun-call-name '-return-type-corollary))))))

         (verify-guards ,relieve-free-var-hyp-and-all-others-name
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :do-not-induct t
                    ;; :use (:instance ,(pack$ SIMPLIFY-TREES-name '-return-type))
                    :expand (axe-rule-hyp-listp hyps)
                    :in-theory '(,@*make-prover-simple-rules*
                                 ,(pack$ 'axe-treep-of- sublis-var-and-eval-name)
                                 ,(pack$ 'axe-treep-of- subcor-var-and-eval-name)
                                 ,(pack$ 'bounded-axe-treep-of- sublis-var-and-eval-name)
                                 ,(pack$ 'bounded-axe-treep-of- subcor-var-and-eval-name)
                                 ;; ,(pack$ 'axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
                                 ;; ,(pack$ 'bounded-axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
                                 ;; ,(pack$ 'consp-of-mv-nth-0-of- instantiate-hyp-name)
                                 ;; ,(pack$ 'not-equal-of-quote-and-car-of-mv-nth-0-of- instantiate-hyp-name)
                                 ;; rules about the free-vars verion:
                                 ,(pack$ 'axe-treep-of- instantiate-hyp-free-vars-name)
                                 ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-free-vars-name)
                                 ,(pack$ 'consp-of- instantiate-hyp-free-vars-name)
                                 ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-free-vars-name)
                                 ;; rules about the no-free-vars verion:
                                 ,(pack$ 'axe-treep-of- instantiate-hyp-no-free-vars-name)
                                 ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-no-free-vars-name)
                                 ,(pack$ 'consp-of- instantiate-hyp-no-free-vars-name)
                                 ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-no-free-vars-name)
                                 (:e booleanp)
                                 (:e expt)
                                 (:e eqlablep)
                                 (:e eqlable-listp)
                                 member-eq-exec-is-member-equal ;(:e member-eq-exec)
                                 member-eql-exec-is-member-equal
                                 zp-compound-recognizer
                                 unsigned-byte-p-forward-to-nonnegative-integerp
                                 ;; unsigned-byte-p-from-bounds
                                 unsigned-byte-p-of-+-of--1
                                 ;; unsigned-byte-p-forward
                                 ;;rule-alistp-means-alistp
                                 axe-bind-free-function-applicationp
                                 natp-of-+-of-1-and-largest-non-quotep
                                 <-of-largest-non-quotep
                                 ;; consp-when-true-listp-and-non-nil
                                 ;; rationalp-+
                                 ;; rationalp-unary--
                                 rationalp-when-integerp
                                 integerp-of-subtract-tries
                                 axe-rule-hypp
                                 stored-axe-rulep
                                 stored-axe-rule-listp
                                 true-listp-of-unify-terms-and-dag-items-fast
                                 (:type-prescription integerp-of-largest-non-quotep)
                                 (:type-prescription pseudo-term-listp)
                                 symbol-alistp-of-pairlis$-alt
                                 true-listp-of-cons
                                 axe-treep-when-consp-of-car
                                 <=-of--1-and-largest-non-quotep-linear ; not-<-of-largest-non-quotep-and--1
                                 integerp-when-natp
                                 pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-other
                                 integerp-of-maxelem2
                                 natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-type
                                 natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
                                 <-of-maxelem-when-all-<
                                 ,(pack$ relieve-free-var-hyp-and-all-others-name '-return-type)
                                 ,(pack$ relieve-rule-hyps-name '-return-type)
                                 ,(pack$ try-to-apply-rules-name '-return-type)
                                 ,(pack$ simplify-if-tree-name '-return-type)
                                 ,(pack$ simplify-boolif-tree-name '-return-type)
                                 ,(pack$ simplify-fun-call-name '-return-type)
                                 ,(pack$ simplify-tree-name '-return-type)
                                 ,(pack$ simplify-trees-name '-return-type)
                                 ,(pack$ relieve-rule-hyps-name '-return-type-corollary)
                                 ,(pack$ simplify-trees-name '-return-type-corollary)
                                 ,(pack$ simplify-trees-name '-return-type-corollary-linear)
                                 ,(pack$ simplify-tree-name '-return-type-corollary)
                                 ,(pack$ simplify-tree-name '-return-type-corollary-linear)
                                 ,(pack$ try-to-apply-rules-name '-return-type-corollary)
                                 ,(pack$ try-to-apply-rules-name '-return-type-corollary-linear)
                                 alist-suitable-for-hypsp-of-unify-terms-and-dag-items-fast-when-stored-axe-rulep
                                 alist-suitable-for-hypsp-when-axe-sytaxp-car
                                 alist-suitable-for-hypsp-of-append-and-cdr-when-axe-bind-free
                                 alist-suitable-for-hypsp-of-append-and-cdr-when-free-vars
                                 alist-suitable-for-hypsp-after-matching
                                 alist-suitable-for-hypsp-of-cdr-of-car-when-normal
                                 alist-suitable-for-hyp-tree-and-hypsp-after-instantiating
                                 subsetp-equal-of-free-vars-in-terms-of-fargs-of-cadr-of-car-when-axe-binding-hyp
                                 alist-suitable-for-hypsp-of-append-and-cdr-when-axe-binding-hyp
                                 subsetp-equal-of-free-vars-in-terms-of-fargs-of-cadr-of-car-when-axe-bind-free
                                 ,(pack$ 'axe-tree-vars-of- instantiate-hyp-free-vars-name)
                                 )
                    ;; :in-theory (e/d (bounded-axe-treep-when-natp-strong
                    ;;                  <-OF-+-OF-1-STRENGTHEN-2
                    ;;                  ;;<-OF-+-OF-1-WHEN-INTEGERS
                    ;;                  len-of-lambda-formals-when-axe-treep
                    ;;                  pseudo-termp-of-lambda-body-when-axe-treep
                    ;;                  axe-bind-free-result-okayp-rewrite
                    ;;                  <-of--1-when-natp)
                    ;;                 (myquotep
                    ;;                  natp
                    ;;                  ;; member-equal ;todo
                    ;;                  SYMBOL-LISTP ;avoid induction
                    ;;                  ))
                    )))

         ;; Rewrites the nodes in WORKLIST and all of their supporters.
         ;; Populates RESULT-ALIST with the nodenums/quoteps that the nodes in WORKLIST rewrote to.
         ;; Returns (mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
         ;; RESULT-ALIST maps nodenums to the nodenums or quoteps to which they rewrote, or nil if the node hasn't been touched.
         ;; it seems possible for a node to get pushed onto the worklist more than once, but i guess a node cannot be pushed more times than it has parents (so not exponentially many times)?
         ;; todo: watch out for equality assumptions ordered the wrong way! - will they get rewritten the wrong way?
         ;; todo: special handling for if/myif/boolif/bvif/boolor/booland?
         ;; todo: Consider whether we can track the equiv used for each node (note that a node may appear in multiple contexts with different equivs).  We currently handle this when we process the parent, and that may be good enough?
         ;; todo: track polarities?
         ;; todo: use a more modern worklist algorithm where we keep the worklist sorted?
         (defund ,rewrite-nodes-name (worklist ;could track the equivs and polarities?
                                      result-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                      rule-alist equiv-alist interpreted-function-alist
                                      print hit-counts tries monitored-symbols case-designator ;none of these should affect soundness
                                      prover-depth options count)
           (declare (xargs :guard (and (nat-listp worklist)
                                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (bounded-node-result-alistp result-alist dag-len)
                                       ;; (all-< worklist (alen1 result-array-name result-array))
                                       (all-< worklist dag-len)
                                       (nat-listp nodenums-to-assume-false1)
                                       (all-< nodenums-to-assume-false1 dag-len)
                                       (nat-listp nodenums-to-assume-false2)
                                       (all-< nodenums-to-assume-false2 dag-len)
                                       (assumption-arrayp 'assumption-array assumption-array)
                                       (natp assumption-array-num-valid-nodes)
                                       (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                       (rule-alistp rule-alist)
                                       (equiv-alistp equiv-alist)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (natp prover-depth)
                                       (simple-prover-optionsp options))
                           :guard-hints (("Goal" :in-theory (e/d ( ;dag-function-call-exprp
                                                                  dag-function-call-exprp-redef
                                                                  all-myquotep-when-darg-listp
                                                                  consp-of-cdr
                                                                  true-listp-of-cdr)
                                                                 (natp dag-function-call-exprp))
                                          :do-not '(generalize eliminate-destructors)
                                          :do-not-induct t))
                           :measure (+ 1 (nfix count))) ;todo: improve?
                    (type (unsigned-byte 59) count))
           (if (zp-fast count)
               (mv :count-exceeded result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
             (if (endp worklist)
                 (mv (erp-nil) result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               (let* ((nodenum (first worklist)))
                 (if (lookup-node-in-node-result-alist nodenum result-alist)
                     ;;we've already handled this node:
                     (,rewrite-nodes-name (rest worklist) result-alist
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                          rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols
                                          case-designator prover-depth options (+ -1 count))
                   (b* (;; (- (and (member-eq print '(:verbose! :verbose))
                        ;;         (cw "Processing node ~x0 (may have to process the args first).~%" nodenum)))
                        (expr (aref1 'dag-array dag-array nodenum)))
                     (if (atom expr) ;must be a variable - just see if its node needs to be replaced
                         ;; Have to use 'equal as the equiv here, unless we track equivs better, but we may do better when we analyze the parent node:
                         (let ((new-nodenum-or-quotep (maybe-replace-nodenum-using-assumption-array nodenum 'equal assumption-array assumption-array-num-valid-nodes print)))
                           (,rewrite-nodes-name (rest worklist)
                                                (update-node-result-alist nodenum new-nodenum-or-quotep result-alist) ;; either rewrote to itself or a constant from an equality assumption
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                rule-alist
                                                equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 count)))
                       (let ((fn (ffn-symb expr)))
                         (if (eq 'quote fn) ;; it's a quoted constant, so it rewrites to itself:
                             (,rewrite-nodes-name (rest worklist)
                                                  ;; update the result-alist (effectively eliminates the naked constant node):
                                                  (update-node-result-alist nodenum expr result-alist)
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                  rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 count))
                           ;; Regular function call or if:
                           (let* ((args (dargs expr))
                                  (extended-worklist-or-nil (get-unmapped-dargs args result-alist worklist nil)))
                             (if extended-worklist-or-nil
                                 ;; Some args are not yet done, so recur on the extended worklist (which has them added to the front).
                                 ;; When the current node is processed again, some analysis will be redone but we'll be in the case below (all args done):
                                 (,rewrite-nodes-name extended-worklist-or-nil result-alist
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                      rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols
                                                      case-designator prover-depth options (+ -1 count))
                               ;; All args have entries in the result-alist (but only for an equiv of 'equal):
                               (if (and (or (eq fn 'if) (eq fn 'myif))
                                        (mbe :exec (consp (cddr args)) ;should always be true
                                             :logic (< 2 (len args))))
                                   ;; It's an IF/MYIF:
                                   (let* ((simplified-test (lookup-darg-in-node-result-alist (first args) result-alist))
                                          ;; Possibly replace the test using an assumption (since we use 'iff as the equiv here, this may succeed even though the test has already been simplified using an equiv of 'equal):
                                          (simplified-test (if (consp simplified-test) ;check for quotep
                                                               simplified-test
                                                             ;; Can rewrite the test of an IF under 'iff:
                                                             (maybe-replace-nodenum-using-assumption-array simplified-test 'iff assumption-array assumption-array-num-valid-nodes print))))
                                     (if (consp simplified-test) ; check for quotep
                                         (if (unquote simplified-test)
                                             ;; The if-test rewrote to true, so the if rewrites to whatever its then-branch rewrote to:
                                             (,rewrite-nodes-name (rest worklist)
                                                                  (update-node-result-alist nodenum (lookup-darg-in-node-result-alist (second args) result-alist) result-alist)
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                  nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                  rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 count))
                                           ;; The if-test rewrote to false, so the if rewrites to whatever its else-branch rewrote to:
                                           (,rewrite-nodes-name (rest worklist)
                                                                (update-node-result-alist nodenum (lookup-darg-in-node-result-alist (third args) result-alist) result-alist)
                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 count)))
                                       ;; The if-test was not resolved (we also therefore know that we don't have a ground term):
                                       (b* (((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                             (,simplify-fun-call-name
                                              fn ; if or myif
                                              ;; btw, since simplified-test was not a cons, we know it wasn't changed by maybe-replace-nodenum-using-assumption-array, which, at least for now, can only put in a constant:
                                              (cons-with-hint simplified-test
                                                              (lookup-dargs-in-node-result-alist (rest args) result-alist) ;or just call lookup-darg-in-node-result-alist twice?
                                                              args)
                                              'equal ; best we can do for now
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alist
                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                              equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                              0 ;todo: think about this
                                              case-designator prover-depth options count))
                                            ((when erp) (mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                                         (,rewrite-nodes-name (rest worklist)
                                                              (update-node-result-alist nodenum new-nodenum-or-quotep result-alist)
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                              rule-alist equiv-alist interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 count)))))
                                 (if (eq fn 'boolif)
                                     (b* ((simplified-args (lookup-dargs-in-node-result-alist args result-alist))
                                          (expr (cons fn simplified-args)) ; todo: consider cons-with-hint here, or avoid this cons
                                          ;; (- (and (member-eq print '(:verbose! :verbose))
                                          ;;         (cw "(Rewriting node ~x0." nodenum)))
                                          ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                           ;; TODO: Optimize this.  Calling ,simplify-tree-name here is overkill.  See what we do for if/myif above, but we do need to deal with the possibility of adding a bool-fix here.
                                           (,simplify-tree-name expr
                                                                'equal ; can't do better than this unless we pass in an equiv
                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                rule-alist
                                                                nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                equiv-alist print
                                                                hit-counts tries interpreted-function-alist monitored-symbols
                                                                0 ;todo: think about this
                                                                case-designator prover-depth options (+ -1 count)))
                                          ((when erp) (mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                                       (,rewrite-nodes-name (rest worklist)
                                                            (update-node-result-alist nodenum new-nodenum-or-quotep result-alist)
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                            rule-alist equiv-alist interpreted-function-alist print hit-counts tries
                                                            monitored-symbols case-designator prover-depth options (+ -1 count)))
                                   ;; TODO: Should we add special handling for bvif?
                                   ;; Not an any kind of IF:
                                   (b* ((simplified-args (lookup-dargs-in-node-result-alist args result-alist)) ;todo: combine this with the maybe-replace below
                                        (equivs (get-equivs 'equal fn equiv-alist))
                                        ;; we could avoid this check if we know that arities were right:
                                        ((when (and equivs ;; (not (equal :equal equivs))
                                                    (not (= (len equivs) (len simplified-args)))))
                                         (mv :bad-equivs result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                                        ;; Try to replace the args now that we may know stronger equivs than equal:
                                        (simplified-args (if equivs
                                                             (maybe-replace-args-using-assumption-array simplified-args equivs assumption-array assumption-array-num-valid-nodes print)
                                                           simplified-args))
                                        ;; Handle possible ground term (TODO: This duplicates code surrounding another call of ,simplify-fun-call-name. We could make a separate function that handles ground terms and then calls ,simplify-fun-call-name and call it both here and there?  Or at least carve out this ground term code itself):
                                        ((mv erp evaluatedp val)
                                         (if (not (all-consp simplified-args)) ;; test for args being quoted constants
                                             ;; not a ground term:
                                             (mv (erp-nil) nil nil)
                                           ;; ground term, so try to evaluate:
                                           (b* (((mv erp val)
                                                 (,apply-axe-evaluator-to-quoted-args-name fn simplified-args interpreted-function-alist)))
                                             (if erp
                                                 (if (call-of :unknown-function erp)
                                                     (mv (erp-nil) nil nil) ;no error, but it didn't produce a value (todo: print a warning?)
                                                   ;; anything else non-nil is a true error:
                                                   (mv erp nil nil))
                                               ;; normal case, evaluation worked:
                                               (mv (erp-nil) t val)))))
                                        ;; I suppose we could suppress any evaluator error here if we choose to (might be a bit faster)?
                                        ((when erp) (mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                                     (if evaluatedp
                                         ;; We evaluated the ground term:
                                         (,rewrite-nodes-name (rest worklist)
                                                              (update-node-result-alist nodenum (enquote val) result-alist)
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                              rule-alist equiv-alist interpreted-function-alist print hit-counts tries
                                                              monitored-symbols case-designator prover-depth options (+ -1 count))
                                       ;; Not a ground term we could evaluate:
                                       (b* (;; (- (and (member-eq print '(:verbose! :verbose))
                                            ;;         (cw "(Rewriting node ~x0." nodenum)))
                                            ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                                             (,simplify-fun-call-name fn
                                                                      simplified-args
                                                                      'equal ; best we can do for now
                                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                      rule-alist
                                                                      nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                                      equiv-alist print hit-counts tries interpreted-function-alist monitored-symbols
                                                                      0 ;todo: think about this
                                                                      case-designator prover-depth options count))
                                            ((when erp) (mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                                         (,rewrite-nodes-name (rest worklist)
                                                              (update-node-result-alist nodenum new-nodenum-or-quotep result-alist)
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                              rule-alist equiv-alist interpreted-function-alist print hit-counts tries
                                                              monitored-symbols case-designator prover-depth options (+ -1 count))))))))))))))))))

         ;; (defthm ,(pack$ rewrite-nodes-name '-return-type-helper)
         ;;   (implies (and (nat-listp worklist)
         ;;                 (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
         ;;                 (result-arrayp result-array-name result-array dag-len)
         ;;                 (all-< worklist (alen1 result-array-name result-array))
         ;;                 (all-< worklist dag-len)
         ;;                 (nat-listp nodenums-to-assume-false)
         ;;                 (all-< nodenums-to-assume-false dag-len)
         ;;                 (assumption-arrayp 'assumption-array assumption-array)
         ;;                 (natp assumption-array-num-valid-nodes)
         ;;                 (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
         ;;                 (rule-alistp rule-alist)
         ;;                 (equiv-alistp equiv-alist)
         ;;                 (interpreted-function-alistp interpreted-function-alist)
         ;;                 (hit-countsp hit-counts)
         ;;                 (triesp tries)
         ;;                 (symbol-listp monitored-symbols)
         ;;                 (stringp case-designator)
         ;;                 (natp prover-depth)
         ;;                 (simple-prover-optionsp options))
         ;;            (mv-let (erp new-result-array new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
         ;;              (,rewrite-nodes-name worklist result-array-name result-array
         ;;                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                   nodenums-to-assume-false assumption-array assumption-array-num-valid-nodes
         ;;                                   rule-alist equiv-alist interpreted-function-alist
         ;;                                   print hit-counts tries monitored-symbols case-designator
         ;;                                   prover-depth options count)
         ;;              (declare (ignore new-result-array new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
         ;;              (implies (not erp)
         ;;                       (<= dag-len new-dag-len))))
         ;;   :hints (("Goal" :induct t
         ;;            :do-not '(generalize eliminate-destructors)
         ;;            :in-theory (e/d (,rewrite-nodes-name
         ;;                             dag-function-call-exprp-redef
         ;;                             all-myquotep-when-darg-listp
         ;;                             consp-of-cdr)
         ;;                            (natp dag-function-call-exprp)))))

         (defthm ,(pack$ rewrite-nodes-name '-return-type)
           (implies (and (nat-listp worklist)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-node-result-alistp result-alist dag-len)
                         ;; (all-< worklist (alen1 result-array-name result-array))
                         (all-< worklist dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (rule-alistp rule-alist)
                         (equiv-alistp equiv-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-result-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-nodes-name worklist result-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                           rule-alist equiv-alist interpreted-function-alist
                                           print hit-counts tries monitored-symbols case-designator ;none of these should affect soundness
                                           prover-depth options count)
                      (implies (not erp)
                               (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (bounded-node-result-alistp new-result-alist new-dag-len)
                                    (node-result-alistp new-result-alist) ;redundant
                                    ;; (array1p result-array-name new-result-array) ;avoid an issue with a free var when backchaining from array1p to result-arrayp
                                    ;; (equal (alen1 result-array-name new-result-array)
                                    ;;        (alen1 result-array-name result-array))
                                    (<= dag-len new-dag-len)
                                    (hit-countsp hit-counts)
                                    (triesp tries)))))
           :hints (("Goal" :induct t
                    :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-nodes-name
                                     dag-function-call-exprp-redef
                                     all-myquotep-when-darg-listp
                                     consp-of-cdr)
                                    (natp dag-function-call-exprp)))))

         ;; Rewrites only the top expression in the literal at NODENNUM (except we strip a not if needed, to get to the interesting part of the literal).
         ;; Does not rewrite supporting nodes!
         ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
         (defund ,rewrite-single-node-name (nodenum
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist
                                            nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                            equiv
                                            equiv-alist ;don't pass this around?
                                            print
                                            hit-counts tries interpreted-function-alist monitored-symbols case-designator prover-depth options)
           (declare (xargs :guard (and (natp nodenum)
                                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (< nodenum dag-len)
                                       (rule-alistp rule-alist)
                                       (nat-listp nodenums-to-assume-false1)
                                       (all-< nodenums-to-assume-false1 dag-len)
                                       (nat-listp nodenums-to-assume-false2)
                                       (all-< nodenums-to-assume-false2 dag-len)
                                       (assumption-arrayp 'assumption-array assumption-array)
                                       (natp assumption-array-num-valid-nodes)
                                       (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                       (equivp equiv)
                                       (equiv-alistp equiv-alist)
                                       ;; print
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (natp prover-depth)
                                       (simple-prover-optionsp options))
                           :guard-hints (("Goal" :in-theory (enable dag-function-call-exprp-when-dag-exprp not-equal-of-len-and-1-when-dargp car-when-dargp)))))
           (b* (;; Try to extract the core function symbol and args for the top node (stripping a not if present):
                (expr (aref1 'dag-array dag-array nodenum))
                ((mv fun-callp fn dargs negatedp) ; if fun-callp is nil, other vars are meaningless
                 (if (or (variablep expr)
                         (quotep expr))
                     (mv nil nil nil nil) ; no rule matches a constant or variable
                   ;; it's a function call, but we might need to strip a not:
                   (if (and (eq 'not (ffn-symb expr))
                            (consp (dargs expr))     ; for the guard proof
                            (not (consp (darg1 expr))) ; ensures it's a nodenum
                            )
                       ;; Strip the not:
                       (let* ((expr (aref1 'dag-array dag-array (darg1 expr))))
                         (if (or (variablep expr)
                                 (quotep expr))
                             (mv nil nil nil nil) ; no rule matches a constant or variable
                           (mv t (ffn-symb expr) (dargs expr) t)))
                     ;; not a call of not:
                     (mv t (ffn-symb expr) (dargs expr) nil))))
                ((when (not fun-callp)) (mv nil nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)) ; no change (rare)
                ;; Simplify the core expr, including rewriting hyps and the RHS, but don't simplify the dargs:
                ((mv erp new-core-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 (,simplify-fun-call-name fn
                                          dargs ; these do not get simplified
                                          equiv
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist
                                          nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                          equiv-alist print
                                          hit-counts tries interpreted-function-alist monitored-symbols
                                          0 ;todo: think about this
                                          case-designator prover-depth options
                                          1000000000 ; todo
                                          ))
                ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
             (if (not negatedp)
                 ;; We did not strip a not above, so no need to negate the result:
                 (mv nil
                     new-core-nodenum-or-quotep ; the core is the whole thing
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
               ;; Must negate the result (todo: optimize if rewriting did nothing?)
               (if (consp new-core-nodenum-or-quotep) ; check for quotep
                   (mv nil (enquote (not (unquote new-core-nodenum-or-quotep))) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 ;; new-core-nodenum-or-quotep is a nodenum, so add its negation to the dag and return that:
                 (b* (((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                       (add-function-call-expr-to-dag-array 'not (list new-core-nodenum-or-quotep) dag-array dag-len dag-parent-array dag-constant-alist))
                      ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                   (mv nil new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))))))

         (defthm ,(pack$ rewrite-single-node-name '-return-type)
           (implies (and (natp nodenum)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (< nodenum dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (equivp equiv)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-single-node-name nodenum
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 rule-alist
                                                 nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                                 equiv
                                                 equiv-alist ;don't pass this around?
                                                 print
                                                 hit-counts tries interpreted-function-alist monitored-symbols case-designator prover-depth options)
                      (implies (not erp)
                               (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (hit-countsp hit-counts)
                                    (triesp tries)
                                    (dargp-less-than new-nodenum-or-quotep new-dag-len)))))
           :hints (("Goal" :in-theory (e/d (,rewrite-single-node-name
                                            natp-when-dargp
                                            <-when-dargp-less-than)
                                           (natp dargp-less-than)))))

         ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries assumption-array).
         ;; It would be nice to call a standard rewriter here, but the assumptions (nodenums-to-assume-false) are likely not in the right form.
         ;; The assumption-array returned has been changed but then changed back.
         ;; TODO: can we use a better equiv?
         ;; TODO: Inline this?
         (defund ,rewrite-literal-name (nodenum ;; should have no extractable disjuncts
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                        rule-alist interpreted-function-alist
                                        hit-counts tries monitored-symbols print case-designator ;none of these should affect soundness
                                        prover-depth
                                        known-booleans options top-node-onlyp)
           (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (natp nodenum)
                                       (< nodenum dag-len)
                                       (nat-listp nodenums-to-assume-false1)
                                       (all-< nodenums-to-assume-false1 dag-len)
                                       (nat-listp nodenums-to-assume-false2)
                                       (all-< nodenums-to-assume-false2 dag-len)
                                       (assumption-arrayp 'assumption-array assumption-array)
                                       (natp assumption-array-num-valid-nodes)
                                       (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                       (< nodenum assumption-array-num-valid-nodes)
                                       (rule-alistp rule-alist)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (simple-prover-optionsp options)
                                       (booleanp top-node-onlyp))))
           (b* ((- (and (or (eq :verbose print) (eq :verbose! print))
                        (cw "(Rewriting literal ~x0.~%" nodenum)))
                ;; See what info this literal contributed to the assumption-array:
                ((mv assumption-nodenum assumption-item)
                 (assumption-array-info-for-literal nodenum dag-array dag-len known-booleans print))
                ;; Clear out the assumption info from this node, so we don't use it to rewrite this literal to true:
                ;; Note that the index used here may not be the nodenum of the literal:
                (assumption-array (aset1 'assumption-array assumption-array assumption-nodenum nil)) ; has info from all literals except this one
                ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 (if (not top-node-onlyp)
                     ;; normal case:
                     (b* (;; ;; Make an array to track results in the worklist algorithm.  We
                          ;; ;; expect the raw Lisp array previously allocated in
                          ;; ;; ,rewrite-clause-name to be reused each time, since it will
                          ;; ;; always be big enough:
                          ;; (result-array (make-empty-array result-array-name (+ 1 nodenum) ;dag-len
                          ;;                                 ))
                          (result-alist nil) ; will become a fast-alist when we do the first hons-acons
                          ;; Rewrite this literal:
                          ((mv erp result-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                           ;; TODO: would it make sense to memoize in this?
                           (,rewrite-nodes-name (list nodenum)
                                                result-alist
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                nodenums-to-assume-false1 nodenums-to-assume-false2
                                                assumption-array assumption-array-num-valid-nodes
                                                rule-alist
                                                *equiv-alist* ;do we need to pass this around?
                                                interpreted-function-alist print hit-counts tries monitored-symbols case-designator prover-depth options (+ -1 (expt 2 59))))
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                          (new-nodenum-or-quotep (lookup-node-in-node-result-alist nodenum result-alist))
                          (- (fast-alist-free result-alist)) ; removes the hash table
                          ((when (not new-nodenum-or-quotep)) ;todo: prove that this can't happen
                           (er hard? ',rewrite-literal-name "Literal did not rewrite to anything!")
                           (mv :error nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                       (mv nil new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                   ;; only rewrite the top node:
                   (,rewrite-single-node-name nodenum
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alist
                                              nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                              'iff ; since we are rewriting a literal (or its core after stripping a not), we only have to preserve iff
                                              *equiv-alist* ;don't pass this around?
                                              print
                                              hit-counts tries interpreted-function-alist monitored-symbols case-designator prover-depth options)))
                ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries assumption-array))
                (- (and (or (eq :verbose print) (eq :verbose! print))
                        (cw "  Done rewriting literal ~x0.)~%" nodenum)))
                ;; Restore the information that was cleared out of the assumption array:
                (assumption-array (aset1 'assumption-array assumption-array assumption-nodenum assumption-item)))
             (mv (erp-nil)
                 new-nodenum-or-quotep
                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                 hit-counts tries assumption-array)))

         (defthm ,(pack$ rewrite-literal-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (< nodenum assumption-array-num-valid-nodes)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries new-assumption-array)
                      (,rewrite-literal-name nodenum
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                             rule-alist interpreted-function-alist
                                             hit-counts tries monitored-symbols print case-designator ;none of these should affect soundness
                                             prover-depth known-booleans options top-node-onlyp)
                      (implies (not erp)
                               (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (hit-countsp hit-counts)
                                    (triesp tries)
                                    (dargp-less-than new-nodenum-or-quotep new-dag-len)
                                    (assumption-arrayp 'assumption-array new-assumption-array)
                                    (equal (alen1 'assumption-array new-assumption-array)
                                           (alen1 'assumption-array assumption-array))))))
           :hints (("Goal" :in-theory (e/d (,rewrite-literal-name
; type-of-aref1-when-result-arrayp-2
                                            )
                                           (natp)))))

         (defthm ,(pack$ rewrite-literal-name '-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (< nodenum assumption-array-num-valid-nodes)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries assumption-array)
                      (,rewrite-literal-name nodenum
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                             rule-alist interpreted-function-alist
                                             hit-counts tries monitored-symbols print case-designator ;none of these should affect soundness
                                             prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore new-nodenum-or-quotep new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries assumption-array))
                      (implies (not erp)
                               (natp new-dag-len))))
           :hints (("Goal" :use (:instance ,(pack$ rewrite-literal-name '-return-type))
                    :in-theory (disable ,(pack$ rewrite-literal-name '-return-type)))))

         (defthm ,(pack$ rewrite-literal-name '-return-type-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp nodenums-to-assume-false1)
                         (all-< nodenums-to-assume-false1 dag-len)
                         (nat-listp nodenums-to-assume-false2)
                         (all-< nodenums-to-assume-false2 dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (< nodenum assumption-array-num-valid-nodes)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries assumption-array)
                      (,rewrite-literal-name nodenum
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nodenums-to-assume-false1 nodenums-to-assume-false2 assumption-array assumption-array-num-valid-nodes
                                             rule-alist interpreted-function-alist
                                             hit-counts tries monitored-symbols print case-designator ;none of these should affect soundness
                                             prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore new-nodenum-or-quotep new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries assumption-array))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ rewrite-literal-name '-return-type))
                    :in-theory (disable ,(pack$ rewrite-literal-name '-return-type)))))

         ;; Rewrite each of the literals in WORK-LIST once, and add the results to DONE-LIST.  When rewriting a literal, assume all
         ;; other literals (from WORK-LIST and DONE-LIST) false.
         ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries),
         ;; where if PROVEDP is t, then the disjunction of WORK-LIST and DONE-LIST was proved to be non-nil,
         ;; and if PROVEDP is nil, then that disjunction is equivalent to the LITERAL-NODENUMS returned.
         ;; If provedp is non-nil, changep is meaningless..
         ;; Not a worklist algorithm of the usual sort (all elements of work-list are literals).
         ;; May extend the dag but doesn't change any nodes (new!).
         ;; TODO: If the only change is that some literals were dropped, perhaps we don't want to make another pass?
         (defund ,rewrite-literals-name (work-list ;a list of nodenums, with no extractable disjuncts
                                         done-list ;a list of nodenums, with no extractable disjuncts
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         assumption-array assumption-array-num-valid-nodes
                                         changep ;; whether anything has changed so far
                                         rule-alist
                                         interpreted-function-alist monitored-symbols print case-designator
                                         hit-counts tries prover-depth
                                         known-booleans options top-node-onlyp)
           (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (nat-listp work-list)
                                       (all-< work-list dag-len)
                                       (assumption-arrayp 'assumption-array assumption-array)
                                       (natp assumption-array-num-valid-nodes)
                                       (all-< work-list assumption-array-num-valid-nodes)
                                       (nat-listp done-list)
                                       (all-< done-list dag-len)
                                       (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                                       (booleanp changep)
                                       (rule-alistp rule-alist)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (symbol-listp monitored-symbols)
                                       ;; print
                                       (stringp case-designator)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (simple-prover-optionsp options)
                                       (booleanp top-node-onlyp))
                           :guard-hints (("Goal" :do-not-induct t))))
           (if (endp work-list)
               (progn$ (and (member-eq print '(t :verbose :verbose!))
                            (print-axe-prover-case done-list 'dag-array dag-array dag-len "rewritten" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options)))
                       (mv (erp-nil)
                           nil ;did not prove the clause
                           changep done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
             (b* ((literal-nodenum (first work-list))
                  (rest-work-list (rest work-list))
                  ;; (nodenums-to-assume-false (append rest-work-list done-list)) ;todo: save this append when no rules have free vars?  or pass this in 2 pieces?
                  ;; Rewrite the literal:
                  ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries assumption-array)
                   (,rewrite-literal-name literal-nodenum
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rest-work-list ; nodenums-to-assume-false1 (we avoid appending these 2, for speed since they may be large)
                                          done-list ; nodenums-to-assume-false2
                                          assumption-array assumption-array-num-valid-nodes
                                          rule-alist interpreted-function-alist hit-counts tries monitored-symbols print case-designator prover-depth known-booleans options top-node-onlyp))
                  ((when erp) (mv erp nil nil done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                  ;; (- (cw "Node ~x0 rewrote to ~x1 in dag:~%" literal-nodenum new-nodenum-or-quotep))
                  ;; (- (if (quotep new-nodenum-or-quotep) (cw ":elided") (if (eql literal-nodenum new-nodenum-or-quote) :no-change (print-dag-array-node-and-supporters 'dag-array dag-array new-nodenum-or-quotep))))
                  )
               (if (eql new-nodenum-or-quotep literal-nodenum)
                   ;; No change for this literal:
                   (,rewrite-literals-name rest-work-list
                                           (cons literal-nodenum done-list)
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           assumption-array assumption-array-num-valid-nodes
                                           changep ;; no change to changep
                                           rule-alist interpreted-function-alist monitored-symbols print case-designator hit-counts tries prover-depth known-booleans options top-node-onlyp)
                 ;; Rewriting changed the literal.  Harvest the disjuncts, raising them to top level, and add them to the done-list:
                 (b* (((mv erp provedp extended-done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       (get-darg-disjuncts new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           done-list ; will be extended with the disjuncts
                                           nil       ;negated-flg
                                           print))
                      ;; TODO: Should we use the assumption-array to check for redundant disjuncts and drop them?  Should
                      ;; we use the assumption-array to check for contradictions?  In either case we might want to use the
                      ;; assumption-array without the information from this literal??  TODO: Should we use the new
                      ;; disjuncts to add information to the assumption-array?
                      ((when erp) (mv erp nil nil done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
                   (if provedp
                       (mv (erp-nil)
                           t ;provedp
                           t ;changep
                           nil ;literal-nodenums
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                     ;; Continue rewriting literals:
                     (,rewrite-literals-name rest-work-list
                                             extended-done-list
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             assumption-array assumption-array-num-valid-nodes
                                             t ;; something changed
                                             rule-alist interpreted-function-alist monitored-symbols print case-designator hit-counts tries prover-depth known-booleans options top-node-onlyp)))))))

         (defthm ,(pack$ rewrite-literals-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp work-list)
                         (all-< work-list dag-len)
                         (nat-listp done-list)
                         (all-< done-list dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (all-< work-list assumption-array-num-valid-nodes)
                         (booleanp changep)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         ;; print
                         (stringp case-designator)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-literals-name work-list
                                              done-list
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              assumption-array assumption-array-num-valid-nodes
                                              changep
                                              rule-alist
                                              interpreted-function-alist monitored-symbols print case-designator
                                              hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (implies (not erp)
                               (and (booleanp provedp)
                                    (booleanp changep)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (hit-countsp hit-counts)
                                    (triesp tries)
                                    (nat-listp literal-nodenums)
                                    (all-< literal-nodenums new-dag-len)))))
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :induct t
                    :in-theory (e/d (,rewrite-literals-name) (natp)))))

         (defthm ,(pack$ rewrite-literals-name '-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp work-list)
                         (all-< work-list dag-len)
                         (nat-listp done-list)
                         (all-< done-list dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (all-< work-list assumption-array-num-valid-nodes)
                         (booleanp changep)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         ;; print
                         (stringp case-designator)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-literals-name work-list
                                              done-list
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              assumption-array assumption-array-num-valid-nodes
                                              changep
                                              rule-alist
                                              interpreted-function-alist monitored-symbols print case-designator
                                              hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore provedp changep literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (pseudo-dag-arrayp 'dag-array new-dag-array new-dag-len))))
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-literals-name) (natp)))))

         ;; This one is a :type-prescription rule
         (defthm ,(pack$ rewrite-literals-name '-return-type-2)
           (implies (true-listp done-list)
                    (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-literals-name work-list
                                              done-list
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              assumption-array assumption-array-num-valid-nodes
                                              changep
                                              rule-alist
                                              interpreted-function-alist monitored-symbols print case-designator
                                              hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (true-listp literal-nodenums)))
           :rule-classes :type-prescription
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-literals-name) (natp)))))

         ;; This one is a :linear rule
         (defthm ,(pack$ rewrite-literals-name '-return-type-corollary-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp work-list)
                         (all-< work-list dag-len)
                         (nat-listp done-list)
                         (all-< done-list dag-len)
                         (assumption-arrayp 'assumption-array assumption-array)
                         (natp assumption-array-num-valid-nodes)
                         (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array))
                         (all-< work-list assumption-array-num-valid-nodes)
                         (booleanp changep)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         ;; print
                         (stringp case-designator)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (natp prover-depth)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries)
                      (,rewrite-literals-name work-list
                                              done-list
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              assumption-array assumption-array-num-valid-nodes
                                              changep
                                              rule-alist
                                              interpreted-function-alist monitored-symbols print case-designator
                                              hit-counts tries prover-depth known-booleans options top-node-only)
                      (declare (ignore provedp changep literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist hit-counts tries))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-literals-name) (natp)))))

         ;; TODO: It would be nice to prove this:
         ;; (defthm ,(pack$ 'no-duplicatesp-equal-of-mv-nth-3-of- rewrite-literals-name)
         ;;   (implies (and (no-duplicatesp-equal work-list)
         ;;                 (no-duplicatesp-equal done-list)
         ;;                 (not (intersection-equal work-list done-list)))
         ;;            (no-duplicatesp-equal (mv-nth 3 (,rewrite-literals-name work-list
         ;;                                                                    done-list
         ;;                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                                                    assumption-array assumption-array-num-valid-nodes
         ;;                                                                    changep
         ;;                                                                    rule-alist
         ;;                                                                    interpreted-function-alist monitored-symbols print case-designator
         ;;                                                                    hit-counts tries prover-depth known-booleans options))))
         ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
         ;;            :in-theory (e/d (,rewrite-literals-name not-member-equal-of-car-when-not-intersection-equal) (natp intersection-equal)))))

         ;; Rewrite each literal once.  This is separate to keep the caller smaller and simpler.
         ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries).
         (defund ,rewrite-clause-name (literal-nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist
                                       rule-set-number
                                       interpreted-function-alist monitored-symbols
                                       case-designator print ;move print arg?
                                       hit-counts tries prover-depth known-booleans options top-node-onlyp)
           (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (nat-listp literal-nodenums)
                                       (consp literal-nodenums)
                                       (all-< literal-nodenums dag-len)
                                       (rule-alistp rule-alist)
                                       (natp rule-set-number)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (simple-prover-optionsp options)
                                       (booleanp top-node-onlyp))
                           :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-strengthen-2 natp-of-+-of-1 rationalp-when-natp ;symbol-alistp-when-hit-countsp
                                                                                           )
                                                                 (natp))
                                          :do-not-induct t))))
           (b* (;; TODO: Do this in the callers?  Maintain an invariant about disjuncts having been extracted from literal-nodenums?  May not be true after we substitute, so do this there instead?
                ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (get-disjuncts-from-nodes literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nil print))
                ((when erp) (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                ((when provedp) (mv (erp-nil) t t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                ((when (not (consp literal-nodenums)))
                 (and print (cw "NOTE: No literals after getting disjuncts.~%"))
                 ;; No error but did not prove (did make a change because there at least one literal was passed in):
                 (mv (erp-nil) nil t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                ;; Make the assumption-array:
                ((mv provedp literal-nodenums assumption-array)
                 (make-assumption-array literal-nodenums dag-array dag-len known-booleans print))
                ((when provedp)
                 (and print (cw "NOTE: Proved due to contradiction in assumptions.~%"))
                 (mv (erp-nil) t t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                (- (and print (cw "(Rewriting with rule set ~x0 (~x1 literals, ~x2 DAG nodes):~%" rule-set-number (len literal-nodenums) dag-len))) ;the printed paren is closed below
                ;; (print-hit-countsp (member-eq print '(t :verbose :verbose!)))
                ;; (hit-count-alist-before (and print-hit-countsp (make-hit-count-alist hit-counts)))
                ;; (result-array-name (pack$ 'result-array- prover-depth))
                ;; Ensure there is a maximal size raw Lisp array under the hood, for use when rewriting each literal.  I hope the compiler
                ;; doesn't optimize this away:
                ;; (- (make-empty-array result-array-name dag-len))
                ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                 (,rewrite-literals-name literal-nodenums
                                         nil ;initial done-list
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         assumption-array
                                         dag-len ;assumption-array-num-valid-nodes
                                         nil     ;changep
                                         rule-alist
                                         interpreted-function-alist monitored-symbols print case-designator
                                         hit-counts tries prover-depth known-booleans options top-node-onlyp))
                ((when erp) (mv erp nil t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                ;; (hit-count-alist-after (and print-hit-countsp (make-hit-count-alist hit-counts)))
                ;; (hit-count-alist (and print-hit-countsp (sort-hit-count-alist (subtract-hit-count-alists hit-count-alist-after hit-count-alist-before))))
                ;; (- (and print-hit-countsp (cw "(Hits: ~x0)~%" hit-count-alist))) ; or check whether we are counting hits
                ((when provedp)
                 (and print (cw "  Rewriting proved case ~s0.)~%" case-designator))
                 (mv (erp-nil)
                     t ;proved the clause
                     t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                ((when (not (consp literal-nodenums)))
                 (and print (cw "No literals left after rewriting.)~%"))
                 ;; No error, did not prove, did make a change:
                 (mv (erp-nil) nil t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries))
                (- (and (member-eq print '(t :verbose :verbose!))
                        (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "rewritten" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options))))
                (- (and print (cw "  Done rewriting (~x0 literals).)~%" (len literal-nodenums)))) ; todo: move down after crunching?
                ;; Maybe crunch (one advantage in doing this is to make the printed result of this step comprehensible if we are tracing):
                ;; TODO: Do we want to do this if changep is nil (perhaps yes, since nodes may have been created when relieving hyps even if no dag node was changed by a successful rule)?
                ;; TODO: Move this to happen before we rewrite?  Or always crunch between phases?
                (crunchp (= prover-depth 0)) ;; can't crunch if prover-depth > 0 since that would change existing nodes:
                ((mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (maybe-crunch-dag-array2 crunchp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                ((when erp)
                 (mv erp nil t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))
             (mv (erp-nil)
                 nil ; didn't prove the clause
                 changep
                 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)))

         (defthm ,(pack$ rewrite-clause-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries)
                      (,rewrite-clause-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (implies (not erp)
                               (and (booleanp provedp)
                                    (booleanp changep)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (implies (< 0 prover-depth)
                                             (<= dag-len new-dag-len))
                                    (nat-listp new-literal-nodenums)
                                    (all-< new-literal-nodenums new-dag-len)
                                    (hit-countsp new-hit-counts)
                                    (triesp new-tries)))))
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-clause-name) (natp)))))

         (defthm ,(pack$ rewrite-clause-name '-return-type-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries)
                      (,rewrite-clause-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore provedp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries))
                      (implies (not erp)
                               (implies (< 0 prover-depth)
                                        (<= dag-len new-dag-len)))))
           :rule-classes :linear
           :hints (("Goal" :use ,(pack$ rewrite-clause-name '-return-type)
                    :in-theory (disable ,(pack$ rewrite-clause-name '-return-type)))))

         (defthm ,(pack$ rewrite-clause-name '-return-type-2)
           (implies (true-listp literal-nodenums)
                    (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries)
                      (,rewrite-clause-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries))
                      (true-listp  new-literal-nodenums)))
           :rule-classes :type-prescription
           :hints (("Goal" :do-not '(generalize eliminate-destructors)
                    :in-theory (e/d (,rewrite-clause-name) (natp)))))

         (defthm ,(pack$ rewrite-clause-name '-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp known-booleans)
                         ;; (simple-prover-optionsp options)
                         )
                    (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries)
                      (,rewrite-clause-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans options top-node-onlyp)
                      (declare (ignore provedp changep new-literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries))
                      (implies (not erp)
                               (pseudo-dag-arrayp 'dag-array new-dag-array new-dag-len))))
           :hints (("Goal" :use (:instance ,(pack$ rewrite-clause-name '-return-type))
                    :in-theory (disable ,(pack$ rewrite-clause-name '-return-type)))))

         (mutual-recursion

           ;; Apply the given tactic.
           ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state).
           ;; where if provedp is non-nil we proved the clause and the other return values are irrelevant.
           ;; otherwise, we return the simplified clause (as the list of literal nodenums and the dag-array, etc.)
           ;; There should be no harvestable disjuncts in the LITERAL-NODENUMS returned?  The LITERAL-NODENUMS returned may be empty.
           ;; In general, this can loop (e.g., due to looping rules), so we use a count to ensure termination.
           (defund ,apply-tactic-name (tactic
                                       literal-nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist rule-set-number
                                       interpreted-function-alist monitored-symbols
                                       case-designator print ;move print arg?
                                       hit-counts tries prover-depth known-booleans var-ordering options count state)
             (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (rule-alistp rule-alist)
                                         (natp rule-set-number)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (stringp case-designator)
                                         (print-levelp print)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options))
                             :stobjs state
                             :verify-guards nil ; done below
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               (if (not (consp literal-nodenums))
                   ;; No error but didn't prove:
                   (prog2$ (cw "NOTE: No literals.~%")
                           (mv (erp-nil) nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                 ;; Each tactic here can assume (consp literal-nodenums) if need:
                 (cond ((member-eq tactic '(:rewrite :rewrite-top))
                        ;; TODO: After rewriting, we could drop any literal of the form (equal <constant> <var>) - if the var appears in any other literal, rewriting should have put in the constant for it, so the var will no longer appear.
                        (b* (((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries)
                              (,rewrite-clause-name literal-nodenums
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    rule-alist rule-set-number
                                                    interpreted-function-alist monitored-symbols
                                                    case-designator print
                                                    hit-counts tries prover-depth known-booleans options
                                                    (eq tactic :rewrite-top))))
                          (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                       ((eq :subst tactic)
                        (b* ((- (and print (cw "(Substituting:~%")))
                             ;; (subst-candidates (subst-candidates literal-nodenums dag-array dag-len nil)) ;only used for printing the count, for now
                             ;; (- (cw "~x0 subst candidates.~%" (len subst-candidates)))
                             ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                              (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth
                                                (if (posp dag-len) ;todo: should always be true
                                                    dag-len
                                                  1)
                                                var-ordering
                                                nil))
                             ((when erp)
                              (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                             ((when provedp)
                              (mv (erp-nil) t nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                             (- (and print (cw "  Done substituting. ~x0 literals left.)~%" (len literal-nodenums))))
                             (- (and (member-eq print '(t :verbose :verbose!))
                                     (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "after subst" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options)))))
                          (mv (erp-nil)
                              nil ;provedp
                              changep
                              literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                       ((eq :elim tactic)
                        (b* (((mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                              ;; TODO: Consider eliminating more than one tuple here, if possible
                              (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                             ((when erp) (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                          (mv (erp-nil)
                              nil ;provedp
                              changep
                              literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                       ((call-of :seq tactic)
                        (,apply-tactics-name (fargs tactic)
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alist rule-set-number
                                             interpreted-function-alist monitored-symbols
                                             case-designator print
                                             hit-counts tries prover-depth known-booleans var-ordering options
                                             nil ; no change yet
                                             (+ -1 count) state))
                       ((call-of :rep tactic)
                        (,apply-rep-tactic-name (fargs tactic)
                                                literal-nodenums
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                rule-alist rule-set-number
                                                interpreted-function-alist monitored-symbols
                                                case-designator print
                                                hit-counts tries prover-depth known-booleans var-ordering options
                                                0 ; interation count
                                                (+ -1 count) state))
                       (t ;this case is impossible
                         (prog2$ (er hard ',apply-tactic-name "Unknown tactic: ~x0." tactic)
                                 (mv :unknown-tactic
                                     nil ;provedp
                                     nil ;changep
                                     literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))))))

           ;; Repeatedly apply the tactic-sequence until nothing changes.
           ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state).
           (defund ,apply-rep-tactic-name (tactic-sequence
                                           literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist rule-set-number
                                           interpreted-function-alist monitored-symbols
                                           case-designator print ;move print arg?
                                           hit-counts tries prover-depth known-booleans var-ordering options iteration-count count state)
             (declare (xargs :guard (and (simple-prover-tactic-listp tactic-sequence)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (rule-alistp rule-alist)
                                         (natp rule-set-number)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (stringp case-designator)
                                         (print-levelp print)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options)
                                         (natp iteration-count))
                             :stobjs state
                             :verify-guards nil ; done below
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               ;; Apply the whole tactic-sequence:
               (b* ((- (and print (cw "(Iteration #~x0 for :rep tactic:~%" iteration-count)))
                    ((mv start-time state) (get-cpu-time state))
                    ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                     (,apply-tactics-name tactic-sequence
                                          literal-nodenums
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist rule-set-number
                                          interpreted-function-alist monitored-symbols
                                          case-designator print
                                          hit-counts tries prover-depth known-booleans var-ordering options
                                          nil ; no change yet
                                          (+ -1 count) state))
                    ((mv end-time state) (get-cpu-time state))
                    (elapsed-time (let ((diff (- end-time start-time))) (if (<= 0 diff) diff 0)))
                    ((when erp)
                     (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    (- (and print (progn$ (cw "End Iteration #~x0: " iteration-count)
                                          (print-to-hundredths elapsed-time)
                                          (cw "s.)~%") ; s for "seconds"
                                          )))
                    ((when provedp)
                     (mv (erp-nil) t t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                 (if changep
                     ;; something changed, so keep going:
                     (,apply-rep-tactic-name tactic-sequence
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alist rule-set-number
                                             interpreted-function-alist monitored-symbols
                                             case-designator print
                                             hit-counts tries prover-depth known-booleans var-ordering options (+ 1 iteration-count) (+ -1 count) state)
                   ;; :rep tactic finished (no change this time):
                   (mv (erp-nil)
                       nil ;provedp
                       nil ;changep
                       literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))))

           ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state).
           (defund ,apply-tactics-name (tactics
                                        literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alist rule-set-number
                                        interpreted-function-alist monitored-symbols
                                        case-designator print ;move print arg?
                                        hit-counts tries prover-depth known-booleans var-ordering options
                                        changep-acc ;whether previous tactics in the list changed anything
                                        count state)
             (declare (xargs :guard (and (simple-prover-tactic-listp tactics)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (rule-alistp rule-alist)
                                         (natp rule-set-number)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (stringp case-designator)
                                         (print-levelp print)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options))
                             :stobjs state
                             :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-strengthen-2 natp-of-+-of-1 rationalp-when-natp) (natp))  :do-not-induct t))
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               (if (endp tactics)
                   (mv (erp-nil)
                       nil ; did not prove the goal
                       changep-acc literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                 (b* ((tactic (first tactics))
                      (- (and print (cw "(Applying tactic ~x0:~%" tactic)))
                      ((mv start-time state) (get-cpu-time state))
                      ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                       (,apply-tactic-name tactic
                                           literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist rule-set-number
                                           interpreted-function-alist monitored-symbols
                                           case-designator print
                                           hit-counts tries prover-depth known-booleans var-ordering options (+ -1 count) state))
                      ((when erp)
                       (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                      ((mv end-time state) (get-cpu-time state))
                      (elapsed-time (let ((diff (- end-time start-time))) (if (<= 0 diff) diff 0)))
                      (- (and print (progn$ (cw "End tactic ~x0: " tactic)
                                            (print-to-hundredths elapsed-time)
                                            (cw "s.)~%") ; s for "seconds"
                                            )))
                      ((when provedp)
                       (mv (erp-nil) t t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                      ((when (not (consp literal-nodenums)))
                       (cw "NOTE: No literals.~%")
                       (mv (erp-nil) nil changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                   (,apply-tactics-name (rest tactics)
                                        literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alist rule-set-number
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options
                                        (or changep changep-acc)
                                        (+ -1 count) state)))))
           ) ; end mutual-recursion

         (make-flag ,apply-tactic-name)

         ;; The main return type theorem, proved using defthm-flag:
         (,(pack$ 'defthm-flag- apply-tactic-name)
          (defthm ,(pack$ apply-tactic-name '-return-type)
            (implies (and ;; (simple-prover-tacticp tactic)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (hit-countsp hit-counts)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       ;; (print-levelp print)
                       (natp prover-depth)
                       ;; (symbol-listp known-booleans)
                       ;; (symbol-listp var-ordering)
                       ;; (simple-prover-optionsp options)
                       (state-p state))
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-tactic-name tactic
                                           literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist rule-set-number
                                           interpreted-function-alist monitored-symbols
                                           case-designator print ;move print arg?
                                           hit-counts tries prover-depth known-booleans var-ordering options count state)
                       (implies (not erp)
                                (and (booleanp provedp)
                                     (booleanp changep)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (nat-listp new-literal-nodenums)
                                     (all-< new-literal-nodenums new-dag-len)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (implies (< 0 prover-depth)
                                              (<= dag-len new-dag-len))
                                     (state-p state)))))
            :flag ,apply-tactic-name)

          (defthm ,(pack$ apply-rep-tactic-name '-return-type)
            (implies (and ;; (simple-prover-tactic-listp tactic-sequence)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (hit-countsp hit-counts)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       ;; (print-levelp print)
                       (natp prover-depth)
                       ;; (symbol-listp known-booleans)
                       ;; (symbol-listp var-ordering)
                       ;; (simple-prover-optionsp options)
                       ;; (natp iteration-count)
                       (state-p state))
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-rep-tactic-name tactic-sequence
                                               literal-nodenums
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist rule-set-number
                                               interpreted-function-alist monitored-symbols
                                               case-designator print ;move print arg?
                                               hit-counts tries prover-depth known-booleans var-ordering options iteration-count count state)
                       (implies (not erp)
                                (and (booleanp provedp)
                                     (booleanp changep)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (nat-listp new-literal-nodenums)
                                     (all-< new-literal-nodenums new-dag-len)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (implies (< 0 prover-depth)
                                              (<= dag-len new-dag-len))
                                     (state-p state)))))
            :flag ,apply-rep-tactic-name)

          (defthm ,(pack$ apply-tactics-name '-return-type)
            (implies (and ;; (simple-prover-tactic-listp tactics)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (hit-countsp hit-counts)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       ;; (print-levelp print)
                       (natp prover-depth)
                       ;; (symbol-listp known-booleans)
                       ;; (symbol-listp var-ordering)
                       ;; (simple-prover-optionsp options)
                       (booleanp changep-acc)
                       (state-p state))
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-tactics-name tactics
                                            literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans var-ordering options changep-acc count state)
                       (implies (not erp)
                                (and (booleanp provedp)
                                     (booleanp changep)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (nat-listp new-literal-nodenums)
                                     (all-< new-literal-nodenums new-dag-len)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (implies (< 0 prover-depth)
                                              (<= dag-len new-dag-len))
                                     (state-p state)))))
            :flag ,apply-tactics-name)
          :hints (("Goal" ;:induct t
                   :in-theory (e/d (,apply-tactic-name
                                    ,apply-rep-tactic-name
                                    ,apply-tactics-name
                                    <-OF-+-OF-1-STRENGTHEN-2
                                    NATP-OF-+-OF-1
                                    rationalp-when-natp)
                                   (natp)))))

         (verify-guards ,apply-tactic-name :hints
           (("Goal" :in-theory (e/d (simple-prover-tacticp simple-prover-tactic-listp <-of-+-of-1-strengthen-2 natp-of-+-of-1 rationalp-when-natp
                                                           not-equal-of-len-and-1-when-dargp
                                                           natp-when-dargp ; trying
                                                           )
                                    (natp
                                     dargp ; trying
                                     ))
             :do-not-induct t)))

         (defthm ,(pack$ apply-tactic-name '-return-type-corollary-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (rule-alistp rule-alist)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,apply-tactic-name tactic
                                          literal-nodenums
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist rule-set-number
                                          interpreted-function-alist monitored-symbols
                                          case-designator print ;move print arg?
                                          hit-counts tries prover-depth known-booleans var-ordering options count state)
                      (declare (ignore provedp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (implies (< 0 prover-depth)
                                        (<= dag-len new-dag-len)))))
           :rule-classes :linear
           :hints (("Goal" :use ,(pack$ apply-tactic-name '-return-type)
                    :in-theory (disable ,(pack$ apply-tactic-name '-return-type)))))

         (,(pack$ 'defthm-flag- apply-tactic-name)
          (defthm ,(pack$ apply-tactic-name '-return-type-2)
            (implies (true-listp literal-nodenums)
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-tactic-name tactic
                                           literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist rule-set-number
                                           interpreted-function-alist monitored-symbols
                                           case-designator print ;move print arg?
                                           hit-counts tries prover-depth known-booleans var-ordering options count state)
                       (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                       (true-listp new-literal-nodenums)))
            :flag ,apply-tactic-name)
          (defthm ,(pack$ apply-rep-tactic-name '-return-type-2)
            (implies (true-listp literal-nodenums)
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-rep-tactic-name tactic-sequence
                                               literal-nodenums
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist rule-set-number
                                               interpreted-function-alist monitored-symbols
                                               case-designator print ;move print arg?
                                               hit-counts tries prover-depth known-booleans var-ordering options iteration-count count state)
                       (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                       (true-listp new-literal-nodenums)))
            :flag ,apply-rep-tactic-name)
          (defthm ,(pack$ apply-tactics-name '-return-type-2)
            (implies (true-listp literal-nodenums)
                     (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,apply-tactics-name tactics
                                            literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist rule-set-number
                                            interpreted-function-alist monitored-symbols
                                            case-designator print ;move print arg?
                                            hit-counts tries prover-depth known-booleans var-ordering options changep-acc count state)
                       (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                       (true-listp new-literal-nodenums)))
            :flag ,apply-tactics-name)
          :hints (("Goal" :in-theory (e/d (,apply-tactic-name
                                           ,apply-rep-tactic-name
                                           ,apply-tactics-name
                                           <-of-+-of-1-strengthen-2
                                           natp-of-+-of-1
                                           rationalp-when-natp)
                                          (natp)))))

         ;; Consider each of the RULE-ALISTS in order, for each applying the TACTIC.  TODO: What if the :tactic doesn't include :rewrite?
         ;; Returns (mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state), where if ERP
         ;; is-non-nil, then an error occurred and the other return values are irrelevant.  Otherwise, if PROVEDP is non-nil, then we proved the clause and the
         ;; other return values are irrelevant.  Otherwise, LITERAL-NODENUMS represent the simplified clause.
         ;; There should be no harvestable disjuncts in the LITERAL-NODENUMS returned, assuming there we none passed in.
         (defund ,apply-tactic-for-rule-alists-name (tactic
                                                     literal-nodenums
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                     rule-alists ;we use these one at a time
                                                     rule-set-number
                                                     interpreted-function-alist monitored-symbols case-designator print
                                                     hit-counts tries prover-depth known-booleans var-ordering options state)
           (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (nat-listp literal-nodenums)
                                       (all-< literal-nodenums dag-len)
                                       (all-rule-alistp rule-alists)
                                       (natp rule-set-number)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (print-levelp print)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (symbol-listp var-ordering)
                                       (simple-prover-optionsp options))
                           :stobjs state
                           :measure (len rule-alists)))
           (if (atom rule-alists)
               ;; No error but failed to prove this case and no more rule-alists after left:
               (prog2$
                 (and (print-level-at-least-tp print)
                      (prog2$ (cw "Case ~s0 didn't simplify to true.~%" case-designator)
                              (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len case-designator (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options))))
                 (mv (erp-nil) nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
             (b* ((- (and print (cw "(Applying rule set #~x0:~%" rule-set-number)))
                  ((mv start-time state) (get-cpu-time state))
                  ((mv erp provedp
                       & ;;changep
                       literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                   (,apply-tactic-name tactic
                                       literal-nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       (first rule-alists) ;; try the first rule-alist
                                       rule-set-number
                                       interpreted-function-alist monitored-symbols case-designator print
                                       hit-counts tries prover-depth known-booleans var-ordering options (+ -1 (expt 2 59)) state))
                  ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                  ((mv end-time state) (get-cpu-time state))
                  (elapsed-time (let ((diff (- end-time start-time))) (if (<= 0 diff) diff 0)))
                  (- (and print (progn$ (cw "End rule set #~x0: " rule-set-number)
                                        (print-to-hundredths elapsed-time)
                                        (cw "s.)~%") ; s for "seconds"
                                        )))
                  ((when provedp) (mv (erp-nil) t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                  ((when (not (consp literal-nodenums)))
                   (cw "NOTE: No literals.~%")
                   (mv (erp-nil) nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
               ;; Continue with the rest of the rule-alists:
               (,apply-tactic-for-rule-alists-name tactic
                                                   literal-nodenums
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   (rest rule-alists)
                                                   (+ 1 rule-set-number)
                                                   interpreted-function-alist monitored-symbols case-designator print
                                                   hit-counts tries prover-depth known-booleans var-ordering options state))))

         (defthm ,(pack$ apply-tactic-for-rule-alists-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (natp rule-set-number)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,apply-tactic-for-rule-alists-name tactic literal-nodenums
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                          rule-alists ;we use these one at a time
                                                          rule-set-number
                                                          interpreted-function-alist monitored-symbols case-designator print
                                                          hit-counts tries prover-depth known-booleans var-ordering options state)
                      (implies (not erp)
                               (and (booleanp provedp)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (nat-listp new-literal-nodenums)
                                    (all-< new-literal-nodenums new-dag-len)
                                    (hit-countsp new-hit-counts)
                                    (triesp new-tries)
                                    (implies (< 0 prover-depth)
                                             (<= dag-len new-dag-len))
                                    (state-p state)))))
           :hints (("Goal" :induct t
                    :in-theory (e/d (,apply-tactic-for-rule-alists-name)
                                    (natp)))))

         (defthm ,(pack$ apply-tactic-for-rule-alists-name '-return-type-2)
           (implies (true-listp literal-nodenums)
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,apply-tactic-for-rule-alists-name tactic literal-nodenums
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                          rule-alists ;we use these one at a time
                                                          rule-set-number
                                                          interpreted-function-alist monitored-symbols case-designator print
                                                          hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore erp provedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (true-listp new-literal-nodenums)))
           :hints (("Goal" :induct t
                    :in-theory (e/d (,apply-tactic-for-rule-alists-name)
                                    (natp)))))

         ;; ;fixme return hit-counts and tries?
         ;;   ;; Returns (mv provedp changep rewriter-rule-alist rule-alist monitored-symbols interpreted-function-alist state result-array-stobj), where if
         ;;   ;;   provedp is non-nil we proved the clause and the other return values are irrelevant (ffixme except the rule-alists and monitored-symbols and interpreted-function-alist?!)
         ;;   ;;fffixme - this should return fns?
         ;;   ;;currently, this just generates lemmas about the nested recursive functions..
         ;;   ;;should we pass in test-case-array-alist??
         ;;   ;;fffffixme update this to actually run test cases and prove equivalences..
         ;;   ;;ffffixme make sure a node is not :unused before proving a theorem about it?
         ;;   ;;should this return extra-stuff?
         ;;   ;;fffixme skip nodes that do not support literal-nodenums..
         ;;   (defund prove-clause-miter (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                               rewriter-rule-alist ;may get extended
         ;;                                               rule-alist ;may get extended
         ;;                                               interpreted-function-alist ;may get extended
         ;;                                               monitored-symbols ;may get extended
         ;;                                               extra-stuff test-cases
         ;;                                               miter-depth             ;new
         ;;                                               unroll
         ;;                                               options count state result-array-stobj)
         ;;     ;;ffixme whoa:
         ;;     (declare (ignore ;literal-nodenums
         ;;               dag-parent-array dag-constant-alist dag-variable-alist)
         ;;              (xargs :mode :program :stobjs (state result-array-stobj)))
         ;;     (if (not test-cases)
         ;;         (prog2$ (cw "No test cases passed in, so nothing to do.~%")
         ;;                 (mv nil nil rewriter-rule-alist rule-alist monitored-symbols interpreted-function-alist state result-array-stobj))
         ;;       (progn$ (cw "Clause miter literals: ~x0~%" literal-nodenums)
         ;;               (cw "Clause miter case: ~x0~%" (expressions-for-this-case-simple literal-nodenums dag-array dag-len)) ;fixme just print this instead of consing it up?
         ;;               (cw "Clause miter literals:~%")
         ;;               ;; (print-array 'dag-array dag-array dag-len)
         ;;               (print-dag-array-node-and-supporters-lst literal-nodenums 'dag-array dag-array)
         ;;               (let* ( ;;fixme or we could use a worklist starting with literal-nodenums..
         ;;                      (tag-array-for-prove-clause-miter (tag-supporters-of-nodes-with-name literal-nodenums 'dag-array dag-array 'tag-array-for-prove-clause-miter
         ;;                                                                                 (+ 1 (maxelem literal-nodenums))))
         ;;                      (rec-fn-nodenums (filter-rec-fn-nodes2 (+ -1 dag-len) 'dag-array dag-array 'tag-array-for-prove-clause-miter tag-array-for-prove-clause-miter state))
         ;;                      (rec-fn-nodenums (merge-sort-< rec-fn-nodenums)) ;handle this better (drop it or call reverse?)
         ;;                      (dummy (cw "Rec fn nodenums in clause miter: ~x0.~%" rec-fn-nodenums))
         ;;                      )
         ;;                 (declare (ignore dummy))
         ;;                 (mv-let (new-runes-and-fns extra-stuff state result-array-stobj)
         ;;                         (analyze-rec-fns rec-fn-nodenums
         ;;                                            'dag-array
         ;;                                            dag-array
         ;;                                            interpreted-function-alist
         ;;                                            t ;;use-axe-prover
         ;;                                            extra-stuff
         ;;                                            rewriter-rule-alist
         ;;                                            rule-alist
         ;;                                            test-cases
         ;;                                            nil ;test-case-array-alist
         ;;                                            analyzed-function-table
         ;;                                            unroll
         ;;                                            miter-depth
         ;;                                            monitored-symbols
         ;;                                            :brief ;;print fixme
         ;;                                            state result-array-stobj)
         ;;                         (declare (ignore extra-stuff)) ;fffixme return this?
         ;;                         (if (or (eq :failed new-runes-and-fns)
         ;;                                 (eq :error new-runes-and-fns))
         ;;                             (mv nil nil rewriter-rule-alist rule-alist monitored-symbols interpreted-function-alist analyzed-function-table state result-array-stobj)
         ;;                           (let* ((new-runes (first new-runes-and-fns))
         ;;                                  (new-rule-symbols (strip-cadrs new-runes))
         ;;                                  (new-fns (second new-runes-and-fns))
         ;;                                  (interpreted-function-alist
         ;;                                   (prog2$ (cw "(Adding interpreted functions:~x0)~%" new-fns)
         ;;                                           (add-fns-to-interpreted-function-alist new-fns interpreted-function-alist (w state)))))
         ;;                             (mv nil ;provedp=nil
         ;; ;this is changep:
         ;;                                 (if new-runes t nil) ;ffixme what if the rules already exist? i hope new-runes would be nil in that case, but i'm not sure
         ;; ;(add-rules-to-rule-alist (make-axe-rules new-runes (w state)) rule-alist)
         ;; ;(extend-rule-alist (make-axe-rules new-runes (w state)) t (table-alist 'axe-rule-priorities-table (w state)) rule-alist)
         ;;                                 (extend-rule-alist (make-axe-rules new-runes (w state)) t (table-alist 'axe-rule-priorities-table (w state)) rewriter-rule-alist)
         ;;                                 ;;old: (extend-rule-alist (filter-rules-to-use-in-prover (make-axe-rules new-runes (w state))) t (table-alist 'axe-rule-priorities-table (w state)) rule-alist)
         ;;                                 (extend-rule-alist (make-axe-rules new-runes (w state)) t (table-alist 'axe-rule-priorities-table (w state)) rule-alist)

         ;;                                 (prog2$ (cw "(Adding monitored symbols: ~x0)~%" new-rule-symbols) ;fffixme don't add definitions or hyp-free rules
         ;;                                         (union-eq new-rule-symbols monitored-symbols))
         ;;                                 interpreted-function-alist
         ;;                                 analyzed-function-table
         ;;                                 ;; (append (filter-rules-to-use-in-prover (make-axe-rules new-runes (w state))) ;duplicated above (is it still?) - fixme don't make rules that will be filtered out
         ;;                                 ;; prover-rules)
         ;;                                 state result-array-stobj))))))))

         ;; Returns (mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state), where if ERP
         ;; is-non-nil, then an error occurred and the other return values are irrelevant.  Otherwise, if PROVEDP is non-nil, then we proved the clause and the
         ;; other return values are irrelevant.  Otherwise, LITERAL-NODENUMS represent the simplified clause.
         ;; TODO: Get rid of this wrapper function.
         (defund ,prove-case-name (literal-nodenums
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                   tactic
                                   rule-alists
                                   interpreted-function-alist monitored-symbols
                                   case-designator print
                                   hit-counts tries prover-depth known-booleans var-ordering options state)
           (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       (nat-listp literal-nodenums)
                                       (all-< literal-nodenums dag-len)
                                       (all-rule-alistp rule-alists)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (hit-countsp hit-counts)
                                       (triesp tries)
                                       (symbol-listp monitored-symbols)
                                       (stringp case-designator)
                                       (print-levelp print)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (symbol-listp var-ordering)
                                       (simple-prover-optionsp options))
                           :stobjs state))
           (,apply-tactic-for-rule-alists-name tactic literal-nodenums
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alists
                                               1 ; number the rule sets starting at 1
                                               interpreted-function-alist monitored-symbols case-designator print
                                               hit-counts tries prover-depth known-booleans var-ordering options state))

         (defthm ,(pack$ prove-case-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (implies (not erp)
                               (and (booleanp provedp)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (nat-listp new-literal-nodenums)
                                    (all-< new-literal-nodenums new-dag-len)
                                    (hit-countsp new-hit-counts)
                                    (triesp new-tries)
                                    (implies (< 0 prover-depth)
                                             (<= dag-len new-dag-len))
                                    (state-p state)))))
           :hints (("Goal" :in-theory (e/d (,prove-case-name)
                                           (natp)))))

         (defthm ,(pack$ prove-case-name '-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore provedp new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (and (pseudo-dag-arrayp 'dag-array new-dag-array new-dag-len)
                                    (true-listp new-literal-nodenums)
                                    (natp new-dag-len)))))
           :hints (("Goal" :use (,(pack$ prove-case-name '-return-type))
                    :in-theory (disable ,(pack$ prove-case-name '-return-type)))))

         (defthm ,(pack$ prove-case-name '-return-type-corollary-2)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore provedp new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (and (not erp)
                                    (<= new-dag-len bound)
                                    (natp bound))
                               (all-< new-literal-nodenums bound))))
           :hints (("Goal" :use (,(pack$ prove-case-name '-return-type))
                    :in-theory (disable ,(pack$ prove-case-name '-return-type)))))

         (defthm ,(pack$ prove-case-name '-return-type-corollary-3)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore provedp new-literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (and (not erp)
                                    (<= bound new-dag-len)
                                    (natp bound))
                               (pseudo-dag-arrayp 'dag-array new-dag-array bound))))
           :hints (("Goal" :use (,(pack$ prove-case-name '-return-type))
                    :in-theory (disable ,(pack$ prove-case-name '-return-type)))))

         (defthm ,(pack$ prove-case-name '-return-type-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore provedp new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (implies (< 0 prover-depth)
                                        (<= dag-len new-dag-len)))))
           :rule-classes :linear
           :hints (("Goal" :use (,(pack$ prove-case-name '-return-type))
                    :in-theory (disable ,(pack$ prove-case-name '-return-type)))))

         (defthm ,(pack$ prove-case-name '-return-type-2)
           (implies (true-listp literal-nodenums)
                    (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-case-name literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        tactic
                                        rule-alists
                                        interpreted-function-alist monitored-symbols
                                        case-designator print
                                        hit-counts tries prover-depth known-booleans var-ordering options state)
                      (declare (ignore erp provedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (true-listp new-literal-nodenums)))
           :rule-classes (:rewrite :type-prescription)
           :hints (("Goal" :in-theory (e/d (,prove-case-name)
                                           (natp)))))

         (mutual-recursion

           ;; Try to prove the clause assuming NODENUM is non-nil.
           ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state) where result is :proved, :failed, or :timed-out.
           ;; This is separate to keep the main function smaller.
           (defund ,prove-true-case-name (nodenum ;; to be assumed non-nil
                                          literal-nodenums
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          tactic
                                          rule-alists
                                          interpreted-function-alist
                                          monitored-symbols
                                          print
                                          case-1-designator
                                          hit-counts tries
                                          prover-depth known-booleans var-ordering options count state)
             (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (natp nodenum)
                                         (< nodenum dag-len)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (all-rule-alistp rule-alists)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (print-levelp print)
                                         (stringp case-1-designator)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options))
                             :verify-guards nil ; done below
                             :stobjs state
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded
                     :failed ; could instead use :timed-out here
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               (b* (;; Harvest disjuncts from the new literal:
                    ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                     (get-darg-disjuncts nodenum
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         literal-nodenums ; will be extended
                                         t ;negated-flag=t, since nodenum is the negation of the new literal.
                                         print))
                    ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    ((when provedp) (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    (- (cw "(True case reduced dag: ~x0)~%" (drop-non-supporters-array-with-name 'dag-array dag-array nodenum nil)))
                    (- (and (member-eq print '(t :verbose :verbose!))
                            (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "true" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options)))))
                 ;; Attempt to prove case #1:
                 (,prove-or-split-case-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            tactic
                                            rule-alists interpreted-function-alist monitored-symbols
                                            print case-1-designator
                                            hit-counts tries
                                            (+ 1 prover-depth) ;to indicate that nodes should not be changed
                                            known-booleans var-ordering options (+ -1 count) state))))

           ;; Try to prove the clause assuming NODENUM is false.
           ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state) where result is :proved, :failed, or :timed-out.
           ;; This is separate to keep the main function smaller.
           (defund ,prove-false-case-name (nodenum ;; to be assumed false
                                           literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           tactic
                                           rule-alists
                                           interpreted-function-alist
                                           monitored-symbols
                                           print
                                           case-2-designator
                                           hit-counts tries
                                           prover-depth known-booleans var-ordering options count state)
             (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (natp nodenum)
                                         (< nodenum dag-len)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (all-rule-alistp rule-alists)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (stringp case-2-designator)
                                         (print-levelp print)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options))
                             :stobjs state
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded
                     :failed ; could instead use :timed-out here
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               (b* (;; Harvest disjuncts from the new literal:
                    ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                     (get-darg-disjuncts nodenum ;the new literal
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         literal-nodenums ; will be extended
                                         nil ;negated-flag=nil, since nodenum itself is the new literal.
                                         print))
                    ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    ((when provedp) (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    (- (and (member-eq print '(t :verbose :verbose!))
                            (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "false" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options)))))
                 ;; Attempt to prove case #2:
                 (,prove-or-split-case-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            tactic
                                            rule-alists interpreted-function-alist monitored-symbols
                                            print case-2-designator
                                            hit-counts tries
                                            (+ 1 prover-depth) ;to match what we do in the other case above
                                            known-booleans var-ordering options (+ -1 count) state))))

           ;; Tries to prove the disjunction of LITERAL-NODENUMS.
           ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state) where result is :proved, :failed, or :timed-out
           ;; If proving the goal as a single case fails, this splits into cases and recurs.
           ;; TODO: This could gather all the failed cases and return corresponding calls to prove-clause for the user to copy and paste to work on manually - currently this stops as soon as one case fails.
           ;; TODO: When should we try to separate the vars?  i think destructor elimination can enable separation...
           ;; upon failure, prints the failed case (sometimes?).
           ;; Does not change any existing DAG nodes if prover-depth > 0 (TODO check that).
           (defund ,prove-or-split-case-name (literal-nodenums
                                              dag-array ;must be named 'dag-array
                                              dag-len
                                              dag-parent-array ;must be named 'dag-parent-array
                                              dag-constant-alist dag-variable-alist
                                              tactic
                                              rule-alists
                                              interpreted-function-alist
                                              monitored-symbols
                                              print
                                              case-designator ;the name of this case
                                              hit-counts tries
                                              prover-depth known-booleans var-ordering options count state)
             (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                         (nat-listp literal-nodenums)
                                         (all-< literal-nodenums dag-len)
                                         (all-rule-alistp rule-alists)
                                         (interpreted-function-alistp interpreted-function-alist)
                                         (hit-countsp hit-counts)
                                         (triesp tries)
                                         (symbol-listp monitored-symbols)
                                         (print-levelp print)
                                         (stringp case-designator)
                                         (natp prover-depth)
                                         (symbol-listp known-booleans)
                                         (symbol-listp var-ordering)
                                         (simple-prover-optionsp options))
                             :stobjs state
                             :measure (+ 1 (nfix count)))
                      (type (unsigned-byte 59) count))
             (if (zp-fast count)
                 (mv :count-exceeded
                     :failed ; could instead use :timed-out here
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
               (b* (;; First try to prove the clause as a single case.  This may do some work even if it doesn't prove the clause.
                    ;; Tuple elim (and substitution) may change the set of variables.
                    ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                     (,prove-case-name literal-nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       tactic
                                       rule-alists interpreted-function-alist monitored-symbols
                                       case-designator print hit-counts tries prover-depth known-booleans var-ordering options state))
                    ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    ((when provedp)
                     ;; (cw "Proved case ~s0 by rewriting, etc.~%" case-designator)
                     (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                    ((when (not (consp literal-nodenums))) ;can this happen? i think so, e.g., by substitition
                     (and print (cw "No literals left!~%"))
                     (mv (erp-nil) :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                 ;; Proving it as a single case didn't finish the job (but may have done some work).
                 (if (lookup-eq :no-splitp options) ;; Check whether we are allowed to split
                     (progn$ (and print
                                  (progn$ (cw "(Not splitting into cases because :no-splitp is true.  Failed to prove case ~s0~%" case-designator)
                                          (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "this" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options))
                                          (cw ")~%")))
                             (mv (erp-nil) :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                   ;; Now maybe try to split on an if-then-else test (or an argument to a bool op).
                   (let ((nodenum (find-node-to-split-for-prover 'dag-array dag-array dag-len literal-nodenums)))
                     (if (not nodenum)
                         (progn$ (and print
                                      (progn$ (cw "(Couldn't find a node to split on.  Failed to prove case ~s0~%" case-designator)
                                              (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "this" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options))
                                              (cw ")~%")))
                                 (mv (erp-nil) :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                       ;;splitting on nodenum (which is not a call of NOT):
                       ;;instead of proving the clause C, we will prove both (or (not nodenum) C) and (or nodenum C)
                       (b* ((- (and print (cw "(Splitting on node ~x0:~%" nodenum)))
                            ;;todo: elide this if too big:
                            (- (and print (print-dag-node-nicely nodenum 'dag-array dag-array dag-len 1000)
;(print-dag-array-node-and-supporters 'dag-array dag-array nodenum)
                                    ))
                            ;; (- (and (or (eq t print) (eq :verbose print) (eq :verbose! print))
                            ;;         (progn$ (cw "Literals:~%")
                            ;;                 (print-dag-array-node-and-supporters-lst literal-nodenums 'dag-array dag-array)
                            ;;                 ;;(cw "parent array:~%")
                            ;;                 ;;(print-array 'dag-parent-array dag-parent-array dag-len)
                            ;;                 )))
                            (- (and print (cw ")~%")))
                            ;;can we somehow avoid this saving? copy to a new array? ;change ,rewrite-literals-name to not destroy existing nodes?!
                            ;;(saved-dag-array dag-array) ;(saved-dag-alist (array-to-alist 'dag-array dag-array dag-len)) ;don't convert to an alist?  just restore later by making the old value of dag-array the new  under-the-hood value?  same for parents array?
                            ;;(saved-dag-len dag-len)
                            ;;(saved-dag-parent-array dag-parent-array) ;(saved-dag-parent-alist (array-to-alist 'dag-parent-array dag-parent-array dag-len))
                            ;;(saved-dag-constant-alist dag-constant-alist)
                            ;;(saved-dag-variable-alist dag-variable-alist)
                            (case-1-designator (concatenate 'string case-designator "1"))
                            ;; In Case 1 we assume nodenum is non-nil (i.e., true).  Thus, we add a new literal (not nodenum) and try to prove (or (not nodenum) C):
                            ;; (mv-let ;Use the split fact:
                            ;;  (dag-array dag-parent-array)
                            ;;  ;fixme consider making this not destructive:
                            ;;  (replace-nodenum-with-t-in-boolean-contexts nodenum dag-array dag-parent-array) ;this leaves the subtree at nodenum itself unchanged
                            (- (and print (cw "(True Case: ~s0~%" case-1-designator)))
                            ((mv erp case-1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                             (,prove-true-case-name nodenum ;; to be assumed true
                                                    literal-nodenums
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    tactic ; same as applied to the original proof
                                                    rule-alists
                                                    interpreted-function-alist
                                                    monitored-symbols
                                                    print
                                                    case-1-designator
                                                    hit-counts tries
                                                    prover-depth known-booleans var-ordering options (+ -1 count) state))
                            ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)))
                         ;;fixme we could make an option to continue if case 1 fails, so that all the failed subgoals are printed
                         (if (not (eq :proved case-1-result))
                             (prog2$ (and print (cw "Failed on ~s0.)~%" case-1-designator))
                                     (mv (erp-nil)
                                         case-1-result ; will be :failed or :timed-out
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         hit-counts tries state))
                           (b* ((- (and print (cw "Proved true case ~s0.)~%" case-1-designator))) ;end of case1
                                ;;restore the dag:
                                ;; (dag-array (compress1 'dag-array saved-dag-array)) ;(dag-array (make-into-array-with-len 'dag-array saved-dag-alist saved-dag-len)) ;leave some slack space?
                                ;; (dag-parent-array (compress1 'dag-parent-array saved-dag-parent-array)) ;(dag-parent-array (make-into-array-with-len 'dag-parent-array saved-dag-parent-alist saved-dag-len)) ;leave some slack space?
                                ;; (dag-constant-alist saved-dag-constant-alist)
                                ;; (dag-variable-alist saved-dag-variable-alist)
                                ;;(dag-len saved-dag-len)
                                (case-2-designator (concatenate 'string case-designator "2"))
                                ;;In case 2 we assume nodenum is nil (false), i.e., we add a new literal NODENUM and try to prove (or nodenum C):
                                (- (and print (cw "(False case: ~s0~%" case-2-designator))) ;todo: print more, like we do for the true case?
                                ;;                                       (mv-let ;Use the split fact:
                                ;;                                        (dag-array dag-parent-array)
                                ;; ;fixme consider making this not destructive:
                                ;;                                        (replace-nodenum-with-nil nodenum dag-array dag-parent-array) ;this leaves the subtree at nodenum itself unchanged
                                ((mv erp case-2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state)
                                 (,prove-false-case-name nodenum ;; to be assumed true
                                                         literal-nodenums
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                         tactic ; same as applied to the original proof
                                                         rule-alists
                                                         interpreted-function-alist
                                                         monitored-symbols
                                                         print
                                                         case-2-designator
                                                         hit-counts tries
                                                         prover-depth known-booleans var-ordering options (+ -1 count) state))
                                ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist hit-counts tries state))
                                (- (and print
                                        (if (not (eq :proved case-2-result))
                                            (cw "Failed on ~s0.)~%" case-2-designator)
                                          (cw "Proved false case ~s0.)~%" case-2-designator))))
                                ;;end of case2
                                )
                             (mv (erp-nil)
                                 (if (and (eq :proved case-1-result) ;leave this check in case we make an option above to continue even when case 1 fails
                                          (eq :proved case-2-result))
                                     ;; print that we proved case 2?
                                     (prog2$ nil ;(cw "Used splitting to prove case: ~s0~%" case-designator) ;print the number of splits?
                                             :proved)
                                   (prog2$ nil ;(cw "Failed to prove both subcases of case ~s0~%" case-designator)
                                           case-2-result ;change this if we make an option above to continue even when case 1 fails
                                           ))
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 hit-counts tries state)))))))))))

         (make-flag ,prove-true-case-name)

         (,(pack$ 'defthm-flag-prove-true-case-with- suffix '-prover)
          (defthm ,(pack$ 'prove-true-case-with- suffix '-prover-return-type)
            (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (natp nodenum)
                          (< nodenum dag-len)
                          (nat-listp literal-nodenums)
                          (all-< literal-nodenums dag-len)
                          (all-rule-alistp rule-alists)
                          (interpreted-function-alistp interpreted-function-alist)
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (symbol-listp monitored-symbols)
                          (stringp case-1-designator)
                          (natp prover-depth)
                          ;; (symbol-listp var-ordering)
                          ;; (simple-prover-optionsp options)
                          (state-p state))
                     (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,prove-true-case-name nodenum
                                              literal-nodenums
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              tactic
                                              rule-alists
                                              interpreted-function-alist
                                              monitored-symbols
                                              print
                                              case-1-designator
                                              hit-counts tries
                                              prover-depth known-booleans var-ordering options count state)
                       (implies (not erp)
                                (and (prover-resultp result)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (<= dag-len new-dag-len)
                                     (state-p state)))))
            :flag ,(pack$ 'prove-true-case-with- suffix '-prover))
          (defthm ,(pack$ 'prove-false-case-with- suffix '-prover-return-type)
            (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (natp nodenum)
                          (< nodenum dag-len)
                          (nat-listp literal-nodenums)
                          (all-< literal-nodenums dag-len)
                          (all-rule-alistp rule-alists)
                          (interpreted-function-alistp interpreted-function-alist)
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (symbol-listp monitored-symbols)
                          (stringp case-2-designator)
                          (natp prover-depth)
                          ;; (symbol-listp var-ordering)
                          ;; (simple-prover-optionsp options)
                          (state-p state))
                     (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,prove-false-case-name nodenum
                                               literal-nodenums
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               tactic
                                               rule-alists
                                               interpreted-function-alist
                                               monitored-symbols
                                               print
                                               case-2-designator
                                               hit-counts tries
                                               prover-depth known-booleans var-ordering options count state)
                       (implies (not erp)
                                (and (prover-resultp result)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (<= dag-len new-dag-len)
                                     (state-p state)))))
            :flag ,(pack$ 'prove-false-case-with- suffix '-prover))
          (defthm ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)
            (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                          (nat-listp literal-nodenums)
                          (all-< literal-nodenums dag-len)
                          (all-rule-alistp rule-alists)
                          (interpreted-function-alistp interpreted-function-alist)
                          (hit-countsp hit-counts)
                          (triesp tries)
                          (symbol-listp monitored-symbols)
                          (stringp case-designator)
                          (natp prover-depth)
                          ;; (symbol-listp var-ordering)
                          ;; (simple-prover-optionsp options)
                          (state-p state))
                     (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                       (,prove-or-split-case-name literal-nodenums
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  tactic
                                                  rule-alists
                                                  interpreted-function-alist
                                                  monitored-symbols
                                                  print
                                                  case-designator
                                                  hit-counts tries
                                                  prover-depth known-booleans var-ordering options count state)
                       (implies (not erp)
                                (and (prover-resultp result)
                                     (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                     (hit-countsp new-hit-counts)
                                     (triesp new-tries)
                                     (implies (< 0 prover-depth)
                                              (<= dag-len new-dag-len))
                                     (state-p state)))))
            :flag ,(pack$ 'prove-or-split-case-with- suffix '-prover))
          :hints (("Goal" :in-theory (e/d (,prove-true-case-name
                                           ,prove-false-case-name
                                           ,prove-or-split-case-name
                                           prover-resultp)
                                          (natp)))))

         (defthm ,(pack$ 'prove-true-case-with- suffix '-prover-return-type-corollary-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-1-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-true-case-name nodenum
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             tactic
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             hit-counts tries
                                             prover-depth known-booleans var-ordering options count state)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (<= dag-len new-dag-len))))
           :rule-classes :linear
           :hints (("Goal" :use (:instance ,(pack$ 'prove-true-case-with- suffix '-prover-return-type))
                    :in-theory (disable ,(pack$ 'prove-true-case-with- suffix '-prover-return-type)))))

         (defthm ,(pack$ 'prove-true-case-with- suffix '-prover-return-type-corollary)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-1-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-true-case-name nodenum
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             tactic
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             hit-counts tries
                                             prover-depth known-booleans var-ordering options count state)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (natp new-dag-len))))
           :hints (("Goal" :use (:instance ,(pack$ 'prove-true-case-with- suffix '-prover-return-type))
                    :in-theory (disable ,(pack$ 'prove-true-case-with- suffix '-prover-return-type)))))

         (verify-guards ,prove-true-case-name
           :hints (("Goal" :in-theory (e/d (rationalp-when-natp
                                            <-of-+-of-1-strengthen-2
                                            integerp-when-natp)
                                           (natp)))))

         (defthm ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type-corollary-linear)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-or-split-case-name literal-nodenums
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 tactic
                                                 rule-alists
                                                 interpreted-function-alist
                                                 monitored-symbols
                                                 print
                                                 case-designator
                                                 hit-counts tries
                                                 prover-depth known-booleans var-ordering options count state)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (implies (< 0 prover-depth)
                                        (<= dag-len new-dag-len)))))
           :rule-classes :linear
           :hints (("Goal" :use ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)
                    :in-theory (disable ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)))))

         (defthm ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type-corollary-gen)
           (implies (and (<= bound dag-len)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (hit-countsp hit-counts)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (state-p state))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state)
                      (,prove-or-split-case-name literal-nodenums
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 tactic
                                                 rule-alists
                                                 interpreted-function-alist
                                                 monitored-symbols
                                                 print
                                                 case-designator
                                                 hit-counts tries
                                                 prover-depth known-booleans var-ordering options count state)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-hit-counts new-tries state))
                      (implies (not erp)
                               (implies (< 0 prover-depth)
                                        (<= bound new-dag-len)))))
           :hints (("Goal" :use ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)
                    :in-theory (disable ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)))))

         ;; The main entry point of the Axe Prover.
         ;; Tries to prove the disjunction of LITERAL-NODENUMS-OR-QUOTEPS.
         ;; Returns (mv erp result state) where result is :proved, :failed, or :timed-out
         ;; Does not change any existing DAG nodes if prover-depth > 0 (TODO check that).
         (defund ,prove-disjunction-name (literal-nodenums-or-quoteps
                                          dag-array ;must be named 'dag-array
                                          dag-len
                                          dag-parent-array ;must be named 'dag-parent-array
                                          dag-constant-alist dag-variable-alist
                                          tactic
                                          rule-alists
                                          interpreted-function-alist
                                          monitored-symbols
                                          print
                                          case-designator ;the name of this case
                                          prover-depth known-booleans var-ordering options
                                          use-hint
                                          wrld
                                          state)
           (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                       ;; (true-listp literal-nodenums-or-quoteps)
                                       (bounded-darg-listp literal-nodenums-or-quoteps dag-len)
                                       (all-rule-alistp rule-alists)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (symbol-listp monitored-symbols)
                                       (print-levelp print)
                                       (stringp case-designator)
                                       (natp prover-depth)
                                       (symbol-listp known-booleans)
                                       (symbol-listp var-ordering)
                                       (simple-prover-optionsp options)
                                       (axe-use-hintp use-hint)
                                       (plist-worldp wrld))
                           :stobjs state
                           :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-listp-rewrite)))))
           (b* (;; If no rule-alists are given, rewrite with a single set of simple rules.  This makes sure that
                ;; constants get evaluated, contradictions get found (when making the assumption-array), etc.
                (rule-alists (if (not rule-alists)
                                 (prog2$ (and print (cw "NOTE: Using a very simple default rule set.~%"))
                                         *default-axe-prover-rule-alists*)
                               rule-alists))
                ;; Handle any constant disjuncts
                ((mv provedp literal-nodenums)
                 (handle-constant-disjuncts literal-nodenums-or-quoteps nil))
                ((when provedp)
                 (and print (cw "! Proved case ~s0 (one literal was a non-nil constant!)~%" case-designator))
                 (mv (erp-nil) :proved state))
                ;; Get the vars:
                ;; (vars (vars-that-support-dag-nodes literal-nodenums 'dag-array dag-array dag-len)) ; too slow if there are many -- optimize!
                ;; (- (cw "(DAG has ~x0 vars.)~%" (len vars)))
                ;; Apply :use hints:
                (axe-use-instances (desugar-axe-use-hint use-hint))
                ((mv erp new-literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (if axe-use-instances
                     (let ((vars (vars-that-support-dag-nodes literal-nodenums 'dag-array dag-array dag-len))) ; todo: optimize!
                       (apply-axe-use-instances axe-use-instances dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist vars wrld nil))
                   (mv nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                ((when erp) (mv erp :failed state))
                (- (cw "(Added ~x0 literal(s) from use hints.)~%" (len new-literal-nodenums)))
                (literal-nodenums (append new-literal-nodenums literal-nodenums))
                ;; Now extract any additional disjuncts from the literals:
                ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (get-disjuncts-from-nodes literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nil print))
                ((when erp) (mv erp :failed state))
                ((when provedp)
                 (and print (cw "! Proved case ~s0 (one literal had a non-nil constant disjunct!)~%" case-designator))
                 (mv (erp-nil) :proved state))
                (- (and (member-eq print '(t :verbose :verbose!))
                        (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len "initial" (lookup-eq :print-as-clausesp options) (lookup-eq :no-print-fns options))))
                (count-hits (lookup-eq :count-hits options))
                (hit-counts (initialize-hit-counts count-hits))
                ;; Decide whether to count and print tries:
                (tries (if (print-level-at-least-verbosep print) (zero-tries) nil)) ; nil means not counting tries
                ((mv erp result & & & & & ; dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     hit-counts tries state)
                 (,prove-or-split-case-name literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            tactic rule-alists interpreted-function-alist monitored-symbols
                                            print case-designator hit-counts tries prover-depth known-booleans var-ordering options
                                            (+ -1 (expt 2 59)) ;max fixnum?
                                            state))
                ((when erp) (mv erp :failed state))
                (- (and tries (cw "~%Total rule tries: ~x0.~%" tries)))
                (- (maybe-print-hit-counts hit-counts)))
             (mv nil result state)))

         (defthm ,(pack$ prove-disjunction-name '-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         ;; (true-listp literal-nodenums-or-quoteps)
                         (bounded-darg-listp literal-nodenums-or-quoteps dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         ;; (symbol-listp var-ordering)
                         ;; (simple-prover-optionsp options)
                         (axe-use-hintp use-hint)
                         (plist-worldp wrld)
                         (state-p state))
                    (mv-let (erp result state)
                      (,prove-disjunction-name literal-nodenums-or-quoteps
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               tactic rule-alists interpreted-function-alist monitored-symbols
                                               print case-designator prover-depth known-booleans var-ordering options use-hint wrld state)
                      (implies (not erp)
                               (and (prover-resultp result)
                                    (state-p state)))))
           :hints (("Goal" :in-theory (enable ,prove-disjunction-name))))

         ;; TODO: Problem fixing up a context when one of the mentioned nodes is the nodenum of a constant.  will be renamed to a constant and fixup-context can return a non-context
         ;;        ;; Returns (mv erp result) where result is :proved [iff we proved that the top-node of dag-lst is non-nil (or is t?)], :failed, or :timed-out
         ;;        (defund ,prove-dag-name (dag
         ;;                                 assumptions ;terms we can assume non-nil
         ;;                                 rule-alists
         ;;                                 interpreted-function-alist
         ;;                                 monitored-symbols
         ;;                                 print
         ;;                                 case-name
         ;;                                 context-array-name
         ;;                                 context-array
         ;;                                 context-array-len
         ;;                                 context ;a contextp over nodes in context-array
         ;;                                 options)
         ;;          (declare (xargs :guard (and (or (myquotep dag)
         ;;                                          (and (pseudo-dagp dag) ;todo: allow a quotep?
         ;;                                               (<= (len dag) *max-1d-array-length*)))
         ;;                                      (pseudo-term-listp assumptions)
         ;;                                      (pseudo-dag-arrayp context-array-name context-array context-array-len)
         ;;                                      (bounded-contextp context context-array-len)
         ;;                                      ;;todo: add more
         ;;                                      (all-rule-alistp rule-alists)
         ;;                                      (true-listp rule-alists)
         ;;                                      (symbol-listp monitored-symbols)
         ;;                                      (interpreted-function-alistp interpreted-function-alist)
         ;;                                      (simple-prover-optionsp options)
         ;;                                      (stringp case-name))
         ;;                          :verify-guards nil ;todo
         ;;                          :guard-hints (("Goal" :in-theory (enable car-of-car-when-pseudo-dagp-cheap)
         ;;                                         :do-not '(generalize eliminate-destructors)))))
         ;;          (if (quotep dag)
         ;;              (if (unquote dag) ;a non-nil constant
         ;;                  (mv (erp-nil) :proved)
         ;;                (b* ((- (cw "Note: The DAG was the constant nil.")))
         ;;                  (mv (erp-nil) :failed)))
         ;;            (b* ( ;(dummy (cw " ~x0 prover rules (print ~x1).~%" (len prover-rules) print)) ;drop?
         ;; ;          (dummy (cw "print-max-conflicts-goalp:  ~x0" print-max-conflicts-goalp))
         ;;                 (dag-array (make-into-array 'dag-array dag))
         ;;                 (top-nodenum (top-nodenum-of-dag dag))
         ;;                 (dag-len (+ 1 top-nodenum))
         ;;                 (negated-assumptions (negate-terms assumptions))
         ;;                 (max-context-nodenum (max-nodenum-in-context context)) ;pass in? ;fixme have this return nil instead of -1
         ;;                 (no-context-nodesp (eql -1 max-context-nodenum))
         ;;                 (- (and no-context-nodesp (cw "(No context.)~%")))
         ;;                 ;; make auxiliary dag data structures:
         ;;                 ((mv dag-parent-array dag-constant-alist dag-variable-alist)
         ;;                  (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
         ;;                 ;;add the context nodes:
         ;;                 ((mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
         ;;                  (if no-context-nodesp ;Thu Sep 16 12:28:55 2010
         ;;                      (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nil)
         ;;                    ;;these is at least one context node:
         ;;                    (add-array-nodes-to-dag 0 max-context-nodenum context-array-name context-array context-array-len
         ;;                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                            (make-empty-array 'renaming-array (+ 1 max-context-nodenum)))))
         ;;                 ((when erp) (mv erp :failed))
         ;;                 ;;Fix up the context to use the new node numbers:
         ;;                 (context (if no-context-nodesp context (fixup-context context 'renaming-array renaming-array))))
         ;;              (if (false-contextp context) ;move up? or not?
         ;;                  (prog2$ (cw "! Proof succeeded due to contradictory context !")
         ;;                          (mv (erp-nil) :proved))
         ;;                (b* ((context-nodenums-to-assume (non-negated-nodenums-in-context context))
         ;;                     (context-negations-to-assume (negated-nodenums-in-context context)) ;the ones surrounded by not
         ;;                     ;;add the negated assumptions to the dag:
         ;;                     ((mv erp negated-assumption-literal-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
         ;;                      (merge-trees-into-dag-array-basic (append (negate-all context-nodenums-to-assume)
         ;;                                                                (strip-cadrs context-negations-to-assume) ;strip off the nots
         ;;                                                                negated-assumptions)
         ;;                                                        nil
         ;;                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                                        'dag-array 'dag-parent-array
         ;;                                                        interpreted-function-alist))
         ;;                     ((when erp) (mv erp :failed))
         ;;                     ((mv erp result & & & & & ;dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                          hit-counts tries)
         ;;                      (,prove-disjunction-name (cons top-nodenum negated-assumption-literal-nodenums-or-quoteps) ;we prove that either the top node of the dag is true or some assumption is false
         ;;                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
         ;;                                               rule-alists
         ;;                                               interpreted-function-alist monitored-symbols
         ;;                                               print
         ;;                                               case-name
         ;;                                               (if (or (not count-hits) (null print)) (no-hit-counting) (if (print-level-at-least-tp print) (empty-hit-counts) (zero-hits)))
         ;;                                               (and print (zero-tries))
         ;;                                               0 ;prover-depth
         ;;                                               options))
         ;;                     ((when erp) (mv erp :failed))
         ;;                     ;;just print the message in the subroutine and don't case split here?
         ;;                     (- (and print (cw "(~x0 tries.)~%" tries)))
         ;;                     (- (maybe-print-hit-counts hit-counts)))
         ;;                  (if (eq :proved result)
         ;;                      (prog2$ (cw "proved ~s0 with dag prover~%" case-name)
         ;;                              (mv (erp-nil) :proved))
         ;;                    (prog2$ (cw "failed to prove ~s0 with dag prover~%" case-name)
         ;;                            (mv (erp-nil) result))))))))

         ;; Try to prove that DAG1 implies DAG2, for all values of the variables.
         ;; TODO: Warning if no variable overlap?
         ;; Returns (mv erp event state) where a failure to prove causes erp to be non-nil.
         ;; The event returned when erp=nil is (value-triple :ok).
         ;; Because this function has a guard that is simply a stobj recognizer, it has no invariant-risk.
         (defund ,prove-dag-implication-name (dag1
                                              dag2
                                              tactic
                                              rule-lists
                                              global-rules
                                              extra-global-rules
                                              interpreted-function-alist
                                              no-splitp
                                              print-as-clausesp
                                              no-print-fns
                                              count-hits
                                              monitor
                                              print
                                              use
                                              var-ordering
                                              state)
           (declare (xargs :guard-hints (("Goal" :use (:instance make-implication-dag-return-type)
                                          :in-theory (e/d (array-len-with-slack wf-dagp)
                                                          (symbol-listp top-nodenum myquotep get-global w quotep make-implication-dag-return-type))))
                           :stobjs state))
           (b* (;; Check inputs:
                ((when (not (or (myquotep dag1)
                                (and (pseudo-dagp dag1)
                                     (<= (len dag1) *max-1d-array-length*)))))
                 (er hard? ',prove-dag-implication-name "Bad first argument: ~x0" dag1)
                 (mv :bad-input nil state))
                ((when (not (or (myquotep dag2)
                                (and (pseudo-dagp dag2)
                                     (<= (len dag2) *max-1d-array-length*)))))
                 (er hard? ',prove-dag-implication-name "Bad second argument: ~x0" dag2)
                 (mv :bad-input nil state))
                ((when (not (rule-item-list-listp rule-lists)))
                 (er hard? ',prove-dag-implication-name "Bad rule lists: ~x0" rule-lists)
                 (mv :bad-input nil state))
                ((when (not (or (eq :auto global-rules)
                                (rule-item-listp global-rules))))
                 (er hard? ',prove-dag-implication-name "Bad global-rules: ~x0" global-rules)
                 (mv :bad-input nil state))
                ((when (not (rule-item-listp extra-global-rules)))
                 (er hard? ',prove-dag-implication-name "Bad extra-global-rules: ~x0" extra-global-rules)
                 (mv :bad-input nil state))
                ((when (not (simple-prover-tacticp tactic)))
                 (er hard? ',prove-dag-implication-name "Bad tactic: ~x0" tactic)
                 (mv :bad-input nil state))
                ((when (not (interpreted-function-alistp interpreted-function-alist)))
                 (er hard? ',prove-dag-implication-name "Ill-formed interpreted-function-alist: ~x0" interpreted-function-alist)
                 (mv :bad-input nil state))
                ;; Check whether functions may be missing when we evaluate terms:
                ((when (not (interpreted-function-alist-completep interpreted-function-alist ,(pack$ '* evaluator-base-name '-fns*))))
                 (er hard? ',prove-dag-implication-name "Incomplete interpreted-function-alist.  See warning(s) above: ~x0" interpreted-function-alist)
                 (mv :bad-input nil state))
                ;; TODO: Some things in this comment may be out of date:
                ;; Check whether functions may be missing when we instantiate hyps, substitute in RHSes and lambda bodies, and merge terms into dags, all of which still use the basic evaluator:
                ((when (not (interpreted-function-alist-completep interpreted-function-alist *axe-evaluator-basic-fns*)))
                 (er hard? ',prove-dag-implication-name "Incomplete interpreted-function-alist.  See warning(s) above: ~x0" interpreted-function-alist)
                 (mv :bad-input nil state))
                ((when (not (symbol-listp monitor)))
                 (er hard? ',prove-dag-implication-name "Bad :monitor argument: ~x0" monitor)
                 (mv :bad-input nil state))
                ((when (not (ilks-plist-worldp (w state))))
                 (er hard? ',prove-dag-implication-name "Bad world (this should not happen).")
                 (mv :bad-input nil state))
                ((when (not (axe-use-hintp use)))
                 (er hard? ',prove-dag-implication-name "Bad :use hint: ~x0." use) ; todo: don't use the term "hint" for these?
                 (mv :bad-input nil state))
                ((when (not (print-levelp print)))
                 (er hard? ',prove-dag-implication-name "Bad :print option: ~x0." print)
                 (mv :bad-input nil state))
                ((when (not (booleanp no-splitp)))
                 (er hard? ',prove-dag-implication-name "Bad :no-splitp hint: ~x0." no-splitp)
                 (mv :bad-input nil state))
                ((when (not (symbol-listp var-ordering)))
                 (er hard? ',prove-dag-implication-name "Bad :var-ordering: ~x0." var-ordering)
                 (mv :bad-input nil state))
                ((when (not (booleanp print-as-clausesp)))
                 (er hard? ',prove-dag-implication-name "Bad :print-as-clausesp hint: ~x0." print-as-clausesp)
                 (mv :bad-input nil state))
                ((when (not (symbol-listp no-print-fns)))
                 (er hard? ',prove-dag-implication-name "Bad :no-print-fns hint: ~x0." no-print-fns)
                 (mv :bad-input nil state))
                ((when (not (count-hits-argp count-hits)))
                 (er hard? ',prove-dag-implication-name "Bad :count-hits hint: ~x0." count-hits)
                 (mv :bad-input nil state))
                ;; Form the implication to prove:
                ((mv erp implication-dag-or-quotep) (make-implication-dag dag1 dag2)) ; todo: we will end up having to extract disjuncts from this implication
                ((when erp) (mv erp nil state))
                ;; Handle the case of a constant DAG to prove (rare):
                ((when (quotep implication-dag-or-quotep))
                 (if (unquote implication-dag-or-quotep)
                     (prog2$ (and print (cw "NOTE: Proved the DAG because it is a constant.~%"))
                             (mv (erp-nil) '(value-triple :ok) state))
                   (prog2$ (and print (cw "NOTE: Failed because the DAG is the constant nil.~%"))
                           (mv :failed nil state))))
                (top-nodenum (top-nodenum-of-dag implication-dag-or-quotep))
                (dag-len (+ 1 top-nodenum))
                ((when (not (<= dag-len *max-1d-array-length*)))
                 (prog2$ (cw "ERROR: DAG too big.")
                         (mv :failed nil state)))
                (slack-amount 0) ;todo: increase slack amount to dag-len?
                ((mv erp dag-array) (make-dag-into-array2 'dag-array implication-dag-or-quotep slack-amount))
                ((when erp) (mv erp nil state))
                ;; make auxiliary dag data structures:
                ((mv dag-parent-array dag-constant-alist dag-variable-alist)
                 (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
                ;; Handle the global-rules option:
                (global-rules (if (eq :auto global-rules)
                                  ,default-global-rules ; this can differ for each prover
                                global-rules))
                ;; Add the extra-global-rules, if any:
                (global-rules (union-equal extra-global-rules global-rules))
                ;; Expand 0-ary function calls in rule-lists:
                (global-rules (elaborate-rule-items global-rules state))
                (rule-lists (elaborate-rule-item-lists rule-lists state))
                ;; Add global-rules to the rule-lists:
                (rule-lists (if (endp rule-lists)
                                (if (endp global-rules)
                                    (prog2$ (cw "Warning: No rule-lists or global rules given!~%")
                                            (list global-rules) ; todo: or just use nil?
                                            )
                                  ;; If no rule-lists given, use the global rules as a single rule-list:
                                  (prog2$ (cw "Note: No rule-lists given.  Using only the global rules.~%")
                                          (list global-rules)))
                              ;; Include the global-rules in each rule-list:
                              (union-eq-with-all global-rules rule-lists)))
                ;; Build the rule-alists:
                ((mv erp rule-alists) (make-rule-alists rule-lists (w state)))
                ((when erp) (mv erp nil state))
                (case-designator "MAIN_CASE") ; the name of this case
                ;; Set up prover options:
                (options nil)
                (options (if no-splitp (acons :no-splitp t options) options))
                (options (if print-as-clausesp (acons :print-as-clausesp t options) options))
                (options (if no-print-fns (acons :no-print-fns no-print-fns options) options))
                (options (if count-hits (acons :count-hits count-hits options) options))
                (- (and print (cw "(Proving ~s0:~%" case-designator)))
                ((mv erp result state)
                 (,prove-disjunction-name (list top-nodenum) ;; just one disjunct
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          tactic
                                          rule-alists
                                          interpreted-function-alist
                                          monitor
                                          print
                                          case-designator
                                          0 ;prover-depth
                                          (known-booleans (w state))
                                          var-ordering
                                          options
                                          use
                                          (w state)
                                          state))
                ((when erp) (mv erp nil state)))
             (if (eq result :proved)
                 (progn$ (and print (cw "Proved ~s0.)~%" case-designator))
                         (mv (erp-nil) '(value-triple :ok) state))
               (prog2$ (and print (cw "Failed to prove ~s0.)~%" case-designator))
                       (mv :failed-to-prove nil state)))))

         ;; Try to prove that DAG-OR-TERM1 implies DAG-OR-TERM2, for all values of the variables.
         ;; Returns (mv erp event state) where a failure to prove causes erp to be non-nil.
         ;; This function has no invariant-risk, because the functions it calls
         ;; have guards that are either t or stobj recognizers.
         (defund ,prove-implication-fn-name (dag-or-term1 ; if a term, gets translated
                                             dag-or-term2 ; if a term, gets translated
                                             tactic
                                             rule-lists
                                             global-rules
                                             extra-global-rules
                                             interpreted-function-alist
                                             no-splitp
                                             print-as-clausesp
                                             no-print-fns
                                             count-hits
                                             monitor
                                             print
                                             use
                                             var-ordering
                                             state)
           (declare (xargs :guard (and (simple-prover-tacticp tactic)
                                       (rule-item-list-listp rule-lists)
                                       (or (eq :auto global-rules)
                                           (rule-item-listp global-rules))
                                       (rule-item-listp extra-global-rules)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (booleanp no-splitp)
                                       (booleanp print-as-clausesp)
                                       (symbol-listp no-print-fns)
                                       (count-hits-argp count-hits)
                                       (symbol-listp monitor)
                                       (print-levelp print)
                                       ;; use
                                       (symbol-listp var-ordering)
                                       (ilks-plist-worldp (w state)))
                           :stobjs state
                           :mode :program ;because this translates its args if they are terms
                           ))
           (b* (;; Converts both arguments to DAGs (if not already):
                ;; We use the unguarded version here to avoid invariant-risk:
                ((mv erp dag1) (dag-or-term-to-dag-basic-unguarded dag-or-term1 (w state)))
                ((when erp) (mv erp nil state))
                ((mv erp dag2) (dag-or-term-to-dag-basic-unguarded dag-or-term2 (w state)))
                ((when erp) (mv erp nil state)))
             ;; This helper function is in :logic mode and is guard-verified:
             (,prove-dag-implication-name dag1 dag2
                                          tactic rule-lists global-rules extra-global-rules interpreted-function-alist
                                          no-splitp print-as-clausesp no-print-fns count-hits monitor print use var-ordering state)))

         ;; Attempts to prove that DAG-OR-TERM1 implies DAG-OR-TERM2.
         ;; Causes an error if the proof attempt fails.
         (defmacro ,prove-implication-name (dag-or-term1 ; if a term, gets translated
                                             dag-or-term2 ; if a term, gets translated
                                             &key
                                             (tactic ''(:rep :rewrite :subst))
                                             (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules?
                                             (global-rules ':auto) ;; rules to be added to every rule-list, replacing the default global-rules
                                             (extra-global-rules 'nil) ;; additional rule to add to the global-rules
                                             (interpreted-function-alist 'nil)
                                             (no-splitp 'nil) ; whether to prevent splitting into cases
                                             (print-as-clausesp 'nil)
                                             (no-print-fns 'nil)
                                             (count-hits 'nil)
                                             (monitor 'nil)
                                             (print ':brief)
                                             (use 'nil)
                                             (var-ordering 'nil))
           ;; all args get evaluated:
           (list 'make-event
                 (list ',prove-implication-fn-name dag-or-term1 dag-or-term2
                       tactic rule-lists global-rules extra-global-rules interpreted-function-alist
                       no-splitp print-as-clausesp no-print-fns count-hits monitor print use var-ordering 'state)))

         ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

         ;; Returns (mv erp provedp state).  Attempts to prove the clause (a disjunction
         ;; of terms) with the Axe Prover.
         (defund ,prove-clause-name (clause tactic name rule-alists monitored-symbols interpreted-function-alist print known-booleans var-ordering options use wrld state)
           (declare (xargs :guard (and (pseudo-term-listp clause)
                                       (simple-prover-tacticp tactic)
                                       (symbolp name)
                                       (all-rule-alistp rule-alists)
                                       (true-listp rule-alists)
                                       (symbol-listp monitored-symbols)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (print-levelp print)
                                       (symbol-listp known-booleans)
                                       (symbol-listp var-ordering)
                                       (simple-prover-optionsp options)
                                       (axe-use-hintp use)
                                       (plist-worldp wrld))
                           :stobjs state))
           (b* ((- (cw "(Proving clause with Axe prover:~%"))
                ((mv erp literal-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (make-terms-into-dag-array-basic clause 'dag-array 'dag-parent-array interpreted-function-alist))
                ((when erp) (mv erp nil state))
                ;;fixme name clashes..
                ;; fixme: check inputs here (combine with checks elsewhere?):
                ((mv erp result state)
                 (,prove-disjunction-name literal-nodenums-or-quoteps ;; fixme think about the options used here!
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          tactic
                                          rule-alists ;;(make-rule-alist-simple rule-alist t (table-alist 'axe-rule-priorities-table (w state)))
                                          interpreted-function-alist
                                          monitored-symbols
                                          print
                                          (symbol-name name) ;; case-designator
                                          0                  ;; prover-depth
                                          known-booleans
                                          var-ordering
                                          options
                                          use
                                          wrld
                                          state))
                ((when erp) (mv erp nil state)))
             (if (eq :proved result)
                 (prog2$ (cw "Proved the theorem.)~%")
                         (mv (erp-nil) t state))
               (prog2$ (cw "Failed to prove the theorem.)~%")
                       (mv (erp-nil) nil state)))))

         ;; Attempt to prove CLAUSE using the Axe Prover.  Returns (mv erp clauses
         ;; state) where CLAUSES is nil if the Axe Prover proved the goal and otherwise
         ;; is a singleton set containing the original clause (indicating that no change
         ;; was made).  TODO: Allow it to change the clause but not prove it entirely?
         ;; We don't actually call define-trusted-clause-processor, because that
         ;; requires a trust tag; see make-clause-processor-simple.lisp for that
         (defund ,clause-processor-name (clause hint state)
           (declare (xargs :guard (and (pseudo-term-listp clause)
                                       (ilks-plist-worldp (w state)))
                           :stobjs state))
           (b* (;; Check the the hint:
                ((when (not (alistp hint)))
                 (er hard? ',clause-processor-name "Unexpected hint (not an alist): ~x0." hint)
                 (mv :bad-hint (list clause) state))
                (hint-keys (strip-cars hint))
                (expected-hint-keys '(:must-prove :tactic :rules :rule-lists :no-splitp :print-as-clausesp :no-print-fns :monitor :use :print :var-ordering :count-hits))
                ((when (not (subsetp-eq hint-keys expected-hint-keys)))
                 (er hard? ',clause-processor-name "Unexpected keys in hint: ~x0." (set-difference-eq hint-keys expected-hint-keys))
                 (mv :bad-hint (list clause) state))
                ;; Handle the :must-prove input:
                (must-prove (lookup-eq :must-prove hint))
                ((when (not (booleanp must-prove)))
                 (er hard? ',clause-processor-name "Bad :must-prove argument: ~x0." must-prove)
                 (mv :bad-must-prove-argument (list clause) state))
                ;; Handle the :rules input:
                (rules (lookup-eq :rules hint)) ; todo: allow a rule-item-list?
                ((when (not (symbol-listp rules)))
                 (er hard? ',clause-processor-name "Bad :rules argument: ~x0." rules)
                 (mv :bad-rules (list clause) state))
                ;; Handle the :rule-lists input:
                (rule-lists (lookup-eq :rule-lists hint))
                ((when (not (symbol-list-listp rule-lists)))
                 (er hard? ',clause-processor-name "Bad :rule-lists argument: ~x0." rule-lists)
                 (mv :bad-rule-lists (list clause) state))
                ((when (and rules rule-lists))
                 (er hard? ',clause-processor-name "Both :rules and :rule-lists given.") ;todo: perhaps allow (combine them?)
                 (mv :bad-input (list clause) state))
                (rule-lists (if rules
                                (list rules)
                              rule-lists))
                ;; Handle the :tactic input:
                (tactic (lookup-eq :tactic hint))
                ((when (not (or (null tactic)
                                (simple-prover-tacticp tactic))))
                 (er hard? ',clause-processor-name "Bad :tactic argument: ~x0." tactic)
                 (mv :bad-tactic (list clause) state))
                ;; Use a suitable default if no tactic is given in the hint:
                (tactic (if (not tactic)
                            '(:rep :rewrite :subst)
                          tactic))
                ;; Handle the :use input:
                (use-hint (lookup-eq :use hint))
                ((when (not (axe-use-hintp use-hint)))
                 (er hard? ',clause-processor-name "Bad :use-hint argument: ~x0." use-hint)
                 (mv :bad-use-hint (list clause) state))
                ;; Handle the :monitor input:
                (monitored-symbols (lookup-eq :monitor hint))
                ((when (not (symbol-listp monitored-symbols)))
                 (er hard? ',clause-processor-name "Bad :monitor argument: ~x0." monitored-symbols)
                 (mv :bad-monitor (list clause) state))
                ;; Handle the :no-splitp input:
                (no-splitp (lookup-eq :no-splitp hint))
                ((when (not (booleanp no-splitp)))
                 (er hard? ',clause-processor-name "Bad :no-splitp argument: ~x0." no-splitp)
                 (mv :bad-no-splitp (list clause) state))
                ;; Handle the :print-as-clausesp argument:
                (print-as-clausesp (lookup-eq :print-as-clausesp hint))
                ((when (not (booleanp print-as-clausesp)))
                 (er hard? ',clause-processor-name "Bad :print-as-clausesp argument: ~x0." print-as-clausesp)
                 (mv :bad-print-as-clausesp (list clause) state))
                ;; Handle the :no-print-fns argument:
                (no-print-fns (lookup-eq :no-print-fns hint))
                ((when (not (symbol-listp no-print-fns)))
                 (er hard? ',clause-processor-name "Bad :no-print-fns argument: ~x0." no-print-fns)
                 (mv :bad-no-print-fns (list clause) state))
                ;; Handle the :count-hits argument:
                (count-hits (lookup-eq :count-hits hint))
                ((when (not (count-hits-argp count-hits)))
                 (er hard? ',clause-processor-name "Bad :count-hits argument: ~x0." count-hits)
                 (mv :bad-count-hits (list clause) state))
                ;; Handle the :var-ordering argument:
                (var-ordering (lookup-eq :var-ordering hint))
                ((when (not (symbol-listp var-ordering)))
                 (er hard? ',clause-processor-name "Bad :var-ordering argument: ~x0." var-ordering)
                 (mv :bad-var-ordering (list clause) state))
                ;; Handle the :print argument:
                (print (lookup-eq :print hint))
                ((when (not (print-levelp print)))
                 (er hard? ',clause-processor-name "Bad :print argument: ~x0." print)
                 (mv :bad-print (list clause) state))
                ((mv erp rule-alists) (make-rule-alists rule-lists (w state)))
                ((when erp) (mv erp (list clause) state))
                ;; Set up prover options:
                (options nil)
                (options (if no-splitp (acons :no-splitp t options) options))
                (options (if print-as-clausesp (acons :print-as-clausesp t options) options))
                (options (if no-print-fns (acons :no-print-fns no-print-fns options) options))
                (options (if count-hits (acons :count-hits count-hits options) options))
                ;; Attempt the proof:
                ((mv erp provedp state)
                 (,prove-clause-name clause
                                     tactic
                                     ',(pack$ suffix '-prover-clause-proc)
                                     rule-alists
                                     monitored-symbols
                                     nil ;interpreted-function-alist ;todo?
                                     print
                                     (known-booleans (w state))
                                     var-ordering
                                     options
                                     use-hint
                                     (w state)
                                     state))
                ((when erp) (mv erp (list clause) state)) ; error (and no change to clause set)
                )
             (if provedp
                 (mv (erp-nil) nil state) ;return the empty set of clauses
               ;; invalid or counterexample or timedout:
               (if must-prove
                   (prog2$ (er hard? ',clause-processor-name "Failed to prove but :must-prove was given.")
                           (mv (erp-t) (list clause) state))
                 ;; no change to clause set
                 (mv (erp-nil) (list clause) state)))))))))

;; Creates a custom Axe prover using the given evaluators:
(defmacro make-prover-simple (suffix ; to be added to generated names
                              evaluator-suffix ;as given to make-evaluator-simple
                              syntaxp-evaluator-suffix ;as given to make-axe-syntaxp-evaluator
                              bind-free-evaluator-suffix ;as given to make-axe-bind-free-evaluator
                              &key
                              (default-global-rules 'nil) ; a form that gets spliced into the generated code
                              )
  (make-prover-simple-fn suffix
                         evaluator-suffix
                         syntaxp-evaluator-suffix
                         bind-free-evaluator-suffix
                         default-global-rules))
