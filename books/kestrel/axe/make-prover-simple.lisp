; A tool to make an Axe Prover for a given application
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

;; This tool generates custom Axe Provers.  Each can be seen as a variant of
;; prover.lisp that does not use STP, does not support work-hard, doesn't
;; handle embedded dags, uses the basic evaluator instead of the main one, and
;; does not depend on any skip-proofs.

;todo: implement backchain limits, polarities, improve handling of equivs
;fixme axe prover requires some rules (like boolor of t, etc.) to be always enabled (without that one, we can get an error in get-disjuncts).  Improve get-disjuncts?
;fixme use faster tests than equal in some places below?

;; Consider doing (set-evisc-tuple t :iprint nil :sites :gag-mode) when working
;; with calls to make-prover-simple, to prevent printing of enormous induction
;; schemes.

(include-book "prover-common")
(include-book "rule-alists")
(include-book "make-implication-dag")
(include-book "elaborate-rule-items")
(include-book "axe-clause-utilities")
;(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "rewriter-common") ; for axe-bind-free-result-okayp, etc.
;(include-book "contexts") ;for max-nodenum-in-context
(include-book "unify-term-and-dag-fast")
(include-book "hit-counts")
(include-book "get-args-not-done")
(include-book "tries")
(include-book "my-sublis-var-and-eval-basic") ;todo: gen
(include-book "instantiate-hyp-basic") ;todo: gen
(include-book "dag-or-term-to-dag-basic") ;todo: gen?
(include-book "merge-tree-into-dag-array-basic") ;for merge-trees-into-dag-array-basic ;todo: gen?
(include-book "kestrel/utilities/all-vars-in-term-bound-in-alistp" :dir :system)

(defthm all-axe-treep-of-keep-atoms-when-contextp
  (implies (and (contextp x)
                (not (equal :false x)))
           (all-axe-treep (keep-atoms x)))
  :hints (("Goal" :in-theory (enable keep-atoms contextp))))

;move
(defthm strip-cdrs-of-pairlis$-3
  (equal (strip-cdrs (pairlis$ x y))
         (take (len x) y))
  :hints (("Goal" :in-theory (enable len))))

(defthmd len-of-lambda-formals-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)) ;it's a lambda
                )
           (equal (len (car (cdr (car tree))))
                  (len (fargs tree))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd pseudo-termp-of-lambda-body-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)) ;it's a lambda
                )
           (pseudo-termp (car (cdr (cdr (car tree))))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd <-of--1-when-natp
  (implies (natp x)
           (not (< x -1))))

;also in merge-sort
(defthmd len-of-cdr-better-for-axe-prover
  (equal (len (cdr x))
         (if (equal 0 (len x))
             0 (+ -1 (len x)))))

;also in merge-sort
(defthmd consp-when-len-equal-for-axe-prover
  (implies (and (equal (len x) free)
                (syntaxp (quotep free)))
           (equal (consp x) (< 0 free)))
  :hints (("Goal" :in-theory (e/d (len) (;len-of-cdr
                                         )))))

(defthmd rationalp-when-natp-for-axe
  (implies (natp x)
           (rationalp x)))

(defthmd rationalp-when-integerp-for-axe
  (implies (integerp x)
           (rationalp x)))

(defthmd integerp-when-natp-for-axe
  (implies (natp x)
           (integerp x)))

(defthm not-<-of-LARGEST-NON-QUOTEP-and--1
  (not (< (LARGEST-NON-QUOTEP dags) '-1)))

(defconst *make-prover-simple-rules*
  '((:COMPOUND-RECOGNIZER AXE-TREEP-COMPOUND-RECOGNIZER)
    (:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
    (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
    (:CONGRUENCE IFF-IMPLIES-EQUAL-NOT)
    (:CONGRUENCE PERM-IMPLIES-EQUAL-ALL-DARGP-LESS-THAN-1)
    (:DEFINITION =)
    (:DEFINITION ALL-AXE-TREEP)
    ;(:DEFINITION AXE-RULE-HYP-LISTP)
    (:DEFINITION ENDP)
    (:DEFINITION EQ)
    (:DEFINITION FIX)
    (:DEFINITION LENGTH)
    (:DEFINITION MAX)
    (:DEFINITION MEMBER-EQUAL)
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
    (:EXECUTABLE-COUNTERPART ALL-AXE-TREEP)
    (:EXECUTABLE-COUNTERPART ALL-NATP)
    (:EXECUTABLE-COUNTERPART ALL-STORED-AXE-RULEP)
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
    (:EXECUTABLE-COUNTERPART INFO-WORLDP)
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
;(:FAKE-RUNE-FOR-LINEAR NIL)
;(:FAKE-RUNE-FOR-TYPE-SET NIL)
    (:FORWARD-CHAINING ACL2-NUMBER-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING ARRAY1P-FORWARD)
    (:FORWARD-CHAINING ARRAY1P-FORWARD-TO-<=-OF-ALEN1)
    (:FORWARD-CHAINING AXE-RULE-HYP-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING
     BOUNDED-DAG-CONSTANT-ALISTP-FORWARD-TO-DAG-CONSTANT-ALISTP)
    (:FORWARD-CHAINING
     BOUNDED-DAG-PARENT-ARRAYP-FORWARD-TO-BOUNDED-DAG-PARENT-ARRAYP)
    (:FORWARD-CHAINING
     BOUNDED-DAG-VARIABLE-ALISTP-FORWARD-TO-DAG-VARIABLE-ALISTP)
    (:FORWARD-CHAINING BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
    (:FORWARD-CHAINING CONSP-ASSOC-EQUAL)
    (:FORWARD-CHAINING CONSP-FORWARD-TO-LEN-BOUND)
    (:FORWARD-CHAINING DAG-CONSTANT-ALISTP-FORWARD-TO-ALISTP)
    (:FORWARD-CHAINING DAG-PARENT-ARRAYP-FORWARD-TO-ARRAY1P)
    (:FORWARD-CHAINING DAG-VARIABLE-ALISTP-FORWARD-SYMBOL-ALISTP)
    (:FORWARD-CHAINING
     DAG-VARIABLE-ALISTP-FORWARD-TO-NAT-LISTP-OF-STRIP-CDRS)
    (:FORWARD-CHAINING EQLABLE-ALISTP-FORWARD-TO-ALISTP)
    (:FORWARD-CHAINING INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP)
    (:FORWARD-CHAINING INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-ALISTP)
    (:FORWARD-CHAINING
     INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-SYMBOL-ALISTP)
    (:FORWARD-CHAINING KEYWORD-VALUE-LISTP-ASSOC-KEYWORD)
    (:FORWARD-CHAINING KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING MYQUOTEP-FORWARD-TO-CONSP)
    (:FORWARD-CHAINING NAT-LISTP-FORWARD-TO-INTEGER-LISTP)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-CHAINING)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-CHAINING-ANOTHER)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-TO-<=-OF-ALEN1)
    (:FORWARD-CHAINING PSEUDO-DAG-ARRAYP-FORWARD-TO-NATP-ARG3)
    (:FORWARD-CHAINING RATIONAL-LISTP-FORWARD-TO-ACL2-NUMBER-LISTP)
    (:FORWARD-CHAINING SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
    (:FORWARD-CHAINING SYMBOL-ALISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING SYMBOL-LISTP-FORWARD-TO-TRUE-LISTP)
    (:FORWARD-CHAINING TRIESP-FORWARD)
    (:FORWARD-CHAINING WF-DAGP-FORWARD)
    (:FORWARD-CHAINING WF-DAGP-FORWARD-TO-<=-OF-LEN)
    (:LINEAR BOUND-ON-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-3)
    (:REWRITE +-COMBINE-CONSTANTS)
    (:REWRITE <-OF-+-OF-1-STRENGTHEN-2)
    (:REWRITE <-OF--1-WHEN-NATP)
    (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP)
    (:REWRITE ALL-<-OF-CDR)
    (:REWRITE ALL-<-OF-NIL)
    (:REWRITE ALL-<-TRANSITIVE)
    (:REWRITE ALL-<-TRANSITIVE-FREE)
    (:REWRITE ALL-<-TRANSITIVE-FREE-2)
    (:REWRITE ALL-AXE-TREEP-OF-CDR)
    (:REWRITE ALL-AXE-TREEP-OF-CDR-2)
    (:REWRITE ALL-BOUNDED-AXE-TREEP-MONO)
    (:REWRITE ALL-BOUNDED-AXE-TREEP-OF-CDR)
    (:REWRITE ALL-BOUNDED-AXE-TREEP-OF-CDR-2)
    (:REWRITE ALL-BOUNDED-AXE-TREEP-OF-CONS)
    (:REWRITE ALL-BOUNDED-AXE-TREEP-WHEN-PSEUDO-TERM-LISTP)
    (:REWRITE ALL-DARGP-LESS-THAN-MONOTONE)
    (:REWRITE ALL-DARGP-LESS-THAN-OF-APPEND)
    (:REWRITE ALL-DARGP-LESS-THAN-OF-CONS)
    (:REWRITE
     ALL-DARGP-LESS-THAN-OF-MV-NTH-1-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE)
    (:REWRITE
     ALL-DARGP-LESS-THAN-OF-STRIP-CDRS-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE ALL-DARGP-LESS-THAN-WHEN-ALL-<)
    (:REWRITE ALL-DARGP-OF-STRIP-CDRS-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE ALL-DARGP-WHEN-ALL-DARGP-LESS-THAN)
    (:REWRITE ALL-NATP-OF-CDR)
    (:REWRITE ALL-NATP-WHEN-NAT-LISTP)
    (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP)
    (:REWRITE ALL-STORED-AXE-RULEP-OF-CDR)
    (:REWRITE ALL-STORED-AXE-RULEP-OF-LOOKUP-EQUAL-WHEN-RULE-ALISTP)
    (:REWRITE AXE-BIND-FREE-RESULT-OKAYP-REWRITE)
    (:REWRITE AXE-RULE-HYP-LISTP-OF-CDR)
    (:REWRITE AXE-RULE-HYP-LISTP-OF-STORED-RULE-HYPS)
    (:REWRITE AXE-RULE-HYPP-WHEN-AXE-BIND-FREE)
    (:REWRITE AXE-RULE-HYPP-WHEN-SIMPLE)
    (:REWRITE AXE-TREEP-OF-CAR)
    (:REWRITE AXE-TREEP-OF-CONS-STRONG)
    (:REWRITE AXE-TREEP-OF-MV-NTH-0-OF-INSTANTIATE-HYP-BASIC)
    (:REWRITE AXE-TREEP-OF-MY-SUBLIS-VAR-AND-EVAL-BASIC)
    (:REWRITE
     AXE-TREEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:REWRITE AXE-TREEP-WHEN-EQUAL-OF-CAR-AND-QUOTE-CHEAP)
    (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP)
    (:REWRITE AXE-TREEP-WHEN-PSEUDO-TERMP)
    (:REWRITE BOUND-ON-MV-NTH-3-AND-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-ALT)
    (:REWRITE BOUNDED-AXE-TREEP-MONO)
    (:REWRITE BOUNDED-AXE-TREEP-OF-CAR)
    (:REWRITE BOUNDED-AXE-TREEP-OF-CONS)
    (:REWRITE BOUNDED-AXE-TREEP-OF-MV-NTH-0-OF-INSTANTIATE-HYP-BASIC)
    (:REWRITE BOUNDED-AXE-TREEP-OF-MY-SUBLIS-VAR-AND-EVAL-BASIC)
    (:REWRITE
     BOUNDED-AXE-TREEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
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
    (:REWRITE
     DARGP-LESS-THAN-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-GEN)
    (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-MYQUOTEP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP)
    (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP)
    (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT)
    (:REWRITE EQUAL-OF-LEN-AND-0)
    (:REWRITE INFO-WORLDP-OF-INCREMENT-HIT-COUNT-IN-INFO-WORLD)
    (:REWRITE INTEGER-LISTP-WHEN-ALL-NATP)
    (:REWRITE
     INTEGERP-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:REWRITE LEN-OF-CDR)
    (:REWRITE LEN-OF-CONS)
    (:REWRITE LEN-OF-LAMBDA-FORMALS-WHEN-AXE-TREEP)
    (:REWRITE LOOKUP-EQ-BECOMES-LOOKUP-EQUAL)
    (:REWRITE MAXELEM-OF-CONS)
    (:REWRITE MV-NTH-6-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:REWRITE MV-NTH-OF-CONS)
    (:REWRITE
     MYQUOTEP-OF-REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:REWRITE NAT-LISTP-WHEN-ALL-NATP)
    (:REWRITE NATP-OF-+-OF-1-ALT)
    (:REWRITE NATP-OF-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:REWRITE NOT-<-OF-+-1-AND-MAXELEM)
    (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP)
    (:REWRITE PERM-OF-APPEND)
    (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE)
    (:REWRITE
     PSEUDO-DAG-ARRAYP-OF-MV-NTH-2-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-GEN)
    (:REWRITE PSEUDO-TERM-LISTP-OF-STORED-RULE-LHS-ARGS)
    (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-WHEN-AXE-TREEP)
    (:REWRITE PSEUDO-TERMP-OF-STORED-RULE-RHS)
    (:REWRITE STRIP-CDRS-OF-APPEND)
    (:REWRITE STRIP-CDRS-OF-PAIRLIS$2)
    (:REWRITE SYMBOL-ALISTP-OF-APPEND)
    (:REWRITE
     SYMBOL-ALISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC)
    (:REWRITE
     SYMBOL-ALISTP-OF-MV-NTH-1-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE)
    (:REWRITE SYMBOL-ALISTP-OF-UNIFY-TERMS-AND-DAG-ITEMS-FAST)
    (:REWRITE SYMBOL-LISTP-OF-CDR)
    (:REWRITE SYMBOL-LISTP-OF-GET-EQUIVS)
    (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP)
    (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP)
    (:REWRITE SYMBOLP-OF-STORED-RULE-SYMBOL)
    (:REWRITE TRIESP-OF-INCREMENT-TRIES)
    (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP)
    (:REWRITE TRUE-LISTP-OF-LOOKUP-EQUAL-WHEN-RULE-ALISTP)
    (:REWRITE USE-ALL-STORED-AXE-RULEP-FOR-CAR)
    (:REWRITE WF-DAGP-AFTER-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP)
    (:TYPE-PRESCRIPTION ALEN1-TYPE)
    (:TYPE-PRESCRIPTION ALISTP)
    (:TYPE-PRESCRIPTION ALL-<)
    (:TYPE-PRESCRIPTION ALL-AXE-TREEP)
    (:TYPE-PRESCRIPTION ALL-BOUNDED-AXE-TREEP)
    (:TYPE-PRESCRIPTION ALL-CONSP)
    (:TYPE-PRESCRIPTION ALL-DARGP-LESS-THAN)
    (:TYPE-PRESCRIPTION ALL-STORED-AXE-RULEP)
    (:TYPE-PRESCRIPTION ARRAY1P)
    (:TYPE-PRESCRIPTION ASSOC-KEYWORD)
    (:TYPE-PRESCRIPTION AXE-PROVER-OPTIONSP)
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
    (:TYPE-PRESCRIPTION INFO-WORLDP)
    (:TYPE-PRESCRIPTION INTEGER-LISTP)
    (:TYPE-PRESCRIPTION INTERPRETED-FUNCTION-ALISTP)
    (:TYPE-PRESCRIPTION KEYWORD-VALUE-LISTP)
    (:TYPE-PRESCRIPTION LEN)
    (:TYPE-PRESCRIPTION LENGTH)
    (:TYPE-PRESCRIPTION MYQUOTEP)
    (:TYPE-PRESCRIPTION NAT-LISTP)
    (:TYPE-PRESCRIPTION NATP-OF-CAR-WHEN-NAT-LISTP-TYPE)
    (:TYPE-PRESCRIPTION NATP-OF-MAXELEM-2)
    (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-3-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY)
    (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP)
    (:TYPE-PRESCRIPTION PSEUDO-TERMP)
    (:TYPE-PRESCRIPTION RATIONAL-LISTP)
    (:TYPE-PRESCRIPTION REPLACE-NODENUM-USING-ASSUMPTIONS-FOR-AXE-PROVER)
    (:TYPE-PRESCRIPTION RULE-ALISTP)
    (:TYPE-PRESCRIPTION STRIP-CDRS)
    (:TYPE-PRESCRIPTION SYMBOL-ALISTP)
    (:TYPE-PRESCRIPTION SYMBOL-LISTP)
    (:TYPE-PRESCRIPTION TRIESP)
    (:TYPE-PRESCRIPTION
     TRUE-LISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC)
    (:TYPE-PRESCRIPTION
     TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-HYP-WITH-NODENUM-TO-ASSUME-FALSE)
    (:TYPE-PRESCRIPTION WF-DAGP)))

(defun make-prover-simple-fn (suffix ;; gets added to generated names
                              apply-axe-evaluator-to-quoted-args-name
                              eval-axe-syntaxp-expr-name
                              eval-axe-bind-free-function-application-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp apply-axe-evaluator-to-quoted-args-name)
                              (symbolp eval-axe-syntaxp-expr-name)
                              (symbolp eval-axe-bind-free-function-application-name))))
  (let* ((relieve-free-var-hyp-and-all-others-name (pack$ 'relieve-free-var-hyp-and-all-others-for- suffix '-prover))
         (relieve-rule-hyps-name (pack$ 'relieve-rule-hyps-for- suffix '-prover))
         (try-to-apply-rules-name (pack$ 'try-to-apply-rules-for- suffix '-prover))
         (simplify-if-tree-name (pack$ 'simplify-if-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-boolif-tree-name (pack$ 'simplify-boolif-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-fun-call-name (pack$ 'simplify-fun-call-and-add-to-dag-for- suffix '-prover))
         (simplify-tree-name (pack$ 'simplify-tree-and-add-to-dag-for- suffix '-prover))
         (simplify-trees-name (pack$ 'simplify-trees-and-add-to-dag-for- suffix '-prover))
         (rewrite-nodes-name (pack$ 'rewrite-nodes-for- suffix '-prover))
         (rewrite-literal-name (pack$ 'rewrite-literal-for- suffix '-prover))
         (rewrite-literals-name (pack$ 'rewrite-literals-for- suffix '-prover))
         (rewrite-subst-and-elim-with-rule-alist-name (pack$ 'rewrite-subst-and-elim-with-rule-alist-for- suffix '-prover))
         (rewrite-subst-and-elim-with-rule-alists-name (pack$ 'rewrite-subst-and-elim-with-rule-alists-for- suffix '-prover))
         (prove-case-name (pack$ 'prove-case-with- suffix '-prover))
         (prove-disjunction-name (pack$ 'prove-disjunction-with- suffix '-prover))
         (prove-true-case-name (pack$ 'prove-true-case-with- suffix '-prover))
         (prove-false-case-name (pack$ 'prove-false-case-with- suffix '-prover))
         (prove-or-split-case-name (pack$ 'prove-or-split-case-with- suffix '-prover))
         ;; (prove-dag-name (pack$ 'prove-dag-with- suffix '-prover))
         (prove-clause-name (pack$ 'prove-clause-with- suffix '-prover))
         (prove-implication-name (pack$ 'prove-implication-with- suffix '-prover)) ;a macro
         (prove-implication-fn-name (pack$ 'prove-implication-with- suffix '-prover-fn))
         (prove-implication-fn-helper-name (pack$ 'prove-implication-with- suffix '-prover-fn-helper))
         (clause-processor-name (pack$ suffix '-prover-clause-processor))
         (defthm-with-clause-processor-name (pack$ 'defthm-with- clause-processor-name))
         (defthm-with-clause-processor-fn-name (pack$ 'defthm-with- clause-processor-name '-fn))

         ;; Keep these in sync with the formals of each function:

         (call-of-relieve-free-var-hyp-and-all-others `(,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false-to-walk-down
                                                                                                  hyp hyp-num other-hyps alist rule-symbol
                                                                                                  dag-array dag-len dag-parent-array
                                                                                                  dag-constant-alist dag-variable-alist
                                                                                                  equiv-alist rule-alist
                                                                                                  nodenums-to-assume-false print
                                                                                                  info tries interpreted-function-alist
                                                                                                  monitored-symbols
                                                                                                  embedded-dag-depth case-designator
                                                                                                  prover-depth options count))
         (call-of-relieve-rule-hyps `(,relieve-rule-hyps-name hyps hyp-num alist rule-symbol
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              equiv-alist rule-alist
                                                              nodenums-to-assume-false print
                                                              info tries interpreted-function-alist
                                                              monitored-symbols
                                                              embedded-dag-depth case-designator
                                                              prover-depth options count))

         (call-of-try-to-apply-rules `(,try-to-apply-rules-name stored-rules rule-alist args-to-match
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                nodenums-to-assume-false
                                                                equiv-alist print
                                                                info tries interpreted-function-alist
                                                                monitored-symbols
                                                                embedded-dag-depth case-designator
                                                                prover-depth options count))
         (call-of-simplify-if-tree `(,simplify-if-tree-name tree
                                                            equiv dag-array dag-len dag-parent-array
                                                            dag-constant-alist dag-variable-alist
                                                            rule-alist nodenums-to-assume-false
                                                            equiv-alist print
                                                            info tries interpreted-function-alist
                                                            monitored-symbols
                                                            embedded-dag-depth case-designator
                                                            prover-depth options count))
         (call-of-simplify-boolif-tree `(,simplify-boolif-tree-name tree
                                                            equiv dag-array dag-len dag-parent-array
                                                            dag-constant-alist dag-variable-alist
                                                            rule-alist nodenums-to-assume-false
                                                            equiv-alist print
                                                            info tries interpreted-function-alist
                                                            monitored-symbols
                                                            embedded-dag-depth case-designator
                                                            prover-depth options count))
         (call-of-simplify-fun-call `(,simplify-fun-call-name fn args
                                                              equiv dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist
                                                              rule-alist nodenums-to-assume-false
                                                              equiv-alist print
                                                              info tries interpreted-function-alist
                                                              monitored-symbols
                                                              embedded-dag-depth case-designator
                                                              prover-depth options count))
         (call-of-simplify-tree `(,simplify-tree-name tree
                                                      equiv dag-array dag-len dag-parent-array
                                                      dag-constant-alist dag-variable-alist
                                                      rule-alist nodenums-to-assume-false
                                                      equiv-alist print
                                                      info tries interpreted-function-alist
                                                      monitored-symbols
                                                      embedded-dag-depth case-designator
                                                      prover-depth options count))

         (call-of-simplify-trees `(,simplify-trees-name trees equivs
                                                        dag-array dag-len dag-parent-array
                                                        dag-constant-alist dag-variable-alist
                                                        rule-alist nodenums-to-assume-false
                                                        equiv-alist print
                                                        info tries interpreted-function-alist
                                                        monitored-symbols
                                                        embedded-dag-depth case-designator
                                                        prover-depth options count))
         )

    `(encapsulate ()

       (local (include-book "kestrel/lists-light/nth" :dir :system))
       (local (include-book "kestrel/lists-light/remove-equal" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/lists-light/reverse" :dir :system))
       (local (include-book "kestrel/lists-light/last" :dir :system))
       (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
       (local (include-book "kestrel/lists-light/take" :dir :system))
       (local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
       (local (include-book "kestrel/lists-light/cons" :dir :system)) ; for true-listp-of-cons
       (local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
       (local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/utilities/acl2-count" :dir :system))
       (local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
       (local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;(in-theory (disable add-to-end))

;(local (in-theory (disable CADR-BECOMES-NTH-OF-1))) ;need better acl2-count rules about nth (maybe when we know the length...)

;for speed
       (local (in-theory (disable ;alistp-consp-hack-equal
                          weak-dagp-aux
                          ;;consp-from-len-cheap
                          default-car
                          <-of-nth-and-alen1 ;todo
                          dag-exprp0
                          ;;list::nth-with-large-index
                          ;;list::nth-with-large-index-2
                          nat-listp
                          all-natp-when-not-consp
                          all-<-when-not-consp
                          all-dargp-when-not-consp
                          acl2-count ;yuck
                          SYMBOL-ALISTP ;move
                          SYMBOL-LISTP ; prevent inductions
                          dag-function-call-exprp-redef
                          axe-treep)))

       (local (in-theory (enable natp-of-+-of-1-alt
                                 natp-of-car-when-all-dargp-less-than-gen)))

       ;;(in-theory (disable car-becomes-nth-of-0)) ;move to arrays-axe

       ;; (defthm all-myquotep-of-mv-nth-1-of-my-sublis-var-and-eval-lst
       ;;   (implies (and (mv-nth 0 (my-sublis-var-and-eval-lst alist l interpreted-function-alist))
       ;;                 (pseudo-term-listp l)
       ;;                 (symbol-alistp alist)
       ;;                 (pseudo-term-listp (strip-cdrs alist))
       ;;                 (alistp interpreted-function-alist))
       ;;            (all-myquotep (mv-nth 1 (my-sublis-var-and-eval-lst alist l interpreted-function-alist))))
       ;;   :hints (("subgoal *1/1"
       ;; ;           :use (:instance pseudo-termp-of-my-sublis-var-and-eval (form (car l)))
       ;;            :in-theory (e/d ( ;consp-of-cdr-when-pseudo-termp
       ;;                             ) (
       ;;                             ;pseudo-termp-of-my-sublis-var-and-eval
       ;;                             )))
       ;;           ("Goal" :induct (len l) :expand (my-sublis-var-and-eval-lst alist l interpreted-function-alist)
       ;;            :in-theory (enable (:i len)))))

       ;;todo: verify guards and remove this:
       (defttag invariant-risk)
       (set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

       ;;
       ;; The main mutual recursion for the Axe Prover:
       ;;

       ;; The PROVER-DEPTH argument ensures that multiple simultaneous result arrays
       ;; don't have the same name.  It also indicates whether we can change existing
       ;; nodes (depth 0) or not (any other depth).

       (mutual-recursion

        ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
        (defund ,relieve-free-var-hyp-and-all-others-name (nodenums-to-assume-false-to-walk-down
                                                           hyp ;partly instantiated
                                                           hyp-num
                                                           other-hyps
                                                           alist rule-symbol
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           equiv-alist rule-alist
                                                           nodenums-to-assume-false ;we keep the whole list as well as walking down it
                                                           print
                                                           info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth ;used for the renaming-array-for-merge-embedded-dag
                                                           case-designator prover-depth options count)
          (declare (xargs
                    :verify-guards nil ; done below
                    :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                (symbol-alistp alist)
                                (all-dargp-less-than (strip-cdrs alist) dag-len)
                                (nat-listp nodenums-to-assume-false-to-walk-down)
                                (all-< nodenums-to-assume-false-to-walk-down dag-len)
                                (axe-treep hyp)
                                (natp hyp-num)
                                (axe-rule-hyp-listp other-hyps)
                                (symbolp rule-symbol)
                                (equiv-alistp equiv-alist)
                                (rule-alistp rule-alist)
                                (nat-listp nodenums-to-assume-false)
                                (all-< nodenums-to-assume-false dag-len)
                                ;; print
                                (info-worldp info)
                                (triesp tries)
                                (interpreted-function-alistp interpreted-function-alist)
                                (symbol-listp monitored-symbols)
                                (natp embedded-dag-depth) ;can we just use the prover depth?
                                (stringp case-designator)
                                (natp prover-depth)
                                (axe-prover-optionsp options) ;; TODO: Not currently used.  Disallow :no-stp?
                                )
                    :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (or (endp nodenums-to-assume-false-to-walk-down)
                  (zp-fast count))
              ;;failed to relieve the hyps:
              (mv (erp-nil) ;we could return an error of :count-exceeded here if (zp-fast count), but that might be slower
                  nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (let* ((nodenum-to-assume-false (first nodenums-to-assume-false-to-walk-down)))
              (mv-let (matchp alist-for-free-vars)
                (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len) ;fixme this could extend the alist
                (if matchp
                    (b* ((new-alist (append alist-for-free-vars alist)) ;skip this append?
                         ((mv erp other-hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                          (,relieve-rule-hyps-name other-hyps
                                                   (+ 1 hyp-num)
                                                   new-alist
                                                   rule-symbol
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   equiv-alist rule-alist
                                                   nodenums-to-assume-false
                                                   print info tries interpreted-function-alist
                                                   monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                         ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                      (if other-hyps-relievedp
                          (mv (erp-nil) t extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                        ;;this nodenum-to-assume-false matches, but we couldn't relieve the rest of the hyps:
                        (,relieve-free-var-hyp-and-all-others-name (rest nodenums-to-assume-false-to-walk-down)
                                                                   hyp
                                                                   hyp-num
                                                                   other-hyps
                                                                   alist ;the original alist
                                                                   rule-symbol
                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                   equiv-alist rule-alist
                                                                   nodenums-to-assume-false
                                                                   print
                                                                   info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                                   prover-depth options (+ -1 count))))
                  ;;this nodenum-to-assume-false didn't match:
                  (,relieve-free-var-hyp-and-all-others-name (rest nodenums-to-assume-false-to-walk-down)
                                                             hyp hyp-num other-hyps
                                                             alist rule-symbol
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             equiv-alist rule-alist
                                                             nodenums-to-assume-false ;we keep the whole list as well as walking down it
                                                             print
                                                             info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))

        ;; ;print something like this:?
        ;;                               (prog2$
        ;;                                (and (member-eq rule-symbol monitored-symbols)
        ;;                                     (progn$ (cw "(Failed.  Reason: Failed to match free var in hyp (number ~x0): ~x1 for ~x2." hyp-num hyp rule-symbol)
        ;;                                             (cw "(Assumptions (to assume false):~%")
        ;; ;this can be big (print it just once per literal?)
        ;;                                             (if (eq print :verbose) (print-dag-only-supporters-lst nodenums-to-assume-false 'dag-array dag-array) (cw ":elided"))
        ;;                                             ;;fixme print the  part of the dag array that supports the hyp??
        ;;                                             (cw ")~%Alist: ~x0~%)~%" alist)))


        ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
        ;; alist maps vars to nodenums or quoteps (not terms?)
        (defund ,relieve-rule-hyps-name (hyps ;the hyps of the rule (not yet instantiated ; trees over vars and quoteps)
                                         hyp-num
                                         alist ;binds variables to nodenums or quoteps
                                         rule-symbol
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         equiv-alist rule-alist
                                         nodenums-to-assume-false
                                         print info tries interpreted-function-alist
                                         monitored-symbols embedded-dag-depth
                                         case-designator
                                         prover-depth options count)
          (declare (xargs :guard (and (axe-rule-hyp-listp hyps)
                                      (natp hyp-num)
                                      (symbol-alistp alist)
                                      (symbolp rule-symbol)
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (all-dargp-less-than (strip-cdrs alist) dag-len)
                                      (equiv-alistp equiv-alist)
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (if (endp hyps)
                ;; all hyps relieved:
                (mv (erp-nil) t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
              (b* ((hyp (first hyps)) ;known to be a non-lambda function call
                   (fn (ffn-symb hyp))
                   (- (and (eq :verbose print) (cw " Relieving hyp: ~x0 with alist ~x1.~%" hyp alist))))
                (if (eq 'axe-syntaxp fn)
                    (let* ((syntaxp-expr (farg1 hyp)) ;; strip off the AXE-SYNTAXP
                           (result (and (all-vars-in-term-bound-in-alistp syntaxp-expr alist) ; TODO: remove this check, since it should be guaranteed statically!  need a better guards in the alist wrt future hyps
                                        (,eval-axe-syntaxp-expr-name syntaxp-expr alist dag-array))))
                      (if result
                          (,relieve-rule-hyps-name
                           (rest hyps) (+ 1 hyp-num) alist rule-symbol ;alist may have been extended by a hyp with free vars
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           equiv-alist rule-alist nodenums-to-assume-false print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                           prover-depth options (+ -1 count))
                        (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                     (cw "(Failed. Reason: Failed to relieve axe-syntaxp hyp (number ~x0): ~x1 for ~x2.)~%" hyp-num hyp rule-symbol))
                                (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))
                  (if (eq 'axe-bind-free fn)
                      (let* ((bind-free-expr (farg1 hyp)) ;; strip off the AXE-BIND-FREE
                             (result (and (all-vars-in-terms-bound-in-alistp (fargs bind-free-expr) alist) ; TODO: remove this check, since it should be guaranteed statically!  need a better guards in the alist wrt future hyps
                                          (,eval-axe-bind-free-function-application-name (ffn-symb bind-free-expr) (fargs bind-free-expr) alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                                          )))
                        (if result ;; nil to indicate failure, or an alist whose keys should be exactly (farg2 hyp)
                            (let ((vars-to-bind (farg2 hyp)))
                              (if (not (axe-bind-free-result-okayp result vars-to-bind dag-len))
                                  (mv (erp-t)
                                      (er hard? 'relieve-rule-hyps "Bind free hyp ~x0 for rule ~x1 returned ~x2, but this is not a well-formed alist that binds ~x3." hyp rule-symbol result vars-to-bind)
                                      alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                                ;; this hyp counts as relieved:
                                (,relieve-rule-hyps-name (rest hyps) (+ 1 hyp-num)
                                                         (append result alist) ;; guaranteed to be disjoint given the analysis done when the rule was made and the call of axe-bind-free-result-okayp above
                                                         rule-symbol dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                         equiv-alist rule-alist nodenums-to-assume-false print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                         prover-depth options (+ -1 count))))
                          ;; failed to relieve the axe-bind-free hyp:
                          (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                       (cw "(Failed.  Reason: Failed to relieve axe-bind-free hyp (number ~x0): ~x1 for ~x2.)~%" hyp-num hyp rule-symbol))
                                  (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))
                    ;; HYP is not a call to axe-syntaxp or axe-bind-free.
                    ;; First, we substitute in for all the vars in HYP that are bound in ALIST
                    ;; fixme precompute the list of vars in the hyp?
                    (mv-let
                      (instantiated-hyp free-vars-flg)
                      (instantiate-hyp-basic hyp alist nil interpreted-function-alist)
                      ;; INSTANTIATED-HYP is now a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars.
                      (if free-vars-flg ;can't be a work-hard since there are free vars?
                          ;; ALIST doesn't bind all the variables in the HYP, so we'll search for free variable matches in NODENUMS-TO-ASSUME-FALSE.
                          (,relieve-free-var-hyp-and-all-others-name nodenums-to-assume-false
                                                                     instantiated-hyp hyp-num
                                                                     (rest hyps)
                                                                     alist rule-symbol
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                     equiv-alist rule-alist
                                                                     nodenums-to-assume-false print
                                                                     info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                        ;; No more free vars remain in the hyp, so we try to relieve the fully instantiated hyp:
                        (b* ((old-try-count tries)
                             ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                              ;;try to relieve through rewriting (this tests atom hyps for symbolp even though i think that's impossible - but should be rare:
                              (,simplify-tree-name instantiated-hyp
                                                   'iff
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   rule-alist
                                                   nodenums-to-assume-false equiv-alist print
                                                   info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator
                                                   prover-depth options (+ -1 count)))
                             ((when erp) (mv erp
                                             nil ;hyps-relievedp
                                             nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                             (try-diff (and old-try-count (sub-tries tries old-try-count))))
                          (if (consp new-nodenum-or-quotep) ;tests for quotep
                              (if (unquote new-nodenum-or-quotep) ;hyp rewrote to a non-nil constant:
                                  (prog2$ (and old-try-count (or (eq :verbose print) (eq t print)) (< 100 try-diff) (cw "(~x0 tries used(p) ~x1:~x2)~%" try-diff rule-symbol hyp-num))
                                          (,relieve-rule-hyps-name
                                           (rest hyps) (+ 1 hyp-num) alist rule-symbol ;alist may have been extended by a hyp with free vars
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           equiv-alist rule-alist nodenums-to-assume-false print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                                ;;hyp rewrote to *nil* :
                                (progn$
                                 (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw "(~x1 tries wasted(p) ~x0:~x2 (rewrote to NIL))~%" rule-symbol try-diff hyp-num))
                                 (and (member-eq rule-symbol monitored-symbols)
                                      (cw "(Failed to relieve hyp ~x3 for ~x0.~% Reason: Rewrote to nil.~%Alist: ~x1.~%Assumptions (to assume false):~%~x2~%DAG:~x4)~%"
                                          rule-symbol
                                          alist
                                          nodenums-to-assume-false
                                          hyp
                                          :elided ;;todo: print dag-array? ;could print only the part of the dag below the maxnodenum in alist? can this stack overflow?
                                          ))
                                 (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                            ;;hyp didn't rewrite to a constant:
                            (prog2$
                             (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw "(~x1 tries wasted(p): ~x0:~x2 (non-constant result))~%" rule-symbol try-diff hyp-num))
                             ;; Give up:
                             (prog2$ ;todo: improve this printing?
                              (and (member-eq rule-symbol monitored-symbols)
                                   (progn$ (cw "(Failed to relieve hyp ~x0, namely, ~x1, for ~x2. " hyp-num hyp rule-symbol)
                                           (cw "Reason: Rewrote to:~%")
                                           (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep)
                                           (cw "Alist: ~x0.~%(Assumptions (to assume false):~%" alist)
                                           (print-dag-only-supporters-lst nodenums-to-assume-false 'dag-array dag-array)
                                           (cw "))~%") ;;(cw "Alist: ~x0.~%Assumptions (to assume false): ~x1~%DAG:~x2)~%" alist nodenums-to-assume-false dag-array)
                                           ))
                              (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))))))))))))

        ;; returns (mv erp new-rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
        ;; where if new-rhs-or-nil is nil, no rule applied. otherwise, new-rhs-or-nil is a tree with nodenums and quoteps at the leaves (what about free vars?  should free vars in the RHS be an error?)
        (defund ,try-to-apply-rules-name (stored-rules
                                          rule-alist
                                          args-to-match ;a list of nodenums and/or quoteps
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          nodenums-to-assume-false equiv-alist print info tries
                                          interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
          (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (true-listp stored-rules)
                                      (all-stored-axe-rulep stored-rules)
                                      (rule-alistp rule-alist)
                                      (all-dargp-less-than args-to-match dag-len)
                                      (true-listp args-to-match)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (or (endp stored-rules) ;no rule fired:
                  (zp-fast count)
                  )
              (mv (erp-nil) ;we could return an error of :count-exceeded here if (zp-fast count), but that might be slower
                  nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (let* ((stored-rule (first stored-rules))
                   (tries (and tries (increment-tries tries)))
                   ;;binds variables to nodenums or quoteps:
                   (alist-or-fail (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule)
                                                                  args-to-match
                                                                  dag-array
                                                                  dag-len)))
              (if (eq :fail alist-or-fail)
                  ;; the rule didn't match, so try the next rule:
                  (,try-to-apply-rules-name (rest stored-rules) rule-alist args-to-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenums-to-assume-false
                                            equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                ;; The rule matched. now try to relieve its hyps:
                (b* ((- (and (eq print :verbose) ;:verbose2?
                             (cw "(Trying: ~x0. Alist: ~x1~%"
                                 (stored-rule-symbol stored-rule)
                                 (reverse alist-or-fail) ;nicer to read if reversed
                                 )))
                     (hyps (stored-rule-hyps stored-rule))
                     ;;binding free vars might extend the alist:
                     ;;the dag may have been extended:
                     ((mv erp hyps-relievedp alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                      (if hyps
                          (,relieve-rule-hyps-name
                           hyps 1 alist-or-fail
                           (stored-rule-symbol stored-rule)
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           equiv-alist rule-alist nodenums-to-assume-false print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                        ;;if there are no hyps, don't even bother: BOZO inefficient?:
;perhaps if we failed to relieve the hyp we should use the old value of info and/or tries?
                        (mv (erp-nil) t alist-or-fail dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                     ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  (if hyps-relievedp
                      ;; instantiate the RHS:
                      (let ((rhs (my-sublis-var-and-eval-basic alist (stored-rule-rhs stored-rule) interpreted-function-alist))) ;fixme what if there are free vars in the rhs?
                        (prog2$ (and (member-eq print '(:verbose2 :verbose))
                                     (cw "Rewriting with ~x0. RHS: ~x1.)~%"
                                         (stored-rule-symbol stored-rule)
                                         rhs))
                                (mv (erp-nil)
                                    rhs
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    (and info (increment-hit-count-in-info-world (stored-rule-symbol stored-rule) info))
                                    tries
                                    )))
                    ;;failed to relieve the hyps, so try the next rule
                    (prog2$ (and (eq print :verbose)
                                 (cw "Failed to apply rule ~x0.)~%" (stored-rule-symbol stored-rule)))
                            (,try-to-apply-rules-name
                             (rest stored-rules)
                             rule-alist args-to-match
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                             nodenums-to-assume-false  equiv-alist print
                             info ;(cons (cons :fail (rule-symbol rule)) info)
                             tries
                             interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))))

        ;;  ;;new!
        ;;  ;;this also simplifies as it goes!
        ;; ;ffixme check that interpreted functions are consistent?!
        ;; ;can this add ifns to the alist?
        ;;  ;;returns (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
        ;;  (defund merge-embedded-dag-into-dag-for-basic-prover (rev-dag
        ;;                                                     renaming-array-name
        ;;                                                     renaming-array2 ;associates nodenums in the embedded dag with the nodenums (or quoteps) they rewrote to in the main dag
        ;;                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                     embedded-dag-var-alist ;associates vars in the embedded dag with their nodenums (or quoteps) in the main dag
        ;;                                                     rule-alist
        ;;                                                     nodenums-to-assume-false ;equality-assumptions
        ;;                                                     equiv-alist
        ;;                                                     print
        ;;                                                     info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count state)
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
        ;;                                (info-worldp info)
        ;;                                (triesp tries)
        ;;                                (interpreted-function-alistp interpreted-function-alist)
        ;;                                (symbol-listp monitored-symbols)
        ;;                                (natp embedded-dag-depth) ;can we just use the prover depth?
        ;;                                (stringp case-designator)

        ;;                                (natp prover-depth)
        ;;                                (axe-prover-optionsp options))
        ;;                    :measure (+ 1 (nfix count)))
        ;;             (type (unsigned-byte 59) count))
        ;;    (if (zp-fast count)
        ;;        (mv :count-exceeded renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
        ;;      (if (endp rev-dag)
        ;;          (mv (erp-nil) renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
        ;;        (let* ((entry (car rev-dag))
        ;;               (nodenum (car entry))
        ;;               (expr (cdr entry)))
        ;;          (if (atom expr) ;variable
        ;;              (let ((new-nodenum (lookup-eq-safe2 expr embedded-dag-var-alist 'merge-embedded-dag-into-dag-for-basic-prover))) ;drop the -safe?
        ;;                (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
        ;;                                                            renaming-array-name
        ;;                                                            (aset1-safe renaming-array-name renaming-array2 nodenum new-nodenum)
        ;;                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                            embedded-dag-var-alist
        ;;                                                            rule-alist
        ;;                                                            nodenums-to-assume-false ;equality-assumptions
        ;;                                                            equiv-alist
        ;;                                                            print
        ;;                                                            info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state))
        ;;            (if (quotep expr)
        ;;                (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
        ;;                                                            renaming-array-name
        ;;                                                            (aset1-safe renaming-array-name renaming-array2 nodenum expr)
        ;;                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                            embedded-dag-var-alist
        ;;                                                            rule-alist
        ;;                                                            nodenums-to-assume-false ;equality-assumptions
        ;;                                                            equiv-alist
        ;;                                                            print
        ;;                                                            info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state)
        ;;              ;;function call:
        ;;              ;;first fixup the call to be about nodenums in the main dag:
        ;;              (let* ((fn (ffn-symb expr))
        ;;                     (args (dargs expr))
        ;;                     (args (rename-args args renaming-array-name renaming-array2))
        ;;                     (expr (cons fn args)))
        ;;                ;;then simplify it:
        ;;                (mv-let (erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
        ;;                  ;;fffixme this can create a new renaming-array2 which can lead to slow-array warnings... <-- old comment?
        ;;                  (,simplify-tree-name expr
        ;;                                                               'equal ;fixme?
        ;;                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                               rule-alist
        ;;                                                               ;;nil ;;trees-equal-to-tree
        ;;                                                               nodenums-to-assume-false ;equality-assumptions
        ;;                                                               equiv-alist
        ;;                                                               print
        ;;                                                               info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state)
        ;;                  (if erp
        ;;                      (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
        ;;                    (merge-embedded-dag-into-dag-for-basic-prover (cdr rev-dag)
        ;;                                                                renaming-array-name
        ;;                                                                (aset1-safe renaming-array-name renaming-array2 nodenum new-nodenum-or-quotep)
        ;;                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                                embedded-dag-var-alist
        ;;                                                                rule-alist
        ;;                                                                nodenums-to-assume-false ;equality-assumptions
        ;;                                                                equiv-alist print
        ;;                                                                info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count) state))))))))))

        ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
        (defund ,simplify-if-tree-name (tree
                                        equiv
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alist
                                        nodenums-to-assume-false
                                        equiv-alist ;don't pass this around?
                                        print
                                        info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
          (declare (xargs :guard (and (axe-treep tree)
                                      (symbolp equiv)
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (bounded-axe-treep tree dag-len)
                                      (consp tree) ;; this case
                                      (member-eq (ffn-symb tree) '(if myif)) ;; this case
                                      (= 3 (len (fargs tree))) ;; this case
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ((args (fargs tree))
                 ;; First, try to resolve the if-test:
                 ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                  (,simplify-tree-name (first args) ;the test
                                       'iff ;can rewrite the test in a propositional context
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth
                                       case-designator prover-depth options (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
              (if (consp simplified-test) ;tests for quotep
                  ;; The test was resolved, so just simplify the appropriate branch:
                  (,simplify-tree-name (if (unquote simplified-test)
                                           (second args) ;then branch
                                         (third args)    ;else branch
                                         )
                                       equiv ;use the same equiv
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols
                                       embedded-dag-depth case-designator prover-depth options (+ -1 count))
                ;; The test was not resolved, so we must rewrite both branches: ;; todo: just call simplify-tree twice here?
                (b* (((mv erp simplified-other-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                      (,simplify-trees-name (rest args)
                                            '(equal equal) ;;equiv-lst ;todo: use the same equiv as for the whole term?
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist nodenums-to-assume-false
                                            equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                     ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  (,simplify-fun-call-name (ffn-symb tree)
                                           (cons simplified-test simplified-other-args)
                                           equiv
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist
                                           nodenums-to-assume-false
                                           equiv-alist
                                           print
                                           info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))

        ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
        (defund ,simplify-boolif-tree-name (tree ;pass less?
                                            equiv
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist
                                            nodenums-to-assume-false
                                            equiv-alist ;don't pass this around?
                                            print
                                            info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
          (declare (xargs :guard (and (axe-treep tree)
                                      (symbolp equiv)
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (bounded-axe-treep tree dag-len)
                                      (consp tree)         ;; this case
                                      (eq (ffn-symb tree) 'boolif) ;; this case
                                      (= 3 (len (fargs tree)))     ;; this case
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ((args (fargs tree))
                 ;; First, try to resolve the if-test:
                 ((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                  (,simplify-tree-name (first args) ;the test
                                       'iff ;can rewrite the test in a propositional context
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth
                                       case-designator prover-depth options (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
              (if (consp simplified-test) ;tests for quotep
                  ;; The test was resolved, so just simplify the appropriate branch:
                  (,simplify-tree-name (if (unquote simplified-test)
                                           `(bool-fix$inline ,(second args)) ;then branch
                                         `(bool-fix$inline ,(third args)) ;else branch
                                         )
                                       equiv ;use the same equiv, todo: consider using IFF here
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols
                                       embedded-dag-depth case-designator prover-depth options (+ -1 count))
                ;; The test was not resolved, so we must rewrite both branches: ;; todo: just call simplify-tree twice here?
                (b* (((mv erp simplified-other-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                      (,simplify-trees-name (rest args)
                                            '(equal equal) ;;equiv-lst ;todo: use '(iff iff) here, or try the same equiv as for the whole term?
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rule-alist nodenums-to-assume-false
                                            equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                     ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  (,simplify-fun-call-name (ffn-symb tree)
                                           (cons simplified-test simplified-other-args)
                                           equiv
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rule-alist
                                           nodenums-to-assume-false
                                           equiv-alist
                                           print
                                           info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))))))

        ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
        ;; Takes a FN and simplified ARGS.  No special handling for IFs, lambdas, or ground terms.
        (defund ,simplify-fun-call-name (fn   ; a function symbol
                                         args ; the simplified args
                                         equiv
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rule-alist
                                         nodenums-to-assume-false
                                         equiv-alist ;don't pass this around?
                                         print
                                         info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
          (declare (xargs :guard (and (symbolp fn)
                                      (not (equal 'quote fn))
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (true-listp args)
                                      (all-dargp-less-than args dag-len)
                                      (symbolp equiv)
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ( ;; Try to apply rules:
                 ((mv erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                  (,try-to-apply-rules-name
                   (get-rules-for-fn fn rule-alist)
                   rule-alist args
                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
              (if rhs-or-nil
                  ;; A rule fired, so rewrite the instantiated RHS:
                  ;; TODO: should try-to-apply-rules-name make this call directly?  if so, what should it do in case of failure?
                  (,simplify-tree-name
                   rhs-or-nil
                   equiv ;; was: 'equal
                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   rule-alist nodenums-to-assume-false equiv-alist
                   print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                ;; No rule fired, so no simplification can be done.  This node is ready to add to the dag:
                (b* ((- (and (eq :verbose print) (cw "(Making ~x0 term with args: ~x1.)~%" fn args)))
                     ((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                      ;; todo: make a variant that takes (cons fn args), which we compute above:
                      ;; todo: perhaps inline this:
                      (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                     ((when erp) (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  ;; Finally, see if the node can be replaced by
                  ;; something using the assumptions.  Note that
                  ;; this uses the simplified args, so
                  ;; assumptions not in normal form may have no effect.
                  (let ((assumption-match (replace-nodenum-using-assumptions-for-axe-prover nodenum equiv nodenums-to-assume-false dag-array))) ;currently, this can only be a constant?
                    (mv (erp-nil)
                        (if assumption-match
                            ;; we replace the term with something it's equated to in nodenums-to-assume-false. we don't simplify the resulting thing (currently a constant). eventually, we might need to think about handling chains of equalities.:
                            assumption-match
                          nodenum)
                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))))))

        ;; Rewrite TREE repeatedly using RULE-ALIST and NODENUMS-TO-ASSUME-FALSE and add the result to the dag, returning a nodenum or a quotep.
        ;; TREE has nodenums and quoteps and variables (really? yes, from when we call this on a worklist of nodes) at the leaves.
        ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
        ;; be sure we always handle lambdas early, in case one is hiding an if - fixme - skip this for now?
        (defund ,simplify-tree-name (tree
                                     equiv
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     rule-alist
                                     nodenums-to-assume-false
                                     equiv-alist ;don't pass this around?
                                     print
                                     info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options count)
          (declare (xargs :guard (and (axe-treep tree)
                                      (symbolp equiv)
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (bounded-axe-treep tree dag-len)
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist)
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (if (atom tree)
                (if (symbolp tree) ;; TODO: Prove that this case is impossible.
                    (progn$ ;;nil ;;(cw "Rewriting the variable ~x0" tree) ;new!
                     (er hard? ',simplify-tree-name "rewriting the var ~x0" tree)
                     (mv :unexpected-var nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                      ;; It's a variable:  todo: perhaps add it first and then use assumptions?
                     ;;                      ;; First try looking it up in the assumptions (fixme make special version of rewrite-term-using-assumptions-for-basic-prover for a variable?):
                     ;;                      (let ((assumption-match (replace-term-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array print)))
                     ;;                        (if assumption-match
                     ;;                            ;; We replace the variable with something it's equated to in nodenums-to-assume-false.
                     ;;                            ;; We don't rewrite the result (by the second pass, nodenums-to-assume-false will be simplified - and maybe we should always do that?)
                     ;; ;fixme what if there is a chain of equalities to follow?
                     ;;                            (mv nil assumption-match dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                          ;; no match, so we just add the variable to the DAG:
                     ;;                          ;;make this a macro? this one might be rare..  same for other adding to dag operations?
                     ;;                          (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist) ;fixme simplify nodenum?
                     ;;                            (add-variable-to-dag-array tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                     ;;                            (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))
                     )
                  ;; TREE is a nodenum (because it's an atom but not a symbol):
                  ;;fffixme what if tree is the nodenum of a constant?
                  (let ((assumption-match (replace-nodenum-using-assumptions-for-axe-prover tree equiv nodenums-to-assume-false dag-array)))
                    (if assumption-match ;;TODO: We know (for now) that this must be a constant
                        ;;fffixme don't simplify here, since nodenums-to-assume-false will be simplified after the 1st pass (what about chains of equalities)?
                        (,simplify-tree-name assumption-match
                                             equiv dag-array dag-len dag-parent-array dag-constant-alist
                                             dag-variable-alist
                                             rule-alist nodenums-to-assume-false  equiv-alist print
                                             info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                      (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))
              ;; TREE is not an atom:
              (let ((fn (ffn-symb tree)))
                (case fn
                  (quote ;; TREE is a quoted constant, so return it:
                   (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                  ((if myif)
                   (if (= 3 (len (fargs tree)))
                       (,simplify-if-tree-name tree
                                               equiv
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist
                                               nodenums-to-assume-false
                                               equiv-alist ;don't pass this around?
                                               print
                                               info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     (mv :bad-arity tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  (boolif
                   (if (= 3 (len (fargs tree)))
                       (,simplify-boolif-tree-name tree
                                                   equiv
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   rule-alist
                                                   nodenums-to-assume-false
                                                   equiv-alist ;don't pass this around?
                                                   print
                                                   info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     (mv :bad-arity tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  ;; TODO: Consider adding back special handling for bvif, booland, and boolor (see below), but do it in separate functions
                  (t ;; TREE is a function call. fn may be a lambda or a short-circuit-function (if/myif/boolif/bvif/booland/boolor):
                   ;; (let ((args (fargs tree)))
                     ;; ;;Rewrite the args, *except* if it's a short-circuit function, we may be able to avoid rewriting them all and instead just return a new term to rewrite (will that new term ever be a constant?).
                     ;; (mv-let
                     ;;   (erp short-circuitp term-or-rewritten-args ;if short-circuitp is non-nil, then this is a term equal to fn applied to args, else it's a list of rewritten args
                     ;;        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;   (if (eq 'bvif fn) ;;(bvif size test thenpart elsepart)
                     ;;       ;; First, try to resolve the if-test:
                     ;;       (mv-let (erp test-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;         (,simplify-tree-name (second args) ;the test
                     ;;                              'iff ;can rewrite the test in a propositional context
                     ;;                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                              rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols
                     ;;                              embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;         (if erp
                     ;;             (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;           (if (consp test-result) ;tests for quotep
                     ;;               (mv (erp-nil)
                     ;;                   t ;; did short-circuit
                     ;;                   (if (unquote test-result)
                     ;;                       `(bvchop ;$inline
                     ;;                         ,(first args) ,(third args)) ;then branch
                     ;;                     `(bvchop ;$inline
                     ;;                       ,(first args) ,(fourth args))) ;else branch
                     ;;                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;             ;;didn't resolve the test; must rewrite the other arguments:
                     ;;             (mv-let (erp other-arg-results dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;               (,simplify-trees-name (cons (first args) ;the size
                     ;;                                           (cddr args) ;then part and else part
                     ;;                                           )
                     ;;                                     '(equal equal equal) ;;equiv-lst
                     ;;                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                     rule-alist nodenums-to-assume-false
                     ;;                                     equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;               (if erp
                     ;;                   (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                 (mv (erp-nil) nil ;did not short-circuit
                     ;;                     (cons (first other-arg-results)
                     ;;                           (cons test-result
                     ;;                                 (cdr other-arg-results)))
                     ;;                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))
                     ;;     (if (eq 'booland fn) ;;(booland arg1 arg2)
                     ;;         ;; First, rewrite arg1:
                     ;;         (mv-let (erp arg1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;           (,simplify-tree-name (first args)
                     ;;                                'iff ;can rewrite the arg in a propositional context
                     ;;                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist
                     ;;                                monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;           (if erp
                     ;;               (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;             (if (equal *nil* arg1-result)
                     ;;                 (mv (erp-nil)
                     ;;                     t       ;; did short-circuit
                     ;;                     *nil*   ;; (booland nil x) = nil
                     ;;                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;               ;;arg1 didn't rewrite to nil (fixme could handle if it rewrote to t); must rewrite the other argument:
                     ;;               (mv-let (erp arg2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                 (,simplify-tree-name (second args)
                     ;;                                      'iff ;can rewrite the arg in a propositional context
                     ;;                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                      rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist
                     ;;                                      monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;                 (if erp
                     ;;                     (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                   (mv (erp-nil)
                     ;;                       nil ;did not short-circuit
                     ;;                       (list arg1-result arg2-result)
                     ;;                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))
                     ;;       (if (eq 'boolor fn) ;;(boolor arg1 arg2)
                     ;;           ;; First, rewrite arg1
                     ;;           (mv-let (erp arg1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;             (,simplify-tree-name (first args)
                     ;;                                  'iff ;can rewrite the arg in a propositional context
                     ;;                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                  rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist
                     ;;                                  monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;             (if erp
                     ;;                 (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;               (if (and (consp arg1-result) (unquote arg1-result)) ;checks for a non-nil constant
                     ;;                   (mv (erp-nil)
                     ;;                       t     ;; did short-circuit
                     ;;                       *t* ;boolor of a non-nil value is t
                     ;;                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                 ;;arg1 didn't rewrite to a non-nil constant (fixme could handle if it rewrote to nil); must rewrite the other argument:
                     ;;                 (mv-let (erp arg2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                   (,simplify-tree-name (second args)
                     ;;                                        'iff ;can rewrite the arg in a propositional context
                     ;;                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                        rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist
                     ;;                                        monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;                   (if erp
                     ;;                       (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;                     (mv (erp-nil)
                     ;;                         nil ;did not short-circuit
                     ;;                         (list arg1-result arg2-result)
                     ;;                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))
                     ;;         ;;not a short-circuit-function:
                     ;;         (mv-let (erp arg-results dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;           (,simplify-trees-name args
                     ;;                                 (get-equivs equiv fn equiv-alist)
                     ;;                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     ;;                                 rule-alist nodenums-to-assume-false
                     ;;                                 equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))
                     ;;           (if erp
                     ;;               (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                     ;;             (mv (erp-nil)
                     ;;                 nil ;did not short-circuit
                     ;;                 arg-results
                     ;;                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))
                       ;; (if erp
                       ;;     (mv erp tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                       ;;   (if short-circuitp
                       ;;       ;;just simplify the term returned from short-circuit rewriting:
                       ;;       (,simplify-tree-name term-or-rewritten-args
                       ;;                            equiv ;use the same equiv
                       ;;                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       ;;                            rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols
                       ;;                            embedded-dag-depth case-designator prover-depth options (+ -1 count))
                   ;;Rewrite the args:
                   (b* (((mv erp simplified-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                         (,simplify-trees-name (fargs tree)
                                               (get-equivs equiv fn equiv-alist)
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alist nodenums-to-assume-false
                                               equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                     ;; Now we simplify the function applied to the simplified args:
                     (if (consp fn) ;;tests for lambda
                         ;; It's a lambda, so we beta-reduce and simplify the result:
                         ;; note that we don't look up lambdas in the nodenums-to-assume-false (this is consistent with simplifying first)
                         (let* ((formals (second fn))
                                (body (third fn))
                                ;;BOZO could optimize this pattern: (my-sublis-var-and-eval-basic (my pairlis$ formals args) body ..)
                                (new-expr (my-sublis-var-and-eval-basic (pairlis$ formals simplified-args) body interpreted-function-alist)))
                           (,simplify-tree-name new-expr
                                                equiv ; was: 'equal
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                rule-alist
                                                nodenums-to-assume-false  equiv-alist print
                                                info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
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
                                     (if (eq :unknown-function erp)
                                         (mv (erp-nil) nil nil) ;no error, but it didn't produce a value (todo: print a warning?)
                                       ;; anything else non-nil is a true error:
                                       (mv erp nil nil))
                                   ;; normal case, evaluation worked:
                                   (mv (erp-nil) t val)))))
                            ;; I suppose we could suppress any evaluator error here if we choose to (might be a bit faster)?
                            ((when erp) (mv erp tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                         (if evaluatedp
                             (mv (erp-nil)
                                 (enquote val)
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 info tries)
                           ;; It wasn't a ground term (that we can evaluate).
                           (,simplify-fun-call-name fn
                                                    simplified-args
                                                    equiv
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    rule-alist
                                                    nodenums-to-assume-false
                                                    equiv-alist ;don't pass this around?
                                                    print
                                                    info tries interpreted-function-alist monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count))))))))))))

        ;; Simplify all the trees in TREES and add to the DAG.
        ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
        ;; If the items in TREES are already all nodenums or quoted constants, this doesn't re-cons-up the list.
        ;; (not tail-recursive, btw.)
        (defund ,simplify-trees-name (trees
                                      equivs
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alist nodenums-to-assume-false
                                      equiv-alist print info tries interpreted-function-alist monitored-symbols
                                      embedded-dag-depth case-designator prover-depth
                                      options count)
          (declare (xargs :guard (and (true-listp trees)
                                      (all-axe-treep trees)
                                      (symbol-listp equivs)
                                      (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (all-bounded-axe-treep trees dag-len)
                                      (rule-alistp rule-alist)
                                      (nat-listp nodenums-to-assume-false)
                                      (all-< nodenums-to-assume-false dag-len)
                                      (equiv-alistp equiv-alist) ;strengthven?
                                      ;; print
                                      (info-worldp info)
                                      (triesp tries)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (symbol-listp monitored-symbols)
                                      (natp embedded-dag-depth) ;can we just use the prover depth?
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (if (endp trees)
                (mv (erp-nil) trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
              (b* ( ;; this simplifies the arguments in reverse order (TODO: why?)
                   ((mv erp rest-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                    (,simplify-trees-name (rest trees)
                                          (rest equivs)
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rule-alist nodenums-to-assume-false  equiv-alist print info tries interpreted-function-alist
                                          monitored-symbols embedded-dag-depth case-designator prover-depth options (+ -1 count)))
                   ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                   ((mv erp first-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                    (,simplify-tree-name (first trees)
                                         (first equivs)
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rule-alist nodenums-to-assume-false equiv-alist print info tries interpreted-function-alist monitored-symbols
                                         embedded-dag-depth
                                         case-designator prover-depth options (+ -1 count)))
                   ((when erp) (mv erp trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                (mv (erp-nil)
                    (cons-with-hint first-result rest-result trees)
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))))

        ;;           (mv-let (rewritten-if-test ;if this is non-nil, tree is an if (or related thing) and this is what the test rewrote to
        ;;                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
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
        ;;                                                                      nodenums-to-assume-false  equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth
        ;;                                                                      options (+ -1 count)))
        ;;                     ;;it's not an IF, so we didn't even attempt to resolve an IF test:
        ;;                     (mv nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
        ;;                   (if rewritten-if-test ;we resolved the test
        ;;                       ;; The test rewrote to a constant, so TREE is equal to its "then" branch or its "else" branch:
        ;;                       (,simplify-tree-name (if (unquote rewritten-if-test)
        ;;                                                                        (fargn tree 2) ;;thenpart
        ;;                                                                      (fargn tree 3) ;;elsepart
        ;;                                                                      )
        ;;                                                                    equiv ;; was: 'equal
        ;;                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                                    rule-alist
        ;;                                                                    nodenums-to-assume-false  equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count))
        ;; ;could not resolve the if test to a constant (treat it like a regular function symbol, but reuse the rewritten test:

        ;;                     (let ((args (fargs tree)))
        ;;                       ;; We are simplifying a call to FN on ARGS, where ARGS are trees.
        ;;                       ;; FN might be a lambda.
        ;;                       ;; FN might be IF/etc for which we couldn't resolve the test.
        ;;                       ;; bozo might it be possible to not check for ground-terms because we never build them -- think about where terms might come from other than my-sublis-var which we could change to not build ground terms (of functions we know about)
        ;;                       ;; First we simplify the args:
        ;;                       ;; ffixme maybe we should try to apply rules here (maybe outside-in rules) instead of rewriting the args
        ;;                       ;;fixme could pass in a flag for the common case where the args are known to be already simplified (b/c the tree is a dag node?) - but are they simplified in this context?
        ;;                       (mv-let (args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries changed-anything-flg)
        ;;                               (if rewritten-if-test
        ;;                                   ;;don't rewrite the if-test again!
        ;;                                   (mv-let
        ;;                                    (nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                                         info tries changed-anything-flg)
        ;;                                    (,simplify-trees-name
        ;;                                     (cdr args) ;skip the if-test
        ;;                                     (cdr (get-equivs equiv fn equiv-alist)) ;lookup what equivs to use for the arguments ;;;;forgot the cdr on this line!
        ;;                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rule-alist
        ;;                                     nodenums-to-assume-false  equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count))
        ;;                                    (mv (cons rewritten-if-test nodenums-or-quoteps)
        ;;                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
        ;;                                        info tries changed-anything-flg))
        ;;                                 ;;rewrite all the args:
        ;;                                 (,simplify-trees-name
        ;;                                  args
        ;;                                  (get-equivs equiv fn equiv-alist) ;lookup what equivs to use for the arguments
        ;;                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rule-alist
        ;;                                  nodenums-to-assume-false  equiv-alist print info tries interpreted-function-alist monitored-symbols embedded-dag-depth options (+ -1 count)))
        ;;                               (declare (ignore changed-anything-flg)) ;could pass in tree and below check this flag to decide whether to use tree or cons fn onto the simplified args...
        ;;                               ))))))))

        ) ;end mutual-recursion for Axe Prover

       ;; TODO: Why is this so slow?
       (make-flag ,relieve-free-var-hyp-and-all-others-name)

       (,(pack$ 'defthm-flag- relieve-free-var-hyp-and-all-others-name)
         (DEFTHM ,(pack$ RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS-name '-return-type)
           (IMPLIES (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len)
                         (nat-listp nodenums-to-assume-false-to-walk-down)
                         (all-< nodenums-to-assume-false-to-walk-down dag-len)
                         (axe-treep hyp)
                         (natp hyp-num)
                         (axe-rule-hyp-listp other-hyps)
                         (symbol-alistp alist)
                         (symbolp rule-symbol)
                         (equiv-alistp equiv-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options)
                         )
                    (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS
                      (declare (ignore HYPS-RELIEVEDP))
                      (implies (not erp)
                               (and (symbol-alistp extended-alist)
                                    (all-dargp-less-than (strip-cdrs extended-alist) new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,RELIEVE-FREE-VAR-HYP-AND-ALL-OTHERS-name)
         (DEFTHM ,(pack$ RELIEVE-rule-HYPS-name '-return-type)
           (IMPLIES (and (axe-rule-hyp-listp hyps)
                         (natp hyp-num)
                         (symbol-alistp alist)
                         (symbolp rule-symbol)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-dargp-less-than (strip-cdrs alist) dag-len)
                         (equiv-alistp equiv-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-relieve-rule-hyps
                      (declare (ignore HYPS-RELIEVEDP))
                      (implies (not erp)
                               (and (symbol-alistp extended-alist)
                                    (all-dargp-less-than (strip-cdrs extended-alist) new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,RELIEVE-rule-HYPS-name)
         (DEFTHM ,(pack$ TRY-TO-APPLY-RULES-name '-return-type)
           (IMPLIES (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (true-listp stored-rules)
                         (all-stored-axe-rulep stored-rules)
                         (rule-alistp rule-alist)
                         (all-dargp-less-than args-to-match dag-len)
                         ;; (true-listp args-to-match)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-try-to-apply-rules
                      (implies (not erp)
                               (and (or (and (axe-treep new-rhs-or-nil) ;todo: variable-free?
                                             (bounded-axe-treep new-rhs-or-nil new-dag-len))
                                        (null new-rhs-or-nil))
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,TRY-TO-APPLY-RULES-name)
         (DEFTHM ,(pack$ SIMPLIFY-if-TREE-name '-return-type)
           (IMPLIES (and (axe-treep tree)
                         (symbolp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-treep tree dag-len)
                         (consp tree) ;; this case
                         (member-eq (ffn-symb tree) '(if myif)) ;; this case
                         (= 3 (len (fargs tree)))               ;; this case
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-if-tree
                      (implies (not erp)
                               (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,SIMPLIFY-if-TREE-name)
         (DEFTHM ,(pack$ SIMPLIFY-boolif-TREE-name '-return-type)
           (IMPLIES (and (axe-treep tree)
                         (symbolp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-treep tree dag-len)
                         (consp tree)                              ;; this case
                         (eq (ffn-symb tree) 'boolif)              ;; this case
                         (= 3 (len (fargs tree)))                  ;; this case
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-boolif-tree
                      (implies (not erp)
                               (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,SIMPLIFY-boolif-TREE-name)
         (DEFTHM ,(pack$ SIMPLIFY-fun-call-name '-return-type)
           (IMPLIES (and (symbolp fn)
                         (not (equal 'quote fn))
                         (true-listp args)
                         (all-dargp-less-than args dag-len)
                         (symbolp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-fun-call
                      (implies (not erp)
                               (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,SIMPLIFY-fun-call-name)
         (DEFTHM ,(pack$ SIMPLIFY-TREE-name '-return-type)
           (IMPLIES (and (axe-treep tree)
                         (symbolp equiv)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (bounded-axe-treep tree dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-tree
                      (implies (not erp)
                               (and (dargp-less-than nodenum-or-quotep new-dag-len)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,SIMPLIFY-TREE-name)
         (DEFTHM ,(pack$ SIMPLIFY-TREES-name '-return-type)
           (IMPLIES (and (true-listp trees)
                         (all-axe-treep trees)
                         (symbol-listp equivs)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-bounded-axe-treep trees dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         ;; print
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth) ;can we just use the prover depth?
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-trees
                      (implies (not erp)
                               (and (all-dargp-less-than nodenums-or-quoteps new-dag-len)
                                    (true-listp nodenums-or-quoteps)
                                    (equal (len nodenums-or-quoteps)
                                           (len trees))
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (<= dag-len new-dag-len)
                                    (info-worldp info)
                                    (triesp tries)))))
           :FLAG ,SIMPLIFY-TREES-name)
         :hints (("Goal" :expand (,call-of-simplify-trees
                                  ,call-of-simplify-if-tree
                                  ,call-of-simplify-boolif-tree
                                  ,call-of-simplify-tree
                                  ,call-of-simplify-fun-call
                                  ,call-of-relieve-rule-hyps
                                  (:free (other-hyps) ,call-of-relieve-free-var-hyp-and-all-others)
                                  (:free (info tries) ,call-of-try-to-apply-rules)
                                  (,relieve-rule-hyps-name nil ; note the nil
                                                           hyp-num
                                                           alist
                                                           rule-symbol
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           equiv-alist rule-alist
                                                           nodenums-to-assume-false
                                                           print info tries interpreted-function-alist
                                                           monitored-symbols embedded-dag-depth
                                                           case-designator
                                                           prover-depth options count)
                                  (,relieve-free-var-hyp-and-all-others-name nil ; note the nil
                                                                             hyp
                                                                             hyp-num
                                                                             other-hyps
                                                                             alist rule-symbol
                                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                             equiv-alist rule-alist
                                                                             nodenums-to-assume-false
                                                                             print
                                                                             info tries interpreted-function-alist monitored-symbols
                                                                             embedded-dag-depth
                                                                             case-designator prover-depth options count)
                                  (,simplify-trees-name nil ;note the nil
                                                        equivs
                                                        dag-array dag-len dag-parent-array
                                                        dag-constant-alist dag-variable-alist
                                                        rule-alist nodenums-to-assume-false
                                                        equiv-alist print
                                                        info tries interpreted-function-alist
                                                        monitored-symbols
                                                        embedded-dag-depth case-designator
                                                        prover-depth options count)
                                  (,try-to-apply-rules-name nil ; note the nil
                                                            rule-alist
                                                            args-to-match
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            nodenums-to-assume-false equiv-alist print info tries
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
                               ,@*make-prover-simple-rules*)
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
                       (natp hyp-num)
                       (symbol-alistp alist)
                       (symbolp rule-symbol)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-dargp-less-than (strip-cdrs alist) dag-len)
                       (equiv-alistp equiv-alist)
                       (rule-alistp rule-alist)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       ;; print
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp hyps-relievedp extended-alist new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-relieve-rule-hyps
                    (declare (ignore hyps-relievedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (all-dargp (strip-cdrs extended-alist)))))
         :hints (("Goal" :use (:instance ,(pack$ relieve-rule-hyps-name '-return-type))
                  :in-theory (disable ,(pack$ relieve-rule-hyps-name '-return-type)))))

       (defthm ,(pack$ try-to-apply-rules-name '-return-type-corollary)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (true-listp stored-rules)
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rule-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       ;; (true-listp args-to-match)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (equiv-alistp equiv-alist)
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-try-to-apply-rules
                    (declare (ignore new-dag-variable-alist info tries))
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
                       (true-listp stored-rules)
                       (all-stored-axe-rulep stored-rules)
                       (rule-alistp rule-alist)
                       (all-dargp-less-than args-to-match dag-len)
                       ;; (true-listp args-to-match)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (equiv-alistp equiv-alist)
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-rhs-or-nil new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-try-to-apply-rules
                    (declare (ignore new-rhs-or-nil new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (<= dag-len new-dag-len))))
         :rule-classes :linear
         :hints (("Goal" :use (:instance ,(pack$ try-to-apply-rules-name '-return-type))
                  :in-theory (disable ,(pack$ try-to-apply-rules-name '-return-type)))))

       (defthm ,(pack$ simplify-tree-name '-return-type-corollary)
         (implies (and (axe-treep tree)
                       (symbolp equiv)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (bounded-axe-treep tree dag-len)
                       (rule-alistp rule-alist)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (equiv-alistp equiv-alist)
                       ;; print
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth) ;can we just use the prover depth?
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-simplify-tree
                    (declare (ignore new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
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
                       (symbolp equiv)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (bounded-axe-treep tree dag-len)
                       (rule-alistp rule-alist)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (equiv-alistp equiv-alist)
                       ;; print
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth) ;can we just use the prover depth?
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-simplify-tree
                    (declare (ignore new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (and (<= dag-len new-dag-len)
                                  (implies (not (consp new-nodenum-or-quotep))
                                           (< new-nodenum-or-quotep new-dag-len))))))
         :rule-classes :linear
         :hints (("Goal" :use (:instance ,(pack$ simplify-tree-name '-return-type))
                  :in-theory (e/d (wf-dagp dargp-less-than)
                                  (,(pack$ simplify-tree-name '-return-type))))))

       (defthm ,(pack$ simplify-trees-name '-return-type-corollary)
           (implies (and (true-listp trees)
                         (all-axe-treep trees)
                         (symbol-listp equivs)
                         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (all-bounded-axe-treep trees dag-len)
                         (rule-alistp rule-alist)
                         (nat-listp nodenums-to-assume-false)
                         (all-< nodenums-to-assume-false dag-len)
                         (equiv-alistp equiv-alist)
                         (info-worldp info)
                         (triesp tries)
                         (interpreted-function-alistp interpreted-function-alist)
                         (symbol-listp monitored-symbols)
                         (natp embedded-dag-depth)
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                      ,call-of-simplify-trees
                      (declare (ignore new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                      (implies (not erp)
                               (and (all-dargp nodenums-or-quoteps)
                                    ;;(true-listp nodenums-or-quoteps)
                                    (equal (all-myquotep nodenums-or-quoteps)
                                           (all-consp nodenums-or-quoteps))
                                    ))))
           :hints (("Goal" :use (:instance ,(pack$ simplify-trees-name '-return-type))
                    :in-theory (e/d (all-myquotep-when-all-dargp) (,(pack$ simplify-trees-name '-return-type))))))

       (defthm ,(pack$ simplify-trees-name '-return-type-corollary-linear)
         (implies (and (true-listp trees)
                       (all-axe-treep trees)
                       (symbol-listp equivs)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (all-bounded-axe-treep trees dag-len)
                       (rule-alistp rule-alist)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (equiv-alistp equiv-alist)
                       (info-worldp info)
                       (triesp tries)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       (natp embedded-dag-depth)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    ,call-of-simplify-trees
                    (declare (ignore nodenums-or-quoteps new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (<= dag-len new-dag-len))))
         :rule-classes :linear
         :hints (("Goal" :use (:instance ,(pack$ simplify-trees-name '-return-type))
                  :in-theory (e/d (all-myquotep-when-all-dargp) (,(pack$ simplify-trees-name '-return-type))))))

       (verify-guards ,relieve-free-var-hyp-and-all-others-name
         :otf-flg t
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :do-not-induct t
                  ;; :use (:instance ,(pack$ SIMPLIFY-TREES-name '-return-type))
                  :expand (axe-rule-hyp-listp hyps)
                  :in-theory '(,@*make-prover-simple-rules*
                               (:e booleanp)
                               (:e expt)
                               (:e EQLABLEP)
                               (:e EQLABLE-LISTP)
                               MEMBER-EQ-EXEC-IS-MEMBER-EQUAL ;(:e member-eq-exec)
                               MEMBER-EQL-EXEC-is-member-equal
                               unsigned-byte-p-from-bounds
                               unsigned-byte-p-forward
                               rule-alistp-means-alistp
                               AXE-BIND-FREE-FUNCTION-APPLICATIONP
                               NATP-OF-+-OF-A-AND-LARGEST-NON-QUOTEP
                               <-OF-LARGEST-NON-QUOTEP
                               CONSP-WHEN-TRUE-LISTP-AND-NON-NIL
                               ;; RATIONALP-+
                               ;; RATIONALP-UNARY--
                               rationalp-when-integerp-for-axe
                               integerp-of-sub-tries
                               AXE-RULE-HYPP
                               STORED-AXE-RULEP
                               ALL-STORED-AXE-RULEP
                               true-listp-of-unify-terms-and-dag-items-fast
                               (:TYPE-PRESCRIPTION INTEGERP-OF-LARGEST-NON-QUOTEP)
                               (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP)
                               all-vars-in-terms-bound-in-alistp-correct
                               all-vars-in-term-bound-in-alistp-correct
                               SYMBOL-ALISTP-OF-PAIRLIS$-ALT
                               true-listp-of-cons
                               axe-treep-when-consp-of-car
                               not-<-of-largest-non-quotep-and--1
                               integerp-when-natp-for-axe
                               pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-other
                               INTEGERP-OF-MAXELEM2
                               integerp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
                               <-OF-MAXELEM-WHEN-ALL-<
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
                               ,(pack$ try-to-apply-rules-name '-return-type-corollary-linear))
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
       ;; Populates RESULT-ARRAY with the nodenums/quoteps that the nodes rewrote to.
       ;; Returns (mv erp result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
       ;; RESULT-ARRAY maps nodenums to the nodenums or quoteps to which they rewrote, or nil if the node hasn't been touched.
       ;; it seems possible for a node to get pushed onto the worklist more than once, but i guess a node cannot be pushed more times than it has parents (so not exponentially many times)?
       ;; todo: watch out for equality assumptions ordered the wrong way! - will they get rewritten the wrong way?
       ;; todo: special handling for if/myif/boolif/bvif/boolor/booland?
       ;; todo: track the equiv used for each node?
       ;; todo: track polarities?
       ;;this (and its callers) could take an explicit substitution for a variable, to support elim and substitute-a-var) - actually, i am changing those operations to not use rewriting..
       (defund ,rewrite-nodes-name (worklist ;could track the equivs and polarities?
                                    result-array-name result-array
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist
                                    print info tries monitored-symbols case-designator ;none of these should affect soundness
                                    prover-depth options count)
         (declare (xargs :guard (and (nat-listp worklist)
                                     (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (result-arrayp result-array-name result-array dag-len)
                                     (all-< worklist (alen1 result-array-name result-array))
                                     (all-< worklist dag-len)
                                     (nat-listp nodenums-to-assume-false)
                                     (all-< nodenums-to-assume-false dag-len)
                                     (rule-alistp rule-alist)
                                     (equiv-alistp equiv-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))
                         :guard-hints (("Goal" :in-theory (e/d (dag-function-call-exprp dag-function-call-exprp-redef) (dag-function-call-exprp))
                                        :do-not-induct t))
                         :measure (+ 1 (nfix count))) ;todo: improve?
                  (type (unsigned-byte 59) count))
         (if (zp-fast count)
             (mv :count-exceeded result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
           (if (endp worklist)
               (mv (erp-nil) result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
             (let* ((nodenum (first worklist)))
               (if (aref1 result-array-name result-array nodenum)
                   ;;we've already handled this node:
                   (,rewrite-nodes-name (rest worklist) result-array-name result-array
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist print info tries monitored-symbols
                                        case-designator prover-depth options (+ -1 count))
                 (if (member nodenum nodenums-to-assume-false) ;do we need this special case?  i guess it could help - what about more fancy use of nodenums-to-assume-false here?
                     (,rewrite-nodes-name
                      (rest worklist)
                      result-array-name (aset1-safe result-array-name result-array nodenum *nil*)
                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist print info tries monitored-symbols
                      case-designator prover-depth options (+ -1 count))
                   (b* ((- (and (eq :verbose print)
                                (cw "Processing node ~x0 (may have to process the args first).~%" nodenum)))
                        (expr (aref1 'dag-array dag-array nodenum)))
                     (if (atom expr) ;must be a variable - just add the node and rewrite that?
                         (b* (((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                               (simplify-var-and-add-to-dag-for-axe-prover expr
                                                                           'equal ;fixme can we do better? the worklist would have to track which equivs to use?
                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                           rule-alist nodenums-to-assume-false equiv-alist print
                                                                           info tries interpreted-function-alist monitored-symbols
                                                                           ;;0 ;embedded-dag-depth
                                                                           case-designator
                                                                           nil ;todo: drop
                                                                           prover-depth
                                                                           ;;options
                                                                           ))
                              ((when erp) (mv erp result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                           ;;option to print the number of rule hits?
                           (,rewrite-nodes-name
                            (rest worklist)
                            result-array-name
                            (aset1-safe result-array-name result-array nodenum new-nodenum-or-quotep) ;; update the result-array
                            dag-array dag-len dag-parent-array
                            dag-constant-alist dag-variable-alist
                            nodenums-to-assume-false rule-alist
                            equiv-alist interpreted-function-alist print info tries monitored-symbols case-designator prover-depth options (+ -1 count)))
                       (let ((fn (ffn-symb expr)))
                         (if (eq 'quote fn)
                             (,rewrite-nodes-name (rest worklist)
                                                  result-array-name
                                                  (aset1-safe result-array-name result-array nodenum expr) ;; update the result-array
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist print info tries monitored-symbols case-designator prover-depth options (+ -1 count))
                           ;;regular function call:
                           ;;first make sure that the args have been processed
                           ;;ffffixme special handling for if and related operators?!?
                           (let* ((args (dargs expr))
                                  (extended-worklist-or-nil (get-args-not-done args result-array-name result-array worklist nil)))
                             (if extended-worklist-or-nil
                                 ;;when the current node is processed again, some work will be redone
                                 (,rewrite-nodes-name
                                  extended-worklist-or-nil result-array-name result-array
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                  nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist print info tries monitored-symbols
                                  case-designator prover-depth options (+ -1 count))
                               ;;all args are simplified:
                               (b* ((args (lookup-args-in-result-array args result-array-name result-array)) ;combine this with the get-args-not-done somehow?
                                    (expr (cons fn args))
                                    (- (and (eq :verbose print)
                                            (cw "(Rewriting node ~x0." nodenum)))
                                    ((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                                     ;; TODO: use the fact that we know it's a function call with simplified args?
                                     (,simplify-tree-name expr
                                                          'equal ;fixme can we do better?
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                          rule-alist
                                                          nodenums-to-assume-false
                                                          equiv-alist print
                                                          info tries interpreted-function-alist monitored-symbols 0 case-designator prover-depth options (+ -1 count)))
                                    ((when erp) (mv erp result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                                    (-  (and (or ;(eq t print) ;new
                                              (eq :verbose print))
                                             (cw ")~%"))))
                                 ;;option to print the number of rule hits?
                                 (,rewrite-nodes-name
                                  (rest worklist) result-array-name
                                  (aset1-safe result-array-name result-array nodenum new-nodenum) ;; update the result-array
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                  nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist print info tries
                                  monitored-symbols case-designator prover-depth options (+ -1 count)))))))))))))))

       (defthm ,(pack$ rewrite-nodes-name '-return-type)
         (implies (and (nat-listp worklist)
                       (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (result-arrayp result-array-name result-array dag-len)
                       (all-< worklist (alen1 result-array-name result-array))
                       (all-< worklist dag-len)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (rule-alistp rule-alist)
                       (equiv-alistp equiv-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-result-array new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-nodes-name worklist result-array-name result-array
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         nodenums-to-assume-false rule-alist equiv-alist interpreted-function-alist
                                         print info tries monitored-symbols case-designator ;none of these should affect soundness
                                         prover-depth options count)
                    (implies (not erp)
                             (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (result-arrayp result-array-name new-result-array new-dag-len)
                                  (array1p result-array-name new-result-array) ;avoid an issue with a free var when backchaining from array1p to result-arrayp
                                  (equal (alen1 result-array-name new-result-array)
                                         (alen1 result-array-name result-array))
                                  (<= dag-len new-dag-len)
                                  (info-worldp info)
                                  (triesp tries)))))
         :hints (("Goal" :in-theory (enable ,rewrite-nodes-name))))

       ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
       ;; It would be nice to call a standard rewriter here, but the assumptions (nodenums-to-assume-false) are likely not in the right form.
       ;; TODO: can we use a better equiv?
       ;; TODO: Inline this?
       (defund ,rewrite-literal-name (nodenum
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      nodenums-to-assume-false
                                      rule-alist interpreted-function-alist
                                      info tries monitored-symbols print case-designator ;none of these should affect soundness
                                      prover-depth options)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (natp nodenum)
                                     (< nodenum dag-len)
                                     (nat-listp nodenums-to-assume-false)
                                     (all-< nodenums-to-assume-false dag-len)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))))
         (b* ((- (and (or (eq :verbose print) (eq :verbose2 print))
                      (cw "(Rewriting literal ~x0.~%" nodenum)))
              ;; Make an array to track results in the worklist algorithm:
              (result-array-name (pack$ 'result-array- prover-depth))
              (result-array (make-empty-array result-array-name dag-len) ;fixme dag-len here is overkill? use (+ 1 nodeum)?
                            )
              ;; Rewrite this literal:
              ((mv erp result-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
               ;;fixme would it make sense to memoize in this (moot if we call the new rewriter)?:
               (,rewrite-nodes-name (list nodenum)
                                    result-array-name
                                    result-array
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    nodenums-to-assume-false
                                    rule-alist
                                    *congruence-table* ;do we need to pass this around?
                                    interpreted-function-alist print info tries monitored-symbols case-designator prover-depth options (+ -1 (expt 2 59))))
              ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
              (- (and (or (eq :verbose print) (eq :verbose2 print))
                      (cw "  Done rewriting literal ~x0.)~%" nodenum)))
              (new-nodenum-or-quotep (aref1 result-array-name result-array nodenum))
              ((when (not new-nodenum-or-quotep)) ;todo: prove that this can't happen
               (er hard? ',rewrite-literal-name "Literal did not rewrite to anything!")
               (mv :error nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   info tries)))
           (mv (erp-nil)
               new-nodenum-or-quotep
               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
               info tries)))

       (defthm ,(pack$ rewrite-literal-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (natp nodenum)
                       (< nodenum dag-len)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literal-name nodenum
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nodenums-to-assume-false
                                           rule-alist interpreted-function-alist
                                           info tries monitored-symbols print case-designator ;none of these should affect soundness
                                           prover-depth options)
                    (implies (not erp)
                             (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (<= dag-len new-dag-len)
                                  (info-worldp info)
                                  (triesp tries)
                                  (dargp-less-than new-nodenum-or-quotep new-dag-len)))))
         :hints (("Goal" :in-theory (e/d (,rewrite-literal-name
                                          type-of-aref1-when-result-arrayp-2)
                                         (natp)))))

       (defthm ,(pack$ rewrite-literal-name '-return-type-corollary)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (natp nodenum)
                       (< nodenum dag-len)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literal-name nodenum
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nodenums-to-assume-false
                                           rule-alist interpreted-function-alist
                                           info tries monitored-symbols print case-designator ;none of these should affect soundness
                                           prover-depth options)
                    (declare (ignore new-nodenum-or-quotep new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (natp new-dag-len))))
         :hints (("Goal" :use (:instance ,(pack$ rewrite-literal-name '-return-type))
                  :in-theory (disable ,(pack$ rewrite-literal-name '-return-type)))))

       (defthm ,(pack$ rewrite-literal-name '-return-type-linear)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (natp nodenum)
                       (< nodenum dag-len)
                       (nat-listp nodenums-to-assume-false)
                       (all-< nodenums-to-assume-false dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp new-nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literal-name nodenum
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nodenums-to-assume-false
                                           rule-alist interpreted-function-alist
                                           info tries monitored-symbols print case-designator ;none of these should affect soundness
                                           prover-depth options)
                    (declare (ignore new-nodenum-or-quotep new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (<= dag-len new-dag-len))))
         :rule-classes :linear
         :hints (("Goal" :use (:instance ,(pack$ rewrite-literal-name '-return-type))
                  :in-theory (disable ,(pack$ rewrite-literal-name '-return-type)))))

       ;; Rewrite each of the literals in WORK-LIST once, and add the results to DONE-LIST.  When rewriting a literal, assume all
       ;; other literals (from WORK-LIST and DONE-LIST) false.
       ;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries),
       ;; where if PROVEDP is t, then the disjunction of WORK-LIST and DONE-LIST was proved to be non-nil,
       ;; and if PROVEDP is nil, then that disjunction is equuialent to the LITERAL-NODENUMS returned.
       ;; If provedp is non-nil, changep is meaningless..
       ;; Not a worklist algorithm of the usual sort (all elements of work-list are literals)
       ;; may extend the dag but doesn't change any nodes (new!).
       ;; TODO: If the only change is that some literals were dropped, perhaps we don't want to make another pass?
       (defund ,rewrite-literals-name (work-list ;a list of nodenums
                                       done-list ;a list of nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       changep ;; whether anything has changed so far
                                       rule-alist
                                       interpreted-function-alist monitored-symbols print case-designator
                                       info tries prover-depth options)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (nat-listp work-list)
                                     (all-< work-list dag-len)
                                     (nat-listp done-list)
                                     (all-< done-list dag-len)
                                     (booleanp changep)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (symbol-listp monitored-symbols)
                                     ;; print
                                     (stringp case-designator)
                                     (info-worldp info)
                                     (triesp tries)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))
                         :guard-hints (("Goal" :do-not-induct t))))
         (if (endp work-list)
             (progn$ (and (eq :verbose print) (progn$ (cw "(Literals after rewriting them all:~%")
                                                      (print-dag-only-supporters-lst done-list 'dag-array dag-array)
                                                      (cw "):~%")))
                     (mv (erp-nil)
                         nil ;did not prove the clause
                         changep done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
           (b* ((literal-nodenum (first work-list))
                (rest-work-list (rest work-list))
                (other-literals (append rest-work-list done-list)) ;todo: save this append somehow?
                ;; Rewrite the literal:
                ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                 (,rewrite-literal-name literal-nodenum
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        other-literals rule-alist interpreted-function-alist info tries monitored-symbols print case-designator prover-depth options))
                ((when erp) (mv erp nil nil done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                ;; (- (cw "Node ~x0 rewrote to ~x1 in dag:~%" literal-nodenum new-nodenum-or-quotep))
                ;; (- (if (quotep new-nodenum-or-quotep) (cw ":elided") (if (eql literal-nodenum new-nodenum-or-quote) :no-change (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep))))
                )
             (if (eql new-nodenum-or-quotep literal-nodenum)
                 ;; No change for this literal:
                 (,rewrite-literals-name rest-work-list
                                         (cons literal-nodenum done-list)
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         changep ;; no change to changep
                                         rule-alist interpreted-function-alist monitored-symbols print case-designator info tries prover-depth options)
               ;; Rewriting changed the literal.  Harvest the disjuncts, raising them to top level, and add them to the done-list:
               (b* (((mv erp provedp extended-done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                     (get-disjuncts new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    done-list ; will be extended with the disjuncts
                                    nil       ;negated-flg
                                    ))
                    ((when erp) (mv erp nil nil done-list dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                 (if provedp
                     (mv (erp-nil)
                         t   ;provedp
                         t   ;changep
                         nil ;literal-nodenums
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                   ;; Continue rewriting literals:
                   (,rewrite-literals-name rest-work-list
                                           extended-done-list
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           t ;; something changed
                                           rule-alist interpreted-function-alist monitored-symbols print case-designator info tries prover-depth options)))))))

       (defthm ,(pack$ rewrite-literals-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp work-list)
                       (all-< work-list dag-len)
                       (nat-listp done-list)
                       (all-< done-list dag-len)
                       (booleanp changep)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       ;; print
                       (stringp case-designator)
                       (info-worldp info)
                       (triesp tries)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literals-name work-list
                                            done-list
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            changep
                                            rule-alist
                                            interpreted-function-alist monitored-symbols print case-designator
                                            info tries prover-depth options)
                    (declare (ignore provedp changep))
                    (implies (not erp)
                             (and (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (<= dag-len new-dag-len)
                                  (info-worldp info)
                                  (triesp tries)
                                  (all-natp literal-nodenums)
                                  (true-listp literal-nodenums)
                                  (all-< literal-nodenums new-dag-len)))))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (,rewrite-literals-name) (natp)))))

       (defthm ,(pack$ rewrite-literals-name '-return-type-corollary)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp work-list)
                       (all-< work-list dag-len)
                       (nat-listp done-list)
                       (all-< done-list dag-len)
                       (booleanp changep)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       ;; print
                       (stringp case-designator)
                       (info-worldp info)
                       (triesp tries)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literals-name work-list
                                            done-list
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            changep
                                            rule-alist
                                            interpreted-function-alist monitored-symbols print case-designator
                                            info tries prover-depth options)
                    (declare (ignore provedp changep literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (pseudo-dag-arrayp 'dag-array new-dag-array new-dag-len))))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (,rewrite-literals-name) (natp)))))

       ;; This one is a :type-prescription rule
       (defthm ,(pack$ rewrite-literals-name '-return-type-2)
         (implies (true-listp done-list)
                  (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literals-name work-list
                                            done-list
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            changep
                                            rule-alist
                                            interpreted-function-alist monitored-symbols print case-designator
                                            info tries prover-depth options)
                    (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
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
                       (booleanp changep)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (symbol-listp monitored-symbols)
                       ;; print
                       (stringp case-designator)
                       (info-worldp info)
                       (triesp tries)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp changep literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries)
                    (,rewrite-literals-name work-list
                                            done-list
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            changep
                                            rule-alist
                                            interpreted-function-alist monitored-symbols print case-designator
                                            info tries prover-depth options)
                    (declare (ignore provedp changep literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist info tries))
                    (implies (not erp)
                             (<= dag-len new-dag-len))))
         :rule-classes :linear
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :in-theory (e/d (,rewrite-literals-name) (natp)))))

       ;; can this loop? probably, if the rules loop?
       ;; Returns (mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
       ;; where if provedp is non-nil we proved the clause and the other return values are irrelevant fffixme is test-cases?
       ;; otherwise, we return the simplified clause (as the list of literal nodenums and the dag-array, etc.)
       ;; perhaps this should return info, which the parent can print
       ;; old: this returns TEST-CASES because destructor elimination can change the vars and changes the test cases analogously.
       ;; There should be no harvestable disjuncts in the LITERAL-NODENUMS returned?
       (defund ,rewrite-subst-and-elim-with-rule-alist-name (literal-nodenums
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rule-alist rule-set-number
                                                             interpreted-function-alist monitored-symbols
                                                             case-designator print ;move print arg?
                                                             info tries prover-depth options count)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (nat-listp literal-nodenums)
                                     (all-< literal-nodenums dag-len)
                                     (rule-alistp rule-alist)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))
                         :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-strengthen-2 natp-of-+-of-1 rationalp-when-natp-for-axe) (natp))  :do-not-induct t))
                         :measure (+ 1 (nfix count)))
                  (type (unsigned-byte 59) count))
         (if (zp-fast count)
             (mv :count-exceeded nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
           (b* (;; TODO: Do this in the callers?  Maintain an invariant about disjuncts having been extracted from literal-nodenums?  May not be true after we substitute, so do this there instead?
                ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (get-disjuncts-from-nodes literal-nodenums
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           nil))
                ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                ((when provedp) (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                (- (cw "(Rewriting with rule set ~x0 (~x1 literals):~%" rule-set-number (len literal-nodenums))) ;the printed paren is closed below
                ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                 (,rewrite-literals-name literal-nodenums
                                         nil ;initial done-list
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         nil ;changep
                                         rule-alist
                                         interpreted-function-alist monitored-symbols print case-designator
                                         info tries prover-depth options))
                (- (cw "  Done rewriting (~x0 literals).)~%" (len literal-nodenums)))
                ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))

                ;; TODO: Right here we could drop any literal of the form (equal <constant> <var>) - if the var appears in any other literal, rewriting should have put in the constant for it, so the var will no longer appear.
                ;; ;todo: this printing should be moved outward!  because now info and tries are threaded through - to print stats for a smaller operation, we could subtract
                ;;              (and print
                ;;                   (or (eq :verbose print) (eq t print)) ;new
                ;;                   (if (or (eq :verbose print) (eq t print)) ; was (eq :verbose print)
                ;;                       (cw "(Rule hits (~x0 total): ~x1)~%" (len info) (summarize-info-world info))
                ;;                     ;;ffixme in this case the info that we keep could just be a count!
                ;;                     (cw "(~x0 rule hits)~%" (len info))))
                ;;              ;;ffffffixme this printing should be moved outward!
                ;;              (and tries
                ;;                   (or (eq :verbose print) (eq t print)) ;new
                ;;                   (cw "(~x0 tries.)~%" tries))
                )
             (if provedp
                 (mv (erp-nil) t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
               (b* ( ;; Maybe crunch (one advantage in doing this is to make the printed result of this step comprehensible if we are tracing):
                    ((mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums)
                     (if (or (not (= prover-depth 0)) ;; can't crunch if prover-depth > 0 since that would change existing nodes:
                             (not (consp literal-nodenums)) ;;can't crunch if no nodenums (can this happen?)
                             )
                         (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums)
                       (b* (;; (- (cw "(Crunching: ...")) ;; matching paren printed below
                            ((mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums)
                             (crunch-dag-array2-with-indices 'dag-array dag-array dag-len 'dag-parent-array literal-nodenums))
                            ;; TODO: Prove that this can't happen.  Need to know that
                            ;; build-reduced-nodes maps all of the literal-nodenums to
                            ;; nodenums (not constants -- currently)
                            ((when (not (and (rational-listp literal-nodenums) ;todo: using nat-listp here didn't work
                                             (all-< literal-nodenums dag-len))))
                             (er hard? ',rewrite-subst-and-elim-with-rule-alist-name "Bad nodenum after crunching.")
                             (mv :error-in-crunching
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums))
                            ;; (- (cw "Done.)~%"))
                            )
                         (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums))))
                    ((when erp)
                     (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                 (if changep
                     ;;Something changed, so keep rewriting (what about loops?)
                     (,rewrite-subst-and-elim-with-rule-alist-name
                      literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      rule-alist rule-set-number
                      interpreted-function-alist monitored-symbols case-designator print info tries prover-depth options (+ -1 count))
                   ;;Rewriting didn't change anything.
                   ;;fixme think about when exactly to do this
                   (b* ((- (cw "(Substituting:~%"))
                        ((mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                         (substitute-vars literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth 0 nil))
                        ((when erp)
                         (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                        ((when (not literal-nodenums))
                         (cw "NOTE: No literals left after substitution!~%") ;can happen if the only lit when we subst is a (negated) var equality
                         (mv (erp-nil)
                             nil ;; did not prove
                             literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                        (- (cw "  Done substituting. ~x0 literals left.)~%" (len literal-nodenums))))
                     (if changep
                         ;;Something changed, so start over:
                         (,rewrite-subst-and-elim-with-rule-alist-name
                          literal-nodenums
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          rule-alist rule-set-number
                          interpreted-function-alist monitored-symbols case-designator print
                          info tries prover-depth options (+ -1 count))
                       (b* (((mv erp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                             ;; TODO: Consider eliminating more than one tuple here, if possible
                             (eliminate-a-tuple literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                            ((when erp) (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                         (if changep
                             ;;Something changed, so start over:
                             (,rewrite-subst-and-elim-with-rule-alist-name
                              literal-nodenums
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                              rule-alist rule-set-number
                              interpreted-function-alist monitored-symbols case-designator print
                              info tries prover-depth options (+ -1 count))
                           (prog2$
                            (and (eq :verbose print) ;; TODO: improve this printing.
                                 ;;should this be printed by the parent, after we attack the clause miter?
                                 ;;yes, probably.
                                 (prog2$ (cw "Case ~s0 didn't simplify to true.  Literal nodenums:~% ~x1~%(This case: ~x2)~%Literals:~%"
                                             case-designator
                                             literal-nodenums
                                             (expressions-for-this-case-simple literal-nodenums dag-array dag-len))
                                         (print-dag-only-supporters-lst literal-nodenums 'dag-array dag-array)))
                            (mv (erp-nil) nil literal-nodenums
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))))))))

       (defthm ,(pack$ rewrite-subst-and-elim-with-rule-alist-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,rewrite-subst-and-elim-with-rule-alist-name literal-nodenums
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                  rule-alist rule-set-number
                                                                  interpreted-function-alist monitored-symbols
                                                                  case-designator print ;move print arg?
                                                                  info tries prover-depth options count)
                    (implies (not erp)
                             (and (booleanp provedp)
                                  (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (nat-listp new-literal-nodenums)
                                  (all-< new-literal-nodenums new-dag-len)
                                  (info-worldp new-info)
                                  (triesp new-tries)
                                  (implies (< 0 prover-depth)
                                           (<= dag-len new-dag-len))))))
         :hints (("Goal" :induct t
                  :in-theory (e/d (,rewrite-subst-and-elim-with-rule-alist-name
                                   <-OF-+-OF-1-STRENGTHEN-2
                                   NATP-OF-+-OF-1
                                   rationalp-when-natp-for-axe)
                                  (natp)))))

       (defthm ,(pack$ rewrite-subst-and-elim-with-rule-alist-name '-return-type-corollary-linear)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (rule-alistp rule-alist)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,rewrite-subst-and-elim-with-rule-alist-name literal-nodenums
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                  rule-alist rule-set-number
                                                                  interpreted-function-alist monitored-symbols
                                                                  case-designator print ;move print arg?
                                                                  info tries prover-depth options count)
                    (declare (ignore provedp new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (implies (not erp)
                             (implies (< 0 prover-depth)
                                      (<= dag-len new-dag-len)))))
         :rule-classes :linear
         :hints (("Goal" :use ,(pack$ rewrite-subst-and-elim-with-rule-alist-name '-return-type)
                  :in-theory (disable ,(pack$ rewrite-subst-and-elim-with-rule-alist-name '-return-type)))))

       (defthm ,(pack$ rewrite-subst-and-elim-with-rule-alist-name '-return-type-2)
         (implies (true-listp literal-nodenums)
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,rewrite-subst-and-elim-with-rule-alist-name literal-nodenums
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                  rule-alist rule-set-number
                                                                  interpreted-function-alist monitored-symbols
                                                                  case-designator print ;move print arg?
                                                                  info tries prover-depth options count)
                    (declare (ignore erp provedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (true-listp new-literal-nodenums)))
         :hints (("Goal" :induct t
                  :in-theory (e/d (,rewrite-subst-and-elim-with-rule-alist-name
                                   <-OF-+-OF-1-STRENGTHEN-2
                                   NATP-OF-+-OF-1
                                   rationalp-when-natp-for-axe)
                                  (natp)))))

       ;; Returns (mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries).
       ;; There should be no harvestable disjuncts in the LITERAL-NODENUMS returned, assuming there we none passed in.
       (defund ,rewrite-subst-and-elim-with-rule-alists-name (literal-nodenums
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              rule-alists ;we use these one at a time
                                                              rule-set-number
                                                              interpreted-function-alist monitored-symbols case-designator print
                                                              info tries prover-depth options)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (nat-listp literal-nodenums)
                                     (all-< literal-nodenums dag-len)
                                     (all-rule-alistp rule-alists)
                                     (natp rule-set-number)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))
                         :measure (len rule-alists)))
         (if (atom rule-alists)
             ;; No error but didn't prove:
             (mv (erp-nil) nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
           (b* (((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                 (,rewrite-subst-and-elim-with-rule-alist-name literal-nodenums
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                               (first rule-alists) ;; try the first rule-alist
                                                               rule-set-number
                                                               interpreted-function-alist monitored-symbols case-designator print
                                                               info tries prover-depth options (+ -1 (expt 2 59))))
                ((when erp) (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                ((when provedp) (mv (erp-nil) t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
             ;; Continue with the rest of the rule-alists:
             (,rewrite-subst-and-elim-with-rule-alists-name literal-nodenums
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            (rest rule-alists)
                                                            (+ 1 rule-set-number)
                                                            interpreted-function-alist monitored-symbols case-designator print
                                                            info tries prover-depth options))))

       (defthm ,(pack$ rewrite-subst-and-elim-with-rule-alists-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (all-rule-alistp rule-alists)
                       (natp rule-set-number)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,rewrite-subst-and-elim-with-rule-alists-name literal-nodenums
                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                   rule-alists ;we use these one at a time
                                                                   rule-set-number
                                                                   interpreted-function-alist monitored-symbols case-designator print
                                                                   info tries prover-depth options)
                    (implies (not erp)
                             (and (booleanp provedp)
                                  (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (nat-listp new-literal-nodenums)
                                  (all-< new-literal-nodenums new-dag-len)
                                  (info-worldp new-info)
                                  (triesp new-tries)
                                  (implies (< 0 prover-depth)
                                           (<= dag-len new-dag-len))))))
         :hints (("Goal" :induct t
                  :in-theory (e/d (,rewrite-subst-and-elim-with-rule-alists-name)
                                  (natp)))))

       (defthm ,(pack$ rewrite-subst-and-elim-with-rule-alists-name '-return-type-2)
         (implies (true-listp literal-nodenums)
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,rewrite-subst-and-elim-with-rule-alists-name literal-nodenums
                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                   rule-alists ;we use these one at a time
                                                                   rule-set-number
                                                                   interpreted-function-alist monitored-symbols case-designator print
                                                                   info tries prover-depth options)
                    (declare (ignore erp provedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (true-listp new-literal-nodenums)))
         :hints (("Goal" :induct t
                  :in-theory (e/d (,rewrite-subst-and-elim-with-rule-alists-name)
                                  (natp)))))

       ;; ;fixme return info and tries?
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
       ;;               ;; (print-array2 'dag-array dag-array dag-len)
       ;;               (print-dag-only-supporters-lst literal-nodenums 'dag-array dag-array)
       ;;               (let* ( ;;fixme or we could use a worklist starting with literal-nodenums..
       ;;                      (tag-array-for-prove-clause-miter (tag-supporters-of-nodes literal-nodenums 'dag-array dag-array 'tag-array-for-prove-clause-miter
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

       ;; returns (mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
       ;; where if provedp is non-nil, then we proved the clause and the other return values are irrelevant
       ;; otherwise, this returns the simplified clause (as the list of literal nodenums and the dag-array, etc.)
       ;; old: this returns TEST-CASES because destructor elimination can change the vars and must change the test cases analogously.
;old: this may do mitering (what if there are no test cases - that could mean dont miter), but does not do splitting or call stp (should we do those things before mitering?)
       (defund ,prove-case-name (literal-nodenums
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 rule-alists
                                 interpreted-function-alist monitored-symbols
                                 case-designator print
                                 info tries prover-depth options)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (nat-listp literal-nodenums)
                                     (all-< literal-nodenums dag-len)
                                     (all-rule-alistp rule-alists)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))))
         (mv-let (erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
           (,rewrite-subst-and-elim-with-rule-alists-name literal-nodenums
                                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                          rule-alists
                                                          1 ; number the rule sets starting at 1
                                                          interpreted-function-alist monitored-symbols case-designator print
                                                          info tries prover-depth options)
           ;;combine these return cases?
           (if erp
               (mv erp nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
             (if provedp
                 (mv (erp-nil) t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
               (prog2$ nil ;(cw "We have been told not to miter.~%")
                       (mv (erp-nil) nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))))))

       (defthm ,(pack$ prove-case-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (all-rule-alistp rule-alists)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (implies (not erp)
                             (and (booleanp provedp)
                                  (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (nat-listp new-literal-nodenums)
                                  (all-< new-literal-nodenums new-dag-len)
                                  (info-worldp new-info)
                                  (triesp new-tries)
                                  (implies (< 0 prover-depth)
                                           (<= dag-len new-dag-len))))))
         :hints (("Goal" :in-theory (e/d (,prove-case-name)
                                         (natp)))))

       (defthm ,(pack$ prove-case-name '-return-type-corollary)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (all-rule-alistp rule-alists)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (declare (ignore provedp new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
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
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (declare (ignore provedp new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
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
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (declare (ignore provedp new-literal-nodenums new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
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
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (declare (ignore provedp new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (implies (not erp)
                             (implies (< 0 prover-depth)
                                      (<= dag-len new-dag-len)))))
         :rule-classes :linear
         :hints (("Goal" :use (,(pack$ prove-case-name '-return-type))
                  :in-theory (disable ,(pack$ prove-case-name '-return-type)))))

       (defthm ,(pack$ prove-case-name '-return-type-2)
         (implies (true-listp literal-nodenums)
                  (mv-let (erp provedp new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-case-name literal-nodenums
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rule-alists
                                      interpreted-function-alist monitored-symbols
                                      case-designator print
                                      info tries prover-depth options)
                    (declare (ignore erp provedp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (true-listp new-literal-nodenums)))
         :rule-classes (:rewrite :type-prescription)
         :hints (("Goal" :in-theory (e/d (,prove-case-name)
                                         (natp)))))

       (mutual-recursion

        ;; Try to prove the clause assuming NODENUM is true.
        ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries) where result is :proved, :failed, or :timed-out.
        ;; This is separate to keep the main function smaller.
        (defund ,prove-true-case-name (nodenum ;; to be assumed true
                                       literal-nodenums
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rule-alists
                                       interpreted-function-alist
                                       monitored-symbols
                                       print
                                       case-1-designator
                                       info tries
                                       prover-depth options count)
          (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (natp nodenum)
                                      (< nodenum dag-len)
                                      (nat-listp literal-nodenums)
                                      (all-< literal-nodenums dag-len)
                                      (all-rule-alistp rule-alists)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (info-worldp info)
                                      (triesp tries)
                                      (symbol-listp monitored-symbols)
                                      (stringp case-1-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :verify-guards nil ; done below
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded
                  :failed ; could instead use :timed-out here
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ( ;; Harvest disjuncts from the new literal:
                 ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (get-disjuncts nodenum
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 literal-nodenums ; will be extended
                                 t ;negated-flag=t, since nodenum is the negation of the new literal.
                                 ))
                 ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                 ((when provedp) (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
              ;; Attempt to prove case #1:
              (,prove-or-split-case-name literal-nodenums
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rule-alists interpreted-function-alist monitored-symbols
                                         print case-1-designator
                                         info tries
                                         (+ 1 prover-depth) ;to indicate that nodes should not be changed
                                         options (+ -1 count)))))

        ;; Try to prove the clause assuming NODENUM is false.
        ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries) where result is :proved, :failed, or :timed-out.
        ;; This is separate to keep the main function smaller.
        (defund ,prove-false-case-name (nodenum ;; to be assumed false
                                        literal-nodenums
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alists
                                        interpreted-function-alist
                                        monitored-symbols
                                        print
                                        case-2-designator
                                        info tries
                                        prover-depth options count)
          (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (natp nodenum)
                                      (< nodenum dag-len)
                                      (nat-listp literal-nodenums)
                                      (all-< literal-nodenums dag-len)
                                      (all-rule-alistp rule-alists)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (info-worldp info)
                                      (triesp tries)
                                      (symbol-listp monitored-symbols)
                                      (stringp case-2-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded
                  :failed ; could instead use :timed-out here
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ( ;; Harvest disjuncts from the new literal:
                 ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (get-disjuncts nodenum ;the new literal
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 literal-nodenums ; will be extended
                                 nil ;negated-flag=nil, since nodenum itself is the new literal.
                                 ))
                 ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                 ((when provedp) (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
              ;; Attempt to prove case #2:
              (,prove-or-split-case-name literal-nodenums
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rule-alists interpreted-function-alist monitored-symbols
                                         print case-2-designator
                                         info tries
                                         (+ 1 prover-depth) ;to match what we do in the other case above
                                         options (+ -1 count)))))

        ;; Tries to prove the disjunction of LITERAL-NODENUMS.
        ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries) where result is :proved, :failed, or :timed-out
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
                                           rule-alists
                                           interpreted-function-alist
                                           monitored-symbols
                                           print
                                           case-designator ;the name of this case (a string?)
                                           info tries
                                           prover-depth options count)
          (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                      (nat-listp literal-nodenums)
                                      (all-< literal-nodenums dag-len)
                                      (all-rule-alistp rule-alists)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (info-worldp info)
                                      (triesp tries)
                                      (symbol-listp monitored-symbols)
                                      (stringp case-designator)
                                      (natp prover-depth)
                                      (axe-prover-optionsp options))
                          :measure (+ 1 (nfix count)))
                   (type (unsigned-byte 59) count))
          (if (zp-fast count)
              (mv :count-exceeded
                  :failed ; could instead use :timed-out here
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
            (b* ( ;; First try to prove the clause as a single case.  This may do some work even if it doesn't prove the clause.
                 ;; Tuple elim (and substitution) may change the set of variables.
                 ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                  (,prove-case-name literal-nodenums
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    rule-alists interpreted-function-alist monitored-symbols
                                    case-designator print info tries prover-depth options))
                 ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                 ((when provedp)
                  (cw "Proved case ~s0 by rewriting, etc.~%" case-designator)
                  (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                 ((when (not literal-nodenums)) ;can this happen? i think so, e.g., by substitition
                  (cw "No literals left!~%")
                  (mv (erp-nil) :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                 ;; Proving it as a single case didn't finish the job (but may have done some work).
                 ;; Now try to split on an if-then-else test (or an argument to a bool op).
                 (nodenum (find-node-to-split-for-prover 'dag-array dag-array dag-len literal-nodenums)))
              (if (not nodenum)
                  (progn$ (cw "(Couldn't find a node to split on.  Failed to prove case ~s0~%" case-designator)
                          (and print
                               (or (eq t print) (eq :verbose print) (eq :verbose2 print)) ;drop?
                               (or (< dag-len 1000) ;fixme not the appropriate test
                                   (eq t print)     ;new
                                   (eq :verbose print)  ;new
                                   (eq :verbose2 print) ;new
                                   )
                               (progn$
                                (cw "(This case (~x0 literals):~%" (len literal-nodenums))
                                (print-axe-prover-case literal-nodenums 'dag-array dag-array dag-len)
                                (cw ")~%")))
                          (cw ")~%")
                          (mv (erp-nil) :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                ;;splitting on nodenum (which is not a call of NOT):
                ;;instead of proving the clause C, we will prove both (or (not nodenum) C) and (or nodenum C)
                (b* ((- (cw "Splitting on node ~x0:~%" nodenum))
                     ;;todo: elide this if too big:
                     (- (print-dag-only-supporters 'dag-array dag-array nodenum))
                     (- (and (or (eq t print) (eq :verbose print) (eq :verbose2 print))
                             (progn$ (cw "Literals:~%")
                                     (print-dag-only-supporters-lst literal-nodenums 'dag-array dag-array)
                                     ;;(cw "parent array:~%")
                                     ;;(print-array2 'dag-parent-array dag-parent-array dag-len)
                                     )))
                     ;;can we somehow avoid this saving? copy to a new array? ;change ,rewrite-literals-name to not destroy existing nodes?!
                     ;;(saved-dag-array dag-array) ;(saved-dag-alist (array-to-alist dag-len 'dag-array dag-array)) ;don't convert to an alist?  just restore later by making the old value of dag-array the new  under-the-hood value?  same for parents array?
                     ;;(saved-dag-len dag-len)
                     ;;(saved-dag-parent-array dag-parent-array) ;(saved-dag-parent-alist (array-to-alist dag-len 'dag-parent-array dag-parent-array))
                     ;;(saved-dag-constant-alist dag-constant-alist)
                     ;;(saved-dag-variable-alist dag-variable-alist)
                     (case-1-designator (concatenate 'string case-designator "1"))
                     ;; In Case 1 we assume nodenum is non-nil (i.e., true).  Thus, we add a new literal (not nodenum) and try to prove (or (not nodenum) C):
                     ;; (mv-let ;Use the split fact:
                     ;;  (dag-array dag-parent-array)
                     ;;  ;fixme consider making this not destructive:
                     ;;  (replace-nodenum-with-t-in-boolean-contexts nodenum dag-array dag-parent-array) ;this leaves the subtree at nodenum itself unchanged
                     (- (cw "(True Case: ~s0~%" case-1-designator))
                     (- (and (or (eq t print) (eq :verbose print) (eq :verbose2 print))
                             (prog2$ (cw "Literals:~%")
                                     (print-dag-only-supporters-lst literal-nodenums 'dag-array dag-array))))
                     ((mv erp case-1-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                      (,prove-true-case-name nodenum ;; to be assumed true
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             info tries
                                             prover-depth options (+ -1 count)))
                     ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
                  ;;fixme we could make an option to continue if case 1 fails, so that all the failed subgoals are printed
                  (if (not (eq :proved case-1-result))
                      (prog2$ (cw "Failed on ~s0.)~%" case-1-designator)
                              (mv (erp-nil)
                                  case-1-result ; will be :failed or :timed-out
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                  info tries))
                    (b* ((- (cw "Proved ~s0)~%" case-1-designator)) ;end of case1
                         ;;restore the dag:
                         ;; (dag-array (compress1 'dag-array saved-dag-array)) ;(dag-array (make-into-array-with-len 'dag-array saved-dag-alist saved-dag-len)) ;leave some slack space?
                         ;; (dag-parent-array (compress1 'dag-parent-array saved-dag-parent-array)) ;(dag-parent-array (make-into-array-with-len 'dag-parent-array saved-dag-parent-alist saved-dag-len)) ;leave some slack space?
                         ;; (dag-constant-alist saved-dag-constant-alist)
                         ;; (dag-variable-alist saved-dag-variable-alist)
                         ;;(dag-len saved-dag-len)
                         (case-2-designator (concatenate 'string case-designator "2"))
                         ;;In case 2 we assume nodenum is nil (false), i.e., we add a new literal NODENUM and try to prove (or nodenum C):
                         (- (cw "(False case: ~s0~%" case-2-designator))
                         ;;                                       (mv-let ;Use the split fact:
                         ;;                                        (dag-array dag-parent-array)
                         ;; ;fixme consider making this not destructive:
                         ;;                                        (replace-nodenum-with-nil nodenum dag-array dag-parent-array) ;this leaves the subtree at nodenum itself unchanged
                         ((mv erp case-2-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)
                          (,prove-false-case-name nodenum ;; to be assumed true
                                                  literal-nodenums
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  rule-alists
                                                  interpreted-function-alist
                                                  monitored-symbols
                                                  print
                                                  case-2-designator
                                                  info tries
                                                  prover-depth options (+ -1 count)))
                         ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
                         (- (if (not (eq :proved case-2-result))
                                (cw "Failed on ~s0.)~%" case-2-designator)
                              (cw "Proved ~s0)~%" case-2-designator)))
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
                          info tries)))))))))

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
                         (info-worldp info)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-1-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                      (,prove-true-case-name nodenum
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             info tries
                                             prover-depth options count)
                      (implies (not erp)
                               (and (prover-resultp result)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (info-worldp new-info)
                                    (triesp new-tries)
                                    (<= dag-len new-dag-len)))))
           :flag ,(pack$ 'prove-true-case-with- suffix '-prover))
         (defthm ,(pack$ 'prove-false-case-with- suffix '-prover-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (natp nodenum)
                         (< nodenum dag-len)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (info-worldp info)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-2-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                      (,prove-false-case-name nodenum
                                              literal-nodenums
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              rule-alists
                                              interpreted-function-alist
                                              monitored-symbols
                                              print
                                              case-2-designator
                                              info tries
                                              prover-depth options count)
                      (implies (not erp)
                               (and (prover-resultp result)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (info-worldp new-info)
                                    (triesp new-tries)
                                    (<= dag-len new-dag-len)))))
           :flag ,(pack$ 'prove-false-case-with- suffix '-prover))
         (defthm ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)
           (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                         (nat-listp literal-nodenums)
                         (all-< literal-nodenums dag-len)
                         (all-rule-alistp rule-alists)
                         (interpreted-function-alistp interpreted-function-alist)
                         (info-worldp info)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                      (,prove-or-split-case-name literal-nodenums
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 rule-alists
                                                 interpreted-function-alist
                                                 monitored-symbols
                                                 print
                                                 case-designator
                                                 info tries
                                                 prover-depth options count)
                      (implies (not erp)
                               (and (prover-resultp result)
                                    (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                    (info-worldp new-info)
                                    (triesp new-tries)
                                    (implies (< 0 prover-depth)
                                             (<= dag-len new-dag-len))))))
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
                         (info-worldp info)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-1-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                      (,prove-true-case-name nodenum
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             info tries
                                             prover-depth options count)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
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
                         (info-worldp info)
                         (triesp tries)
                         (symbol-listp monitored-symbols)
                         (stringp case-1-designator)
                         (natp prover-depth)
                         (axe-prover-optionsp options))
                    (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                      (,prove-true-case-name nodenum
                                             literal-nodenums
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-1-designator
                                             info tries
                                             prover-depth options count)
                      (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                      (implies (not erp)
                               (natp new-dag-len))))
           :hints (("Goal" :use (:instance ,(pack$ 'prove-true-case-with- suffix '-prover-return-type))
                    :in-theory (disable ,(pack$ 'prove-true-case-with- suffix '-prover-return-type)))))

       (verify-guards ,prove-true-case-name :otf-flg t
         :hints (("Goal" :in-theory (e/d (rationalp-when-natp-for-axe
                                          <-of-+-of-1-strengthen-2
                                          integerp-when-natp-for-axe)
                                         (natp)))))

       (defthm ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type-corollary-linear)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (nat-listp literal-nodenums)
                       (all-< literal-nodenums dag-len)
                       (all-rule-alistp rule-alists)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-or-split-case-name literal-nodenums
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rule-alists
                                               interpreted-function-alist
                                               monitored-symbols
                                               print
                                               case-designator
                                               info tries
                                               prover-depth options count)
                    (declare (ignore result new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries))
                    (implies (not erp)
                             (implies (< 0 prover-depth)
                                      (<= dag-len new-dag-len)))))
         :rule-classes :linear
         :hints (("Goal" :use ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type)
                  :in-theory (disable ,(pack$ 'prove-or-split-case-with- suffix '-prover-return-type))))
         )

       ;; The main entry point of the Axe Prover.
       ;; Tries to prove the disjunction of LITERAL-NODENUMS-OR-QUOTEPS.
       ;; Returns (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries) where result is :proved, :failed, or :timed-out
       ;; Does not change any existing DAG nodes if prover-depth > 0 (TODO check that).
       (defund ,prove-disjunction-name (literal-nodenums-or-quoteps
                                        dag-array ;must be named 'dag-array
                                        dag-len
                                        dag-parent-array ;must be named 'dag-parent-array
                                        dag-constant-alist dag-variable-alist
                                        rule-alists
                                        interpreted-function-alist
                                        monitored-symbols
                                        print
                                        case-designator ;the name of this case
                                        info tries
                                        prover-depth options)
         (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                                     (true-listp literal-nodenums-or-quoteps)
                                     (all-dargp-less-than literal-nodenums-or-quoteps dag-len)
                                     (all-rule-alistp rule-alists)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     (info-worldp info)
                                     (triesp tries)
                                     (symbol-listp monitored-symbols)
                                     (stringp case-designator)
                                     (natp prover-depth)
                                     (axe-prover-optionsp options))))
         (b* ( ;; Handle any constant disjuncts
              ((mv provedp literal-nodenums)
               (handle-constant-disjuncts literal-nodenums-or-quoteps nil))
              ((when provedp)
               (cw "! Proved case ~s0 (one literal was a non-nil constant!)~%" case-designator)
               (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
              ;; Now extract any additional disjuncts from the literals:
              ((mv erp provedp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (get-disjuncts-from-nodes literal-nodenums
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         nil))
              ((when erp) (mv erp :failed dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries))
              ((when provedp)
               (cw "! Proved case ~s0 (one literal had a non-nil constant disjunct!)~%" case-designator)
               (mv (erp-nil) :proved dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries)))
           (,prove-or-split-case-name literal-nodenums
                                        dag-array
                                        dag-len
                                        dag-parent-array
                                        dag-constant-alist dag-variable-alist
                                        rule-alists
                                        interpreted-function-alist
                                        monitored-symbols
                                        print
                                        case-designator
                                        info tries
                                        prover-depth options
                                        (+ -1 (expt 2 59)) ;max fixnum?
                                        )))

       (defthm ,(pack$ prove-disjunction-name '-return-type)
         (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                       (true-listp literal-nodenums-or-quoteps)
                       (all-dargp-less-than literal-nodenums-or-quoteps dag-len)
                       (all-rule-alistp rule-alists)
                       (interpreted-function-alistp interpreted-function-alist)
                       (info-worldp info)
                       (triesp tries)
                       (symbol-listp monitored-symbols)
                       (stringp case-designator)
                       (natp prover-depth)
                       (axe-prover-optionsp options))
                  (mv-let (erp result new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-info new-tries)
                    (,prove-disjunction-name literal-nodenums-or-quoteps
                                             dag-array
                                             dag-len
                                             dag-parent-array
                                             dag-constant-alist dag-variable-alist
                                             rule-alists
                                             interpreted-function-alist
                                             monitored-symbols
                                             print
                                             case-designator
                                             info tries
                                             prover-depth options)
                    (implies (not erp)
                             (and (prover-resultp result)
                                  (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                                  (info-worldp new-info)
                                  (triesp new-tries)
                                  (implies (< 0 prover-depth)
                                           (<= dag-len new-dag-len))))))
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
;;                                               (< (len dag) 2147483647)))
;;                                      (pseudo-term-listp assumptions)
;;                                      (pseudo-dag-arrayp context-array-name context-array context-array-len)
;;                                      (contextp-with-bound context context-array-len)
;;                                      ;;todo: add more
;;                                      (all-rule-alistp rule-alists)
;;                                      (true-listp rule-alists)
;;                                      (symbol-listp monitored-symbols)
;;                                      (interpreted-function-alistp interpreted-function-alist)
;;                                      (axe-prover-optionsp options)
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
;; ;          (dummy (cw "print-timeout-goalp:  ~x0" print-timeout-goalp))
;;                 (dag-array (make-into-array 'dag-array dag))
;;                 (top-nodenum (top-nodenum dag))
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
;;                (b* ((context-nodenums-to-assume (keep-atoms context)) ;fixme turn keep-atoms and keep-non-atoms into special functions for contexts?
;;                     (context-negations-to-assume (keep-non-atoms context)) ;the ones surrounded by not
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
;;                          info tries)
;;                      (,prove-disjunction-name (cons top-nodenum negated-assumption-literal-nodenums-or-quoteps) ;we prove that either the top node of the dag is true or some assumption is false
;;                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                               rule-alists
;;                                               interpreted-function-alist monitored-symbols
;;                                               print
;;                                               case-name
;;                                               (and print (empty-info-world))
;;                                               (and print (zero-tries))
;;                                               0 ;prover-depth
;;                                               options))
;;                     ((when erp) (mv erp :failed))
;;                     ;;just print the message in the subroutine and don't case split here?
;;                     (- (and print (cw "(~x0 tries.)~%" tries)))
;;                     (- (and print (print-hit-counts print info (rules-from-rule-alists rule-alists)))))
;;                  (if (eq :proved result)
;;                      (prog2$ (cw "proved ~s0 with dag prover~%" case-name)
;;                              (mv (erp-nil) :proved))
;;                    (prog2$ (cw "failed to prove ~s0 with dag prover~%" case-name)
;;                            (mv (erp-nil) result))))))))

       ;; Try to prove that DAG1 implies DAG2, for all values of the variables.
       ;; TODO: Warning if no variable overlap?
       ;; Returns (mv erp event state) where a failure to prove causes erp to be non-nil.
       ;; TODO: Check all inputs, including arities.
       (defund ,prove-implication-fn-helper-name (dag1
                                                  dag2
                                                  rule-lists
                                                  interpreted-function-alist
                                                  monitor
                                                  state)
         (declare (xargs :guard (and (or (myquotep dag1)
                                         (and (pseudo-dagp dag1)
                                              (<= (len dag1) 2147483646)))
                                     (or (myquotep dag2)
                                         (and (pseudo-dagp dag2)
                                              (<= (len dag2) 2147483646)))
                                     (rule-item-list-listp rule-lists)
                                     (symbol-listp monitor)
                                     (ilks-plist-worldp (w state)))
                         :guard-hints (("Goal" :use (:instance make-implication-dag-return-type)
                                        :in-theory (e/d (array-len-with-slack top-nodenum-of-dag-when-pseudo-dagp wf-dagp)
                                                        (symbol-listp top-nodenum myquotep get-global w quotep make-implication-dag-return-type))))
                         :stobjs state))
         (b* (((when (not (interpreted-function-alistp interpreted-function-alist)))
               (er hard? ',prove-implication-fn-name "Ill-formed interpreted-function-alist: ~x0" interpreted-function-alist)
               (mv :bad-input nil state))
              ;; Form the implication to prove:
              ((mv erp implication-dag-or-quotep) (make-implication-dag dag1 dag2)) ; todo: we will end up having to extract disjuncts from this implication
              ((when erp) (mv erp nil state))
              ;; Handle the case of a constant DAG to prove (rare):
              ((when (quotep implication-dag-or-quotep))
               (if (unquote implication-dag-or-quotep)
                   (prog2$ (cw "NOTE: Proved the DAG because it is a constant.")
                           (mv (erp-nil) '(value-triple :ok) state))
                 (prog2$ (cw "NOTE: Failed because the DAG is the constant nil.")
                         (mv :failed nil state))))
              (top-nodenum (top-nodenum-of-dag implication-dag-or-quotep))
              (dag-len (+ 1 top-nodenum))
              ((when (>= dag-len 2147483647))
               (prog2$ (cw "ERROR: DAG too big.")
                       (mv :failed nil state)))
              (slack-amount 0) ;todo: increase slack amount to dag-len?
              ((mv erp dag-array) (make-dag-into-array2 'dag-array implication-dag-or-quotep slack-amount))
              ((when erp) (mv erp nil state))
              ;; make auxiliary dag data structures:
              ((mv dag-parent-array dag-constant-alist dag-variable-alist)
               (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
              (rule-lists (elaborate-rule-item-lists rule-lists state))
              ((mv erp rule-alists) (make-rule-alists rule-lists (w state)))
              ((when erp) (mv erp nil state))
              ((mv erp result & & & & & ; dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   & &                  ;info tries ;todo: use these
                   )
               (,prove-disjunction-name (list top-nodenum) ;; just one disjunct
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alists
                                        interpreted-function-alist
                                        monitor
                                        t ;print
                                        "MAIN_CASE" ;;case-designator ;the name of this case (a string?)
                                        (empty-info-world) ;(and print (empty-info-world))
                                        (zero-tries)  ;(and print (zero-tries))
                                        0             ;prover-depth
                                        nil           ;options
                                        ))
              ((when erp) (mv erp nil state)))
           (if (eq result :proved)
               (prog2$ (cw "Proved.~%")
                       (mv (erp-nil) '(value-triple :ok) state))
             (mv :failed-to-prove nil state))))

       ;; Try to prove that DAG1 implies DAG2, for all values of the variables.
       ;; Returns (mv erp event state) where a failure to prove causes erp to be non-nil.
       (defund ,prove-implication-fn-name (dag-or-term1 ; not yet translated
                                           dag-or-term2 ; not yet translated
                                           rule-lists
                                           interpreted-function-alist
                                           monitor
                                           state)
         (declare (xargs :guard (and (rule-item-list-listp rule-lists)
                                     ;; (interpreted-function-alistp interpreted-function-alist)
                                     (symbol-listp monitor)
                                     (ilks-plist-worldp (w state)))
                         :stobjs state
                         :mode :program ;because this translates its args if they are terms
                         ))
         (b* (((mv erp dag1) (dag-or-term-to-dag-basic dag-or-term1 (w state)))
              ((when erp) (mv erp nil state))
              ((mv erp dag2) (dag-or-term-to-dag-basic dag-or-term2 (w state)))
              ((when erp) (mv erp nil state)))
           ;; This helper function is in :logic mode and is guard-verified:
           (,prove-implication-fn-helper-name dag1
                                              dag2
                                              rule-lists
                                              interpreted-function-alist
                                              monitor
                                              state)))

       ;; Returns (mv erp event state) where a failure to prove causes erp to be non-nil.
       (defmacro ,prove-implication-name (dag-or-term1
                                          dag-or-term2
                                          &key
                                          (rule-lists 'nil) ;todo: improve by building some in and allowing :extra-rules and :remove-rules?
                                          (interpreted-function-alist 'nil)
                                          (monitor 'nil))
         ;; all args get evaluated:
         (list 'make-event
               (list ',prove-implication-fn-name
                     dag-or-term1
                     dag-or-term2
                     rule-lists
                     interpreted-function-alist
                     monitor
                     'state)))

       ;; ;; Returns (mv erp provedp)
       ;; (defund ,prove-implication-name (conc ;a term
       ;;                                              hyps ;list of terms
       ;;                                              name rule-alists monitored-symbols interpreted-function-alist print options)
       ;;   (declare (xargs :guard (and (pseudo-termp conc)
       ;;                               (pseudo-term-listp hyps)
       ;;                               (symbolp name)
       ;;                               (all-rule-alistp rule-alists)
       ;;                               (symbol-listp monitored-symbols)
       ;;                               (interpreted-function-alistp interpreted-function-alist)
       ;;                               ;;... todo add more
       ;;                               (axe-prover-optionsp options))
       ;;                   :verify-guards nil ;todo
       ;;                   ))
       ;;   (b* ((- (cw "(Proving theorem with Axe prover:~%"))
       ;;        (literal-terms (cons conc (negate-terms hyps)))
       ;;        ((mv erp literal-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
       ;;         (make-terms-into-dag-array-basic literal-terms 'dag-array 'dag-parent-array interpreted-function-alist))
       ;;        ((when erp) (mv erp nil))
       ;;        ;;fixme name clashes..
       ;;        ((mv erp result & & & & & info tries)
       ;;         (,prove-disjunction-name literal-nodenums-or-quoteps ;; fixme think about the options used here!
       ;;                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
       ;;                                              rule-alists ;;(make-rule-alist-simple rule-alist t (table-alist 'axe-rule-priorities-table (w state)))
       ;;                                              nil ;interpreted-function-alist
       ;;                                              monitored-symbols
       ;;                                              t           ;print
       ;;                                              (symbol-name name) ;;case-designator
       ;;                                              (and print (empty-info-world))
       ;;                                              (and print (zero-tries))
       ;;                                              0 ;prover-depth
       ;;                                              options
       ;;
       ;;                                             ))
       ;;        ((when erp) (mv erp nil))
       ;;        (- (and print (print-hit-counts print info (rules-from-rule-alists rule-alists))))
       ;;        (- (and print (cw "Total tries: ~x0.~%" tries))))
       ;;     (if (eq :proved result)
       ;;         (prog2$ (cw "Proved the theorem.)~%")
       ;;                 (mv (erp-nil) t))
       ;;       (prog2$ (cw "Failed to prove the theorem.)~%")
       ;;               (mv (erp-nil) nil)))))

       ;; ;; Returns (mv erp provedp state) where if provedp is non-nil, defthm has been proved in state
       ;; ;pass in rule-classes?
       ;; ;the caller should check that defthm-name is not already defined
       ;; (defund prove-theorem-with-basic-prover (conc ;a term
       ;;                                          hyps ;list of terms
       ;;                                          defthm-name rule-alists monitored-symbols interpreted-function-alist print options state)
       ;;   (declare (xargs :mode :program ;because this calls submit-events
       ;;                   :guard (and (pseudo-termp conc)
       ;;                               (pseudo-term-listp hyps)
       ;;                               (symbolp defthm-name)
       ;;                               (all-rule-alistp rule-alists)
       ;;                               (symbol-listp monitored-symbols)
       ;;                               (interpreted-function-alistp interpreted-function-alist)
       ;;                               ;;... todo add more
       ;;                               (axe-prover-optionsp options)
       ;;                               )
       ;;                   :stobjs state))
       ;;   (mv-let (erp provedp)
       ;;     (,prove-implication-name conc hyps defthm-name rule-alists monitored-symbols interpreted-function-alist print options)
       ;;     (if erp
       ;;         (mv erp nil state)
       ;;       (if provedp
       ;;           (b* ((- (cw "(Making the theorem ~x0.~%" defthm-name))
       ;;                (state (submit-events
       ;;                        ;;where should this go?  should we use a clause processor?
       ;;                        ;;ffixme perhaps miter-and-merge should submit the defthm??
       ;;                        ;;skip-proofs here are bad?
       ;;                        `((skip-proofs (defthm ,defthm-name
       ;;                                         (implies (and ,@hyps)
       ;;                                                  ,conc)
       ;;                                         :rule-classes nil)))
       ;;                        state))
       ;;                (- (cw "Done making the theorem ~x0.)~%" defthm-name)))
       ;;             (mv (erp-nil) t state))
       ;;         (mv (erp-nil) nil state)))))

       ;; ;this one throws an error if it fails
       ;; ;; Returns state
       ;; ;the caller should check that defthm-name is not already defined
       ;; ;; TODO: Support taking an IMPLIES and extracting from it the CONC and HYPS
       ;; ;; TODO: Make a macro wrapper
       ;; ;; TODO: Allow giving an untranslated term
       ;; (defund prove-theorem-with-basic-prover2 (conc     ;a term
       ;;                                           hyps     ;list of terms
       ;;                                           defthm-name ;TODO: Should this come first?
       ;;                                           rule-alists monitored-symbols interpreted-function-alist print options state)
       ;;   (declare (xargs :mode :program
       ;;                   :stobjs state
       ;;                   :guard (and (pseudo-termp conc)
       ;;                               (pseudo-term-listp hyps)
       ;;                               (symbolp defthm-name)
       ;;                               (all-rule-alistp rule-alists)
       ;;                               (symbol-listp monitored-symbols)
       ;;                               (interpreted-function-alistp interpreted-function-alist)
       ;;                               ;;... todo add more
       ;;                               (axe-prover-optionsp options)
       ;;                               )))
       ;;   (mv-let (erp provedp state)
       ;;     (prove-theorem-with-basic-prover conc hyps defthm-name rule-alists monitored-symbols interpreted-function-alist print options state)
       ;;     (if erp
       ;;         (prog2$ (hard-error 'prove-theorem-with-basic-prover2 "Failed to prove ~s0.~%" (acons #\0 defthm-name nil))
       ;;                 state)
       ;;       (if provedp
       ;;           state
       ;;         (prog2$ (hard-error 'prove-theorem-with-basic-prover2 "Failed to prove ~s0.~%" (acons #\0 defthm-name nil))
       ;;                 state)))))

       ;; Returns (mv erp provedp).  Attempts to prove the clause (a disjunction
       ;; of terms) with the Axe Prover.
       (defund ,prove-clause-name (clause name rule-alists monitored-symbols interpreted-function-alist print options)
         (declare (xargs :guard (and (pseudo-term-listp clause)
                                     (symbolp name)
                                     (all-rule-alistp rule-alists)
                                     (true-listp rule-alists)
                                     (symbol-listp monitored-symbols)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     ;;... todo add more
                                     (axe-prover-optionsp options)
                                     )))
         (b* ((- (cw "(Proving clause with Axe prover:~%"))
              ((mv erp literal-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (make-terms-into-dag-array-basic clause 'dag-array 'dag-parent-array interpreted-function-alist))
              ((when erp) (mv erp nil))
              ;;fixme name clashes..
              ((mv erp result & & & & & info tries)
               (,prove-disjunction-name literal-nodenums-or-quoteps ;; fixme think about the options used here!
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        rule-alists ;;(make-rule-alist-simple rule-alist t (table-alist 'axe-rule-priorities-table (w state)))
                                        interpreted-function-alist
                                        monitored-symbols
                                        t                              ;print
                                        (symbol-name name) ;;case-designator
                                        (and print (empty-info-world))
                                        (and print (zero-tries))
                                        0 ;prover-depth
                                        options))
              ((when erp) (mv erp nil))
              (- (and print (print-hit-counts print info (rules-from-rule-alists rule-alists))))
              (- (and print (cw "Total tries: ~x0.~%" tries))))
           (if (eq :proved result)
               (prog2$ (cw "Proved the theorem.)~%")
                       (mv (erp-nil) t))
             (prog2$ (cw "Failed to prove the theorem.)~%")
                     (mv (erp-nil) nil)))))

       ;; Attempt to prove CLAUSE using the Axe Prover.  Returns (mv erp clauses
       ;;) where CLAUSES is nil if the Axe Prover proved the goal and otherwise
       ;; is a singleton set containing the original clause (indicating that no change
       ;; was made).  TODO: Allow it to change the clause but not prove it entirely?
       (defund ,clause-processor-name (clause hint state)
         (declare (xargs :stobjs state
                         :guard (and (pseudo-term-listp clause)
                                     (alistp hint)
                                     ;todo: make these into checks with nice error messages:
                                     (true-listp (lookup-equal :rule-lists hint))
                                     (symbol-listp (lookup-equal :monitor hint))
                                     (ilks-plist-worldp (w state)))))
         (b* ((must-prove (lookup-eq :must-prove hint))
              ;; Handle the :rules input:
              (rules (lookup-eq :rules hint))
              ((when (not (symbol-listp rules)))
               (er hard? ',clause-processor-name "Bad :rules argument: ~x0." rules)
               (mv (erp-t) (list clause)))
              ;; Handle the :rule-lists input:
              (rule-lists (lookup-eq :rule-lists hint))
              ((when (not (symbol-list-listp rule-lists)))
               (er hard? ',clause-processor-name "Bad :rule-lists argument: ~x0." rule-lists)
               (mv (erp-t) (list clause)))

              ((when (and rules rule-lists))
               (er hard? ',clause-processor-name "Both :rules and :rule-lists given.") ;todo: perhaps allow (combine them?)
               (mv (erp-t) (list clause)))
              (rule-lists (if rules
                              (list rules)
                            rule-lists))
              (monitored-symbols (lookup-eq :monitor hint))
              (print (lookup-eq :print hint))
              ((mv erp rule-alists) (make-rule-alists rule-lists (w state)))
              ((when erp) (mv erp (list clause)))
              ((mv erp provedp)
               (,prove-clause-name clause
                                   ',(pack$ suffix '-prover-clause-proc)
                                   rule-alists
                                   monitored-symbols
                                   nil ;interpreted-function-alist ;todo?
                                   print
                                   nil ;; options
                                   ))
              ((when erp) (mv erp (list clause))) ; error (and no change to clause set)
              )
           (if provedp
               (mv (erp-nil) nil) ;return the empty set of clauses
             ;; invalid or counterexample or timedout:
             (if must-prove
                 (prog2$ (er hard? ',clause-processor-name "Failed to prove but :must-prove was given.")
                         (mv (erp-t) (list clause)))
               ;; no change to clause set
               (mv (erp-nil) (list clause))))))

       ;; See also the define-trusted-clause-processor in prover2.lisp.
       (define-trusted-clause-processor
         ,clause-processor-name
         nil ;supporters ; todo: Think about this (I don't understand what :doc define-trusted-clause-processor says about "supporters")
         :ttag ,clause-processor-name)

       ;; Returns a defthm event.
       (defun ,defthm-with-clause-processor-fn-name (name term rules rule-lists remove-rules rule-classes print state)
         (declare (xargs :guard (and (symbolp name)
                                     ;; term need not be a pseudo-term
                                     (rule-item-listp rules)
                                     (rule-item-list-listp rule-lists)
                                     (symbol-listp remove-rules) ;allow rule-items?
                                     ;; todo: rule-classes
                                     ;; print
                                     )
                         :stobjs state))
         (b* (((when (and rules rule-lists))
               (er hard? ',defthm-with-clause-processor-fn-name "Both :rules and :rule-lists were given for ~x0." name))
              (rule-lists (if rules
                              (list (elaborate-rule-items rules nil state))
                            (elaborate-rule-item-lists rule-lists state)))
              (rule-lists (remove-from-all rule-lists remove-rules)))
           `(defthm ,name
              ,term
              :hints (("Goal" :clause-processor (,',clause-processor-name clause
                                                                        '((:must-prove . t)
                                                                          (:rule-lists . ,rule-lists)
                                                                          (:print . ,print))
                                                                        state)))
              ,@(if (eq :auto rule-classes)
                    nil
                  `(:rule-classes ,rule-classes)))))

       ;; Submit a defthm that uses the clause-processor:
       (defmacro ,defthm-with-clause-processor-name (name
                                                     term
                                                     &key
                                                     (rules 'nil)
                                                     (rule-lists 'nil)
                                                     (remove-rules 'nil)
                                                     (rule-classes ':auto)
                                                     (print 'nil))
         (if (and (consp term)
                  (eq :eval (car term)))
             ;; Evaluate TERM:
             `(make-event (,',defthm-with-clause-processor-fn-name ',name ,(cadr term) ',rules ',rule-lists ',remove-rules ',rule-classes ',print state))
           ;; Don't evaluate TERM:
           `(make-event (,',defthm-with-clause-processor-fn-name ',name ',term ',rules ',rule-lists ',remove-rules ',rule-classes ',print state))))

       )))

(defmacro make-prover-simple (suffix
                                apply-axe-evaluator-to-quoted-args-name
                                eval-axe-syntaxp-expr-name
                                eval-axe-bind-free-function-application-name)
  (make-prover-simple-fn suffix
                           apply-axe-evaluator-to-quoted-args-name
                           eval-axe-syntaxp-expr-name
                           eval-axe-bind-free-function-application-name))
