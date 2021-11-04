; The Axe Rewriter (somewhat old)
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

;; NOTE: Instead of this rewriter, consider using rewriter-basic or
;; rewriter-jvm or another custom rewriter if possible.  Unlike this one, they
;; do not depend on any skip-proofs.

;; NOTE: This currentlty depends on the JVM model, for the axe-syntaxp and
;; axe-bind-free functions.

(include-book "rewriter-common")
(include-book "refined-assumption-alists")
(include-book "equality-assumption-alists")
(include-book "dag-array-builders3")
(include-book "node-replacement-alist")
(include-book "node-replacement-alist-for-context")
(include-book "instantiate-hyp")
(include-book "prover")
(include-book "dag-to-term")
(include-book "simplify-xors")
(include-book "rule-limits")
(include-book "tagged-rule-sets")
(include-book "dag-array-printing2")
(include-book "rule-lists") ;todo: just for lookup-rules (can we do without that? - try to avoid using make-var-lookup-terms -- instead require the nested DAG alist to have a certain form and just do the lookup).
(include-book "kestrel/utilities/defconst-computed" :dir :system) ;not strictly needed
(include-book "jvm/axe-syntaxp-evaluator-jvm") ; JVM-specific
(include-book "jvm/axe-bind-free-evaluator-jvm") ; JVM-specific

;; Axe contains a sophisticated rewriter capable of efficiently transforming
;; large terms by repeatedly applying local ``rewrite rules.''  The rewrite
;; rules used are equivalence-preserving.  That is, they allow a term to be
;; replaced only by another term which always returns the same value.  Because
;; Axe terms are side-effect-free, rewriting can be performed without changing
;; the meaning of any over-arching term.

;; A major goal of rewriting is to simplify the terms involved. Simplification
;; is almost always desirable; it helps keep terms small and is sufficient to
;; completely prove some claims (because they simplify down to ``true'').  A
;; related goal is to normalize terms.  Normalization is the process of
;; transforming syntactically different but semantically equivalent terms so
;; that they have the same syntactic representation (and so are clearly equal
;; by inspection).  Efficient rewriting schemes may not exist to completely
;; normalize the terms with which Axe deals.  Nevertheless, normalization works
;; fairly well in practice, using the techniques and the rewrite rules
;; described here.

;; Rewriting can also be used to simply change the form of terms, for example,
;; to bit-blast them (to split multi-bit operations into single-bit
;; operations), or to eliminate certain operators (such as the
;; \texttt{leftrotate} operator, which cannot always be directly translated
;; into the language of STP).  Finally, rewriting can be used to strengthen a
;; set of known facts, using information provided by some new fact.

;; The Axe Rewriter is similar to the rewriter of the ACL2 theorem prover and
;; borrows many important ideas from it.  However, the Axe Rewriter has several
;; advantages.  The most significant is its efficient representation of terms
;; as directed acyclic graphs (DAGs).  In the DAG representation, each distinct
;; subterm is represented only once.  Nodes in the DAG represent expressions
;; and are numbered sequentially from 0.  The allowed expression types are
;; constants, variables, and functions applied to lists of arguments, each of
;; which is a constant or the number of another node.  The DAG is acyclic
;; because a function call node's arguments must be nodes with smaller numbers.

;; The Axe Rewriter also performs memoization, uses ``objectives'' to guide
;; rewriting, efficiently handles large XOR nests, provides more fine-grained
;; control of rule ordering, and provides a facility for calling the Axe Prover
;; (a separate but related tool) to discharge hypotheses of conditional rewrite
;; rules.

;; The Axe Rewriter is very fast, performing, in one example, about 600,000
;; rewrite rule attempts per second.

;; The Axe Rewriter is designed to be used as a stand-alone component, in
;; contrast to the ACL2 rewriter, which is interwoven with the rest of ACL2's
;; proof process.  The Axe Rewriter is designed to be trusted but is not proved
;; correct with ACL2 (although that could be attempted some day).

;; An alternative to using a rewriter in a verification system is to simply
;; encode all the desired transformations by hand; one would simply write a
;; program that transforms terms (DAGs) in whatever way is desired. However,
;; this is likely to be complicated and error prone.  Adding a new
;; transformation would require writing more code, and programming bugs could
;; compromise the correctness of the system.  Axe's approach is to factor the
;; problem into two parts, a general-purpose rewriter and a set of rewrite
;; rules (theorems) used to ``program'' the rewriter.  This approach has
;; several advantages.  First, it allows a large number of different
;; transformations to be added to the system; Axe contains hundreds of rewrite
;; rules, and it would be tedious to write code for all of them.  Second, Axe's
;; approach makes it easy to experiment with different sets of transformations;
;; one simply passes different sets of rewrite rules to the Axe Rewriter.
;; Similarly, one can easily change the order in which transformations are
;; applied, using Axe's system of rule ``priorities''.  Finally, adding new
;; transformations can be done in a sound way because the transformations can
;; be proved as theorems in the ACL2 logic.  This ensures that adding a new
;; rule won't render the system unsound.  When new rules are added, the amount
;; of the code that must be trusted (the code of the Axe Rewriter itself) stays
;; the same.

;; The Axe Rewriter lacks several features of the ACL2 rewriter, including
;; ``forward-chaining'' rules, a procedure to determine the types of terms, and
;; a built-in linear arithmetic procedure.  None of these features were
;; necessary for the examples discussed here.

;; TODO: combine this rewriter with the one in rewriter-new.lisp?

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;;
;; The main mutual recursion of the old rewriter ("simplify"):
;;

;TODO: Is the stuff in the dag assumed to be simplified, or not?  Some of those nodes may come from assumptions or even context.

;todo: drop EMBEDDED-DAG-DEPTH?

(mutual-recursion

 ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state), where extended-alist is irrelevant if hyps-relievedp is nil
 ;; keeps trying ASSUMPTION-ARG-LISTS until it finds a match for HYP-ARGS (thus binding some free vars) for which it can relieve all the OTHER-HYPS (using those variable bindings)
 (defund relieve-free-var-hyp-and-all-others (assumption-arg-lists ;these are lists of nodenums/quoteps for calls of fn that we can assume (where fn is the top function symbol of the hyp)
                                             hyp-args ;partially instantiated; any vars that remain must match the assumption
                                             hyp-num other-hyps
                                             alist rule-symbol
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             print-interval rewriter-rule-alist
                                             refined-assumption-alist ;we need to keep the whole alist in addition to walking down the entry for the current fn
                                             equality-assumption-alist
                                             node-replacement-alist ;pairs of the form (<nodenum> . <nodenum-or-quotep>)
                                             print
                                             memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
   (declare (xargs :mode :program ;;because of termination
                   :verify-guards nil
                   :stobjs state))
   (if (endp assumption-arg-lists)
       ;; failed to relieve the hyp:
       (prog2$ (and (member-eq rule-symbol monitored-symbols)
                    (cw "(Failed to relieve free vars in hyp ~x0 of rule ~x1.)~%" hyp-num rule-symbol))
               (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))
     (b* ((arg-list (first assumption-arg-lists))
          (fail-or-extended-alist (unify-trees-with-dag-nodes hyp-args arg-list dag-array alist)))
       (if (eq :fail fail-or-extended-alist)
           ;;this assumption didn't match:
           (relieve-free-var-hyp-and-all-others (rest assumption-arg-lists)
                                                hyp-args hyp-num other-hyps
                                                alist rule-symbol
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                                memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
         ;; the assumption matched, so try to relieve the rest of the hyps using the resulting extension of ALIST:
         (mv-let (erp other-hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
           (relieve-rule-hyps other-hyps (+ 1 hyp-num)
                              fail-or-extended-alist ;ASSUMPTION bound some free vars
                              rule-symbol
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                              print-interval rewriter-rule-alist
                              refined-assumption-alist
                              equality-assumption-alist node-replacement-alist print
                              memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
           (if erp
               (mv erp nil nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
             (if other-hyps-relievedp
                 (mv (erp-nil) t extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
               ;;this assumption matched, but we couldn't relieve the rest of the hyps:
               (relieve-free-var-hyp-and-all-others (rest assumption-arg-lists)
                                                    hyp-args hyp-num other-hyps
                                                    alist ;the original alist
                                                    rule-symbol
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                                    memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))))))))

 ;; ALIST is the substitution alist so far (it maps vars in the rule to nodenums and quoteps). If alist doesn't bind all the variables in the
 ;; HYP, we'll search for free variable matches in REFINED-ASSUMPTION-ALIST.
 ;; Relieving the hyp through rewriting may cause more nodes to be added to the DAG and more things to be added to memoization, info, and tries.
 ;; BOZO precompute the list of vars in the hyp?  or maybe just the ones that need to be bound in the alist?
 ;; Returns (mv erp hyps-relievedp alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state), where alist is irrelevant if hyps-relievedp is nil.
 ;; Otherwise, the alist returned may have been extended by the binding of free vars.
 (defund relieve-rule-hyps (hyps hyp-num alist rule-symbol
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 print-interval rewriter-rule-alist
                                 refined-assumption-alist ;maps each fn to a list of arg-lists (quoteps / nodenums in dag-array?) (have been refined for matching), can be assumed for all nodes (the vars may or may not appear already in the dag?? i think now they must appear?)
                                 equality-assumption-alist node-replacement-alist print
                                 memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
   (declare (xargs :stobjs state :measure (len hyps)))
   (if (endp hyps)
       ;; all hyps relieved:
       (mv (erp-nil) t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
     (b* ((hyp (first hyps))
          (fn (ffn-symb hyp)) ;; all hyps are conses
          (- (and (eq :verbose2 print)
                  (cw "Relieving hyp: ~x0 with alist ~x1.~%" hyp alist))))
       ;; todo: consider using CASE here:
       (if (eq :axe-syntaxp fn)
           (let* ((syntax-expr (cdr hyp)) ;; strip off the AXE-SYNTAXP
                  (result (eval-axe-syntaxp-expr-jvm syntax-expr alist dag-array)))
             (if result
                 ;;this hyp counts as relieved
                 (relieve-rule-hyps (rest hyps) (+ 1 hyp-num) alist rule-symbol
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                    memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
               (prog2$ (and (member-eq rule-symbol monitored-symbols)
                            ;;is it worth printing in this case?
                            (progn$ (cw "(Failed to relieve axe-syntaxp hyp: ~x0 for ~x1.)~%" hyp rule-symbol)
                                    ;; (cw "(Alist: ~x0)~%" alist)
                                    ;; (cw "(DAG:~%")
                                    ;; (print-array2 'dag-array dag-array dag-len)
                                    ;; (cw ")~%")
                                    ))
                       (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))))
         (if (eq :axe-bind-free fn)
             ;; To evaluate the axe-bind-free hyp, we use alist, which binds vars to their nodenums or quoteps (fffffixme free vars may be bound to entire terms!) but we also bind the special variable dag-array to the dag-array.
             ;;The soundness of Axe should not depend on what an axe-bind-free function does; thus we cannot pass alist to such a function and trust it to faithfully extend it.  Nor can we trust it to extend the dag without changing any existing nodes. TODO: What if the axe-bind-free function gives back a result that is not even well-formed?
             ;;TODO: It might be nice to be able to pass in the assumptions to the axe-bind-free-function? e.g., for finding usbp facts.
             (let* ((bind-free-expr (cadr hyp)) ;; strip off the AXE-BIND-FREE
                    (result (eval-axe-bind-free-function-application-jvm (ffn-symb bind-free-expr) (fargs bind-free-expr) alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                            ))
               (if result ;; nil to indicate failure, or an alist whose keys should be exactly (cddr hyp)
                   (let ((vars-to-bind (cddr hyp)))
                     (if (not (axe-bind-free-result-okayp result vars-to-bind dag-len))
                         (mv (erp-t)
                             (er hard? 'relieve-rule-hyps "Bind free hyp ~x0 for rule ~x1 returned ~x2, but this is not a well-formed alist that binds ~x3." hyp rule-symbol result vars-to-bind)
                             alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
                       ;; this hyp counts as relieved:
                       (relieve-rule-hyps (rest hyps) (+ 1 hyp-num)
                                          (append result alist) ;; guaranteed to be disjoint given the analysis done when the rule was made and the call of axe-bind-free-result-okayp above
                                          rule-symbol dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                          memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)))
                 ;; failed to relieve the axe-bind-free hyp:
                 (prog2$ (and (member-eq rule-symbol monitored-symbols)
                              (cw "(Failed to relieve axe-bind-free hyp: ~x0 for ~x1.)~%" hyp rule-symbol))
                         (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))))
           (if (eq :free-vars fn) ;can't be a work-hard
               (b* (((mv instantiated-hyp &)
                     (instantiate-hyp (cdr hyp) ;strip the :free-vars
                                      alist nil interpreted-function-alist)))
                 ;; If some vars remain in the instantiated-hyp, we search the REFINED-ASSUMPTIONS for matches to bind them:
                 ;; fffixme search node-replacement-alist too? or make sure all the context info gets put into REFINED-ASSUMPTIONS?
                 ;;the refined-assumptions have been refined so that (equal (pred x) t) becomes (pred x) for better matching
                 (relieve-free-var-hyp-and-all-others (lookup-eq (ffn-symb instantiated-hyp) refined-assumption-alist)
                                                      (fargs instantiated-hyp)
                                                      hyp-num
                                                      (rest hyps)
                                                      alist rule-symbol
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      print-interval rewriter-rule-alist
                                                      refined-assumption-alist
                                                      equality-assumption-alist node-replacement-alist print
                                                      memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)

                 ;;                  (mv-let (flg alist-for-free-vars)
                 ;;                          (unify-pattern-sexp-lst instantiated-hyp refined-assumptions dag-array)
                 ;;                          (if flg
                 ;;                              ;;fffixme instead of this append, pass the original alist into unify-pattern-sexp-lst?
                 ;;                              ;;BOZO i had union-equal before...
                 ;;                              (let* ((alist (append alist-for-free-vars alist)))
                 ;;                                ;;the hyp counts as relieved, and we've extended alist
                 ;;                                ;;ffixme simplify the terms that the free vars were bound to??
                 ;;                                (relieve-rule-hyps (rest hyps)
                 ;;                                                   alist
                 ;;                                                   rule-symbol
                 ;;                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                 ;;                                                   print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                 ;;                                                   memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp))
                 ;;                            ;;fail.  didn't find a match for the hyp...
                 ;;                            (prog2$ (and (member-eq rule-symbol monitored-symbols)
                 ;;                                         (progn$ (cw "(Failed to match free var in hyp: ~x0 for ~x1." instantiated-hyp rule-symbol)
                 ;;                                                 (cw "(Assumptions:~%")
                 ;;                                                 ;;this can be big?
                 ;;                                                 (print-list refined-assumptions)
                 ;;                                                 ;;fixme print the part of the dag array that supports the hyp??
                 ;;                                                 (cw ")~%Alist: ~x0~%)~%" alist)))
                 ;;                                    (mv nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries))))

                 )
             ;; HYP is not a call to :axe-syntaxp or :axe-bind-free or :free-vars:
             ;;Set the work-hard flag and strip-off work-hard if present:
             (mv-let
               (work-hardp hyp)
               (if (eq 'work-hard fn)
                   (mv t (farg1 hyp)) ;strip off the call of work-hard
                 (mv nil hyp))
               ;; First, we substitute in for all the vars in HYP:
               (mv-let
                 (instantiated-hyp free-vars-flg)
                 (instantiate-hyp hyp alist nil interpreted-function-alist)
                 (declare (ignore free-vars-flg))
                 ;; Now instantiated-hyp is an axe-tree with leaves that are quoteps and nodenums (from vars already bound).
                 ;; TODO: Consider adding a special case here to check whether the hyp is a constant (can happen during instantiation and may be very common).
                 ;; Since no free vars are in the hyp, we try to relieve the fully instantiated hyp:
                 (b* ((old-try-count tries)
                      ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                       ;;try to relieve through rewriting (this tests atom hyps for symbolp even though i think that's impossible (why??? did i mean atom hyps must be symbolps?)- but should be rare:
                       ;;bozo do we really want to add stupid natp hyps, etc. to the memoization? what about ground terms?
                       (simplify-tree-and-add-to-dag instantiated-hyp
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                     rewriter-rule-alist
                                                     nil ;nothing is yet known to be equal to instantiated-HYP - fixme name this use of nil
                                                     refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                                     memoization
                                                     info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                      ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))
                      (try-diff (and old-try-count (- tries old-try-count))))
                   (if (consp new-nodenum-or-quotep) ;tests for quotep
                       (if (unquote new-nodenum-or-quotep) ;the unquoted value is non-nil:
                           (prog2$ (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw " (~x1 tries used ~x0:~x2 (rewrote to true).)~%" rule-symbol try-diff hyp-num))
                                   ;;hyp rewrote to a non-nil constant and so counts as relieved:
                                   (relieve-rule-hyps (rest hyps)
                                                      (+ 1 hyp-num)
                                                      alist
                                                      rule-symbol
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                                      memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                         ;;hyp rewrote to *nil*:
                         (progn$ (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw "(~x1 tries wasted ~x0:~x2 (rewrote to NIL))~%" rule-symbol try-diff hyp-num))
                                 (and (member-eq rule-symbol monitored-symbols)
                                      (progn$ (cw "(Failed to relieve hyp ~x0 for ~x1.~% Reason: Rewrote to nil.~%" hyp rule-symbol)
                                              ;; (cw "Alist: ~x0.~%Assumptions:~%~x1~%DAG:~x2~%" ;;ffixme improve this printing
                                              ;;     alist
                                              ;;     refined-assumption-alist
                                              ;;     :elided ;;fffixmedag-array ;could print only the part of the dag below the maxnodenum in alist? can this stack overflow?
                                              ;;     )
                                              ;; (cw "equality assumptions: ~x0~%" equality-assumption-alist)
                                              ;;print these better?:
                                              ;; (cw "node equality assumptions: ~x0~%)" node-replacement-alist)
                                              ))
                                 (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)))
                     ;;hyp didn't rewrite to a constant (new-nodenum-or-quotep is a node number):
                     ;; Check whether the rewritten hyp is one of the known assumptions (todo: would be better to rewrite it using IFF).  TODO: Do the other versions of the rewriter/prover do something like this?
                     (if (nodenum-equal-to-refined-assumptionp new-nodenum-or-quotep refined-assumption-alist dag-array)
                         (prog2$ (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw " (~x1 tries used ~x0:~x2 (rewrote to true).)~%" rule-symbol try-diff hyp-num))
                                 ;;hyp rewrote to a known assumption and so counts as relieved:
                                 (relieve-rule-hyps (rest hyps)
                                                    (+ 1 hyp-num)
                                                    alist
                                                    rule-symbol
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                                    memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                       (prog2$
                        (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw "(~x1 tries wasted: ~x0:~x2 (non-constant result))~%" rule-symbol try-diff hyp-num))
                        (if (and work-hardp work-hard-when-instructedp)
                            ;;If we have been instructed to work hard:
                            (b* ((- (cw "(Rewriter is working hard on a hyp of ~x0, namely: ~x1~%" rule-symbol hyp)) ;print the instantiated-hyp and hyp num too?
                                 (- (cw "(Rewrote to:~%"))
                                 (- (if (member-eq print '(t :verbose :verbose2))
                                        (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep) ;fixme print the assumptions (of all kinds)?
                                      (cw ":elided")))
                                 (- (cw ")~%"))
                                 ;; we used to have to save and restore the dag, but now the prover doesn't change any nodes, so that isn't necessary
                                 ;;add the negated assumptions to the dag (fixme what about other equality-assumptions? anything else?):
                                 ((mv erp negated-assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                  (merge-trees-into-dag-array ;inefficient?
                                   (let ((assumption-terms
                                          (append (decode-refined-assumption-alist refined-assumption-alist)
                                                  (make-equalities-from-dotted-pairs node-replacement-alist) ;fffixme is all this info already in the refined-assumption-alist?
                                                  )))
                                     (prog2$ (and (member-eq print '(t :verbose :verbose2)) (cw "(assumption terms: ~x0)" assumption-terms))
                                             (negate-terms assumption-terms)))
                                   nil
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                   nil ;fixme ifns
                                   ))
                                 ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))
                                 ;;call the full prover:
                                 ((mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
                                  ;;fixme should this do mitering and merging (which would then call the prover on individual node pairs)?
                                  (prove-disjunction-with-axe-prover (cons new-nodenum-or-quotep negated-assumptions) ;these are the literals
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                     (list rewriter-rule-alist) ;fixme this should be prover-rule-alist
                                                                     interpreted-function-alist
                                                                     nil ;Sun Jan  2 19:08:59 2011 monitored-symbols (was printing too much)
                                                                     print ;:brief ;;print more for work-hard hyps (seemed to print too much? but i would like to see the failures) was :brief until Mon Nov  1 04:23:45 2010 but that may have caused errors with increment-hit-count
                                                                     (symbol-name (pack$ rule-symbol "-HYP-" hyp-num "-WORK-HARD-FOR-" tag))
                                                                     *default-stp-timeout* ;timeout ;fixme pass this around
                                                                     t ;nil ;print-timeout-goalp
                                                                     nil ;don't work hard on another work-hard hyp fffixme think about this
                                                                     info tries
                                                                     1 ;prover-depth > 1 disallows changing existing nodes
                                                                     nil ;options
                                                                     (+ -1 (expt 2 59)) ;max fixnum?
                                                                     state))
                                 ((when erp) (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)))
                              (if (eq :proved result)
                                  (progn$ ;(print-hit-counts t info (rules-from-rule-alist rewriter-rule-alist)) ;ffffixme these are cumulative counts
                                   (cw "Proved the work-hard hyp)~%")
                                   ;;the hyp counts as relieved:
                                   (relieve-rule-hyps (rest hyps)
                                                      (+ 1 hyp-num)
                                                      alist rule-symbol
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print
                                                      memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp
                                                      tag limits state))
                                (prog2$ (cw "Failed to prove the work-hard hyp for ~x0)~%" rule-symbol)
                                        (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state))))
                          (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                       (progn$ (cw "(Failed to relieve hyp ~x0 of rule ~x1 (work-hardp: ~x2, work-hard-when-instructedp: ~x3).~%" hyp rule-symbol work-hardp work-hard-when-instructedp)
                                               (cw "Reason: Rewrote to:~%")
                                               (print-dag-node-nicely new-nodenum-or-quotep 'dag-array dag-array dag-len 200)
                                               (cw "(Alist: ~x0)~%(Refined assumption alist: ~x1)~%(Equality assumption alist: ~x2)~%" alist refined-assumption-alist equality-assumption-alist)
                                               ;;print these better?:
                                               (cw "(node equality assumptions: ~x0)~%" node-replacement-alist)
                                               (cw "(DAG:~%")
                                               (print-array2 'dag-array dag-array dag-len)
                                               (cw "))~%")))
                                  (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)))))))))))))))

 ;;returns (mv erp new-rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
 (defund try-to-apply-rules (stored-rules ;the list of rules for the fn in question
                            rewriter-rule-alist args-to-match
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                            refined-assumption-alist ;can be assumed for all nodes
                            equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                            embedded-dag-depth work-hard-when-instructedp tag limits state)
   (declare (xargs :stobjs state))
   (if (endp stored-rules) ;no rule fired
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
     (b* ((stored-rule (first stored-rules))
          ((when (and limits (limit-reachedp stored-rule limits print)))
           ;; the limit for this rule has been reached, so skip this rule:
           (try-to-apply-rules (rest stored-rules) rewriter-rule-alist args-to-match
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist refined-assumption-alist equality-assumption-alist
                               node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                               embedded-dag-depth work-hard-when-instructedp tag limits state))
          (tries (and tries (+ 1 tries)))
          (alist-or-fail (unify-terms-and-dag-items-fast (stored-rule-lhs-args stored-rule)
                                                     args-to-match
                                                     dag-array
                                                     dag-len)))
       (if (eq :fail alist-or-fail)
           ;; the rule didn't match, so try the next rule:
           (try-to-apply-rules
            (rest stored-rules) rewriter-rule-alist args-to-match
            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist refined-assumption-alist equality-assumption-alist
            node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
            embedded-dag-depth work-hard-when-instructedp tag limits state)
         ;; The rule matched, so try to relieve its hyps:
         (b* ((- (and (eq print ':verbose2)
                      (cw "(Trying to apply ~x0.~%" (stored-rule-symbol stored-rule))))
              (hyps (stored-rule-hyps stored-rule))
              ((mv erp hyps-relievedp alist ; may get extended by the binding of free vars
                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)
               (if hyps
                   (let ((rule-symbol (stored-rule-symbol stored-rule))) ;delay extracting this? not always needed?
                     (relieve-rule-hyps hyps
                                        1 ;initial hyp number
                                        alist-or-fail
                                        rule-symbol
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        print-interval rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp  tag limits state))
                 ;;if there are no hyps, don't even bother: BOZO inefficient?:
                 (mv (erp-nil) t alist-or-fail dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries memoization limits state)))
              ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
           (if hyps-relievedp
               ;; the hyps were relieved, so instantiate the RHS:
               (prog2$ (and (eq print ':verbose2)
                            (cw "Rewriting with ~x0.)~%" (stored-rule-symbol stored-rule)))
                       (mv (erp-nil)
                           (sublis-var-and-eval alist (stored-rule-rhs stored-rule) interpreted-function-alist)
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           memoization
                           ;;no need to assemble the info if we are not going to print it
                           (and info (increment-hit-count-in-info-world (stored-rule-symbol stored-rule) info))
                           tries
                           (and limits (decrement-rule-limit stored-rule limits))
                           state))
             ;;failed to relieve the hyps, so try the next rule:
             (prog2$ (and (eq print :verbose2)
                          (cw "Failed to apply rule ~x0.)~%" (stored-rule-symbol stored-rule)))
                     (try-to-apply-rules
                      (cdr stored-rules)
                      rewriter-rule-alist args-to-match
                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                      refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization
                      info ;(cons (cons :fail (rule-symbol rule)) info)
                      tries
                      interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp
                      tag limits state))))))))

 ;;rename
 ;;this also simplifies as it goes!
 ;;returns (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
 (defund merge-embedded-dag-into-dag (rev-dag
                                     renaming-array-name
                                     renaming-array2 ;associates nodenums in the embedded dag with the nodenums (or qupteps) they rewrote to in the main dag
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     embedded-dag-var-alist ;associates vars in the embedded dag with their nodenums (or quoteps) in the main dag
                                     rewriter-rule-alist
                                     refined-assumption-alist ;can be assumed for all nodes
                                     equality-assumption-alist node-replacement-alist print-interval print
                                     memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
   (declare (xargs :measure t ;fake!
                   :stobjs state
                   ))
   (if (endp rev-dag)
       (mv (erp-nil) renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
     (let* ((entry (car rev-dag))
            (nodenum (car entry))
            (expr (cdr entry)))
       (if (atom expr) ;variable
           (let ((new-nodenum (lookup-eq-safe2 expr embedded-dag-var-alist 'merge-embedded-dag-into-dag))) ;drop the -safe?
             (merge-embedded-dag-into-dag (cdr rev-dag)
                                          renaming-array-name
                                          (aset1-safe renaming-array-name renaming-array2 nodenum new-nodenum)
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          embedded-dag-var-alist
                                          rewriter-rule-alist
                                          refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                          memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp  tag limits state))
         (let ((fn (ffn-symb expr)))
           (if (eq 'quote fn)
               (merge-embedded-dag-into-dag (cdr rev-dag)
                                            renaming-array-name
                                            (aset1-safe renaming-array-name renaming-array2 nodenum expr)
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            embedded-dag-var-alist
                                            rewriter-rule-alist
                                            refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                            memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp  tag limits state)
             ;;function call:
             ;;first fixup the call to be about nodenums in the main dag:
             (let* ((args (dargs expr))
                    (args (rename-args args renaming-array-name renaming-array2))
                    (expr (cons fn args)))
               ;;then simplify the function applied to the simplified args:
               (mv-let (erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                 ;;fffixme this can create a new renaming-array2 which can lead to slow-array warnings...
                 ;;ffixme call simplify-fun-call-and-add-to-dag?
                 (simplify-tree-and-add-to-dag expr
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rewriter-rule-alist
                                               nil ;;trees-equal-to-tree
                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                               memoization
                                               info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp  tag limits state)
                 (if erp
                     (mv erp renaming-array2 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                   (merge-embedded-dag-into-dag (cdr rev-dag)
                                                renaming-array-name
                                                (aset1-safe renaming-array-name renaming-array2 nodenum new-nodenum-or-quotep)
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                embedded-dag-var-alist
                                                rewriter-rule-alist
                                                refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                                memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp  tag limits state))))))))))

  (defund simplify-fun-call-and-add-to-dag (fn ;; a function
                                           args ;; list of simplified args (so these are nodenums or quoteps?)
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           rewriter-rule-alist
                                           trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                           refined-assumption-alist ;can be assumed for all nodes, for free variable matching, mentions nodenums in dag-array
                                           equality-assumption-alist ;pairs of terms over vars and quoteps
                                           node-replacement-alist ;pairs of the form (<nodenum> . <nodenum-or-quotep>)
                                           print-interval ;if non-nil the whole dag gets printed each time its size hits a multiple of this!
                                           print
                                           memoization ;conceptually, a mapping from trees to (constants and nodenums)
                                           info ;this is an info-world ;fixme call this info-world everywhere?
                                           tries interpreted-function-alist monitored-symbols
                                           embedded-dag-depth ;helps keep the names of the arrays distinct
                                           work-hard-when-instructedp
                                           tag limits state)
    (declare (xargs :stobjs state))
    (b* ((expr (cons fn args)) ;todo: use below
         ;;Try looking it up in the memoization (note that now args are simplified):
         (memo-match (and memoization (lookup-in-memoization expr memoization))))
      (if memo-match
          (mv (erp-nil)
              memo-match
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
              (if (and memoization trees-equal-to-tree)
                  (add-pairs-to-memoization trees-equal-to-tree
                                            memo-match ;the nodenum or quotep they are all equal to
                                            memoization)
                memoization)
              info tries limits state)
        ;;Try looking it up in equality-assumption-alist (BOZO should we move this down? or up?)
        ;; this uses the simplified args, so assumptions not in normal form may not ever match ;fffixme what about node-replacement-alist?
        (let ((assumption-match (replace-fun-call-using-equality-assumption-alist equality-assumption-alist fn args dag-array)))
          (if assumption-match
              ;; we replace the term with something it's equated to in assumptions...
              ;; we then to simplify the result (BOZO presimplify assumption RHSes?)
              (simplify-tree-and-add-to-dag assumption-match
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            rewriter-rule-alist
                                            (cons-if-not-equal-car (cons fn args) trees-equal-to-tree)
                                            refined-assumption-alist equality-assumption-alist node-replacement-alist
                                            print-interval
                                            print
                                            memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
            ;; Next, try to apply rules:
            (b* (((mv erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                  (try-to-apply-rules
                   (get-rules-for-fn fn rewriter-rule-alist)
                   rewriter-rule-alist args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                   memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                 ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
              (if rhs-or-nil
                  ;;A rule fired, so simplify the instantiated right-hand-side:
                  ;; This is a tail call, which allows long chains of rewrites:
                  (simplify-tree-and-add-to-dag rhs-or-nil
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                rewriter-rule-alist
                                                ;;in the common case in which simplifying the args had no effect, the car of trees-equal-to-tree will be the same as (cons fn args), so don't add it twice
                                                (cons-if-not-equal-car (cons fn args) ;could save this and similar conses in the function
                                                                       trees-equal-to-tree)
                                                refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries
                                                interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
                ;; check for dag-val-with-axe-evaluator (move up?)
                (if (and (eq 'dag-val-with-axe-evaluator fn) ;fixme what if we can just evaluate it because all args are ground terms?
                         (quotep (first args))               ;the dag
                         (integerp (second args)) ;relax this to allow a quotep? ;move this test down?
                         )
                    ;; We are rewriting a call to dag-val-with-axe-evaluator (this stuff is new)
                    ;;fffixme think about this
                    ;;ffffixme this should/could be simplified! can we call add-simplified-dag-to-dag-array (bring it into the mutual rec.)? no, vars must be handled differently!?
                    (let* ((embedded-dag (unquote (first args)))) ;either a dag or a quoted constant
                      (if (quotep embedded-dag)
                          (mv (erp-nil) embedded-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state) ;todo: update the memoization?
                        (b* ((embedded-dag-len (len embedded-dag))
                             (alist-nodenum (second args))
                             ;; (interpreted-function-alist (third args)) ;fffixme pay attention to this!
                             (embedded-dag-vars (dag-vars embedded-dag))
                             (var-lookup-terms (make-var-lookup-terms embedded-dag-vars alist-nodenum))
                             ;;add the lookup of each var to the dag:
                             ((mv erp var-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries & limits state)
                              (simplify-trees-and-add-to-dag
                               var-lookup-terms
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                               rewriter-rule-alist
                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                               memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                             ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                             ;;now rewrite the embedded dag.  each var rewrites to the corresponding result we just computed for looking it up in the alist
                             ;;other nodes get fixed up and then simplified.
                             (renaming-array-for-merge-embedded-dag-name (pack$ 'renaming-array-for-merge-embedded-dag embedded-dag-depth))
                             ((mv erp renaming-array-for-merge-embedded-dag ;this renames nodes in the embedded dag to nodes in the main dag
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                              (merge-embedded-dag-into-dag
                               (reverse embedded-dag)
                               renaming-array-for-merge-embedded-dag-name
                               (make-empty-array renaming-array-for-merge-embedded-dag-name embedded-dag-len)
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                               (pairlis$ embedded-dag-vars var-nodenums-or-quoteps)
                               rewriter-rule-alist
                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                               memoization info tries interpreted-function-alist monitored-symbols (+ 1 embedded-dag-depth) work-hard-when-instructedp  tag limits state))
                             ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
                          (mv (erp-nil)
                              (aref1 renaming-array-for-merge-embedded-dag-name renaming-array-for-merge-embedded-dag (top-nodenum embedded-dag))
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))))
                  ;; No rule fired, so no simplifcation can be done:
                  ;; This node is ready to add to the dag
                  ;; in-line this?
                  (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization)
                    (add-function-call-expr-to-dag-array-with-memo
                     fn args ;(if any-arg-was-simplifiedp (cons fn args) tree) ;could put back the any-arg-was-simplifiedp trick to save this cons
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     print-interval print
                     (cons-if-not-equal-car (cons fn args)
                                            trees-equal-to-tree) ; might be the same as tree if the args aren't simplified?) well, each arg should be simplified and memoed.
                     memoization)
                    (if erp
                        (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                      ;; combine with the case above?
                      (if (consp nodenum-or-quotep) ;must be a quotep (fixme can this happen?!):
                          (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                        ;; nodenum-or-quotep is a nodenum:
                        ;; ffixme move this up?  or move the logic for equality-assumption-alist down?
                        ;; better yet, combine the two
                        (let ((node-equality-assumption-match (assoc-in-node-replacement-alist nodenum-or-quotep node-replacement-alist)))
                          (mv (erp-nil)
                              (if node-equality-assumption-match
                                  (cdr node-equality-assumption-match) ;fffffffffffixme shouldn't rewrite this? do that for all the node-equality-assumptions outside the main clique?
                                nodenum-or-quotep)
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))))))))))))

 ;; Returns (mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state).
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
 (defund simplify-tree-and-add-to-dag (tree ;the tree to rewrite
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      rewriter-rule-alist
                                      trees-equal-to-tree ;a list of the successive RHSes, all of which are equivalent to tree (to be added to the memoization)
                                      refined-assumption-alist ;can be assumed for all nodes, for free variable matching, mentions nodenums in dag-array
                                      equality-assumption-alist ;conceptually, maps terms to terms
                                      node-replacement-alist ;pairs of the form (<nodenum> . <nodenum-or-quotep>)
                                      print-interval ;if non-nil the whole dag gets printed each time its size hits a multiple of this!
                                      print
                                      memoization ;conceptually, a mapping from trees to (constants and nodenums)
                                      info ;this is an info-world ;fixme call this info-world everywhere?
                                      tries interpreted-function-alist monitored-symbols
                                      embedded-dag-depth ;helps keep the names of the arrays distinct
                                      work-hard-when-instructedp
                                      tag limits state)
   (declare (xargs :stobjs state))
   (if (atom tree)
       (if (symbolp tree)
           ;; It's a variable (this case may be very rare; can we eliminate it by pre-handling vars in the initial term?):
           ;; First try looking it up in the equality-assumption-alist: ;fixme what about node-replacement-alist?
           ;;fixme should do this first or last?
           (let ((assumption-match (replace-var-using-equality-assumption-alist equality-assumption-alist tree)))
             (if assumption-match
                 ;; We replace the variable with something it's equated to in assumptions and then rewrite the result.
                 ;; presimplify assumption RHSes? - nah?
                 ;; BBOZO sort the assumptions into those with LHSes that are vars and those with LHSes are conses
                 (simplify-tree-and-add-to-dag assumption-match
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               rewriter-rule-alist
                                               ;; we don't equate the variable with anything in the memoization (we don't look up vars in the memoization either):
                                               trees-equal-to-tree
                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries
                                               interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
               ;; no luck looking it up in assumptions, so we just add the variable to the DAG:
               ;; BOZO make this a macro! same for other adding to dag operations?
               (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info) ;fixme don't bother to pass through the info and memo?  do memo separately?
                 (add-variable-to-dag-array-with-memo tree
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                      trees-equal-to-tree
                                                      memoization info)
                 (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))))
         ;; TREE is a nodenum (because it's an atom but not a symbol): fixme use equalities?
;ffffixme, this assumes that nodes in the dag are already rewritten.  but what if this nodenum came from a node-equality assumption? in that case, it may not be rewritten! should we simplify the cdrs of node-replacement-alist once at the beginning?  also think about equality-assumption-alist (they are terms so the cdr gets simplified each time an equality fires, but maybe they get simplified over and over).
         ;; First, see if the nodenum is mapped to anything in the node-replacement-alist:
         (let* ((replacement-match (assoc-in-node-replacement-alist tree node-replacement-alist))
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
               info tries
               limits state)))

     ;; TREE is not an atom:
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
               info tries
               limits state)

         ;; TREE is a function call:

         ;;Try looking it up in memoization (note that the args are not yet simplified):
         (let ((memo-match (and memoization (lookup-in-memoization tree memoization))))
           (if memo-match
               (mv (erp-nil)
                   memo-match
                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   (if (and memoization trees-equal-to-tree)
                       (add-pairs-to-memoization trees-equal-to-tree
                                                 memo-match ;the nodenum or quotep they are all equal to
                                                 memoization)
                     memoization)
                   info tries
                   limits state)

             ;; Handle the various kinds of if:
             (if (or (eq 'if fn)
                     (eq 'myif fn))
                 ;; First, try to resolve the if-test (fixme would like to do this in an iff context):
                 (mv-let (erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                   (b* (((mv erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                         (simplify-tree-and-add-to-dag (farg1 tree) ;the if-test
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                       rewriter-rule-alist
                                                       nil ;no trees are yet known equal to the test
                                                       refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval
                                                       print memoization info tries interpreted-function-alist monitored-symbols
                                                       embedded-dag-depth work-hard-when-instructedp tag limits state))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
                     (if (consp simplified-test)
                         ;; test simplified to a constant:
                         (mv (erp-nil) simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                       ;; test didn't simplify to a constant, so it's a nodenum.  now try looking it up in the refined-assumption-alist:
                       ;; TODO: Do this also for the other kinds of IF below
                       (if (nodenum-equal-to-refined-assumptionp simplified-test refined-assumption-alist dag-array)
                           ;; Since the test is known to be true from the refined-assumption-alist, it's as if it rewrote to 't (even though it may not be a predicate, IF/MYIF only looks at whether it is nil):
                           (mv (erp-nil) *t* dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                         (mv (erp-nil) simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))))
                   (if erp
                       (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                     (if (consp simplified-test)
                         ;; Rewrite either the then branch or the else branch, according to whether the test simplified to nil:
                         (simplify-tree-and-add-to-dag (if (unquote simplified-test) (farg2 tree) (farg3 tree))
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                       rewriter-rule-alist
                                                       (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                       refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                       embedded-dag-depth work-hard-when-instructedp tag limits state)
                       ;;couldn't resolve the if-test:
                       ;;fffixme i guess these are not tail calls...
                       (b* (((mv erp thenpart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                             (simplify-tree-and-add-to-dag (farg2 tree) ;"then" branch
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           rewriter-rule-alist
                                                           nil ;no trees are yet known equal to the then branch
                                                           refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth work-hard-when-instructedp tag limits state))
                            ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                            ((mv erp elsepart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                             (simplify-tree-and-add-to-dag (farg3 tree) ;"else" branch
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           rewriter-rule-alist
                                                           nil ;no trees are yet known equal to the else branch
                                                           refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth work-hard-when-instructedp tag limits state))
                            ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))

                         ;;this function takes simplified args and does not handle ifs (or else things might loop):
                         (simplify-fun-call-and-add-to-dag fn (list simplified-test thenpart-result elsepart-result)
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                       rewriter-rule-alist
                                                       (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                       refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                       embedded-dag-depth work-hard-when-instructedp tag limits state)))))
               (if (eq 'boolif fn)
                   ;; First, try to resolve the if-test:
                   (mv-let (erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                     (simplify-tree-and-add-to-dag (farg1 tree) ;the if-test
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   rewriter-rule-alist
                                                   nil ;no trees are yet known equal to the test
                                                   refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
                     (if erp
                         (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                       (if (consp simplified-test)
                           (if (unquote simplified-test)
                               ;;test rewrote to non-nil:
                               (simplify-tree-and-add-to-dag `(bool-fix$inline ,(farg2 tree)) ;the "then" branch
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rewriter-rule-alist
                                                             (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                             refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                             embedded-dag-depth work-hard-when-instructedp tag limits state)
                             ;;test rewrote to nil:
                             (simplify-tree-and-add-to-dag `(bool-fix$inline ,(farg3 tree)) ;the "else" branch
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           rewriter-rule-alist
                                                           (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                           refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth work-hard-when-instructedp tag limits state))
                         ;;couldn't resolve the if-test:
                         (b* (((mv erp thenpart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                               (simplify-tree-and-add-to-dag (farg2 tree) ;"then" branch
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rewriter-rule-alist
                                                             nil ;no trees are yet known equal to the then branch
                                                             refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                             embedded-dag-depth work-hard-when-instructedp tag limits state))
                              ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                              ((mv erp elsepart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                               (simplify-tree-and-add-to-dag (farg3 tree) ;"else" branch
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rewriter-rule-alist
                                                             nil ;no trees are yet known equal to the else branch
                                                             refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                             embedded-dag-depth work-hard-when-instructedp tag limits state))
                              ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
                           (simplify-fun-call-and-add-to-dag 'boolif (list simplified-test thenpart-result elsepart-result)
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                         rewriter-rule-alist
                                                         (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                         refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                         embedded-dag-depth work-hard-when-instructedp tag limits state)))))

                 (if (eq 'bvif fn)
                     ;; First, try to resolve the if-test:
                     (mv-let (erp simplified-test dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                       (simplify-tree-and-add-to-dag (farg2 tree) ;the if-test
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                     rewriter-rule-alist
                                                     nil ;no trees are yet known equal to the test
                                                     refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
                       (if erp
                           (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                         (if (consp simplified-test)
                             (if (unquote simplified-test)
                                 ;;test rewrote to non-nil:
                                 (simplify-tree-and-add-to-dag `(bvchop ;$inline
                                                                 ,(farg1 tree) ,(farg3 tree)) ;the "then" branch
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                               rewriter-rule-alist
                                                               (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                               embedded-dag-depth work-hard-when-instructedp tag limits state)
                               ;;test rewrote to nil:
                               (simplify-tree-and-add-to-dag `(bvchop ;$inline
                                                               ,(farg1 tree) ,(farg4 tree)) ;the "else" branch
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rewriter-rule-alist
                                                             (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                             refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                             embedded-dag-depth work-hard-when-instructedp tag limits state))
                           ;;couldn't resolve the if-test:
                           (b* (((mv erp size-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                                 (simplify-tree-and-add-to-dag (farg1 tree) ;size param
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                               rewriter-rule-alist
                                                               nil ;no trees are yet known equal to the the size param
                                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                               embedded-dag-depth work-hard-when-instructedp tag limits state))
                                ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                                ((mv erp thenpart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                                 (simplify-tree-and-add-to-dag (farg3 tree) ;"then" branch
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                               rewriter-rule-alist
                                                               nil ;no trees are yet known equal to the then branch
                                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                               embedded-dag-depth work-hard-when-instructedp tag limits state))
                                ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                                ((mv erp elsepart-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                                 (simplify-tree-and-add-to-dag (farg4 tree) ;"else" branch
                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                               rewriter-rule-alist
                                                               nil ;no trees are yet known equal to the else branch
                                                               refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                               embedded-dag-depth work-hard-when-instructedp tag limits state))
                                ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)))
                             (simplify-fun-call-and-add-to-dag 'bvif (list size-result simplified-test thenpart-result elsepart-result)
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           rewriter-rule-alist
                                                           (cons tree trees-equal-to-tree) ;the thing we are rewriting here is equal to tree
                                                           refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth work-hard-when-instructedp tag limits state)))))

                   ;;It wasn't any kind of IF:
                   (b* ((args (fargs tree))
                        ;; We are simplifying a call to FN on ARGS, where ARGS may themselves be trees.
                        ;; First we simplify the args:
                        ;;ffixme should we simplify the args earlier? e.g., before looking the term up in the memoization?
                        ;; FN might be a lambda.
                        ;; fixme might it be possible to not check for ground-terms because we never build them -- think about where terms might come from other than sublis-var-simple, which we could change to not build ground terms (of functions we know about)
                        ;; ffixme maybe we should try to apply rules here (maybe outside-in rules) instead of rewriting the args
                        ;; fixme could pass in a flag for the common case where the args are known to be already simplified (b/c the tree is a dag node?)
                        (- (and (eq :verbose2 print) (cw "(Rewriting args of ~x0:~%" fn)))
                        ((mv erp args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries & limits state) ;ffixme dont ignore and use any-arg-was-simplifiedp?
                         (simplify-trees-and-add-to-dag args
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        rewriter-rule-alist
                                                        refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print
                                                        memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                        ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state))
                        (- (and (eq :verbose2 print) (cw "Done rewriting args.)~%")))
                        ;;ARGS is now a list of nodenums and quoteps.
                        ;;Now we simplify FN applied to (the simplified) ARGS:
                        )
                     (if (consp fn) ;;tests for lambda
                         ;; It's a lambda, so we beta-reduce and simplify the result:
                         ;; note that we don't look up lambdas in the assumptions (this is consistent with simplifying first)
                         (let* ((formals (second fn))
                                (body (third fn))
                                ;; TODO: We could avoid the consing in make-alist-fast by making a variant of sublis-var-and-eval that takes 2 lists:
                                (new-expr (sublis-var-and-eval (pairlis$-fast formals args) body interpreted-function-alist)))
                           ;;simplify the result of beta-reducing:
                           (simplify-tree-and-add-to-dag new-expr
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                         rewriter-rule-alist
                                                         (cons tree trees-equal-to-tree) ;we memoize the lambda
                                                         refined-assumption-alist equality-assumption-alist node-replacement-alist print-interval print memoization info tries
                                                         interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
                       ;;test for ground term
                       (if (and (all-consp args)
                                (or (member-eq fn *axe-evaluator-functions*) ;reordered
                                    (eq fn 'DAG-VAL-WITH-AXE-EVALUATOR) ;new Thu Jun 24 05:32:19 2010 add the other fns..
                                    (assoc-eq fn interpreted-function-alist) ;ffffffixme
                                    ;;ffixme maybe for soundness we must pass in defns in the ifns for all fns we may encounter in the dag... (e.g., for checking when we flatten embedded dags)
                                    )
                                ;; (not (eq 'repeat fn)) ;Wed Feb 16 22:23:28 2011 ;todo: just don't include repeat in the evaluator?
                                (not (eq fn 'th)) ;ffffixme drop this check?
                                )
                           ;; Call the evaluator:
                           (let ((result (enquote (apply-axe-evaluator-to-quoted-args fn args interpreted-function-alist 0))))
                             (mv (erp-nil)
                                 result
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 (and memoization
                                      ;;we memoize the ground term (should we?!?!)
                                      (add-pairs-to-memoization (cons tree trees-equal-to-tree)
                                                                result ;the quoted constant they are all equal to
                                                                memoization))
                                 info tries limits state))
                         ;;Otherwise, simplify the non-lambda FN applied to the simplified args:
                         (simplify-fun-call-and-add-to-dag fn args
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           rewriter-rule-alist
                                                           (cons tree trees-equal-to-tree) ;the thing we are rewriting is equal to tree
                                                           refined-assumption-alist equality-assumption-alist node-replacement-alist
                                                           print-interval
                                                           print
                                                           memoization
                                                           info tries interpreted-function-alist monitored-symbols
                                                           embedded-dag-depth work-hard-when-instructedp tag limits state)))))))))))))

 ;;simplify all the trees in tree-lst and add to the DAG
 ;;returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries changed-anything-flg limits state)
 ;;if the items in TREES are already all nodenums or quoted constants this doesn't re-cons-up the list
 ;;not tail-recursive, btw.
 ;; The changed-anything-flg flag is not used by callers other than this function itself.
 (defund simplify-trees-and-add-to-dag (trees
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       rewriter-rule-alist
                                       refined-assumption-alist ;can be assumed for all nodes
                                       equality-assumption-alist node-replacement-alist print-interval print
                                       memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state)
   (declare (xargs :measure (len trees) :stobjs state))
   (if (endp trees)
       (mv (erp-nil) trees dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries nil limits state)
     (b* ((first-tree (first trees))
          ;; why do we do the rest before the first?
          ((mv erp rest-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries changed-anything-for-rest limits state)
           (simplify-trees-and-add-to-dag (rest trees)
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          rewriter-rule-alist refined-assumption-alist equality-assumption-alist node-replacement-alist
                                          print-interval print memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries nil limits state))
          ((mv erp first-tree-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
           (simplify-tree-and-add-to-dag first-tree
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         rewriter-rule-alist nil refined-assumption-alist equality-assumption-alist node-replacement-alist
                                         print-interval print memoization info tries interpreted-function-alist monitored-symbols embedded-dag-depth work-hard-when-instructedp tag limits state))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries nil limits state))
          ;;this avoids reconsing when nothing changes (maybe use cons-with-hint?):
          (changed-anything (or changed-anything-for-rest
                                (not (equal first-tree-result first-tree)) ;slow?
                                ))
          (result (if changed-anything
                      (cons first-tree-result rest-result)
                    trees)))
       (mv (erp-nil) result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries changed-anything limits state))))

  ) ;end of mutual-recursion

;; For each node in REV-DAG, fix up its args (if any) according to the renaming-array, then add its simplified form to the dag-array and add its new nodenum or quotep to the renaming.
;; Returns (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array info tries limits state).
;ffixme for speed, could keep track the lowest node renamed (anything lower renames to itself)?
(defun add-simplified-dag-to-dag-array (rev-dag ;low nodes come first; can there be gaps in the numbering?
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        renaming-array ;;maps nodenums in rev-dag to the nodenums or quoteps they rewrote to in dag-array
                                        rewriter-rule-alist
                                        refined-assumption-alist ;mentions nodenums in dag-array (can be assumed for all nodes)
                                        equality-assumption-alist ;dotted pairs of terms (can be assumed for all nodes) ;fffixme handle this better (see the node-replacement-array)
                                        print-interval print
                                        memoization
                                        info ;tracks numbers of rule hits
                                        tries ;tracks the amount of work (number of attempts to match a rule with a term) done by the rewriter
                                        interpreted-function-alist
                                        monitored-symbols
                                        internal-context-array ;either nil (not using internal contexts), or an array that associates each nodenum in rev-dag with a contextp (in terms of nodes in dag-array) to be assumed when rewriting the node
                                        context-for-all-nodes ;a possibly-negated-nodenumsp (list of items of the form <nodenum> or (not <nodenum>)) where the nodenums are in dag-array (can be assumed for all nodes)
                                        known-booleans
                                        work-hard-when-instructedp
                                        tag limits state)
  (declare (xargs :mode :program
                  :guard (and (rule-limitsp limits) ;todo: add more guard conjuncts
                              (maybe-bounded-memoizationp memoization dag-len)
                              ;; For soundness, we should not have both memoization and a non-nil internal-context-array!
                              ;; We could consider memoizing per node, or using a memoization for nodes that have no context.
                              (not (and memoization
                                        internal-context-array))
                              (possibly-negated-nodenumsp context-for-all-nodes)
                              (symbol-listp known-booleans)
                              (booleanp work-hard-when-instructedp)
                              (symbolp tag)
                              (rule-limitsp limits))
                  :stobjs state))
  (if (endp rev-dag)
      (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array info tries limits state)
    (let* ((entry (first rev-dag))
           (nodenum (car entry)) ;or, if they are consecutive, we could track this numerically..
           (expr (cdr entry)))
      (if (quotep expr) ;inline? ;this should be rare...
          (add-simplified-dag-to-dag-array (rest rev-dag)
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           (aset1-safe 'renaming-array renaming-array nodenum expr)
                                           rewriter-rule-alist refined-assumption-alist equality-assumption-alist print-interval print memoization info tries interpreted-function-alist
                                           monitored-symbols internal-context-array context-for-all-nodes known-booleans work-hard-when-instructedp tag limits state)
        ;;expr is a variable or function call (TODO: Split out the var case):
        (let* ((context-for-this-node (if internal-context-array (aref1 'context-array internal-context-array nodenum) (true-context)))
               (full-context (conjoin-contexts context-for-all-nodes context-for-this-node))) ;todo: reverse the args to conjoin-contexts?
          (if (false-contextp full-context)
              ;; The node is in a false context, so we can rewrite it to whatever we want:
              ;; TODO: Consider eliminating this, if we can do a better job resolving IFs, perhaps when we compute the contexts.
              (prog2$ (and print (cw "! Node ~x0 is irrelevant !~%" nodenum))
                      (add-simplified-dag-to-dag-array
                       (rest rev-dag)
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                       (aset1-safe 'renaming-array renaming-array nodenum (enquote :irrelevant)) ;fixme think about this
                       rewriter-rule-alist refined-assumption-alist equality-assumption-alist print-interval print memoization info tries interpreted-function-alist
                       monitored-symbols internal-context-array context-for-all-nodes known-booleans work-hard-when-instructedp tag limits state))
            (b* ((node-replacement-alist-for-this-node (node-replacement-alist-for-context full-context dag-array known-booleans print)) ;fffixme this gets redone over and over for context-for-all-nodes?
                 ;; This is an attempt to include the context information in the assumptions used for free var matching:
                 (context-exprs-for-this-node (context-to-exprs full-context dag-array))
                 (refined-assumption-alist-for-this-node (extend-refined-assumption-alist context-exprs-for-this-node refined-assumption-alist))
                 ;;(context-assumptions (get-extra-assumptions full-context predicate-nodenum-term-alist))
                 ;;(dummy (and context-assumptions (cw "Using ~x0 context assumption(s) for node ~x1.~%" (len context-assumptions) nodenum)))
                 ;;(equality-assumption-alist-for-this-node (add-equality-pairs context-assumptions equality-assumption-alist))
                 ;;(assumptions-for-this-node (refine-assumptions-for-matching context-assumptions assumptions))
                 (- (and print
                         (progn$ (and (or (eq print :verbose2) (eq print :verbose))
                                      nil ;(cw "Using ~x0 context assumption(s) for node ~x1 (including ~x2 for matching free vars).~%" (len node-replacement-alist-for-this-node) nodenum (len context-exprs-for-this-node))
                                      )
                                 (and (not (eq :brief print)) ;new
                                      (equal 0 (mod nodenum 1000)) ;how expensive is this mod?  could keep a counter... or always track the next multiple of 1000 and compare to that?
                                      (cw " Processing node: ~x0~%" nodenum)))))
                 ((mv erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info tries limits state)
                  ;;BOZO might there be IFs here?
                  ;;bozo might get speed up by taking advantage of the fact that the expr came from a dag node and so can't be some big tree
                  ;;it's probably a function call tree? check whether it's of an if or lambda and if not, don't waste time simplifying the args? pass in a flag saying the args are simplified?
                  ;;fffixme do different things depending on whether expr is a var or a fn call:
                  (simplify-tree-and-add-to-dag ;fffixme call simplify-fun-call-and-add-to-dag?? ;or (because we may still want to handle ifs and other stuff) pass a flag saying args are simplified - what about lambdas?
                   (rename-var-or-fn-call-expr expr renaming-array (+ -1 nodenum))
                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                   rewriter-rule-alist
                   nil ;no other trees are yet known to be equal to expr
                   refined-assumption-alist-for-this-node
                   equality-assumption-alist ;yuck! these are still pairs of terms?!
                   node-replacement-alist-for-this-node
                   print-interval print
                   (if internal-context-array nil memoization) ; TODO: Replace this with just memoization once have verified guards
                   info tries interpreted-function-alist
                   monitored-symbols
                   0 ;embedded-dag-depth
                   work-hard-when-instructedp
                   tag limits state))
                 ((when erp) (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array info tries limits state)))
              (add-simplified-dag-to-dag-array (rest rev-dag)
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               (aset1-safe 'renaming-array renaming-array nodenum new-nodenum-or-quotep)
                                               rewriter-rule-alist refined-assumption-alist equality-assumption-alist print-interval print
                                               memoization ;invalid if internal-context-array is non-nil but won't be used on future iterations
                                               info tries interpreted-function-alist monitored-symbols
                                               internal-context-array
                                               context-for-all-nodes known-booleans work-hard-when-instructedp tag limits state))))))))

;; Returns (mv erp simplified-dag-or-quotep limits state) where SIMPLIFIED-DAG-OR-QUOTEP is equivalent to DAG, given the REFINED-ASSUMPTION-ALIST, EQUALITY-ASSUMPTION-ALIST, context stuff, the rules in REWRITER-RULE-ALIST, and the bindings in INTERPRETED-FUNCTION-ALIST.
;;does one simplification pass (NO, now does 2 if contexts are to be used) -- is the result then completely simplified? - what if one of the context assumptions (a pred in an if-test governing a term) gets simplified on this pass?  that might let us do better at simplifying nodes guarded by that node.
;does not simplify the refined-assumptions or equality-assumption-alist (or context nodes?) passed in
;fffixme stay in the world of arrays, instead of going back and forth between arrays and dags?
;If both memoizep and use-internal-contextsp are non-nil, this will NOT memoize on the second pass (that would be unsound!), unless we change the memoization machinery to track contexts - fffixme can that lead to exponential behavior?!
;fffixme consider having this return an array...
;change this to load the dag into the array first and to use assumptions that refer to that array (instead of possibly being huge terms)??
;ffixme consider doing a top-down pass using a worklist to determine which nodes actually need to be simplified (making use of ifs, etc.)
;ffffixme include only the necesary nodes in the context?!
;ffixme external contexts could allow us to drop whole subdags and not waste time simplifying them..
;;smashes 'dag-array, 'dag-parent-array, and 'renaming-array (fixme anything else?)
(defun simplify-dag (dag ;; must not be a quotep, should have no gaps in the numbering? (should have no duplicate entries? maybe okay if we are doing the first phase with no contexts?),
                     rewriter-rule-alist
                     slack-amount ;amount of extra space to allocate (slack before the arrays have to be expanded; does not affect soundness)
                     refined-assumption-alist ;maps fns to lists of arg-lists (quoteps/nodenums) in external-context-array (this function may find more assumptions from the context of each node)
                     equality-assumption-alist ;these are dotted pairs of terms (they represent a subset of REFINED-ASSUMPTION-ALIST?)
                     print-interval print
                     interpreted-function-alist
                     monitored-symbols
                     memoizep
                     use-internal-contextsp ;these contexts will come from dag itself.  there are also external contexts:
                     ;;rename these things assumptions-arrayXXX?
                     ;;eventually merge this stuff with the handling of equality assumptions?  what currently happens to equalities in the external-context-array?
                     ;; these are "external" contexts to be assumed for all nodes:
                     external-context-array-name
                     external-context-array ;this seems to *not* get smashed.
                     external-context ;a possibly-negated-nodenumsp over nodes in external-context-array; indicates facts we can assume
                     external-context-array-len
                     external-context-parent-array-name
                     external-context-parent-array
                     external-context-dag-constant-alist
                     external-context-dag-variable-alist
                     work-hard-when-instructedp tag limits state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and (pseudo-dagp dag)
                              (natp external-context-array-len)
                              (natp slack-amount)
                              (rule-limitsp limits))))
  ;;Even if use-internal-contextsp is non-nil, we first simplify without internal contexts, to make sure that the contexts themselves are simplified (fixme might that take several passes? when we use them on the second pass (otherwise when using a term that came from a context we might have to simplify it before using it, which might be awkward (a whole subdag would be involved, and simplifying the context might cause other terms from context to be simplified)... and what about something like (if x (foo x) (bar x)) where the test x guards an appearance of itself? rethink this?
;in many cases the contexts will equate terms with constants..
  (b* ((top-nodenum (top-nodenum dag))
       (original-dag-len (len dag)) ;fixme could just add one to the top node if there are no gaps.. or maybe gaps are okay - then pass in the dag-len?
       (- (and print (cw "(Simplifying DAG (~x0 nodes)...~%" original-dag-len)))
       ;; Preload the external contexts into the dag-array (node numbers remain the same):
       (max-external-context-nodenum (+ -1 external-context-array-len))
       (initial-array-size (+ original-dag-len external-context-array-len slack-amount))
       (dag-array (make-empty-array 'dag-array initial-array-size))
       (dag-array (copy-array-vals max-external-context-nodenum external-context-array-name external-context-array 'dag-array dag-array)) ;make a version that also updates the aux data structures? maybe add-array-nodes-to-dag? for speed, make sure we take advantage of the fact that there are no dups in the context-array?
       (dag-len external-context-array-len)
       (dag-parent-array (make-empty-array 'dag-parent-array initial-array-size))
       (dag-parent-array (copy-array-vals max-external-context-nodenum external-context-parent-array-name external-context-parent-array 'dag-parent-array dag-parent-array))
       (dag-constant-alist external-context-dag-constant-alist) ;inline?
       (dag-variable-alist external-context-dag-variable-alist) ;inline?
       (- (and print (cw "(Simplifying with no internal contexts (memoize ~x0):~%" memoizep)))
       ;; Work hard on the first rewrite if there won't be a second one:
       (work-hard-on-first-rewrite (not use-internal-contextsp) ;nil ;work-hard-when-instructedp ;Mon Sep 20 09:54:39 2010 since we are not using contexts, working hard can be a big waste.  on the other hand, we are memoizing on this rewrite (but can't on the one with contexts), so work-hards would be memoized here but not there
                                   )
       (known-booleans (known-booleans (w state)))
       ;; STEP 1: Rewrite dag by simplifying its nodes and adding to dag-array:
       ((mv erp dag-array & & & & renaming-array info tries limits state) ;use the ignored values?!
        (add-simplified-dag-to-dag-array (reverse dag) ;;we'll simplify nodes from the bottom-up
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                         (make-empty-array 'renaming-array original-dag-len)
                                         rewriter-rule-alist
                                         refined-assumption-alist ;mentions nodenums in external-context-array; those nodes have the same numbers in dag-array
                                         equality-assumption-alist
                                         print-interval print
                                         (and memoizep ;hope this is okay and not too slow:
                                              (empty-memoization)) ;fixme add some option to make this bigger?
                                         (and print (empty-info-world)) ;used to track the number of rule hits
                                         (and print (zero-tries)) ;(if rewriter-rule-alist (zero-tries) nil) ;fixme think about this
                                         interpreted-function-alist
                                         monitored-symbols ;; (if use-internal-contextsp nil monitored-symbols) ;; (don't monitor if this is the first of two passes) -- TODO: Note that this can cause problems if we get an unexpected error (e.g., in an axe-syntaxp function) on the first pass)
                                         nil ;internal-context-array=nil means don't use internal contexts
                                         external-context
                                         known-booleans
                                         work-hard-on-first-rewrite
                                         tag limits state))
       ((when erp) (mv erp nil limits state))
       (- (and print (print-hit-counts print info (rules-from-rule-alist rewriter-rule-alist))))
       (- (and print tries (cw "(~x0 tries.)" tries))) ;print these after dropping non supps?
       (- (and print (cw ")"))) ;  "(Simplifying with no internal contexts"
       (renamed-top-node (aref1 'renaming-array renaming-array top-nodenum)))
    (if (consp renamed-top-node) ; check for quotep
        (prog2$ (and print (cw "Result: ~x0)~%" renamed-top-node)) ; balances "(Simplifying DAG ...
                (mv (erp-nil) renamed-top-node limits state))
      (if (not use-internal-contextsp)     ;why would this ever be the case?
          (prog2$ (and print (cw ")~%"))   ; balances "(Simplifying DAG ...
                  (mv (erp-nil)
                      ;; todo: could consider doing prune-with-contexts here
                      (drop-non-supporters-array 'dag-array dag-array renamed-top-node print) ; also converts to a dag (list)
                      limits state))
        ;; STEP 2: Rewrite again, using internal contexts:
        (b* (;;could we stay in the world of arrays when doing this?
             ;;could check here whether nothing changed and not build a new list?
             (dag (drop-non-supporters-array 'dag-array dag-array renamed-top-node print))
             (dag-len (+ 1 (top-nodenum dag)))
             (- (and print (cw "~%(Simplifying again with internal contexts (~x0 nodes)...~%" dag-len)))
             (initial-array-size (+ (* 2 dag-len) external-context-array-len slack-amount)) ;the array starts out containing the dag; we leave space for another copy, plus the external context nodes, plus some slack
             ;;Load all the nodes into the dag-array (fixme only include nodes that support contexts?!):
;ffixme should we start by pre-loading the context array into the dag-array, like we do above?  that might make it harder to figure out what contexts to use?
             (dag-array (make-into-array-with-len 'dag-array dag initial-array-size))
             ;; Make the auxiliary data structures for the DAG:
             ((mv dag-parent-array dag-constant-alist dag-variable-alist)
              (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
             ;; Now figure out the context we can use for each node
             ;; TODO: If this doesn't contain any information, consider skipping the rewrite below (see below):
             (internal-context-array (make-full-context-array-with-parents 'dag-array dag-array dag-len dag-parent-array))
             ;; ((when ...) ; could check here whether there is any context information to use
             ;;  (and print (cw ")~%"))
             ;;  (mv (erp-nil) dag limits state))
             ;; TODO: Consider using the context array here to prune if branches (maybe even repeatedly in a loop).
             ;; Add nodes that support the external context:
             ((mv erp
                  dag-array dag-len-with-external-context-nodes dag-parent-array dag-constant-alist dag-variable-alist
                  renaming-array ;maps context nodes to nodes in dag-array
                  )
              (add-array-nodes-to-dag 0 max-external-context-nodenum
                                      external-context-array-name external-context-array external-context-array-len
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      (make-empty-array 'renaming-array (max 1 (+ 1 max-external-context-nodenum) ;fixme the max of 1 is new
                                                                             ))))
             ((when erp) (mv erp nil nil state))
             ;;fix-up the external-context to refer to nodes in dag-array:
             (external-context (fixup-possibly-negated-nodenums external-context 'renaming-array renaming-array))
             ;;ffixme handle (false-context)?!  can that happen?  what would it mean?!  that the assumptions contradict?!
             (refined-assumption-alist (fixup-refined-assumption-alist refined-assumption-alist 'renaming-array renaming-array nil))
             ;; Simplify all the nodes:
             ((mv erp dag-array & & & & renaming-array info tries limits state) ;use the ignored things ?!
              (add-simplified-dag-to-dag-array (reverse dag)
                                               dag-array
                                               dag-len-with-external-context-nodes
                                               dag-parent-array dag-constant-alist dag-variable-alist
                                               (make-empty-array 'renaming-array dag-len) ;reuse this? does the default value need to be in every slot?
                                               rewriter-rule-alist
                                               refined-assumption-alist ;mentions nodenums in dag-array
                                               equality-assumption-alist print-interval print
                                               nil ;memoization (not sound to memoize between nodes when using internal contexts)  :TODO: Print a warning if this turns off memoization.
                                               (and print (empty-info-world)) ;used to track the number of rule hits
                                               (and print (zero-tries)) ;fixme think about this (if rewriter-rule-alist (zero-tries) nil)
                                               interpreted-function-alist monitored-symbols
                                               ;;fixme refine the internal contexts? handle equalities?:
                                               internal-context-array
                                               external-context known-booleans work-hard-when-instructedp tag limits state))
             ((when erp) (mv erp nil nil state))
             (- (and print (cw "(~x0 tries.)~%" tries)))
             (- (and print (print-hit-counts print info (rules-from-rule-alist rewriter-rule-alist))))
             (- (and print (cw ")")))
             (top-nodenum (top-nodenum dag))
             (renamed-top-node (aref1 'renaming-array renaming-array top-nodenum))
             )
          (if (quotep renamed-top-node)
              (prog2$ (and print (cw ")~%"))
                      (mv (erp-nil) renamed-top-node limits state))
            (if (not (integerp renamed-top-node)) ;impossible?
                (progn$ (print-list renaming-array)
                        (er hard? 'simplify-dag "renaming of node ~x0 must be a quotep or an integer" top-nodenum)
                        (mv (erp-t) nil limits state))
              (let ((dag
                     ;;could check here whether nothing changed and not build a new list?
                     ;;is this call still important? (well it converts the array to a list...)
                     (drop-non-supporters-array 'dag-array dag-array renamed-top-node print)))
                (prog2$ (and print (cw ")~%"))
                        (mv (erp-nil) dag limits state))))))))))

;TODO: Try calling this (but what about rules that commute things based on node number? they may cause this to loop forever?!  what about simplify-xors?  can it commute based on node number -- maybe change that to use some notion of term size...)
;;Call simplify-dag repeatedly until nothing changes (except perhaps node
;;numbering).  Multiple calls may be needed because internal contexts may be
;;simplified and then help other things get simplified (which may also be
;;internal contexts, etc.)
;; Returns (mv erp result limits state) where RESULT is a
;; dag-or-quotep equivalent to DAG, given the REFINED-ASSUMPTION-ALIST,
;; EQUALITY-ASSUMPTION-ALIST, context stuff, the rules in REWRITER-RULE-ALIST, and the
;; bindings in INTERPRETED-FUNCTION-ALIST
(defun repeat-simplify-dag (dag ;; must not be a quotep, should have no gaps in the numbering? (should have no duplicate entries? maybe okay if we are doing the first phase with no contexts?), dag can't be empty (btw, does weak-dagp require that?)
                            rewriter-rule-alist
                            slack-amount ;amount of extra space to allocate (slack before the arrays have to be expanded; does not affect soundness)
                            refined-assumption-alist ;maps fns to lists of arg-lists (quoteps/nodenums in external-context-array) (this function may find more assumptions from the context of each node)
                            equality-assumption-alist ;these represent a subset of REFINED-ASSUMPTION-ALIST?
                            print-interval print
                            interpreted-function-alist monitored-symbols memoizep
                            use-internal-contextsp ;these contexts will come from dag itself.  there are also external contexts:
                            ;;rename these things assumptions-arrayXXX?
                            ;;eventually merge this stuff with the handling of equality assumptions?  what currently happens to equalities in the external-context-array?
                            ;; these are "external" contexts to be assumed for all nodes:
                            external-context-array-name
                            external-context-array ;this seems to *not* get smashed.
                            external-context ;a possibly-negated-nodenumsp over nodes in external-context-array; indicates facts we can assume
                            external-context-array-len
                            external-context-parent-array-name
                            external-context-parent-array
                            external-context-dag-constant-alist
                            external-context-dag-variable-alist
                            work-hard-when-instructedp tag limits state)
  (declare (xargs :mode :program
                  :guard (and (rule-limitsp limits)
                              ;;todo
                              )
                  :stobjs state))
  (mv-let (erp result-dag limits state)
    (simplify-dag dag
                  rewriter-rule-alist
                  slack-amount
                  refined-assumption-alist
                  equality-assumption-alist
                  print-interval print
                  interpreted-function-alist monitored-symbols memoizep
                  use-internal-contextsp
                  external-context-array-name
                  external-context-array
                  external-context
                  external-context-array-len
                  external-context-parent-array-name
                  external-context-parent-array
                  external-context-dag-constant-alist
                  external-context-dag-variable-alist
                  work-hard-when-instructedp tag limits state)
    (if erp
        (mv erp nil nil state)
      (if (quotep result-dag)
          (mv (erp-nil) result-dag limits state)
        (if (equivalent-dags dag result-dag)
            (mv (erp-nil) dag limits state)
          (progn$ (cw "(Something changed, so simplify again.)~%")
                  (print-list result-dag)
                  (repeat-simplify-dag result-dag
                                       rewriter-rule-alist
                                       slack-amount
                                       refined-assumption-alist
                                       equality-assumption-alist
                                       print-interval print
                                       interpreted-function-alist monitored-symbols memoizep
                                       use-internal-contextsp
                                       external-context-array-name
                                       external-context-array
                                       external-context
                                       external-context-array-len
                                       external-context-parent-array-name
                                       external-context-parent-array
                                       external-context-dag-constant-alist
                                       external-context-dag-variable-alist
                                       work-hard-when-instructedp tag limits state)))))))

;call simplify-dag either once or repeatedly, according to exhaustivep
;; Returns (mv erp result limits state) where RESULT is a
;; dag-or-quotep equivalent to DAG, given the REFINED-ASSUMPTION-ALIST,
;; EQUALITY-ASSUMPTION-ALIST, context stuff, the rules in REWRITER-RULE-ALIST, and the
;; bindings in INTERPRETED-FUNCTION-ALIST
(defun maybe-repeat-simplify-dag (dag ;; must not be a quotep, should have no gaps in the numbering? (should have no duplicate entries? maybe okay if we are doing the first phase with no contexts?), dag can't be empty (btw, does weak-dagp require that?)
                                  rewriter-rule-alist
                                  slack-amount ;amount of extra space to allocate (slack before the arrays have to be expanded; does not affect soundness)
                                  refined-assumption-alist ;maps fns to lists of arg-lists (quoteps/nodenums in external-context-array) (this function may find more assumptions from the context of each node)
                                  equality-assumption-alist ; these represent a subset of REFINED-ASSUMPTION-ALIST?
                                  print-interval print
                                  interpreted-function-alist monitored-symbols memoizep
                                  use-internal-contextsp ;these contexts will come from dag itself.  there are also external contexts:
                                  ;;rename these things assumptions-arrayXXX?
                                  ;;eventually merge this stuff with the handling of equality assumptions?  what currently happens to equalities in the external-context-array?
                                  ;; these are "external" contexts to be assumed for all nodes:
                                  external-context-array-name
                                  external-context-array ;this seems to *not* get smashed.
                                  external-context ;a possibly-negated-nodenumsp over nodes in external-context-array; indicates facts we can assume
                                  external-context-array-len
                                  external-context-parent-array-name
                                  external-context-parent-array
                                  external-context-dag-constant-alist
                                  external-context-dag-variable-alist
                                  work-hard-when-instructedp tag
                                  exhaustivep
                                  limits state)
  (declare (xargs :mode :program
                  :guard (and (rule-limitsp limits)
                              ;;todo
                              )
                  :stobjs state))
  (if exhaustivep
      (repeat-simplify-dag dag
                           rewriter-rule-alist
                           slack-amount
                           refined-assumption-alist
                           equality-assumption-alist
                           print-interval print
                           interpreted-function-alist monitored-symbols memoizep
                           use-internal-contextsp
                           external-context-array-name
                           external-context-array
                           external-context
                           external-context-array-len
                           external-context-parent-array-name
                           external-context-parent-array
                           external-context-dag-constant-alist
                           external-context-dag-variable-alist
                           work-hard-when-instructedp tag limits state)
    (simplify-dag dag
                  rewriter-rule-alist
                  slack-amount
                  refined-assumption-alist
                  equality-assumption-alist
                  print-interval print
                  interpreted-function-alist monitored-symbols memoizep
                  use-internal-contextsp
                  external-context-array-name
                  external-context-array
                  external-context
                  external-context-array-len
                  external-context-parent-array-name
                  external-context-parent-array
                  external-context-dag-constant-alist
                  external-context-dag-variable-alist
                  work-hard-when-instructedp tag limits state)))

;; Returns (mv erp result limits state) where RESULT is a dag-or-quotep equivalent to DAG, given the REFINED-ASSUMPTION-ALIST, EQUALITY-ASSUMPTION-ALIST, context stuff, the rules in REWRITER-RULE-ALIST, and the bindings in INTERPRETED-FUNCTION-ALIST.
;ffixme don't go back and forth between lists and arrays so much..
;goes until either phase has no effect...
;whenever this is called we've just rewritten the dag, so if normalizing xors does nothing, we are done
;fixme - add the ability to assume the bottom n nodes of the dag are simplified?
;dag must not be a quotep
(defun normalize-xors-and-simplify-until-stable (dag rewriter-rule-alist slack-amount
                                                     refined-assumption-alist ;mentions nodenums in the context-array
                                                     equality-assumption-alist
                                                     print-interval print interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                                                     context-array-name
                                                     context-array
                                                     context ;(list of items of the form <nodenum> or (not <nodenum>) - can this be the false context?
                                                     context-array-len context-parent-array-name context-parent-array context-dag-constant-alist context-dag-variable-alist
                                                     work-hard-when-instructedp tag exhaustivep limits state)
  (declare (xargs :mode :program
                  :guard (and (rule-limitsp limits)
                              ;;todo
                              )
                  :stobjs state))
  (b* (((mv erp normalized-dag changep) (simplify-xors dag print)) ;now does both bitxors and bvxors (seemed important to do them both at the same time?)
       ;;(normalized-dag (simplify-bvxors normalized-dag print)) ;new!
       ((when erp) (mv erp nil nil state)))
    (if (quotep normalized-dag) ;if we reduced it to a constant we are done:
        (mv (erp-nil) normalized-dag limits state)
      (if (not changep)
          (mv (erp-nil) dag limits state) ;;normalizing xors did nothing, so we are done (we just simplified before calling this function, so doing it again won't help)
        (mv-let (erp simplified-dag limits state)
          (maybe-repeat-simplify-dag normalized-dag rewriter-rule-alist slack-amount refined-assumption-alist equality-assumption-alist
                                     print-interval print
                                     interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                                     context-array-name
                                     context-array
                                     context ;(list of items of the form <nodenum> or (not <nodenum>)
                                     context-array-len context-parent-array-name context-parent-array context-dag-constant-alist context-dag-variable-alist
                                     work-hard-when-instructedp tag exhaustivep limits state)
          (if erp
              (mv erp nil nil state)
            ;; if we reduced it to a constant we are done
            (if (quotep simplified-dag)
                (mv (erp-nil) simplified-dag limits state)
              ;; normalizing xors did nothing, so we are done (we already rewrote until stable, so doing it again won't help)
              (if (equivalent-dags simplified-dag normalized-dag)
                  (mv (erp-nil) normalized-dag limits state)
                (normalize-xors-and-simplify-until-stable
                 simplified-dag rewriter-rule-alist slack-amount refined-assumption-alist equality-assumption-alist print-interval print
                 interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                 context-array-name
                 context-array
                 context ;(list of items of the form <nodenum> or (not <nodenum>)
                 context-array-len context-parent-array-name context-parent-array
                 context-dag-constant-alist context-dag-variable-alist
                 work-hard-when-instructedp
                 tag exhaustivep limits state)))))))))

;;pass in a flag for whether the xors are normalized???
;;dag must not be a quotep
;; Returns (mv erp res limits state), where RES is a dag or a quotep.
(defun simplify-and-normalize-xors-until-stable (dag rewriter-rule-alist slack-amount simplify-xorsp
                                                     refined-assumption-alist ;mentions nodenums in the context-array
                                                     equality-assumption-alist
                                                     print-interval print interpreted-function-alist
                                                     monitored-symbols memoizep use-internal-contextsp
                                                     context-array-name
                                                     context-array
                                                     context ;(list of items of the form <nodenum> or (not <nodenum>)
                                                     context-array-len context-parent-array-name context-parent-array context-dag-constant-alist context-dag-variable-alist
                                                     work-hard-when-instructedp tag exhaustivep limits state)
  (declare (xargs :mode :program
                  :guard (and (rule-limitsp limits)
                              ;;todo
                              )
                  :stobjs state))
  (mv-let (erp simplified-dag-or-quotep limits state)
    (maybe-repeat-simplify-dag dag rewriter-rule-alist slack-amount refined-assumption-alist equality-assumption-alist
                               print-interval print interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                               context-array-name context-array context context-array-len context-parent-array-name context-parent-array
                               context-dag-constant-alist context-dag-variable-alist work-hard-when-instructedp tag exhaustivep limits state)
    (if erp
        (mv erp nil nil state)
      (if (or (not simplify-xorsp) ;; if we are told to not simplify xors, we are done (TODO: Not necessarily!  make sure no change (except differences in node numbering - make a wrapper of simplify-dag that does that)
              (quotep simplified-dag-or-quotep) ;if we reduced it to a constant we are done
              )
          (mv (erp-nil) simplified-dag-or-quotep limits state)
        ;; Otherwise, we are to normalize xors, so do that and simplify alternately until things are stable:
        (normalize-xors-and-simplify-until-stable simplified-dag-or-quotep
                                                  rewriter-rule-alist slack-amount refined-assumption-alist equality-assumption-alist print-interval
                                                  print interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                                                  context-array-name
                                                  context-array
                                                  context ;(list of items of the form <nodenum> or (not <nodenum>)
                                                  context-array-len context-parent-array-name context-parent-array
                                                  context-dag-constant-alist context-dag-variable-alist
                                                  work-hard-when-instructedp tag exhaustivep limits state)))))

;; is it okay for dag to have irrelevant nodes?
;; or have the same expression at two different nodenums?
;; can the numbering have gaps?  be out of order?
;; Returns (mv erp simplified-dag-or-quotep limits state) where simplified-dag-or-quotep is equivalent to dag, given the assumptions (fixme what exactly is the story with ifns?).
;;change this to print out the list of rules all at once?
(defun simplify-with-rule-sets-aux (dag ;; must not be a quotep
                                    tagged-rule-sets ;; the tag of each rule set indicates whether it's a list of rules or a rule-alist
                                    slack-amount simplify-xorsp
                                    refined-assumption-alist ;mentions nodenums in the context-array
                                    equality-assumption-alist ; use the context array for this?
                                    print-interval print
                                    priorities ;ignored for rule-alists
                                    interpreted-function-alist monitored-symbols remove-duplicate-rulesp memoizep use-internal-contextsp
                                    rule-set-number total-rule-set-count
                                    context-array-name
                                    context-array
                                    context ;(list of items of the form <nodenum> or (not <nodenum>)
                                    context-array-len context-parent-array-name context-parent-array
                                    context-dag-constant-alist context-dag-variable-alist
                                    work-hard-when-instructedp tag exhaustivep limits state)
  (declare (xargs :mode :program :stobjs state
                  :measure (len tagged-rule-sets)
                  :guard (and (tagged-rule-setsp tagged-rule-sets)
                              ;;guard for equality-assumption-alist?
                              (rationalp total-rule-set-count)
                              (acl2-numberp rule-set-number)
                              (alistp priorities)
                              (rule-limitsp limits))))
  (if (endp tagged-rule-sets)
      (mv (erp-nil) dag limits state)
    (b* ((- (and (> total-rule-set-count 1) (cw "(Applying rule set ~x0 of ~x1.~%" rule-set-number total-rule-set-count)))
         (tagged-rule-set (first tagged-rule-sets))
         (rule-set-tag (car tagged-rule-set))
         (item (cdr tagged-rule-set))
         ((mv erp rule-alist)
          (if (eq :rule-names rule-set-tag)
              ;;todo: do better here?
              (b* (((mv erp axe-rules)
                    (make-axe-rules item (w state)))
                   ((when erp) (mv erp nil)))
                (mv (erp-nil) (make-rule-alist-simple axe-rules remove-duplicate-rulesp priorities)))
            (if (eq :rules rule-set-tag) ;todo: deprecate this case
                (mv (erp-nil) (make-rule-alist-simple item remove-duplicate-rulesp priorities))
              (if (eq :rule-alist rule-set-tag)
                  (mv (erp-nil) item)
                (prog2$ (er hard? 'simplify-with-rule-sets-aux "Unknown tag!  tagged-rule-set: ~x0" tagged-rule-set)
                        (mv :unknown-tag nil))))))
         ((when erp) (mv erp nil nil state))
         (- (print-missing-rules monitored-symbols rule-alist)) ;todo: think about where to put this printing
         )
      (mv-let (erp dag-or-quotep limits state)
        ;;apply the first rule set:
        (simplify-and-normalize-xors-until-stable dag
                                                     rule-alist
                                                     slack-amount simplify-xorsp refined-assumption-alist equality-assumption-alist
                                                     print-interval print interpreted-function-alist monitored-symbols memoizep use-internal-contextsp
                                                     context-array-name
                                                     context-array
                                                     context
                                                     context-array-len context-parent-array-name context-parent-array
                                                     context-dag-constant-alist context-dag-variable-alist
                                                     work-hard-when-instructedp tag exhaustivep limits state)
        (if erp
            (mv erp nil nil state)
          (prog2$ (and (> total-rule-set-count 1) (cw ")~%"))
                  (if (quotep dag-or-quotep)
                      (mv (erp-nil) dag-or-quotep limits state)
                    (prog2$ (and (member-eq print '(t :verbose :verbose2))
                                 (print-list dag-or-quotep))
                            ;;apply the rest of the rule sets:
                            (simplify-with-rule-sets-aux dag-or-quotep (rest tagged-rule-sets) slack-amount simplify-xorsp refined-assumption-alist equality-assumption-alist
                                                         print-interval print priorities
                                                         interpreted-function-alist monitored-symbols remove-duplicate-rulesp memoizep use-internal-contextsp
                                                         (+ 1 rule-set-number) total-rule-set-count
                                                         context-array-name context-array context context-array-len context-parent-array-name context-parent-array
                                                         context-dag-constant-alist context-dag-variable-alist
                                                         work-hard-when-instructedp tag exhaustivep limits state)))))))))

;; Simplifies the given DAG to produce a new DAG. This function is the main
;; entry point for the Axe rewriter (all the wrapper macros should call this
;; function).  Returns (mv erp simplified-dag-or-quotep state) where simplified-dag-or-quotep is
;; equivalent to dag-or-quotep, given the assumptions (how do the ifns play
;; into the logical story?).  no longer smashes context-array.  This version
;; takes its rules as a list of tagged-rule-sets.
(defun simplify-with-rule-sets (dag-or-quotep
                                tagged-rule-sets ;the tag of each rule set indicates whether it is a list of rules or a rule-alist
                                slack-amount
                                simplify-xorsp
                                assumptions ;terms to be assumed non-nil (probably share most vars with the dag but may contain new vars?) - merge the handling of this with the context-array?
                                print-interval
                                print
                                priorities ;the priorities to use, or :default, ignored for rule-alists ;todo: drop this arg?
                                interpreted-function-alist
                                monitored-symbols
                                remove-duplicate-rulesp
                                memoizep
                                use-internal-contextsp
                                ;; The context represents global assumptions to be assumed when rewriting all nodes.
                                ;; fixme rename to something other than "context"?
                                ;; CONTEXT mentions nodenums in CONTEXT-ARRAY, whose name is CONTEXT-ARRAY-NAME.  The variables in CONTEXT-ARRAY have the same meanings as vars with the
                                ;; same names in DAG.  We use a dag representation because the context terms might be big.  Currently, the context is rarely used.
                                context-array-name ; meaningful iff context is non-nil
                                context-array ; meaningful iff context is non-nil
                                context ;a possibly-negated-nodenumsp (nil means "true" context) over nodes in context-array; fixme can these be the nodenums of constants?!
                                ;; fixme refine the context entries for matching?!?
                                ;; fixme what if the context is contradictory?
                                context-array-len ; meaningful iff context is non-nil
                                work-hard-when-instructedp
                                tag
                                exhaustivep
                                limits
                                state)
  (declare (xargs :guard (and (or (pseudo-dagp dag-or-quotep)
                                  (myquotep dag-or-quotep))
                              (tagged-rule-setsp tagged-rule-sets)
                              (natp slack-amount)
                              (booleanp simplify-xorsp)
                              (pseudo-term-listp assumptions)
                              (or (eq :default priorities)
                                  (alistp priorities))
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitored-symbols)
                              (booleanp remove-duplicate-rulesp)
                              (booleanp memoizep)
                              (booleanp use-internal-contextsp)
                              (symbolp context-array-name)
                              ;; context-array
                              (possibly-negated-nodenumsp context)
                              (if context (natp context-array-len) t)
                              (booleanp work-hard-when-instructedp)
                              (symbolp tag)
                              (booleanp exhaustivep)
                              (rule-limitsp limits))
                  :mode :program ; because of termination of the main mut-rec (and perhaps also guards)
                  :stobjs state))
  (if (quotep dag-or-quotep) ;todo: may be impossible now
      (prog2$ (and print (cw "(Simplifying: Already a constant.)~%"))
              (mv (erp-nil) dag-or-quotep state))
    (b* ((- (and print (cw "(Simplifying:~%")))
         (assumptions (get-conjuncts-list assumptions))
         (equality-assumption-alist (make-equality-assumption-alist assumptions (w state)))
         (refined-assumptions (refine-assumptions-for-matching assumptions (known-booleans (w state)) nil)) ;terms (known to be function calls)
         ;; copy context-array to new-context-array (fixme abstract out the array copying pattern)
         (new-context-array-name 'context-array-for-simplify-with-rule-sets) ;will there ever be several of these nested?
         (new-context-array-len (if context context-array-len 0))
         (new-context-array (make-empty-array new-context-array-name (max 1 (+ new-context-array-len slack-amount)))) ;the max is new
         (new-context-array (if (and context ;skip the test and just pass -1 to copy-array-vals?
                                     ;;(not (eql 0 context-array-len)) ;do we need this?
                                     )
                                ;; preserves nodenums, so we don't have to fix up the context (but what if not all these nodes are needed?)
                                (copy-array-vals (+ -1 new-context-array-len) context-array-name context-array new-context-array-name new-context-array)
                              new-context-array ;the new, empty array
                              ))
         (new-context-parent-array-name 'context-parent-array-for-simplify-with-rule-sets) ;will there ever be several of these nested? tag with the depth?
         ((mv new-context-parent-array new-context-dag-constant-alist new-context-dag-variable-alist) ;make sure this works if the array is empty
          (make-dag-indices new-context-array-name new-context-array new-context-parent-array-name
                            new-context-array-len)
          )
         ;;for each refined assumption, add its args to the context array and fixup the refined assumption
         ;; this is where the new-context-array gets smashed!:
         ;;fixme do something similar with the equality pairs?!
         ((mv erp refined-assumption-exprs ;fn calls applied to quoteps/nodenums in context-array
              new-context-array new-context-array-len new-context-parent-array new-context-dag-constant-alist new-context-dag-variable-alist)
          (add-refined-assumptions-to-dag-array refined-assumptions
                                                new-context-array new-context-array-len new-context-parent-array new-context-dag-constant-alist new-context-dag-variable-alist
                                                new-context-array-name
                                                new-context-parent-array-name
                                                nil))
         ((when erp) (mv erp nil state))
         (refined-assumption-alist (make-refined-assumption-alist refined-assumption-exprs)) ;the nodenums mentioned are in the new-context-array!
         (- (and monitored-symbols (cw "(Monitoring: ~x0)~%" monitored-symbols))) ;move this?
         (priorities (if (eq :default priorities)
                         (table-alist 'axe-rule-priorities-table (w state))
                       priorities))
         ((mv erp
              dag-or-quotep
              & ;limits
              state)
          (simplify-with-rule-sets-aux dag-or-quotep
                                       tagged-rule-sets slack-amount simplify-xorsp refined-assumption-alist equality-assumption-alist print-interval print priorities
                                       interpreted-function-alist monitored-symbols remove-duplicate-rulesp memoizep use-internal-contextsp
                                       1 ;;rule-set-number; starts at 1 (saying rule set "0 of 3" looked odd)
                                       (len tagged-rule-sets)
                                       new-context-array-name
                                       new-context-array
                                       context ;okay since the nodes in the new context are the same as those in the old context
                                       new-context-array-len
                                       new-context-parent-array-name new-context-parent-array new-context-dag-constant-alist new-context-dag-variable-alist
                                       work-hard-when-instructedp tag exhaustivep limits state))
         ((when erp) (mv erp nil state))
         (- (and print (cw ")~%"))) ;matches "(Simplifying ..."
         )
      (mv (erp-nil) dag-or-quotep state))))

;;;
;;; simp-dag
;;;

;; Returns (mv erp simplified-dag-or-quotep state).  Smashes the context-array?
;; When simp-dag is called by the user, we should check all the inputs.  When
;; simp-dag is called from our code, we can set :check-inputs to nil to avoid
;; the checks (in which case, the guard requires the checks to hold).
(defun simp-dag-fn (dag-or-quotep
                    rules
                    rule-alist
                    rule-alists
                    slack-amount
                    simplify-xorsp
                    assumptions
                    print-interval
                    print
                    interpreted-function-alist
                    monitored-symbols
                    remove-duplicate-rulesp
                    memoizep
                    use-internal-contextsp
                    context-array-name
                    context-array
                    context
                    context-array-len
                    work-hard-when-instructedp
                    tag
                    exhaustivep
                    limits
                    check-inputs
                    state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and (booleanp check-inputs)
                              (if check-inputs
                                  t ;; everything should be checked in the body (todo: add the checks)
                                (and (pseudo-term-listp assumptions)
                                     (or (eq :none rules) (symbol-listp rules))
                                     (or (eq :none rule-alist) (rule-alistp rule-alist))
                                     (or (eq :none rule-alists) (and (true-listp rule-alists)
                                                                     (all-rule-alistp rule-alists)))
                                     ;;todo: add more checks
                                     (rule-limitsp limits)
                                     )))))
  (b* (;; Check inputs if instructed:
       ((when (and check-inputs
                   (not (ensure-rules-etc-ok 'simp-dag-fn rules rule-alist rule-alists))))
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (pseudo-term-listp assumptions))))
        (er hard? 'simp-dag-fn "Bad assumptions (must be a list of pseudo-terms): ~x0." assumptions)
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (rule-limitsp limits))))
        (er hard? 'simp-dag-fn "Bad rule limits: ~x0." limits)
        (mv :bad-input nil state))
       ;; TODO: Check more inputs here, if check-inputs is true

       ((when (quotep dag-or-quotep))
        (mv (erp-nil) dag-or-quotep state))
       ;; ((when (and check-aritiesp
       ;;             (not (arities-okayp term state))))
       ;;  (er hard? 'simp-dag-fn "Arities check failed for term ~x0" term)
       ;;  (mv t nil state))
       ((mv erp tagged-rule-sets) (make-tagged-rule-sets rules rule-alist rule-alists))
       ((when erp) (mv erp nil state))
       (slack-amount (if (quotep dag-or-quotep) ;think about this
                         0
                       (if slack-amount
                           slack-amount
                         (* 10 (len dag-or-quotep))))))
    (simplify-with-rule-sets dag-or-quotep
                             tagged-rule-sets
                             slack-amount
                             simplify-xorsp
                             assumptions
                             print-interval
                             print
                             :default
                             interpreted-function-alist
                             monitored-symbols
                             remove-duplicate-rulesp
                             memoizep
                             use-internal-contextsp
                             context-array-name
                             context-array
                             context
                             context-array-len
                             work-hard-when-instructedp
                             tag
                             exhaustivep
                             limits
                             state)))

;; Returns (mv erp simplified-dag-or-quotep state).
(defmacro simp-dag (dag-or-quotep
                    &KEY
                    (rules ':none)
                    (rule-alist ':none)
                    (rule-alists ':none)
                    (slack-amount '100) ;(slack-amount '1048576) ;must be at least 1048576 (only because we don't pass it into the memoization stuff now...) - can't the memo size be smaller? <-- old comment?
                    (simplify-xorsp 't)
                    (assumptions 'nil)
                    (print-interval 'nil)
                    (print 'nil)
                    (interpreted-function-alist 'nil)
                    (monitor 'nil)
                    (remove-duplicate-rulesp 't)
                    (memoizep 't)
                    (use-internal-contextsp 'nil) ;should t be the default instead?
                    (context-array-name 'nil)
                    (context-array 'nil)
                    (context 'nil) ;(list of items of the form <nodenum> or (not <nodenum>)
                    (context-array-len 'nil)
                    (work-hard-when-instructedp 't)
                    (tag ''unknown)
                    (exhaustivep 'nil) ;TODO: deprecate once issues with loops (due to nodenum comparisons) are worked out
                    (limits 'nil)
                    (check-inputs 't))
  `(simp-dag-fn ,dag-or-quotep
                ,rules
                ,rule-alist
                ,rule-alists
                ,slack-amount
                ,simplify-xorsp
                ,assumptions
                ,print-interval
                ,print
                ,interpreted-function-alist
                ,monitor
                ,remove-duplicate-rulesp
                ,memoizep
                ,use-internal-contextsp
                ,context-array-name
                ,context-array
                ,context
                ,context-array-len
                ,work-hard-when-instructedp
                ,tag
                ,exhaustivep
                ,limits
                ,check-inputs
                state))

;;;
;;; simp-term
;;;

;; Simplify TERM to produce an equivalent dag. Returns (mv erp simplified-dag-or-quotep state).
(defun simp-term-fn (term
                     rules
                     rule-alist
                     rule-alists
                     slack-amount
                     simplify-xorsp
                     assumptions
                     print-interval
                     print
                     interpreted-function-alist
                     monitored-symbols
                     remove-duplicate-rulesp
                     memoizep
                     use-internal-contextsp
                     context-array-name
                     context-array
                     context
                     context-array-len
                     work-hard-when-instructedp
                     tag
                     exhaustivep
                     limits
                     check-inputs ;suggest using this when called on a term from the user ;;todo: generalize to check-inputs
                     state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (if check-inputs
                             t
                           (and (pseudo-termp term)
                                (pseudo-term-listp assumptions)
                                ;; todo: add more
                                (interpreted-function-alistp interpreted-function-alist)
                                (booleanp memoizep)
                                (booleanp use-internal-contextsp)
                                (booleanp check-inputs)
                                (rule-limitsp limits)))))
  (b* (;; Check inputs if instructed:
       ((when (and check-inputs
                   (not (ensure-rules-etc-ok 'simp-term-fn rules rule-alist rule-alists))))
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (pseudo-term-listp assumptions))))
        (er hard? 'simp-term-fn "Bad assumptions (must be a list of pseudo-terms): ~x0." assumptions)
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (rule-limitsp limits))))
        (er hard? 'simp-term-fn "Bad rule limits: ~x0." limits)
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (pseudo-termp term))))
        (er hard? 'simp-term-fn "The value supplied, ~x0, is not a pseudo-term" term)
        (mv (erp-t) nil state))
       ((when (and check-inputs
                   (not (arities-okayp term state))))
        (er hard? 'simp-term-fn "Arities check failed for term ~x0" term)
        (mv (erp-t) nil state))
       ;; TODO: Check more inputs here, if check-inputs is true

       ;; Handle the case of term already a constant:
       ((when (quotep term))
        (mv (erp-nil) term state))

       ((mv erp tagged-rule-sets) (make-tagged-rule-sets rules rule-alist rule-alists))
       ((when erp) (mv erp nil state))

       ;; TODO: Perhaps return the auxiliary data structures for the dag.  Or
       ;; directly call the rewriter function that takes a term (then
       ;; repeatedly simplify and normalize xors).
       ((mv erp dag-or-quotep) (make-term-into-dag term interpreted-function-alist)) ;does/should this evaluate ground terms?
       ((when erp) (mv erp nil state))
       ;; Maybe not possible since we check above that TERM is not a quotep:
       ((when (quotep dag-or-quotep))
        (mv (erp-nil) dag-or-quotep state))
       )
    (simplify-with-rule-sets dag-or-quotep
                             tagged-rule-sets
                             slack-amount
                             simplify-xorsp
                             assumptions
                             print-interval
                             print
                             :default
                             interpreted-function-alist
                             monitored-symbols
                             remove-duplicate-rulesp
                             memoizep
                             use-internal-contextsp
                             context-array-name
                             context-array
                             context
                             context-array-len
                             work-hard-when-instructedp
                             tag
                             exhaustivep
                             limits
                             state)))


;; This is the main user-level function to simplify a term.  Returns (mv erp
;; simplified-dag-or-quotep state).  This can return an error if the simplified term is
;; too big to be a DAG.  Note: The name simplify-term is already used by the
;; simplify transformation, so we don't use that name for this function.
(defmacro simp-term (term
                     &KEY
                     (rules ':none)
                     (rule-alist ':none)
                     (rule-alists ':none)
                     (slack-amount '100) ;(slack-amount '1048576) ;fffixme too big?!
                     (simplify-xorsp 't)
                     (assumptions 'nil)
                     (print-interval 'nil)
                     (print 'nil)
                     (interpreted-function-alist 'nil)
                     (monitor 'nil)
                     (remove-duplicate-rulesp 't)
                     (memoizep 't)
                     (use-internal-contextsp 'nil) ;should t be the default instead?
                     (context-array-name 'nil)
                     (context-array 'nil)
                     (context 'nil) ;(list of items of the form <nodenum> or (not <nodenum>)
                     (context-array-len 'nil)
                     (work-hard-when-instructedp 't)
                     (tag ''unknown)
                     (exhaustivep 'nil) ;TODO: deprecate once issues with loops (due to nodenum comparisons) are worked out
                     (limits 'nil)
                     (check-inputs 't) ;todo: pass nil when calling from trusted code
                     )
  `(simp-term-fn ,term
                 ,rules
                 ,rule-alist
                 ,rule-alists
                 ,slack-amount ,simplify-xorsp ,assumptions ,print-interval ,print
                 ,interpreted-function-alist
                 ,monitor
                 ,remove-duplicate-rulesp
                 ,memoizep
                 ,use-internal-contextsp
                 ,context-array-name
                 ,context-array
                 ,context ;(list of items of the form <nodenum> or (not <nodenum>)
                 ,context-array-len
                 ,work-hard-when-instructedp
                 ,tag ,exhaustivep ,limits ,check-inputs state))

;; It can happen that the rewriter and simplify xors repeatedly
;; interconvert between equivalent but not equal dags.  One might think that
;; after simplify-xors, if no rules apply, the rewriter should return the
;; dag unchanged.  but nodes may be reordered (high nodes may be placed at
;; lower numbers because they happen to equal low nodes created when rewriting
;; hyps on behalf of rewrites for lower terms).

;move all this up:

;; ;; Returns (mv erp new-terms state).
;; (defun simplify-terms-to-new-terms-aux (terms rule-alist monitored-rules state)
;;   (declare (xargs :stobjs state
;;                   :guard (and (pseudo-term-listp terms)
;;                               (rule-alistp rule-alist)
;;                               (symbol-listp monitored-rules))
;;                   :mode :program))
;;   (if (endp terms)
;;       (mv nil nil state)
;;     (b* ((term (first terms))
;;          ((mv erp dag state)
;;           (simp-term term :rule-alist rule-alist
;;                      :monitor monitored-rules
;;                      :print (if monitored-rules t nil)))
;;          ((when erp) (mv erp nil state))
;;          (new-term (dag-to-term dag))
;;          ((mv erp new-terms state)
;;           (simplify-terms-to-new-terms-aux (rest terms) rule-alist monitored-rules state))
;;          ((when erp) (mv erp nil state)))
;;       (mv nil (cons new-term new-terms) state))))

;; ;; Returns (mv erp new-terms state).
;; (defun simplify-terms-to-new-terms-fn (terms rule-alist monitored-rules state)
;;   (declare (xargs :stobjs state
;;                   :guard (rule-alistp rule-alist)
;;                   :mode :program))
;;   (b* (((when (not (symbol-listp monitored-rules)))
;;         (mv t
;;             (er hard 'simplify-terms-to-new-terms-fn "Monitored rules must be a list of symbols, but we got: ~x0." monitored-rules)
;;             state))
;;        (terms (translate-terms terms 'simplify-terms-to-new-terms (w state))))
;;   (simplify-terms-to-new-terms-aux terms rule-alist monitored-rules state)))


;; ;; The awkward name indicates that the results are not DAGs.  Returns (mv
;; ;; erp new-terms state).  We could add various rewriter options
;; ;; to this as needed.  In theory, this could blow up since it converts DAGs to
;; ;; terms.
;; (defmacro simplify-terms-to-new-terms (terms rule-alist &key (monitor 'nil))
;;   `(simplify-terms-to-new-terms-fn ,terms ,rule-alist ,monitor state))


;;Returns (mv erp old-term new-term state) where old-term is nil if nothing simplified.
(defun find-a-term-to-simplify (terms-to-simplify rule-alist monitored-rules all-terms state)
  (declare (xargs :mode :program :stobjs state))
  (if (endp terms-to-simplify)
      (mv nil nil nil state) ;failed to simplify anything
    (let ((term (first terms-to-simplify)))
      (mv-let (erp result-dag state)
        ;; could instead to rewrite-term...
        (simp-term term :rule-alist rule-alist
                   :assumptions (remove-equal term all-terms) ;don't use the term to simplify itself!
                   :monitor monitored-rules)
        (if erp
            (mv erp nil nil state)
          (let ((result-term (dag-to-term result-dag))) ;fixme could this ever blow up?
            (if (equal result-term term)
                ;;no change, so keep looking
                (find-a-term-to-simplify (rest terms-to-simplify) rule-alist monitored-rules all-terms state)
              ;;term was simplified, so stop this pass:
              (mv nil term result-term state))))))))

;fixme compare to improve-invars
;fixme handle boolands?
;; Returns (mv erp new-terms state) where new-terms is a set of terms whose conjunction is equal to the conjunction of terms.
(defun simplify-terms (terms ;hyps
                       ;;print
                       rule-alist
                       monitored-rules
                       state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp old-term new-term state)
    (find-a-term-to-simplify terms rule-alist monitored-rules terms state)
    (if erp
        (mv erp nil state)
      (if (not old-term)
          ;; Nothing more could be done:
          (mv nil terms state)
        (if (equal *t* new-term) ;todo: also check for *nil*?
            ;; if the term became t, drop it and start again (this can happen if there is redundancy between the terms)
            (simplify-terms (remove-equal old-term terms) rule-alist monitored-rules state)
          (let ((conjuncts (get-conjuncts-of-term2 new-term))) ;flatten any conjunction returned (some conjuncts may be needed to simplify others)
            (simplify-terms (append conjuncts (remove-equal old-term terms)) rule-alist monitored-rules state)))))))

;; Simplify all the terms, which are implicitly conjoined, assuming all the
;; others (being careful not to let two terms each simplify the other to true).
;todo: maybe translate the terms
;; Returns (mv erp new-terms state).
(defun simplify-terms-using-each-other-fn (terms rule-alist monitored-rules state)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-rules)) ;todo: turn some of these into checks
                  :stobjs state
                  :mode :program))
  (let ((terms (get-conjuncts-of-terms2 terms))) ;start by flattening all conjunctions (all new conjunctions generated also get flattened)
    (simplify-terms terms rule-alist monitored-rules state)))

;; Returns (mv erp new-terms state).
(defmacro simplify-terms-using-each-other (terms rule-alist &key (monitor 'nil))
  `(simplify-terms-using-each-other-fn ,terms ,rule-alist ,monitor state))

;; todo: make these into proper tests:

;gives (Y (EQUAL X '3)):
;;(simplify-terms-using-each-other '((if (equal x '3) y z)  (equal x '3)) nil)

;; gives ('NIL (EQUAL X '4))
;;(simplify-terms-using-each-other '((equal (car (cons x y)) '3) (equal x '4)) (make-axe-rules '(car-cons) (w state)))

;; (defun foo (x) x)
;; ;gives (W (EQUAL X '3) Y)
;; ; foo opens, then the result is flattened, giving conjuncts of (equal x '3) and y, then (equal x '3) is used to simplify (if (equal x '3) w v)
;; (simplify-terms-using-each-other '((foo (if (equal x '3) y 'nil)) (if (equal x '3) w v)) (make-axe-rules '(foo) (w state)))

;; This version translates the term it is given
;; Returns (mv erp dag).
(defun compose-term-and-dag2 (term var-to-replace dag wrld)
  (declare (xargs :mode :program))
  (let ((term (translate-term term 'compose-term-and-dag2 wrld)))
    (compose-term-and-dag term var-to-replace dag)))

;;;
;;; quick-simp-dag
;;;

;; Returns (mv erp simplified-dag-or-quotep state).
(defun quick-simp-dag-fn (dag-or-quotep
                          rules
                          rule-alist
                          rule-alists
                          slack-amount
                          simplify-xorsp
                          assumptions
                          print-interval
                          print
                          interpreted-function-alist
                          monitored-symbols
                          remove-duplicate-rulesp
                          memoizep
                          use-internal-contextsp
                          context-array-name
                          context-array
                          context
                          context-array-len
                          work-hard-when-instructedp
                          tag
                          exhaustivep
                          limits
                          check-inputs
                          state)
  (declare (xargs :mode :program
                  :stobjs state
                  ;; TODO: Guard
                  ))
  (b* (;; Check inputs if instructed:
       ((when (and check-inputs
                   (not (ensure-rules-etc-ok 'quick-simp-dag-fn rules rule-alist rule-alists))))
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (pseudo-term-listp assumptions))))
        (er hard? 'quick-simp-dag-fn "Bad assumptions (must be a list of pseudo-terms): ~x0." assumptions)
        (mv :bad-input nil state))
       ((when (and check-inputs
                   (not (rule-limitsp limits))))
        (er hard? 'quick-simp-dag-fn "Bad rule limits: ~x0." limits)
        (mv :bad-input nil state))
       ;; TODO: Check more inputs here, if check-inputs is true

       ((when (quotep dag-or-quotep))
        (mv (erp-nil) dag-or-quotep state))
       ((mv erp tagged-rule-sets) (make-tagged-rule-sets rules rule-alist rule-alists))
       ((when erp) (mv erp nil state))
       ;; ((when (and check-aritiesp
       ;;             (not (arities-okayp term state))))
       ;;  (er hard? 'quick-simp-dag-fn "Arities check failed for term ~x0" term)
       ;;  (mv t nil state))
       ((when (not (pseudo-term-listp assumptions)))
        (mv (erp-t)
            (er hard? 'quick-simp-dag "The assumptions argument must be a list of pseudo-terms, but we got ~X01" assumptions nil)
            state)))
    (simplify-with-rule-sets dag-or-quotep
                             tagged-rule-sets
                             (if (quotep dag-or-quotep) 0 (if slack-amount slack-amount (* 10 (len dag-or-quotep)))) ;think about this
                             simplify-xorsp
                             assumptions
                             print-interval
                             print
                             :default
                             interpreted-function-alist
                             monitored-symbols
                             remove-duplicate-rulesp
                             memoizep
                             use-internal-contextsp
                             context-array-name
                             context-array
                             context
                             context-array-len
                             work-hard-when-instructedp
                             tag
                             exhaustivep
                             limits
                             state)))

;; Returns (mv erp simplified-dag-or-quotep state).  This one does not simplify xors, uses a
;; slack-amount of nil, does not memoize, and doesn't have any of the context
;; stuff.
(defmacro quick-simp-dag (dag-or-quotep
                          &KEY
                          (rules ':none)
                          (rule-alist ':none)
                          (rule-alists ':none)
                          (slack-amount 'nil) ;fixme think about this limit
                          (simplify-xorsp 'nil)
                          (assumptions 'nil)
                          (print-interval 'nil)
                          (print 'nil)
                          (interpreted-function-alist 'nil)
                          (monitor 'nil)
                          (remove-duplicate-rulesp 't)
                          (memoizep 'nil)
                          ;; use-internal-contextsp
                          ;; context-array-name
                          ;; context-array
                          ;; context
                          ;; context-array-len
                          (work-hard-when-instructedp 't)
                          (tag ''unknown)
                          (exhaustivep 'nil)
                          (limits 'nil)
                          (check-inputs 't))
  `(quick-simp-dag-fn ,dag-or-quotep
                      ,rules
                      ,rule-alist
                      ,rule-alists
                      ,slack-amount
                      ,simplify-xorsp
                      ,assumptions
                      ,print-interval
                      ,print
                      ,interpreted-function-alist
                      ,monitor
                      ,remove-duplicate-rulesp
                      ,memoizep
                      nil ;;use-internal-contextsp
                      nil ;;context-array-name
                      nil ;;context-array
                      nil ;;context
                      nil ;; context-array-len
                      ,work-hard-when-instructedp
                      ,tag
                      ,exhaustivep
                      ,limits
                      ,check-inputs
                      state))

;;;
;;; quick-simp-composed-term-and-dag
;;;

;; Returns (mv erp simplified-dag-or-quotep state).
(defun quick-simp-composed-term-and-dag-fn (term
                                            var-to-replace
                                            dag
                                            rules
                                            rule-alist
                                            rule-alists
                                            slack-amount
                                            simplify-xorsp
                                            assumptions
                                            print-interval
                                            print
                                            interpreted-function-alist
                                            monitored-symbols
                                            remove-duplicate-rulesp
                                            memoizep
                                            use-internal-contextsp
                                            context-array-name
                                            context-array
                                            context
                                            context-array-len
                                            work-hard-when-instructedp
                                            tag
                                            exhaustivep
                                            limits
                                            check-inputs
                                            state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((mv erp dag)
        (compose-term-and-dag term var-to-replace dag))
       ((when erp) (mv erp nil state)))
    (quick-simp-dag-fn dag
                       rules
                       rule-alist
                       rule-alists
                       slack-amount
                       simplify-xorsp
                       assumptions
                       print-interval
                       print
                       interpreted-function-alist
                       monitored-symbols
                       remove-duplicate-rulesp
                       memoizep
                       use-internal-contextsp
                       context-array-name
                       context-array
                       context
                       context-array-len
                       work-hard-when-instructedp
                       tag
                       exhaustivep
                       limits
                       check-inputs
                       state)))

;; Returns (mv erp simplified-dag-or-quotep state).
(defmacro quick-simp-composed-term-and-dag (term
                                            var-to-replace
                                            dag
                                            &KEY
                                            (rules ':none)
                                            (rule-alist ':none)
                                            (rule-alists ':none)
                                            (slack-amount 'nil) ;fixme think about this limit
                                            (simplify-xorsp 'nil)
                                            (assumptions 'nil)
                                            (print-interval 'nil)
                                            (print 'nil)
                                            (interpreted-function-alist 'nil)
                                            (monitor 'nil)
                                            (remove-duplicate-rulesp 't)
                                            (memoizep 'nil)
                                            ;; use-internal-contextsp
                                            ;; context-array-name
                                            ;; context-array
                                            ;; context
                                            ;; context-array-len
                                            (work-hard-when-instructedp 't)
                                            (tag ''unknown)
                                            (exhaustivep 'nil)
                                            (limits 'nil)
                                            (check-inputs 't))
  `(quick-simp-composed-term-and-dag-fn ,term
                                        ,var-to-replace
                                        ,dag
                                        ,rules
                                        ,rule-alist
                                        ,rule-alists
                                        ,slack-amount
                                        ,simplify-xorsp
                                        ,assumptions
                                        ,print-interval
                                        ,print
                                        ,interpreted-function-alist
                                        ,monitor
                                        ,remove-duplicate-rulesp
                                        ,memoizep
                                        nil ;;use-internal-contextsp
                                        nil ;;context-array-name
                                        nil ;;context-array
                                        nil ;;context
                                        nil ;; context-array-len
                                        ,work-hard-when-instructedp
                                        ,tag
                                        ,exhaustivep
                                        ,limits
                                        ,check-inputs
                                        state))
