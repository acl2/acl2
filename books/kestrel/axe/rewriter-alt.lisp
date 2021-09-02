; Another Axe Rewriter (not used much yet)
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

;; Instead of this rewriter, consider using rewriter-basic or rewriter-jvm or
;; another newer rewriter.

(include-book "kestrel/axe/rewriter-common" :dir :system)
(include-book "kestrel/axe/equality-pairs" :dir :system)
;(include-book "kestrel/axe/equality-assumptions" :dir :system)
(include-book "kestrel/axe/refined-assumption-alists" :dir :system)
(include-book "kestrel/axe/result-array-stobj" :dir :system)
(include-book "kestrel/axe/prover" :dir :system)
(include-book "kestrel/axe/simplify-xors" :dir :system)
(include-book "kestrel/axe/leaves-of-normalized-bvxor-nest" :dir :system)
(include-book "kestrel/axe/if-rules" :dir :system)
(include-book "kestrel/axe/defconst-computed2" :dir :system) ;not strictly needed
(include-book "kestrel/utilities/pseudo-termp" :dir :system) ; make local
(include-book "kestrel/axe/rule-lists" :dir :system) ;todo: just for lookup-rules (can we do without that? - try to avoid using make-var-lookup-terms -- instead require the nested DAG alist to have a certain form and just do the lookup).
(include-book "kestrel/axe/jvm/axe-syntaxp-evaluator-jvm" :dir :system)
(include-book "kestrel/axe/jvm/axe-bind-free-evaluator-jvm" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable default-car
                           default-cdr
                           ;list::nth-with-large-index
                           ;list::nth-with-large-index-2
                           ;cdr-non-nil
                           ;nth1-when-not-cdr
                           ;consp-from-len-cheap
                           ;iff-of-member-equal ;rename
                           ;list::member-eq-is-memberp-propositionally ;same as iff-of-member-equal?
                           ;memberp-nth-when-perm ;yuck!
                           all-consp-when-not-consp ;yuck!
                           ;list::nth-when-l-is-not-a-consp
                           ;list::len-when-consp-linear
                           )))

;objective is t, nil, or ?
(defmacro flip-objective (objective)
  `(if (eq t ,objective)
       nil
     (if (eq nil ,objective)
         t
       ,objective)))

;checks whether all vars in term appear as keys in alist
;fixme maybe this handles (complete) lambdas naturally?
(defun any-free-varsp (term alist lst-flg)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (if lst-flg
                                  (pseudo-term-listp term)
                                (pseudo-termp term)))))
  (if lst-flg
      (if (endp term)
          nil
        (or (any-free-varsp (first term) alist nil)
            (any-free-varsp (rest term) alist t)))
    ;;non-list case:
    (if (atom term)
        (not (assoc-eq term alist))
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            nil
          (any-free-varsp (fargs term) alist t))))))

(local (in-theory (enable pseudo-termp-of-car-of-car-when-equality-pairsp)))

;call merge-term... instead of merge-tree... here if appropriate
;fixme how are we going to ensure that using equalities doesn't cause loops? e.g., when using context assumptions to prove a merge?
;; Returns (mv erp equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; only used by the new rewriter.
(defun populate-equality-array (equality-pairs equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (equality-pairsp equality-pairs)
                              (array1p 'equality-array equality-array)
                              ;; (equal (alen1 'equality-array equality-array)
                              ;;        dag-len)
                              )
                  :guard-hints (("Goal" :in-theory (enable equality-pairsp)))))
  (if (endp equality-pairs)
      (mv (erp-nil) equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((pair (first equality-pairs))
           (lhs-term (car pair))
           (rhs-term (cdr pair)))
      (mv-let (erp lhs-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (merge-tree-into-dag-array lhs-term nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                   nil ;fixme interpreted-function-alist
                                   )
        (if erp
            (mv erp equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (if (consp lhs-nodenum-or-quotep)
              (prog2$ (hard-error 'populate-equality-array "equality assumption with constant lhs" nil)
                      (mv (erp-t) equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
            ;;it's a nodenum
            (mv-let (erp rhs-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (merge-tree-into-dag-array rhs-term nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                         nil ;fixme interpreted-function-alist
                                         )
              (if erp
                  (mv erp equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (populate-equality-array (rest equality-pairs)
                                         (aset1-expandable 'equality-array equality-array lhs-nodenum-or-quotep rhs-nodenum-or-quotep)
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))))))

;;each stack entry is either <nodenum> or (<nodenum> . <t-or-nil-rewrite-objective>)
;;the former indicates a rewrite-objective of '?

(defmacro push-stack-entry (nodenum rewrite-objective stack)
  `(if (eq '? ,rewrite-objective)
       (cons ,nodenum ,stack)
     ;;rewrite-objective of t or nil:
     (cons (cons ,nodenum ,rewrite-objective) ,stack)))

(defmacro push-new-stack (nodenum rewrite-objective stacks)
  `(cons (push-stack-entry ,nodenum ,rewrite-objective nil ;empty stack
                          )
        ,stacks))

;; the rewriter uses a stack of stacks to track its work. each of the smaller
;; stacks represents one term to rewrite (the last node is the top node of that
;; term).  the stack may grow and shrink as child nodes are pushed and popped
;; each smaller stack is equal to the top node of the previous stack, so when a
;; rule is applied to the top node of the current stack (rewriting it to a new
;; term), a new stack is pushed and rewritten fully.  the result is the
;; rewritten version of the top node of the current stack ex: ((a b) (c d e) (f
;; g h)) means we are rewriting h but to do so we must rewrite its supporters f
;; and g.  a rule rewrote f to e, and to rewrite that we are writing its
;; supporters c and d.  a rule rewrote c to b, and to rewrite it we must rewrite
;; its supporter a

;; we can use equality assumptions by preloading information into the result array
;; the result array also captures the memoization
;; i guess when we match free vars using known assumptions the variables so introduced must be rewritten - maybe natural if they get used in further hyps or in the rhs?

;either returns nil (no args are untagged) or extends acc with the untagged args
;if any of the args are not rewritten yet, this returns an extended version of stack, else nil.
(defun get-args-to-simplify (args
                             arg-objectives ;;a list of objectives, or nil (meaning use '? for all)
                             stack
                             found-an-arg-to-rewritep
                             result-array-stobj)
  (declare (xargs :guard (and ;(array1p 'result-array result-array)
                          (true-listp args)
                          (true-listp arg-objectives)
                          (all-dargp-less-than
                           args ; (alen1 'result-array result-array)
                           (len (thearray-length result-array-stobj)) ;2147483646
                           ))
                  :stobjs result-array-stobj))
  (if (endp args)
      (if found-an-arg-to-rewritep
          stack
        nil)
    (let* ((arg (first args))
           (rewrite-objective (if arg-objectives (first arg-objectives) '?))
           )
      (if (or (consp arg) ;it's a quotep, so skip it
              (get-result ;-expandable
               arg rewrite-objective result-array-stobj) ;it's tagged as done, so skip it
              )
          (get-args-to-simplify (rest args) (rest arg-objectives) ;result-array
                                stack found-an-arg-to-rewritep result-array-stobj)
        ;; add an entry to the stack:
        (get-args-to-simplify (rest args) (rest arg-objectives) ;result-array
                              (push-stack-entry arg rewrite-objective stack)
                              t
                              result-array-stobj)))))

(local (in-theory (disable use-all-<-for-car
                           all-dargp-less-than-when-<-of-largest-non-quotep
                           ;;all-dargp-less-than-when-all-consp
                           )))

;drop some of this stuff?:

(set-case-split-limitations 'nil)
(set-case-split-limitations '(10 10))

(local (in-theory (disable  use-all-consp-for-car default-+-2 default-cdr
                           quote-lemma-for-all-dargp-less-than-gen-alt)))

(local (in-theory (disable symbol-alistp))) ;don't induct on this


;todo: remove this
(defun add-bvxor-nest-to-dag-array-ignore-errors (rev-leaves
                                                  size
                                                  quoted-size
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (add-bvxor-nest-to-dag-array rev-leaves
                                 size
                                 quoted-size
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
    (declare (ignore erp))
    (mv nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

;fixme move this up?
;;
;; the main mutual recursion for the new rewriter ("rewrite"):
;;
(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

(mutual-recursion

 ;; Returns (mv erp hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj),
 ;; where extended-alist is irrelevant if hyps-relievedp is nil
 ;; keeps trying ASSUMPTION-ARG-LISTS until it finds a match for HYP (thus binding some free vars) for which it can relieve all the OTHER-HYPS (using those variable bindings)
 (defun relieve-free-var-hyp-and-all-others-for-rewrite-rule (assumption-arg-lists ;these are lists of nodenums/quoteps for calls of fn that we can assume (where fn is the top function symbol of hyp)
                                                              hyp-args ;partially instantiated; any vars that remain must match the assumption
                                                              rewrite-objective
                                                              hyp-num ;for printing.  just pass in the full hyp?
                                                              other-hyps
                                                              alist ;maps vars to nodenums/quoteps
                                                              rule-symbol
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              ;; print-interval embedded-dag-depth work-hard-when-instructedp
                                                              interpreted-function-alist
                                                              rule-alist
                                                              oi-rule-alist
                                                              refined-assumption-alist ;we need to keep the whole alist in addition to walking down the entry for the current fn
                                                              equality-array
                                                              print monitored-symbols info tries simplify-xorsp state result-array-stobj)
   (declare (xargs :mode :program :stobjs (state result-array-stobj)))
   (if (endp assumption-arg-lists)
       ;;failed to relieve the hyp
       ;;fixme think about how to print failure messages for monitored rules when backtracking..
       (progn$ (and (member-eq rule-symbol monitored-symbols)
                    (cw "(Failed to bind free vars in hyp ~x0 of ~x1.)~%" hyp-num rule-symbol))
               (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))
     (let* ((arg-list (first assumption-arg-lists))
            (fail-or-extended-alist (unify-trees-with-dag-nodes hyp-args arg-list dag-array alist)))
       (if (eq :fail fail-or-extended-alist)
           ;;this assumption didn't match:
           (relieve-free-var-hyp-and-all-others-for-rewrite-rule (rest assumption-arg-lists)
                                                                 hyp-args rewrite-objective hyp-num other-hyps
                                                                 alist rule-symbol
                                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                 ;;print-interval embedded-dag-depth work-hard-when-instructedp
                                                                 interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
         (mv-let (erp other-hyps-relievedp extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
           (relieve-rewrite-rule-hyps other-hyps (+ 1 hyp-num)
                                      rewrite-objective
                                      fail-or-extended-alist ;ASSUMPTION bound some free vars
                                      rule-symbol
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      interpreted-function-alist
                                      rule-alist oi-rule-alist refined-assumption-alist equality-array
                                      print monitored-symbols info tries simplify-xorsp state result-array-stobj
;                                           print-interval embedded-dag-depth work-hard-when-instructedp
                                      )
           (if erp
               (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
             (if other-hyps-relievedp
                 (mv (erp-nil) t extended-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
               ;;this assumption matched but we couldn't relieve the rest of the hyps:
               (relieve-free-var-hyp-and-all-others-for-rewrite-rule (rest assumption-arg-lists)
                                                                     hyp-args rewrite-objective hyp-num other-hyps
                                                                     alist ;the original alist
                                                                     rule-symbol
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                     ;;  embedded-dag-depth work-hard-when-instructedp
                                                                     interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols
                                                                     info tries simplify-xorsp state result-array-stobj))))))))

 ;; Returns (mv erp hyps-relievedp alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
 ;; where ALIST may get extended by the binding of free vars to nodenums/quoteps.
 (defun relieve-rewrite-rule-hyps (hyps ;terms (all non-lambda function calls)
                                   hyp-num
                                   rewrite-objective ;the objective under which we are rewriting the lhs or the rule?
                                   alist ;binds vars in the rule to nodenums/quoteps
                                   rule-symbol
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;print-interval embedded-dag-depth work-hard-when-instructedp
                                   interpreted-function-alist
                                   rule-alist oi-rule-alist refined-assumption-alist equality-array
                                   print monitored-symbols info tries simplify-xorsp state result-array-stobj)
   (declare (xargs :mode :program :stobjs (state result-array-stobj)))
   (if (endp hyps)
       ;; all hyps relieved:
       (mv (erp-nil) t alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
     (b* ((hyp (first hyps)) ;known to be a non-lambda function call
          (fn (ffn-symb hyp))
          (- (and (eq :verbose2 print) (cw "Relieving hyp: ~x0 with alist ~x1.~%" hyp alist))))
       (if (eq 'axe-rewrite-objective fn)
           (let ((arg (farg1 hyp)))
             (if (and (quotep arg) ;check when making the rule?  would we ever want a term that evaluates to an objective?
                      (eq rewrite-objective (unquote arg)))
                 ;;this hyp counts as relieved:
                 (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective alist rule-symbol
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
;failed:
               (progn$ (and (member-eq rule-symbol monitored-symbols)
                            ;;is it worth printing in this case?
                            (cw "(Failed (rewrite-objective is ~x0) for hyp ~x1 of ~x2.)~%" rewrite-objective hyp rule-symbol))
                       (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))))
         (if (eq :axe-syntaxp fn)
             (let* ((syntax-expr (cdr hyp)) ;; strip off the AXE-SYNTAXP
                    (result (eval-axe-syntaxp-expr-jvm syntax-expr alist dag-array)))
               (if result
                   ;;this hyp counts as relieved:
                   (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective alist rule-symbol
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                 ;;failed to relieve the axe-syntaxp hyp:
                 (progn$ (and (member-eq rule-symbol monitored-symbols)
                              ;;is it worth printing in this case?
                              (progn$ (cw "(Failed to relieve axe-syntaxp hyp: ~x0 for ~x1.)~%" hyp rule-symbol)
                                      ;; (cw "(DAG:~%")
                                      ;; (print-array2 'dag-array dag-array dag-len)
                                      ;; (cw ")~%")
                                      ))
                         (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))))
           (if (eq :axe-bind-free fn)
               ;; To evaluate the axe-bind-free hyp, we use alist, but we also bind the special variable dag-array to the dag-array.
               ;; The soundness of Axe should not depend on what a axe-bind-free function does; thus we cannot pass alist to a bind-free function and trust it to faithfully extend it.  Nor can we trust it to extend the dag without changing any existing nodes (fixme might be nice to allow it to build new nodes though? could return them as terms, unless they get huge?).
;ffixme might be nice to pass in the assumptions to the axe-bind-free-function? e.g., for finding usbp facts
               (let* ((bind-free-expr (cadr hyp)) ;; strip off the AXE-BIND-FREE
                      (result (eval-axe-bind-free-function-application-jvm (ffn-symb bind-free-expr) (fargs bind-free-expr) alist dag-array) ;could make a version without dag-array (may be very common?).. fixme use :dag-array?
                              ))
                 (if result ;; nil to indicate failure, or an alist whose keys should be exactly (cddr hyp)
                     (let ((vars-to-bind (cddr hyp)))
                       (if (not (axe-bind-free-result-okayp result vars-to-bind dag-len))
                           (mv (erp-t)
                               (er hard? 'relieve-rewrite-rule-hyps "Bind free hyp ~x0 for rule ~x1 returned ~x2, but this is not a well-formed alist that binds ~x3." hyp rule-symbol result vars-to-bind)
                               alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                         ;;this hyp counts as relieved:
                         (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective
                                                    (append result alist) ;; guaranteed to be disjoint given the analysis done when the rule was made and the call of axe-bind-free-result-okayp above
                                                    rule-symbol
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)))
                   ;; failed to relieve the axe-bind-free hyp:
                   (prog2$ (and (member-eq rule-symbol monitored-symbols)
                                (cw "(Failed to relieve axe-bind-free hyp: ~x0 for ~x1.)~%" hyp rule-symbol))
                           (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))))
             (if (eq :free-vars fn) ;can't be a work-hard since there are free vars
                 ;; First, we substitute in for all the vars in HYP that are bound in ALIST (inefficient?)
                 (let ((instantiated-hyp (sublis-var-simple ;fixme allow eval too?  call instantiate-hyp! but then handle the case where a quote is returned.
                                          alist
                                          (cdr hyp) ; strip the :free-vars
                                          )))
                   ;; Now instantiated-hyp is a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars yet to be bound.
                   ;;Since some vars remain in the instantiated-hyp, we search the REFINED-ASSUMPTION-ALIST for matches to bind them:
;fffixme search node-replacement-alist too? or make sure all the context info gets put into REFINED-ASSUMPTIONS?
;the refined-assumptions have been refined so that (equal (pred x) t) becomes (pred x) for better matching
                   (relieve-free-var-hyp-and-all-others-for-rewrite-rule
                    (lookup-eq (ffn-symb instantiated-hyp) refined-assumption-alist) ;hyp will always be a non-lambda function call
                    (fargs instantiated-hyp) rewrite-objective
                    hyp-num
                    (rest hyps)
                    alist rule-symbol
                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;print-interval embedded-dag-depth work-hard-when-instructedp
                    interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
               ;; HYP is not a call to :axe-syntaxp or :axe-bind-free or :axe-rewrite-objective or :free-vars:
               ;; Set the work-hard flag and strip-off the call to work-hard, if present:
               (mv-let
                 (work-hardp hyp)
                 (if (eq 'work-hard fn)
                     (mv t (farg1 hyp)) ;strip off the work-hard
                   (mv nil hyp))
                 ;; No free vars are in the hyp, so we try to relieve the hyp:
                 ;;could add a special case if the hyp is a constant (can happen during instantiation, may be very common?)?
                 (mv-let
                   (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                   (merge-term-into-dag-array hyp alist
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              'dag-array 'dag-parent-array
                                              interpreted-function-alist)
                   (if erp
                       (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                     (if (consp nodenum-or-quotep) ;checks for quotep
                         (if (unquote nodenum-or-quotep)
                             ;;this hyp counts as relieved
                             (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective alist rule-symbol
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        ;;print-interval embedded-dag-depth work-hard-when-instructedp
                                                        interpreted-function-alist rule-alist oi-rule-alist
                                                        refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                           ;;failed to relieve this hyp:
                           (progn$ (and (member-eq rule-symbol monitored-symbols)
                                        (cw "(Failed to relieve hyp: ~x0 for ~x1 (instantiated to nil).)~%" hyp rule-symbol))
                                   (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)))
                       ;;we need to rewrite the hyp:
                       (let ((old-try-count tries))
                         (mv-let
                           (erp new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                           (rewrite-dag-core (push-new-stack nodenum-or-quotep t nil)
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                             nil nil
                                             interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                           (if erp
                               (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                             (let ((try-diff (and old-try-count (- tries old-try-count))))
                               (if (consp new-nodenum-or-quotep) ;checks for quotep
                                   (if (unquote new-nodenum-or-quotep)
                                       ;; hyp rewrote to a non-nil constant and so counts as relieved:
                                       (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective alist
                                                                  rule-symbol
                                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                  ;;print-interval embedded-dag-depth work-hard-when-instructedp
                                                                  interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                                     ;;hyp rewrote to nil, so we failed to relieve it:
                                     ;;fffixme add support for printing if try-diff is large
                                     (progn$ (and (member-eq rule-symbol monitored-symbols)
                                                  (cw "(Failed to relieve hyp: ~x0 for ~x1 (rewrote to nil).)~%" hyp rule-symbol))
                                             (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)))
                                 ;;hyp didn't rewrite to a constant:
                                 (prog2$
                                  (and old-try-count print (or (eq :verbose print) (eq :verbose2 print)) (< 100 try-diff) (cw "(~x0 tries wasted: ~x1:~x2 (non-constant result))~%" try-diff rule-symbol hyp-num))
                                  (if (and work-hardp
                                           ;;work-hard-when-instructedp fffffixme thread this through
                                           )
                                      ;;If we have been instructed to work hard:
                                      (progn$
                                       (cw "(Axe Rewriter is working hard on a hyp of ~x0, namely: ~x1~%" rule-symbol hyp) ;print the instantiated-hyp and hyp num too?
                                       (cw "(Rewrote to:~%")
                                       (if (member-eq print '(t :verbose :verbose2))
                                           (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep) ;fixme print the assumptions (of all kinds)?
                                         (cw ":elided"))
                                       (cw ")~%")
                                       ;; we used to have to save and restore the dag, but now the prover doesn't change any nodes, so that isn't necessary
                                       ;;add the negated assumptions to the dag (fixme what about other equality-assumptions? anything else?):
                                       (mv-let
                                         (erp negated-assumptions dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                         (merge-trees-into-dag-array ;inefficient?: fixme use equality-array here too, or is that info all in refined-assumption-alist??
                                          (negate-terms (decode-refined-assumption-alist refined-assumption-alist))
                                          nil
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                          nil ;fixme ifns
                                          )
                                         (if erp
                                             (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                           ;;call the full prover:
                                           (mv-let
                                             (erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state)
                                             ;;fixme should this do mitering and merging (which would then call the prover on individual node pairs)?
                                             (prove-disjunction-with-axe-prover (cons new-nodenum-or-quotep negated-assumptions) ;these are the literals
                                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                                (list rule-alist) ;fffixme this should be prover-rule-alist
                                                                                interpreted-function-alist
                                                                                nil ;Sun Jan  2 19:08:59 2011 monitored-symbols (was printing too much)
                                                                                print ;:brief ;;print more for work-hard hyps (seemed to print too much? but i would like to see the failures) was :brief until Mon Nov  1 04:23:45 2010 but that may have caused errors with increment-hit-count
                                                                                (symbol-name (pack$ rule-symbol "-HYP-" hyp-num "-WORK-HARD-FOR-"  "UNKNOWN" ;fixme pass around a tag to use instead of unknown?
                                                                                                    ))
                                                                                *default-stp-timeout* ;timeout ;fixme pass this around
                                                                                t ;nil ;print-timeout-goalp
                                                                                nil ;don't work hard on another work-hard hyp fffixme think about this
                                                                                info tries
                                                                                1 ;; prover-depth > 1 disallows changing existing nodes
                                                                                ;;simplify-xorsp ;pass in to prover?
                                                                                nil ;options
                                                                                (+ -1 (expt 2 59)) ;max fixnum?
                                                                                state)
                                             (if erp
                                                 (mv erp nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                               (if (eq :proved result)
                                                   ;;the hyp counts as relieved:
                                                   (progn$ ;(print-hit-counts t info (rules-from-rule-alist rule-alist)) ;ffffixme these are cumulative counts
                                                    (cw "Proved the work-hard hyp)~%")
                                                    (relieve-rewrite-rule-hyps (rest hyps) (+ 1 hyp-num) rewrite-objective alist
                                                                               rule-symbol dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                               interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols
                                                                               info tries simplify-xorsp state result-array-stobj))
                                                 (progn$ (cw "Failed to prove the work-hard hyp for ~x0)~%" rule-symbol)
                                                         (and (member-eq rule-symbol monitored-symbols)
                                                              (progn$
                                                               (cw "(Failed to relieve hyp: ~x0 for ~x1 (rewrote to non-constant).~%" hyp rule-symbol)
                                                               (cw "Reason: Rewrote to:~%")
                                                               (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep)
                                                               ;;fixme print the equality array?
                                                               (cw "Alist: ~x0.~%Refined assumption alist: ~x1)~%" alist refined-assumption-alist)))
                                                         (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))))))))
                                    ;;failed to relieve this hyp:
                                    (progn$ (and (member-eq rule-symbol monitored-symbols)
                                                 (progn$
                                                  (cw "(Failed to relieve hyp: ~x0 for ~x1 (rewrote to non-constant).~%" hyp rule-symbol)
                                                  (cw "Reason: Rewrote to:~%")
                                                  (print-dag-only-supporters 'dag-array dag-array new-nodenum-or-quotep)
                                                  ;;fixme print the equality array?
                                                  (cw "Alist: ~x0.~%Refined assumption alist: ~x1)~%" alist refined-assumption-alist)))
                                            (mv (erp-nil) nil alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj))))))))))))))))))))

 ;; Returns (mv erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj),
 ;; where RHS-OR-NIL is either nil (no rule fired) or a quotep/nodenum from instantiating the rhs of a rule that fired
 (defun try-to-apply-rewrite-rules (stored-rules ;;the rules for the current fn, in stored-rule format
                                    args-to-match ;;nodenums or quoteps of the arguments to fn
                                    rewrite-objective
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    interpreted-function-alist
                                    rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
   (declare (xargs :mode :program :stobjs (state result-array-stobj)))
   (if (endp stored-rules)
       ;;no rule fired:
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
     (let* ((stored-rule (first stored-rules))
            (rule-lhs-args (stored-rule-lhs-args stored-rule))
            (tries (and tries (+ 1 tries))) ;so tries includes rules that have the right function symbol but don't even match
            (alist-or-fail (unify-terms-and-dag-items-fast rule-lhs-args
                                                       args-to-match
                                                       dag-array
                                                       dag-len)))
       (if (eq :fail alist-or-fail)
           ;;the rule didn't match, so try the next rule:
           (try-to-apply-rewrite-rules (rest stored-rules) args-to-match rewrite-objective
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       interpreted-function-alist rule-alist oi-rule-alist
                                       refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
         ;;the rule matched, so try to relieve its hyps:
         (b* ((rule-symbol (stored-rule-symbol stored-rule))
              (- (and (eq print ':verbose2)
                          (cw "(Trying to apply ~x0.~%" rule-symbol)))
              (hyps (stored-rule-hyps stored-rule)))
           (mv-let (erp hyps-relievedp alist ;may get extended by the binding of free vars
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                   (if (not hyps)
                       ;;if there are no hyps, don't even bother: fixme is this special case worth it?
                       (mv (erp-nil) t alist-or-fail dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                     (relieve-rewrite-rule-hyps hyps
                                                1 ;;initial hyp number
                                                rewrite-objective
                                                alist-or-fail
                                                rule-symbol
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                   (if erp
                       (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                     (if hyps-relievedp
                         ;;the hyps were relieved:
                         (let* ((info (and info (increment-hit-count-in-info-world rule-symbol info))))
                           (prog2$ (and (eq print ':verbose2)
                                        (cw "Rewriting with ~x0.)~%" rule-symbol))
                                   (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                     (merge-term-into-dag-array (stored-rule-rhs stored-rule) alist
                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                                                interpreted-function-alist)
                                     (if erp
                                         (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                       (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)))))
                       ;;failed to relieve the hyps, so try the next rule:
                       (prog2$ (and (eq print :verbose2)
                                    (cw "Failed to apply rule ~x0.)~%" rule-symbol))
                               (try-to-apply-rewrite-rules (rest stored-rules) args-to-match rewrite-objective
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))))))))))

 ;;each stack represents the pending rewrites.  the bottom node of each stack represents the rewrite of the top node of the stack beneath.
 ;;the bottom node of the bottom stack represents the whole thing being rewritten
 ;;instead of using aref1-expandable, we could expand the result-array in sync with the dag-array - old comment?
 ;; Returns (mv erp final-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
 ;; the dag coming in should not include lambdas (they should be beta-reduced whenever we make a dag?)
 ;; Extends the DAG but doesn't change any existing nodes?
 (defun rewrite-dag-core (stacks
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                          previous-node-result ;nil or the result of a node we just popped off
                          previous-stack-result ;nil or the result of a stack we just popped off
                          ;;fixme add flags, etc.
                          interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist
                          equality-array ;nil or an array mapping nodenums to nodenums-or-quoteps? maybe use an alist with sorted keys?
                          print monitored-symbols
                          info  ;a non-empty info-world or nil
                          tries ;a natural or nil
                          simplify-xorsp state result-array-stobj ;; (includes polarity info)
                          )
   (declare (xargs :mode :program :stobjs (state result-array-stobj)))
   (if (endp stacks)
       (mv (erp-nil) previous-stack-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
     ;;there is at least one stack left:
     (let* ((stack (first stacks)))
       (if (endp stack)
           ;;The current stack is empty, so we must have just popped off its bottom node (and previous-node-result must contain the result of rewriting that node, which is also the result of rewriting the top node in the previous stack).  We pop off the current (empty) stack and set previous-stack-result to previous-node-result.
           (rewrite-dag-core (rest stacks)
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                             nil
                             previous-node-result
                             interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
         (let* ((stack-entry (first stack)) ;use "top"?
                (nodenum (if (atom stack-entry) stack-entry (car stack-entry)))
                (rewrite-objective (if (atom stack-entry) '? (cdr stack-entry))))
           (if previous-stack-result
               ;;we just popped off a stack that was pushed to rewrite the top node of the current stack
               (let ((result-array-stobj (set-result nodenum rewrite-objective previous-stack-result result-array-stobj)))
                 (rewrite-dag-core (cons (rest stack) (rest stacks))
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                   previous-stack-result nil interpreted-function-alist rule-alist oi-rule-alist
                                   refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
             ;;normal case:
             (let* ((possible-result (get-result nodenum rewrite-objective result-array-stobj)))
               (if possible-result
                   ;; we know what the top node on the current stack rewrites to (with the current objective), so just pop it off:
                   (rewrite-dag-core (cons (rest stack) (rest stacks))
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     possible-result
                                     nil
                                     interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                 ;;we don't yet know what the top node on the current stack rewrites to (with the current objective):
                 (b* ((- (and print
                              (equal 0 (mod nodenum 1000)) ;fixme how expensive are these mods?  just keep a counter from 0 to 1000 and reset it to 0 once it hits 1000 (of course the nodes are not processed in order)?
                              (cw "(Rewriting node ~x0 (obj: ~x1).)~%" nodenum rewrite-objective)))
                      (expr (aref1 'dag-array dag-array nodenum)))
                   (if (atom expr)
                       ;;expr is a variable: all we can do is look it up in the equality assumptions
                       (let ((equality-match (and equality-array
                                                  (aref1-expandable 'equality-array equality-array nodenum))))
                         (if equality-match
                             (if (consp equality-match) ;equated to a constant
                                 (let ((result-array-stobj
                                        (set-result nodenum rewrite-objective equality-match result-array-stobj)))
                                   (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                     equality-match
                                                     nil
                                                     interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                               ;;rewrite the thing this node is equal to (equality-match is a nodenum):
                               (rewrite-dag-core (push-new-stack equality-match rewrite-objective stacks) ;pushes a new stack for the thing
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 nil
                                                 nil
                                                 interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                           ;;no equality match for the variable, so it just rewrites to itself :
                           (let ((result-array-stobj (set-result nodenum rewrite-objective nodenum result-array-stobj)))
                             (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               nodenum
                                               nil
                                               interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))))
                     (let ((fn (ffn-symb expr)))
                       (if (eq 'quote fn)
                           ;;expr is a constant and so rewrites to itself:
                           (let ((result-array-stobj (set-result nodenum rewrite-objective expr result-array-stobj)))
                             (rewrite-dag-core (cons (rest stack) (rest stacks))
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                               expr
                                               nil
                                               interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                         ;;expr is a function call (should never be a lambda, since those should never be stored in dag nodes):
                         (let* ((args (dargs expr)))
                           ;;check whether it is a ground term: ffixme don't even add an evaluatable ground term to the dag and then improve this?
                           (if (and (all-consp args)
                                    (or (member-eq fn *axe-evaluator-functions*)
                                        (eq fn 'DAG-VAL-WITH-AXE-EVALUATOR) ;fixme add to *axe-evaluator-functions*? or use a different list? fixme add the other generated fn names?
                                        (assoc-eq fn interpreted-function-alist) ;fixme?
                                        )
                                    (not (eq fn 'repeat)) ;Wed Feb 16 22:23:08 2011
                                    )
                               ;;it's a ground term:
                               (let* ((result (enquote (apply-axe-evaluator-to-quoted-args fn args interpreted-function-alist 0)))
                                      (result-array-stobj (set-result nodenum rewrite-objective result result-array-stobj)))
                                 (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop this nodenum
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                   result
                                                   nil
                                                   interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                             ;; it's not a ground term:
                             ;;Before simpifying the args, we try to apply outside-in rewrite rules:
                             (mv-let (erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                               (try-to-apply-rewrite-rules (get-rules-for-fn fn oi-rule-alist)
                                                           args
                                                           rewrite-objective
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           interpreted-function-alist
                                                           rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                               (if erp
                                   (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                 (if rhs-or-nil
                                     ;;some rule fired:
                                     (if (consp rhs-or-nil) ;it's a quotep
                                         (let ((result-array-stobj (set-result nodenum rewrite-objective rhs-or-nil result-array-stobj)))
                                           (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop this nodenum
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                             rhs-or-nil
                                                             nil
                                                             interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                       ;;rewrite the rhs:
                                       (rewrite-dag-core (push-new-stack rhs-or-nil rewrite-objective stacks) ;;pushes a new stack for the rhs
                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                         nil
                                                         nil
                                                         interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                   ;;no outside-in rule fired, so simplify the args and then try regular rules:
                                   ;;fixme check this..
                                   ;;fixme add support for boolor and booland..
                                   (let* ((arg-objectives (if (eq 'not fn)
                                                              (list (flip-objective rewrite-objective))
                                                            nil))
                                          (extended-stack-or-nil (get-args-to-simplify args arg-objectives stack nil result-array-stobj))) ;maybe just always push the nodes?
                                     (if extended-stack-or-nil
                                         ;;there are some args to simplify, so push them onto the current stack and handle them first:
                                         (rewrite-dag-core (cons extended-stack-or-nil (rest stacks))
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                           nil
                                                           nil
                                                           interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                                       ;;there are no args to simplify:
                                       (let* ((simplified-args (lookup-args-in-result-array2 args arg-objectives result-array-stobj))) ;check for all quoteps here?
                                         ;;check whether it is a ground term now:
                                         (if (and (all-consp simplified-args) ;check whether they are all quoteps
                                                  (or (member-eq fn *axe-evaluator-functions*)
                                                      (eq fn 'DAG-VAL-WITH-AXE-EVALUATOR) ;fixme add to *axe-evaluator-functions*? or use a different list? fixme add the other generated fn names?
                                                      (assoc-eq fn interpreted-function-alist) ;fixme?
                                                      )
                                                  (not (eq 'repeat fn)) ;Wed Feb 16 22:23:19 2011
                                                  )
                                             ;;it's a ground term:
                                             (let* ((result (enquote (apply-axe-evaluator-to-quoted-args fn simplified-args interpreted-function-alist 0)))
                                                    (result-array-stobj (set-result nodenum rewrite-objective result result-array-stobj)))
                                               (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop this nodenum
                                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                 result
                                                                 nil interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                           ;;it is not a ground term:
                                           ;;Now try to apply rewrite rules:
                                           (mv-let (erp rhs-or-nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                             (try-to-apply-rewrite-rules (get-rules-for-fn fn rule-alist)
                                                                         simplified-args
                                                                         rewrite-objective
                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                         interpreted-function-alist
                                                                         rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj)
                                             (if erp
                                                 (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                               (if rhs-or-nil
                                                   ;;some rule fired, so simplify the rhs if necessary:
                                                   (if (consp rhs-or-nil)
                                                       ;; the rhs is a quotep
                                                       (let ((result-array-stobj (set-result nodenum rewrite-objective rhs-or-nil result-array-stobj)))
                                                         (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop this nodenum
                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                           rhs-or-nil
                                                                           nil
                                                                           interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                     ;;rewrite the rhs:
                                                     (rewrite-dag-core (push-new-stack rhs-or-nil rewrite-objective stacks) ;pushes a new stack for the rhs
                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                       nil nil
                                                                       interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                 ;;no rule fired, so add this expr to the dag, then check whether it is equated to anything:
                                                 (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist) ;version for non-ground terms? or maybe we can't eval the fn
                                                   (add-function-call-expr-to-dag-array2 fn simplified-args dag-array dag-len dag-parent-array dag-constant-alist)
                                                   (if erp
                                                       (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
                                                     ;;see if the node is equated to anything (is this the right place to check this?)
                                                     (let ((equality-match (and equality-array
                                                                                (aref1-expandable 'equality-array equality-array new-nodenum))))
                                                       (if equality-match
                                                           (if (consp equality-match) ;equated to a constant
                                                               (let ((result-array-stobj (set-result nodenum rewrite-objective equality-match result-array-stobj)))
                                                                 (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                                   equality-match nil
                                                                                   interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print
                                                                                   monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                             ;;rewrite the thing this node is equal to (equality-match is a nodenum):
                                                             (rewrite-dag-core
                                                              (push-new-stack equality-match rewrite-objective stacks)
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              nil nil
                                                              interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array
                                                              print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                         ;;no equality match:
                                                         (if (and (eq fn 'bvxor) ;todo: what about bitxor?
                                                                  simplify-xorsp
                                                                  (quoted-natp (first simplified-args)))
                                                             ;;it's a bvxor. note that since the args are simplified, if they are bvxor nests they are *normalized* bvxor nests
                                                             (b* ((bvxor-width (unquote (first simplified-args)))
                                                                  ;; get xors from arg2:
                                                                  ((mv arg2-constant arg2-leaves-increasing)
                                                                   (leaves-of-normalized-bvxor-nest (second simplified-args) bvxor-width 'dag-array dag-array dag-len))
                                                                  ;; get xors from arg3:
                                                                  ((mv arg3-constant arg3-leaves-increasing)
                                                                   (leaves-of-normalized-bvxor-nest (third simplified-args) bvxor-width 'dag-array dag-array dag-len))
                                                                  ;; (mv-let
                                                                  ;;  (nodenum-leaves ;sorted in increasing order
                                                                  ;;   accumulated-constant)
                                                                  ;;  (bvxor-nest-leaves-aux (list new-nodenum) (unquote (first simplified-args))
                                                                  ;;                         'dag-array dag-array nil
                                                                  ;;                         '0 ;initial constant
                                                                  ;;                         )
                                                                  ;; Make the leaves of the new nest:
                                                                  (nodenum-leaves-decreasing (merge-and-remove-dups arg2-leaves-increasing arg3-leaves-increasing nil))
                                                                  (accumulated-constant (bvxor bvxor-width arg2-constant arg3-constant))
                                                                  ;; Build the new nest:
                                                                  ((mv new-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                                                                   (add-bvxor-nest-to-dag-array-ignore-errors ;fixme handle the constant separately
                                                                    ;;add-bvxor-nest-to-dag-array takes the list of items in *increasing* (reverse) order:
                                                                    (if (eql 0 accumulated-constant)
                                                                        (reverse-list nodenum-leaves-decreasing) ;if the constant is 0, drop it
                                                                      (revappend nodenum-leaves-decreasing ;fixme handle the constant separately?
                                                                                 (list (enquote accumulated-constant))))
                                                                    bvxor-width
                                                                    (enquote bvxor-width)
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array)))
                                                               (if (consp new-nodenum-or-quotep) ;the bvxor nest became a constant
                                                                   (let ((result-array-stobj (set-result nodenum rewrite-objective new-nodenum-or-quotep result-array-stobj)))
                                                                     (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                                       new-nodenum-or-quotep nil
                                                                                       interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print
                                                                                       monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                                 (if (eql new-nodenum new-nodenum-or-quotep)
                                                                     ;;the bvxor nest is already normalized: (fixme more efficient handling of this case?
                                                                     (let ((result-array-stobj (set-result nodenum rewrite-objective new-nodenum-or-quotep result-array-stobj)))
                                                                       (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                                         new-nodenum-or-quotep nil
                                                                                         interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array
                                                                                         print monitored-symbols info tries simplify-xorsp state result-array-stobj))
                                                                   ;;rewrite the node the bvxor nest became:
                                                                   ;;fffixme think about this?!
                                                                   (rewrite-dag-core
                                                                    (push-new-stack new-nodenum-or-quotep rewrite-objective stacks) ;pushes a new stack for the thing
                                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                    nil nil
                                                                    interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print monitored-symbols
                                                                    info tries simplify-xorsp state result-array-stobj))))
                                                           ;; it's not a bvxor we can handle (or we are not handling bvxor specially):
                                                           ;; we are done rewriting nodenum:
                                                           (let ((result-array-stobj (set-result nodenum rewrite-objective new-nodenum result-array-stobj)))
                                                             (rewrite-dag-core (cons (rest stack) (rest stacks)) ;pop the nodenum
                                                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                               new-nodenum nil
                                                                               interpreted-function-alist rule-alist oi-rule-alist refined-assumption-alist equality-array print
                                                                               monitored-symbols info tries simplify-xorsp state result-array-stobj)))))))))))))))))))))))))))))))
 ) ;end mutual-recursion

;; rewrites nodenum and all supporting nodes
;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist state result-array-stobj)
  ;; Extends the DAG but doesn't change any existing nodes?
(defun rewrite-nodenum (nodenum rewrite-objective
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                interpreted-function-alist rule-alist oi-rule-alist
                                refined-assumption-alist
                                equality-array
                                print monitored-symbols
                                simplify-xorsp state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (let* ((result-array-stobj (clear-result-array-stobj result-array-stobj)))
    (mv-let (erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist info tries state result-array-stobj)
      (rewrite-dag-core (push-new-stack nodenum rewrite-objective
                                        nil ;empty stack
                                        )
                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                        nil nil
                        interpreted-function-alist rule-alist oi-rule-alist
                        refined-assumption-alist
                        equality-array
                        print monitored-symbols
                        (and print (not (eq :brief print)) (empty-info-world)) ;fixme if print is brief, keep a simple total number of hits and just print the total below??:
                        (and print (zero-tries))
                        simplify-xorsp state result-array-stobj)
      (progn$ (and print (not (eq :brief print)) (print-hit-counts print info (append (rules-from-rule-alist rule-alist)
                                                                                      ;; do these get counted?
                                                                                      (rules-from-rule-alist oi-rule-alist))))
              (and print (cw "Total tries: ~x0.~%" tries))
              (mv erp result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist state result-array-stobj)))))

;; todo: rename
;;returns (mv erp dag-lst-or-quotep state result-array-stobj)
;;fixme allow this to take assumptions as nodenums in some array (should this function be allowed to destroy that array?  can there be irrelevant nodes supporting the nodes?)
(defun rewrite-dag-lst (dag-lst-or-quotep rewrite-objective interpreted-function-alist rule-alist oi-rule-alist
                                          assumptions ;terms to assume
                                          print monitored-symbols simplify-xorsp state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (if (quotep dag-lst-or-quotep)
      (mv (erp-nil) dag-lst-or-quotep state result-array-stobj)
    (b* ((assumptions (get-conjuncts-list assumptions))
         (dag-array (make-into-array 'dag-array dag-lst-or-quotep))
         (top-nodenum (top-nodenum dag-lst-or-quotep))
         (dag-len (+ 1 top-nodenum))
         ;;make aux. data structures:
         ((mv dag-parent-array dag-constant-alist dag-variable-alist)
          (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
         ;;handle assumptions:
         (refined-assumptions (refine-assumptions-for-matching assumptions (known-booleans (w state)) nil))
         ;;fixup the refined-assumptions to be fn calls applied to nodenums/quoteps:
         ((mv erp refined-assumption-exprs ;function calls applied to quoteps and /or nodenums in dag-array
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (add-refined-assumptions-to-dag-array refined-assumptions ;these are terms that are function calls
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                'dag-array
                                                'dag-parent-array
                                                nil))
         ((when erp) (mv erp nil state result-array-stobj))
         (equality-pairs (make-equality-pairs assumptions (w state))) ;dotted pairs of terms (fixme don't bother to make these: just populate the array directly?) fixme will there be enough equalities to justify using an array?
         ((mv erp equality-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (if equality-pairs
              (populate-equality-array equality-pairs
                                       (make-empty-array 'equality-array dag-len) ;fixme is dag-len overkill?
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            ;;there are no equalities:
            (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
         ((when erp) (mv erp nil state result-array-stobj))
         ;;make this more directly?  btw, what about duplicate assumptions?
         (refined-assumption-alist (make-refined-assumption-alist refined-assumption-exprs)) ;todo: move up
         ((mv erp final-result dag-array dag-len & & & state result-array-stobj)
          (rewrite-nodenum top-nodenum rewrite-objective
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           interpreted-function-alist rule-alist oi-rule-alist
                           refined-assumption-alist
                           equality-array
                           print monitored-symbols
                           simplify-xorsp state result-array-stobj))
         ((when erp) (mv erp nil state result-array-stobj)))
      (if (quotep final-result) ;check consp?
          (mv (erp-nil) final-result state result-array-stobj)
        (prog2$
         (and (eq print :verbose2)
              (prog2$ (cw "array before crunching:~%")
                      (print-array-vals (+ -1 dag-len) 0 'dag-array dag-array)))
         (mv (erp-nil)
             (drop-non-supporters-array 'dag-array dag-array final-result nil)
             state result-array-stobj))))))

;; Returns (mv erp dag-lst-or-quotep state result-array-stobj)
(defun rewrite-dag-fn (dag-lst rewrite-objective assumptions interpreted-function-alist
                               rules rule-alist
                               oi-rules oi-rule-alist
                               priorities print monitored-symbols simplify-xorsp state result-array-stobj)
  (declare (xargs :mode :program
                  :stobjs (state result-array-stobj)))
  (progn$
   (and monitored-symbols (cw "(Monitoring: ~x0.)~%" monitored-symbols))
   (print-missing-rules monitored-symbols rule-alist)
   (rewrite-dag-lst dag-lst rewrite-objective
                    interpreted-function-alist
                    (extend-rule-alist rules t priorities rule-alist) ;could use different priorities for the two kinds of rules..
                    (extend-rule-alist oi-rules t priorities oi-rule-alist)
                    assumptions
                    print monitored-symbols simplify-xorsp state result-array-stobj)))

; Calls the new rewriter.
;; Returns (mv erp dag-lst-or-quotep state result-array-stobj)
;things to consider adding: remove-duplicate-rulesp, use-internal-contextsp, context-array (really an assumptions array)?, work-hard-when-instructedp
(defmacro rewrite-dag (dag-lst &key
                               (rewrite-objective ''?)
                               (assumptions 'nil)
                               (interpreted-function-alist 'nil)
                               (runes 'nil) ;todo: rename to rules
                               (rules 'nil) ;todo: rename to rule-set
                               (rule-alist 'nil)
                               (oi-runes 'nil)
                               (oi-rules 'nil) ;todo rename to oi-rule-set
                               (oi-rule-alist 'nil)
                               (priorities '(table-alist 'axe-rule-priorities-table (w state)))
                               (print 'nil) ;meaning of this?  is there a print interval?
                               (monitored-symbols 'nil)
                               (simplify-xorsp 't)
                               )
  `(rewrite-dag-fn ,dag-lst ,rewrite-objective ,assumptions ,interpreted-function-alist
                   ,(if runes `(append (make-axe-rules! ,runes (w state)) ,rules) rules)
                   ,rule-alist
                   ,(if oi-runes `(append (make-axe-rules! ,oi-runes (w state)) ,oi-rules) oi-rules)
                   ,oi-rule-alist
                   ,priorities ,print ,monitored-symbols ,simplify-xorsp state result-array-stobj))

;; Returns (mv erp dag-lst-or-quotep state result-array-stobj)
(defun rewrite-term-fn (term rewrite-objective assumptions interpreted-function-alist
                             runes
                             rules ;drop?
                             rule-alist
                             oi-runes oi-rules oi-rule-alist
                             priorities print monitored-symbols simplify-xorsp state result-array-stobj)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp assumptions)
                              (symbol-listp runes)
                              (axe-rule-listp rules))
                  :mode :program
                  :stobjs (state result-array-stobj)))
  (b* (((mv erp rules0) (make-axe-rules runes (w state)))
       ((when erp) (mv erp nil state result-array-stobj))
       (rules (append rules0 rules))
       ((mv erp oi-rules0) (make-axe-rules oi-runes (w state)))
       ((when erp) (mv erp nil state result-array-stobj))
       (oi-rules (append oi-rules0 oi-rules))
       ((mv erp dag-lst) (make-term-into-dag term interpreted-function-alist))
       ((when erp) (mv erp nil state result-array-stobj)))
    (rewrite-dag-lst dag-lst
                     rewrite-objective
                     interpreted-function-alist
                     (extend-rule-alist rules t priorities rule-alist) ;could use different priorities for the two kinds of rules..
                     (extend-rule-alist oi-rules t priorities oi-rule-alist)
                     assumptions
                     print monitored-symbols simplify-xorsp state result-array-stobj)))

; Calls the new rewriter.
;; Returns (mv erp dag-lst-or-quotep state result-array-stobj)
(defmacro rewrite-term (term &key
                             (rewrite-objective ''?)
                             (assumptions 'nil)
                             (interpreted-function-alist 'nil)
                             (runes 'nil)
                             (rules 'nil)
                             (rule-alist 'nil)
                             (oi-runes 'nil)
                             (oi-rules 'nil)
                             (oi-rule-alist 'nil)
                             (priorities '(table-alist 'axe-rule-priorities-table (w state)))
                             (print 'nil)
                             (monitored-symbols 'nil)
                             (simplify-xorsp 't)
                             )
  `(rewrite-term-fn ,term ,rewrite-objective ,assumptions ,interpreted-function-alist
                    ,runes
                    ,rules
                    ,rule-alist
                    ,oi-runes
                    ,oi-rules
                    ,oi-rule-alist ,priorities ,print ,monitored-symbols ,simplify-xorsp state result-array-stobj))

;returns (mv erp dag state result-array-stobj) where theorem-name has been proved in state
(defun rewrite-term-and-prove-theorem (term theorem-name assumptions runes interpreted-function-alist
                                            ;;fixme what other options to rewrite-term should we pass in?
                                            simplify-xorsp rule-classes state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (mv-let (erp dag state result-array-stobj)
    (rewrite-term term
                  :assumptions assumptions
                  :runes runes
                  :simplify-xorsp simplify-xorsp
                  :interpreted-function-alist interpreted-function-alist)
    (if erp
        (mv erp nil state result-array-stobj)
      (let ((state (submit-event-quiet ;pass in a quiet flag?
                    `(skip-proofs
                      ;;this is correct if the rewriter operates correctly:
                      (defthm ,theorem-name
                        (implies ,(make-conjunction-from-list assumptions)
                                 (equal ,term ;fixme error if this is a variable and we're making a rewrite rule
                                        (dag-val-with-axe-evaluator ',dag
                                                                    ,(make-acons-nest (dag-vars dag))
                                                                    ;;fixme think about this:
                                                                    ;;check that all the fns are already in interpreted-function-alist?
                                                                    ;;',interpreted-function-alist
                                                                    ;;is this overkill?
                                                                    ',(supporting-interpreted-function-alist
                                                                       (dag-fns dag)
                                                                       interpreted-function-alist
                                                                       t)
                                                                    '0 ;array depth (not very important)
                                                                    )))
                        :rule-classes ,rule-classes))
                    state)))
        (mv (erp-nil) dag state result-array-stobj)))))

;returns (mv erp dags state result-array-stobj)
(defun rewrite-terms-with-assumptions (terms assumptions acc state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (if (endp terms)
      (mv (erp-nil) (reverse acc) state result-array-stobj)
    (mv-let (erp result state result-array-stobj)
      (rewrite-term (first terms) :runes (lookup-rules) :assumptions assumptions)
      (if erp
          (mv erp nil state result-array-stobj)
        (rewrite-terms-with-assumptions (rest terms) assumptions (cons result acc) state result-array-stobj)))))


;returns (mv erp dags state result-array-stobj)
;fixme add options? maybe use a macro
(defun rewrite-terms (terms acc state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (if (endp terms)
      (mv (erp-nil) (reverse-list acc) state result-array-stobj)
    (let* ((term (first terms)))
      (mv-let (erp dag state result-array-stobj)
        (rewrite-term term :runes (lookup-rules))
        (if erp
            (mv erp nil state result-array-stobj)
          (rewrite-terms (rest terms) (cons dag acc) state result-array-stobj))))))

;; fixme use outside-in rules?

;todo: put these tests back?
;; (check-test (equivalent-dags-or-quoteps (rewrite-term 'x) (make-term-into-dag 'x nil)))
;; (check-test (not (equivalent-dags-or-quoteps (rewrite-term 'x) (make-term-into-dag 'y nil))))

;; Returns (mv erp value state result-array-stobj)
(defun check-rewrite-fn (term-in term-out
                                 runes
                                 oi-runes
                                 interpreted-function-alist
                                 assumptions
                                 rewrite-objective print state result-array-stobj)
  (declare (xargs :mode :program :stobjs (state result-array-stobj)))
  (mv-let (erp result state result-array-stobj)
    (rewrite-term term-in
                  :rewrite-objective rewrite-objective
                  :assumptions assumptions
                  :interpreted-function-alist interpreted-function-alist
                  :rule-alist (extend-rule-alist (make-axe-rules! runes (w state)) t nil (empty-rule-alist)) ;pull out this pattern
                  :oi-rule-alist (extend-rule-alist (make-axe-rules! oi-runes (w state)) t nil (empty-rule-alist))
                  :print print
                  )
    (if erp
        (mv erp nil state result-array-stobj)
      (mv-let (erp dag)
        (make-term-into-dag term-out nil)
        (if erp
            (mv erp nil state result-array-stobj)
          (if (equivalent-dags-or-quoteps dag result)
              (mv (erp-nil) '(progn) state result-array-stobj)
            (mv (erp-t) :failed state result-array-stobj)))))))

;; Returns (mv erp value state result-array-stobj)
(defmacro check-rewrite (term-in term-out &key
                                 (runes 'nil)
                                 (oi-runes 'nil)
                                 (interpreted-function-alist 'nil)
                                 (assumptions 'nil)
                                 (rewrite-objective ''?)
                                 (print ''t))
  `(make-event (check-rewrite-fn ,term-in ,term-out ,runes ,oi-runes ,interpreted-function-alist ,assumptions ,rewrite-objective ,print state result-array-stobj)))
