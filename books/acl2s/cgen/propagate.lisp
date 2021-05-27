#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "basis")
(include-book "utilities")
(include-book "misc/expander" :dir :system)

;copied from tools/easy-simplify.lisp (by sol swords)
(defun easy-simplify-term1-fn (term hyps hints equiv
                              normalize rewrite
                              repeat
                              backchain-limit
                              state)
  (declare (XargS :mode :program :stobjs state))
  (b* ((world (w state))
       
       ((er hint-settings)
        (acl2::translate-hint-settings
         'simp-term "Goal" hints 'easy-simplify-term world state))
       (ens (acl2::ens state))
       (base-rcnst
        (acl2::change acl2::rewrite-constant
                acl2::*empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((er rcnst)
        (acl2::load-hint-settings-into-rcnst
         hint-settings base-rcnst nil world 'easy-simplify-term state))
       (ens (acl2::access acl2::rewrite-constant rcnst :current-enabled-structure))
       ((mv flg hyps-type-alist ?ttree)
        (acl2::hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state))
       ((mv ?step-limit new-term ?new-ttree state)
        (acl2::pc-rewrite*
         term hyps-type-alist
         (if (eq equiv 'acl2::equal)
             nil
           (list (acl2::make acl2::congruence-rule
                       :rune acl2::*fake-rune-for-anonymous-enabled-rule*
                       :nume nil
                       :equiv equiv)))
         (eq equiv 'acl2::iff)
         world rcnst nil nil normalize rewrite ens state
         repeat backchain-limit
         (acl2::initial-step-limit world state))))
    (value new-term)))


(def easy-simplify-term (term hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify term under hyps. erp is T if hyps have a contradiction
  in them. return the simplifed term in error triple")
  (easy-simplify-term1-fn term hyps hints 'acl2::equal 't 't 1000 1000 state))
;  (symsim-fn term hyps :no-split hints nil t nil (w state) state))


(def easy-simplify-terms (terms hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "loop over simplify-term")
  (if (endp terms)
      (value nil)
    (er-let* ((sterm (easy-simplify-term (car terms) hyps hints state))
              (rest  (easy-simplify-terms (cdr terms) hyps hints state)))
      (value (cons sterm rest)))))




; TODO: WHat will happen if some variable gets elided during this
; simplifcation?  Then our code breaks, especially rem-vars logic and capturing
; full assignment.

;; (def simplify-hyps1-under-assignment (rem-hyps init-hyps x a hints ans. vl state)
;;   (decl :sig ((pseudo-term-list pseudo-term-list symbol quoted-constant true-list pseudo-term-list bool state)
;;               -> (mv erp pseudo-term state))
;;         :mode :program
;;         :doc "simplify each hyp in rem-hyps assuming init-hyps (minus
;;   hyp), accumulate in ans. and return a value triple containing shyps
;;   and an error triple if a contradiction is found in an syhp")
;;   (if (endp rem-hyps)
;;       (value ans.)
;;     (b* ((hyp         (car rem-hyps))
;;          (other-hyps  (remove1-equal hyp init-hyps))
;;          ((er shyp)   (simplify-term hyp other-hyps hints state))
;;          (simplified? (term-order shyp hyp))
;;          ((when (equal shyp ''nil)) ;contradiction
;;           (mv T ans. state))
;; ; 27th Aug '12. FIXED a bug in testing-regression.lsp. In incremental mode
;; ; the assert$ that x should not be in the free vars of the conjecture
;; ; was being violated because I was naively checking against term-order.
;; ; But in the case of small-posp, the type assumptions that could have been
;; ; brought to ACL2's attention using compound-recognizer rules were hidden
;; ; leading to a big IF term being generated in shyp.
;; ; SO now if the above happens(I should give a warning here), at the very
;; ;  least I subst the assignment in hyp.
;;          (- (cw? (and (system-debug-flag vl) 
;;                       (not simplified?))
;;              "~|ACHTUNG: simplify-hyps result not less than hyp in term-order~|"))
;;          (shyp (if simplified? shyp (subst a x hyp))))
     
;;       (simplify-hyps1-under-assignment 
;;        (cdr rem-hyps) init-hyps x a hints
;;        (if (equal shyp ''t) ans.
;;          (append ans. (list shyp))) ;dont mess with order
;;        vl state))))



(def simplify-term (hyp other-hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify term under hyps. erp is T if hyps have a contradiction
  in them. return the simplifed term in error triple")
  (b* ((ens (acl2::ens state))
       (wrld (w state))
       (ctx 'simplify-term)
       ((mv erp x state) (acl2::tool2-fn0 hyp
                                          other-hyps
                                          'iff ctx ens wrld state
                                          hints nil t nil nil nil))
       (shyp (if erp
                 hyp
               (acl2::normalize-no-ttree (cadr x) t nil ens wrld))))
    (value shyp)))
         

(def simplify-term-lst (terms hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "loop over simplify-term, but be conservative")
  (if (endp terms)
      (value nil)
    (b* ((term (car terms))
         ((er sterm) (simplify-term (car terms) hyps hints state))
         (simplified? (term-order sterm term))
         (sterm (if simplified? sterm term))
         ((er rest)  (simplify-term-lst (cdr terms) hyps hints state)))
      (value (cons sterm rest)))))

(include-book "acl2s/defdata/defdata-util" :dir :system)
(defun type-hyp-p (hyp wrld)
  (and (consp hyp)
       (let ((hyp (defdata::expand-lambda hyp)))
         (and (defdata::is-type-predicate (car hyp) wrld)
              (proper-symbolp (cadr hyp))))))

(def simplify-hyps1 (rem-hyps init-hyps hints ans. vl state)
  (decl :sig ((pseudo-term-list pseudo-term-list true-list pseudo-term-list bool state)
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify each hyp in rem-hyps assuming init-hyps (minus
  hyp), accumulate in ans. and return a value triple containing shyps
  and an error triple if a contradiction is found in an syhp")
  (if (endp rem-hyps)
      (value ans.)
    (b* ((hyp         (car rem-hyps))
         (other-hyps  (remove1-equal hyp init-hyps))
         ((er shyp)   (easy-simplify-term hyp other-hyps hints state))
         (simplified? (term-order shyp hyp))
         ((when (equal shyp ''nil)) ;contradiction
          (mv T ans. state))
; 27th Aug '12. FIXED a bug in testing-regression.lsp. In incremental mode
; the assert$ that x should not be in the free vars of the conjecture
; was being violated because I was naively checking against term-order.
; But in the case of small-posp, the type assumptions that could have been
; brought to ACL2's attention using compound-recognizer rules were hidden
; leading to a big IF term being generated in shyp.
; SO now if the above happens(I should give a warning here), at the very
;  least I subst the assignment in hyp.
         (- (cw? (and (debug-flag vl) 
                      (not simplified?))
                 "~|ACHTUNG: simplify-hyps result not less than hyp in term-order~|"))
         (shyp-list (acl2::expand-assumptions-1 shyp))
         )
     
      (simplify-hyps1 
       (cdr rem-hyps) init-hyps hints
       (cond ((type-hyp-p hyp (w state)) (append ans. (list hyp))) ;leave type hyps unchanged
             ((equal shyp ''t) ans.)
             (t (append ans. shyp-list))) ;dont mess with order
       vl state))))

(def simplify-hyps-under-assignment (hyps x a vl state)
  (decl :sig ((pseudo-term-list symbol quoted-constant boolean state)
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "simplify hyps assuming x=a. return shyps in an error
        triple. erp=T if contradiction found in shyps")
  (b* ((hyps (remove-duplicates-equal hyps))
       (hyps1 (acl2::subst-var-lst a x hyps))
       ((er shyps1) (simplify-hyps1  hyps1 hyps1 '() '() vl state)))
;I do the above and then again simplify to get order-insensitive list of
;simplified hypotheses i.e the order of the hyps in the argument should not
;change the result of this function.
   (simplify-hyps1 shyps1 shyps1 '() '() vl state)))



;; (defun replace-variable-terms (terms)
;;   (declare (xargs :guard (pseudo-term-listp terms)))
;;   (if (endp terms)
;;       '()
;;     (if (acl2::variablep (car terms))
;;         (replace-variable-terms (cdr terms))
;;       (cons (car terms) (replace-variable-terms (cdr terms))))))


(def translate-lst (terms state)
  (decl :sig ((true-list true-list state)
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "loop over translate")
  (if (endp terms)
      (value nil)
    (er-let* ((sterm (acl2::translate (car terms) T T T "t-lst" (w state) state))
              (rest  (translate-lst (cdr terms) state)))
    (value (cons sterm rest)))))

; [2015-08-30 Sun] TODO -- return failure explanation i.e. the hypothesis that got contradicted.
;(include-book "misc/bash" :dir :system)
;(include-book "misc/simp" :dir :system)

; [2015-09-19 Sat] above code not working. use bash instead
(def propagate (x a hyps concl vl state)
  (decl :sig ((symbol pseudo-term ;actually a quoted constant
                      pseudo-term-list pseudo-term fixnum state)
              -> (mv erp (list pseudo-term-list pseudo-term) state))
        :mode :program
        :doc "propagate the assignment of a to variable x by using a utility
  function from tools/easy-simplify.lisp (earlier I was using
  expander.lisp). return (mv erp (shyps sconcl) state) where erp might be T
  indicating discovery of inconsistency/contradiction in the hypotheses")
  (b* (;;(hyps (replace-variable-terms hyps)) ;strange bug in bash?? ASK MATT!
       ;; ((er shyps)  (acl2::bash-fn `(IMPLIES (EQUAL ,x ,a) (AND ,@hyps))
       ;;                             nil (debug-flag vl) 'propagate state))
       ;; ((er shyps) (translate-lst shyps state)) ;convert them back to terms
       ((er shyps) (simplify-hyps-under-assignment hyps x a vl state))
       
;IMP: sconcl shud be a pseudo-term; not a term-list, or an IF
      (- (cw? (debug-flag vl)
"~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" hyps x a shyps))
      (?eq-hyp (list 'equal x a)) ;variable comes first
      ((er sconcl) (simplify-term (acl2::subst-var a x concl) shyps nil state))
      (- (cw? (debug-flag vl)
              "~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" concl x a sconcl))
;if conclusion is simplied to true, why waste time? -- abort with error/inconsistent [2015-09-20 Sun]
      ((when (or (equal sconcl 't)
                 (equal sconcl ''t)))
       (mv T nil state))
      
      ;; (simplified? (term-order sconcl concl))
      ;; ;[2015-09-25 Fri] Uncomment these two lines for ma-pipeline-original to work..
      ;; ;[2015-12-08 Tue] Comment these back, because the invariant below (assert) breaks..
      ;; (sconcl (if simplified? sconcl concl)) 

;TODO: this following check is causing problem in regression
; May 13 '12
      ;; ((when (or (pseudo-term-listp sconcl)))
;;                  ;(eq (ffn-symb sconcl) 'IF)))
;; ;IF is okay for an and in the conclusion. But will we ever get an IF from
;; ;inside test-checkpoint??
;;        (mv (prog2$ 
;;             (cw? (normal-output-flag vl)
;; "~|BAD: conclusion got reduced to something we dont want!!~|")
;;             T)
;;            (list shyps sconcl) state))
      (vars (all-vars-lst (cons sconcl shyps))))
      
  (assert$ (not (member-eq x vars)) (mv NIL (list vars shyps sconcl) state))))
                  
