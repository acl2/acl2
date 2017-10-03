#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Fixer Rules Metadata Table
;; Atomic-Lit -> [{:fixer fixer-name :rule rule}]
;; Ic(F) => (mv-let Out(F) F(In) Lit)

;; Preservation Rules Metadata Table
;; Atomic-Lit -> [{:preserved-by fixer-name :rule rule}]
;; Ic(F) /\ Hyps => L => (mv-let Out(F) F(In) L)


(in-package "CGEN")

(include-book "utilities")
(include-book "misc/bash" :dir :system)
(include-book "data-structures/utilities" :dir :system)
;(include-book "../defdata/cgen-rules")
(include-book "cgen-state")



(defun cweight (c Cwt{})
  (or (get1 c Cwt{})
      0))

(defun cweight-lst (cs Cwt{})
  (if (endp Cwt{})
      0
    (+ (cweight (car cs) Cwt{})
       (cweight-lst (cdr cs) Cwt{}))))

(defloop filter-terms-without-vars (terms vars)
  (for ((term in terms))
       (when (not (intersectp-eq (acl2::all-vars term) vars))
         (collect term))))

(defun pval (fname fxri{} flits term->flits{} Cwt{} vl)
  (declare (ignorable vl term->flits{}))
  (b* ((fruleI (get1 fname fxri{}))
       (cterm (get1 :constraint-term fruleI))
       (pterms (get1 :preserves fruleI))
       (trivially-preserved-terms (filter-terms-without-vars flits (get1 :Out fruleI))))
    (list (+ (cweight cterm Cwt{}) (cweight-lst pterms Cwt{}))
          (cweight-lst trivially-preserved-terms Cwt{}))))
       
  
;; (defun fxri-let*-soln/greedy1 (term->flits{} var-clique-rep{} Cwt{} fxri{} vl state pval{} ans)
;;   (declare (ignorable vl))
;;   (if (or (endp term->flits{})
;;           (endp fxri{}))
;;       (value ans)
;;     (b* ((pval{} (update-pval-alist pval{} fxri{} term->flits{} Cwt{}))
;;          (fname (choose-maximal-pval-fxri pval{}))
;;          (- (cw? (debug-flag vl) "~| Cgen/Debug: Maximal pvalued fixer: ~x0~%" fname))
;;          (ans (cons (fxri-b*-entry (assoc-equal fname fxri{})) ans))
;;          (fxri1{} (delete-assoc-equal fname fxri{}))
;;          (fxri1{} (remove-unpreserved-fxrs fxri{} fname))
;;          (term->flits1{} (remove-unpreserved-flits term->flits{} fname fxri{}))
;;          )
;;       (fxri-let*-soln/greedy1 term->flits1{} Cwt{} fxri1{} vl state pval{} ans))))


(program)
(set-state-ok t)

(defun fixer-arrangement1 (terms all-terms Cwt{} vl ctx state)
; returns (mv erp (cons let*-soln-binding new-hyps unsat-terms) state)
; unsat-terms are a subset of terms. they exclude type-hyps and
; those terms that have no applicable fixer rules.
; these terms were unsat, because the preservation rules did not work out
         
  (b* ((wrld (w state))
       (frules (strip-cdrs (fixer-rules-table wrld)))
       (prules (strip-cdrs (preservation-rules-table wrld)))
       ((mv ?erp1 (list new-hyps fxri{}) state) ;;new-hyps introduce "free" parameters into fix/enum test-data gen
        (instantiate-fixer-rules terms frules vl state '() '() all-terms '()))
       ((when erp1)
        (er soft ctx "~| Cgen/Error in instantiation of fixer rules!~%"))
       
       ((mv ?erp2 fxri{} state)
        (instantiate-pres-rules prules terms all-terms vl state fxri{}))
       ((when erp2)
        (er soft ctx "~| Cgen/Error in instantiation of preservation rules!~%"))

       ;; (type-hyps  (filter-type-hyps terms wrld))
       ;; (non-type-hyps (set-difference-equal terms type-hyps))
       ;; (fixable-terms (filter-fixable-terms terms fxri{}))
       ;; (relevant-terms (intersection-equal non-type-hyps fixable-terms))

       ((er (list let*-soln01 C_sat))
        (fxri-let*-soln terms Cwt{} fxri{} vl state))
       (C_unsat (set-difference-equal terms C_sat))
       ;(b*-soln (to-b*-mv-binding let*-soln))
       ;(let*-soln (assoc-equal-lst vars let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixer-bindings: ~x0~%" let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixed terms: ~x0~%" C_sat))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Unsat fixable terms: ~x0~%" C_unsat))
       ;; TODO check that this let* binding is sound/correct, i.e., it
       ;; satisfies all the hyps under fixer and pres rules.
       )
    (value (list let*-soln new-hyps C_unsat))))

(defun fixer-arrangement1/repeat (C i all-terms vl ctx state B new-hyps)
  (if (endp C)
      (value (list B new-hyps '()))
    (b* ((- (cw? (verbose-stats-flag vl)
                 "~| Cgen/Note: Recursively fix (loop iteration: ~x0) ~x1~%" i C))
         ((mv erp res state) (fixer-arrangement1 C all-terms vl ctx state))
         ((when erp) (value (list B new-hyps C))) ;return current
         ((list B1 new-hyps1 C_unsat) res)
         ((unless (< (len C_unsat) (len C))) (value (list B new-hyps C))) ;return current
         (B (append B1 B))
         (new-hyps (union-equal new-hyps1 new-hyps)))
      (fixer-arrangement1/repeat C_unsat (1+ i) all-terms vl ctx state B new-hyps))))
         
(defun fixer-arrangement-builtin (hyps concl vl ctx state)
  (b* ((terms (append hyps  (if (not (acl2::logic-termp concl (w state)))
                                '()
                              (list (cgen-dumb-negate-lit concl)))))
       ((mv erp res state)
        (fixer-arrangement1 terms terms vl ctx state))
       ((when erp) (value (list nil nil)))
       ((list B new-hyps C_unsat) res)

       (rec-fixp (acl2s-defaults :get :recursively-fix))
       ((mv ?erp (list B new-hyps C_unsat) state) ;does not return an error
        (if (and rec-fixp 
                 (< (len C_unsat) (len terms)))
            (fixer-arrangement1/repeat C_unsat 1 terms vl ctx state B new-hyps)
          (value (list B new-hyps C_unsat)))) ;o.w return current values

       (- (cw? (and (verbose-stats-flag vl) rec-fixp (consp C_unsat))
               "~| Cgen/Verbose: ~x0 still not fixed! ~%" C_unsat))
        
       (b*-binding (to-b*-mv-binding B))
       (b*-binding (collapse-b*-binding b*-binding nil))
       )
    (value (list b*-binding new-hyps))))


(logic)
(defttag t)
(defattach (fixer-arrangement fixer-arrangement-builtin) :skip-checks t)
(defttag nil)
