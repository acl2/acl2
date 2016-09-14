(in-package "PROOF-CHECKER-ITP13")


;; ===================================================================

(ld "rat-checker.lisp")

(ld "rat-parser.lsp")

(in-package "PROOF-CHECKER-ITP13")


(defun get-formula (clause-list num-clauses)
  (cond
   ((atom clause-list) (mv nil nil))
   ((<= num-clauses 0) (mv nil clause-list))
   (t
    (mv-let (formula learned)
            (get-formula (cdr clause-list) (1- num-clauses))
            (mv (cons (car clause-list) formula) learned)))))

;; ===================================================================

(defun verify-file (filename)
  (declare (xargs :mode :program))
  (b* (((mv fail ?num-vars num-clauses clause-list)
        (acl2::parse-unsat-proof filename))
       ((when fail) 'parse-fail)
       ((mv formula proof) (get-formula clause-list num-clauses)))
      (verify-proof proof formula)))

;; ===================================================================

;; (defconst *input* (mv-let (fail num-vars num-clauses clause-list)
;;                           (acl2::parse-unsat-proof "rat-1")
;;                           (list fail num-vars num-clauses clause-list)))



;; (defconst *separated-input* (mv-let (formula proof)
;;                                     (get-formula (nth 3 *input*) (nth 2 *input*))
;;                                     (list formula proof)))

;; (defconst *formula* (nth 0 *separated-input*))
;; (defconst *proof* (nth 1 *separated-input*))



;; (defthm unsat-proof
;;   (not (exists-solution *formula*))
;;   :hints (("Goal"
;;            :use ((:instance refutationp-implies-not-exists-solution
;;                             (clause-list *proof*)
;;                             (formula *formula*))))))
