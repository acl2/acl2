
(in-package "ACL2")

(include-book "bv-lib-definitions" :skip-proofs-okp t)
(include-book "bv-lib-lemmas" :skip-proofs-okp t :ttags (sat sat-cl))

;; The following turns our table of function signatures
;; (for a later defeval) into a constant that can be
;; used without accessing or returning state.
(make-event
 (mv-let
  (erp bv-defeval-sigs state)
  (table bv-defeval-sigs nil nil :alist)
  (declare (ignore erp))
  (mv nil
      `(defconst *bv-defeval-sigs* (quote ,bv-defeval-sigs))
      state)))

