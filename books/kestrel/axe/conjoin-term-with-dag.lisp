(in-package "ACL2")

(include-book "make-conjunction-dag")
(include-book "make-term-into-dag-basic")

;; TODO: Make a variant that translates the term
;; TODO: Make a variant that takes ifns as an option
(defun conjoin-term-with-dag! (term dag)
  (declare (xargs :guard (and (pseudo-termp term)
                              (or (myquotep dag)
                                  (and (pseudo-dagp dag)
                                       (<= (len dag) 2147483646))))
                  :guard-hints (("Goal" :in-theory (disable myquotep quotep)))))
  (mv-let (erp dag-or-quotep)
    (acl2::make-term-into-dag-basic term
                                    nil ;todo: ifns
                                    )
    (if erp
        (er hard? 'conjoin-term-with-dag! "Error making term into dag.")
      (if (and (not (myquotep dag-or-quotep))
               (< 2147483646 (len dag-or-quotep)))
          ;; todo: can this happen?
          (er hard? 'conjoin-term-with-dag! "DAG too long.")
        (acl2::make-conjunction-dag! dag-or-quotep dag)))))
