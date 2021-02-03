(in-package "ACL2")

(include-book "make-conjunction-dag")
(include-book "make-term-into-dag-array-basic")

;; TODO: Make a variant that translates the term
;; TODO: Make a variant that takes ifns as an option
(defun conjoin-term-with-dag! (term dag)
  (declare (xargs :guard (and (pseudo-termp term)
                              (or (myquotep dag)
                                  (and (pseudo-dagp dag)
                                       (<= (len dag) 2147483646))))
                  :verify-guards nil ;todo
                  ))
  (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic! term
                                                                nil ;todo: ifns
                                                                )
                               dag))
