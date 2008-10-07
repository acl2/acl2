

(in-package "ACL2")

(include-book "tools/rulesets" :dir :system)

;; This is included so that this book will be considered dependent on
;; arith4-theory, so that any books that include this will be considered
;; dependent on arith4-theory.
(local (include-book "arith4-theory"))

(defmacro allow-arith4-help ()
  `(progn
     (local (include-book
             "tools/arith4-theory" :dir :system))
     (defmacro with-arith4-help (&rest stuff)
       `(encapsulate
         nil
         (local (in-theory (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))))
;;          (local (table theory-invariant-table nil
;;                        (table-alist 'post-arith4-theory-invariants world)))
         . ,stuff))

     (defmacro with-arith4-nonlinear-help (&rest stuff)
       `(encapsulate
         nil
         (local (in-theory (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))))
         (local (set-default-hints '((nonlinearp-default-hint
                                      stable-under-simplificationp
                                      hist pspv))))
         (local (table theory-invariant-table nil
                       (table-alist 'post-arith4-theory-invariants world)
                       :clear))
         . ,stuff))

     (defmacro with-arith4-nonlinear++-help (&rest stuff)
       `(encapsulate
         nil
         (local (in-theory (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))))
         (local (set-default-hints '((nonlinearp-default-hint
                                      stable-under-simplificationp
                                      hist pspv))))
         (local (table theory-invariant-table nil
                       (table-alist 'post-arith4-theory-invariants world)
                       :clear))
         . ,stuff))))


;; Notes:

;; This book allows the arithmetic-4 library to be included locally within a book
;; while only affecting (i.e. arithmetically helping and slowing down proofs of)
;; forms that are surrounded by (with-arith4-help  ...).  To allow this:

;; (include-book "tools/with-arith4-help" :dir :system)

;; ;; Locally includes arithmetic-4, reverts to the pre-arithmetic-4 theory,
;; and defines the with-arith4-help macro.
;; (allow-arith4-help)
