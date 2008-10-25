

(in-package "ACL2")


;; This is included so that this book will be considered dependent on
;; arith4-theory, so that any books that include this will be considered
;; dependent on arith4-theory.

(include-book "rulesets")

(defmacro allow-arith4-help ()
  `(progn
     (local
      (progn

        (defun before-including-arithmetic-4 () nil)

        (table pre-arith4-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear)

        (include-book "arithmetic-4/top" :dir :system)


        (def-ruleset! arith4-enable-ruleset (set-difference-theories
                                             (current-theory :here)
                                             (current-theory
                                              'before-including-arithmetic-4)))

        (def-ruleset! arith4-disable-ruleset (set-difference-theories
                                              (current-theory 'before-including-arithmetic-4)
                                              (current-theory :here)))


        (table post-arith4-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear)

        (table theory-invariant-table nil
               (table-alist 'pre-arith4-theory-invariants world)
               :clear)

        (in-theory (current-theory 'before-including-arithmetic-4))))))


(defun check-for-arith4-rulesets (world)
  (let ((ruleset-alist (table-alist 'ruleset-table world)))
    (and (consp (assoc 'arith4-enable-ruleset ruleset-alist))
         (consp (assoc 'arith4-disable-ruleset ruleset-alist)))))

(defmacro with-arith4-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (if (check-for-arith4-rulesets world)
                           (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))
                         (er hard 'with-arith4-help
                             "Run (ALLOW-ARITH4-HELP) in the current local
scope before using WITH-ARITH4-HELP.~%"))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith4-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro with-arith4-nonlinear-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (if (check-for-arith4-rulesets world)
                           (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))
                         (er hard 'with-arith4-nonlinear-help
                             "Run (ALLOW-ARITH4-HELP) in the current local
scope before using WITH-ARITH4-NONLINEAR-HELP.~%"))))
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
     (local (in-theory (if (check-for-arith4-rulesets world)
                           (e/d* ((:ruleset arith4-enable-ruleset))
                                 ((:ruleset arith4-disable-ruleset)))
                         (er hard 'with-arith4-nonlinear++-help
                             "Run (ALLOW-ARITH4-HELP) in the current local
scope before using WITH-ARITH4-NONLINEAR++-HELP.~%"))))
     (local (set-default-hints '((nonlinearp-default-hint
                                  stable-under-simplificationp
                                  hist pspv))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith4-theory-invariants world)
                   :clear))
     . ,stuff))


;; Notes:

;; This book allows the arithmetic-4 library to be included locally within a book
;; while only affecting (i.e. arithmetically helping and slowing down proofs of)
;; forms that are surrounded by (with-arith4-help  ...).  To allow this:

;; (include-book "tools/with-arith4-help" :dir :system)

;; ;; Locally includes arithmetic-4, reverts to the pre-arithmetic-4 theory,
;; and defines the with-arith4-help macro.
;; (allow-arith4-help)
