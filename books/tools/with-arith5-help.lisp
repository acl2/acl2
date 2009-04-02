

(in-package "ACL2")


;; This is included so that this book will be considered dependent on
;; arith5-theory, so that any books that include this will be considered
;; dependent on arith5-theory.

(include-book "rulesets")

(defun check-for-arith5-rulesets (world)
  (let ((ruleset-alist (table-alist 'ruleset-table world)))
    (and (consp (assoc 'arith5-enable-ruleset ruleset-alist))
         (consp (assoc 'arith5-disable-ruleset ruleset-alist)))))

(defun allow-arith5-help-fn (world)
  (if (check-for-arith5-rulesets world)
      '(value-triple :redundant-allow-arith5-help)
    '(local
      (progn

        (defun before-including-arithmetic-5 () nil)

        (table pre-arith5-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear)

        (include-book "arithmetic-5/top" :dir :system)


        (def-ruleset! arith5-enable-ruleset (set-difference-theories
                                             (current-theory :here)
                                             (current-theory
                                              'before-including-arithmetic-5)))

        (def-ruleset! arith5-disable-ruleset (set-difference-theories
                                              (current-theory 'before-including-arithmetic-5)
                                              (current-theory :here)))


        (table post-arith5-theory-invariants nil
               (table-alist 'theory-invariant-table world)
               :clear)

        (table theory-invariant-table nil
               (table-alist 'pre-arith5-theory-invariants world)
               :clear)

        (in-theory (current-theory 'before-including-arithmetic-5))))))

(defmacro allow-arith5-help ()
  '(make-event (allow-arith5-help-fn (w state))))



(defmacro my-enable-arith5 (ctx)
  `(if (check-for-arith5-rulesets world)
       (e/d* ((:ruleset arith5-enable-ruleset))
             ((:ruleset arith5-disable-ruleset)))
     (er hard ,ctx
         "~
Run (ALLOW-ARITH5-HELP) in the current local scope before using ~x0.~%" ,ctx)))


(defmacro with-arith5-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-help)))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro with-arith5-nonlinear-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-nonlinear-help)))
     (local (set-default-hints '((nonlinearp-default-hint
                                  stable-under-simplificationp
                                  hist pspv))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))

(defmacro with-arith5-nonlinear++-help (&rest stuff)
  `(encapsulate
     nil
     (local (in-theory (my-enable-arith5 'with-arith5-nonlinear++-help)))
     (local (set-default-hints '((nonlinearp-default-hint++
                                  id stable-under-simplificationp
                                  hist nil))))
     (local (table theory-invariant-table nil
                   (table-alist 'post-arith5-theory-invariants world)
                   :clear))
     . ,stuff))


(defmacro enable-arith5 ()
  '(my-enable-arith5 'enable-arith5))

;; Notes:

;; This book allows the arithmetic-5 library to be included locally within a book
;; while only affecting (i.e. arithmetically helping and slowing down proofs of)
;; forms that are surrounded by (with-arith5-help  ...).  To allow this:

;; (include-book "tools/with-arith5-help" :dir :system)

;; ;; Locally includes arithmetic-5, reverts to the pre-arithmetic-5 theory,
;; and defines the with-arith5-help macro.
;; (allow-arith5-help)
