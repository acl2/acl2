(in-package "SMT")
(include-book "std/util/define" :dir :system)
(include-book "../hint-interface")

(define foo ((x integerp)
             (y rationalp))
  :returns (res rationalp)
  (b* ((x (ifix x))
       (y (rfix y)))
    (+ x y)))

(defun smt-fun ()
  `(,(make-smt-function
      :name 'ifix
      :expansion-depth 0)
    ,(make-smt-function
      :name 'rfix
      :expansion-depth 0)))

(defun my-hint ()
  (make-smtlink-hint
   :functions (smt-fun)
   :wrld-fn-len 99))
