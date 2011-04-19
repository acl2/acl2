
(in-package "GL")

(include-book "bfr")

(defun hyp-fix (x hyp)
  (declare (xargs :guard (and (bfr-p x)
                              (bfr-p hyp))))
  (bfr-fix-vars
   (x hyp)
   (let ((and (bfr-and x hyp)))
     (if and
         (if (hqual and hyp)
             t
           x)
       nil))))

(prove-congruences (bfr-equiv bfr-equiv) hyp-fix)

(defn hyp-fixedp (x hyp)
  (declare (xargs :guard (and (bfr-p x)
                              (bfr-p hyp))))
  (bfr-fix-vars
   (x hyp)
   (hqual (hyp-fix x hyp) x)))

(prove-congruences (bfr-equiv bfr-equiv) hyp-fixedp)

(defn true-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x t))

(defn false-under-hyp (x hyp)
  (declare (ignorable hyp))
  (eq x nil))


(defmacro hf (x)
  `(hyp-fix ,x hyp))

(defmacro th (x)
  `(true-under-hyp ,x hyp))

(defmacro fh (x)
  `(false-under-hyp ,x hyp))

(add-untranslate-pattern (true-under-hyp ?x hyp) (th ?x))
(add-untranslate-pattern (false-under-hyp ?x hyp) (fh ?x))
(add-untranslate-pattern (hyp-fix ?x hyp) (hf ?x))
