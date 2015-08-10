
;;;  measure.lisp                              Warren A. Hunt, Jr.

(in-package "ACL2")

(include-book "help-defuns")
(include-book "../../../ordinals/e0-ordinal")

(deflabel measure-section)

;;;  We define a measure function CONS-SIZE that we use in the
;;;  definition of our DE simulators.

(defun cons-size (x)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (+ 1 (cons-size (car x)) (cons-size (cdr x)))))

#|
(defthm cons-size-cons
  (and (implies (consp x)
                (< 0 (cons-size x)))
       (implies (consp x)
                (< (cons-size (car x))
                   (cons-size x)))
       (implies (consp x)
                (< (cons-size (cdr x))
                   (cons-size x))))
  :rule-classes :linear)
|#

(defthm cons-size-cons
  (implies (consp x)
	   (and (< 0 (cons-size x))
                (< (cons-size (car x))
                   (cons-size x))
		(< (cons-size (cdr x))
                   (cons-size x))
		(< (cons-size (caddar x))
		   (cons-size x))))
  :rule-classes :linear)

(defthm cons-size-fn-delete-eq
   (implies (assoc-eq fn netlist)
           (< (cons-size (delete-eq fn netlist))
              (cons-size netlist)))
   :rule-classes (:linear :rewrite))

(defthm cons-size-no-fn-delete-eq
   (implies (and (alistp netlist)
                 (not (assoc-eq fn netlist)))
            (equal (cons-size (delete-eq fn netlist))
                   (cons-size netlist)))
   :rule-classes (:linear :rewrite))

(defthm cons-size-fn-delete-eq-module
   (implies (assoc-eq fn netlist)
           (< (cons-size (delete-eq-module fn netlist))
              (cons-size netlist)))
   :rule-classes (:linear :rewrite))



;;;  The measure function for the DE recursions.

(defun se-measure (ins-or-occurs netlist)
  (declare (xargs :guard t))
  (cons (1+ (cons-size netlist))
        (cons-size ins-or-occurs)))


(deftheory measure
  (set-difference-theories (current-theory :here)
			   (current-theory 'measure-section)))
