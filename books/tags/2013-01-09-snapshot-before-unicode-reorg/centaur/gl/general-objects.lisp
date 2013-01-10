

(in-package "GL")

(include-book "gtypes")

(local (include-book "gobjectp-thms"))

(defun general-booleanp (x)
  (declare (xargs :guard (gobjectp x)))
  (or (booleanp x)
      (and (consp x)
           (or (eq (tag x) :g-boolean)
               (and (eq (tag x) :g-concrete)
                    (booleanp (g-concrete->obj x)))))))

(in-theory (disable (general-booleanp)))

(defund general-boolean-value (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-booleanp x))))
  (if (atom x)
      x
    (cdr x)))

(in-theory (disable (general-boolean-value)))





(defun general-concrete-atom (x)
  (declare (xargs :guard (gobjectp x)
                  :guard-hints (("goal" :in-theory (enable gobjectp
                                                           gobject-hierarchy)))))
  (if (atom x)
      (mbt (not (g-keyword-symbolp x)))
    (and (eq (tag x) :g-concrete)
         (atom (g-concrete->obj x))
         (not (g-keyword-symbolp (g-concrete->obj x))))))

(defun general-concrete-atom-val (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-concrete-atom x))))
  (if (atom x) x (g-concrete->obj x)))

(in-theory (disable (general-concrete-atom)
                    (general-concrete-atom-val)))



(defn general-concretep (x)
  (mbe :logic
       (let ((res (gobject-hierarchy x)))
         (or (eq res 'general)
             (eq res 'concrete)))
       :exec
       (if (gobject-hierarchy-lite x) t nil)))

(defun general-concrete-obj-bdd (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-concretep x))
                  :verify-guards nil))
  (cond ((atom x) x)
        ((g-concrete-p x) (g-concrete->obj x))
        ((mbe :logic (eq (gobject-hierarchy-bdd x) 'concrete)
              :exec (eq (gobject-hierarchy-lite x) 'concrete))
         x)
        (t (cons (general-concrete-obj-bdd (car x))
                 (general-concrete-obj-bdd (cdr x))))))

(defun general-concrete-obj-aig (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-concretep x))
                  :verify-guards nil))
  (cond ((atom x) x)
        ((g-concrete-p x) (g-concrete->obj x))
        ((mbe :logic (eq (gobject-hierarchy-aig x) 'concrete)
              :exec (eq (gobject-hierarchy-lite x) 'concrete))
         x)
        (t (cons (general-concrete-obj-aig (car x))
                 (general-concrete-obj-aig (cdr x))))))


(defun general-concrete-obj (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-concretep x))
                  :verify-guards nil))
  (mbe :logic (cond ((atom x) x)
                    ((g-concrete-p x) (g-concrete->obj x))
                    ((concrete-gobjectp x) x)
                    (t (cons (general-concrete-obj (car x))
                             (general-concrete-obj (cdr x)))))
       :exec (bfr-case :bdd (general-concrete-obj-bdd x)
                       :aig (general-concrete-obj-aig x))))

(defthm general-concrete-obj-bdd-is-general-concrete-obj
  (implies (not (bfr-mode))
           (equal (general-concrete-obj-bdd x)
                  (general-concrete-obj x)))
  :hints(("Goal" :in-theory (enable concrete-gobjectp))))

(defthm general-concrete-obj-aig-is-general-concrete-obj
  (implies (bfr-mode)
           (equal (general-concrete-obj-aig x)
                  (general-concrete-obj x)))
  :hints(("Goal" :in-theory (enable concrete-gobjectp))))



(in-theory (disable (general-concrete-obj)))




(defn general-numberp (x)
  (declare (xargs :guard (gobjectp x)))
  (or (acl2-numberp x)
      (and (consp x)
           (or (eq (tag x) :g-number)
               (and (eq (tag x) :g-concrete)
                    (acl2-numberp (g-concrete->obj x)))))))

(in-theory (disable (general-numberp)))

(defthm general-numberp-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-numberp x)
                  (acl2-numberp x))))


(defun number-to-components (n)
  (declare (xargs :guard (acl2-numberp n)))
  (let* ((real (realpart n))
         (rnum (numerator real))
         (rden (denominator real))
         (imag (imagpart n))
         (inum (numerator imag))
         (iden (denominator imag)))
    (mv (i2v rnum) (n2v rden) (i2v inum) (n2v iden))))


(defn general-number-components (x)
  (declare (xargs :guard (and (gobjectp x)
                              (general-numberp x))
                  :guard-hints (("goal" :in-theory (enable general-numberp)))))
  (if (atom x)
      (number-to-components x)
    (if (eq (tag x) :g-concrete)
        (number-to-components (g-concrete->obj x))
      (break-g-number (g-number->num x)))))




;; Note that, as in the case of general-number and general-boolean, it could
;; still be the case that x always represents a cons even if x is not a
;; general-consp.
(defun general-consp (x)
  (declare (xargs :guard (gobjectp x)))
  (and (consp x)
       (if (eq (tag x) :g-concrete)
           (consp (g-concrete->obj x))
         (not (g-keyword-symbolp (tag x))))))

(in-theory (disable (general-consp)))



(defun general-consp-car (x)
  (declare (xargs :guard (and (gobjectp x) (general-consp x))))
  (if (eq (tag x) :g-concrete)
      (mk-g-concrete (car (g-concrete->obj x)))
    (car x)))


(defun general-consp-cdr (x)
  (declare (xargs :guard (and (gobjectp x) (general-consp x))))
  (if (eq (tag x) :g-concrete)
      (mk-g-concrete (cdr (g-concrete->obj x)))
    (cdr x)))

(in-theory (disable (general-consp-car)
                    (general-consp-cdr)))


(defun bool-cond-itep (x)
  (declare (xargs :guard (gobjectp x)))
  (and (consp x)
       (eq (tag x) :g-ite)
       (general-booleanp (g-ite->test x))))

(defun bool-cond-itep-cond (x)
  (declare (xargs :guard (and (gobjectp x) (bool-cond-itep x))))
  (general-boolean-value (g-ite->test x)))


(defun bool-cond-itep-truebr (x)
  (declare (xargs :guard (and (gobjectp x) (bool-cond-itep x))))
  (g-ite->then x))



(defun bool-cond-itep-falsebr (x)
  (declare (xargs :guard (and (gobjectp x) (bool-cond-itep x))))
  (g-ite->else x))

(in-theory (disable (bool-cond-itep)
                    (bool-cond-itep-cond)
                    (bool-cond-itep-truebr)
                    (bool-cond-itep-falsebr)))



