


(in-package "GL")

(include-book "gobject-types")

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defund nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))


;; An shape spec is an object that is similar to a g object, but a) where there
;; would be BDDs in a g object, there are natural numbers in an shape spec, and
;; b) no G-APPLY constructs are allowed in an shape spec.

(defund number-specp (nspec)
  (declare (xargs :guard t))
  (and (consp nspec)
       (nat-listp (car nspec))
       (if (atom (cdr nspec))
           (not (cdr nspec))
         (and (nat-listp (cadr nspec))
              (if (atom (cddr nspec))
                  (not (cddr nspec))
                (and (nat-listp (caddr nspec))
                     (if (atom (cdddr nspec))
                         (not (cdddr nspec))
                         (nat-listp (cadddr nspec)))))))))


(defagg g-integer (sign bits var))
(defagg g-integer? (sign bits var intp))

(defund shape-specp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (and (not (g-keyword-symbolp x))
           (not (member x '(:g-integer :g-integer?))))
    (case (tag x)
      (:g-number (number-specp (g-number->num x)))
      (:g-integer (and (natp (g-integer->sign x))
                       (nat-listp (g-integer->bits x))))
      (:g-integer? (and (natp (g-integer?->sign x))
                        (nat-listp (g-integer?->bits x))
                        (natp (g-integer?->intp x))))
      (:g-boolean (natp (g-boolean->bool x)))
      (:g-concrete t)
      (:g-var t)
      (:g-ite
       (and (shape-specp (g-ite->test x))
            (shape-specp (g-ite->then x))
            (shape-specp (g-ite->else x))))
      (:g-apply nil)
      (otherwise (and (shape-specp (car x))
                      (shape-specp (cdr x)))))))


(defund shape-spec-obj-in-range-iff (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (iff x obj)
    (pattern-match x
      ((g-number &)
       obj)
      ((g-integer & & &) obj)
      ((g-integer? & & & &) t)
      ((g-boolean &) t)
      ((g-var &) t)
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range-iff then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range-iff else obj))))
      ((g-concrete y) (iff y obj))
      (& obj))))

(defund integer-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (integerp obj)
       (if (atom vlist)
           (eql obj 0)
         (and (<= (- (ash 1 (len (cdr vlist)))) obj)
              (< obj (ash 1 (len (cdr vlist))))))))

(defund natural-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (natp obj)
       (and (<= 0 obj)
            (< obj (ash 1 (len vlist))))))

(defund number-spec-in-range (nspec obj)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints(("Goal" :in-theory (enable number-specp)))))
  (and (acl2-numberp obj)
       (integer-in-range (car nspec) (numerator (realpart obj)))
       (if (consp (cdr nspec))
           (and (natural-in-range (cadr nspec) (denominator (realpart obj)))
                (if (consp (cddr nspec))
                    (and (integer-in-range
                          (caddr nspec) (numerator (imagpart obj)))
                         (if (consp (cdddr nspec))
                             (natural-in-range
                              (cadddr nspec) (denominator (imagpart obj)))
                           (eql (denominator (imagpart obj)) 1)))
                  (rationalp obj)))
         (integerp obj))))

(defund shape-spec-obj-in-range (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (equal x obj)
    (pattern-match x
      ((g-number n) (number-spec-in-range n obj))
      ((g-integer & & &) (integerp obj))
      ((g-integer? & & & &) t)
      ((g-boolean &) (booleanp obj))
      ((g-var &) t)
      ((g-concrete y) (equal y obj))
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range else obj))))
      (& (and (consp obj)
              (shape-spec-obj-in-range (car x) (car obj))
              (shape-spec-obj-in-range (cdr x) (cdr obj)))))))
