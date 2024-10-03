(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-type-value")
(include-book "../../M6-DJVM-shared/jvm-state")



(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)



(defun fix-zp-mode (mode)
  (declare (xargs :guard (and (integerp mode)
                              (<= 0 mode))))
  (if (zp mode) 0
    1))

; valid-type-s 
;
; reference-type-s is mutual recursive with array-type-s
; 
; This makes it is difficult to do current induction
; and harder to prove properties of functions.
;
; valid-type-s is defined to merge array-type-s and
; reference-type-s


(defun valid-type-s (type cl mode)
    (DECLARE (XARGS :GUARD
                    (WFF-INSTANCE-CLASS-TABLE CL)
                    :hints (("Goal" :in-theory (enable array-component-type)))
                    :MEASURE
                    (CONS (+ (ACL2-COUNT TYPE) 1) (fix-zp-mode mode))))
    (cond ((equal mode 1)
           (OR (EQUAL TYPE 'NULL)
               (valid-type-s TYPE  CL 0)
               (CLASS-EXISTS? TYPE cl)))
          ((equal mode 0) 
           (AND (WFF-ARRAY-TYPE TYPE)
                (OR (PRIMITIVE-TYPE? (ARRAY-COMPONENT-TYPE TYPE))
                    (AND (valid-TYPE-S (ARRAY-COMPONENT-TYPE TYPE) cl 1)
                         (NOT (EQUAL (ARRAY-COMPONENT-TYPE TYPE)
                                     'NULL))))))))

(defthm valid-type-s-add-class-decl
  (implies (and (valid-type-s type cl mode)
                (isclassterm class-rep))
           (valid-type-s type (add-instance-class-entry class-rep cl) mode)))


;;; basically copy from the definition of the reference-type-s, array-type-s

(defun induct-valid-type-is-m (type1 type2 mode)
  (cond ((equal mode 1)
         (cons (cons (+ 1 (acl2-count type1)) 0) 1))
        ((equal mode 0)
         (cons (cons (+ 1 (acl2-count type2)) 0) 0))
        (t 0)))


(acl2::set-verify-guards-eagerness 0)

(defun induct-valid-type-is (type1 cl1 type2 cl2 mode)
  (declare (xargs :measure (induct-valid-type-is-m type1 type2 mode)
                  :hints (("Goal" :do-not '(generalize)
                           :in-theory (enable array-component-type)))))
  (cond ((equal mode 1)
         (induct-valid-type-is type1 cl1 type1 cl1 0))
        ((equal mode 0)
         (if (wff-array-type type2)
             (induct-valid-type-is (array-component-type type2) cl2 
                                   type2 cl2 1)
           (list type1 cl1 type2 cl2 mode)))))

(acl2::set-verify-guards-eagerness 2)


(local 
 (defthm valid-type-s-is-lemma
  (cond ((equal mode 1)
         (equal (valid-type-s type1 cl1 1)
                (reference-type-s type1 cl1)))
        ((equal mode 0)
         (equal (valid-type-s type2 cl2 0)
                (array-type-s type2 cl2)))
        (t t))
  :hints (("Goal" :in-theory (disable isclassterm)
           :induct (induct-valid-type-is type1 cl1 type2 cl2 mode)))
  :rule-classes nil))


(defthm valid-type-s-is
  (and (equal (valid-type-s type cl 1)
              (reference-type-s type cl))
       (equal (valid-type-s type cl 0)
              (array-type-s type cl)))
  :hints (("Goal" :use ((:instance 
                         valid-type-s-is-lemma
                         (cl1 cl) (type1 type) (mode 1))
                        (:instance 
                         valid-type-s-is-lemma
                         (cl2 cl) (type2 type) (mode 0)))))
  :rule-classes nil)


(defun valid-type-strong (type cl)
  (DECLARE (XARGS :GUARD (WFF-INSTANCE-CLASS-TABLE CL)))
  (and (not (equal type 'null))
       (or (valid-type-s type cl 0)
           (valid-type-s type cl 1))))

