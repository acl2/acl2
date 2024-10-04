(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")

(encapsulate ()
 (local (include-book "base-consistent-object-m6-getfield"))
 (defthm consistent-object-consistent-state-m6-getfield-consistent-value
   (implies (and (consistent-state s)
                 (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                      (fieldcp-classname fieldCP)
                                      s))
                 (REFp v (heap s))
                 (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                      S))
                        classname)
                 (lookupField (fieldcp-to-field-ptr fieldCP) s)
                 (not (NULLp v)))
            (CONSISTENT-VALUE
             (TAG (M6-GETFIELD classname
                               (fieldcp-fieldname fieldcp)
                               (RREF v)
                               S)
                  (fieldcp-fieldtype fieldcp))
             (fieldcp-fieldtype fieldcp)
             (INSTANCE-CLASS-TABLE S)
             (HEAP S)))))
 

(local 
 (defthm consistent-value-implies-wff-tagged-value
   (implies (consistent-value v type cl hp)
            (wff-tagged-value v))))

(defthm consistent-value-implies-wff-tagged-value-specific-get-field
  (implies (consistent-value  (TAG (M6-GETFIELD classname
                                                (fieldcp-fieldname fieldcp)
                                                (RREF v)
                                                S)
                                   (fieldcp-fieldtype fieldcp))
                              (fieldcp-fieldtype fieldcp)
                              (INSTANCE-CLASS-TABLE S)
                              (HEAP S))
           (wff-tagged-value (tag (M6-GETFIELD classname
                                               (fieldcp-fieldname fieldcp)
                                               (RREF v)
                                               S)
                                  (fieldcp-fieldtype fieldcp)))))


;----------------------------------------------------------------------


(local 
 (defthm obj-equal-implies-get-field-equal
   (implies (equal (deref2 v (heap s2))
                   (deref2 v (heap s1)))
            (equal (m6-getfield cn fn (rREF v) s2)
                   (m6-getfield cn fn (rREF v) s1)))))
                



(defthm obj-equal-implies-get-field-equal-specific
  (implies (equal (deref2 v (heap (resolveclassreference any s1)))
                  (deref2 v (heap s1)))
           (equal (m6-getfield cn fn (rREF v) (resolveclassreference any s1))
                  (m6-getfield cn fn (rREF v) s1))))
                


