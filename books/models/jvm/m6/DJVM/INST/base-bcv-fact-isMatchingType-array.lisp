(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base-bind-free")




(defthm ismatchingtype-aarray-implies-array-element-type-fact1
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness
                                                     "DJVM")) 
                           (env))
                (ismatchingtype '(array (class "java.lang.Object")) stk env))
           (not (equal (arrayelementtype (car stk)) 'void))))

;;;
;;; these are easy because ismatchingtype demand (array ...) or (class ...) 
;;; for it to be possible to assignable to (array (class "java.lang.Object")) 
;;; 
;;; It is good to tag types like this.  

(defthm ismatchingtype-aarray-implies-array-element-type-size-1
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness
                                                     "DJVM")) 
                           (env))
                (ismatchingtype '(array (class "java.lang.Object")) stk env))
           (equal (sizeof (arrayelementtype (car stk))) 1)))

