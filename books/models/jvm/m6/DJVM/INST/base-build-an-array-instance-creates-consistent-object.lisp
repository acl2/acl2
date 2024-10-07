(in-package "DJVM")
(include-book "../../DJVM/consistent-state")


(defthm build-an-array-intance-consistent-object
  (implies (and (equal (heap s) hp)
                (integerp bound)
                (<= 0 bound)
                (equal (instance-class-table s) cl))
           (consistent-object (car (build-an-array-instance basetype bound s))
                              hp cl))
  :hints (("Goal" :in-theory (enable build-an-array-instance 
                                     wff-obj-strong
                                     isArrayType
                                     common-info))))


(defthm build-an-array-intance-isArrayType
  (isArrayType (obj-type (car (build-an-array-instance basetype bound s))))
  :hints (("Goal" :in-theory (enable isArrayType obj-type
                                     build-an-array-instance 
                                     common-info))))


;; (i-am-here) ;; Sun Jun  5 00:26:40 2005

(local 
 (defthm array-content-initialized-init-array
   (implies (and (not (primitive-type? type))
                 (or (stringp type)
                     (array-type? type)))
   (array-content-initialized (init-array type bound) hp-init))))



(defthm array-content-initialized-build-array-instance
  (implies (and (not (primitive-type? (normalize-type-rep type)))
                (wff-type-rep type))
           (ARRAY-CONTENT-INITIALIZED
            (ARRAY-DATA
             (CAR
              (BUILD-AN-ARRAY-INSTANCE (normalize-type-rep type) bound s)))
            hp-init))
  :hints (("Goal" :in-theory (enable build-an-array-instance
                                     init-array
                                     primitive-type?
                                     array-component-type
                                     wff-type-rep
                                     array-content-initialized
                                     array-data))))


;;; Sun Jun  5 00:32:50 2005 this is WRONG will be fixed..

;;; this is false.. 
;;;
;;; We need to get the 

;;;
;;; We need to be sure that getArrayClass in fact load the array-type
;;; ... 
;;; check the base-consistent-state-load-class.trash.lisp
;;; Mon May 30 17:27:45 2005
;;;


(defthm array-component-type-build-array-instance-reduce
  (equal (array-component-type (obj-type (car (build-an-array-instance type
                                                                       bound
                                                                       s))))
         type)
  :hints (("Goal" :in-theory (enable build-an-array-instance
                                     common-info
                                     obj-type array-component-type))))

        
(encapsulate ()
  (local (include-book "base-consistent-state-load-class-support"))
  (defthm build-an-array-instance-consistent-array-object-specific
    (implies (and (consistent-state s)
                  (no-fatal-error? (getArrayClass basetype s))
                  (equal (heap (getArrayClass basetype s)) hp)
                  (equal (instance-class-table (getArrayClass basetype s)) cl)
                  (equal (array-class-table (getArrayClass basetype s)) acl)
                  (integerp bound)
                  (<= 0 bound))
             (consistent-array-object 
              (car (build-an-array-instance basetype
                                            bound
                                            (getArrayClass basetype s)))
              hp cl acl))))

