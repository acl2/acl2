(in-package "M6")
(include-book "../M6/m6-type-value")
(include-book "../M6/m6-class-table")
(include-book "../M6/m6-state")
(include-book "../M6/m6-class-hierachy-aux")
(include-book "../M6/m6-obj")
(include-book "../M6/m6-thread")
(include-book "../M6/m6-frame-manipulation-primitives")

(acl2::set-verify-guards-eagerness 0)
;;; still problematic!! guard verification!! 

;-------------------------------------------------
; Primitives for building an java-visible-portion
;-------------------------------------------------

;; (defun array-type? (type-sig)
;;   (and (true-listp type-sig)
;;        (equal (length type-sig) 2)
;;        (equal (car type-sig) 'ARRAY)))


;; (defun reference-type (type)
;;   (or (stringp type)
;;       (array-type? type)))

;; ;; Does not handle floating point constant properly.
;; ;; ACL2 has no support for floating numbers directly.

;; (defun default-value (type)
;;   (cond ((equal type 'BYTE)  0)
;;         ((equal type 'SHORT) 0)
;;         ((equal type 'INT)   0)
;;         ((equal type 'LONG)  0)
;;         ((equal type 'FLOAT) "0.0")
;;         ((equal type 'DOUBLE) "0.0");
;;         ((equal type 'CHAR)   0)
;;         ((equal type 'BOOLEAN) nil)
;;         ((array-type? type) -1)
;;         ((reference-type type) -1) ;; use -1 as null pointer.
;;         (t 'NOT-DEFINED))) 
;;

;; ;;; moved to jvm-type-value.lisp

(include-book "../M6-DJVM-shared/jvm-object-manipulation-primitives")

;; (defun make-field-value-pair (field-name value)
;;   (cons field-name value))


;; (defun make-immediate-field-bindings (class-name field-bindings)
;;   (cons class-name field-bindings))


;; ;; initialization will actually fill in default values for those
;; ;; fields. however in build-class-fields-bindings

;; (defun wff-class-fields (class-fields)
;;   (if (not (consp class-fields))
;;       (equal class-fields nil)
;;     (and (wff-field (car class-fields))
;;          (wff-class-fields (cdr class-fields)))))

;; (defun build-class-fields-bindings (class-fields)
;;   (declare (xargs :guard (wff-class-fields class-fields)))
;;   (if (endp class-fields)
;;       nil
;;     (let* ((field (car class-fields))
;;            (field-name (field-fieldname field))
;;            (field-type (field-fieldtype field)))
;;     (cons (make-field-value-pair field-name (default-value field-type))
;;           (build-class-fields-bindings (cdr class-fields))))))
  
;; ;; too much efforts in defining those guard checks!! 
;; ;; (acl2::set-verify-guards-eagerness 0)

;; (defun build-immediate-instance-data-guard (class-name s)
;;   (and (wff-state s)
;;        (wff-class-table (class-table s))
;;        (wff-instance-class-table (instance-class-table s))
;;        (wff-class-rep (class-by-name class-name
;;                                      (instance-class-table s)))
;;        (wff-class-fields (fields (class-by-name
;;                                   class-name
;;                                   (instance-class-table s))))))

;; (defun build-immediate-instance-data (class-name S)
;;   (declare (xargs :guard (build-immediate-instance-data-guard class-name s)))
;;   (let* ((dcl (instance-class-table S))
;;          (field-bindings 
;;           (build-class-fields-bindings 
;;            (fields (class-by-name class-name dcl)))))
;;     (mv (make-immediate-field-bindings class-name field-bindings) S)))


;; (defun build-a-java-visible-instance-data-guard (class-names s)
;;   (if (not (consp class-names))
;;       t
;;     (and (build-immediate-instance-data-guard (car class-names) s)
;;          (build-a-java-visible-instance-data-guard (cdr class-names) s))))
        
;; (defun build-a-java-visible-instance-data (class-names S)
;;   (declare (xargs :guard (build-a-java-visible-instance-data-guard class-names s)))
;;   (if (not (consp class-names))
;;       (mv nil S)
;;     (mv-let (immediate-instance-data new-S)
;;             (build-immediate-instance-data (car class-names) S)
;;           (mv-let (remaining-instance-data new-S2)
;;                   (build-a-java-visible-instance-data (cdr class-names) new-S)
;;               (mv (cons immediate-instance-data remaining-instance-data)
;;                    new-S2)))))

;; (defun make-java-lang-Object-java-visible-part (s)
;;   (mv (list (cons "java.lang.Object" nil))
;;       s))

;; ;------------
;; ;; contains definition of collect-superclass-list and 
;; ;; it's termination argument.

;; ;; assume all superclasses are loaded already.

;; ;; forget about guard verification for now!! 

;; (acl2::set-verify-guards-eagerness 0) 

;; ;; many guard will not be verified. 
  

;; (defun build-a-java-visible-instance (classname S)
;;   (let* ((cl (instance-class-table S))
;;          (classnames (collect-superclass-list classname cl)))
;;     (if (equal classname "java.lang.Object")
;;         (make-java-lang-Object-java-visible-part S)
;;       (build-a-java-visible-instance-data classnames S))))
  

;; (defun jvp-setfield (classname fieldname value obj) 
;;   (bind classname 
;;         (bind fieldname value
;;               (binding classname obj))
;;         obj))   ;; about how to change the java-visible-portion.

;; (defun jvp-getfield (classname fieldname obj)
;;   (binding fieldname 
;;            (binding classname obj)))




;; (defun build-common-info (of-class)
;;   (make-common-info 0 (new-monitor) of-class)) ;; ha code is same 

;; (defun build-INSTANCE-specific-info ()
;;   (make-INSTANCE-specific-info))

;; ;; add accessor to ... 
;; (defun build-an-instance (classname S)
;;   (mv-let (java-visible-portion new-S) 
;;           (build-a-java-visible-instance classname S)
;;           (let ((commoninfo           (build-common-info classname))
;;                 (specificinfo         (build-INSTANCE-specific-info)))
;;             (mv (make-object commoninfo specificinfo java-visible-portion)  new-S))))


;; ;; so far only deal with building one instance 

;; ;; this M6 and DJVM specific!! because it make uses of topStack and depends on
;; ;; the value representation of values on the stack. 

;; ;------------------------------------------
;; ; Primitives for building an Array instance
;; ;------------------------------------------

;; ;; to build string, we need "array of char"
;; ;; use information from book jvm-type-value

;; (defun build-ARRAY-specific-info (the-internal-array bound)
;;   (list 'specific-info 'ARRAY the-internal-array bound))


;; (defun array-type (array-obj) 
;;   (obj-type array-obj))


;; (defun array-bound (array-obj) 
;;   (let ((array-specific-info (specific-info array-obj)))
;;     (nth 3 array-specific-info)))

;; (defun array-data (array-obj)
;;   (let ((array-specific-info (specific-info array-obj)))
;;     (nth 2 array-specific-info)))

;; (defun element-at (index array)
;;   (nth index (array-data array)))

;; (defun init-array (type count)
;;   (if (zp count)
;;       nil
;;       (cons (default-value type) (init-array type (- count 1)))))


;; (defun make-array (type bound data S)
;;   (mv-let (java-visible-portion new-S)
;;           (build-a-java-visible-instance "java.lang.Object" S)
;;           (let* ((common-info (build-common-info type))
;;                  (specific-info (build-ARRAY-specific-info data bound)))
;;             (mv (make-object common-info specific-info java-visible-portion) new-S))))



;; (defun set-element-at (index value array S)
;;   (make-array (array-type array)
;;               (array-bound array)
;;               (update-nth index value (array-data array))
;;               S))


;; (defun build-an-array-instance (element-type length S)
;;   (let ((array-type (make-array-type element-type))
;;         (array-data (init-array element-type length)))
;;     (make-array array-type length array-data S)))


;; ;; make a change here. don't want to introduce exception here.  let's assume
;; ;; once this is called, length is guaranteed to be correct. 
;; ;; all possible exception should be thrown before it call this function.

;; (defun new-array (element-type length S)
;;   (if (< length 0)
;;       (m6-internal-error "new-array precondition violated" s)
;;     (mv-let (the-object new-s)
;;             (build-an-array-instance element-type length S)
;;             (let* ((old-heap (heap new-s))
;;                    (addr     (alloc old-heap))
;;                    (new-heap (bind addr the-object old-heap)))
;;               (pushStack addr (update-trace addr (state-set-heap new-heap new-s)))))))
;; ;; whenever we create a new object, we update-the trace.

;; ;; .... M6, DJVM specific ...


;; (defun set-element-at-array (index value array-ref s)
;;   (let* ((old-heap (heap s))
;;          (old-array-obj (binding array-ref old-heap)))
;;     (mv-let (new-array-obj new-s)
;;             (set-element-at index value old-array-obj s)
;;             (let* ((new-heap (bind array-ref new-array-obj old-heap)))
;;               (state-set-heap new-heap new-s)))))
;; ;; we don't update the trace if there is only a write.


;; (defun set-array-content1 (obj-refs array-ref s offset)
;;   (if (endp obj-refs)
;;       s
;;     (set-array-content1 (cdr obj-refs) array-ref 
;;                         (set-element-at-array offset (car obj-refs) 
;;                                               array-ref s)
;;                         (+ offset 1))))


;; (defun set-array-content (obj-refs array-ref s)
;;   (set-array-content1 obj-refs array-ref s 0))


;; ;;  another definition will be 


;; ;; (defun multiarray-measure (counts length)
;; ;;   (if (zp length)
;; ;;       (cons (cons (+ (len counts) 1) 0) 0)
;; ;;     (cons (cons (+ (len counts) 1) 0) (+ length 1))))



;; ;; (mutual-recursion 
;; ;;  (defun make-multiarray1 (array-type counts s)
;; ;;    (declare (xargs :measure (multiarray-measure counts 0)))
;; ;;    (if (endp counts)
;; ;;        (pushStack -1 s)  
;; ;;      ;; with the array-ref on the top of the stack
;; ;;      (mv-let (obj-refs s1)
;; ;;              (make-multiarray2 (array-base-type array-type)
;; ;;                                (cdr counts) 
;; ;;                                (car counts) 
;; ;;                                s)
;; ;;              ;; first create all elements of the array
;; ;;              (let* ((s2 (new-array (array-base-type array-type) 
;; ;;                                    (car counts)
;; ;;                                    s1))
;; ;;                     (array-ref (topStack s2))
;; ;;                     (s3 (set-array-content obj-refs array-ref s2)))
;; ;;                s3))))

;; ;;  (defun make-multiarray2 (array-type counts length s)
;; ;;    (declare (xargs :measure (multiarray-measure counts length)))
;; ;;    (if (zp length)
;; ;;        (mv nil s)
;; ;;      (mv-let (obj-refs new-s)
;; ;;              (make-multiarray2 array-type counts (- length 1) s)
;; ;;              (let* ((new-s2 (make-multiarray1 array-type counts new-s))
;; ;;                     (obj-ref (topStack new-s2)))
;; ;;                (mv (cons obj-ref obj-refs) (popStack new-s2)))))))


;; ;; ;; bytecode verifier would ensure the array-type is actually has more depths
;; ;; ;; than dim, here we check the runtime data from stack to ensure there are 
;; ;; (defun multiarray-stack-non-negative (dim s)
;; ;;   (if (zp dim)
;; ;;       t
;; ;;     (if (< (topStack s) 0)
;; ;;         nil
;; ;;       (multiarray-stack-non-negative (- dim 1) (popStack s)))))
  

;; ;; ;; similiar to new-array, assume exception is not thrown here.
;; ;; (defun new-multiarray (array-type dim s)
;; ;;   (if (multiarray-stack-non-negative dim s)
;; ;;       (m6-internal-error "new-multiarray precondition violated" s)
;; ;;     (let ((counts (reverse (take dim (operand-stack (current-frame s))))))
;; ;;       (make-multiarray1 array-type counts s))))
    


;; ;------------------------------------------
;; ; Primitives for building an Generic Object 
;; ;------------------------------------------

;; ;---------------------------------------------------------------------------
;; ; 
;; ;  Build a String before class is properly loaded.  only used by Class Loader
;; ;  to create initial heap when loading the classs.
;; ;
;; ;----------------------------------------------------------------------------

;; ;; 08/19/2002
;; ;; because the special field appeared in the String also appeared as java
;; ;; visible field in String. We treat it as a generic_object.

;; (defun build-STRING-specific-info ()
;;   (make-STRING-specific-info))

;; (defun build-a-javaString (s)
;;   (mv-let (java-visible-portion new-S) 
;;           (build-a-java-visible-instance "java.lang.String" S)
;;           (let ((commoninfo           (build-common-info "java.lang.String"))
;;                 (specificinfo         (build-STRING-specific-info)))
;;             (mv (make-object commoninfo specificinfo java-visible-portion)  new-S))))


;; ;  build the heap objects that represent the classes loaded.
;; ;

;; (defun build-instanceClass-info (classname) 
;;   (make-INSTANCE_CLASS-specific-info classname))


;; ; (defun build-instanceClass-info (classname) 
;; ;   (list 'INSTANCE_CLASS classname))
;; ;; FIXED for consistent-test.  10/27/03 


;; (defun isInstanceClass? (specificinfo)
;;   (equal (cadr specificinfo) 'INSTANCE_CLASS))
 
;; (defun specific-info-classname (info)
;;   (caddr info))


;; (defun build-java-lang-Class-java-visible-part (S)
;;   (mv (list (cons "java.lang.Class" nil)
;;             (cons "java.lang.Object" nil))
;;       s))


;; (defun build-an-instanceClass (classname S)
;;   (mv-let (java-visible-portion new-S)
;;           (build-java-lang-Class-java-visible-part s)
;;           (let ((commoninfo           (build-common-info "java.lang.Class"))
;;                 (specific-info        (build-instanceClass-info classname)))
;;             (mv (make-object commoninfo specific-info java-visible-portion)
;;                 new-S))))
                                                

;; (defun build-instanceClassArrayClass-info (type-desc) 
;;   (make-instanceclassarrayclass-info type-desc))

;; (defun isArrayClass? (specificinfo)
;;   (equal (cadr specificinfo) 'ARRAY_CLASS))

;; ;; may need to seperate the pacakage name out...
;; ;; notice this is an instance of java.lang.Class which described an array-type.


;; (defun specific-info-array-desc (info)
;;   (caddr info))

;; (defun build-instanceClassArrayClass (base-type-desc S)
;;   (mv-let (java-visible-portion new-S)
;;           (build-java-lang-Class-java-visible-part s)
;;           (let ((commoninfo   (build-common-info "java.lang.Class"))
;;                 (specific-info   (build-instanceClassArrayClass-info
;;                                   (make-array-type base-type-desc))))
;;             (mv (make-object commoninfo specific-info java-visible-portion)
;;                 new-S))))



;; ;--------------- build a Throwable-instance ----- 
;; (defun build-throwable-specific-info (message backtrace)
;;   (make-throwable-specific-info message backtrace))

;; (defun specific-info-throwable-instance-message (specific-info)
;;   (nth 2 specific-info))


;; (defun build-a-Throwable-instance (classname s)
;;   (mv-let (java-visible-portion new-s)
;;           (build-a-java-visible-instance classname s)
;;           (let ((commoninfo (build-common-info classname))
;;                 (specific-info (build-throwable-specific-info -1 nil)))
;;             (mv (make-object commoninfo specific-info java-visible-portion)
;;                 new-S))))



;; ;  
;; ;-------------- above we defined how to build various objects ------- 
;; ;
;; ;        GENERIC-OBJECT
;; ;        ARRAY
;; ;        STRING
;; ;        INSTANCE-CLASS
;; ;        ARRAY-CLASS
;; ;        THROWABLE-instance
;; ;        
;; ;

;; ;-------------- next we defined a unified interface face to use them --- 

;; ;; assuming both c1 has been loaded (all it's superclass has been loaded. 

;; ;; isSubClassOf1 is defined in jvm-semantics-primitives-aux.lisp
;; ;; for the termination argument.

;; (defun isSubClassOf (c1 c2 s)
;;   (isSubClassOf1 c1 c2 (instance-class-table s) nil))


;; ;; 
;; ;; the class of classname MUST have been loaded. 
;; ;; before we can call this function.
;; ;;
;; (defun instantiate (classname S)
;;   (cond ((equal classname "java.lang.String") 
;;          (build-a-javaString S))
;;         ;; classname can't be string. 
;;         ;; is a Throwable class.
;;         ((isSubClassOf classname "java.lang.Throwable" s) 
;;          (build-a-Throwable-instance classname s))
;;         (t  (build-an-instance classname s))))
        

;; (defun  new-instance (classname S)
;;   (mv-let (instance new-S)
;;           (instantiate classname S)
;;           (let* ((heap (heap new-S))
;;                  (new-addr (alloc heap))
;;                  (new-heap (bind new-addr instance heap)))
;;             (mv new-addr (update-trace new-addr (state-set-heap new-heap s))))))


;; ;-


;; (defun type-by-class-ref (class-ref s)
;;   (let* ((class-obj (deref class-ref (heap s)))
;;          (specific-info (specific-info class-obj)))
;;     (if (isInstanceClass? specific-info)
;;         (specific-info-classname specific-info)
;;       (if (isArrayClass? specific-info)
;;           (specific-info-array-desc specific-info)
;;         nil))));; impossible


;; ;-------------- primitives for modifying obj ----
;; ; this is internal operation, assume all classes are already initialized. 
;; ;

;; (defun m6-putfield (classname fieldname value obj-ref s)
;;   (let* ((old-heap (heap s))
;;          (old-obj  (binding obj-ref old-heap))
;;          (old-jvp  (java-visible-portion old-obj))
;;          (new-jvp  (jvp-setfield classname fieldname value old-jvp))
;;          (new-obj  (make-object (common-info old-obj)
;;                                 (specific-info old-obj)
;;                                 new-jvp))
;;          (new-heap (bind obj-ref new-obj old-heap)))
;;     (state-set-heap new-heap s)))


;; (defun m6-getfield (classname fieldname obj-ref s)
;;   (binding fieldname 
;;            (binding classname 
;;                     (java-visible-portion (deref obj-ref (heap s))))))


