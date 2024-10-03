(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-type-value")
(include-book "../M6-DJVM-shared/jvm-loader")
(include-book "../M6-DJVM-shared/jvm-class-hierachy-aux")
(include-book "../M6-DJVM-shared/jvm-loader-guard-verification")
;;(include-book "../M6-DJVM-shared/jvm-class-table")

(acl2::set-verify-guards-eagerness 2)

;------ Class Resolution ------

;; let's have no caching. 
;; our constant pool doesn't contain the symbolic links. 

;;; Wed Jan 14 01:10:34 2004. We are not concerned with defining a
;;; consistent-state
;;; We don do any guard verification for any operations that modify state!!
;;;

;; (acl2::set-verify-guards-eagerness 0) ;; temp

(defun resolveClassReference1 (classname s)
  (declare (xargs :guard (and (load_array_class_guard s)
                              (load_class-guard s))))

  (if (array-type? classname)
      (load_array_class (array-base-type classname) s)
    (if (class-loaded? classname s)
        s
      (load_class classname s))))

;; no access checking.
;; should we include access checking??
;; why not? not now.
;; our loader isn't quite right now. 

;;
;; put a wrapper to do the access control runtime checking 
;;
;; shall we put the checking outside? 
;;
;; Sun Dec 28 18:49:44 2003

(defun hasAccessToClass (from to s)
  (declare (ignore from to s))
  ;; tmp implementation 
  t)

(defun resolveClassReference-guard (s)
  (and (load_array_class_guard s)
       (load_class-guard s)
       (current-frame-guard s)
       (wff-call-frame (current-frame s))
       (wff-method-ptr (current-method-ptr s))
       (wff-state s)
       (wff-class-table (class-table s))
       (wff-instance-class-table (instance-class-table s))))

(defun resolveClassReference (classname s)
  (declare (xargs :guard (resolveClassReference-guard s)))
  (let ((new-s (resolveClassReference1 classname s)))
    (if (not (hasAccessToClass (current-class s) classname s))
        (state-set-pending-exception-safe "java.lang.IllegalAccessException" s)
      new-s)))


;------ method Resolution ------

;;

;; Fri Apr  2 00:51:12 2004 stop here. 

;; primitives for how to get a method-ptr
;; used in invokevirtual <methodCP>
;;
;; Sun Jun 20 21:19:28 2004. Deal with it later?? 
;;

(defun wff-methodCP (methodCP)
  (and (true-listp methodCP)
       (equal (len methodCP) 5)
       (equal (car methodCP) 'methodCP)
       (or (equal (nth 4 methodCP) 'VOID)
           (wff-type-rep  (nth 4 methodCP)))
       (wff-type-reps (nth 3 methodCP))))


(defun methodCP-classname  (methodCP)
  (declare (xargs :guard (wff-methodCP methodCP)))
  (nth 2 methodCP))

(defun methodCP-methodname (methodCP)
  (declare (xargs :guard (wff-methodCP methodCP)))
  (nth 1 methodCP))

(defun methodCP-args-type  (methodCP)
  (declare (xargs :guard (wff-methodCP methodCP)))
  (nth 3 methodCP))

(defun methodCP-returntype  (methodCP)
  (declare (xargs :guard (wff-methodCP methodCP)))
  (nth 4 methodCP))

(defun methodCP-to-method-ptr (methodCP)
  (declare (xargs :guard (wff-methodCP methodCP)))
  (make-method-ptr (methodCP-classname methodCP)
                   (methodCP-methodname methodCP)
                   (normalize-type-reps (methodCP-args-type methodCP))
                   (if (equal (methodCP-returntype methodCP) 'VOID)
                       'VOID
                     (normalize-type-rep  (methodCP-returntype methodCP)))))


;;; Wed Jan 14 01:11:33 2004
;;;
; Once we have method-ptr we use the following to find the method-rep

(defun wff-method-decls (methods)
  (if (not (consp methods)) t
    (and (wff-method-decl (car methods))
         (wff-method-decls (cdr methods)))))

;;(i-am-here) ;; Mon May  1 01:54:47 2006

(defun match-method (method-ptr method)
  (declare (xargs :guard (and (wff-method-decl method)
                              (wff-method-ptr method-ptr))))
  (let* ((methodname (method-ptr-methodname method-ptr))
         (args       (method-ptr-args-type  method-ptr))
         (returntype (method-ptr-returntype method-ptr))
         (thisMethod method))
    (and (equal (method-methodname thisMethod) methodname)
         (equal (method-args       thisMethod) args)
         (equal (method-returntype thisMethod) returntype))))
;; Mon May  1 17:26:03 2006 
;; class loader normalize the returntype and parameters!! 



(defun searchMethod (method-ptr methods)
  (declare (xargs :guard (and (wff-method-decls methods)
                              (wff-method-ptr method-ptr))))
  (if (not (consp methods))
      nil
    (if (match-method method-ptr (car methods))
        (car methods)
      (searchMethod method-ptr (cdr methods)))))

;;  Mon May  1 00:53:05 2006
;; 


(defun deref-method (method-ptr class-table)
  (declare (xargs :guard (and (wff-method-ptr method-ptr)
                              (wff-instance-class-table class-table))))
  (and (class-exists? (method-ptr-classname method-ptr) class-table)
       (let* ((classname (method-ptr-classname method-ptr))
              (class-rep (class-by-name classname class-table))
              (methods   (methods class-rep)))
         (and  (wff-method-decls methods)
               (searchMethod method-ptr methods)))))

;; ;; methods is a list of method
;; (defun searchMethod (method-ptr methods)
;;   (if (endp methods)
;;       nil
;;     (let* ((methodname (method-ptr-methodname method-ptr))
;;            (args       (method-ptr-args-type  method-ptr))
;;            (returntype (method-ptr-returntype method-ptr))
;;            (thisMethod (car methods)))
;;       (if (and (equal (method-methodname thisMethod) methodname)
;;                (equal (method-args       thisMethod) args)
;;                (equal (method-returntype thisMethod) returntype))
;;           thisMethod
;;         (searchMethod method-ptr (cdr methods))))))


;; (defun deref-method (method-ptr class-table)
;;   (let* ((classname (method-ptr-classname method-ptr))
;;          (class-rep (class-by-name classname class-table))
;;          (methods   (methods class-rep)))
;;     (searchMethod method-ptr methods)))


;; to prove termination hard. 


(defthm method-ptr-accessor 
  (let ((mpr (make-method-ptr c m a r)))
    (and (equal (method-ptr-classname mpr) c)
         (equal (method-ptr-methodname mpr) m)
         (equal (method-ptr-args-type mpr) a )
         (equal (method-ptr-returntype mpr) r))))


(in-theory (disable method-ptr-classname method-ptr-methodname
                    method-ptr-args-type method-ptr-returntype make-method-ptr))


(acl2::set-verify-guards-eagerness 0)

(defun lookupMethod-measure (method-ptr s)
  (let ((n1  (method-ptr-classname method-ptr))
        (cl  (instance-class-table s)))
  (len (collect-superclass-list n1 cl))))

(acl2::set-verify-guards-eagerness 2)

(defun lookupMethod-inv (method-ptr s)
  (declare (xargs :guard (and (wff-method-ptr method-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (superclass-no-loop (method-ptr-classname method-ptr) (instance-class-table s)))



; --- proofs for collect-superclass-list increase --- 

;; copied from typechecker.lisp

      
(defcong set-equal equal (collect-superclass-list1 n cl ss) 3)

(defthm set-equal-cons-cons
      (set-equal (cons x (cons y a))
                 (cons y (cons x a)))
  :hints (("Goal" :in-theory (enable set-equal))))


; ---- important observation I  -----
;
; If X doesn't belongs to superclasses of N, add it to SS doesn't matter
;
; SS represents the set that can't be superclasses of N under well formed
; Direct SuperClass Relation.

(defthm collect-superclass-list1-non-mem-cons
  (implies (and (not (mem x (collect-superclass-list1 n cl ss)))
                (superclass-no-loop1 n cl ss))
           (equal (collect-superclass-list1 n cl (cons x ss))
                  (collect-superclass-list1 n cl ss))))

(defcong set-equal equal (superclass-no-loop1 n cl ss) 3)

(defthm superclass-no-loop1-cons
  (implies (superclass-no-loop1 n cl (cons x ss))
           (superclass-no-loop1 n cl ss)))
           


; ---- important obseration II -----
;
; If superclass-no-loop is true, none of the superclasses of N can
; appear in SS.
(defthm mem-collect-superclass-no-loop
  (implies (mem n (collect-superclass-list1 n1 cl ss))
           (not (superclass-no-loop1 n1 cl (cons n ss)))))




; --- this also basically
;   (cdr (collect-superclass-list A cl))
;                   = (collect-superclass-list (super A cl))
(defthm collect-superclass-list1-equal-2
  (implies (and (superclass-no-loop1 n1 cl ss)
                (isClassTerm (class-by-name n1 cl)))
           (equal (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                                     cl 
                                                     (cons n1 ss))
                  (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                                 cl
                                                 ss)))
  :hints (("Goal" :in-theory (disable classSuperClassName isClassTerm
                                      collect-superclass-list1-non-mem-cons)
           :use ((:instance collect-superclass-list1-non-mem-cons
                            (x n1)
                            (n (classSuperClassName (class-by-name n1 cl))))))))


(defthm collect-superclass-list1-equal-1 
  (implies (and (superclass-no-loop1 n1 cl ss)
                (isClassTerm (class-by-name n1 cl)))
           (equal (collect-superclass-list1 n1 cl ss)
                  (cons n1 (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                                     cl 
                                                     ss))))
  :hints (("Goal" :in-theory (disable classSuperClassName)
           :use collect-superclass-list1-equal-2)))



(defthm wff-method-ptr-make-method-ptr
  (implies (wff-method-ptr method-ptr)
           (wff-method-ptr (make-method-ptr any 
                                           (method-ptr-methodname method-ptr)
                                           (method-ptr-args-type  method-ptr)
                                           (method-ptr-returntype
                                            method-ptr))))
  :hints (("Goal" :in-theory (enable make-method-ptr
                                     method-ptr-args-type
                                     wff-method-ptr))))

;;
;; Fri Aug  6 18:53:03 2004: lookupMethod is treated as an internal primitive. 
;; We did not assert strong guard such as all super are loaded. 
;; we probably can. Fri Aug  6 18:54:02 2004

(defun lookupMethod (method-ptr s)
  (declare (xargs :measure (lookupMethod-measure  method-ptr s)
                  :guard (and (wff-method-ptr method-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (if (not (lookupMethod-inv method-ptr s))
      (prog2$ (acl2::cw "lookupMethod-inv violated~%")
              nil) ;; return nil to indicate not found.
    ;; NEED FIX here to deal with method-ptr's classname field is an array
    ;; class!! We could skip to convert it into "java.lang.Object"
    ;; TO BE FIXED. 
    ;;
    ;; ??? Fri Aug  6 15:08:13 2004. not clear now. 
    ;; array has not has method!! 
    ;;
    ;; We have a choice to fix it in jvm-bytecode.lisp so that when one want to
    ;; invoke-xxx on a object of array type, we convert type to
    ;; "java.lang.Object" before invoke this lookupMethod procedure. Thus fix
    ;; in this file is not needed. 
    ;; ??? some annotated in unknown time. Fri Aug  6 15:08:57 2004
    ;;
    ;; This above is for termination purpose only, we could not remove it. 
    ;;
  (let ((method-rep (deref-method method-ptr (instance-class-table s))))
    (if (not (equal method-rep nil))
        method-rep
      (mylet* ((classname (method-ptr-classname method-ptr))
               (class-rep (class-by-name classname (instance-class-table s)))
               (super    (super class-rep)))
        (if (not (isClassTerm class-rep))
            nil ;; return nil
          ;; Need to correctly deal with "java.lang.Object". MORE WORK!!
          ;; HOWEVER this is HARD, converting an array type to java.lang.Object
          ;; we may have problem of proving termination. We need stronger
          ;; invariant that java.lang.Object's super is nil. 
          ;; or using a seperate function in looking up method in
          ;; java.lang.Object!!
          ;; TO BE FIXED!!  ?? This is related to the previous comment? 
          ;; consider solved? 
          (if (equal super "")
              nil
            (lookupMethod (make-method-ptr super
                                           (method-ptr-methodname method-ptr)
                                           (method-ptr-args-type  method-ptr)
                                           (method-ptr-returntype method-ptr))
                          s))))))))



;; this make involves changing state. 
;; doesn't check for access permissions. 
;;
;; need a mechanism to propagate the exception back to the interpreter loop to
;; properly handle it. 
;;
;; The problem is that not access control checking is done.
;;

(defun hasAccessToMethod (from method s)
  (declare (ignore from method s))
  t)


;; Fri Aug  6 15:33:54 2004. We need to prove 
;;
;; when lookupMethod returns non-nil, it is a well formed method decl! 
;; 
;; We could insert a more complicated check of well-method-decl here.  however
;; to be more close to real jvm implementation, we use an equivalent concept
;; in this concept!! 
;;
;; Comment: this show our difference with other people's work. I assume. 
;;

(defthm searchMethod-in-wff-class-method-decls
  (implies (and (searchMethod method-ptr methods)
                (wff-class-method-decls methods))
           (wff-method-decl (searchMethod method-ptr methods))))

;; (defthm wff-instance-class-table-strong-bound-implies-wff-class-rep-strong
;;   (implies (and (wff-instance-class-table-strong cl)
;;                 (consp (class-by-name name cl)))
;;            (wff-class-rep-strong (class-by-name name cl))))


(defthm wff-instance-class-table-strong-bound-implies-wff-class-rep-strong
  (implies (and (wff-instance-class-table-strong cl)
                (class-by-name name cl))
           (wff-class-rep-strong (class-by-name name cl))))

(defthm wff-methods-methods-if-class-rep-strong
  (implies (wff-class-rep-strong crep)
           (wff-class-method-decls (methods crep))))

  


(defthm
  wff-instance-class-table-s-implies-lookup-return-well-formed-method-decl
  (implies (and (lookupMethod method-ptr s)
                (wff-instance-class-table-strong (instance-class-table s)))
           (wff-method-decl (lookupMethod method-ptr s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable wff-method-decl methods-s methods))))


(defthm loader-inv-preserved-by-load_array_class
  (implies (loader-inv s)
           (loader-inv (load_array_class base-type s))))


;; (defthm
;;   wff-instance-class-table-s-implies-lookup-return-well-formed-method-decl
;;   (implies (and (lookupMethod method-ptr s)
;;                 (loader
;;                 (no-fatal-error? 
;;            (wff-method-decl (lookupMethod method-ptr s)))))


(defthm loader-inv-implies-wff-intance-class-table-strong
  (implies (loader-inv s)
           (wff-instance-class-table-strong (instance-class-table s))))



(local (in-theory (disable wff-method-decl)))


;; we need some theorems to say how ResolveClassName does not affect the
;; callstack to speed up the proof of the following. 
;; Fri Aug  6 15:42:07 2004. 
;;
;; These proofs will be based on the properties of load_class_x
;;


(defthm load_class2-does-not-change-thread-table
  (equal (thread-table (load_class2 any s))
         (thread-table s)))

(defthm load_class-does-not-change-thread-table
  (equal (thread-table (load_class_x any s seen mode))
         (thread-table s)))

(defthm load_array_class2-does-not-change-thread-table
  (equal (thread-table (load_array_class2 any s))
         (thread-table s)))

(defthm load_array_class-does-not-change-thread-table
  (equal (thread-table (load_array_class any s))
         (thread-table s)))

(defthm resolveClassReference-does-not-change-thread-table
  (equal (thread-table (resolveClassReference any s))
         (thread-table s)))


(defthm load_class2-does-not-change-current-thread
  (equal (current-thread (load_class2 any s))
         (current-thread s)))

(defthm load_class-does-not-change-current-thread
  (equal (current-thread (load_class_x any s seen mode))
         (current-thread s)))

(defthm load_array_class2-does-not-change-current-thread
  (equal (current-thread (load_array_class2 any s))
         (current-thread s)))

(defthm load_array_class-does-not-change-current-thread
  (equal (current-thread (load_array_class any s))
         (current-thread s)))


(defthm resolveClassReference-does-not-change-current-thread
  (equal (current-thread (resolveClassReference any s))
         (current-thread s)))

(defthm current-frame-equal
  (equal (current-frame (resolveClassReference any s))
         (current-frame s)))

(local (in-theory (disable method-ptr)))

;(i-am-here)

(defun resolveMethodReference (method-ptr needStatic? s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-method-ptr method-ptr)
                              (resolveClassReference-guard s))))
  (mylet* ((classname (method-ptr-classname method-ptr))
           (new-s (resolveClassReference classname s))
        ;; cause necessary classes to load. (all super, all interfaces, 
        ;; *** need to add exception handling here ***!! 
           (thisMethod (lookupMethod method-ptr new-s)))
    ;; we chose not to check whether the constant pool contain the
    ;; referenc is an interfaceMethod. 
    #|
    ;; if (  (((thisTag & CP_CACHEMASK) == CONSTANT_InterfaceMethodref) &&
    ;;           !(thisClass->accessFlags & ACC_INTERFACE))
    ;;        ||
    ;;          (((thisTag & CP_CACHEMASK) == CONSTANT_Methodref) &&
    ;;            (thisClass->accessFlags & ACC_INTERFACE))) {
    ;;        /* "Bad methodref" */
    ;;        fatalError(KVM_MSG_BAD_FIELD_OR_METHOD_REFERENCE);
    ;; }
    |#
    (if (pending-exception new-s)
        (mv nil new-s)
      (if thisMethod
          (if (not needStatic?)
              (if (mem '*static* (method-accessflags thisMethod))
                  (mv nil (fatalError "use invokevirtual to call static methods" new-s))
                (if (hasAccessToMethod (current-class new-s) thisMethod s)
                    (mv thisMethod new-s)
                  (mv nil (state-set-pending-exception-safe
                           "java.lang.IllegalAccessException" new-s))))
            (if (not (mem '*static* (method-accessflags thisMethod)))
                (mv nil (fatalError "use invokestatic to call a non static methods" new-s))
              (if (hasAccessToMethod (current-class new-s) thisMethod s)
                  (mv thisMethod new-s)
                (mv nil (state-set-pending-exception-safe
                         "java.lang.IllegalAccessException" new-s)))))
        (mv nil (state-set-pending-exception-safe 
                 "java.lang.NoSuchMethodError" new-s))))))

;; SpecialMethod such as <init> <clinit> is not using the dynamic binding
;; methods as it is in the resolveMethodReference 
;; it is defined here.

;;;

(defun getSpecialMethod1 (mptr methods)
  (declare (xargs :guard (and (wff-method-ptr mptr)
                              (wff-class-method-decls methods))))
  (if (not (consp methods))
      nil
  (let ((methodname  (method-ptr-methodname mptr))
        (args        (method-ptr-args-type mptr))
        (return-type (method-ptr-returntype mptr))
        (this-method (car methods)))
    (if (and (equal (method-methodname this-method) methodname)
             (equal (method-args  this-method)  args)
             (equal (method-returntype this-method) return-type))
        this-method
      (getSpecialMethod1 mptr (cdr methods))))))


(local (in-theory (disable methods wff-class-method-decls)))

(local (in-theory (enable class-loaded?)))


;; this version shouldn't throw exceptions.
;; doesn't do dynamic method binding.
(defun getSpecialMethod (mptr s)
  (declare (xargs :guard (and (wff-method-ptr mptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table-strong
                               (instance-class-table s))
                              (class-loaded? (method-ptr-classname mptr) s))))
  (let* ((classname  (method-ptr-classname mptr))
         (class-rep  (class-by-name classname (instance-class-table s)))
         (methods    (methods class-rep)))
    (getSpecialMethod1 mptr methods)))

(local (in-theory (disable class-loaded?)))

;; Fri Aug  6 18:18:38 2004 what happen if the class-name is not found? 
;;

;----------------------------------------------------------------------

;(i-am-here)
;(acl2::set-verify-guards-eagerness 2)

;----- Field Resolution -------
;;(include-book "../M6-DJVM-shared/jvm-class-table")

(defun static-field-size (static-field-rep)
  (declare (xargs :guard (wff-static-field static-field-rep)))
  (type-size (static-field-fieldtype static-field-rep)))
  

;; (defun execute-getstatic1 (field-rep s)
;;   (if (equal (static-field-size field-rep) 2)
;;       (pushLong (static-field-fieldvalue field-rep) s)
;;     (pushStack (static-field-fieldvalue field-rep) s)))
;;
;; Example: Sun Dec 28 19:08:30 2003               


;; (fieldCP "detailMessage" "java.lang.Throwable" (class "java.lang.String"))))

(defun wff-fieldCP (fieldCP)
  (and (true-listp fieldCP)
       (equal (len fieldCP) 4)
       (equal (car fieldCP) 'fieldCP)
       (wff-type-rep (nth 3 fieldCP))))

(defun fieldCP-classname (fieldCP)
  (declare (xargs :guard (wff-fieldCP fieldCP)))
  (nth 2 fieldCP))

(defun fieldCP-fieldname (fieldCP)
  (declare (xargs :guard (wff-fieldCP fieldCP)))
  (nth 1 fieldCP))

(defun fieldCP-fieldtype (fieldCP)
  (declare (xargs :guard (wff-fieldCP fieldCP)))
  ;; Mon May 17 23:18:48 2004 normalized type-rep strip the class
  (normalize-type-rep (nth 3 fieldCP)))

(defun make-field-ptr (classname fieldname type)
  (list 'field-ptr classname fieldname type))

(defun wff-field-ptr (field-ptr)
  (and (true-listp field-ptr)
       (equal (len field-ptr) 4)
       (equal (car field-ptr) 'field-ptr)))

(defun field-ptr-classname (field-ptr)
  (declare (xargs :guard (wff-field-ptr field-ptr)))
  (nth 1 field-ptr))

(defun field-ptr-fieldname (field-ptr)
  (declare (xargs :guard (wff-field-ptr field-ptr)))
  (nth 2 field-ptr))

(defun field-ptr-type (field-ptr)
  (declare (xargs :guard (wff-field-ptr field-ptr)))
  (nth 3 field-ptr))

(defun fieldCP-to-field-ptr (fieldCP)
  (declare (xargs :guard (wff-fieldCP fieldCP)))
  (make-field-ptr (fieldCP-classname fieldCP)
                  (fieldCP-fieldname fieldCP)
                  (fieldCP-fieldtype fieldCP)))

;----------------------------------------------------------------------

;; Mon May 17 23:28:02 2004 guard verify those function.


(defun searchStaticFields (field-ptr fields)
  (declare (xargs :guard (and (wff-field-ptr field-ptr)
                              (wff-static-fields-x fields))))
  (if (not (consp fields))
      nil
    (if (and (equal (field-ptr-classname field-ptr) (static-field-classname (car fields)))
             (equal (field-ptr-fieldname field-ptr) (static-field-fieldname (car fields)))
             (equal (field-ptr-type field-ptr)      (static-field-fieldtype
                                                     (car fields))))
        (car fields)
      (searchStaticFields field-ptr (cdr fields)))))


(defun deref-static-field-guard (field-ptr s)
  (mylet* ((classname (field-ptr-classname field-ptr))
           (cl (class-table s))
           (icl (instance-class-table s))
           (class-rep (class-by-name classname icl))
           (fields (static-fields class-rep)))
          (and (wff-field-ptr field-ptr)
               (wff-state s)
               (wff-class-table cl)
               (wff-instance-class-table icl)
               (wff-class-rep class-rep)
               (wff-static-fields-x fields))))



(defun deref-static-field (field-ptr s)
  (declare (xargs :guard (deref-static-field-guard field-ptr s)))
  (mylet* ((classname (field-ptr-classname field-ptr))
           (cl (class-table s))
           (icl (instance-class-table s))
           (class-rep (class-by-name classname icl))
           (fields (static-fields class-rep)))
          (searchStaticFields field-ptr fields)))


(defthm field-ptr-accessor 
  (let ((fpr (make-field-ptr c f tp)))
    (and (equal (field-ptr-classname fpr) c)
         (equal (field-ptr-fieldname fpr) f)
         (equal (field-ptr-type fpr) tp))))


(in-theory (disable make-field-ptr field-ptr-classname field-ptr-fieldname field-ptr-type))


;; termination proofs.

(acl2::set-verify-guards-eagerness 0)
(defun lookupStaticField-measure (field-ptr s)
  (let ((n1  (field-ptr-classname field-ptr))
        (cl  (instance-class-table s)))
  (len (collect-superclass-list n1 cl))))

;;(acl2::set-verify-guards-eagerness 2) ;; Fri Jun 18 16:58:14 2004
;; Fri Jun 18 17:09:50 2004

(acl2::set-verify-guards-eagerness 2)

(defun lookupStaticField-inv (field-ptr s)
  (declare (xargs :guard (and (wff-field-ptr field-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (superclass-no-loop (field-ptr-classname field-ptr) (instance-class-table s)))


;(skip-proofs (verify-guards lookupStaticField-inv))

;; need the following invariant for it to be correct! 
;; the superclass of any loaded class is loaded. 

;; we need some strong property!! all super class are loaded!  Tue May 18
;; 00:13:45 2004
;;


;; ;; (defun lookupStaticField-guard1 (cl)
;; ;;    (if (not (consp cl)) t
;; ;;      (and (wff-class-rep (car cl))
;; ;;           (wff-static-fields-x (static-fields (car cl)))
;; ;;           (lookupStaticField-guard1 (cdr cl)))))


;; ;; ;; Fri Aug  6 21:35:51 2004. we could just assert 
;; ;; ;; wff-instance-class-table-strong!! 


;; ;; (defun all-loaded-weak (l cl)
;; ;;   (declare (xargs :guard (wff-instance-class-table cl)))
;; ;;   (if (not (consp l)) t
;; ;;     (and (wff-class-rep (class-by-name (car l) cl))
;; ;;          (all-loaded-weak (cdr l) cl))))
      

;; ;; (defun lookupStaticField-guard (field-ptr s)
;; ;;   (and (wff-field-ptr field-ptr)
;; ;;        (wff-state s)
;; ;;        (wff-class-table (class-table s))
;; ;;        (wff-instance-class-table (instance-class-table s))
;; ;;        (lookupStaticField-guard1 (instance-class-table s))
;; ;;        (all-loaded-weak (collect-superclass-list 
;; ;;                          (field-ptr-classname field-ptr)
;; ;;                          (instance-class-table s))
;; ;;                         (instance-class-table s))))
                          

;; ;; (local (in-theory (disable wff-class-rep)))       


;; ;; (defthm all-loaded-weak-implies-wff-class-rep
;; ;;   (implies (and (all-loaded-weak l cl)
;; ;;                 (mem x l))
;; ;;            (wff-class-rep (class-by-name x cl))))


;; ;; (defthm mem-n-collect-superclass-list1
;; ;;   (implies (isClassTerm (class-by-name n cl))
;; ;;            (mem n (collect-superclass-list1 n cl nil)))
;; ;;   :hints (("Goal" :expand (collect-superclass-list1 n cl nil))))
           


;; ;; (defthm all-loaded-weak-implies-wff-class-rep-specific
;; ;;   (implies (and (all-loaded-weak (collect-superclass-list1 n cl nil) cl)
;; ;;                 (isClassTerm (class-by-name n cl)))
;; ;;            (wff-class-rep (class-by-name n cl))))


;; ;; (defthm mem-c-cl-is-class-term
;; ;;   (implies (isClassTerm (class-by-name n cl))
;; ;;            (mem (class-by-name n cl) cl)))


;; ;; (defthm wff-static-fields-x-if-mem-of-lookupStaticField-guard1
;; ;;   (implies (and (lookupStaticField-guard1 cl)
;; ;;                 (mem class-rep cl))
;; ;;            (wff-static-fields-x (static-fields class-rep))))



;; ;; (defthm wff-static-fields-x-if-mem-of-lookupStaticField-guard1-specific
;; ;;   (implies (and (lookupStaticField-guard1 cl)
;; ;;                 (isClassTerm (class-by-name n cl)))
;; ;;            (wff-static-fields-x (static-fields (class-by-name n cl)))))
  


;; (defthm all-loaded-weak-implies-wff-class-rep-specific
;;   (implies (and (all-loaded-weak (collect-superclass-list1 n cl nil) cl)
;;                 (isClassTerm (class-by-name n cl)))
;;            (wff-class-rep (class-by-name n cl))))

;; (defun lookupStaticField (field-ptr s)
;;   (declare (xargs :measure (lookupStaticField-measure field-ptr s)
;;                   :guard (lookupStaticField-guard field-ptr s)
;;                   :guard-hints (("Goal" :in-theory (disable isClassTerm make-field-ptr)))))
;;   (if (not (lookupStaticField-inv field-ptr s))
;;       (prog2$ (acl2::cw "lookupStaticField-inv violated~%")
;;               nil) ;; return nil to indicate not found.
;;     (let ((field-rep (deref-static-field field-ptr s)))
;;       (if (not (equal field-rep nil))
;;           field-rep
;;         (let* ((classname (field-ptr-classname field-ptr))
;;                (class-rep (class-by-name classname (instance-class-table s)))
;;                (super     (super class-rep)))
;;           (if (not (isClassTerm class-rep))
;;               nil
;;             (if (equal super "") 
;;                 nil
;;               (lookupStaticField (make-field-ptr super
;;                                                  (field-ptr-fieldname field-ptr)
;;                                                  (field-ptr-type      field-ptr))
;;                                  s))))))))

;;;; Tue May 18 00:52:47 2004. this above version does not check whether class
;;;; exists before search for the field!! fixed. 

(defthm wff-field-ptr-make-field-ptr
  (wff-field-ptr (make-field-ptr classname fieldname type))
  :hints (("Goal" :in-theory (enable make-field-ptr))))


;;;
;;; In lookupMethod, we did not assert that all super are loaded!! 
;;; Maybe we should!! Fri Aug  6 18:36:27 2004
;;; 

(defthm wff-instance-class-table-wff-class-rep-strong
  (implies (and (class-by-name name cl)
                (wff-instance-class-table-strong cl))
           (wff-class-rep-strong (class-by-name name cl))))


(defthm wff-class-rep-strong-implies-wff-static-field-x
  (implies (wff-class-rep-strong crep)
           (wff-static-fields-x (static-fields crep))))

;(i-am-here)

(local (in-theory (disable static-fields)))

(defun lookupStaticField (field-ptr s)
  (declare (xargs :measure (lookupStaticField-measure field-ptr s)
                  :guard (and (wff-field-ptr field-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table-strong
                               (instance-class-table s)))))
  (if (not (lookupStaticField-inv field-ptr s))
      (prog2$ (acl2::cw "lookupStaticField-inv violated~%")
              nil) ;; return nil to indicate not found.
    (mylet* ((classname (field-ptr-classname field-ptr))
             (class-rep (class-by-name classname (instance-class-table s)))
             (super     (super class-rep)))
      (if (not (isClassTerm class-rep))  nil
        (let ((field-rep (deref-static-field field-ptr s)))
          (if (not (equal field-rep nil))
              field-rep
            (if (equal super "") 
                nil
              (lookupStaticField (make-field-ptr super
                                                 (field-ptr-fieldname field-ptr)
                                                 (field-ptr-type      field-ptr))
                                 s))))))))


;; Fri Aug  6 21:45:09 2004. Chose to not to assert that all super are loaded!! 
;; But when this is called, we know loader-inv, which will entail that all
;; super are loaded!! 


;; ;; (defun lookupStaticField (field-ptr s)
;; ;;   (declare (xargs :measure (lookupStaticField-measure field-ptr s)
;; ;;                   :guard (lookupStaticField-guard field-ptr s)
;; ;;                   :guard-hints (("Goal" :in-theory (disable isClassTerm
;; ;;                                                              static-fields)))))
;; ;;   (if (not (lookupStaticField-inv field-ptr s))
;; ;;       (prog2$ (acl2::cw "lookupStaticField-inv violated~%")
;; ;;               nil) ;; return nil to indicate not found.
;; ;;     (mylet* ((classname (field-ptr-classname field-ptr))
;; ;;              (class-rep (class-by-name classname (instance-class-table s)))
;; ;;              (super     (super class-rep)))
;; ;;       (if (not (isClassTerm class-rep))  nil
;; ;;         (let ((field-rep (deref-static-field field-ptr s)))
;; ;;           (if (not (equal field-rep nil))
;; ;;               field-rep
;; ;;             (if (equal super "") 
;; ;;                 nil
;; ;;               (lookupStaticField (make-field-ptr super
;; ;;                                                  (field-ptr-fieldname field-ptr)
;; ;;                                                  (field-ptr-type      field-ptr))
;; ;;                                  s))))))))



;; ;; (defun lookupStaticField (field-ptr s)
;; ;;   (declare (xargs :measure (lookupStaticField-measure field-ptr s)
;; ;;                   :guard (and (wff-field-ptr field-ptr)
;; ;;                               (wff-state s)
;; ;;                               (wff-class-table (class-table s))
;; ;;                               (wff-instance-class-table (instance-class-table s)))))
;; ;;   (if (not (lookupStaticField-inv field-ptr s))
;; ;;       (prog2$ (acl2::cw "lookupStaticField-inv violated~%")
;; ;;               nil) ;; return nil to indicate not found.
;; ;;     (mylet* ((classname (field-ptr-classname field-ptr))
;; ;;              (class-rep (class-by-name classname (instance-class-table s)))
;; ;;              (super     (super class-rep)))
;; ;;       (if (not (isClassTerm class-rep))  nil
;; ;;         (let ((field-rep (deref-static-field field-ptr s)))
;; ;;           (if (not (equal field-rep nil))
;; ;;               field-rep
;; ;;             (if (equal super "") 
;; ;;                 nil
;; ;;               (lookupStaticField (make-field-ptr super
;; ;;                                                  (field-ptr-fieldname field-ptr)
;; ;;                                                  (field-ptr-type      field-ptr))
;; ;;                                  s))))))))


(defun hasAccessToField (from field s)
  (declare (ignore from field s))
  t)

(defthm fieldCP-to-field-ptr-wff-field-ptr
  (implies (wff-fieldCP fieldcp)
           (wff-field-ptr (fieldCP-to-field-ptr fieldcp))))


;; (defthm loader-inv-implies-all-loaded-weak

;; (defthm lookupStaticField-guard1-implied-by-wff-ins
  


(defun resolveStaticFieldReference (fieldCP s)
   (declare (xargs :guard (and (wff-fieldCP fieldCP)
                                 (resolveClassReference-guard s))
                   :guard-hints (("Goal" :in-theory (disable 
                                                     current-frame-guard
                                                     current-method-ptr
                                                     field-ptr-classname
                                                     fieldCP-to-field-ptr
                                                     wff-field-ptr)))))
                                                     ;;resolveClassReference-guard
                                                     ;;lookupStaticField-guard)))))
                              ;; Some assertions about some property of
                              ;; external class table is still missing!!  We
                              ;; need to show when no pending exception then
                              ;; all super class has been loaded!!  non
                              ;; trivial!!
   ;; Fri Aug  6 21:19:45 2004. loader-inv will provide that when we know class
   ;; is loaded and there is no fatal error. 
  (let* ((field-ptr (fieldCP-to-field-ptr fieldCP))
         (new-s (resolveClassReference (field-ptr-classname field-ptr) s)))
    (if (not (no-fatal-error? s))
        (mv nil s)
      (if (pending-exception new-s)
          (mv nil new-s)
        (let ((sfield (lookupStaticField field-ptr new-s)))
          (if (not sfield)
              (mv nil new-s)
            (if (not (hasAccessToField (current-class s) sfield new-s))
                (mv nil (state-set-pending-exception-safe
                         "java.lang.IllegalAccessException" new-s))
              (mv sfield new-s))))))))

;;; skipped the guard verification of this. 

;; updated with access checking          

(defun static-field-class-rep (static-field-rep s)
  (declare (xargs :guard (and (wff-static-field static-field-rep)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (class-by-name (static-field-classname static-field-rep)
                 (instance-class-table s)))


; --- above static field resolution ----
; --- below field resolution        ----

;;; the following is similar!! 

;(acl2::set-verify-guards-eagerness 2)

(defun searchFields-guard (field-ptr fields)
  (and (wff-field-ptr field-ptr)
       (wff-fields-x fields)))

(defun searchFields (field-ptr fields)
  (declare (xargs :guard (searchFields-guard field-ptr fields)))
  (if (not (consp fields))
      nil
    (if (and (equal (field-ptr-classname field-ptr) (field-classname (car fields)))
             (equal (field-ptr-fieldname field-ptr) (field-fieldname (car fields)))
             (equal (field-ptr-type field-ptr)      (field-fieldtype (car fields))))
        (car fields)
      (searchFields field-ptr (cdr fields)))))



(defun deref-field-guard (field-ptr s)
  (mylet* ((classname (field-ptr-classname field-ptr))
           (cl (class-table s))
           (icl (instance-class-table s))
           (class-rep (class-by-name classname icl))
           (fields (fields class-rep)))
          (and (wff-field-ptr field-ptr)
               (wff-state s)
               (wff-class-table cl)
               (wff-instance-class-table icl)
               (wff-class-rep class-rep)
               (wff-fields-x fields))))




(defun deref-field (field-ptr s)
  (declare (xargs :guard (deref-field-guard field-ptr s)))
  (let* ((classname (field-ptr-classname field-ptr))
         (class-rep (class-by-name classname (instance-class-table s)))
         (fields    (fields class-rep)))
    (searchFields field-ptr fields)))

;; need the following invariant for it to be correct! 
;; the superclass of any loaded class is loaded. 

;; termination proofs.

(acl2::set-verify-guards-eagerness 0)

(defun lookupField-measure (field-ptr s)
  (let ((n1  (field-ptr-classname field-ptr))
        (cl  (instance-class-table s)))
  (len (collect-superclass-list n1 cl))))


(acl2::set-verify-guards-eagerness 2)

(defun lookupField-inv (field-ptr s)
  (declare (xargs :guard (and (wff-field-ptr field-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (superclass-no-loop (field-ptr-classname field-ptr) (instance-class-table s)))

;; (defun lookupField-guard1 (cl)
;;   (if (not (consp cl)) t
;;     (and (wff-class-rep (car cl))
;;          (wff-static-fields (fields (car cl)))
;;          (lookupField-guard1 (cdr cl)))))


;; (defun lookupField-guard (field-ptr s)
;;   (and (wff-field-ptr field-ptr)
;;        (wff-state s)
;;        (wff-class-table (class-table s))
;;        (wff-instance-class-table (instance-class-table s))
;;        (lookupField-guard1 (instance-class-table s))
;;        (all-loaded-weak (collect-superclass-list 
;;                          (field-ptr-classname field-ptr)
;;                          (instance-class-table s))
;;                         (instance-class-table s))))

;; ;; (skip-proofs 
;; ;;  ;; need something about all-loaded-weak Fri Jun 18 20:37:10 2004
;; ;;  ;;                          
;; ;;  (defun lookupField (field-ptr s)
;; ;;    (declare (xargs :measure (lookupField-measure field-ptr s)
;; ;;                    :guard (lookupField-guard field-ptr s)
;; ;;                    :guard-hints (("Goal" :in-theory (disable isClassTerm
;; ;;                                                              fields)))))
;; ;;   (if (not (lookupField-inv field-ptr s))
;; ;;       (prog2$ (acl2::cw "lookupField-inv violated~%")
;; ;;               nil) ;; return nil to indicate not found.
;; ;;     ;;
;; ;;     ;; We also need some fix to deal with situations when field-ptr's 
;; ;;     ;; class is an array class.
;; ;;     ;; We probably can fix it in getfield, putfield and getstatic etc. 
;; ;;     ;; Mmm. We probably don't need to change anything because, array class's
;; ;;     ;; super is always java.lang.Object, and we know java.lang.Object does not
;; ;;     ;; contain a field!!
;; ;;     ;;
;; ;;     ;; This is a different from invokeinterface, invokevirtual!
;; ;;     ;; 
;; ;;     (let ((field-rep (deref-field field-ptr s)))
;; ;;       (if (not (equal field-rep nil))
;; ;;           field-rep
;; ;;         (let* ((classname (field-ptr-classname field-ptr))
;; ;;                (class-rep (class-by-name classname (instance-class-table s)))
;; ;;                (super     (super class-rep)))
;; ;;           (if (not (isClassTerm class-rep))
;; ;;               nil
;; ;;             (if (equal super "") 
;; ;;                 nil
;; ;;               (lookupField (make-field-ptr super
;; ;;                                            (field-ptr-fieldname field-ptr)
;; ;;                                            (field-ptr-type      field-ptr))
;; ;;                            s)))))))))

;; Fri Aug  6 22:22:35 2004. Get rid of all-loaded-weak predicate

(defthm wff-fields-x-equal-wff-class-fields
  (iff (wff-class-fields fields)
       (wff-fields-x fields)))

(defthm wff-class-rep-strong-implies-wff-fields-x
  (implies (wff-class-rep-strong crep)
           (wff-fields-x (fields crep)))
  :hints (("Goal" :in-theory (enable wff-class-fields wff-fields-x))))

(local (in-theory (disable fields)))


(defun lookupField (field-ptr s)
  (declare (xargs :measure (lookupField-measure field-ptr s)
                  :guard (and (wff-field-ptr field-ptr)
                              (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table-strong
                               (instance-class-table s)))))
  (if (not (lookupField-inv field-ptr s))
      (prog2$ (acl2::cw "lookupField-inv violated~%")
              nil) ;; return nil to indicate not found.
    ;;
    ;; We also need some fix to deal with situations when field-ptr's 
    ;; class is an array class.
    ;; We probably can fix it in getfield, putfield and getstatic etc. 
    ;; Mmm. We probably don't need to change anything because, array class's
    ;; super is always java.lang.Object, and we know java.lang.Object does not
    ;; contain a field!!
    ;;
    ;; This is a different from invokeinterface, invokevirtual!
    ;;
    ;;; Fri Aug  6 22:39:14 2004 
    ;; 
    (mylet* ((classname (field-ptr-classname field-ptr))
             (class-rep (class-by-name classname (instance-class-table s)))
             (super     (super class-rep)))
            (if (not (isClassTerm class-rep))
                nil
              (let ((field-rep (deref-field field-ptr s)))
                (if (not (equal field-rep nil))
                    field-rep
                  (if (equal super "") 
                      nil
                    (lookupField (make-field-ptr super
                                                 (field-ptr-fieldname field-ptr)
                                                 (field-ptr-type      field-ptr))
                                 s))))))))





;; Notice here the lookupField-inv is an invariant of valid class table. Which
;; should be a part of consistent-state. It is preserved by class loader which
;; we have already proved. 
;; (i-am-here)

(defun resolveFieldReference (fieldCP s)
   (declare (xargs :guard (and (wff-fieldCP fieldCP)
                               (resolveClassReference-guard s))
                   :guard-hints (("Goal" :in-theory (disable 
                                                     current-frame-guard
                                                     current-method-ptr
                                                     field-ptr-classname
                                                     fieldCP-to-field-ptr
                                                     wff-field-ptr)))))
   ;; we need to prove when resolveClassReference returns with no 
   ;; exception. lookupField is safe!! 
   ;;
  (let* ((field-ptr (fieldCP-to-field-ptr fieldCP))
         (new-s (resolveClassReference (field-ptr-classname field-ptr) s)))
    (if (pending-exception new-s)
        (mv nil new-s)
      (let ((field (lookupField field-ptr new-s)))
        (if (not field)
            (mv nil new-s)
          (if (not (hasAccessToField (current-class s) field new-s))
              (mv nil (state-set-pending-exception-safe
                       "java.lang.IllegalAccessException" new-s))
            (mv field new-s)))))))


;; (i-am-here)


;---- functions for support call back.

;;(acl2::set-verify-guards-eagerness 0)

(defun make-callback-func-ptr (funcname)
  (list 'call-back funcname))

(defun wff-call-back (call-back)
  (and (true-listp call-back)
       (equal (len call-back) 2)
       (equal (car call-back) 'call-back)))

(defun callback-funcname (call-back)
  (declare (xargs :guard (wff-call-back call-back)))
  (nth 1 call-back))

(defun callback-func-ptr? (value)
  (and (consp value)
       (true-listp value)
       (equal (length value) 2)
       (equal (car value) 'call-back)))


(defun clinitMethod-ptr (classname)
  (make-method-ptr classname "<clinit>" nil 'void))

(defun initMethod-ptr (classname)
  (make-method-ptr classname "<init>" nil 'void))

(defun RunCustomCode-method-ptr ()
  (make-method-ptr "java.lang.Class" "runCustomCode" nil 'void))














