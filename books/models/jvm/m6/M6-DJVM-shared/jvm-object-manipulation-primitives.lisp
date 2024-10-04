(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-class-table")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-class-hierachy-aux")
(include-book "../M6-DJVM-shared/jvm-obj")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives")

(acl2::set-verify-guards-eagerness 2)
;;; Still problematic!! guard verification!! 
;;; Tue Jan 13 14:36:57 2004

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

;;; moved to jvm-type-value.lisp

(defun make-field-value-pair (field-name value)
  (cons field-name value))


(defun make-immediate-field-bindings (class-name field-bindings)
  (cons class-name field-bindings))


;; initialization will actually fill in default values for those
;; fields. however in build-class-fields-bindings

(defun build-class-fields-bindings (class-fields)
  (declare (xargs :guard (wff-class-fields class-fields)))
  (if (endp class-fields)
      nil
    (let* ((field (car class-fields))
           (field-name (field-fieldname field))
           (field-type (field-fieldtype field)))
    (cons (make-field-value-pair field-name (default-value field-type))
          (build-class-fields-bindings (cdr class-fields))))))
  
;; too much efforts in defining those guard checks!! 
;; (acl2::set-verify-guards-eagerness 0)

(defun build-immediate-instance-data-guard (class-name s)
  (and (wff-state s)
       (wff-class-table (class-table s))
       (wff-instance-class-table (instance-class-table s))
       (wff-class-rep (class-by-name class-name
                                     (instance-class-table s)))
       (wff-class-fields (fields (class-by-name
                                  class-name
                                  (instance-class-table s))))))

(defun build-immediate-instance-data (class-name S)
  (declare (xargs :guard (build-immediate-instance-data-guard class-name s)))
  (let* ((dcl (instance-class-table S))
         (field-bindings 
          (build-class-fields-bindings 
           (fields (class-by-name class-name dcl)))))
    (mv (make-immediate-field-bindings class-name field-bindings) S)))


(defun build-a-java-visible-instance-data-guard (class-names s)
  (if (not (consp class-names))
      t
    (and (build-immediate-instance-data-guard (car class-names) s)
         (build-a-java-visible-instance-data-guard (cdr class-names) s))))
        
(defun build-a-java-visible-instance-data (class-names S)
  (declare (xargs :guard (build-a-java-visible-instance-data-guard class-names s)))
  (if (not (consp class-names))
      (mv nil S)
    (mv-let (immediate-instance-data new-S)
            (build-immediate-instance-data (car class-names) S)
          (mv-let (remaining-instance-data new-S2)
                  (build-a-java-visible-instance-data (cdr class-names) new-S)
              (mv (cons immediate-instance-data remaining-instance-data)
                   new-S2)))))

(defun make-java-lang-Object-java-visible-part (s)
  (mv (list (cons "java.lang.Object" nil))
      s))

;------------
;; contains definition of collect-superclass-list and 
;; it's termination argument.

;; assume all superclasses are loaded already.

;; forget about guard verification for now!! 
;;; Tue Jan 13 17:43:11 2004

;;(acl2::set-verify-guards-eagerness 0) 

;; many guard will not be verified. 
;;
 
;; This part will be shared, thus we make it guard verify correctly!

;;; Tue Jan 13 20:09:15 2004. The guard is complicated!!
;;;; Let's first write out consistent-state, we could use that as a guard. 


;(i-am-here)


(defun build-a-java-visible-instance-guard (classname S)
  (and (wff-state s)
       (wff-class-table (class-table s))
       (wff-env (env s))
       (wff-instance-class-table (instance-class-table s))
       (wff-static-class-table (external-class-table s))
       (equal (collect-superclass-list classname (instance-class-table s))
              (collect-superclassname classname (external-class-table s)))
       ;; Wed Jun 23 17:58:02 2004. modified 
       ;; need to move definition of collect-superclassname to here. 
       (build-a-java-visible-instance-data-guard
        (collect-superclass-list classname
                                 (instance-class-table s)) s)))

;;; Tue Jul  6 11:57:15 2004
;;; I could add a no-fatal-error assertion here. 
;;; then I have to add it everywhere, which is a pain.

(defun build-a-java-visible-instance (classname S)
  (declare (xargs :guard (build-a-java-visible-instance-guard classname S)))
  (mylet* ((cl (instance-class-table S))
           (classnames (collect-superclass-list classname cl)))
    (if (equal classname "java.lang.Object")
        (make-java-lang-Object-java-visible-part S)
      (build-a-java-visible-instance-data classnames S))))
  


;;;
;;; Wed Mar 31 12:52:20 2004

(defun jvp-access-field-guard (classname fieldname obj)
  (and (alistp obj)
       (bound? classname obj)
       (alistp (binding classname obj))
       (bound? fieldname (binding classname obj))))

(defun jvp-setfield (classname fieldname value obj) 
  (declare (xargs :guard (jvp-access-field-guard classname fieldname obj)))
  (bind classname 
        (bind fieldname value
              (binding classname obj))
        obj))   ;; about how to change the java-visible-portion.

(defun jvp-getfield (classname fieldname obj)
  (declare (xargs :guard (jvp-access-field-guard classname fieldname obj)))
  (binding fieldname 
           (binding classname obj)))

;;; Wed Mar 31 12:54:02 2004. Very weak guard!! 
;;; WE can make it stronger, but it potentially will introduce changes to guard
;;; of other functions!! 
;;;

;;; (acl2::set-verify-guards-eagerness 2)

(defun build-common-info (of-class)
  (make-common-info 0 (new-monitor) of-class)) ;; ha code is same 

(defun build-INSTANCE-specific-info ()
  (make-INSTANCE-specific-info))

;; add accessor to ... 
(defun build-an-instance (classname S)
  (declare (xargs :guard (build-a-java-visible-instance-guard classname S)))
  (mv-let (java-visible-portion new-S) 
          (build-a-java-visible-instance classname S)
          (let ((commoninfo           (build-common-info classname))
                (specificinfo         (build-INSTANCE-specific-info)))
            (mv (make-object commoninfo specificinfo java-visible-portion)  new-S))))

;; so far only deal with building one instance 


(defun build-ARRAY-specific-info (the-internal-array bound)
  (list 'specific-info 'ARRAY the-internal-array bound))

;; Tue Jan  6 14:15:30 2004. we seem to changed the specific info
;; representation.

(defun array-type (array-obj) 
  (declare (xargs :guard (wff-internal-array array-obj)))
  (obj-type array-obj))


(defun array-bound (array-obj) 
  (declare (xargs :guard (wff-internal-array array-obj)))
  (let ((array-specific-info (specific-info array-obj)))
    (nth 3 array-specific-info)))


(defun array-data (array-obj)
  (declare (xargs :guard (wff-internal-array array-obj)))
  (let ((array-specific-info (specific-info array-obj)))
    (nth 2 array-specific-info)))


(defun element-at-guard (index array-obj)
  (mylet* ((bound (array-bound array-obj)))
    (and (integerp index)
         (wff-internal-array array-obj)
         (integerp bound)
         (<= 0 index)
         (< index bound))))

(defun element-at (index array)
  (declare (xargs :guard (element-at-guard index array)))
  (nth index (array-data array)))


;; (defun element-at (index array)
;;   (nth index (array-data array)))


(defun init-array (type count)
  (declare (xargs :guard (and (integerp count)
                              (>= count  0))))
  (if (zp count)
      nil
      (cons (default-value type) (init-array type (- count 1)))))


(defun make-array (type bound data S)
  (declare (xargs :guard (and (build-a-java-visible-instance-guard
                               "java.lang.Object" s))))
  (mv-let (java-visible-portion new-S)
          (build-a-java-visible-instance "java.lang.Object" S)
          (let* ((common-info (build-common-info type))
                 (specific-info (build-ARRAY-specific-info data bound)))
            (mv (make-object common-info specific-info java-visible-portion) new-S))))


(defun set-element-at-guard (index array S)
  (and (element-at-guard index array)
       (build-a-java-visible-instance-guard "java.lang.Object" s)))

(defun set-element-at (index value array S)
  (declare (xargs :guard (set-element-at-guard index array s)))
  (make-array (array-type array)
              (array-bound array)
              (update-nth index value (array-data array))
              S))

(defun build-an-array-instance (element-type length S)
  (declare (xargs :guard (and (build-a-java-visible-instance-guard "java.lang.Object" s)
                              (integerp length)
                              (>= length 0))))
  (let ((array-type (make-array-type element-type))
        (array-data (init-array element-type length)))
    (make-array array-type length array-data S)))


;; make a change here. don't want to introduce exception here.  let's assume
;; once this is called, length is guaranteed to be correct. 
;; all possible exception should be thrown before it call this function.


;; (acl2::set-verify-guards-eagerness 0)
;;
;; delayed!! fix this later. Tue Jan 13 22:08:01 2004 
;; update-trace should be make guard t!!
;;

;; (defthm build-a-java-visible-instance-guard-implies-perserve-wff-state
;;   (implies (and (build-a-java-visible-instance-guard "java.lang.Object" s)
;;                 (wff-state s))
;;            (wff-state (mv-nth 1 (build-a-java-visible-instance
;;                                  "java.lang.Object" s)))))

;; (defthm build-a-java-visible-instance-guard-implies-perserve-wff-heap
;;   (implies (and (build-a-java-visible-instance-guard "java.lang.Object" s)
;;                 (wff-heap (heap s)))
;;            (wff-heap (heap (mv-nth 1 (build-a-java-visible-instance
;;                                       "java.lang.Object" s))))))

(defthm BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-does-not-change-s
  (equal (mv-nth 1 (build-a-java-visible-instance-data anylist s))
         s))

(defthm build-a-java-visible-instance-does-not-change-s
  (equal (mv-nth 1 (build-a-java-visible-instance any s))
         s))

;; (defthm update-trace-does-not-change
;;   (and (equal (thread-table (update-trace addr s))
;;               (thread-table s))
;;        (equal (class-table (update-trace addr s))
;;               (class-table s))
;;        (equal (pc (update-trace addr s))
;;               (class-table s))
;;
;; Just expand update-trace into make-state !! 
;;


(defthm wff-state-implies-pc-numberp
  (implies (wff-state s)
           (integerp (pc s)))
  :hints (("Goal" :in-theory (enable wff-state pc)))
  :rule-classes :forward-chaining)



;; (defthm wff-state-state-set-pc
;;   (implies (integerp pc) ;; 
;;            (wff-state (make-state pc cid hp tt cl env ef aux)))
;;   :hints (("Goal" :in-theory (e/d (make-state wff-state)))))
;;
;; Sun May  8 16:16:24 2005


(defthm wff-state-state-set-pc
  (implies (integerp pc)
           (wff-state (make-state pc cid hp tt cl env ef aux)))
  :hints (("Goal" :in-theory (e/d (make-state wff-state)))))

;; (i-am-here) ;; Sun May  8 16:24:37 2005

(defun new-array (element-type length S)
  (declare (xargs :guard (and (build-a-java-visible-instance-guard "java.lang.Object" s)
                              (integerp length)
                              (>= length 0)
                              (wff-state s)
                              (wff-heap (heap s))
                              (wff-thread-table (thread-table s))
                              (current-frame-guard s)
                              (wff-call-frame (current-frame s)))
                  :guard-hints (("Goal" :in-theory (e/d (update-trace)
                                                        (build-a-java-visible-instance
                                                         collect-superclass-list
                                                         ))))))
    (mv-let (the-object new-s)
            (build-an-array-instance element-type length S)
            (let* ((old-heap (heap new-s))
                   (addr     (alloc old-heap))
                   (new-heap (bind addr the-object old-heap)))
              (pushStack addr (update-trace addr (state-set-heap new-heap new-s))))))

;;; This new-array is M6 specific!! 
;;;
;;; if for DJVM we need properly TAG it. 
;;;

;; whenever we create a new object, we update-the trace.
;; .... M6, DJVM specific ... No. They should share the same implementation!!

(defun set-element-at-array-guard (index array-ref s)
  (and (wff-state s)
       (wff-heap (heap s))
       (bound? array-ref (heap s))
       (set-element-at-guard 
        index (binding array-ref (heap s)) s)))


;; (defun set-element-at-array (index value array-ref s)
;;   (declare (xargs :guard (set-element-at-array-guard index array-ref s)))
;;   (let* ((old-heap (heap s))
;;          (old-array-obj (binding array-ref old-heap)))
;;     (mv-let (new-array-obj new-s)
;;             (set-element-at index value old-array-obj s)
;;             (let* ((new-heap (bind array-ref new-array-obj old-heap)))
;;               (state-set-heap new-heap new-s)))))
;; ;; we don't update the trace if there is only a write.


(defun set-element-at-array (index value array-ref s)
  (declare (xargs :guard (set-element-at-array-guard index array-ref s)))
  (let* ((old-heap (heap s))
         (old-array-obj (binding array-ref old-heap)))
    (mv-let (new-array-obj new-s)
            (set-element-at index value old-array-obj s)
            (let* ((new-heap (bind array-ref new-array-obj old-heap)))
              (state-set-heap new-heap new-s)))))

;; we don't update the trace if there is only a write. ??? 
;;

;;;; Sat May  7 21:23:38 2005!!! potential bug. 
;;;; the old-heap should be from new-s!! 
;;;; 
;;;; But we can prove that when set-element-at-array-guard succeeds
;;;; build-an-array-instance does not change state!! 
;;;; 


(defun set-array-content-guard (obj-refs array-ref s offset)
  (and (integerp offset)
       (if (not (consp obj-refs))
           t
         (and (set-element-at-array-guard offset array-ref s)
              (set-array-content-guard (cdr obj-refs) array-ref 
                                       (set-element-at-array offset 
                                                             (car obj-refs)
                                                             array-ref s) 
                                       (+ offset 1))))))
                                     


;; (defun set-array-content-guard (obj-refs array-ref s offset)
;;   (and (integerp offset)
;;        (if (not (consp obj-refs))
;;            t
;;          (and (set-element-at-array-guard offset array-ref s)
;;               (set-array-content-guard (cdr obj-refs) array-ref 
;;                                        (set-element-at-array offset 
;;                                                              (car obj-refs)
;;                                                              array-ref s) 
;;                                        (+ offset 1))))))
;;; modified to make it easier!!                                     
                                     
(defun set-array-content1 (obj-refs array-ref s offset)
  (declare (xargs :guard (set-array-content-guard obj-refs array-ref s offset)))
  (if (not (consp obj-refs))
      s
    (set-array-content1 (cdr obj-refs) array-ref 
                        (set-element-at-array offset (car obj-refs) 
                                              array-ref s)
                        (+ offset 1))))


(defun set-array-content (obj-refs array-ref s)
  (declare (xargs :guard (set-array-content-guard obj-refs array-ref s 0)))
  (set-array-content1 obj-refs array-ref s 0))


;;  another definition will be 


;; (defun multiarray-measure (counts length)
;;   (if (zp length)
;;       (cons (cons (+ (len counts) 1) 0) 0)
;;     (cons (cons (+ (len counts) 1) 0) (+ length 1))))



;; (mutual-recursion 
;;  (defun make-multiarray1 (array-type counts s)
;;    (declare (xargs :measure (multiarray-measure counts 0)))
;;    (if (endp counts)
;;        (pushStack -1 s)  
;;      ;; with the array-ref on the top of the stack
;;      (mv-let (obj-refs s1)
;;              (make-multiarray2 (array-base-type array-type)
;;                                (cdr counts) 
;;                                (car counts) 
;;                                s)
;;              ;; first create all elements of the array
;;              (let* ((s2 (new-array (array-base-type array-type) 
;;                                    (car counts)
;;                                    s1))
;;                     (array-ref (topStack s2))
;;                     (s3 (set-array-content obj-refs array-ref s2)))
;;                s3))))

;;  (defun make-multiarray2 (array-type counts length s)
;;    (declare (xargs :measure (multiarray-measure counts length)))
;;    (if (zp length)
;;        (mv nil s)
;;      (mv-let (obj-refs new-s)
;;              (make-multiarray2 array-type counts (- length 1) s)
;;              (let* ((new-s2 (make-multiarray1 array-type counts new-s))
;;                     (obj-ref (topStack new-s2)))
;;                (mv (cons obj-ref obj-refs) (popStack new-s2)))))))


;; ;; bytecode verifier would ensure the array-type is actually has more depths
;; ;; than dim, here we check the runtime data from stack to ensure there are 
;; (defun multiarray-stack-non-negative (dim s)
;;   (if (zp dim)
;;       t
;;     (if (< (topStack s) 0)
;;         nil
;;       (multiarray-stack-non-negative (- dim 1) (popStack s)))))
  

;; ;; similiar to new-array, assume exception is not thrown here.
;; (defun new-multiarray (array-type dim s)
;;   (if (multiarray-stack-non-negative dim s)
;;       (m6-internal-error "new-multiarray precondition violated" s)
;;     (let ((counts (reverse (take dim (operand-stack (current-frame s))))))
;;       (make-multiarray1 array-type counts s))))
    


;------------------------------------------
; Primitives for building an Generic Object 
;------------------------------------------

;---------------------------------------------------------------------------
; 
;  Build a String before class is properly loaded.  only used by Class Loader
;  to create initial heap when loading the classs.
;
;----------------------------------------------------------------------------

;; 08/19/2002
;; because the special field appeared in the String also appeared as java
;; visible field in String. We treat it as a generic_object.

(defun build-STRING-specific-info ()
  (make-STRING-specific-info))

(defun build-a-javaString (s)
  (declare (xargs :guard (build-a-java-visible-instance-guard
                          "java.lang.String" s)))
  (mv-let (java-visible-portion new-S) 
          (build-a-java-visible-instance "java.lang.String" S)
          (let ((commoninfo           (build-common-info "java.lang.String"))
                (specificinfo         (build-STRING-specific-info)))
            (mv (make-object commoninfo specificinfo java-visible-portion)  new-S))))


;  build the heap objects that represent the classes loaded.
;

(defun build-instanceClass-info (classname) 
  (make-INSTANCE_CLASS-specific-info classname))


; (defun build-instanceClass-info (classname) 
;   (list 'INSTANCE_CLASS classname))
;; FIXED for consistent-test.  10/27/03 


(defun isInstanceClass? (specificinfo)
  (declare (xargs :guard (wff-specific-info specificinfo)))
  (wff-instance_class-specific-info specificinfo))
 
(defun specific-info-classname (info)
  (declare (xargs :guard (wff-INSTANCE_CLASS-specific-info info)))
  (caddr info))


(defun build-java-lang-Class-java-visible-part (S)
  (mv (list (cons "java.lang.Class" nil)
            (cons "java.lang.Object" nil))
      s))


(defun build-an-instanceClass (classname S)
  (declare (xargs :guard (build-a-java-visible-instance-guard
                          "java.lang.Class" s)))
  (mv-let (java-visible-portion new-S)
          (build-java-lang-Class-java-visible-part s)
          (let ((commoninfo           (build-common-info "java.lang.Class"))
                (specific-info        (build-instanceClass-info classname)))
            (mv (make-object commoninfo specific-info java-visible-portion)
                new-S))))
                                                

(defun build-instanceClassArrayClass-info (type-desc) 
  (make-instanceclassarrayclass-info type-desc))

(defun isArrayClass? (specificinfo)
  (declare (xargs :guard (wff-specific-info specificinfo)))
  (wff-ARRAY-specific-info specificinfo))

;; may need to seperate the pacakage name out...
;; notice this is an instance of java.lang.Class which described an array-type.


(defun specific-info-array-desc (info)
  (declare (xargs :guard (wff-specific-info info)))
  (caddr info))

(defun build-instanceClassArrayClass (base-type-desc S)
  (declare (xargs :guard (build-a-java-visible-instance-guard
                          "java.lang.Class" s)))
  (mv-let (java-visible-portion new-S)
          (build-java-lang-Class-java-visible-part s)
          (let ((commoninfo   (build-common-info "java.lang.Class"))
                (specific-info   (build-instanceClassArrayClass-info
                                  (make-array-type base-type-desc))))
            (mv (make-object commoninfo specific-info java-visible-portion)
                new-S))))



;--------------- build a Throwable-instance ----- 
(defun build-throwable-specific-info (message backtrace)
  (make-throwable-specific-info message backtrace))

(defun specific-info-throwable-instance-message (specific-info)
  (declare (xargs :guard (wff-specific-info specific-info)))
  (nth 2 specific-info))


;;;
;;; we could add stronger guard checking that classname does implement
;;; throwable interface!!
;;;



(defun isSubClassOf (c1 c2 s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table s)))))
  (isSubClassOf1 c1 c2 (instance-class-table s) nil))

;----------------------------------------------------------------------


(defun build-a-Throwable-instance (classname s)
  (declare (xargs :guard (and (build-a-java-visible-instance-guard
                               classname s)
                              (isSubClassOf classname "java.lang.Throwable" s))))
  (mv-let (java-visible-portion new-s)
          (build-a-java-visible-instance classname s)
          (let ((commoninfo (build-common-info classname))
                (specific-info (build-throwable-specific-info -1 nil)))
            (mv (make-object commoninfo specific-info java-visible-portion)
                new-S))))

;;; That' is a special handing of throwable....
;;; There is a runtime specific info section ...

;  
;-------------- above we defined how to build various objects ------- 
;
;        GENERIC-OBJECT
;        ARRAY
;        STRING
;        INSTANCE-CLASS
;        ARRAY-CLASS
;        THROWABLE-instance
;        
;

;-------------- next we defined a unified interface face to use them --- 

;; assuming both c1 has been loaded (all it's superclass has been loaded. 

;; isSubClassOf1 is defined in jvm-semantics-primitives-aux.lisp
;; for the termination argument.

;;; We need to chose to redefine isSubClassOf to 


;; 
;; the class of classname MUST have been loaded. 
;; before we can call this function.
;;
(defun instantiate (classname S)
  (declare (xargs :guard (build-a-java-visible-instance-guard classname s)))
  (cond ((equal classname "java.lang.String") 
         (build-a-javaString S))
        ;; classname can't be string. 
        ;; is a Throwable class.
        ((isSubClassOf classname "java.lang.Throwable" s) 
         (build-a-Throwable-instance classname s))
        (t  (build-an-instance classname s))))

(defthm instantiate-wff-state
  (implies (wff-state s)
           (wff-state (mv-nth 1 (instantiate classname s)))))
  

        
;;; (acl2::set-verify-guards-eagerness 0)

;; temp. after we fix the definition of update-trace to make it guard T

;;; Wed Mar 31 13:09:43 2004

(defthm wff-heap-alistp
  (implies (wff-heap hp)
           (alistp hp))
  :rule-classes :forward-chaining)


(defun  new-instance (classname S)
  (declare (xargs :guard (and (wff-state s)
                              (wff-heap (heap s))
                              (build-a-java-visible-instance-guard classname s))))
  (mv-let (instance new-S)
          (instantiate classname S)
          (let* ((heap (heap new-S))
                 (new-addr (alloc heap))
                 (new-heap (bind new-addr instance heap)))
            (mv new-addr (update-trace new-addr (state-set-heap new-heap s))))))

;; (acl2::set-verify-guards-eagerness 2)

;-
;;; some short hand utilities functions. 
;;; something wrong!! Tue Jan 13 22:38:46 2004;; need to fix wff-specific-info
;; (acl2::set-verify-guards-eagerness 0)

(defun type-by-class-ref (class-ref s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-heap (heap s))
                              (bound? class-ref (heap s))
                              (wff-obj-strong (deref class-ref (heap s))))))
  (let* ((class-obj (deref class-ref (heap s)))
         (specific-info (specific-info class-obj)))
    (if (isInstanceClass? specific-info)
        (specific-info-classname specific-info)
      (if (isArrayClass? specific-info)
          (specific-info-array-desc specific-info)
        nil))));; impossible

;-------------- primitives for modifying obj ----
; this is internal operation, assume all classes are already initialized. 
;

;;; (acl2::set-verify-guards-eagerness 0)

;; Delay any state modification primitive Tue Jan 13 22:59:35 2004
;; Currently focusing on getting consistent-state predicate defined!
;;

(defun field-access-guard (classname fieldname obj-ref s)
  (and (wff-state s)
       (wff-heap (heap s))
       (bound? obj-ref (heap s))
       (wff-obj (binding obj-ref (heap s)))
       (jvp-access-field-guard classname fieldname (java-visible-portion (binding obj-ref (heap s))))))

(defun m6-putfield (classname fieldname value obj-ref s)
  (declare (xargs :guard (field-access-guard classname fieldname obj-ref s)))
  (let* ((old-heap (heap s))
         (old-obj  (binding obj-ref old-heap))
         (old-jvp  (java-visible-portion old-obj))
         (new-jvp  (jvp-setfield classname fieldname value old-jvp))
         (new-obj  (make-object (common-info old-obj)
                                (specific-info old-obj)
                                new-jvp))
         (new-heap (bind obj-ref new-obj old-heap)))
    (state-set-heap new-heap s)))


(defun m6-getfield (classname fieldname obj-ref s)
  (declare (xargs :guard (field-access-guard classname fieldname obj-ref s)))
  (binding fieldname 
           (binding classname 
                    (java-visible-portion (deref obj-ref (heap s))))))


