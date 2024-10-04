(in-package "DJVM")
(acl2::set-verify-guards-eagerness 2)
(include-book "../M6-DJVM-shared/jvm-type-value")
(include-book "../M6-DJVM-shared/jvm-class-table")
(include-book "../M6-DJVM-shared/jvm-obj")


;----------------------------------------------------------------------

(defun wff-tagged-value (tagged-value)
  (declare (xargs :verify-guards t))
  (and (consp tagged-value)
       (equal (len tagged-value) 1))) 

(defun tag-of (tagged-value)
  (declare (xargs :guard (wff-tagged-value tagged-value)))
  (car tagged-value)) 

(defun value-of (tagged-value)
  (declare (xargs :guard (wff-tagged-value tagged-value)))
  (cdr tagged-value))

;----------------------------------------------------------------------

;; Need a reference type predicate: 
(defun wff-REFp (ref)
  (declare (xargs :verify-guards t))
  ;; when we assert globally syntax correct.  we need assert wff-tagged-value
  ;; and appropriate wff-REFp like predicate.
  (and (wff-tagged-value ref)
       (equal (tag-of ref) 'REF)
       (integerp (value-of ref))))
       ;; we probably do not to assert (integerp (value-of ref))
       ;; because we never only use those as key into heap. 


(defun rREF (ref)
  (declare (xargs :guard (wff-REFp ref)))
  ;; make sure it is only called after we can establish ref is a wff-REFp
  (cdr ref))

;; only called on wff-REFp

(defun NULLp (ref)
  (declare (xargs :verify-guards t))
  (and (wff-REFp ref)
       (equal (rREF ref) -1)))

;----------------------------------------------------------------------

;; (defun wff-Heap (hp)
;;   (declare (xargs :verify-guards t))
;;   (alistp hp)) ;; minium requirement 


(defun Valid-REFp (ref hp)
  ;; somethin about consistency
  (declare (xargs :guard (wff-Heap hp)))
  (and (wff-REFp ref)
       (bound? (rREF ref) hp)))

;; Note: We do not assert objected at (rREF ref) is a valid object. 
;; Because that would cause mutual recurision. 
;; We will be relying on the fact that every object in the heap is a
;; valid-object (valid-object means its reference valued fields are REFp)

(defun REFp (ref hp)
  (declare (xargs :guard (wff-Heap hp)))
  ;; more semantic REF bounded! 
  (or (NULLp ref)
      (Valid-REFp ref hp)))

;----------------------------------------------------------------------


(defun wff-INT (tagged-value)
  (and (wff-tagged-value tagged-value)
       (equal  (tag-of tagged-value) 'INT)
       (integerp (value-of tagged-value)))) 


(defun Valid-INTp (tagged-value)
  (and (wff-INT tagged-value)
       (int32p (value-of tagged-value))))

;;  int32p defined in primitive.lisp


;----------------------------------------------------------------------

;; (defun wff-array-type (arraytype)
;;   (declare (xargs :verify-guards t))
;;   (and (consp arraytype)
;;        (equal (car arraytype) 'ARRAY)
;;        (equal (len arraytype) 2)))

;; (defun array-component-type (arraytype)
;;   (declare (xargs :guard (wff-array-type arraytype)))
;;   (cadr arraytype))

;; (defun primitive-type (type)
;;   (declare (xargs :verify-guards t))
;;   (or (equal type 'INT)
;;       (equal type 'ADDR) ;; different from jvm's definition. WHY?
;;       (equal type 'BYTE)
;;       (equal type 'LONG)
;;       (equal type 'SHORT)
;;       (equal type 'CHAR)));; ARRAY-type MAY NEED THIS
;;                              ;; need to deal with LONG, etc.  

;; (defun primitive-opvalue-type (type) 
;;   (declare (xargs :verify-guards t))
;;    (or (equal type 'INT)
;;        (equal type 'ADDR)
;;        (equal type 'LONG)))


;; ;----------------------------------------------------------------------

;; (mutual-recursion 
;;  (defun reference-type-s (type cl)
;;    ;; why reference-type-s should it just be reference-type
;;    ;; this recursive.
;;    (declare (xargs :guard (wff-instance-class-table cl)
;;                    :measure (cons (+ (acl2-count type) 1) 1)))
;;    (or (equal type 'NULL) ;; never used. ;; we represent NULL with (REF . -1)
;;        (array-type-s type cl)
;;        (class-exists? type cl)))
 
;;  (defun array-type-s (type cl)
;;    (declare (xargs :guard (wff-instance-class-table cl)
;;                    :measure (cons (+ (acl2-count type) 1) 0)))
;;    (and (wff-array-type type)
;;         (or (primitive-type (array-component-type type))
;;             (reference-type-s (array-component-type type) cl)))))

;; ;----------------------------------------------------------------------


;; (defun wff-type-desc (type-desc)
;;   (or (primitive-type type-desc)
;;       (isClassType type-desc)
;;       (isArrayType type-desc)))
;; ;;

;; (defun classname-classtype (ctype)
;;   (declare (xargs :guard (isClassType ctype)))
;;   ctype) ;; FIXED  10/28/03. see above fix for isClassType

;; (defun compound (x)
;;   (consp x))

;; (defun isJavaLangObject (type)
;;   (equal type '(class  "java.lang.Object")))

;; ; -- used only on arrayType
;; (defun component-type (aArrayType)
;;   (declare (xargs :guard (isArrayType aArrayType)))
;;   (cadr aArrayType))


;; ;;; from consistent-state.lisp


;; ;----------------------------------------------------------------------


;; (defun ADDRp (v) 
;;   (integerp v))

;; (defun CHARp (v)
;;   ;; temp implementation
;;   ;; should be 16 bit unsigned integer.
;;   ;;
;;   (INT32p v))

;; (defun jvmBOOLEANp (v)
;;   ;; temp implementation
;;   ;; should be 1 bit unsigned integer.
;;   (INT32p v))


;; (defun SHORTp (v)
;;   (INT32p v)) ;; Mon May 30 14:40:10 2005

;; (defun BYTEp (v)
;;   (INT32p v))

;; (defun jvmFLOATp (v) 
;;   (stringp v))

;; (defun DOUBLEp (v) 
;;   (stringp v))


;;; moved to jvm-type-value.lisp
;; ;----------------------------------------------------------------------

(defun tag (untagged-value field-type)
  (if (primitive-type? field-type)
      (cons field-type untagged-value)
    (cons 'REF untagged-value)))


;----------------------------------------------------------------------

(defun deref2 (ref hp)
  (declare (xargs :guard (and (wff-Heap hp)
                              (Valid-REFp ref hp))))
  ;; never deref2 a non pointer. 
  ;; ensure our owm implementation is right. 
              
  (binding (rREF ref) hp))

