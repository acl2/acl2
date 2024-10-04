(in-package "DJVM")
(include-book "base")

; Mon Apr 18 15:50:18 2005. This base-array-class
(acl2::set-verify-guards-eagerness 2)


(defun CHECK-ARRAY-guard (array-ref hp)
  (declare (xargs :guard (wff-heap hp)))
  (mylet* ((array-obj (binding array-ref hp)))
          (and (bound? array-ref hp) 
               ;; it is not necessary to assert, 
               ;; Mon Apr 18 22:38:49 2005
               ;; because we know the it is a REF it is not null
               ;; then know it is bounded!! 
               (wff-internal-array array-obj))))

(local (in-theory (enable wff-internal-array)))

(defun CHECK-ARRAY (array-ref index s)
  (declare (xargs :guard (and (wff-state s)
                              (integerp index)
                              (wff-heap (heap s))
                              (CHECK-ARRAY-guard array-ref (heap s)))))
  (mylet* ((array (binding array-ref (heap s)))
           (bound (array-bound array)))
    (and (<= 0 index)
         (< index bound))))


(defun element-at-array-ref-guard (index ref s)
  (and (wff-state s)
       (wff-heap (heap s))
       (integerp index)
       (CHECK-ARRAY-guard ref (heap s))
       (CHECK-ARRAY ref index s))) 


; To access an element at certain offset of a pointer alleged to
; be pointing an array. We defined the guard to assert:
;
; * It is ok to invoke CHECK-ARRAY: "CHECK-ARRAY-guard"
; * Array access in within bound: CHECK-ARRAY
; * Index must be: integerp 
;   ; We could assert stronger guard than "(integerp index)"
;
; NOTE: Access control to arrays are not defined here. 
;       It is defined in higher level.  


(defun element-at-array (index array-ref s)
  (declare (xargs :guard (element-at-array-ref-guard index array-ref s)))
  (let ((array-obj (binding array-ref (heap s))))
    (element-at index array-obj)))



(defthm check-array-guard-implies-bound?-hp-f
   (implies (check-array-guard p hp)
            (BOUND? p hp))
   :rule-classes :forward-chaining)


(defthm check-array-guard-implies-wff-array-type
  (implies (CHECK-ARRAY-GUARD (RREF tagged-ref) hp)
           (wff-array-type (obj-type (deref2 tagged-ref hp)))))

(defthm check-array-guard-check-array-element-at-array-ref-guard
  (implies (and (check-array-guard (rREF ref) (heap s))
                (check-array (rREF ref) index s)
                (integerp index)
                (wff-REFp ref)
                (consistent-state s))
           (element-at-array-ref-guard index (rREF ref) s))
  :hints (("Goal" :in-theory (enable element-at-array-ref-guard 
                                     wff-REFp
                                     check-array))))

(in-theory (disable CHECK-ARRAY-guard check-ARRAY element-at-array-ref-guard 
                    element-at-array))

(in-theory (disable CONSISTENT-ARRAY-OBJECT
                    consistent-value
                    element-at
                    INT32P
                    INT64P))

(defthm consistent-value-element-at-consistent-array-when-guard
  (implies (and (element-at-array-ref-guard index (rREF ref) s)
                (CONSISTENT-ARRAY-OBJECT (deref2 ref (heap s)) 
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s)))
           (consistent-value (tag (element-at-array index (rREF ref) s)
                                  (array-component-type 
                                   (obj-type (deref2 ref (heap s)))))
                             (array-component-type 
                              (obj-type (deref2 ref (heap s))))
                             (instance-class-table s)
                             (heap s)))
  :hints (("Goal" :restrict ((CONSISTENT-VALUE-ELEMENT-AT-CONSISTENT-ARRAY
                               ((acl (array-class-table s)))))
           :in-theory (e/d (element-at-array-ref-guard element-at-array
                                                       check-array
                            check-array-guard) (ARRAY-COMPONENT-TYPE tag)))))



(defthm wff-array-type-implies-isArrayType
  (implies (wff-array-type typ)
           (isArrayType typ))
  :hints (("Goal" :in-theory (enable isArrayType wff-array-type))))



(local 
 (defthm check-array-guard-in-consistent-heap2-consistent-array-object
  (implies (and (check-array-guard ref hp1)
                (consistent-heap2 hp1 hp cl acl id))
           (consistent-array-object (binding ref hp1)
                                    hp cl acl))
  :hints (("Goal"  :do-not-induct t
           :use ((:instance
                  consistent-heap2-isArrayType-consistent-array-object
                  (xobj (assoc-equal ref hp1))))
           :in-theory (enable check-array-guard
                              binding bound?)))))


(local 
 (defthm check-array-guard-in-consistent-heap-consistent-array-object
  (implies (and (check-array-guard (rREF ref) hp)
                (consistent-heap hp cl acl))
           (consistent-array-object (deref2 ref hp) hp cl acl))
  :hints (("Goal"  :do-not-induct t
           :in-theory (e/d (deref2 consistent-heap)
                           (binding-rref-normalize))))))

(local (in-theory (disable consistent-heap)))

(local (defthm consistent-state-implies-consistent-heap
         (implies (consistent-state s)
                  (consistent-heap (heap s) 
                                   (instance-class-table s)
                                   (array-class-table s)))
         :hints (("Goal" :in-theory (enable consistent-state)))))


(defthm check-array-guard-in-consistent-state-consistent-array-object
  (implies (and (check-array-guard (rREF ref) (heap s))
                (consistent-state s))
           (consistent-array-object (deref2 ref (heap s)) (heap s)
                                    (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal"  :do-not-induct t)))



(defthm consistent-value-implies-consistent-value-x-b-array-element-specific
  (implies  (consistent-value (tag (element-at-array index (rREF ref) s)
                                   (array-component-type (obj-type (deref2 ref (heap s)))))
                              (array-component-type 
                               (obj-type (deref2 ref (heap s))))
                              cl hp)
            (consistent-value-x (tag (element-at-array index (rREF ref) s)
                                     (array-component-type 
                                      (obj-type (deref2 ref (heap s)))))
                                cl hp)))
                                

(defthm consistent-value-x-tag-REF-tag
  (implies (and (consistent-value-x (tag (element-at-array index (rREF ref) s)
                                         (array-component-type 
                                          (obj-type (deref2 ref (heap s))))) cl hp)
                (not (primitive-type? 
                      (array-component-type 
                       (obj-type (deref2 ref (heap s)))))))
           (consistent-value-x (tag-REF (element-at-array index (rREF ref) s))
                                cl hp)))

(in-theory (disable array-component-type consistent-array-object))


(defthm consistent-value-category1-specific
  (implies (and (consistent-value (tag (element-at-array index (rREF ref) s)
                                       (array-component-type (obj-type (deref2 ref (heap s)))))
                                  (array-component-type 
                                   (obj-type (deref2 ref (heap s))))
                                  (instance-class-table s) 
                                  (heap s))
                (not (primitive-type? (array-component-type 
                                       (obj-type (deref2 ref (heap s)))))))
           (category1 (tag (element-at-array index (rREF ref) s)
                           (array-component-type (obj-type (deref2 ref (heap
                                                                        s)))))))
  :hints (("Goal" :in-theory (enable consistent-value category1))))


(local 
 (defthm array-type-s-in-consistent-heap-means-consistent-array-object
   (implies (and (array-type-s (obj-type (deref2 ref hp1)) cl)
                 (consistent-heap2 hp1 hp cl acl id))
            (consistent-array-object (deref2 ref hp1) hp cl acl))
   :hints (("Goal" :in-theory (e/d (rref binding deref2 obj-type)
                                   (consistent-array-object))
            :do-not '(generalize)))))


(defthm consistent-array-object-implies-wff-internal-array
  (implies (consistent-array-object (deref2 ref (heap s)) 
                                    (heap s)
                                    (instance-class-table s)
                                    (array-class-table s))
           (wff-internal-array (deref2 ref (heap s))))
  :hints (("Goal" :in-theory (enable consistent-array-object
                                     wff-internal-array))))



(defthm array-type-s-in-consistent-state-means-consistent-array-object
  (implies (and (array-type-s (obj-type (deref2 ref (heap s))) 
                              (instance-class-table s))
                (consistent-state s))
           (consistent-array-object (deref2 ref (heap s))
                                    (heap s)
                                    (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-heap consistent-state))))


(in-theory (disable array-type-s))


;; (defthm not-bound-not-array-type-s
;;   (implies (not (bound? (rREF ref) hp))
;;            (not (array-type-s (obj-type (deref2 ref hp)) 
;;                               cl)))
;;   :hints (("Goal" :in-theory (e/d (array-type-s 
;;                                    bound? 
;;                                    wff-array-type
;;                                    deref2)
;;                                   ())))
;;   :do-not '(preprocess))

(defthm not-bound?-deref2-nil
  (implies (not (bound? (rREF ref) hp))
           (equal (deref2 ref hp) nil))
  :hints (("Goal" :in-theory (e/d (deref2 binding bound?) (binding-rRef-normalize))
           :do-not '(preprocess))))


(defthm not-array-type-s
  (not (array-type-s nil cl)))

(defthm check-array-guard-implied-by-array-type-s
  (implies (and (array-type-s (obj-type (deref2 ref (heap s)))
                              (instance-class-table s))
                (consistent-state s))
           (check-array-guard (rREF ref) (heap s)))
  :hints (("Goal" :in-theory (enable check-array-guard))))
           
;----------------------------------------------------------------------

;; (i-am-here) ;; Wed May  4 13:16:12 2005

(local (defthm array-obj-consistent1-l
         (implies (and (array-obj-consistent1 l type hp cl)
                       (mem x l))
                  (CONSISTENT-VALUE  (TAG x type) type cl hp))
         :hints (("Goal" :in-theory (e/d (consistent-array-object)
                                         (array-data))))))


(local 
 (defthm consistent-value-element-at
   (implies 
    (and (consistent-array-object obj hp cl acl)
         (mem x (array-data obj)))
    (CONSISTENT-VALUE
     (TAG x (array-component-type (obj-type obj)))
     (array-component-type (obj-type obj))
     cl hp))
   :hints (("Goal" :in-theory (e/d (consistent-array-object
                                    array-obj-consistent)
                                   (array-data tag))))))


(local 
 (defthm consistent-value-element-at-specific
   (implies 
    (and (consistent-array-object (deref2 v (heap s)) (heap s) 
                                  (instance-class-table s) 
                                  (array-class-table s))
         (mem x (array-data (deref2 v (heap s))))
         (equal (instance-class-table s) cl)
         (equal (heap s) hp))
    (CONSISTENT-VALUE
     (TAG x (array-component-type (obj-type (deref2 v (heap s)))))
     (array-component-type (obj-type (deref2 v (heap s))))
     cl hp))
   :hints (("Goal" :in-theory (e/d (consistent-array-object
                                    array-obj-consistent)
                                   (array-data tag))))))



(local 
 (defthm nth-mem-if-in-bound
   (implies  (AND (<= 0 INDEX) 
                  (< INDEX (len list)))
             (mem (nth index list) list))))


(local 
 (defthm element-at-index-mem
   (implies  (AND (<= 0 INDEX) 
                  (< INDEX (len (array-data array-obj))))
             (mem (element-at index array-obj)
                  (array-data array-obj)))
   :hints (("Goal" :in-theory (e/d (element-at))))))


(local 
 (defthm len-array-data-normalize
   (implies (wff-internal-array obj)
            (equal (len (array-data obj))
                   (array-bound obj)))
   :hints (("Goal" :in-theory (enable wff-internal-array)))))


;; (i-am-here) ;; Wed May  4 14:50:15 2005


(local (defthm element-of-array-is-consistent-value
         (implies (and (consistent-array-object array hp cl acl)
                       (<= 0 index)
                       (< index (array-bound array)))
                  (consistent-value (tag (element-at index array)
                                         (array-component-type (obj-type array)))
                                    (array-component-type (obj-type array))
                                    cl hp))
         :hints (("Goal" :in-theory (e/d (consistent-array-object)
                                         (array-data tag))))))


(defthm element-of-array-is-consistent-value-specific
  (implies (and (consistent-array-object (deref2 v (heap s)) 
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s))
                (check-array (rREF v) index s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp))
           (consistent-value (tag (element-at-array index (rREF v) s)
                                  (array-component-type (obj-type (deref2 v
                                                                          (heap s)))))
                             (array-component-type (obj-type (deref2 v (heap s))))
                             cl hp))
  :hints (("Goal" :in-theory (e/d (check-array element-at-array) (array-bound 
                                                 tag )))))



;----------------------------------------------------------------------


(local 
 (defthm array-content-initialized-mem-specific
   (implies (and (array-content-initialized data hp-init)
                 (not (equal (rREF x) -1))
                 (mem (rREF x) data))
            (not (consp (deref2-init x hp-init))))
   :hints (("Goal" :in-theory (enable deref2-init)))))


(local 
 (defthm consistent-heap-array-init-state3-implies-array
   (implies (and (consistent-heap-array-init-state3 hp hp-init)
                 (bound? ref hp)
                 (WFF-INTERNAL-ARRAY (binding ref hp))
                 (not (primitive-type? (array-component-type (obj-type (binding ref hp)))))
                 (isArrayType (obj-type (binding ref hp))))
            (array-content-initialized (array-data (binding ref hp)) hp-init))
   :hints (("Goal" :in-theory (e/d (binding bound?) (array-data 
                                                     isarraytype
                                                     array-content-initialized))))))



(local (defthm wff-internal-array-implies-bound?
  (implies (not (bound? (rREF v) hp))
           (not (wff-internal-array (deref2 v hp))))))

(local (defthm wff-internal-array-implies-bound?-f
  (implies (wff-internal-array (deref2 v hp))
           (bound? (rREF v) hp))
  :rule-classes :forward-chaining))



(local 
 (defthm consistent-heap-array-init-state3-implies-array-specific
   (implies (and (consistent-heap-array-init-state3 hp hp-init)
                 (WFF-INTERNAL-ARRAY (deref2 array-ref hp))
                 (not (primitive-type? (array-component-type (obj-type (deref2 array-ref hp)))))
                 (isArrayType (obj-type (deref2 array-ref hp))))
            (array-content-initialized (array-data (deref2 array-ref hp)) hp-init))
   :hints (("Goal" :in-theory (e/d (deref2 ) (array-data 
                                              isarraytype
                                              binding-rref-normalize
                                              array-content-initialized))
            :cases ((bound? (rREF array-ref) hp))))))


(local 
 (defthm rREF-tag-REF 
   (equal (rREF (tag-REF v)) v)
   :hints (("Goal" :in-theory (enable rREF tag-REF)))))

(local (defthm consistent-array-object-implies-isArrayType
   (implies (consistent-array-object obj hp cl acl)
            (isArrayType (obj-type obj)))
   :hints (("Goal" :in-theory (enable consistent-array-object)))
   :rule-classes :forward-chaining))



(local (defthm mem-element-at-array
         (implies (and (check-ARRAY (rREF array-ref) index s)
                       (wff-internal-array (deref2 array-ref (heap s))))
                  (MEM (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF)
                                  S)
                       (ARRAY-DATA (DEREF2 ARRAY-REF (HEAP S)))))
         :hints (("Goal" :in-theory (e/d (element-at-array element-at
                                                           wff-internal-array 
                                                           check-ARRAY)
                                         (array-data array-bound))))))


(local (defthm consistent-state-consistent-heap-init-state3
         (implies (consistent-state s) 
                  (consistent-heap-array-init-state3 (heap s) (heap-init-map (aux s))))
         :hints (("Goal" :in-theory (enable consistent-heap-array-init-state3
                                            consistent-state)))))


;; (defthm element-at-consistent-array-not-deref2-init
;;   (implies (and (consistent-array-object (deref2 array-ref (heap s))
;;                                          (heap s)
;;                                          (instance-class-table s)
;;                                          (array-class-table s))
;;                 (check-ARRAY (rREF array-ref) index s)  ;; we can assume this
;;                 (NOT (EQUAL (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF) S) '-1))
;;                 (consistent-state s)
;;                 (not (primitive-type? (array-component-type (obj-type (deref2 array-ref (heap s)))))))
;;            (not (consp (deref2-init (tag-REF (element-at-array index (rREF array-ref) s))
;;                                     (heap-init-map (aux s))))))
;;   :hints (("Goal" :in-theory (e/d () (deref2-init tag-REF array-data
;;                                                   TAG-REF-TAG 
;;                                                   heap-init-map))
;;            :restrict ((array-content-initialized-mem-specific
;;                        ((data (array-data (deref2 array-ref (heap s))))))))))


;;; moved the specific one to the end so that it matches first!! 
;;; Wed May  4 18:45:16 2005

;----------------------------------------------------------------------

(in-theory (disable tag))


(local 
 (defthm consistent-heap-array-init-state1-implies-array-object-all-initialized
   (implies (and (consistent-heap-array-init-state1 HP CL ACL HP-INIT)
                 (ISARRAYTYPE (OBJ-TYPE (deref2 v hp))))
            (not (consp (deref2-init v hp-init))))
   :hints (("Goal" :in-theory (e/d (deref2-init deref2 assoc-equal binding
                                                bound?) (binding-rRef-normalize))))))


;; (local 
;;  (defthm consistent-heap-array-init-state1-implies-array-object-all-initialized-f
;;    (implies (and (consistent-heap-array-init-state1 HP CL ACL HP-INIT)
;;                  (ISARRAYTYPE (OBJ-TYPE (deref2 v hp))))
;;             (not (consp (deref2-init v hp-init))))
;;    :hints (("Goal" :in-theory (e/d (deref2-init deref2 assoc-equal binding
;;                                                 bound?)
;;                                    (binding-rRef-normalize))))
;;    :rule-classes :forward-chaining))



;; (defthm array-object-always-initialized
;;   (implies (and (array-type-s (obj-type (deref2 v (heap s)))
;;                               (instance-class-table s))
;;                 (consistent-state s))
;;            (not (consp (deref2-init v (heap-init-map (aux s)))))))


;;
;; Optimization. .. However the optimization does not work too well. 
;;


(local (defthm array-type-s-implies-isArrayType-f
         (implies  (array-type-s (obj-type (deref2 v (heap s)))
                                 (instance-class-table s))
                   (isArrayType (obj-type (deref2 v (heap s)))))
         :rule-classes :forward-chaining))
           


(defthm array-object-always-initialized
  (implies (and (isArrayType (obj-type (deref2 v (heap s))))
                (consistent-state s))
           (not (consp (deref2-init v (heap-init-map (aux s))))))
  :hints (("Goal" :in-theory (e/d (consistent-state) (heap-init-map
                                                      deref2-init)))))


(defthm array-object-always-initialized-alternative
  (implies (and (array-type-s (obj-type (deref2 v (heap s)))
                              (instance-class-table s))
                (consistent-state s))
           (not (consp (deref2-init v (heap-init-map (aux s))))))
  :hints (("Goal" :in-theory (disable deref2-init heap-init-map))))


(defthm element-type-of-fix-sig-is-fix-sig-of-element-type
  (implies (isArrayType type)
           (equal (bcv::arrayelementtype (fix-sig type))
                  (FIX-SIG (array-component-type type))))
  :hints (("Goal" :in-theory (enable fix-sig component-type 
                                     bcv::arrayelementtype
                                     primitive-type? isArrayType
                                     array-component-type))))

;----------------------------------------------------------------------

;; (i-am-here)

(defthm element-at-consistent-array-not-deref2-init
  (implies (and (consistent-array-object (deref2 array-ref (heap s))
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s))
                (check-ARRAY (rREF array-ref) index s)  ;; we can assume this
                (NOT (EQUAL (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF) S) '-1))
                (consistent-state s)
                (not (primitive-type? (array-component-type (obj-type (deref2 array-ref (heap s)))))))
           (not (consp (deref2-init (tag-REF (element-at-array index (rREF array-ref) s))
                                    (heap-init-map (aux s))))))
  :hints (("Goal" :in-theory (e/d () (deref2-init tag-REF array-data
                                                  TAG-REF-TAG 
                                                  heap-init-map))
           :restrict ((array-content-initialized-mem-specific
                       ((data (array-data (deref2 array-ref (heap s))))))))))


;----------------------------------------------------------------------

; for array update operation!!


;; (skip-proofs 
;;  (defthm set-element-at-guard-implies-set-element-at-1
;;    (implies (and (check-null value)
;;                  (set-element-at-guard index array s)
;;                  (equal (heap s) hp)
;;                  (equal (instance-class-table s) cl)
;;                  (equal (array-class-table s) acl)
;;                  (not (primitive-type? (array-component-type (obj-type array))))
;;                  (consistent-array-object array hp cl acl))
;;             (consistent-array-object 
;;              (car (set-element-at index (rREF value) array s)) hp cl acl))
;;    :hints (("Goal" :in-theory (e/d (consistent-array-object)
;;                                    (make-array array-data specific-info tag-REF
;;                                                array-bound array-type))))))

;----------------------------------------------------------------------

;;; the following are for array update operation. ;; Wed May 11 00:51:32 2005

;;; (i-am-here)


;;; safe to set some component to -1

;----------------------------------------------------------------------
;;;; check the old djvm-bytecode.lisp for useful lemmas to prove these!! 


(skip-proofs 
 (defthm set-element-at-guard-implies-set-element-at-1
  (implies (and (set-element-at-guard index array s)
                (equal (heap s) hp)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl)
                (not (primitive-type? (array-component-type (obj-type array))))
                (consistent-array-object array hp cl acl))
           (consistent-array-object 
            (car (set-element-at index -1 array s)) hp cl acl))
  :hints (("Goal" :in-theory (e/d (consistent-array-object)
                                  (make-array array-data specific-info tag-REF
                                              array-bound array-type))))))



(skip-proofs 
 (defthm obj-type-not-change-set-element-at
   (equal (obj-type (set-element-at index value array s))
          (obj-type array))))



(skip-proofs 
 (defthm consistent-object-set-elment-at
   (implies (and (set-element-at-guard index array s)
                 (equal (heap s) hp)
                 (equal (instance-class-table s) cl)
                 (not (primitive-type? (array-component-type (obj-type
                                                              array))))
                 (consistent-object array hp cl)
                 (consistent-array-object array hp cl (array-class-table s)))
            (CONSISTENT-OBJECT
             (CAR (SET-ELEMENT-AT index -1 array s)) hp cl))))



;----------------------------------------------------------------------

(skip-proofs 
 (defthm obj-type-not-change-by-set-element-at
   (equal 
    (OBJ-TYPE (CAR (SET-ELEMENT-AT index value array s)))
    (OBJ-TYPE array))))


;----------------------------------------------------------------------



(skip-proofs 
 (defthm set-element-at-guard-implies-set-element-at-2
   (implies (and (set-element-at-guard index array s)
                 (equal (heap s) hp)
                 (equal (instance-class-table s) cl)
                 (equal (array-class-table s) acl)
                 (not (primitive-type? (array-component-type (obj-type
                                                              array))))
                 (not (NULLp v))
                 (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                      (array-component-type (obj-type array)) s))
                 (consistent-array-object array hp cl acl))
            (consistent-array-object 
             (car (set-element-at index (value-of v) array s)) hp cl acl))
   :hints (("Goal" :in-theory (e/d (consistent-array-object)
                                   (make-array array-data specific-info tag-REF
                                               array-bound array-type))))))






(skip-proofs 
 (defthm consistent-object-set-elment-at-2
   (implies (and (set-element-at-guard index array s)
                 (equal (heap s) hp)
                 (equal (instance-class-table s) cl)
                 (not (primitive-type? (array-component-type (obj-type
                                                              array))))
                 (not (NULLp v))
                 (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                      (array-component-type (obj-type array)) s))
                 (consistent-object array hp cl)
                 (consistent-array-object array hp cl (array-class-table s)))
            (CONSISTENT-OBJECT
             (CAR (SET-ELEMENT-AT index (value-of v) array s)) hp cl))))


;----------------------------------------------------------------------



;; (defthm element-of-array-is-consistent-value-specific
;;   (implies (and (consistent-array-object (deref2 v (heap s)) 
;;                                          (heap s)
;;                                          (instance-class-table s)
;;                                          (array-class-table s))
;;                 (check-array (rREF v) index s)
;;                 (equal (instance-class-table s) cl)
;;                 (equal (heap s) hp))
;;            (consistent-value (tag (element-at-array index (rREF v) s)
;;                                   (array-component-type (obj-type (deref2 v
;;                                                                           (heap s)))))
;;                              (array-component-type (obj-type (deref2 v (heap s))))
;;                              cl hp))
;;   :hints (("Goal" :in-theory (e/d (check-array element-at-array) (array-bound 
;;                                                  tag )))))

(local 
 (defthm consistent-value-implies-wff-tagged-value
   (implies (consistent-value v type cl hp)
            (wff-tagged-value v))))

(defthm consistent-value-implies-wff-tagged-value-specific
  (implies (consistent-value (tag (element-at-array index (rREF v) s)
                                  (array-component-type (obj-type (deref2 v
                                                                          (heap s)))))
                              (array-component-type (obj-type (deref2 v (heap s))))
                              (instance-class-table s)
                              (heap s))
           (wff-tagged-value (tag (element-at-array index (rREF v) s)
                                  (array-component-type (obj-type (deref2 v
                                                                          (heap
                                                                           s))))))))

;----------------------------------------------------------------------

;;(i-am-here) ;; Sat Aug  6 19:59:43 2005

(defthm element-at-consistent-array-not-deref2-init-specific
  (implies (and (consistent-array-object (deref2 array-ref (heap s))
                                         (heap s)
                                         (instance-class-table s)
                                         (array-class-table s))
                (check-ARRAY (rREF array-ref) index s)  ;; we can assume this
                (NOT (EQUAL (ELEMENT-AT-ARRAY INDEX (RREF ARRAY-REF) S) '-1))
                (consistent-state s)
                (not (primitive-type? (array-component-type (obj-type (deref2 array-ref (heap s)))))))
           (not (consp (deref2-init (tag (element-at-array index (rREF
                                                                  array-ref) s)
                                         (array-component-type (obj-type (deref2 array-ref (heap s)))))
                                    (heap-init-map (aux s))))))
  :hints (("Goal" :use element-at-consistent-array-not-deref2-init
           :in-theory (enable tag))))

;----------------------------------------------------------------------

;;(i-am-here) ;; Sat Aug  6 21:52:22 2005

(local 
 (defthm NULLp-tag-implies-not-equal-minus-1
   (implies (and (not (NULLp (tag v type)))
                 (not (primitive-type? type)))
            (not (equal v -1)))
   :hints (("Goal" :in-theory (enable tag)))))


(defthm NULLp-tag-implies-not-equal-minus-1-specific
  (implies (and (NOT
                 (NULLP
                  (TAG (ELEMENT-AT-ARRAY index 
                                         (RREF v) 
                                         S)
                       (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 v (HEAP S)))))))
                (not (primitive-type? (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 v (HEAP S)))))))
           (not (equal (element-at-array index (rREF v) s) -1)))
  :hints (("Goal" :use ((:instance NULLp-tag-implies-not-equal-minus-1
                                   (type (ARRAY-COMPONENT-TYPE (OBJ-TYPE
                                                                (DEREF2 v (HEAP
                                                                           S)))))
                                   (v (ELEMENT-AT-ARRAY index 
                                         (RREF v) 
                                         S)))))))
                       



