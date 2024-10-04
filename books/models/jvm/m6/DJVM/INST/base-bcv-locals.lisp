(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")

(include-book "base-locals")
   
(in-theory (disable bcv::arg1 local-at max-local
                    CURRENT-METHOD
                    arg BCV::ISARRAYTYPE
                    BCV::ISASSIGNABLE
                    BCV::ISCLASSTYPE
                    BCV::ISJAVAASSIGNABLE
                    BCV::ISNULLTYPE
                    BCV::ISUNINITIALIZEDOBJECT))


(defthm arg-normalize-bcv-arg1
  (equal (arg inst)
         (bcv::arg1 inst))
  :hints (("Goal" :in-theory (enable arg bcv::arg1))))


(defthm len-locals-sig-is-len-locals
  (implies (consistent-locals locals cl hp)
           (equal (len (locals-sig locals cl hp hp-init method-ptr))
                  (len locals))))

;; this is generally useful. 
;; we will normalize terms into locals-sig


(defthm frame-locals-normalize
  (equal (BCV::FRAMELOCALS (FRAME-SIG (CURRENT-FRAME S)
                                      cl hp hp-init))
         (locals-sig (locals (current-frame s)) cl
                     hp hp-init (method-ptr (current-frame s))))
  :hints (("Goal" :in-theory (enable frame-sig))))


(include-book "base-bcv-fact-isAssignable-len-pushOpstack")
;; contains rules to reduce (len (bcv::pushoperandstack ... stk)) ...



;; (skip-proofs 
;;   (defthm isAssignable-implies-valid-local-index
;;     (implies  (bcv::isAssignable (nth i 
;;                                       (locals-sig locals cl hp hp-init method-ptr))  'reference env)
;;               (valid-local-index i locals))))
;; merged into the following book 
(include-book "base-bcv-valid-local-index-facts")

    
(local 
 (defthm valid-local-index-implies-i-no-greater-than-len-locals
   (implies (valid-local-index i locals)
            (< i (len locals)))
   :rule-classes :linear))



(local 
 (defthm consistent-frame-implies-locals-within-bound
   (implies (and (consistent-frame frame cl hp)
                 (not (mem '*native* 
                           (method-accessflags (deref-method (method-ptr frame)
                                                       cl)))))
            (<= (len (locals frame))
                (method-maxlocals (deref-method (method-ptr frame) cl))))
   :rule-classes :linear))
                                          


(local 
 (defthm consistent-state-implies-len-current-frame-less-than-max-locals
   (implies (and (consistent-state s)
                 (not (MEM '*NATIVE*
                           (METHOD-ACCESSFLAGS (current-method s)))))
            (<= (len (locals (current-frame s)))
                (max-local s)))
   :hints (("Goal" :in-theory (e/d (max-local current-method)
                                   (current-method-normalization))))
   :rule-classes :linear))


(defthm valid-local-index-implies-not-out-of-bound
  (implies (and (valid-local-index i (locals (current-frame s)))
                (not (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (current-method s))))
                (consistent-state s))
           (< i (max-local s)))
  :hints (("Goal" :use ((:instance 
                         valid-local-index-implies-i-no-greater-than-len-locals
                         (locals (locals (current-frame s))))))))


;; now we need some rules arg1 being in the range 
;;

;;(i-am-here) ;; Sat May 21 19:10:01 2005

(local (in-theory (disable env-sig)))




(local 
 (encapsulate ()
              (local 
               (defthm isAssignable-expander
                 (implies (syntaxp 
                           (and (or (eq (len (cdr bcv::t1)) 1)
                                    (eq (len (cdr bcv::t2)) 1))
                                (or (eq (car bcv::t1) 'QUOTE)
                                    (eq (car bcv::t2) 'QUOTE))))
                          (equal (bcv::isAssignable bcv::t1 bcv::t2 bcv::env)
                                 (LET
                                  ((BCV::CL (BCV::CLASSTABLEENVIRONMENT BCV::ENV)))
                                  (IF
                                   (EQUAL BCV::T1 BCV::T2)
                                   T
                                   (COND
                                    ((AND (EQUAL BCV::T1 'ONEWORD)
                                          (EQUAL BCV::T2 'topx))
                                     T)
                                    ((AND (EQUAL BCV::T1 'TWOWORD)
                                          (EQUAL BCV::T2 'topx))
                                     T)
                                    ((EQUAL BCV::T1 'INT)
                                     (BCV::ISASSIGNABLE 'ONEWORD
                                                        BCV::T2 BCV::ENV))
                                    ((EQUAL BCV::T1 'FLOAT)
                                     (BCV::ISASSIGNABLE 'ONEWORD
                                                        BCV::T2 BCV::ENV))
                                    ((EQUAL BCV::T1 'LONG)
                                     (BCV::ISASSIGNABLE 'TWOWORD
                                                        BCV::T2 BCV::ENV))
                                    ((EQUAL BCV::T1 'DOUBLE)
                                     (BCV::ISASSIGNABLE 'TWOWORD
                                                        BCV::T2 BCV::ENV))
                                    ((EQUAL BCV::T1 'REFERENCE)
                                     (BCV::ISASSIGNABLE 'ONEWORD
                                                        BCV::T2 BCV::ENV))
                                    ((EQUAL 'UNINITIALIZED BCV::T1)
                                     (BCV::ISASSIGNABLE 'REFERENCE
                                                        BCV::T2 BCV::ENV))
                                    ((BCV::ISCLASSTYPE BCV::T1)
                                     (OR (BCV::ISASSIGNABLE 'REFERENCE
                                                            BCV::T2 BCV::ENV)
                                         (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL)))
                                    ((BCV::ISARRAYTYPE BCV::T1)
                                     (OR
                                      (BCV::ISASSIGNABLE 'REFERENCE
                                                         BCV::T2 BCV::ENV)
                                      (AND (BCV::ISCLASSTYPE BCV::T2)
                                           (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))
                                      (AND (BCV::ISARRAYTYPE BCV::T2)
                                           (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))))
                                    ((EQUAL BCV::T1 'UNINITIALIZEDTHIS)
                                     (BCV::ISASSIGNABLE 'UNINITIALIZED
                                                        BCV::T2 BCV::ENV))
                                    ((BCV::ISUNINITIALIZEDOBJECT BCV::T1)
                                     (BCV::ISASSIGNABLE 'UNINITIALIZED
                                                        BCV::T2 BCV::ENV))
                                    ((BCV::ISNULLTYPE BCV::T1)
                                     (OR (BCV::ISCLASSTYPE BCV::T2)
                                         (BCV::ISARRAYTYPE BCV::T2)
                                         (BCV::ISASSIGNABLE '(CLASS "java.lang.Object")
                                                            BCV::T2 BCV::ENV)))
                                    (T NIL))))))
                 :hints (("Goal" :expand (bcv::isassignable bcv::t1 bcv::t2 bcv::env)))))

              (defthm isAssignable-value-sig-implies-REFp
                (implies (and (valid_local_type (tag-of v))
                              (bcv::isAssignable (value-sig v (instance-class-table s)
                                                            (heap s)
                                                            (heap-init-map (aux s))
                                                            (method-ptr (current-frame s)))
                                                 'reference
                                                 (env-sig s))
                              (consistent-state s))
                         (REFp v (heap s)))
                :hints (("Goal" :in-theory (enable env-sig bcv::isnulltype
                                                   primitive-type?))))))

;; we avoid rewriting (nth i (locals-sig ...)) 
;; into value-sig !! 
;;

;;(i-am-here) 

(local 
 (defthm equal-minus-one-minus-one-plus-negative-two
   (equal (+ -1 -1 i)
          (+ -2 i))))


(local 
 (defthm nth-i-specific-cons
   (implies (and (< 0 i)
                 (integerp i))
            (equal (nth i (cons x locals))
                   (nth (- i 1) locals)))))


(local 
 (defthm nth-i-specific-2-cons
   (implies (and (< 1 i)
                 (integerp i))
            (equal (nth i (list*  x y locals))
                   (nth (- i 2) locals)))
   :hints (("Goal" 
            :in-theory (disable nth-i-specific-cons)
            :use ((:instance nth-i-specific-cons
                             (i (- i 1))
                             (locals (cdr locals)))
                  (:instance nth-i-specific-cons))
            :do-not-induct t))))

(local 
 (defthm valid-local-index-implies-i-positive
   (implies (VALID-LOCAL-INDEX (+ -2 I) any)
            (< 1 i))
   :rule-classes :forward-chaining))




(local 
 (defthm valid-local-index-implies-nth-i-local-sig-reduce
   (implies (and (valid-local-index i locals)
                 (integerp i))
            (equal (nth i (locals-sig locals cl hp hp-init method-ptr))
                   (value-sig (nth i locals) cl hp hp-init method-ptr)))
   :hints (("Goal" :in-theory (disable value-sig)))))



(skip-proofs
 (local 
  (defthm consistent-value-x-implies-tag-of-valid_local_type
    (implies (consistent-value-x v cl hp)
             (valid_local_type (tag-of v))))))



(local 
 (defthm valid-local-index-implies-nth-i-local-is-consistent-value-x
   (implies (and (valid-local-index i locals)
                 (integerp i)
                 (consistent-locals locals cl hp))
            (consistent-value-x (nth i locals) cl hp))))

;; this is a nice rule.. 


(local 
 (defthm valid-local-index-implies-nth-i-local-is-valid-type-sig
   (implies (and (valid-local-index i locals)
                 (integerp i)
                 (consistent-locals locals cl hp))
            (valid_local_type (tag-of (nth i locals))))
   :hints (("Goal" :in-theory (disable valid_local_type)))))



(local 
 (defthm valid-local-index-implies-nth-i-local-is-valid-type-sig-specific
   (implies (and (valid-local-index i (locals (current-frame s)))
                 (integerp i)
                 (consistent-state s))
            (valid_local_type (tag-of (nth i (locals (current-frame s))))))
   :hints (("Goal" :in-theory (disable valid_local_type)))))




(local 
 (defthm isAssignable-implies-isAssignable-x
   (implies (and (valid-local-index i (locals (current-frame s)))
                 (consistent-state s)
                 (integerp i)
                 (equal (instance-class-table s) cl)
                 (equal (heap s) hp)
                 (bcv::isAssignable (nth i (locals-sig (locals (current-frame
                                                                s)) cl hp
                                                                hp-init
                                                                method-ptr))
                                    type env))
            
           (bcv::isAssignable (value-sig (nth  i (locals (current-frame s)))
                                         cl hp hp-init method-ptr)
                              type env))
   :hints (("Goal" :in-theory (disable bcv::isAssignable)))))


(defthm isAssignable-reference-implies-REEp
  (implies  (and (bcv::isAssignable (nth i (locals-sig (locals (current-frame s))
                                                       (instance-class-table s)
                                                       (heap s)
                                                       (heap-init-map (aux s))
                                                       (method-ptr (current-frame
                                                                    s))))
                                    'reference
                                    (env-sig s))
                 (consistent-state s)
                 (integerp i)
                 (<= 0 i)
                 (equal (heap s) hp))
            (REFp (local-at i s) hp))
  :hints (("Goal" :in-theory (e/d (local-at) (REFp value-sig bcv::isAssignable 
                                                   valid_local_type))
           :do-not-induct t)))



    






