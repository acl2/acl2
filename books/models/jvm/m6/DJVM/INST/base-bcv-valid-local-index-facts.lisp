(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "base-locals")


;; (include-book "arithmetic/top-with-meta" :dir :system)


;; we will want consistent-locals 

;;(local (include-book "base-bcv"))


(local 
 (defthm nth-i-cons-is
   (implies (and (<= 0 i)
                 (integerp i))
            (equal (nth i (cons x l))
                   (if (> i 0)
                       (nth (- i 1) l)
                     x)))))




(local 
 (defthm if-out-of-range-implies-nil
   (implies (and (>= i (len (locals-sig locals cl hp hp-init method-ptr)))
                 (integerp i)
                 (consistent-locals locals cl hp))
            (equal (nth i (locals-sig locals cl hp hp-init method-ptr))
                   nil))
   :hints (("Goal" :in-theory (enable tag-of wff-REFp shift1slot category1
                                      shift2slot)))))


;;;
;;; the problem is nth -1 return the first element!! 
;;;

(local 
 (defthm equal-minus-one-minus-one-plus-negative-two
   (equal (+ -1 -1 i)
          (+ -2 i))))


;; (local 
;;  (defthm len-l-fact
;;    (>= (len l) 0)))

(local 
 (defthm fix-sig-never-bcv-top
   (not (equal (fix-sig any) 'topx))))

(local 
 (defthm consistent-value-x-not-equal-value-sig-top
   (implies (CONSISTENT-VALUE-X v CL HP)
            (not (equal (value-sig v cl hp hp-init method-ptr)
                        'topx)))
   :hints (("Goal" :in-theory (enable consistent-value-x consistent-value)))))


(local 
 (defthm consistent-value-x-facts
   (implies (and (NOT (PRIMITIVE-TYPE? (TAG-OF ACL2::LOCALS1)))
                 (NOT (EQUAL (TAG-OF ACL2::LOCALS1) 'REF)))
            (not (CONSISTENT-VALUE-X ACL2::LOCALS1 CL HP)))
   :hints (("Goal" :in-theory (enable consistent-value-x
                                      wff-tagged-value
                                      tag-of
                                      wff-REFp
                                      value-of
                                      consistent-value)))))


;; (i-am-here) ;; Sat May 21 19:22:18 2005

(local 
 (defthm nth-i-cons-is-2
   (implies (and (<= 0 i)
                 (not (equal i 0))
                 (integerp i))
            (equal (nth i (cons x l))
                   (nth (- i 1) l)))))






(local 
 (defthm not-valid-locals-implies-top
   (implies (and (not (valid-local-index i locals))
                 (<= 0 i)
                 (consistent-locals locals cl hp)
                 (integerp i)
                 (< i (len (locals-sig locals cl hp hp-init
                                       method-ptr))))
            (equal (nth i (locals-sig locals cl hp hp-init method-ptr))
                   'topx))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable value-sig)))))


(local 
 (defthm top-is-not-assignable-into-any-thing
   (implies (not (equal type 'topx))
            (not (bcv::isAssignable 'topx type env)))))
 

;----------------------------------------------------------------------

;;; the proof for the following is twisted
;;; 
;;; by cases: if i is within the range, if not valid-local-index, we know 
;;;           nth i reduce to bcv::top, thus not possible to be assignable to 'reference
;;;

;; (i-am-here) ;;  Sat May 21 19:09:18 2005


(local 
 (defthm isAssignable-implies-valid-local-index
   (implies  (and (bcv::isAssignable (nth i 
                                          (locals-sig locals cl hp hp-init
                                                      method-ptr))  
                                     'reference
                                     env)
                  (integerp i)
                  (<= 0 i)
                  (consistent-locals locals cl hp))
             (valid-local-index i locals))
   :hints (("Goal" :in-theory (e/d () (valid-local-index))
            :do-not-induct t
            :cases ((>= i (len (locals-sig locals cl hp hp-init
                                           method-ptr))))))))



;; specific version

(defthm isAssignable-reference-implies-valid-local-index-specific
   (implies  (and (bcv::isAssignable (nth i (locals-sig 
                                             (locals (current-frame s))
                                             (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s))))
                                     'reference
                                     (env-sig s))
                  (integerp i)
                  (<= 0 i)
                  (consistent-state s))
             (valid-local-index i (locals (current-frame s))))
   :hints (("Goal" :in-theory (e/d () (valid-local-index bcv::isAssignable))
            :use ((:instance isAssignable-implies-valid-local-index
                             (locals (locals (current-frame s)))
                             (cl (instance-class-table s))
                             (hp (heap s))
                             (hp-init (heap-init-map (aux s)))
                             (method-ptr (method-ptr (current-frame s)))
                             (env (env-sig s)))))))






;
; expect other similiar theorem. 
;
;----------------------------------------------------------------------

