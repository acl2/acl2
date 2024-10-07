(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")


(defthm mv-nth-1-set-element-at
  (equal (mv-nth 1 (set-element-at index value array s))
         s))



(local 
 (encapsulate ()
  (local (include-book "base-consistent-state-step-definition"))
  (defun consistent-state-step (s)
    (and
     (wff-state s)
     (wff-env (env s))
     (wff-aux (aux s))
     (alistp (heap-init-map (aux s)))
     (wff-heap-init-map-strong (heap-init-map (aux s)))
     (wff-class-table (class-table s))
     (wff-instance-class-table-strong (instance-class-table s))
     (wff-array-class-table (array-class-table s))
     (wff-static-class-table-strong (external-class-table s))
     (wff-methods-instance-class-table-strong
      (instance-class-table s))
     (consistent-class-hierachy (instance-class-table s))
     (consistent-heap (heap s)
                      (instance-class-table s)
                      (array-class-table s))
     (consistent-heap-init-state (heap s)
                                 (instance-class-table s)
                                 (heap-init-map (aux s)))
     (consistent-heap-array-init-state (heap s)
                                       (instance-class-table s)
                                       (array-class-table s)
                                       (heap-init-map (aux s)))
     (consistent-class-table (instance-class-table s)
                             (external-class-table s)
                             (heap s))
     (consistent-thread-table (thread-table s)
                              (instance-class-table s)
                              (heap s))
     (unique-id-thread-table (thread-table s))
     (thread-exists? (current-thread s)
                     (thread-table s))
     (instance-class-table-inv s)
     (array-class-table-inv s)
     (boot-strap-class-okp s)
     (equal (bcv::scl-bcv2jvm
             (bcv::scl-jvm2bcv (external-class-table s)))
            (external-class-table s))
     (bcv::good-scl (bcv::scl-jvm2bcv (external-class-table s)))))))


(local (include-book "base-consistent-state-modifying-object"))
(local (include-book "base-consistent-state-step-properties"))

(local 
 (defthm state-set-heap-loader-inv
   (implies (wff-state s)
            (equal (jvm::loader-inv (state-set-heap hp s))
                   (jvm::loader-inv s)))
   :hints (("Goal" :in-theory (enable jvm::loader-inv no-fatal-error?)))))

(local 
 (defthm state-set-heap-class-loaded?
   (equal (class-loaded? any (state-set-heap hp s))
          (class-loaded? any s))
   :hints (("Goal" :in-theory (enable class-loaded?)))))



(defthm state-set-heap-build-a-java-instance-data-guard
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-data-guard any (state-set-heap hp s))
                  (build-a-java-visible-instance-data-guard any s))))





(local
 (defthm state-set-heap-build-a-java-instance-guard
   (implies (wff-state s)
            (equal (build-a-java-visible-instance-guard any (state-set-heap hp s))
                   (build-a-java-visible-instance-guard any s)))
   :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard) (state-set-heap))))))



(local 
 (defthm state-set-heap-array-class-correctly-loaded?
   (implies (wff-state s)
            (equal (jvm::array-class-correctly-loaded? l (state-set-heap hp s))
                   (jvm::array-class-correctly-loaded? l s)))
   :hints (("Goal" :in-theory (e/d (array-base-type)
                                   (state-set-heap))))))
  

(local 
 (defthm state-set-heap-array-class-table-inv-helper
   (implies (wff-state s)
            (equal (jvm::array-class-table-inv-helper l (state-set-heap hp s))
                   (jvm::array-class-table-inv-helper l s)))
   :hints (("Goal" :in-theory (e/d () (state-set-heap))))))


(local 
 (defthm consistent-array-object-implies-wff-internal-array-f
   (implies (consistent-array-object obj hp cl acl)
            (wff-internal-array obj))
   :hints (("Goal" :in-theory (enable consistent-array-object)))
   :rule-classes :forward-chaining))

;; (i-am-here) ;; Sat Jul 16 17:16:19 2005

(local (in-theory (disable bcv::good-scl)))

(local 
 (defthm boot-strap-class-okp-implies-class-exists?
   (implies (boot-strap-class-okp s)
            (class-exists? "java.lang.Object"
                           (instance-class-table s)))
   :rule-classes :forward-chaining))


; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(local 
 (defthm consistent-state-implies-class-exists?
   (implies (consistent-state s)
            (class-exists? "java.lang.Object"
                           (instance-class-table s)))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   (boot-strap-class-okp))))
   :rule-classes :forward-chaining))


;; (i-am-here) ;; Thu Jul 21 16:49:46 2005

(skip-proofs 
 (defthm consistent-state-implies-bind-any-object
   (implies (and (consistent-state s)
                 (consistent-object obj (heap s) (instance-class-table s)))
            (CONSISTENT-HEAP-INIT-STATE (BIND (RREF V) OBJ (HEAP S))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP-INIT-MAP (AUX S))))))

(local 
 (defthm consistent-state-bind-consistent-object-of-same-type-preserves-consistent-state
   (implies (and (consistent-state s)
                 (REFp v (heap s))
                 (not (NULLp v))
                 (or (not (isArrayType (obj-type (deref2 v (heap s)))))
                     (and (consistent-array-object obj (heap s) (instance-class-table s)
                                                   (array-class-table s))
                          (or (primitive-type? (array-component-type (obj-type obj)))
                              (array-content-initialized (array-data obj)
                                                         (heap-init-map (aux s))))))
                 (consistent-object obj (heap s) (instance-class-table s))
                 (equal (obj-type obj) (obj-type (deref2 v (heap s))))
                 (equal (heap s) hp))
            (consistent-state-step (state-set-heap (bind (rREF v) obj hp)
                                                   s)))
   :hints (("Goal" :in-theory (e/d (consistent-state-step
                                    )
                                   (consistent-heap REFp NULLp
                                                    state-set-heap
                                    consistent-heap-array-init-state))
            :do-not-induct t))))


(local 
 (defthm consistent-state-step-implies-consistent-state
   (implies (consistent-state-step s)
            (consistent-state s))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes nil))


(local (defthm consistent-state-step-consistent-state-state-set-heap
         (implies (consistent-state-step (state-set-heap hp s))
                  (consistent-state (state-set-heap hp s)))
         :hints (("Goal" :use ((:instance
                                consistent-state-step-implies-consistent-state
                                (s (state-set-heap hp s))))))))



(defthm consistent-state-bind-consistent-object-of-same-type-preserves-consistent-state-general
  (implies (and (consistent-state s)
                 (REFp v (heap s))
                 (not (NULLp v))
                 (or (not (isArrayType (obj-type (deref2 v (heap s)))))
                     (and (consistent-array-object obj (heap s) (instance-class-table s)
                                                   (array-class-table s))
                          (or (primitive-type? (array-component-type (obj-type obj)))
                              (array-content-initialized (array-data obj)
                                                         (heap-init-map (aux s))))))
                 (consistent-object obj (heap s) (instance-class-table s))
                 (equal (obj-type obj) (obj-type (deref2 v (heap s))))
                 (equal (heap s) hp))
            (consistent-state (state-set-heap (bind (rREF v) obj hp)
                                              s)))
  :hints (("Goal" :in-theory (e/d ()
                                  (consistent-state-step state-set-heap)))))



(in-theory (disable set-element-at state-set-heap))





            
                   
                
                
