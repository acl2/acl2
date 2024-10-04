(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")

(defthm REFp-REFp-after-bind
   (implies (REFp v hp)
            (REFp v (bind ref obj hp)))
   :hints (("Goal" :in-theory (enable REFp wff-REFp bind bound? binding))))

(defthm binding-bind-ref-no-change
  (equal (binding ref (bind v obj hp))
         (if (equal ref v)
             obj
           (binding ref hp)))
  :hints (("Goal" :in-theory (enable binding bind))))



(defthm bind-bounded-consistent-value
   (implies (and (consistent-value tagged-value type cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-value tagged-value type cl (bind vx new-obj hp)))
   :hints (("Goal" :in-theory (e/d (consistent-value deref2)
                                   (REFp binding-rref-normalize))
            :cases ((REFp tagged-value hp)))))

(defthm bind-bounded-consistent-value-x
  (implies (and (consistent-value-x tagged-value cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-value-x tagged-value cl (bind vx new-obj hp)))
  :hints (("Goal" :in-theory (e/d (consistent-value-x deref2)
                                  (REFp binding-rref-normalize))
           :cases ((REFp tagged-value hp)))))


;----------------------------------------------------------------------

(defthm bind-bounded-consistent-opstack
   (implies (and (consistent-opstack stack cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-opstack stack cl (bind vx new-obj hp)))
   :hints (("Goal" :in-theory (e/d () (consistent-value-x REFp)))))


(defthm bind-bounded-consistent-locals
   (implies (and (consistent-locals locals cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-locals locals cl (bind vx new-obj hp)))
   :hints (("Goal" :in-theory (e/d () (consistent-value-x REFp)))))



(defthm bound?-still-bound?
   (implies (bound? x hp)
            (bound? x (bind ref any hp)))
   :hints (("Goal" :in-theory (enable bound? bind))))



(defthm bind-bounded-consistent-frame
   (implies (and (consistent-frame frame cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-frame frame cl (bind vx new-obj hp)))
   :hints (("Goal" :in-theory (e/d (consistent-frame) (consistent-value-x
                                                       REFp)))))



(defthm bind-bounded-consistent-call-stack
   (implies (and (consistent-call-stack call-stack cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-call-stack call-stack cl (bind vx new-obj hp))))



(defthm bind-bounded-consistent-thread-entry
   (implies (and (consistent-thread-entry thread cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-thread-entry thread cl (bind vx new-obj hp)))
   :hints (("Goal" :in-theory (disable REFp consistent-call-stack))))





(defthm bind-bounded-consistent-thread-table
   (implies (and (consistent-thread-table threads cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-thread-table threads cl (bind vx new-obj hp)))
  :hints (("Goal" :in-theory (disable consistent-thread-entry))))




;----------------------------------------------------------------------

(defthm bind-bounded-consistent-field
   (implies (and (consistent-field field field-decl cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-field field field-decl cl (bind vx new-obj hp))))


(defthm bind-bounded-consistent-fields
   (implies (and (consistent-fields fields field-decls cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-fields fields field-decls cl (bind vx new-obj hp))))



(defthm bind-bounded-consistent-immediate-instance
   (implies (and (consistent-immedidate-instance type fields  cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-immedidate-instance type fields cl (bind vx new-obj
                                                                 hp))))



(defthm bind-bounded-consistent-jvp
   (implies (and (consistent-jvp type field-lists  cl hp)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-jvp type field-lists cl (bind vx new-obj hp))))



(defthm bind-bounded-consistent-object
   (implies (and (consistent-object obj hp cl)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-object obj (bind vx new-obj hp) cl))
   :hints (("Goal" :in-theory (enable consistent-object))))
               




(defthm bind-bounded-consistent-heap1-1
   (implies (and (consistent-heap1 hp1 hp cl id)
                 (bound? vx hp)
                 (equal (obj-type new-obj) (obj-type (binding vx hp))))
            (consistent-heap1 hp1 (bind vx new-obj hp) cl id)))


(defthm bind-bounded-consistent-heap1-2
  (implies (and (consistent-heap1 hp1 hp cl id)
                (bound? vx hp1)
                (consistent-object new-obj hp cl))
           (consistent-heap1 (bind vx new-obj hp1) hp cl id))
  :hints (("Goal" :in-theory (e/d (bind bound?) (consistent-object)))))

(defthm bind-bounded-array-obj-consistent1
  (implies (and (array-obj-consistent1 data type hp cl)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (array-obj-consistent1 data type (bind vx new-obj hp) cl)))


(defthm bind-bounded-consistent-array-obj
  (implies (and (consistent-array-object obj hp cl acl)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-array-object obj (bind vx new-obj hp) cl acl))
  :hints (("Goal" :in-theory (enable consistent-array-object))))



(defthm bind-bounded-consistent-heap2-1
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-heap2 hp1 (bind vx new-obj hp) cl acl id)))

(defthm bind-bounded-consistent-heap2-2
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (bound? vx hp1)
                (consistent-object new-obj hp cl)
                (or (not (isArrayType (obj-type new-obj)))
                    (consistent-array-object new-obj hp cl acl)))
           (consistent-heap2 (bind vx new-obj hp1) hp cl acl id))
  :hints (("Goal" :in-theory (e/d (bind bound?) ()))))


                
(defthm wff-heap-strong-bind
  (implies (and (wff-heap-strong hp)
                (wff-obj-strong new-obj))
           (wff-heap-strong (bind vx new-obj hp)))
  :hints (("Goal" :in-theory (enable wff-heap))))

(defthm consistent-object-wff-obj-strong
  (implies (consistent-object obj hp cl)
           (wff-obj-strong obj))
  :rule-classes :forward-chaining)


(defthm bind-bounded-consistent-heap
  (implies (and (consistent-heap hp cl acl)
                (consistent-object new-obj hp cl)
                (or (not (isArrayType (obj-type new-obj)))
                    (consistent-array-object new-obj hp cl acl))
                (equal (obj-type new-obj) (obj-type (binding vx hp)))
                (bound? vx hp))
           (consistent-heap (bind vx new-obj hp) cl acl))
  :hints (("Goal" :in-theory (e/d (consistent-heap) (consistent-object
                                                     consistent-heap1 consistent-heap2))
           :do-not-induct t)))



;; (defthm consistent-heap-implies-alistp
;;   (implies (consistent-heap hp cl acl)
;;            (alistp hp))
;;   :hints (("Goal" :in-theory (enable consistent-heap)))
;;   :rule-classes :forward-chaining)



(defthm bind-bound-consistent-heap-init-state1
  (implies (and (consistent-heap-array-init-state1 hp cl acl hp-init)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-heap-array-init-state1 (bind vx new-obj hp)
                                              cl acl hp-init))
  :hints (("Goal" :in-theory (enable bind bound? binding))))


(defthm bind-bound-consistent-heap-init-state2
  (implies (consistent-heap-array-init-state2 hp hp-init)
           (consistent-heap-array-init-state2 (bind vx new-obj hp)
                                               hp-init))
  :hints (("Goal" :in-theory (enable bind bound? binding))))


(defthm bind-bound-consistent-heap-init-state3
  (implies (and (consistent-heap-array-init-state3 hp hp-init)
                (or (not (isArrayType (obj-type new-obj)))
                    (and (wff-internal-array new-obj)
                         (OR (PRIMITIVE-TYPE? (array-component-type (obj-type new-obj)))
                             (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA new-obj)
                                                        HP-INIT)))))
           (consistent-heap-array-init-state3 (bind vx new-obj hp)
                                               hp-init))
  :hints (("Goal" :in-theory (enable bind bound? binding))))


(defthm bind-bound-consistent-heap-init-state
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp)))
                (or (not (isArrayType (obj-type new-obj)))
                    (and (wff-internal-array new-obj)
                         (OR (PRIMITIVE-TYPE? (array-component-type (obj-type new-obj)))
                             (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA new-obj)
                                                        HP-INIT)))))
           (consistent-heap-array-init-state (bind vx new-obj hp)
                                             cl acl hp-init)))





(defthm bind-bounded-consistent-static-field
  (implies (and (consistent-static-field name fields cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-static-field name fields cl (bind vx new-obj hp))))



(defthm bind-bounded-consistent-static-fields
  (implies (and (consistent-static-fields name fields cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-static-fields name fields cl (bind vx new-obj hp))))


(defthm bind-bounded-consistent-pool-entry
  (implies (and (consistent-constantpool-entry cp hp cl)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-constantpool-entry cp (bind vx new-obj hp) cl)))


(defthm bind-bounded-consistent-pool
  (implies (and (consistent-constantpool cps hp cl)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-constantpool cps (bind vx new-obj hp) cl)))


(defthm bind-bounded-consistent-decl
  (implies (and (consistent-class-decl crep cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-class-decl crep cl (bind vx new-obj hp))))


(defthm bind-bounded-consistent-decls 
  (implies (and (consistent-class-decls cl1 cl hp)
                (bound? vx hp)
                (equal (obj-type new-obj) (obj-type (binding vx hp))))
           (consistent-class-decls cl1 cl (bind vx new-obj hp))))

;(i-am-here)

(local (in-theory (disable state-set-heap wff-state jvm::loader-inv-helper)))


(defthm state-set-heap-loader-inv
  (implies (wff-state s)
           (equal (jvm::loader-inv (state-set-heap hp s))
                  (jvm::loader-inv s)))
  :hints (("Goal" :in-theory (enable jvm::loader-inv no-fatal-error?))))

(defthm state-set-heap-class-loaded?
  (equal (class-loaded? any (state-set-heap hp s))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?))))


(defthm state-set-heap-build-a-java-instance-data-guard
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-data-guard any (state-set-heap hp s))
                  (build-a-java-visible-instance-data-guard any s))))


(defthm state-set-heap-build-a-java-instance-guard
  (implies (wff-state s)
           (equal (build-a-java-visible-instance-guard any (state-set-heap hp s))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard) ()))))

                                  


(defthm state-set-heap-array-class-correctly-loaded?
  (implies (wff-state s)
           (equal (jvm::array-class-correctly-loaded? l (state-set-heap hp s))
                  (jvm::array-class-correctly-loaded? l s)))
  :hints (("Goal" :in-theory (e/d (array-base-type)
                                  (state-set-heap)))))
  


(defthm state-set-heap-array-class-table-inv-helper
  (implies (wff-state s)
           (equal (jvm::array-class-table-inv-helper l (state-set-heap hp s))
                  (jvm::array-class-table-inv-helper l s))))


(defthm wff-heap-bind-wff-heap
  (implies (wff-heap hp)
           (wff-heap (bind ref obj hp)))
  :hints (("Goal" :in-theory (enable wff-heap bind))))




;; (defthm consistent-state-modify-object
;;   (implies (and (consistent-state s)
;;                 (consistent-object new-obj (heap s) (instance-class-table s))
;;                 (or (not (isArrayType (obj-type new-array)))
;;                     (and (consistent-array-object new-array (heap s)
;;                                                   (instance-class-table s)
;;                                                   (array-class-table s))
;;                          (or (primitive-type? (array-component-type (obj-type
;;                                                                      new-array)))
;;                              (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA new-obj)
;;                                                         (heap-init-map (aux s))))))
;;                 (equal (heap s) hp)
;;                 (bound? (rREF v) hp)
;;                 (equal (obj-type (deref2 v (heap s)))
;;                        (obj-type new-array)))
;;            (consistent-state (state-set-heap 
;;                               (bind (rREF v) new-obj hp) s)))
;;   :hints (("Goal" :in-theory (e/d (consistent-state)
;;                                   (state-set-heap consistent-heap
;;                                                   consistent-object))
;;            :do-not-induct t)))

