(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-bind-free")



(local 
 (defthm deref2-v-no-change-after-bind
   (implies (and (not (NULLp v))
                 (REFp v hp)
                 (not (bound? ref hp)))
            (equal (deref2 v (bind ref obj hp))
                   (deref2 v hp)))
   :hints (("Goal" :in-theory (e/d (deref2 binding bound? bind)
                                   (BINDING-RREF-NORMALIZE))
            :do-not '(preprocess)))))


(local (include-book "arithmetic-2/meta/top" :dir :system))


(local 
 (defthm consistent-heap1-implies-not-bound?-len-lemma
   (implies (and (consistent-heap1 hp1 hp cl id)
                 (bound? x hp1))
            (< x (+ id (len hp1))))
   :hints (("Goal" :in-theory (enable bound?)
            :do-not '(generalize)))))


(local 
 (defthm consistent-heap1-implies-not-bound?-len-local
   (implies (and (consistent-heap1 hp1 hp cl id)
                 (>= x (+ id (len hp1))))
            (not (bound? x hp1)))
   :hints (("Goal" :in-theory (enable bound?)
            :do-not '(generalize)))))





(local 
  (defthm consistent-state-implies-not-bound-local
    (implies (and (consistent-state s)
                  (equal (heap s) hp))
             (not (bound? (len hp)
                          (heap s))))
    :hints (("Goal" :in-theory (e/d (consistent-state) ())
             :use ((:instance consistent-heap1-implies-not-bound?-len-local
                              (hp1 (heap s))
                              (hp (heap s))
                              (id 0)
                              (x 0)
                              (cl (instance-class-table s))))))))




(local 
  (defthm consistent-state-implies-not-bound-2
    (implies (and (consistent-state s)
                  (equal (heap s) hp))
             (not (bound? (+ 1 (len hp))
                          (heap s))))
    :hints (("Goal" :in-theory (e/d (consistent-state) ())
             :use ((:instance consistent-heap1-implies-not-bound?-len-local
                              (hp1 (heap s))
                              (hp (heap s))
                              (id 0)
                              (x 1)
                              (cl (instance-class-table s))))))))


(local 
 (defthm len-bind-not-bound
   (implies (and (not (bound? ref hp))
                 (alistp hp))
            (equal (len (bind ref obj hp))
                   (+ 1 (len hp))))
   :hints (("Goal" :in-theory (enable bound? bind)))))



(local 
 (defthm REFp-remain-REFp-after-bind
   (implies (REFp v hp)
            (REFp v (bind x obj hp)))
   :hints (("Goal" :in-theory (enable REFp bound? bind)))))



(local 
 (defthm REFp-remains-REFp-load-cp-entry
   (implies (REFp v (heap s))
            (REFp v (heap (mv-nth 1 (load_cp_entry any s)))))
   :hints (("Goal" :in-theory (e/d (load_cp_entry) (REFp))))))




(encapsulate ()
 (local (include-book "base-loader-preserve-consistent-state"))
 (defthm consistent-state-implies-consistent-state-1
  (implies (consistent-state s)
           (consistent-state (mv-nth 1 (load_cp_entry cp s))))))


(local 
 (defthm not-bound-not-bound-after-bind
   (implies (and (not (bound? x hp))
                 (not (equal x y)))
            (not (bound? x (bind y obj hp))))
   :hints (("Goal" :in-theory (enable bound?)))))


(local 
 (defthm deref2-no-change-after-load-cp-entry
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (mv-nth 1 (load_cp_entry any s))))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (load_cp_entry)
                                   (REFp))))))


(local 
 (defthm deref2-no-change-after-load-cp-entries
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (mv-nth 1 (load_cp_entries cps s))))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d ()
                                   (REFp))))))




(encapsulate ()
 (local (include-book "base-loader-preserve-consistent-state"))
 (defthm consistent-state-preserved-by-load-cp-entries
   (implies (consistent-state s)
            (consistent-state (mv-nth 1 (load_cp_entries cps s))))))



(local 
 (defthm REFp-remains-REFp-load-cp-entries
   (implies (REFp v (heap s))
            (REFp v (heap (mv-nth 1 (load_cp_entries any s)))))
   :hints (("Goal" :in-theory (e/d () (REFp))))))


(local 
 (defthm deref2-no-change-after-load-class2
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (load_class2 any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (load_class2)
                                   (REFp))))))



(local 
 (encapsulate () 
  (local (include-book "base-loader-preserve-consistent-state"))
  (defthm consistent-state-load-class_x
    (implies (consistent-state s)
             (consistent-state (load_class_x any s seen mode)))
    :hints (("Goal" :in-theory (e/d (instance-class-table-inv)
                                    (fatalError
                                     consistent-state-step))
             :do-not '(generalize))))))



(local 
 (defthm REFp-remains-REFp-load-class2 
   (implies (REFp v (heap s))
            (REFp v (heap (load_class2 any s))))
   :hints (("Goal" :in-theory (e/d (load_class2) (REFp))))))


(local 
 (defthm REFp-remains-REFp-load-class-x
   (implies (REFp v (heap s))
            (REFp v (heap (load_class_x any s seen mode))))
   :hints (("Goal" :in-theory (e/d () (REFp))))))




(local 
 (defthm deref2-no-change-after-load-class-x
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (load_class_x any s seen mode)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d ()
                                   (REFp))
            :do-not '(generalize fertilize)))))



(local 
 (defthm deref2-no-change-after-load-class
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (load_class any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (load_class)
                                   (REFp))
            :do-not '(generalize fertilize)))))



(local 
 (defthm deref2-no-change-after-load-array-class2
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (load_array_class2 any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (load_array_class2)
                                   (REFp))
            :do-not '(generalize fertilize)))))



(local 
 (defthm REFp-remains-REFp-load-array-class2 
   (implies (REFp v (heap s))
            (REFp v (heap (load_array_class2 any s))))
   :hints (("Goal" :in-theory (e/d (load_array_class2) (REFp))))))



(local 
 (defthm REFp-remains-REFp-load-class
   (implies (REFp v (heap s))
            (REFp v (heap (load_class any s))))
   :hints (("Goal" :in-theory (e/d (load_class) (REFp))))))




(local 
 (defthm REFp-remains-REFp-load-array-class 
   (implies (REFp v (heap s))
            (REFp v (heap (load_array_class any s))))
   :hints (("Goal" :in-theory (e/d (load_array_class) (REFp))))))


(local 
 (encapsulate ()
  (local (include-book "base-loader-preserve-consistent-state"))
  (defthm load_class-preserve-consistency-general
    (implies (consistent-state s)
             (consistent-state (load_class any s))))

  (defthm load_array_class-preserve-consistency
    (implies (consistent-state s)
             (consistent-state (load_array_class any s))))))



(local 
 (defthm deref2-no-change-after-load-array-class
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (load_array_class any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (load_array_class)
                                   (REFp))
            :do-not '(generalize fertilize)))))



(local 
 (defthm deref2-no-change-after-resolveClassReference
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (resolveclassreference any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (resolveclassreference)
                                   (REFp))
            :do-not '(generalize fertilize)))))


(defthm REFp-remains-REFp-resolveCalssReference
   (implies (REFp v (heap s))
            (REFp v (heap (resolveClassReference any s))))
   :hints (("Goal" :in-theory (e/d (resolveClassReference) (REFp)))))




(local 
 (defthm deref2-no-change-after-getArrayClass 
   (implies (and (not (NULLp v))
                 (consistent-state s)
                 (REFp v (heap s)))
            (equal (deref2 v (heap (getArrayClass any s)))
                   (deref2 v (heap s))))
   :hints (("Goal" :in-theory (e/d (resolveclassreference)
                                   (REFp))
            :do-not '(generalize fertilize)))))


(defthm REFp-remains-REFp-getArrayClass
   (implies (REFp v (heap s))
            (REFp v (heap (getArrayClass any s))))
   :hints (("Goal" :in-theory (e/d (getArrayClass) (REFp)))))


(local
 (defthm consistent-value-x-not-REFp-primitive-type
   (implies (and (consistent-value-x v cl hp)
                 (not (REFp v hp)))
            (primitive-type? (tag-of v)))
   :hints (("Goal" :in-theory (enable consistent-value-x consistent-value)))))


(local 
 (defthm primitive-type?-implies-value-sig-is-tag
   (implies (primitive-type? (tag-of v))
            (equal (value-sig v cl hp hp-init method-ptr)
                   (djvm-translate-int-type (tag-of v))))
   :hints (("Goal" :in-theory (enable value-sig)))))



;; (local 
;;  (defthm deref2-v-no-change-after-bind
;;    (implies (and (not (NULLp v))
;;                  (REFp v hp)
;;                  (not (bound? ref hp)))
;;             (equal (deref2 v (bind ref obj hp))
;;                    (deref2 v hp)))
;;    :hints (("Goal" :in-theory (e/d (deref2 binding bound? bind)
;;                                    (BINDING-RREF-NORMALIZE))
;;             :do-not '(preprocess)))))


(local
 (defthm primitive-type?-not-REFp
   (implies (primitive-type? (tag-of v))
            (not (REFp v hp)))
   :hints (("Goal" :in-theory (enable primitive-type? REFp wff-REFp)))))


(local 
 (defthm NULLp-implies-REFp
   (implies (NULLp v)
            (REFp v hp))))



(defthm bind-new-obj-not-affect-value-sig
  (implies (and  (not (bound? ref hp))
                 (consistent-value-x v cl hp))
           (equal (value-sig v cl (bind ref obj hp) hp-init method-ptr)
                  (value-sig v cl hp hp-init method-ptr)))
  :hints (("Goal" :cases ((REFp v hp))
           :in-theory (e/d (value-sig) 
                           (REFp NULLp)))))

;----------------------------------------------------------------------

;; some facts about heap-init-map does not change!! 
;;

(defthm heap-init-map-no-change-load_cp_entry
  (equal (heap-init-map (aux (mv-nth 1 (load_cp_entry any s))))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_cp_entry))))


(defthm heap-init-map-no-change-load_cp_entries
  (equal (heap-init-map (aux (mv-nth 1 (load_cp_entries any s))))
         (heap-init-map (aux s))))



(defthm heap-init-map-no-change-load_class2
  (equal (heap-init-map (aux (load_class2 any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_class2))))


(defthm heap-init-map-no-change-load_class_x
  (equal (heap-init-map (aux (load_class_x any s seen mode)))
         (heap-init-map (aux s))))

(defthm heap-init-map-no-change-load_class
  (equal (heap-init-map (aux (load_class any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_class))))


(defthm heap-init-map-no-change-load_array_class2
  (equal (heap-init-map (aux (load_array_class2 any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_array_class2))))

(defthm heap-init-map-no-change-load_array_class
  (equal (heap-init-map (aux (load_array_class any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_array_class))))



(defthm heap-init-map-no-change-resolveClassReference
  (equal (heap-init-map (aux (resolveclassreference any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable resolveclassreference))))


(defthm heap-init-map-no-change-getArrayClass
  (equal (heap-init-map (aux (getArrayClass any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable getArrayClass))))




;----------------------------------------------------------------------

;; (defthm NULLp-implies-REFp
;;   (implies (NULLp v)
;;            (REFp v hp)))


(defthm value-sig-of-consistent-value-no-change-after-resolveClassReference
  (implies (and (equal (heap (resolveclassreference any s)) hp)
                (equal (heap-init-map (aux (resolveclassreference any s))) hp-init)
                (consistent-value-x v (instance-class-table s) (heap s))
                (consistent-state s))
           (equal (value-sig v 
                             (instance-class-table (resolveclassreference any s))
                             hp
                             hp-init
                             method-ptr)
                  (value-sig v
                             (instance-class-table s)
                             (heap s)
                             (heap-init-map (aux s))
                             method-ptr)))
  :hints (("Goal" :in-theory (e/d (value-sig)
                                  (REFp NULLp))
           :cases ((REFp v (heap s))))))



(defthm value-sig-of-consistent-value-no-change-after-getArrayClass
  (implies (and (equal (heap (getArrayClass any s)) hp)
                (equal (heap-init-map (aux (getArrayClass any s))) hp-init)
                (consistent-value-x v (instance-class-table s) (heap s))
                (consistent-state s))
           (equal (value-sig v 
                             (instance-class-table (getArrayClass any s))
                             hp
                             hp-init
                             method-ptr)
                  (value-sig v
                             (instance-class-table s)
                             (heap s)
                             (heap-init-map (aux s))
                             method-ptr)))
  :hints (("Goal" :in-theory (e/d (value-sig)
                                  (REFp NULLp))
           :cases ((REFp v (heap s))))))




