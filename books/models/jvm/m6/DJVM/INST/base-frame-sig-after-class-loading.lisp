(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base")
(include-book "base-consistent-state")



(encapsulate ()
  (local (include-book "base-value-sig-no-change-after-class-table-heap-extension"))
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
                               method-ptr)))))



(defthm opstack-sig-of-consistent-opstack-no-change-after-resolveClassReference
   (implies (and (equal (heap (resolveclassreference any s)) hp)
                 (equal (heap-init-map (aux (resolveclassreference any s))) hp-init)
                 (consistent-opstack stack (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (opstack-sig stack
                                (instance-class-table (resolveclassreference any s))
                                hp
                                hp-init
                                method-ptr)
                   (opstack-sig stack
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              method-ptr))))


(local 
 (defthm tag-of-topx-not-REFp
   (implies (equal (tag-of v) 'topx)
            (not (REFp v hp)))
   :hints (("Goal" :in-theory (enable REFp wff-REFp NULLp)))))

(local 
 (defthm equal-value-sig-implies-tag-of
   (implies (equal (tag-of v) 'topx)
            (equal (value-sig v cl hp hp-init method-ptr)
                   'topx))
   :hints (("Goal" :in-theory (enable value-sig)))))


(defthm local-sig-of-consistent-locals-no-change-after-resolveClassReference
   (implies (and (equal (heap (resolveclassreference any s)) hp)
                 (equal (heap-init-map (aux (resolveclassreference any s))) hp-init)
                 (consistent-locals locals (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (locals-sig locals
                                (instance-class-table (resolveclassreference any s))
                                hp
                                hp-init
                                method-ptr)
                   (locals-sig locals
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              method-ptr)))
   :hints (("Goal" :in-theory (e/d () (consistent-value-x))
            :do-not '(generalize))))

;; (i-am-here) ;; Sun Jul 31 14:44:25 2005
;;; made necessary by the change
;;; 

(encapsulate () 
   (local (include-book "base-value-sig-no-change-after-class-table-heap-extension"))
   (defthm heap-init-map-no-change-resolveClassReference
     (equal (heap-init-map (aux (resolveclassreference any s)))
            (heap-init-map (aux s)))
     :hints (("Goal" :in-theory (enable resolveclassreference)))))

(defthm equal-frame-sig-when-consistent-resolveClassReference
  (implies (and (consistent-frame frame
                                  (instance-class-table s)
                                  (heap s))
                (equal (heap (resolveClassreference any s)) hp)
                (equal (heap-init-map (aux (resolveClassreference any s)))
                       hp-init)
                (consistent-state s))
           (equal (frame-sig frame 
                             (instance-class-table (resolveClassreference any s))
                             hp
                             hp-init)
                  (frame-sig frame (instance-class-table s) (heap s) 
                             (heap-init-map (aux s)))))
  :hints (("Goal" :in-theory (e/d (frame-sig)
                                  (resolveClassreference 
                                   consistent-frame
                                   gen-frame-flags)))))




(encapsulate ()
 (local (include-book "base-value-sig-no-change-after-class-table-heap-extension"))
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
                              method-ptr)))))




(defthm opstack-sig-of-consistent-opstack-no-change-after-getArrayClass
   (implies (and (equal (heap (getArrayClass any s)) hp)
                 (equal (heap-init-map (aux (getArrayClass any s))) hp-init)
                 (consistent-opstack stack (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (opstack-sig stack
                                (instance-class-table (getArrayClass any s))
                                hp
                                hp-init
                                method-ptr)
                   (opstack-sig stack
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              method-ptr)))
   :hints (("Goal" :in-theory (disable getArrayClass value-sig))))



(defthm local-sig-of-consistent-locals-no-change-after-getArrayClass
   (implies (and (equal (heap (getArrayClass any s)) hp)
                 (equal (heap-init-map (aux (getArrayClass any s))) hp-init)
                 (consistent-locals locals (instance-class-table s) (heap s))
                 (consistent-state s))
            (equal (locals-sig locals
                                (instance-class-table (getArrayClass any s))
                                hp
                                hp-init
                                method-ptr)
                   (locals-sig locals
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))
                              method-ptr)))
   :hints (("Goal" :in-theory (e/d () (consistent-value-x value-sig getArrayClass))
            :do-not '(generalize))))


(encapsulate () 
   (local (include-book
           "base-value-sig-no-change-after-class-table-heap-extension"))
   (defthm heap-init-map-no-change-getArrayClass
     (equal (heap-init-map (aux (getArrayClass any s)))
            (heap-init-map (aux s)))
     :hints (("Goal" :in-theory (enable getArrayClass)))))

(defthm equal-frame-sig-when-consistent-getArrayClass
  (implies (and (consistent-frame frame
                                  (instance-class-table s)
                                  (heap s))
                (equal (heap (getArrayClass any s)) hp)
                (equal (heap-init-map (aux (getArrayClass any s))) hp-init)
                (consistent-state s))
           (equal (frame-sig frame 
                             (instance-class-table (getArrayClass any s))
                             hp
                             hp-init)
                  (frame-sig frame (instance-class-table s) (heap s) 
                             (heap-init-map (aux s)))))
  :hints (("Goal" :in-theory (e/d (frame-sig consistent-frame) (getArrayClass 
                                                                value-sig)))))



;; (encapsulate () 
;;  (local (include-book "base-loader-preserve-consistent-state"))
;;  (defthm consistent-state-implies-not-bound
;;    (implies (consistent-state s)
;;             (not (bound? (len (heap s))
;;                          (heap s))))))


(encapsulate ()
 (local (include-book "base-value-sig-no-change-after-class-table-heap-extension"))
 (defthm bind-new-obj-not-affect-value-sig
   (implies (and  (not (bound? ref hp))
                 (consistent-value-x v cl hp))
           (equal (value-sig v cl (bind ref obj hp) hp-init method-ptr)
                  (value-sig v cl hp hp-init method-ptr)))))


(defthm local-sig-of-consistent-locals-no-change-after-bind-new-object
   (implies (and  (not (bound? ref hp))
                  (consistent-locals locals cl hp))
            (equal (locals-sig locals
                               cl 
                               (bind ref obj hp)
                               hp-init
                               method-ptr)
                   (locals-sig locals
                               cl hp hp-init
                              method-ptr)))
   :hints (("Goal" :in-theory (e/d () (value-sig)))))




(defthm opstack-sig-of-consistent-locals-no-change-after-bind-new-object
   (implies (and  (not (bound? ref hp))
                  (consistent-opstack stack cl hp))
            (equal (opstack-sig stack
                                cl 
                                (bind ref obj hp)
                                hp-init
                                method-ptr)
                   (opstack-sig stack
                                cl hp hp-init
                                method-ptr)))
   :hints (("Goal" :in-theory (e/d () (value-sig)))))




(defthm equal-frame-sig-bind-extra-object
  (implies (and (not (bound? ref hp))
                (consistent-frame frame cl hp))
           (equal (frame-sig frame cl (bind ref obj hp) hp-init)
                  (frame-sig frame cl hp hp-init))))
