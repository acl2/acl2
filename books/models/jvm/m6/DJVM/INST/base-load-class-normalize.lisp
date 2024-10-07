(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")

(in-theory (disable getArrayClass resolveClassReference))


(local (include-book "base-load-class-normalize-support"))


(encapsulate () 
  (local (include-book "base-load-class-normalize-support"))
  (acl2::set-enforce-redundancy t)
  (defthm topStack-guard-strong-not-affected-by-class-loading
    (and (implies (consistent-state s) 
                ;; Wed Apr  7 11:29:37 2004 added 
                (equal (topStack-guard-strong (getArrayClass any s))
                       (topStack-guard-strong s)))
       (implies (consistent-state s)
                (equal (topStack-guard-strong (resolveClassReference any s))
                       (topStack-guard-strong s))))))





(defthm getArrayClass-does-not-affect-current-thread
  (and (equal (current-thread (getArrayClass any s)) 
              (current-thread s))
       (equal (thread-table (getArrayClass any s))
              (thread-table s))))



(defthm current-frame-getArrayClass
  (equal (current-frame (getArrayClass any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (getArrayClass)))))

(defthm current-frame-resolveClassReference
  (equal (current-frame (resolveClassReference any s))
         (current-frame s))
  :hints (("Goal" :in-theory (e/d (current-frame)
                                  (resolveClassReference)))))




(defthm build-an-array-instance-does-not-affect-s
  (equal (mv-nth 1 (build-an-array-instance base-type  bound s))
         s))


(defthm thread-by-id-popStack-is-popStack-of-thread
  (implies (and (consistent-state s)
                (equal (current-thread s) id))
           (equal (thread-by-id id
                                (thread-table (popstack s)))
                  (popstack-of-thread (thread-by-id (current-thread s)
                                                    (thread-table s))))))

;; this is likely to be wrong!! 

(defthm thread-call-stack-pop-stack-of-thread-is
  (equal (thread-call-stack (popSTACK-OF-THREAD thread))
         (push (frame-set-operand-stack (pop (operand-stack (top
                                                             (thread-call-stack thread))))
                                        (top (thread-call-stack thread)))
               (pop (thread-call-stack thread))))
  :hints (("Goal" :in-theory (e/d (popstack-of-thread) ()))))



(defthm deref-method-not-changing-if-exist-getArrayClass
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (deref-method method-ptr (instance-class-table
                                            (getArrayClass any s)))
                  (deref-method method-ptr (instance-class-table s)))))
                                 


(defthm deref-method-not-changing-if-exist-resolveClassReference
  (implies (and (consistent-state s)
                (equal (method-ptr (current-frame s)) method-ptr))
           (equal (deref-method method-ptr (instance-class-table
                                            (resolveClassReference any s)))
                  (deref-method method-ptr (instance-class-table s)))))


(defthm current-frame-make-state-normalize
   (implies (equal (current-thread s) tid)
            (equal (current-frame (make-state anypc 
                                              tid
                                              anyheap
                                              (thread-table s)
                                              anycl
                                              anyenv
                                              anyerror
                                               anyaux))
                   (current-frame s))))



(defthm current-frame-getArrayClass
  (equal (current-frame (getArrayClass any s))
         (current-frame s)))


(defthm current-frame-resolveClassReference
  (equal (current-frame (resolveClassReference any s))
         (current-frame s)))


;;; basic any operation that does not affect class-table!! 

(defthm build-an-array-instance-reduce
  (equal (CAR (BUILD-AN-ARRAY-INSTANCE anytype anyvalue (popStack s)))
         (CAR (BUILD-AN-ARRAY-INSTANCE anytype anyvalue s))))

;;; expect similiar rules!! 


(defthm class-table-no-change-popStack
  (equal (class-table (POPSTACK s))
         (class-table s)))



(defthm heap-no-change-popStack
  (equal (heap (POPSTACK s))
         (heap s)))


(defthm errorflag-no-change-popStack
  (equal (error-flag (POPSTACK s))
         (error-flag s)))


;; because we enabled update-trace. 
;; however we disabled state-set-heap
;; but enabled all accessors in state-set-heap
;; 
;; As a result, the normalized stuff is not recognizable!! 
;;
;; If we have expresed everything in terms of make-state...
;;
;;


;; (defthm consistent-state-make-state-heap-change
;;   (implies (and (consistent-state s)
;;                 (consistent-object obj hp (instance-class-table s))
;;                 (
;;                 (equal (pc s) pc)
;;                 (equal (current-thread s) tid)
;;                 (equal (class-table s) cl)
;;                 (equal (env s) env)
;;                 (equal (aux s) aux))
;;            (consistent-state (make-state pc tid 
;;                                          (bind (tag-ref (len (heap s)))
;;                                                obj 
;;                                                (heap s))
;;                                          cl 
;;                                          env aux)))))
;;;

;;; Wed May 25 13:42:00 2005                                                       
  
(in-theory (disable update-trace))



(defthm update-trace-reduce
  (and (equal (pc (update-trace any s))
              (pc s))
       (equal (current-thread (update-trace any s))
              (current-thread s))
       (equal (thread-table (update-trace any s))
              (thread-table s))
       (equal (heap  (update-trace any s))
              (heap  s))
       (equal (class-table  (update-trace any s))
              (class-table  s))
       (equal (heap-init-map (aux (update-trace any s)))
              (heap-init-map (aux s)))
       (equal (error-flag (update-trace any s))
              (error-flag s))
       (equal (current-frame (update-trace any s))
              (current-frame s)))
  :hints (("Goal" :in-theory (enable update-trace aux-set-trace))))


(local 
 (defthm pc-load-array-class-reduce
   (equal (pc (load_array_class any s))
          (pc s))))

;; (i-am-here) ;; Sun Aug  7 09:54:57 2005

(local 
 (defthm heap-init-map-load_cp_entry
   (equal (heap-init-map (aux (mv-nth 1 (load_cp_entry any s))))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d (load_cp_entry) (heap-init-map))))))

(local 
 (defthm heap-init-map-load_cp_entries
   (equal (heap-init-map (aux (mv-nth 1 (load_cp_entries cps s))))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d () (load_cp_entry heap-init-map))))))



(local 
 (defthm heap-init-map-load_class2
   (equal (heap-init-map (aux (load_class2 any s)))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d (load_class2) (heap-init-map))))))


(local 
 (defthm heap-init-map-load_class_x
   (equal (heap-init-map (aux (load_class_x any s seen mode)))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d (load_class_x) (load_class2 
                                                   heap-init-map))))))


(local 
 (defthm heap-init-map-load_array_class2
   (equal (heap-init-map (aux (load_array_class2 any s)))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d (load_array_class2) 
                                   (heap-init-map))))))


(local 
 (defthm heap-init-map-load_array_class
   (equal (heap-init-map (aux (load_array_class any s)))
          (heap-init-map (aux s)))
   :hints (("Goal" :in-theory (e/d (load_array_class) 
                                   (heap-init-map))))))





(defthm getArrayClass-reduce
  (and (equal (PC (GETARRAYCLASS any s))
              (pc s))
       (equal (current-thread (getarrayclass any s))
              (current-thread s))
       (equal (thread-table (getarrayclass any s))
              (thread-table s))
       (equal (current-frame (getarrayclass any s))
              (current-frame s))
       (equal (heap-init-map (aux (getarrayclass any s)))
              (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (getarrayclass)
                                  (heap-init-map)))))


;;; getArrayClass will change heap, 

(defthm resolveClassReference-reduce
  (and (equal (PC (resolveClassReference any s))
              (pc s))
       (equal (current-thread (resolveClassReference any s))
              (current-thread s))
       (equal (thread-table (resolveClassReference any s))
              (thread-table s))
       (equal (heap-init-map (aux (resolveClassReference any s)))
              (heap-init-map (aux s)))
       (equal (current-frame (resolveClassReference any s))
              (current-frame s)))
  :hints (("Goal" :in-theory (e/d (resolveClassReference)
                                  (heap-init-map)))))

 

(defthm resolveClassReference-reduce2
  (equal (topStack (resolveClassReference any s))
         (topStack s)))




;----------------------------------------------------------------------
;; Tue Jun  7 20:30:48 2005
;;


;; (skip-proofs 
;;  (defthm deref2-after-resolveClassReference
;;    (implies (and (REFp v (heap s))
;;                  (not (NULLp v)))
;;             (equal (deref2 v (heap (resolveClassReference any s)))
;;                    (deref2 v (heap s))))))


(include-book "base-load-class-normalize-deref2")
(include-book "base-load-class-normalize-class-by-name")