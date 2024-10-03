(in-package "DJVM")

(include-book "../../DJVM/consistent-state-obj-init")
(include-book "../../DJVM/consistent-state-strong")
(include-book "../../DJVM/consistent-state-obj-init-properties-export")




(in-theory (disable NULLp initialized-ref))

(defthm len-update-nt-specific
  (implies (< i (len locals))
           (EQUAL
            (LEN (IF (< i '0)
                     locals
                     (IF (EQUAL (TYPE-SIZE (TAG-OF (NTH i locals)))
                                '1)
                         locals
                         (UPDATE-NTH i
                                     '(TOPX . TOPX)
                                     locals))))
            (LEN locals))))

(defthm thread-by-id-back-chain-consistent-state
  (implies (and (consistent-state s)
                (equal (current-thread s) id))
           (THREAD-BY-ID id (THREAD-TABLE s))))



(defthm tag-of-tag-non-primitive-type
  (implies (not (primitive-type? type))
           (equal (tag-of (tag v type))
                  'REF))
  :hints (("Goal" :in-theory (enable tag tag-of ))))


(defthm value-of-tag-is-v
  (equal (value-of (tag v type))
         v)
  :hints (("Goal" :in-theory (enable tag value-of))))


(in-theory (disable deref2-init))


;; this following case could not handled by consistent-state!! 
;; because the intermediate state is not consistent-state

;; ;; (defthm thread-by-id-back-chain-consistent-state
;; ;;   (implies (and (consistent-state s)
;; ;;                 (equal (current-thread s) id))
;; ;;            (THREAD-BY-ID id (THREAD-TABLE s))))


;;(i-am-here) ;; Mon Aug  8 12:51:58 2005


(local 
 (defthm thread-by-id-replace-entry-local
   (implies (and (thread-by-id id tt)
                 (equal (thread-id new)
                        (thread-id old))
                 new)
            (thread-by-id id (replace-thread-table-entry
                               old new tt)))
   :hints (("Goal" :do-not '(generalize)))))


(defthm thread-by-id-back-chain-topx-topx
  (implies (thread-by-id id (thread-table s))
           (THREAD-BY-ID id (THREAD-TABLE (pushStack '(topx . topx) s))))
  :hints (("Goal" :in-theory (enable pushStack))))

(local 
 (defthm thread-by-id-consp-replace-entry
   (implies (and (consp (thread-call-stack (thread-by-id id tt)))
                 (equal (thread-id new) (thread-id old))
                 (consp (thread-call-stack new)))
            (consp (thread-call-stack (thread-by-id id
                                                    (replace-thread-table-entry 
                                                        old 
                                                        new tt)))))
   :hints (("Goal" :do-not '(generalize)))))


(local 
 (defthm thread-id-push-stack-of-thread
   (equal (thread-id (push-Stack-of-thread any thread))
          (thread-id thread))
   :hints (("Goal" :in-theory (enable push-Stack-of-thread)))))


(local 
 (defthm consp-thread-call-stack-push-stack-of-thread
   (consp (thread-call-stack (push-Stack-of-thread any thread)))
   :hints (("Goal" :in-theory (enable push-Stack-of-thread thread-call-stack)))))

(defthm thread-by-id-back-chain-topx-topx-consp
  (implies (consp (thread-call-stack (thread-by-id id (thread-table s))))
           (consp (thread-call-stack (THREAD-BY-ID id 
                                                   (THREAD-TABLE 
                                                    (pushStack '(topx . topx) s))))))
  :hints (("Goal" :in-theory (enable pushStack))))



(defthm wff-tagged-value-tag-REF
  (WFF-TAGGED-VALUE
   (TAG-REF (len x)))
  :hints (("Goal" :in-theory (enable wff-tagged-value tag-ref value-of
                                     tag-of))))





(defthm heap-init-map-s-pending-exception-no-change
  (equal (heap-init-map (acl2::s 'pending-exception any aux))
         (heap-init-map aux))
  :hints (("Goal" :in-theory (enable heap-init-map))))


;----------------------------------------------------------------------

(local 
 (encapsulate ()
   (local (include-book "base-loader-preserve-consistent-state"))
   (defthm consistent-state-implies-not-bound-len-heap
     (implies (consistent-state s)
              (not (bound? (len (heap s)) (heap s)))))

   
   (defthm consistent-heap-array-init-state2-bound-bound-b
     (implies (and (consistent-heap-array-init-state2 hp hp-init)
                   (not (bound? ref hp)))
              (not (bound? ref hp-init)))
     :hints (("Goal" :in-theory (enable bound?))))))


(local  
 (defthm consistent-state-implies-consistent-heap-array-init-state-2
   (implies (consistent-state s)
            (consistent-heap-array-init-state2 (heap s) 
                                               (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (enable consistent-state)))))
   

(local 
 (defthm consistent-state-implies-not-bind-len-heap-init-2
   (implies (and (consistent-state s)
                 (equal (heap-init-map (aux s)) hp-init))
            (not (bound? (len (heap s))
                         hp-init)))
   :hints (("Goal" :in-theory (disable bound? heap-init-map)
            :restrict ((consistent-heap-array-init-state2-bound-bound-b
                        ((hp (heap s)))))))))

(defthm consistent-state-implies-len-heap-new-obj
  (implies (and (consistent-state s)
                (equal (heap-init-map (aux s)) hp-init))
           (INITIALIZED-REF (len (heap s))
                            hp-init))
  :hints (("Goal" :in-theory (e/d (initialized-ref) (bound?)))))

;----------------------------------------------------------------------






