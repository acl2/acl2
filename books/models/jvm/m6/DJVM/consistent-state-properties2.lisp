(in-package "DJVM")
(include-book "consistent-state")
(include-book "djvm-frame-manipulation-primitives")

(in-theory (disable consistent-state consistent-thread-entry))

(include-book "INST/base-bind-free")

(defthm consistent-state-imlies-thread-by-id
  (implies (consistent-state s)
           (thread-by-id (current-thread s) 
                         (thread-table s)))
  :hints (("Goal" :in-theory (enable consistent-state thread-exists?))))



(defthm consistent-state-implies-consistent-thread-entries
  (implies (and (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp))
           (consistent-thread-entries (thread-table s) cl hp))
  :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-thread-entries-implies-consistent-thread
  (implies (and (thread-by-id id tt)
                (consistent-thread-entries tt cl hp))
           (consistent-thread-entry (thread-by-id id tt)
                                    cl hp))
  :hints (("Goal" :in-theory (enable thread-by-id))))



(defthm consistent-thread-entry-implies-consp-thread-call-stack
  (implies  (and (syntaxp (acl2::found-symbol2 's thread))
                 (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                 (consistent-thread-entry thread 
                                          (instance-class-table s)
                                          (heap s)))
            (consp (thread-call-stack thread)))
  :hints (("Goal" :in-theory (enable consistent-thread-entry))))

;----------------------------------------------------------------------

;;(i-am-here) 

(encapsulate ()
  (local (include-book "consistent-state-properties"))
  (local 
    (defthm consistent-state-topstack-consistent-value-x
      (implies (and (topStack-guard-strong s)
                    (consistent-state s))
               (consistent-value-x (safe-topStack s) 
                                   (instance-class-table s)
                                   (heap s)))
      :rule-classes :forward-chaining))

 (defthm consistent-value-x-implies-wff-tagged-value
   (implies (consistent-value-x v cl hp)
            (wff-tagged-value v))
   :rule-classes :forward-chaining)

 (local 
  (defthm safe-topStack-is-topStack 
    (equal (safe-topStack s)
           (topStack s))
    :hints (("Goal" :in-theory (enable safe-topStack topStack
                                       current-frame)))))


 (defthm consistent-state-topstack-consistent-value-x-2
   (implies (and (topStack-guard-strong s)
                 (consistent-state s))
            (consistent-value-x (topStack s)
                                (instance-class-table s)
                                (heap s)))
   :hints (("Goal" :in-theory (disable safe-topStack 
                                       topStack  consistent-value-x)
            :use ((:instance consistent-state-topstack-consistent-value-x))))
   :rule-classes :forward-chaining))


(in-theory (disable topStack safe-topStack consistent-value-x 
                    topStack-guard-strong))
              
     