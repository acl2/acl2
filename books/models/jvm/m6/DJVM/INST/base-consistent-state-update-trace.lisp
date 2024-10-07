(in-package "DJVM") 
(include-book "base-update-trace-normalize")

(local 
 (encapsulate ()
   (local (include-book "base-consistent-state-make-state"))
   (defthm consistent-state-make-state-x
     (implies (and (consistent-state s)
                   (equal (pc s) pc)
                   (wff-aux aux)
                   (equal (heap-init-map (aux s)) (heap-init-map aux))
                   (equal (current-thread s) cid))
              (consistent-state (make-state pc 
                                            cid 
                                            (heap s)
                                            (thread-table s)
                                            (class-table s)
                                            (env s)
                                            (error-flag s)
                                            aux))))))



(defthm consistent-state-update-trace
  (implies (consistent-state s)
           (consistent-state (update-trace any s)))
  :hints (("Goal" :in-theory (e/d (update-trace aux-set-trace) ()))))


(in-theory (disable update-trace))