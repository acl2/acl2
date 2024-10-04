(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-state")
(include-book "../../DJVM/consistent-state")

(local 
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
   :hints (("Goal" :in-theory (enable update-trace aux-set-trace)))))

