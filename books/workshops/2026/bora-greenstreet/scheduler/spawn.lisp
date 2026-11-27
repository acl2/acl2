; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "network")

; To spawn a process, we need a new unique PID. Since multiple processes can invoke
; it at the same, spawn must be a blocking operation like receive, where the scheduler
; can decide to add the new process to the network and pass its PID to a process that has
; requested the spawn.

; Some Helpers ----------------------------------------------------------------

; Show that the order of the spawned PIDs decrease.
; TODO: This lemma will have to change if the natp representation of pids changes.
(local (defrule order-of-make-pid
  (implies (pid-p p) (<< p (erl-val-pid (+ 1 (erl-val-pid->id p)))))
  :in-theory
    (e/d*
      (pid-p erl-val-kind erl-val-pid erl-val-pid->id set::order-rules)
      (list-order))
  :expand ((erl-val-p p))
  :use (:instance list-order (a p) (b (list :pid (+ 1 (cadr p)))))
  :prep-books ((include-book "arithmetic/top" :dir :system)
               (include-book "std/lists/len" :dir :system))
  :prep-lemmas
    ((defrule list-order
       (implies
         (and a b (true-listp a) (true-listp b) (car a) (car b) (cadr a) (cadr b)
              (equal (car a) (car b)) (not (equal (cadr a) (cadr b)))
              (not (cddr a)) (not (cddr b)) (<< (cadr a) (cadr b)))
         (<< a b))
       :enable (<< lexorder))
     (defrule natp-order
       (implies (natp x) (<< x (+ 1 x))) :enable (<< lexorder alphorder)))))

(local (defrule set-order
  (implies (and (not (set::emptyp s)) (not (set::emptyp (set::tail s))))
           (<< (set::head s) (set::head (set::tail s))))
  :in-theory (enable* set::order-rules)))

; Spawn -----------------------------------------------------------------------

; It does not matter how a PID is chosen as long as it is unique.
(encapsulate
  (((spawn *) => * :formals (pids) :guard (pid-set-p pids)))

  (local (in-theory (enable* set::definitions)))

  ; witness function
  (local (define spawn ((pids pid-set-p))
    :returns pid
    :measure (set::cardinality (pid-set-fix pids))
    :guard-hints (("Goal" :in-theory (enable pid-set-p pid-p set::head)))
    (b* ((pids (pid-set-fix pids))
         ((if (set::emptyp pids)) '(:pid 0))
         ((if (set::emptyp (set::tail pids)))
          (make-erl-val-pid :id (+ 1 (erl-val-pid->id (set::head pids))))))
        (spawn (set::tail pids)))))
  
  ; spawn returns a PID
  (more-returns spawn
    (pid :name pid-p-of-spawn :rule-classes :type-prescription
      pid-p :hints (("Goal" :in-theory (enable spawn pid-p)))))
  
  (defcong pid-set-equiv equal (spawn pids) 1
    :hints (("Goal" :in-theory (enable spawn))))

  ; TODO: This will have to change if the natp representation of pids changes.
  (local (defruled order-of-spawn
    (implies (pid-set-p pids) (<< (set::head pids) (spawn pids)))
    :in-theory (e/d (spawn) (set-order))
    :hints (("Subgoal *1/4" :use (:instance set-order (s pids)))
            ("Subgoal *1/2" :in-theory (enable set::head pid-set-p)
                            :expand (spawn pids)))))

  ; the new PID is unique
  (defrule unique-pid-of-spawn
    (implies (pid-set-p pids) (not (set::in (spawn pids) pids)))
    :in-theory (enable* spawn set::order-rules)
    :hints (("Subgoal *1/4" :use (:instance order-of-spawn)))))

; an executable counterpart for spawn
(define simple-spawn ((pids pid-set-p))
  :returns pid
  :measure (set::cardinality (pid-set-fix pids))
  :prepwork ((local (in-theory (enable* set::definitions))))
  :guard-hints (("Goal" :in-theory (enable pid-set-p pid-p set::head)))
  (b* ((pids (pid-set-fix pids))
        ((if (set::emptyp pids)) '(:pid 0))
        ((if (set::emptyp (set::tail pids)))
        (make-erl-val-pid :id (+ 1 (erl-val-pid->id (set::head pids))))))
      (simple-spawn (set::tail pids)))
  ///
    (more-returns
      (pid :name pid-p-of-simple-spawn :rule-classes :type-prescription
       pid-p :hints (("Goal" :in-theory (enable simple-spawn pid-p)))))
  
    (defcong pid-set-equiv equal (simple-spawn pids) 1
      :hints (("Goal" :in-theory (enable simple-spawn))))
    
    (local (defruled order-of-simple-spawn
      (implies (pid-set-p pids) (<< (set::head pids) (simple-spawn pids)))
      :in-theory (e/d (simple-spawn) (set-order))
      :hints (("Subgoal *1/4" :use (:instance set-order (s pids)))
              ("Subgoal *1/2" :in-theory (enable set::head pid-set-p)
                              :expand (simple-spawn pids)))))

    (defrule unique-pid-of-simple-spawn
      (implies (pid-set-p pids) (not (set::in (simple-spawn pids) pids)))
      :in-theory (enable* simple-spawn set::order-rules)
      :hints (("Subgoal *1/4" :use (:instance order-of-simple-spawn))))

    (defattach spawn simple-spawn))

; More theorems about spawn
(defrule unique-pid-of-spawn-on-network
 (implies
  (and (pid-set-p pids) (set::subset (omap::keys net) pids))
  (not (set::in (spawn pids) (omap::keys net))))
  :use ((:instance set::subset-in-2
          (a (spawn pids)) (x (omap::keys net)) (y pids))))

(defrule not-assoc-of-spawn-on-network
  (implies (and (pid-set-p pids) (set::subset (omap::keys net) pids))
           (not (omap::assoc (spawn pids) net)))
  :enable omap::assoc-to-in-of-keys)

(defrule spawned-pid-not-in-pids
  (implies (and (pid-set-p pids) (set::in p pids))
           (not (equal p (spawn pids)))))

(defrule spawned-pid-not-in-pids-rev
  (implies (and (pid-set-p pids) (set::in p pids))
           (not (equal (spawn pids) p))))