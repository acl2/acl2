; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(include-book "tools/pattern-match" :dir :system)
(set-ignore-ok t)

(defconst *fence-0*
  (list (immov 1 'x)
        (fence)
        (mrmov 'y 'ry)))

(defconst *fence-1*
  (list (immov 1 'y)
        (fence)
        (mrmov 'x 'rx)))

(define fence-p ((m machine-p))
  :returns (fence? booleanp)
  :enabled t
  (and (machine-p m)
       (equal (num-procs m) 2)
       (equal (proc->program (nth 0 (machine->procs m))) *fence-0*)
       (equal (proc->program (nth 1 (machine->procs m))) *fence-1*)))

;; exhaustive invariant
(define inv ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (fence-p m)) nil)
    ((proc proc0) (nth 0 m.procs))
    ((proc proc1) (nth 1 m.procs))
    ((unless (no-pending m 0 'y)) nil)
    ((unless (no-pending m 1 'x)) nil)
    ((unless (not-blocked m 0)) nil)
    ((unless (not-blocked m 1)) nil))
   (pml 
    (proc0.pc proc1.pc)
    ;; cases
    ((0 0) t)
    ((0 1) (equal (lookup-addr m 1 'y) 1))
    ((0 2) (and (no-pending m 1 'y)
                (equal (lookup-addr-mem m 'y) 1)))
    ((0 3) (and (no-pending m 1 'y)
                (equal (lookup-addr-mem m 'y) 1)))
    ((1 0) (equal (lookup-addr m 0 'x) 1))
    ((1 1) (and (equal (lookup-addr m 1 'y) 1)
                (equal (lookup-addr m 0 'x) 1)))
    ;; don't care about phase of proc1
    ((1 2) (and (no-pending m 1 'y)
                (equal (lookup-addr-mem m 'y) 1)))
    ((1 3) (and (no-pending m 1 'y)
                (equal (lookup-addr-mem m 'y) 1)))
    ((2 0) (and (no-pending m 0 'x)
                (equal (lookup-addr-mem m 'x) 1)))
    ;; don't care about phase of proc0
    ((2 1) (and (no-pending m 0 'x)
                (equal (lookup-addr-mem m 'x) 1)))
    ((2 2)
     (or
      (and (no-pending m 1 'y)
           (equal (lookup-addr-mem m 'y) 1)
           (case proc0.phase
             (0 t)
             (1 t)
             (2 (equal proc0.tmp-data 1))
             (otherwise nil)))
      (and (no-pending m 0 'x)
           (equal (lookup-addr-mem m 'x) 1)
           (case proc1.phase
             (0 t)
             (1 t)
             (2 (equal proc1.tmp-data 1))
             (otherwise nil)))))
    ((2 3)
     (or
      (and (no-pending m 1 'y)
           (equal (lookup-addr-mem m 'y) 1)
           (case proc0.phase
             (0 t)
             (1 t)
             (2 (equal proc0.tmp-data 1))
             (otherwise nil)))
      (equal (read-reg m 1 'rx) 1)))
    ((3 0) (and (no-pending m 0 'x)
                (equal (lookup-addr-mem m 'x) 1)))
    ((3 1) (and (no-pending m 0 'x)
                (equal (lookup-addr-mem m 'x) 1)))
    ((3 2)
     (or (equal (read-reg m 0 'ry) 1)
         (and (no-pending m 0 'x)
              (equal (lookup-addr-mem m 'x) 1)
              (case proc1.phase
                (0 t)
                (1 t)
                (2 (equal proc1.tmp-data 1))
                (otherwise nil)))))
    ((3 3) (or (equal (read-reg m 0 'ry) 1)
               (equal (read-reg m 1 'rx) 1)))
    (& nil)))

  ///

  (defrule step-inv
    (implies (and (machine-p m)
                  (inv m)
                  (natp i)
                  (< i (num-procs m)))
             (inv (step m i)))
    :enable (inv 
             step
             open-<-with-explicit-natp)
    :otf-flg t)

  (defrule flush-sb-inv
    (implies (and (machine-p m)
                  (inv m)
                  (natp j)
                  (< j (num-procs m)))
             (inv (flush-sb m j)))
    :enable (inv open-<-with-explicit-natp)))

(define starting-state-p ((m machine-p))
  :returns (starting-state? booleanp)
  :enabled t
  (b* (((machine m) m)
       ((unless (fence-p m)) nil)
       ((proc proc0) (nth 0 m.procs))
       ((proc proc1) (nth 1 m.procs)))
      (and (equal proc0.pc 0)
           (equal proc0.phase 0)
           (equal proc1.pc 0)
           (equal proc1.phase 0)
           (not-blocked m 0)
           (not-blocked m 1)
           (endp proc0.sb)
           (endp proc1.sb))))

(defrule inv-starting-state
  (implies (starting-state-p m)
           (inv m))
  :enable inv)

(defrule run-inv
  (implies (and (machine-p m)
                (inv m)
                (oracle-p oracle))
           (inv (run m oracle)))
  :enable run)

(defrule inv-halt
  (implies (and (inv m)
                (equal (proc->pc (nth 0 (machine->procs m))) 3)
                (equal (proc->pc (nth 1 (machine->procs m))) 3))
           (or (equal (read-reg m 0 'ry) 1)
               (equal (read-reg m 1 'rx) 1)))
  :enable inv
  :rule-classes nil)

(in-theory (disable starting-state-p
                    inv-starting-state
                    run-inv))

(defrule correct
  (implies (and (machine-p m)
                (starting-state-p m)
                (oracle-p oracle)
                (equal (proc->pc (nth 0 (machine->procs (run m oracle)))) 3)
                (equal (proc->pc (nth 1 (machine->procs (run m oracle)))) 3))
           (or (equal (read-reg (run m oracle) 0 'ry) 1)
               (equal (read-reg (run m oracle) 1 'rx) 1)))
  :use ((:instance inv-starting-state)
        (:instance run-inv)
        (:instance inv-halt (m (run m oracle))))
  :rule-classes nil)
