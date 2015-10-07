; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(set-ignore-ok t)

(defconst *stupid-0*
  (list (immov 3 'd)))

(define stupid-p ((m machine-p))
  :returns (stupid? booleanp)
  :enabled t
  (and (equal (num-procs m) 1)
       (equal (proc->program (nth 0 (machine->procs m))) *stupid-0*)))

(define starting-state-p ((m machine-p))
  :returns (starting-state? booleanp)
  :enabled t
  (and (stupid-p m)
       (equal (proc->pc (nth 0 (machine->procs m))) 0)
       (equal (proc->phase (nth 0 (machine->procs m))) 0)))

(define inv-old ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (stupid-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 (if (no-pending m 0 'd)
            (equal (lookup-addr-mem m 'd) 3)
          (equal (sb-latest 'd proc.sb)
                 (sb-element 'd 3))))
     (otherwise nil))))

;; Notice how we avoid reasoning directly about the store buffer here by using
;; lookup-addr.
(define inv ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (stupid-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 (equal (lookup-addr m 0 'd) 3))
     (otherwise nil))))

(defrule step-inv
  (implies (and (machine-p m)
                (inv m)
                (natp i)
                (< i (num-procs m)))
           (inv (step m i)))
  :enable (inv step))

(defrule flush-sb-inv
  (implies (and (machine-p m)
                (inv m)
                (natp j)
                (< j (num-procs m)))
           (inv (flush-sb m j)))
  :enable (inv))

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

(defrule inv-pc-1
  (implies (and (machine-p m)
                (inv m)
                (equal (proc->pc (nth 0 (machine->procs m))) 1)
                (no-pending m 0 'd))
           (equal (lookup-addr-mem m 'd) 3))
  :enable inv)

(in-theory (disable starting-state-p
                    inv-starting-state
                    run-inv
                    inv-pc-1))

(defrule stupid-correct
  (implies (and (machine-p m)
                (starting-state-p m)
                (oracle-p oracle)
                (equal (proc->pc (nth 0 (machine->procs (run m oracle)))) 1)
                (no-pending (run m oracle) 0 'd))
           (equal (lookup-addr-mem (run m oracle) 'd) 3))
  :use ((:instance inv-starting-state)
        (:instance run-inv)
        (:instance inv-pc-1 (m (run m oracle)))))
