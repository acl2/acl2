; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; A simple program involving a single immediate write (immediate to memory)
;; followed by a fence. The theorem is that after the program has halted, the
;; value of the memory location written to is the value written by the
;; processor (i.e., by the end of execution, the store buffer has been
;; flushed). 

(in-package "SB")

(include-book "../../sb")
(set-ignore-ok t)

(defconst *fence-0*
  (list (immov 1 'x)
        (fence)))

(define fence-p ((m machine-p))
  :returns (fence? booleanp)
  :enabled t
  (and (equal (num-procs m) 1)
       (equal (proc->program (nth 0 (machine->procs m))) *fence-0*)))

(define starting-state-p ((m machine-p))
  :returns (starting-state? booleanp)
  :enabled t
  (and (fence-p m)
       (equal (proc->pc (nth 0 (machine->procs m))) 0)
       (equal (proc->phase (nth 0 (machine->procs m))) 0)))

(define inv ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (fence-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 (equal (lookup-addr m 0 'x) 1))
     (2 (and (no-pending m 0 'x)
             (equal (lookup-addr-mem m 'x) 1)))
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
  (implies (and (inv m)
                (equal (proc->pc (nth 0 (machine->procs m))) 2))
           (equal (lookup-addr-mem m 'x) 1))
  :enable inv)


(in-theory (disable starting-state-p
                    inv-starting-state
                    run-inv
                    inv-pc-1))

(defrule fence-correct
  (implies (and (machine-p m)
                (starting-state-p m)
                (oracle-p oracle)
                (equal (proc->pc (nth 0 (machine->procs (run m oracle)))) 2))
           (equal (lookup-addr-mem (run m oracle) 'x) 1))
  :use ((:instance inv-starting-state)
        (:instance run-inv)
        (:instance inv-pc-1 (m (run m oracle)))))
