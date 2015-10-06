; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(set-ignore-ok t)

(defconst *stupid-0*
  (list (irmov 1 'rd)))

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

(define inv ((m machine-p))
  (b*
   (((machine m) m)
    ((unless (stupid-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 (equal (read-reg m 0 'rd) 1))
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
                (equal (proc->pc (nth 0 (machine->procs m))) 1))
           (equal (read-reg m 0 'rd) 1))
  :enable inv)

;; Theorem I will prove about this program:
;; After the machine has halted, register 'rd contains the value 1.

(in-theory (disable starting-state-p
                    inv-starting-state
                    run-inv
                    inv-pc-1))

(defrule stupid-correct
  (implies (and (machine-p m)
                (starting-state-p m)
                (oracle-p oracle)
                (equal (proc->pc (nth 0 (machine->procs (run m oracle)))) 1))
           (equal (read-reg (run m oracle) 0 'rd) 1))
  :use ((:instance inv-starting-state)
        (:instance run-inv)
        (:instance inv-pc-1 (m (run m oracle)))))
  
