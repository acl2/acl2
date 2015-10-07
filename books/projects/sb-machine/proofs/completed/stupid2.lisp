; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(set-ignore-ok t)

(defconst *stupid-0*
  (list (irmov 1 'rd)
        (rmmov 'rd 'd)))

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

;; We decline to verify the guards for the invariant because they do not
;; matter. We're using read-mem, read-reg, etc. as functions that inspect the
;; contents of the registers and memory rather than operations that are meant
;; to be part of the process of executing an instruction.
(define inv ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (stupid-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 
      (case proc.phase
        (0 (equal (read-reg m 0 'rd) 1))
        (1 (equal proc.tmp-data 1))))
     (2
      (if (no-pending m 0 'd)
          (equal (lookup-addr-mem m 'd) 1)
        (equal (sb-latest 'd proc.sb)
               (sb-element 'd 1))))
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
                (equal (proc->pc (nth 0 (machine->procs m))) 2)
                (no-pending m 0 'd))
           (equal (lookup-addr-mem m 'd) 1))
  :enable inv)

;; This invariant won't work!
;; We have to specify which case corresponds to which phase, because if we
;; assume the wrong one holds (like proc.tmp-data = 1 when phase = 0) then when
;; we step the machine, we don't know what's in the 'rd register and therefore
;; the invariant actually isn't an invariant.
;;
;; However, we ought to be able to generalize away the state of the store
;; buffer, because that's not affected by the pc or phase.
(define inv-wrong ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (stupid-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 t)
     (1 
      (or (equal (read-reg m 0 'rd) 1) ; phase 0
          (equal proc.tmp-data 1)))    ; phase 1
     (2
      (if (no-pending m 0 'd)
          (equal (lookup-addr-mem m 'd) 1)
        (equal (sb-latest 'd proc.sb)
               (sb-element 'd 1))))
     (otherwise nil))))

;; Theorem I will prove about this program:
;; After the machine has halted, and the store buffer is flushed, memory
;; location d has the value 1.

(in-theory (disable starting-state-p
                    inv-starting-state
                    run-inv
                    inv-pc-1))

(defrule stupid-correct
  (implies (and (machine-p m)
                (starting-state-p m)
                (oracle-p oracle)
                (equal (proc->pc (nth 0 (machine->procs (run m oracle)))) 2)
                (no-pending (run m oracle) 0 'd))
           (equal (lookup-addr-mem (run m oracle) 'd) 1))
  :use ((:instance inv-starting-state)
        (:instance run-inv)
        (:instance inv-pc-1 (m (run m oracle)))))
