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

(define inv ((m machine-p)
             (v0 booleanp)
             (v1 booleanp))
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
   (and
    (case proc0.pc
      (0 (and (not v0)
              (implies v1 (equal (lookup-addr-mem m 'y) 1))))
      (1 (and (equal (lookup-addr m 0 'x) 1)
              (not v0)
              (implies v1 (equal (lookup-addr-mem m 'y) 1))))
      (2 (and (no-pending m 0 'x)
              (equal (lookup-addr-mem m 'x) 1)
              (implies v1 (equal (lookup-addr-mem m 'y) 1))
              (case proc0.phase
                (0 (not v0))
                (1 (not v0))
                (2 (and (or v0 v1)
                        (implies v1 (equal proc0.tmp-data 1)))))))
      (3 (and (no-pending m 0 'x)
              (equal (lookup-addr-mem m 'x) 1)
              (or v0 v1)
              (implies v1 (equal (read-reg m 0 'ry) 1)))))
    (case proc1.pc
      (0 (and (not v1)
              (implies v0 (equal (lookup-addr-mem m 'x) 1))))
      (1 (and (equal (lookup-addr m 1 'y) 1)
              (not v1)
              (implies v0 (equal (lookup-addr-mem m 'x) 1))))
      (2 (and (no-pending m 1 'y)
              (equal (lookup-addr-mem m 'y) 1)
              (implies v0 (equal (lookup-addr-mem m 'x) 1))
              (case proc1.phase
                (0 (not v1))
                (1 (not v1))
                (2 (and (or v0 v1)
                        (implies v0 (equal proc1.tmp-data 1)))))))
      (3 (and (no-pending m 1 'y)
              (equal (lookup-addr-mem m 'y) 1)
              (or v0 v1)
              (implies v0 (equal (read-reg m 1 'rx) 1))))))))

(define step-ghost-v0 ((m (and (machine-p m)
                               (fence-p m)))
                       (i (and (natp i)
                               (< i (num-procs m))))
                       (v0 booleanp)
                       (v1 booleanp))
  :returns (new-v0 booleanp :hyp :fguard)
  (b* (((unless (= i 0)) v0) ; v0 only changes on step 0
       ((machine m) m)
       ((proc proc0) (nth 0 m.procs)))
      (case proc0.pc
        (0 v0)
        (1 v0)
        (2 (case proc0.phase
             (0 v0)
             (1 (not v1))
             (2 v0)))
        (3 v0))))

(define step-ghost-v1 ((m (and (machine-p m)
                               (fence-p m)))
                       (i (and (natp i)
                               (< i (num-procs m))))
                       (v0 booleanp)
                       (v1 booleanp))
  :returns (new-v1 booleanp :hyp :fguard)
  (b* (((unless (= i 1)) v1) ; v1 only changes on step 1
       ((machine m) m)
       ((proc proc1) (nth 1 m.procs)))
      (case proc1.pc
        (0 v1)
        (1 v1)
        (2 (case proc1.phase
             (0 v1)
             (1 (not v0))
             (2 v1)))
        (3 v1))))

(defrule step-inv
  (implies (and (machine-p m)
                (booleanp v0)
                (booleanp v1)
                (inv m v0 v1)
                (natp i)
                (< i (num-procs m)))
           (inv (step m i)
                (step-ghost-v0 m i v0 v1)
                (step-ghost-v1 m i v0 v1)))
  :enable (inv 
           step
           step-ghost-v0
           step-ghost-v1
           open-<-with-explicit-natp))

(defrule step-flush-sb
  (implies (and (machine-p m)
                (booleanp v0)
                (booleanp v1)
                (inv m v0 v1)
                (natp i)
                (< i (num-procs m)))
           (inv (flush-sb m i) v0 v1))
  :enable (inv 
           step
           open-<-with-explicit-natp)
  :otf-flg t)

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
           (inv m nil nil))
  :enable inv)

(define run-with-ghost
  ((m (and (machine-p m)
           (fence-p m)))
   (v0 booleanp)
   (v1 booleanp)
   (oracle oracle-p))
  :returns (mv (final-m machine-p :hyp :fguard)
               (final-v0 booleanp :hyp :fguard)
               (final-v1 booleanp :hyp :fguard))
  (if (endp oracle) (mv m v0 v1)
    (b*
     ((next (car oracle)))
      (o-case next
              ;; We will only use this function if (oracle-p oracle)
              ;; is t. However, this does not guarantee that every
              ;; element in the oracle only steps or flushes a
              ;; processor that actually exists. So, we do a check
              ;; here to make sure that the next oracle instruction in
              ;; fact involves a processor that exists. 
              (:step
               (if (< next.proc-num (num-procs m))
                   (run-with-ghost (step m next.proc-num)
                                   (step-ghost-v0 m next.proc-num v0 v1)
                                   (step-ghost-v1 m next.proc-num v0 v1)
                                   (cdr oracle))
                 (run-with-ghost m v0 v1 (cdr oracle))))
              (:flush
               (if (and (< next.proc-num (num-procs m))
                        (not-blocked m next.proc-num))
                   (run-with-ghost (flush-sb m next.proc-num)
                                   v0
                                   v1
                                   (cdr oracle))
                 (run-with-ghost m v0 v1 (cdr oracle))))))))

(defrule run-inv
  (implies (and (machine-p m)
                (booleanp v0)
                (booleanp v1)
                (inv m v0 v1)
                (oracle-p oracle))
           (inv (mv-nth 0 (run-with-ghost m v0 v1 oracle))
                (mv-nth 1 (run-with-ghost m v0 v1 oracle))
                (mv-nth 2 (run-with-ghost m v0 v1 oracle))))
  :enable run-with-ghost)

(defrule inv-halt
  (implies (and (inv m v0 v1)
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
  (let ((m-final (mv-nth 0 (run-with-ghost m nil nil oracle)))
        (v0-final (mv-nth 1 (run-with-ghost m nil nil oracle)))
        (v1-final (mv-nth 2 (run-with-ghost m nil nil oracle))))
    (implies (and (machine-p m)
                  (starting-state-p m)
                  (oracle-p oracle)
                  (equal (proc->pc (nth 0 (machine->procs m-final))) 3)
                  (equal (proc->pc (nth 1 (machine->procs m-final))) 3))
             (or (equal (read-reg m-final 0 'ry) 1)
                 (equal (read-reg m-final 1 'rx) 1))))
  :rule-classes nil
  :use ((:instance inv-starting-state)
        (:instance run-inv (v0 nil) (v1 nil))
        (:instance inv-halt
                   (m (mv-nth 0 (run-with-ghost m nil nil oracle)))
                   (v0 (mv-nth 1 (run-with-ghost m nil nil oracle)))
                   (v1 (mv-nth 2 (run-with-ghost m nil nil oracle))))))
