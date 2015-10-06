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

(defalist ghost-state
  :key-type symbolp
  :true-listp t

  ///
  (defrule put-assoc-ghost-state
    (implies (and (ghost-state-p ghost-state)
                  (symbolp var))
             (ghost-state-p (put-assoc var val ghost-state)))
    :enable put-assoc)
  (defrule assoc-ghost-state
    (implies (and (ghost-state-p ghost-state)
                  (assoc loc ghost-state))
             (and (consp (assoc loc ghost-state))
                  (symbolp (car (assoc loc ghost-state)))))
    :enable assoc)
  (defrule ghost-state-eqlable-alistp
    (implies (ghost-state-p ghost-state)
             (eqlable-alistp ghost-state))))

(define inv ((m machine-p)
             (ghost-state ghost-state-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (fence-p m)) nil)
    ((proc proc0) (nth 0 m.procs))
    ((proc proc1) (nth 1 m.procs))
    ; global invariants: proc0 has no writes to y, proc1 has no writes to x,
    ; and neither are EVER blocked.
    ((unless (no-pending m 0 'y)) nil)
    ((unless (no-pending m 1 'x)) nil)
    ((unless (not-blocked m 0)) nil)
    ((unless (not-blocked m 1)) nil)
    (v0 (cdr (assoc 'v0 ghost-state)))
    (v1 (cdr (assoc 'v1 ghost-state))))
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

(define step-ghost ((m (and (machine-p m)
                            (fence-p m)))
                    (i (and (natp i)
                            (< i (num-procs m))))
                    (ghost-state ghost-state-p))
  :returns (new-ghost ghost-state-p
                      :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc0) (nth 0 m.procs))
       ((proc proc1) (nth 1 m.procs))
       (v0 (cdr (assoc 'v0 ghost-state)))
       (v1 (cdr (assoc 'v1 ghost-state)))
       (new-v0
        (if (= i 0)
            (case proc0.pc
              (0 v0)
              (1 v0)
              (2 (case proc0.phase
                   (0 v0)
                   (1 (not v1))
                   (2 v0)
                   (t v0)))
              (3 v0)
              (t v0))
          v0))
       (new-v1
        (if (= i 1)
            (case proc1.pc
              (0 v1)
              (1 v1)
              (2 (case proc1.phase
                   (0 v1)
                   (1 (not v0))
                   (2 v1)
                   (3 v1)))
              (3 v1)
              (t v1))
          v1)))
      (put-assoc 'v0 new-v0
                 (put-assoc 'v1 new-v1 ghost-state))))

(defrule step-inv
  (implies (and (machine-p m)
                (ghost-state-p ghost-state)
                (inv m ghost-state)
                (natp i)
                (< i (num-procs m)))
           (inv (step m i)
                (step-ghost m i ghost-state)))
  :enable (inv 
           step
           step-ghost
           step-ghost
           open-<-with-explicit-natp))

(defrule step-flush-sb
  (implies (and (machine-p m)
                (ghost-state-p ghost-state)
                (inv m ghost-state)
                (natp i)
                (< i (num-procs m)))
           (inv (flush-sb m i) ghost-state))
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
           (inv m nil))
  :enable inv)

(define run-with-ghost
  ((m (and (machine-p m)
           (fence-p m)))
   (ghost-state ghost-state-p)
   (oracle oracle-p))
  :returns (mv (final-m machine-p :hyp :fguard)
               (final-ghost ghost-state-p :hyp :fguard))
  (if (endp oracle) (mv m ghost-state)
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
                                   (step-ghost m next.proc-num ghost-state)
                                   (cdr oracle))
                 (run-with-ghost m ghost-state (cdr oracle))))
              (:flush
               (if (and (< next.proc-num (num-procs m))
                        (not-blocked m next.proc-num))
                   (run-with-ghost (flush-sb m next.proc-num)
                                   ghost-state
                                   (cdr oracle))
                 (run-with-ghost m ghost-state (cdr oracle))))))))

(defrule run-inv
  (implies (and (machine-p m)
                (fence-p m)
                (ghost-state-p ghost-state)
                (inv m ghost-state)
                (oracle-p oracle))
           (inv (mv-nth 0 (run-with-ghost m ghost-state oracle))
                (mv-nth 1 (run-with-ghost m ghost-state oracle))))
  :enable run-with-ghost)

(defrule inv-halt
  (implies (and (inv m ghost-state)
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
  (let ((m-final (mv-nth 0 (run-with-ghost m nil oracle))))
    (implies (and (machine-p m)
                  (fence-p m)
                  (starting-state-p m)
                  (oracle-p oracle)
                  (equal (proc->pc (nth 0 (machine->procs m-final))) 3)
                  (equal (proc->pc (nth 1 (machine->procs m-final))) 3))
             (or (equal (read-reg m-final 0 'ry) 1)
                 (equal (read-reg m-final 1 'rx) 1))))
  :rule-classes nil
  :use ((:instance inv-starting-state)
        (:instance run-inv (ghost-state nil))
        (:instance inv-halt
                   (m (mv-nth 0 (run-with-ghost m nil oracle)))
                   (ghost-state (mv-nth 1 (run-with-ghost m nil oracle))))))
