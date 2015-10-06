; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(include-book "../../tools")
(include-book "tools/pattern-match" :dir :system)
(set-ignore-ok t)

(defconst *producer-0*
  (list (immov 1 'd)
        (immov 1 'f)))

(define producer-p ((m machine-p))
  :returns (producer? booleanp)
  :enabled t
  (and (machine-p m)
       (equal (num-procs m) 1)
       (equal (proc->program (nth 0 (machine->procs m))) *producer-0*)))

(define inv
  ((m machine-p))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (producer-p m)) nil)
    ((proc proc) (nth 0 m.procs)))
   (case proc.pc
     (0 (and (equal (lookup-addr-mem m 'd) 0)
             (equal (lookup-addr-mem m 'f) 0)
             (store-buffer-plus-memory m 0 nil)))
     (1 (and (equal (lookup-addr-mem m 'f) 0)
             (store-buffer-plus-memory m 0 (list (sb-element 'd 1)))))
     (2 (store-buffer-plus-memory m 0 (list (sb-element 'f 1)
                                            (sb-element 'd 1)))))))

;; Question for Matt:
;; How can I make a version of the rule write-sb-store-buffer-plus-memory-2
;; that will apply to Subgoal 1' of the following conjecture? I want to rewrite
;; the store-buffer-plus-memory call in the conclusion according to that rule,
;; but there is a quoted list instead of a call to cons, which is preventing
;; the rule from firing (I think).
(defrule step-inv
  (implies (and (machine-p m)
                (inv m)
                (natp i)
                (< i (num-procs m)))
           (inv (step m i)))
  :enable (inv
           step))

(defrule flush-sb-inv
  (implies (and (machine-p m)
                (inv m)
                (natp j)
                (< j (num-procs m)))
           (inv (flush-sb m j)))
  :enable (inv)
  :otf-flg t)
