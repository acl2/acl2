; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(include-book "../../tools")
(include-book "tools/pattern-match" :dir :system)
(set-ignore-ok t)

(defconst *read-write-0*
  (list (mrmov 'x 'rx)
        (immov 1 'y)))

(defconst *read-write-1*
  (list (mrmov 'y 'ry)
        (immov 1 'x)))

(define read-write-p ((m machine-p))
  :returns (fence? booleanp)
  :enabled t
  (and (machine-p m)
       (equal (num-procs m) 2)
       (equal (proc->program (nth 0 (machine->procs m))) *read-write-0*)
       (equal (proc->program (nth 1 (machine->procs m))) *read-write-1*)))

(
