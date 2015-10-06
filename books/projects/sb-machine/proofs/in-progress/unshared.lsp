; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../../sb")
(include-book "tools/pattern-match" :dir :system)
(set-ignore-ok t)

(defconst *unshared*
  (list (immov 1 'x)
        (mrmov 'x 'rx)))

;; We don't know how many processors there are, but we know that one of them is
;; the program in question. In our invariant, we will implicitly assume that
;; none of the other processors touch memory location x through the
;; ``no-pending'' predicate (which will apply to all the other processors).
(define unshared-p ((m machine-p)
                    (i (and (natp i)
                            (< i (num-procs m)))))
  :returns (unshared? booleanp)
  :enabled t
  (and (machine-p m)
       (equal (proc->program (nth i (machine->procs m))) *unshared*)))

(define program-doesnt-write-x
  ((program program-p))
  :returns (untouched? booleanp)
  (if (endp program)
      t
    (and
     (b*
      ((inst (car program)))
      (instruction-case
       inst
       (:rmmov (not (equal inst.addr 'x)))
       (:immov (not (equal inst.addr 'x)))
       (& t)))
     (program-doesnt-write-x (cdr program)))))

(define proc-doesnt-write-x
  ((m machine-p)
   (j (and (natp j)
           (< j (num-procs m)))))
  :returns (untouched? booleanp)
  (b* (((machine m) m)
       ((proc proc) (nth j m.procs)))
      (program-doesnt-write-x proc.program))

  ///

  (defrule proc-doesnt-write-x-step
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc-doesnt-write-x (step m j) i)
                    (proc-doesnt-write-x m i)))))

;; No processor other than i ever writes to location 'x.
(define x-is-unshared-recursive
  ((m machine-p)
   (i (and (natp i)
           (< i (num-procs m))))
   (j (and (natp j)
           (< j (num-procs m)))))
  (cond ((zp j) t)
        ((= i j) (x-is-unshared-recursive m i (1- j)))
        (t (and (proc-doesnt-write-x m j)
                (x-is-unshared-recursive m i (1- j)))))

  ///

  (defrule x-is-unshared-recursive-step
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (natp k)
                  (< k (num-procs m)))
             (equal (x-is-unshared-recursive (step m k) i j)
                    (x-is-unshared-recursive m i j)))))

(define x-is-unshared
  ((m machine-p)
   (i (and (natp i)
           (< i (num-procs m)))))
  (x-is-unshared-recursive m i (1- (num-procs m)))

  ///

  (defrule x-is-unshared-step
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (x-is-unshared (step m j) i)
                    (x-is-unshared m i)))))

(defrule x-is-unshared-step
  (implies (and (machine-p m)
                (natp i)
                (< i (num-procs m))
                (natp j)
                (< j (num-procs m)))
           (equal (x-is-unshared (step m j) i)
                  (x-is-unshared m i)))
  :enable (x-is-unshared))

(define inv ((m machine-p)
             (i (and (natp i)
                     (< i (num-procs m)))))
  :verify-guards nil
  (b*
   (((machine m) m)
    ((unless (unshared-p m i)) nil)
    ((proc proc) (nth i m.procs)))
   (case proc.pc
     (0 t)
     (1 
      (case proc.phase
        (0 (equal (lookup-addr m i 'x) 1))
        (1 (and (no-pending m i 'x)
                (equal (lookup-addr-mem m 'x) 1)))
        (2 (equal proc.tmp-data 1))))
     (2 (equal (read-reg m i 'rx) 1)))))

(defrule step-inv
  (implies (and (machine-p m)
                (natp i)
                (< i (num-procs m))
                (natp j)
                (< j (num-procs m))
                (inv m i)
                (x-is-unshared m i))
           (inv (step m j) i))
  :enable (inv step))

(defrule flush-sb-inv
  (implies (and (machine-p m)
                (natp i)
                (< i (num-procs m))
                (natp j)
                (< j (num-procs m))
                (inv m i)
                (x-is-unshared m i))
           (inv (flush-sb m j) i))
  :enable (inv))

