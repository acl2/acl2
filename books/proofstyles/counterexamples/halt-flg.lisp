(in-package "ACL2")

#||

  halt-flg.lisp
  ~~~~~~~~~~~~~

Author: Sandip Ray

The machine here has a halt flag and when the flag is not set it sets
the flag, clears the memory and halts.   We show that the machine
satisfies the spurious correctness criterion.

||#

;; The machine has a halt flag and any other component the programmer
;; cares about.

(defun not-halt-flg (s) (first s))
(defun program-component (s) (second s))
(defun mem (s) (third s))

;; I just define next this way.  Note that it is easy to do variants
;; of this, for example defining (next s) to be just nil.

(defun next (s)
  (if (not-halt-flg s) nil
    s))

;; Here is the definition of halting.

(defun halting (s) (equal (next s) s))

;; Now I introduce Manolios and Moore's notion of correctness.

(include-book "misc/defpun" :dir :system)

(defpun stepw (s)
  (if (halting s) s
    (stepw (next s))))

(defun == (x y)
  (equal (stepw x) (stepw y)))

;; Finally we consider arbitrary pre- and modify conditions.  If the
;; program component of interest is the factorial then the modify
;; function might say that the factorial is in some memory location, I
;; don't care.  The only thing is that this is not the end of the
;; program so the halt-flg is not set by modify yet.

(encapsulate
 (((pre *) => *)
  ((modify *) => *))

 (local (defun pre (s) (equal s  (list 1 2 3))))
 (local (defun modify (s) (declare (ignore s)) (list 4 5 6)))

 (defthm pre-not-halting
   (implies (pre s) (not-halt-flg s)))

 (defthm modify-not-halting
   (not-halt-flg  (modify s))))

;; Now we prove the Manolios and Moore's correctness condition here.

(defthm pre-==-modify
  (implies (pre s)
           (== s (modify s)))
  :hints (("Goal"
           :use ((:instance stepw-def)))))


