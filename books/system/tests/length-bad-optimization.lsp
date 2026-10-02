; This file was produced by Claude and passed along by Grant Jurgensen.  It is
; not a book because after an ACL2 fix in mid-September, 2026, the final form
; runs for a very long time.

; A proof of NIL in ACL2 built on SBCL.

; SBCL derives the type of (length x) as (MOD 4611686018427387901) for ANY x,
; since no Common Lisp sequence may be longer than ARRAY-DIMENSION-LIMIT.  So
; it folds (< (length s) (expt 2 62)) to T by type inference alone, without
; looking at s -- and then DELETES the code that built s, because APPEND is
; flushable.  Nothing large is ever allocated.

; DBL must be inline: SBCL will not flush a call to a user-defined function.
; It must also be a function rather than a LET, so that each level mentions
; its argument once; (let ((s (append c c))) ... s ... s ...) nested 62 deep
; beta-reduces into a term of size 2^62.

; Every function below is introduced disabled, and its :e rule is disabled
; immediately, so evaluation is never available by default.  The only :e rule
; of ours ever enabled is (:e foo), in CONTRADICTION at the end -- which is
; precisely where the unsoundness enters.

(in-package "ACL2")

(defund-inline dbl (s)
  (declare (xargs :guard (true-listp s)))
  (append s s))

(in-theory (disable (:e dbl)))

(defthm true-listp-dbl
  (implies (true-listp s)
           (true-listp (dbl s)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable (:d dbl)))))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm len-dbl
  (equal (len (dbl s))
         (* 2 (len s)))
  :hints (("Goal" :in-theory (enable (:d dbl)))))

; The nests below are only 8 deep because of the known exponential blowup in
; guard-conjecture generation over nested calls (at depth 16 the conjecture
; takes a minute to compute, with prove time 0.00).  Two levels of 8 give
; 2^64, which is all we need.
(defund-inline d8 (c)
  (declare (xargs :guard (true-listp c)))
  (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl c)))))))))

(in-theory (disable (:e d8)))

(defthm true-listp-d8
  (implies (true-listp c)
           (true-listp (d8 c)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable (:d d8)))))

(defthm len-d8
  (equal (len (d8 c))
         (* 256 (len c)))
  :hints (("Goal" :in-theory (enable (:d d8)))))

; (len (d8^8 c)) = 256^8 * (len c) = 2^64 * (len c).
(defund foo (c)
  (declare (xargs :guard (true-listp c)))
  (< (length (d8 (d8 (d8 (d8 (d8 (d8 (d8 (d8 c)))))))))
     (expt 2 62)))

(in-theory (disable (:e foo)))

; Logically NIL for every non-empty true list.  Proved symbolically; no :e
; rule of ours is available here.
(defthmd not-foo
  (implies (and (true-listp c)
                (consp c))
           (not (foo c)))
  :hints (("Goal" :in-theory (enable (:d foo)))))

; But (foo '(1)) evaluates to T, via the raw compiled SBCL code.  So the
; instance of NOT-FOO at '(1) rewrites to NIL.
(defthm contradiction
  nil
  :hints (("Goal" :use ((:instance not-foo (c '(1))))
                  :in-theory (enable (:e foo))))
  :rule-classes nil)
