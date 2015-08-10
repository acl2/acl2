(in-package "ACL2")

;; Essay on formalizing "black" data.

;; This file introduces some concepts useful in specifying a firewall.
;; It was not immediately obvious how to formalize the correct
;; operation of a firewall.  What makes it difficult is describing
;; what it means for data not to contain sensitive information.  We
;; introduce the notion of "black", which is a predicate on a segment
;; name and a system state.  The intended interpretation is that black
;; segments do not contain sensitive information that requires
;; protection.

;; Mostly we leave "black" unspecified.  However, we assume that it
;; has the following properties:

;; 1.  If all segments in a system are black, then after the system
;;     progresses one step each segment is black.  (No "spontaneous
;;     generation".)

;; 2.  There exists a function "scrub" that modifies a segment so
;;     that it is black.

;; 3.  Elements of system state that are not associated with the
;;     segment are irrelevant in deciding whether a segment is black.

;; Is this approach to modeling reasonable?  Assume that each byte of
;; the system has associated with it a "black" bit that tells whether
;; the byte is cleared.  Any operation that produces data sets the
;; result's black bit to the "and" of all the input black bits.

;; Axiom one holds, since any operation will set black bits if every
;; segment in the system has its black bits set.  Note that
;; applications are not modeled at this level, but it is worth
;; considering whether this framework could model something like a
;; decryption algorithm.  Note that decryption requires keys or
;; algorithms that would not be considered "black" in this framework,
;; so this axiom would not be inconsistent with such models.

;; Axiom two holds since one can "scrub" a data segment by zeroizing
;; all the data and setting the black bits.  (Of course, not under
;; user control.)

;; Axiom three holds since it is straightforward to tell if a segment
;; is black by checking all its black bits.

(encapsulate
;; BLACK
;; input: segment name, machine state
;; output: boolean indicating whether segment is cleared

 (((black * *) => *)

;; SCRUB
;; input: segment name, machine state
;; output machine state in which segment is cleared and other
;;   segments are untouched

 ((scrub * *) => *)
)

;; A "black" segment contains no sensitive information
(local (defun black (segname st) (declare (ignore segname) (ignore st)) t))

;; A list of segments is all black
(defun blacklist (segnames st)
   (if (consp segnames)
       (and
	(black (car segnames) st)
	(blacklist (cdr segnames) st))
     t))

;; A segment to be "scrubbed"
(local (defun scrub (seg st) (declare (ignore seg)) st))

;; A list of segments to be "scrubbed"
(defun scrublist (segs st)
	 (if (consp segs)
	     (scrublist (cdr segs) (scrub (car segs) st))
	   st))

(defthm scrub-commutative
  (equal
   (scrub seg1 (scrub seg2 st))
   (scrub seg2 (scrub seg1 st))))

(defthm segment-scrub-different
  (implies (not (equal seg1 seg2))
	   (equal (select seg1 (scrub seg2 st))
		  (select seg1 st))))
(defthm black-scrub
  (equal
   (black seg1 (scrub seg2 st))
   (or
    (equal seg1 seg2)
    (black seg1 st))))

(defthm current-scrub
  (equal
   (current (scrub seg st))
   (current st)))

;; If every segment is black, then after one step an arbitrary segment
;; is black
(defthm spontaneous-generation
  (implies
   (blacklist (segslist (allparts)) st)
   (black seg (next st))))

;; Only the contents of a segment determine its blackness
(defthm black-function-of-segment
  (implies
   (equal (select x st1) (select x st2))
   (equal (black x st1) (black x st2)))
  :rule-classes nil)

)



