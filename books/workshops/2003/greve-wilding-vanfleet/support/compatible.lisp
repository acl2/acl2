(in-package "ACL2")

;; This file demonstrates that our notion of separation implies the
;; "standard" notion presented to us by Vanfleet and derived from
;; previous work.  These separation notions are: infiltration,
;; exfiltration, and mediation.
;;
;; Matt July 2002

;; Requires:
;; (include-book "separation")

(defthm subsetp-intersection-equal
  (and
   (subsetp (intersection-equal a b) a)
   (subsetp (intersection-equal a b) b)))

(defthm member-selectlist-means
  (implies
   (and
    (equal (selectlist l l1) (selectlist l l2))
    (member x l))
   (iff (equal (select x l1) (select x l2)) t))
  :rule-classes :forward-chaining)

(defthm selectlist-subset
  (implies
   (and
    (equal (selectlist y l1) (selectlist y l2))
    (subsetp x y))
   (iff (equal (selectlist x l1) (selectlist x l2)) t)))

(defthm infiltration
  (implies
   (and
    (equal (current st1) (current st2))
    (equal (selectlist (segs (current st1)) st1)
	   (selectlist (segs (current st2)) st2))
    (member x (segs (current st1))))
   (equal (select x (next st1))
	  (select x (next st2))))
  :hints (("goal" :use (:instance separation (seg x)))))

;; Our initial version of exfiltration was quite strong: the segment
;; in question was unchanged assuming that the current partition had
;; no dia segments.  This version using these functions would be
;; something like:

;(defthm exfiltration
;  (implies
;   (not (intersection-equal (dia y) (segs (current st))))
;   (equal (select y (next st))
;	  (select y st)))
;  :hints (("goal" :use (:instance separation (seg y)))))

;; Unfortunately, this formulation forecloses the possibility of
;; free-running counters, interrupt handlers, etc. that change the
;; state of y in a way not dependant on the current partition.  This
;; kind of behavior ought to be allowed by this formalization, so we
;; weaken it somewhat.

; Matt K., after v4-2:
; Commenting out the following rule, which rewrites a term to itself!
#||
(defthm exfiltration
  (implies
   (and
    (equal (current st1) (current st2))
    (not (intersection-equal (dia y) (segs (current st1)))))
   (equal (select y (next st2))
	  (select y (next st2))))
  :hints (("goal" :use (:instance separation (seg y)))))
||#

(defthm mediation
  (implies
   (and
    (equal (current st1) (current st2))
    (equal (selectlist (segs (current st1)) st1)
	   (selectlist (segs (current st2)) st2))
    (equal (select x st1) (select x st2)))
   (equal (select x (next st1)) (select x (next st2))))
  :hints (("goal" :use (:instance separation (seg x)))))




