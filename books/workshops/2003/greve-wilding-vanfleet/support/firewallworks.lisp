(in-package "ACL2")

;; (include-book "firewallspec")

;; Firewall works

;; We formalize a particular firewall system and use the separation
;; axiom to show that it works.  We use the notion of "black" data to
;; describe what is and what is not cleared.

;; We introduce the firewall system using three axioms.

;; Note about the axioms consistency
;; ---------------------------------
;; We would like to show that the axioms we've added here are
;; consistent with the axioms added using encapsulate.  Although doing
;; this does not guarantee that we've axiomitized things properly,
;; since it's a check on our axioms we'd like to do it.
;; Unfortunately, there seems to be no way to accomplish this
;; conveniently using ACL2 2.6.

;; So, we do it manually, using code written to work with a Makefile.
;; The makefile is arranged so that if these axioms are inconsistent
;; with the axioms added previously, then an error occurs.  We use the
;; witnesses introduced by the encapsulate, which is not the most
;; robust way to do this since it requires foresight when introducing
;; the encapsulates and may limit their use.  (Better to have a
;; mechanism that allows a new witness to be introduced when the
;; consistency check is being accomplished.)

;; We would of course prefer ACL2 to support doing this, and we have
;; suggested this to the ACL2 authors and others.

;; b, and f are partitions.  Their names are meant to suggest "black"
;; and "firewall".
(defaxiom allparts-includes
  (and
   (member 'b (allparts))
   (member 'f (allparts))))

;; When the system is executing partition f, the contents of memory
;; segment "outbox" does not unblacken
(defaxiom firewall-blackens
  (implies
   (and
    (equal (current st) 'f)
    (black 'outbox st))
   (black 'outbox (next st))))

;; If there is a segment in partition B that is writable from a
;; segment in a non-B partition, then it is called "outbox" and it is
;; only writable from segments that are in partition F and not in
;; partition B.
(defaxiom dia-setup
  (implies
   (and
    (member seg1 (dia seg2))
    (member seg2 (segs 'b))
    (member seg1 (segs p))
    (not (equal p 'b)))
   (and
    (equal seg2 'outbox)
    (equal p 'f)
    (not (member seg1 (segs 'b)))))
  :rule-classes nil)

;; Some of the recursive functions we have introduced were added in
;; the scope of an encapsulate.  ACL2 will not allow us to use their
;; recursive structure in inductive proofs, because we might have done
;; something fishy.  We now provide ACL2 some recursive functions to
;; guide its choice of induction schemes on a few of these functions.

(defun scrublist-induct (segs st)
   (if (consp segs)
       (scrublist-induct (cdr segs) (scrub (car segs) st))
     st))

(defthm scrublist-induction-scheme
  t
  :rule-classes ((:induction :pattern (scrublist segs st)
			     :scheme (scrublist-induct segs st))))

(defthm blacklist-induction-scheme
  t
  :rule-classes ((:induction :pattern (blacklist segs st)
			     :scheme (len segs))))

(defun run-induct (st n)
  (if (zp n) st (run-induct (next st) (1- n))))

(defthm run-induction-scheme
  t
  :rule-classes ((:induction :pattern (run st n)
			     :scheme (run-induct st n))))

;; We introduce some underlying useful theorems about our functions

(defthm remains-black-after-scrublist
  (implies
   (black seg st)
   (black seg (scrublist segs st))))

(defthm black-scrublist
  (iff
   (black x (scrublist list st))
   (or
    (member x list)
    (black x st))))

(defthm scrublist-scrub
  (equal
   (scrublist list (scrub x st))
   (scrub x (scrublist list st))))

(defthm blacklist-scrub
  (implies
   (blacklist x list)
   (blacklist x (scrub y list))))

;; Scrubbing the non-black elements yields a system state with all
;; black elements
(defthm scrub-nonblack-means-black
  (implies
   (blacklist y st)
   (blacklist x (scrublist (set-difference-equal x y) st))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm member-equal-is-member
;   (equal (member-equal a l) (member a l)))

(defthm intersection-equal-dia-b-segs-f-helper
  (implies
   (and
    (member x (segs 'b))
    (not (equal x 'outbox))
    (subsetp z (dia x)))
   (equal (intersection-equal z (segs 'f)) nil))
  :hints
  (("Subgoal *1/3'4'" :use (:instance dia-setup (seg1 z1) (seg2 x) (p 'f))))
  :rule-classes nil)

(defthm subsetp-append
  (subsetp x (append a x)))

(defthm subsetp-x-x
  (subsetp x x)
  :hints (("goal" :use (:instance subsetp-append (a nil))
	   :in-theory (disable subsetp-append))))

(defthm intersection-equal-dia-b-segs-f
  (implies
   (and
    (member x (segs 'b))
    (not (equal x 'outbox)))
   (equal (intersection-equal (dia x) (segs 'f)) nil))
  :hints (("goal" :use (:instance intersection-equal-dia-b-segs-f-helper
				  (z (dia x))))))

(defthm select-scrublist
  (implies
   (not (member a l))
   (equal (select a (scrublist l st))
	  (select a st))))

(defthm current-scrublist
  (equal
   (current (scrublist segs st))
   (current st)))

(defthm selectlist-scrublist
  (implies
   (equal (intersection-equal x y) nil)
   (equal
    (selectlist x (scrublist y st))
    (selectlist x st))))

(defthm member-set-difference-equal
  (iff
   (member e (set-difference-equal l1 l2))
   (and
    (member e l1)
    (not (member e l2)))))

(defthm intersection-equal-set-difference
  (equal
   (intersection-equal
    (intersection-equal a b)
    (set-difference-equal c b))
   nil))

;; We will prove that the firewall works by casesplitting on which
;; partition is the current partition.  For each of the cases we use
;; the separation axiom to posit a state that is "equivalent" to the
;; actual state with respect to an arbitrary memory segment of b.  The
;; following rule helps that proof along by using a free variable
;; match of the equivalent state.

(defthm black-from-equivalent-allblack
  (implies
   (and
    (equal (select seg (next st)) (select seg (next st2)))
    (blacklist (segslist (allparts)) st2))
   (black seg (next st)))
  :hints (("goal" :use (:instance black-function-of-segment
				  (st1 (next st))
				  (st2 (next st2))
				  (x seg)))))

;; Now, each of the cases.  The current partition is either b, f, or
;; some other partition, and we prove a lemma about each case

;(defthm firewall-step-kernel
; (implies (and (subsetp segs (segs 'b))
;               (blacklist segs st)
;               (equal (current st) (kernel-name)))
;          (blacklist segs (next st)))
; :hints (("Subgoal *1/3'" :use
;	  (:instance separation (seg (car segs))
;		     (st1 st)
;		     (st2 (scrublist (set-difference-equal
;				      (segslist (allparts))
;				      segs)
;				     st))))))

(defthm firewall-step-firewall-helper
 (implies (and (subsetp segs (segs 'b))
               (blacklist segs st)
               (equal (current st) 'f))
          (blacklist segs (next st)))
 :hints (("Subgoal *1/3'" :cases ((equal (car segs) 'outbox)))
	 ("Subgoal *1/3.2" :use
	  (:instance separation (seg (car segs))
		     (st1 st)
		     (st2 (scrublist (set-difference-equal
				      (segslist (allparts))
				      segs)
				     st))))))

(defthm firewall-step-firewall
 (implies (and (blacklist (segs 'b) st)
               (equal (current st) 'f))
          (blacklist (segs 'b) (next st)))
 :hints (("goal" :use (:instance firewall-step-firewall-helper
				 (segs (segs 'b))))))


(defthm firewall-step-black-helper
 (implies (and (blacklist (segs 'b) st)
               (equal (current st) 'b)
               (subsetp segs (segs 'b)))
          (blacklist segs (next st)))
 :hints (("Subgoal *1/2'" :use
	  (:instance separation (seg (car segs))
		     (st1 st)
		     (st2 (scrublist (set-difference-equal
				      (segslist (allparts))
				      (segs 'b))
				     st))))))

(defthm firewall-step-black
 (implies (and (blacklist (segs 'b) st)
               (equal (current st) 'b))
          (blacklist (segs 'b) (next st)))
 :hints (("goal" :use (:instance firewall-step-black-helper
				 (segs (segs 'b))))))

(defthm intersection-equal-segs-b-segs-other-helper
  (implies
   (and
    (not (equal other 'b))
    (not (equal other 'f))
;    (not (equal other (kernel-name)))
    (member x (segs 'b))
    (member other (allparts))
    (subsetp z (dia x)))
   (equal (intersection-equal z (segs other)) nil))
  :hints (("Subgoal *1/3''"
	   :use (:instance dia-setup (seg2 x) (seg1 (car z))
			   (p other)
			   ;; (p2 other)  obsolete
			   )))
  :rule-classes nil)

(defthm intersection-equal-segs-b-segs-other
  (implies
   (and
    (not (equal other 'b))
    (not (equal other 'f))
;    (not (equal other (kernel-name)))
    (member x (segs 'b))
    (member other (allparts)))
   (equal (intersection-equal (dia x) (segs other)) nil))
  :hints (("goal" :use
	   (:instance intersection-equal-segs-b-segs-other-helper
		      (z (dia x))))))

(defthm firewall-step-other-helper
 (implies (and (blacklist (segs 'b) st)
;               (not (equal (current st) (kernel-name)))
               (not (equal (current st) 'f))
               (not (equal (current st) 'b))
               (member (current st) (allparts))
               (subsetp segs (segs 'b)))
          (blacklist segs (next st)))
 :hints (("Subgoal *1/2'" :use
	  (:instance separation (seg (car segs))
		     (st1 st)
		     (st2 (scrublist (set-difference-equal
				      (segslist (allparts))
				      (segs 'b))
				     st))))))
(defthm firewall-step-other
 (implies (and (blacklist (segs 'b) st)
;               (not (equal (current st) (kernel-name)))
               (not (equal (current st) 'f))
               (not (equal (current st) 'b))
               (member (current st) (allparts)))
          (blacklist (segs 'b) (next st)))
 :hints (("goal" :use (:instance firewall-step-other-helper
				 (segs (segs 'b))))))


;; We combine the sublemmas about a single step into a single lemma
;; about a single step
(defthm firewall-step
  (implies
   (blacklist (segs 'b) st)
   (blacklist (segs 'b) (next st)))
  :hints (("goal" :use ( ;firewall-step-kernel
			firewall-step-black
			firewall-step-firewall
			firewall-step-other))))

;;
;; The firewall system works: Data in partition b is always black
;;
(defthm firewall-works
  (implies
   (blacklist (segs 'b) st)
   (blacklist (segs 'b) (run st n))))
