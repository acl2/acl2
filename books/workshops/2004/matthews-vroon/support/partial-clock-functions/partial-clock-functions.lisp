#|==================================================================|#

#|
  A template for using inductive assertions to prove
  that a program eventually reaches an exit state.
  Using this proof an efficient simulator can be
  written that doesn't require step-counter parameters.

  However, ACL2 2.8 cannot execute these simulators
  as they are written, because some of the guards
  associated with function calls internal to the
  simulators are not executable. Nevertheless, ACL2
  is able to prove that the guards hold for all
  arguments the internal functions will be called on.

  Thus this restriction will hopefully be relaxed
  in future versions of ACL2.
|#

;(in-package "partial-clock-functions")
(in-package "ACL2")
(include-book "../tiny-fib-example/defstobj+")

#|================ Generic arithmetic lemmas and books ===================|#

(encapsulate
 ()

; (Matt K., 10/2013: Changed rel8 to rel9.)
 (local (include-book "rtl/rel9/arithmetic/top" :dir :system))
 (local (in-theory (enable mod-sum-cases mod-force-chosen-a-neg)))

 (defthm mod-zero-subtract-remainder
   (implies (and (equal (mod m k) 0)
		 (natp m)
		 (posp k)
		 (integerp c)
		 (< c 0)
		 (<= (- k) c))
	    (equal (mod (+ c m) k)
		   (+ k c))))

 (defthm mod-zero-subtract-modulus-natp
   (implies (and (equal (mod m k) 0)
		 (posp m)
		 (posp k)
		 (equal c (- k)))
	    (natp (+ c m))))

 (defthm mod-zero-simplify-less
   (implies (and (equal (mod n k) 0)
		 (integerp n)
		 (posp k)
		 (< n k))
	    (<= n 0))
   :rule-classes :forward-chaining))

(include-book "arithmetic/top-with-meta" :dir :system)


#|========================== MSTATE theory =========================|#

;;A very simple machine model with a next-state function,
;; called NEXT. The machine model itself is called MSTATE,
;; after the name of the stobj it is using.

;A machine-state. For this example the state
; only contains a program counter.
(defstobj+ mstate
  (progc :type integer :initially 0))

(defthm mstatep-type
  (implies (mstatep mstate)
           (consp mstate))
  :rule-classes :compound-recognizer)

(defthm mstatep-cons
  (iff (mstatep (cons pc rest))
       (and (integerp pc)
            (equal rest nil))))

(defthm progc-integerp
  (implies (mstatep mstate)
           (integerp (progc mstate)))
  :rule-classes :type-prescription)

(defthm true-listp-len-zero
  (implies (and (true-listp xs)
                (equal (len xs) 0))
           (not xs))
  :rule-classes :forward-chaining)

(defthm make-mstate
  (implies (mstatep mstate)
           (equal (list (progc mstate))
                  mstate)))

(defthm update-progc-type
  (implies (and (mstatep mstate)
                (integerp pc))
           (mstatep (update-progc pc mstate)))
  :rule-classes (:type-prescription :rewrite))

(defthm update-progc-list
  (implies (integerp pc)
           (equal (update-progc pc (list pc))
                  (list pc))))

(defthm update-progc-mstatep
  (implies (mstatep mstate)
           (equal (update-progc (progc mstate) mstate)
                  mstate)))

(defthm progc-update-progc
  (equal (progc (update-progc pc mstate))
         pc))

(defthm update-progc-twice
  (equal (update-progc pc2
                       (update-progc pc1 mstate))
         (update-progc pc2 mstate)))

(in-theory (disable progc update-progc mstatep))

;A next-state function that simulates one step of a machine.
; For this example we just decrement the program counter.
(defund next (mstate)
  (declare (xargs :stobjs (mstate)))
  (update-progc (1- (progc mstate)) mstate))

;;A common form of induction used for
;; reasoning about runs of the machine.
(defun run-induction (n mstate)
  (declare (xargs :stobjs (mstate)))
  (cond
   ((not (posp n)) mstate)
   (t (let ((mstate (next mstate)))
        (run-induction (1- n) mstate)))))

(defthm negative-progc-implies-next-negative-progc
  (implies (< (progc mstate) 0)
           (< (progc (next mstate)) 0))
  :hints (("Goal" :in-theory (enable next)))
  :rule-classes (:forward-chaining))

;; For this example we arbitrarily choose
;; a cutpoint state to be any valid mstate where
;; the program counter is nonnegative and evenly
;; divisible by 10.
(defund at-cutpoint (mstate)
  (declare (xargs :stobjs (mstate)))
  (and (mstatep mstate)
       (natp (progc mstate))
       (equal (mod (progc mstate) 10)
              0)))

(in-theory (disable mod))

(defthm prove-nil-not-cutpoint
  (not (at-cutpoint nil))
  :hints (("Goal" :in-theory (enable at-cutpoint))))

;;NEXT preserves the structure of MSTATEs.
(defthm next-mstatep
  (implies (mstatep mstate)
	   (mstatep (next mstate)))
  :hints (("Goal" :in-theory (enable next))))

#|====== Partial clock functions and symbolic simulation ======|#

(include-book "misc/defpun" :dir :system)
(include-book "ordinals/ordinals" :dir :system)

(defthm nil-not-cutpoint
  (not (at-cutpoint nil)))

;A simulator that runs for N steps.
; N is a step-counter parameter.
(defun run (n mstate)
  (declare (xargs :stobjs (mstate)
                  :guard (natp n)))
  (if (zp n)
      mstate
    (let ((mstate (next mstate)))
      (run (1- n) mstate))))

;A tail-recursive partial function that returns the
; number of steps until mstate reaches a cutpoint state,
; if in fact mstate can eventually reach a cutpoint state.
; The parameter N is an accumulator, which clients
; should initially set to zero.
(defpun steps-to-cutpoint-tail (n mstate)
  (if (at-cutpoint mstate)
      n
    (steps-to-cutpoint-tail (1+ n) (run 1 mstate))))

;The number of steps until mstate reaches the next
; cutpoint state, if there is one. If there isn't,
; then this function returns zero.
(defun-nx steps-to-cutpoint (mstate)
  (let ((steps (steps-to-cutpoint-tail 0 mstate)))
    (if (at-cutpoint (run steps mstate))
	steps
      (omega))))

;Simulate mstate until it reaches a cutpoint state,
; assuming it does.
(defun-nx run-to-cutpoint (mstate)
  (run (steps-to-cutpoint mstate) mstate))

#|
;;This version of RUN-TO-CUTPOINT looks nicer, but
;; then (AT-CUTPOINT (RUN-TO-CUTPOINT MSTATE)) does
;; not imply that MSTATE eventually reaches a cutpoint
;; state. The problem is that if MSTATE never reaches
;; a cutpoint state then (RUN-TO-CUTPOINT MSTATE) can return anything,
;; including a cutpoint state.
(defpun run-to-cutpoint (mstate)
  (if (at-cutpoint mstate)
      mstate
    (run-to-cutpoint (next mstate))))
|#

(defthm steps-to-cutpoint-tail-at-cutpoint
  (implies (at-cutpoint mstate)
           (equal (steps-to-cutpoint-tail n mstate)
                  n)))

(defthm steps-to-cutpoint-tail-not-cutpoint
  (implies (and (integerp n)
                (not (at-cutpoint mstate)))
           (equal (steps-to-cutpoint-tail n (run 1 mstate))
                  (steps-to-cutpoint-tail (- n 1) mstate))))

(in-theory (disable steps-to-cutpoint-tail-def))

(defthm run-zero
  (implies (zp n)
           (equal (run n mstate)
                  mstate)))

(defthm run-1
  (equal (next mstate)
	 (run 1 mstate)))

(defthm run-plus
  (let ((steps (cond
		((zp m)
		 n)
		((zp n)
		 m)
		(t
		 (+ m n)))))
    (equal (run m (run n mstate))
	   (run steps mstate))))

(in-theory (disable run))

(defun-nx steps-to-cutpoint-induction (k mstate steps)
  (declare (xargs :verify-guards nil
                  :guard (and (equal mstate mstate)
                              (equal steps steps))))
  (or (zp k)
      (steps-to-cutpoint-induction (1- k) (next mstate) (1+ steps))))

(defthmd steps-to-cutpoint-tail-inv
  (implies (and (at-cutpoint (run k mstate))
                (integerp steps))
           (let* ((result     (steps-to-cutpoint-tail steps mstate))
                  (cutpoint-steps (- result steps)))
             (and (integerp result)
                  (natp cutpoint-steps)
                  (implies (natp k)
                           (<= cutpoint-steps k))
                  (at-cutpoint (run cutpoint-steps mstate)))))
  :hints (("Goal" :induct (steps-to-cutpoint-induction k mstate steps)
                  :do-not-induct t)
          ("Subgoal *1/2" :cases ((at-cutpoint mstate)))))

(defthm steps-to-cutpoint-tail-at-cutpoint-simp
  (implies (at-cutpoint (run k mstate))
           (at-cutpoint (run (steps-to-cutpoint-tail 0 mstate)
                        mstate)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv
				  (steps 0))))
  :rule-classes (:forward-chaining :rewrite))

(defthm steps-to-cutpoint-at-cutpoint
  (implies (at-cutpoint (run k mstate))
           (at-cutpoint (run (steps-to-cutpoint mstate)
                        mstate)))
  :rule-classes (:rewrite :forward-chaining))

(defthm steps-to-cutpoint-tail-diff
  (implies (and (at-cutpoint (run k mstate))
                (syntaxp (not (equal n ''0)))
                (integerp n))
           (equal (steps-to-cutpoint-tail n mstate)
                  (+ n (steps-to-cutpoint-tail 0 mstate))))
  :hints (("Goal" :use ((:instance steps-to-cutpoint-tail-inv
                                   (k (- (steps-to-cutpoint-tail n mstate)
                                         n))
                                   (steps 0))
                        (:instance steps-to-cutpoint-tail-inv
                                   (k (steps-to-cutpoint mstate))
                                   (steps n))
                        (:instance steps-to-cutpoint-tail-inv
                                   (steps 0))))))

(defthm not-at-cutpoint-implies-steps-to-cutpoint-tail-nonzero
  (implies (and (at-cutpoint (run (steps-to-cutpoint-tail 0 mstate)
				  mstate))
		(not (at-cutpoint mstate)))
	   (posp (steps-to-cutpoint-tail 0 mstate)))
  :rule-classes (:rewrite))

(defthm not-at-cutpoint-implies-steps-to-cutpoint-tail-nonzero-fwd-chain
  (implies (and (at-cutpoint (run k mstate))
		(not (at-cutpoint mstate)))
	   (posp (steps-to-cutpoint-tail 0 mstate)))
  :rule-classes (:forward-chaining))

(defthm natp-steps-to-cutpoint-tail
  (implies (at-cutpoint (run (steps-to-cutpoint-tail 0 mstate) mstate))
	   (natp (steps-to-cutpoint-tail 0 mstate)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv)))
  :rule-classes (:rewrite :forward-chaining))

(defthm natp-steps-to-cutpoint
  (iff (at-cutpoint (run (steps-to-cutpoint mstate) mstate))
       (natp (steps-to-cutpoint mstate)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv)))
  :rule-classes (:rewrite))

(defthm steps-to-cutpoint-equals-omega-simp
  (iff (equal (steps-to-cutpoint mstate)
	      (omega))
       (not (natp (steps-to-cutpoint mstate)))))

(defthm o-p-steps-to-cutpoint
  (o-p (steps-to-cutpoint mstate))
  :hints (("Goal" :cases ((natp (steps-to-cutpoint mstate))))))

(defthm steps-to-cutpoint-zero
  (implies (at-cutpoint mstate)
	   (equal (steps-to-cutpoint mstate) 0)))

(defthm integerp-add
  (iff (integerp (+ -1 n))
       (or (integerp n)
	   (not (acl2-numberp n)))))

(defthmd steps-to-cutpoint-nonzero-intro
  (implies (not (at-cutpoint mstate))
	   (equal (steps-to-cutpoint mstate)
		  (o+ 1 (steps-to-cutpoint (next mstate)))))
  :hints (("Subgoal 1'" :cases ((equal (steps-to-cutpoint-tail 0 mstate)
				       0)))))

(defthm integerp-ord-decrement
  (implies (natp n)
	   (equal (o- n 1)
		  (max 0 (- n 1))))
  :hints (("Goal" :in-theory (enable o-))))

(defthm natp-steps-to-cutpoint-increment
  (iff (natp (o+ 1 (steps-to-cutpoint mstate)))
       (natp (steps-to-cutpoint mstate)))
  :hints (("Goal" :in-theory (enable o+))))

(defthm natp-steps-to-cutpoint-decrement
  (iff (natp (o- (steps-to-cutpoint mstate) 1))
       (natp (steps-to-cutpoint mstate)))
  :hints (("Goal" :in-theory (enable o-))))

(defthm omega-minus-one-equals-omega
  (equal (o- (omega) 1)
	  (omega))
  :hints (("Goal" :in-theory (enable o-))))

(defthmd natp-ord-decrement
  (iff (natp (o- n 1))
       (or (and (o-finp n)
		(or (<= n 1)
		    (posp n)))
	   (< (o-first-expt n) 0)))
  :hints (("Goal" :in-theory (enable o- o< o-finp))))

(defthm o-finp-steps-to-cutpoint-iff-natp
  (iff (o-finp (steps-to-cutpoint mstate))
       (natp (steps-to-cutpoint mstate))))

(defthmd convert-at-cutpoint-to-steps-to-cutpoint
  (iff (at-cutpoint mstate)
       (equal (steps-to-cutpoint mstate)
	      0)))

(defthm at-cutpoint-implies-steps-to-cutpoint-zero
  (implies (at-cutpoint mstate)
	   (equal (steps-to-cutpoint mstate)
		  0))
  :rule-classes :forward-chaining)

(defthm not-at-cutpoint-implies-steps-to-cutpoint-nonzero
  (implies (not (at-cutpoint mstate))
	   (not (equal (steps-to-cutpoint mstate)
		       0)))
  :rule-classes :forward-chaining)

(defthmd steps-to-cutpoint-nonzero-elim
  (implies (not (at-cutpoint mstate))
	   (equal (steps-to-cutpoint (next mstate))
		  (o- (steps-to-cutpoint mstate) 1)))
  :hints (("Goal" :in-theory (enable steps-to-cutpoint-nonzero-intro))))

(defthm natp-steps-to-cutpoint-run
  (implies (natp (steps-to-cutpoint (run k mstate)))
	   (natp (steps-to-cutpoint mstate))))

(in-theory (disable steps-to-cutpoint))

(defthm steps-to-cutpoint-run-1-elim
  (implies (not (at-cutpoint mstate))
	   (equal (steps-to-cutpoint (run 1 mstate))
		  (o- (steps-to-cutpoint mstate) 1)))
  :hints (("Goal" :in-theory (e/d (steps-to-cutpoint-nonzero-elim run)
				  (run-1)))))

;Simulate MSTATE until it reaches the next
; cutpoint state, if there is one. If there isn't,
; then return NIL.
; This function allows simpler rewrite rules
; than RUN-TO-CUTPOINT does.

(defun-nx next-cutpoint (mstate)
  (let ((steps (steps-to-cutpoint mstate)))
    (if (natp steps)
	(run steps mstate)
      nil)))

;;A derived induction scheme, useful for reasoning
;; about NEXT-CUTPOINT
(defun-nx next-cutpoint-induction (k mstate)
  (cond
   ((at-cutpoint mstate)
    t)
   ((zp k)
    t)
   (t
    (next-cutpoint-induction (+ -1 k) (next mstate)))))

(defthm next-cutpoint-at-cutpoint
  (implies (at-cutpoint mstate)
           (equal (next-cutpoint mstate)
                  mstate)))

(defthmd next-cutpoint-elim-next
  (implies (not (at-cutpoint mstate))
           (equal (next-cutpoint (next mstate))
                  (next-cutpoint mstate))))

(defthm next-cutpoint-intro-next
  (implies (not (at-cutpoint mstate))
           (equal (next-cutpoint mstate)
                  (next-cutpoint (next mstate)))))

(defthm next-cutpoint-reaches-cutpoint
  (iff (at-cutpoint (next-cutpoint mstate))
       (natp (steps-to-cutpoint mstate))))

(in-theory (e/d (steps-to-cutpoint-nonzero-intro) (next-cutpoint)))

(defun-nx cutpoint-to-cutpoint (mstate)
  (next-cutpoint (next mstate)))

(defthm cutpoint-to-cutpoint-returns-cutpoint-state
  (implies (natp (steps-to-cutpoint (next mstate)))
           (at-cutpoint (cutpoint-to-cutpoint mstate))))

(defthmd convert-cutpoint-to-cutpoint-to-run
  (let ((steps (steps-to-cutpoint (next mstate))))
    (implies (natp steps)
	     (equal (cutpoint-to-cutpoint mstate)
		    (run (+ 1 steps) mstate))))
  :hints (("Goal" :in-theory (enable next-cutpoint))))

(in-theory (disable cutpoint-to-cutpoint run-1))

(defthm run-cutpoint-to-cutpoint
  (let ((steps (steps-to-cutpoint (next mstate))))
    (implies (and (natp steps)
		  (natp k))
	     (equal (run k (cutpoint-to-cutpoint mstate))
		    (run (+ 1 k steps) mstate))))
  :hints (("Goal" :in-theory (enable convert-cutpoint-to-cutpoint-to-run))))


#|================== Program exit points  =================|#

;;For this example we arbitrarily define the program to
;; have exited when the program counter has reached zero.
(defund at-exitpoint (mstate)
  (declare (xargs :stobjs (mstate)))
  (and (mstatep mstate)
       (equal (progc mstate)
              0)))

(defthm not-at-exitpoint-implies-not-progc-zero
  (implies (and (mstatep mstate)
                (not (at-exitpoint mstate))
                (natp (progc mstate)))
           (posp (progc mstate)))
  :hints (("Goal" :in-theory (enable at-exitpoint))))

(defthm at-exitpoint-implies-at-cutpoint
  (implies (at-exitpoint mstate)
           (at-cutpoint mstate))
  :hints (("Goal" :in-theory (enable at-exitpoint at-cutpoint))))

(defthm prove-steps-to-next-cutpoint-natp
  (implies (and (at-cutpoint mstate)
		(not (at-exitpoint mstate)))
	   (natp (steps-to-cutpoint (next mstate))))
  :hints (("Goal" :in-theory (enable at-cutpoint next))))

;; This is an ordinal measure function that should
;; decrease from cutpoint to cutpoint, until an
;; exit point has been reached. In this example we
;; just use the value of the program counter.
(defun cutpoint-measure (mstate)
  (declare (xargs :stobjs (mstate)))
  (nfix (progc mstate)))

(defthm prove-cutpoint-measure-is-ordinal
  (o-p (cutpoint-measure mstate)))

(defthm prove-cutpoint-measure-decreases
  (implies (and (at-cutpoint mstate)
                (not (at-exitpoint mstate)))
           (o< (cutpoint-measure (cutpoint-to-cutpoint mstate))
               (cutpoint-measure mstate)))
  :hints (("Goal" :in-theory (enable cutpoint-to-cutpoint next
                                     at-cutpoint at-exitpoint))))

(in-theory (disable cutpoint-measure cutpoint-to-cutpoint))


#|================= The termination proof ===============|#

;;Proves that every cutpoint state eventually
;; leads to an exitpoint state.

(defthm steps-to-next-cutpoint-natp
  (implies (and (at-cutpoint mstate)
                (not (at-exitpoint mstate)))
           (natp (steps-to-cutpoint (next mstate)))))

(defthm cutpoint-measure-is-ordinal
  (o-p (cutpoint-measure mstate)))

(defthm cutpoint-measure-decreases
  (implies (and (at-cutpoint mstate)
                (not (at-exitpoint mstate)))
           (o< (cutpoint-measure (cutpoint-to-cutpoint mstate))
		     (cutpoint-measure mstate))))

;;Number of machine steps until we exit, assuming
;; we start at a cutpoint state.
(defun-nx steps-to-exitpoint (mstate)
  (declare (xargs :measure (cutpoint-measure mstate)))
  (cond
   ((not (at-cutpoint mstate)) 0)
   ((at-exitpoint mstate) 0)
   (t (+ 1 (steps-to-cutpoint (next mstate))
         (steps-to-exitpoint (cutpoint-to-cutpoint mstate))))))

(defthmd adding-natp-args-implies-natp
  (implies (and (natp m)
                (natp n))
           (natp (binary-+ m n))))

(defthm steps-to-exitpoint-natp
  (natp (steps-to-exitpoint mstate))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable cutpoint-to-cutpoint
                                     adding-natp-args-implies-natp))))

(defun-nx next-exitpoint (mstate)
  (declare (xargs :measure (cutpoint-measure mstate)))
  (cond
   ((not (at-cutpoint mstate))
    mstate)
   ((at-exitpoint mstate)
    mstate)
   (t
    (next-exitpoint (cutpoint-to-cutpoint mstate)))))

;;This is the guard verification condition for
;; a more efficient guarded version of NEXT-EXITPOINT
;; that assumes it starts in a cutpoint state. However,
;; CUTPOINT-TO-CUTPOINT is still non-executable.
(defthmd next-exitpoint-mbe
  (implies (and (at-cutpoint mstate)
                (not (at-exitpoint mstate)))
           (equal (next-exitpoint (cutpoint-to-cutpoint mstate))
                  (next-exitpoint mstate))))

;;The following two theorems show that any cutpoint
;; state eventually leads to an exitpoint state.

(defthmd next-exitpoint-correct
  (implies (at-cutpoint mstate)
           (equal (run (steps-to-exitpoint mstate) mstate)
                  (next-exitpoint mstate)))
  :hints (("Goal" :induct (steps-to-exitpoint mstate)
                  :do-not-induct t)))

(defthm at-cutpoint-implies-reaches-exitpoint
  (implies (at-cutpoint mstate)
           (at-exitpoint (next-exitpoint mstate)))
  :hints (("Goal" :induct (next-exitpoint mstate))))

(defthm cutpoint-implies-mstatep
  (implies (at-cutpoint mstate)
           (mstatep mstate))
  :hints (("Goal" :in-theory (enable at-cutpoint))))

#|==================================================================|#
