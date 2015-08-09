#|==================================================================|#

#|
An application of the techniques of our paper to a program to calculate
the nth number in the fibonacci sequence written for the tiny machine.
|#

;(in-package "partial-clock-functions")

(in-package "ACL2")

(include-book "tiny-rewrites")
(include-book "fib-def")
(include-book "misc/defpun" :dir :system)
(include-book "ordinals/ordinals" :dir :system)

(defun at-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (and	(member (progc tiny-state) *fib-cutpoints*)
        (program-loaded tiny-state *fib-prog* *prog-start-address*)
        (tiny-statep tiny-state)
        (equal (dtos tiny-state) *init-dtos*)
        (cond ((equal (progc tiny-state) *prog-start-address*)
               (< 0 (dtos-val tiny-state 0)))
              ((equal (progc tiny-state) *loop-label*)
               (<= 0 (dtos-val tiny-state 0)))
              ((equal (progc tiny-state) *done-label*)
               (= 0 (dtos-val tiny-state 0)))
              (t t))))

(defthm cutpoint-implies-tiny-statep
  (implies (at-cutpoint tiny-state)
           (tiny-statep tiny-state))
  :hints (("Goal" :in-theory (enable at-cutpoint)))
  :rule-classes :forward-chaining)

#|====== Partial clock functions and symbolic simulation ======|#

;A simulator that runs for N steps.
; N is a step-counter parameter.
(defun run (n tiny-state)
  (declare (xargs :stobjs (tiny-state)
                  :guard (natp n)))
  (if (zp n)
      tiny-state
    (let ((tiny-state (next tiny-state)))
      (run (1- n) tiny-state))))

;A tail-recursive partial function that returns the
; number of steps until tiny-state reaches a cutpoint state,
; if in fact tiny-state can eventually reach a cutpoint state.
; The parameter N is an accumulator, which clients
; should initially set to zero.
(defpun steps-to-cutpoint-tail (n tiny-state)
  (if (at-cutpoint tiny-state)
      n
    (steps-to-cutpoint-tail (1+ n) (run 1 tiny-state))))

(verify-guards omega)

(defthm tiny-statep-create-tiny-state
  (tiny-statep (create-tiny-state))
  :rule-classes :type-prescription)

(in-theory (disable create-tiny-state))

(defun steps-to-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (let ((steps (steps-to-cutpoint-tail 0 (copy-from-tiny-state tiny-state))))
    (if (and (natp steps)        ;the number of steps is a natural number
             (with-copy-of-stobj ;running a copy of tiny-state forward steps steps
	      tiny-state         ;gives us a cutpoint.
	      (mv-let (result tiny-state)
		      (let ((tiny-state (run steps tiny-state)))
			(mv (at-cutpoint tiny-state) tiny-state))
		      result)))
	steps
      (omega))))

;Simulate tiny-state until it reaches a cutpoint state,
; assuming it does.
(defun-nx run-to-cutpoint (tiny-state)
  (run (steps-to-cutpoint tiny-state) tiny-state))

(in-theory (disable at-cutpoint tiny-statep))

(defthm steps-to-cutpoint-tail-at-cutpoint
  (implies (at-cutpoint tiny-state)
           (equal (steps-to-cutpoint-tail n tiny-state)
                  n)))

(defthm steps-to-cutpoint-tail-not-cutpoint
  (implies (and (integerp n)
                (not (at-cutpoint tiny-state)))
           (equal (steps-to-cutpoint-tail n (run 1 tiny-state))
                  (steps-to-cutpoint-tail (- n 1) tiny-state))))

(in-theory (disable steps-to-cutpoint-tail-def))

(defthm tiny-statep-run
  (implies (tiny-statep tiny-state)
           (tiny-statep (run n tiny-state)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((run n tiny-state)))))

(defthm run-zero
  (implies (zp n)
           (equal (run n tiny-state)
                  tiny-state)))

(defthm run-1
  (equal (next tiny-state)
	 (run 1 tiny-state)))

(defthm run-plus
  (equal (run m (run n tiny-state))
         (run (+ (nfix m) (nfix n)) tiny-state)))

(in-theory (disable run))

(local
 (defun-nx steps-to-cutpoint-induction (k tiny-state steps)
   (declare (xargs :verify-guards nil
                   :guard (and (equal tiny-state tiny-state)
                               (equal steps steps))))
   (or (zp k)
       (steps-to-cutpoint-induction (1- k) (next tiny-state) (1+ steps)))))

(defthmd steps-to-cutpoint-tail-inv
  (implies (and (at-cutpoint (run k tiny-state))
                (integerp steps))
           (let* ((result     (steps-to-cutpoint-tail steps tiny-state))
                  (cutpoint-steps (- result steps)))
             (and (integerp result)
                  (natp cutpoint-steps)
                  (implies (natp k)
                           (<= cutpoint-steps k))
                  (at-cutpoint (run cutpoint-steps tiny-state)))))
  :hints (("Goal" :induct (steps-to-cutpoint-induction k tiny-state steps)
                  :do-not-induct t)
          ("Subgoal *1/2" :cases ((at-cutpoint tiny-state)))))

(defthm steps-to-cutpoint-tail-at-cutpoint-simp
  (implies (at-cutpoint (run k tiny-state))
           (at-cutpoint (run (steps-to-cutpoint-tail 0 tiny-state)
                        tiny-state)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv
				  (steps 0))))
  :rule-classes (:forward-chaining :rewrite))

(defthm steps-to-cutpoint-at-cutpoint
  (implies (and (at-cutpoint (run k tiny-state))
                (tiny-statep tiny-state))
           (at-cutpoint (run (steps-to-cutpoint tiny-state)
                        tiny-state)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv
				  (steps 0))))
  :rule-classes (:rewrite :forward-chaining))

(defthm steps-to-cutpoint-tail-diff
  (implies (and (at-cutpoint (run k tiny-state))
                (syntaxp (not (equal n ''0)))
                (integerp n)
                (tiny-statep tiny-state))
           (equal (steps-to-cutpoint-tail n tiny-state)
                  (+ n (steps-to-cutpoint-tail 0 tiny-state))))
  :hints (("Goal" :use ((:instance steps-to-cutpoint-tail-inv
                                   (k (- (steps-to-cutpoint-tail n tiny-state)
                                         n))
                                   (steps 0))
                        (:instance steps-to-cutpoint-tail-inv
                                   (k (steps-to-cutpoint tiny-state))
                                   (steps n))
                        (:instance steps-to-cutpoint-tail-inv
                                   (steps 0))))))

(defthm not-at-cutpoint-implies-steps-to-cutpoint-tail-nonzero
  (implies (and (at-cutpoint (run (steps-to-cutpoint-tail 0 tiny-state)
				  tiny-state))
		(not (at-cutpoint tiny-state)))
	   (posp (steps-to-cutpoint-tail 0 tiny-state)))
  :rule-classes (:rewrite))

(defthm not-at-cutpoint-implies-steps-to-cutpoint-tail-nonzero-fwd-chain
  (implies (and (at-cutpoint (run k tiny-state))
		(not (at-cutpoint tiny-state)))
	   (posp (steps-to-cutpoint-tail 0 tiny-state)))
  :rule-classes (:forward-chaining))

(defthm natp-steps-to-cutpoint-tail
  (implies (at-cutpoint (run (steps-to-cutpoint-tail 0 tiny-state) tiny-state))
	   (natp (steps-to-cutpoint-tail 0 tiny-state)))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv)))
  :rule-classes (:rewrite :forward-chaining))

(defthm natp-steps-to-cutpoint
  (implies (tiny-statep tiny-state)
           (equal (at-cutpoint (run (steps-to-cutpoint tiny-state) tiny-state))
                  (natp (steps-to-cutpoint tiny-state))))
  :hints (("Goal" :use (:instance steps-to-cutpoint-tail-inv)))
  :rule-classes (:rewrite))

(defthm steps-to-cutpoint-equals-omega-simp
  (iff (equal (steps-to-cutpoint tiny-state)
	      (omega))
       (not (natp (steps-to-cutpoint tiny-state)))))

(defthm o-p-steps-to-cutpoint
  (o-p (steps-to-cutpoint tiny-state))
  :hints (("Goal" :cases ((natp (steps-to-cutpoint tiny-state))))))

(defthm steps-to-cutpoint-zero
  (implies (and (at-cutpoint tiny-state)
                (tiny-statep tiny-state))
	   (equal (steps-to-cutpoint tiny-state) 0)))

(defthm integerp-add
  (equal (integerp (+ -1 n))
         (or (integerp n)
             (not (acl2-numberp n)))))

(defthmd steps-to-cutpoint-nonzero-intro
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
	   (equal (steps-to-cutpoint tiny-state)
		  (o+ 1 (steps-to-cutpoint (next tiny-state))))))

(defthm integerp-ord-decrement
  (implies (natp n)
	   (equal (o- n 1)
		  (max 0 (- n 1))))
  :hints (("Goal" :in-theory (enable o-))))

(defthm natp-steps-to-cutpoint-increment
  (equal (natp (o+ 1 (steps-to-cutpoint tiny-state)))
         (natp (steps-to-cutpoint tiny-state)))
  :hints (("Goal" :in-theory (enable o+))))

(defthm natp-steps-to-cutpoint-decrement
  (equal (natp (o- (steps-to-cutpoint tiny-state) 1))
         (natp (steps-to-cutpoint tiny-state)))
  :hints (("Goal" :in-theory (enable o-))))

(defthm omega-minus-one-equals-omega
  (equal (o- (omega) 1)
         (omega))
  :hints (("Goal" :in-theory (enable o-))))

(defthmd natp-ord-decrement
  (equal (natp (o- n 1))
         (or (and (o-finp n)
                  (or (<= n 1)
                      (posp n)))
             (< (o-first-expt n) 0)))
  :hints (("Goal" :in-theory (enable o- o< o-finp))))

(defthm o-finp-steps-to-cutpoint-iff-natp
  (equal (o-finp (steps-to-cutpoint tiny-state))
         (natp (steps-to-cutpoint tiny-state))))

(defthmd convert-at-cutpoint-to-steps-to-cutpoint
  (implies (tiny-statep tiny-state)
           (equal (at-cutpoint tiny-state)
                  (equal (steps-to-cutpoint tiny-state)
                         0))))

(defthm at-cutpoint-implies-steps-to-cutpoint-zero
  (implies (and (at-cutpoint tiny-state)
                (tiny-statep tiny-state))
	   (equal (steps-to-cutpoint tiny-state)
		  0))
  :rule-classes :forward-chaining)

(defthm not-at-cutpoint-implies-steps-to-cutpoint-nonzero
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
	   (not (equal (steps-to-cutpoint tiny-state)
		       0)))
  :rule-classes :forward-chaining)

(defthmd steps-to-cutpoint-nonzero-elim
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
	   (equal (steps-to-cutpoint (next tiny-state))
		  (o- (steps-to-cutpoint tiny-state) 1)))
  :hints (("Goal" :in-theory (enable steps-to-cutpoint-nonzero-intro))))

(defthm natp-steps-to-cutpoint-run
  (implies (and (natp (steps-to-cutpoint (run k tiny-state)))
                (tiny-statep tiny-state))
	   (natp (steps-to-cutpoint tiny-state))))

(in-theory (disable steps-to-cutpoint))

(defthm steps-to-cutpoint-run-1-elim
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
	   (equal (steps-to-cutpoint (run 1 tiny-state))
		  (o- (steps-to-cutpoint tiny-state) 1)))
  :hints (("Goal" :in-theory (e/d (steps-to-cutpoint-nonzero-elim run)
				  (run-1)))))

;Simulate TINY-STATE until it reaches the next
; cutpoint state, if there is one. If there isn't,
; then return NIL.
; This function allows simpler rewrite rules
; than RUN-TO-CUTPOINT does.
(defun dummy-state (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (let ((ts (with-local-stobj
             tiny-state
             (mv-let (result tiny-state)
                     (mv (copy-from-tiny-state tiny-state) tiny-state)
                     result))))
    (copy-to-tiny-state ts tiny-state)))

(defthm dummy-state-create-tiny-state
 (implies (tiny-statep tiny-state)
          (equal (dummy-state tiny-state)
                 (create-tiny-state))))

(defthm not-at-cutpoint-create-tiny-state
 (not (at-cutpoint (create-tiny-state)))
 :hints (("goal" :in-theory (enable create-tiny-state))))

(defun next-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)
                  :measure (steps-to-cutpoint tiny-state)
                  :guard (and (tiny-statep tiny-state)
                              (natp (steps-to-cutpoint tiny-state)))))
  (if (mbt (and (tiny-statep tiny-state)
		(natp (steps-to-cutpoint tiny-state))))
      (if (at-cutpoint tiny-state)
	  tiny-state
	(let ((tiny-state (next tiny-state)))
	  (next-cutpoint tiny-state)))
    (dummy-state tiny-state)))

(defthm tiny-statep-next-cutpoint
 (implies (tiny-statep tiny-state)
          (tiny-statep (next-cutpoint tiny-state)))
 :rule-classes ((:type-prescription) (:rewrite)))

(defthm next-cutpoint-at-cutpoint
  (implies (at-cutpoint tiny-state)
           (equal (next-cutpoint tiny-state)
                  tiny-state)))

(defthmd next-cutpoint-elim-next
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
           (equal (next-cutpoint (next tiny-state))
                  (next-cutpoint tiny-state))))

(defthm next-cutpoint-intro-next
  (implies (and (not (at-cutpoint tiny-state))
                (tiny-statep tiny-state))
           (equal (next-cutpoint tiny-state)
                  (next-cutpoint (next tiny-state)))))

(defthm next-cutpoint-reaches-cutpoint
  (implies (tiny-statep tiny-state)
           (equal (at-cutpoint (next-cutpoint tiny-state))
                  (natp (steps-to-cutpoint tiny-state)))))

(in-theory (e/d (steps-to-cutpoint-nonzero-intro) (next-cutpoint run-1)))

#|================== Program exit points and cutpoint-to-cutpoint =================|#

(defun at-exitpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (and (equal (progc tiny-state) *prog-halt-address*)
       (program-loaded tiny-state *fib-prog* *prog-start-address*)
       (tiny-statep tiny-state)
       (equal (dtos tiny-state) *init-dtos*)))

(defthm at-exitpoint-implies-at-cutpoint
  (implies (at-exitpoint tiny-state)
           (at-cutpoint tiny-state))
  :hints (("Goal" :in-theory (enable at-exitpoint at-cutpoint))))

(defthm prove-steps-to-next-cutpoint-natp
  (implies (and (at-cutpoint tiny-state)
		(not (at-exitpoint tiny-state)))
	   (natp (steps-to-cutpoint (next tiny-state))))
  :hints (("Goal" :in-theory (enable at-cutpoint steps-to-cutpoint-nonzero-intro tiny-statep))))

(defun cutpoint-to-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)
                  :guard (and (at-cutpoint tiny-state)
                              (not (at-exitpoint tiny-state)))
                  :guard-hints (("goal"
                                 :in-theory (disable steps-to-cutpoint-run-1-elim)))))
  (let ((tiny-state (next tiny-state)))
    (next-cutpoint tiny-state)))

(defthm tiny-statep-cutpoint-to-cutpoint
 (implies (tiny-statep tiny-state)
          (tiny-statep (cutpoint-to-cutpoint tiny-state)))
 :rule-classes ((:type-prescription) (:rewrite)))

(defthm cutpoint-to-cutpoint-returns-cutpoint-state
  (implies (and (natp (steps-to-cutpoint (next tiny-state)))
                (tiny-statep tiny-state))
           (at-cutpoint (cutpoint-to-cutpoint tiny-state))))

;had to add this one.
(defthmd next-cutpoint-to-run
 (let ((steps (steps-to-cutpoint tiny-state)))
    (implies (and (natp steps)
                  (tiny-statep tiny-state))
	     (equal (next-cutpoint tiny-state)
		    (run steps tiny-state))))
 :hints (("goal" :in-theory (e/d (next-cutpoint run)
                                 (run-1 run-zero)))))

(defthmd convert-cutpoint-to-cutpoint-to-run
  (let ((steps (steps-to-cutpoint (next tiny-state))))
    (implies (and (natp steps)
                  (tiny-statep tiny-state))
	     (equal (cutpoint-to-cutpoint tiny-state)
		    (run (1+ steps) tiny-state))))
  :hints (("Goal"
           :in-theory (enable run-1)
           :use ((:instance next-cutpoint-to-run (tiny-state
                                                  (next tiny-state)))))))

(in-theory (disable cutpoint-to-cutpoint))

(defthm run-cutpoint-to-cutpoint
  (let ((steps (steps-to-cutpoint (next tiny-state))))
    (implies (and (natp steps)
                  (tiny-statep tiny-state)
		  (natp k))
	     (equal (run k (cutpoint-to-cutpoint tiny-state))
		    (run (+ 1 k steps) tiny-state))))
  :hints (("Goal" :in-theory (enable convert-cutpoint-to-cutpoint-to-run))))

(defconst *max-prog-address* (1- (+ *prog-start-address*
				    (len *fib-prog*))))

;; This is an ordinal measure function that should
;; decrease from cutpoint to cutpoint, until an
;; exit point has been reached. In this example we
;; just use the value of the program counter.
(defun-nx cutpoint-measure (tiny-state)
  (if (at-exitpoint tiny-state)
      0
    (o+ (o* (omega) (nfix (dtos-val tiny-state 0)))
        (nfix (- *max-prog-address* (progc tiny-state))))))

(defthm prove-cutpoint-measure-is-ordinal
  (o-p (cutpoint-measure tiny-state)))

(local
  (defthm l1
    (implies (and (natp a)
                  (natp b)
                  (natp c)
                  (natp d)
                  (< a b))
             (o< (o+ (o* (omega) a) c)
                 (o+ (o* (omega) b) d)))
    :hints (("goal" :cases ((equal a 0))))))

(defthm prove-cutpoint-measure-decreases
  (implies (and (at-cutpoint tiny-state)
                (not (at-exitpoint tiny-state)))
           (o< (cutpoint-measure (cutpoint-to-cutpoint tiny-state))
               (cutpoint-measure tiny-state)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable cutpoint-to-cutpoint next
                              at-cutpoint at-exitpoint tiny-statep))))

(in-theory (disable cutpoint-measure cutpoint-to-cutpoint))


#|================= The termination proof ===============|#

#|======   Application: An efficient simulator              ======|#
#|======   FAST-CUTPOINT-TO-CUTPOINT with non-executable    ======|#
#|======   guards in the function's body                    ======|#

(in-theory (disable at-exitpoint))

;here's the defexec version. but the mbt version below is equivalent,
;still guaranteed to terminate, and more succinct.
;(defexec fast-cutpoint-to-cutpoint (tiny-state)
;  (declare (xargs :stobjs (tiny-state)
;                  :measure (cutpoint-measure tiny-state)
;                  :guard (at-cutpoint tiny-state))
;           (exec-xargs :default-value (dummy-state tiny-state)))
;  (mbe :logic (cond ((not (at-cutpoint tiny-state)) (dummy-state tiny-state))
;                    ((at-exitpoint tiny-state) tiny-state)
;                    (t (let ((tiny-state (cutpoint-to-cutpoint tiny-state)))
;                         (fast-cutpoint-to-cutpoint tiny-state))))
;       :exec (if (at-exitpoint tiny-state)
;                 tiny-state
;               (let ((tiny-state (cutpoint-to-cutpoint tiny-state)))
;                 (fast-cutpoint-to-cutpoint tiny-state)))))

(defun fast-cutpoint-to-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)
                  :measure (cutpoint-measure tiny-state)
                  :guard (at-cutpoint tiny-state)))
  (if (mbt (at-cutpoint tiny-state))
      (if (at-exitpoint tiny-state)
          tiny-state
        (let ((tiny-state (cutpoint-to-cutpoint tiny-state)))
          (fast-cutpoint-to-cutpoint tiny-state)))
    (dummy-state tiny-state)))

#|==================================================================|#