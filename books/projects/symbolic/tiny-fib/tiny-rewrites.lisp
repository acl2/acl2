(in-package "ACL2")

(include-book "tiny")
(local (include-book "arithmetic/top-with-meta" :dir :system))

; Helper function to lookup values from the top
; of the TINY data stack.
(defun dtos-val (tiny-state n)
  (declare (xargs :stobjs (tiny-state)
		  :guard (and (natp n)
			      (< (+ (dtos tiny-state) n 1)
				 (mem-length tiny-state))
			      (acl2-numberp (dtos tiny-state)))))
  (memi (+ (dtos tiny-state) n 1) tiny-state))

;Return the instruction pointed to by tiny's program counter
(defun instr-val (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (memi (progc tiny-state) tiny-state))


#|==== Rewrite rules for symbolically simulating tiny ====|#

;REVISIT: The RHS of each rewrite rule was taken directly
;         from the definition of 'next'. However, the RHS
;         could probably be simplified, if we added to the hypotheses
;         of each rewrite the condition (tiny-statep tiny-state).
;         Try the command
;           :pr
;         to see the rewrite rule generated from each theorem.

(defthm next-instr-pop
  (let* ((progc (progc tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 0)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
		      (popus (fix|10| (memi (+|10| progc 1)
					    tiny-state))
			     tiny-state)))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-pushs
  (let* ((progc (progc tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 1)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
		      (pushus (memi (fix|10| (memi (+|10| progc 1) tiny-state)) tiny-state) tiny-state)))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-pushsi
  (let* ((progc (progc tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 2)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
		      (pushus (memi (+|10| progc 1) tiny-state) tiny-state)))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-add
  (let* ((progc (progc tiny-state))
         (dtos  (dtos tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 3)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
		      (let ((tiny-state (update-dtos (+|10| dtos 2) tiny-state)))
			(pushus (add<32> (Int32 (memi (+|10| dtos 1) tiny-state))
					 (Int32 (memi (+|10| dtos 2) tiny-state)))
				tiny-state))))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-jump
  (let* ((progc (progc tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 4)
	     (equal (next tiny-state)
		    (update-progc (fix|10| (memi (+|10| progc 1) tiny-state)) tiny-state))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-jumpz
  (let* ((progc (progc tiny-state))
         (dtos  (dtos tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 5)
	     (equal (next tiny-state)
		    (let ((nprogc (if (= (memi (+|10| dtos 1) tiny-state) 0)
			     (fix|10| (memi (+|10| progc 1) tiny-state))
			   (+|10| progc 2))))
	     (declare (type (unsigned-byte 10) nprogc))
	     (let ((tiny-state (update-progc nprogc tiny-state)))
	       (update-dtos (+|10| dtos 1) tiny-state))))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-call
  (let* ((progc (progc tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 6)
	     (equal (next tiny-state)
		    (let ((nadd (fix|10| (memi (+|10| progc 1) tiny-state))))
		      (declare (type (unsigned-byte 10) nadd))
		      (let ((tiny-state (update-progc nadd tiny-state)))
			(pushcs (+|10| progc 2) tiny-state))))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-return
  (let* ((progc (progc tiny-state))
         (ctos  (ctos tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 7)
	     (equal (next tiny-state)
		    (let ((nadd (fix|10| (memi (+|10| ctos 1) tiny-state))))
		      (declare (type (unsigned-byte 10) nadd))
		      (let ((tiny-state (update-progc nadd tiny-state)))
			(update-ctos (+|10| ctos 1) tiny-state))))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-sub
  (let* ((progc (progc tiny-state))
         (dtos  (dtos tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 8)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
		      (let ((tiny-state (update-dtos (+|10| dtos 2) tiny-state)))
			(pushus (max<32> 0 (sub<32> (memi (+|10| dtos 2) tiny-state)
						    (memi (+|10| dtos 1) tiny-state)))
				tiny-state))))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-dup
  (let* ((progc (progc tiny-state))
         (dtos  (dtos tiny-state))
         (ins   (memi progc tiny-state)))
    (implies (equal ins 9)
	     (equal (next tiny-state)
		    (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
		      (pushus (memi (+|10| dtos 1) tiny-state) tiny-state)))))
  :hints (("Goal" :expand (next tiny-state))))

(defthm next-instr-halt
   (let* ((progc (progc tiny-state))
	  (ins   (memi progc tiny-state)))
     (implies (or (not (natp ins))
		  (<= 10 ins))
	      (equal (next tiny-state)
		     tiny-state)))
   :hints (("Goal" :expand (next tiny-state))))


#|==== Rules for infering when a program is loaded ====|#

(defun memory-block-loadedp (address list array)
  (declare (xargs :measure (acl2-count list)))
  (or (endp list)
      (and (equal (nth address array)
		  (first list))
	   (memory-block-loadedp (1+ address) (rest list) array))))

;;Refine the type-set ACL2 infers for the len function
(defthm typset-len-zero
  (implies (equal (len xs) 0)
	   (equal (consp xs) nil))
  :rule-classes ((:type-prescription)))

(defthm posp-n-consp-repeat
  (implies (posp n)
	   (consp (repeat n x)))
  :rule-classes :type-prescription)

(defthm car-repeat-posp
  (implies (posp n)
	   (equal (car (repeat n x)) x)))

;REVISIT: Is there an existing ACL2 idiom for specifying
;         induction on the naturals?
(defun nat-induction (n)
  (and (posp n)
       (nat-induction (1- n))))

;;This function is defined only to cause ACL2 to generate
;; an induction scheme needed to prove the nth-repeat theorem
;; below.
(defun nat-nat-induction (k n)
  (and (natp k)
       (natp n)
       (< 0 k)
       (< 0 n)
       (nat-nat-induction (1- k) (1- n))))

(defthm nth-repeat
  (implies (and (natp k)
		(natp n)
		(< k n))
	   (equal (nth k (repeat n x))
		  x))
  :hints (("Goal" :in-theory (enable nth repeat)
	          :induct (nat-nat-induction k n))))

(defthm memory-block-unmodified
  (implies (and (natp addr)
		(natp start-addr)
		(< addr (len memory))
		(<= (+ start-addr (len prog)) (len memory))
		(or (< addr start-addr)
		    (<= (+ start-addr (len prog)) addr)))
	   (iff (memory-block-loadedp start-addr
				      prog
				      (update-nth addr val memory))
		(memory-block-loadedp start-addr prog memory))))

;;Most memory accesses do not change the program code
(defthm code-not-self-modifying
  (iff (program-loaded (update-nth *memi* memory tiny-state)
		       prog
		       start-addr)
       (memory-block-loadedp start-addr prog memory))
       :hints (("goal" :in-theory (enable program-loaded))))

#|===== General lemmas needed during the proof of fib-partial-correctness ====|#

;The following theorems implement an "improved" version of
; memp-update-nth that can be applied
; in more cases than memp-update-nth can.

;;Used to generate a specialized induction scheme where an
;; index value is decreasing at the same rate as the length of a list.
(defun list-nat-induction (xs n)
  (and (consp xs)
       (posp n)
       (list-nat-induction (cdr xs) (1- n))))

(defthm memp-is-truelist
  (implies (memp m)
	   (true-listp m))
  :rule-classes :compound-recognizer)

(defthm update-nth-zero
  (implies (zp a)
	   (equal (update-nth a v xs)
		  (cons v (cdr xs))))
  :hints (("Goal" :expand (update-nth a v xs))))


(defthm update-nth-truelistp
  (implies (and (natp a)
		(< a (len m)))
	        (iff (true-listp (update-nth a v m))
		     (true-listp m)))
  :hints (("Goal" :in-theory (enable (update-nth))
	          :induct (list-nat-induction m a)
		  :do-not-induct t)
	  ("Subgoal *1/1.2" :expand (update-nth a v m))))

(defthm update-nth-truelistp-type
  (implies (and (natp a)
		(< a (len m))
		(true-listp m))
	   (true-listp (update-nth a v m)))
  :rule-classes :type-prescription)

(defthm update-nth-not-truelistp-type
  (implies (and (natp a)
		(< a (len m))
		(not (true-listp m)))
	   (not (true-listp (update-nth a v m))))
  :rule-classes :type-prescription)

(defthm nth-update-addr-integerp
  (implies (and (memp (update-nth a v m))
		(natp a)
		(< a (len m)))
	   (equal (integerp v) t))
  :hints (("Goal" :expand (update-nth a v m)
	          :induct (list-nat-induction m a)
	          :do-not-induct t)))

(defthm memp-update-nth-2
  (let ((old-v (nth a m)))
    (implies (and (natp a)
		  (< a (len m))
		  (integerp old-v)
		  (<= -2147483648 old-v)
		  (<= old-v 2147483647))
	     (iff (memp (update-nth a v m))
		  (and (integerp v)
		       (<= -2147483648 v)
		       (<= v 2147483647)
		       (memp m)))))
  :hints (("Goal" :in-theory (enable update-nth nth)
	          :induct (list-nat-induction m a)
		  :do-not-induct t)))

(in-theory (disable update-nth-zero))

(defthm memp-nth-integerp
  (implies (and (memp m)
		(integerp a)
		(<= 0 a)
		(< a (len m)))
	   (integerp (nth a m)))
  :rule-classes :type-prescription)

(defthm signed-byte-p-32-bounds
  (implies (signed-byte-p 32 n)
	   (and (<= -2147483648 n)
		(<= n 2147483647))))

(defthm tiny-posp-next
  (equal (tiny (next tiny-state) n)
	 (next (tiny tiny-state n)))
  :hints (("Goal" :in-theory (enable tiny))))

(defthm memi-elements-leq
  (implies (and (memp (nth *memi* tiny-state))
		(integerp n)
		(<= 0 n)
		(< n (len (nth *memi* tiny-state))))
	   (<= (nth n (nth *memi* tiny-state)) 2147483647))
  :rule-classes :linear)


#|==== Rules for stepping tiny an arbitrary number of times ====|#

;;The definition of TINY in tiny.lisp assumes that tiny will not
;; be stepped more than 2^32 times. For proving termination properties
;; of tiny we need to define a function that can step tiny any number
;; of times.

;daron: i'm not sure why this wasn't made executable, so i changed the definition
;(defun run (tiny-state n)
;  (declare (xargs :non-executable t))
;  (if (zp n)
;      tiny-state
;    (run (next tiny-state) (1- n))))

;(defun run (tiny-state n)
;  (declare (xargs :stobjs (tiny-state)
;                  :guard (natp n)))
;  (if (zp n)
;      tiny-state
;    (let ((tiny-state (next tiny-state)))
;      (run tiny-state (1- n)))))

;(defthm run-tiny-statep
;  (implies (tiny-statep tiny-state)
;	   (tiny-statep (run tiny-state n)))
;  :hints (("Goal" :in-theory (disable tiny-statep next))))

;(defthmd run-posp-next
;  (implies (posp n)
;	   (equal (run tiny-state n)
;		  (next (run tiny-state (1- n))))))

;(defthm run-next
;  (implies (natp n)
;	   (equal (run (next tiny-state) n)
;		  (next (run tiny-state n))))
;  :hints (("Goal" :induct (nat-induction n)
;	          :in-theory (enable run-posp-next))))

;(defthm run-run
;  (implies (and (natp k)
;		(natp n))
;	   (equal (run (run tiny-state k) n)
;		  (run tiny-state (+ k n)))))
