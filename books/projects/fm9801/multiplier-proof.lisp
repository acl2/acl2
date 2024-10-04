;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; multiplier.lisp:
; Author  Jun Sawada, University of Texas at Austin
;
;  Correctness proof of the Wallace tree multiplier.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "b-ops-aux")
(include-book "basic-def")
(include-book "multiplier-def")

(deflabel begin-multiplier-proof)
(in-theory (disable def-multiplier))

; In the following few lemmas, we prove that the standard adder adds.
(in-theory (enable (:REWRITE FOLD-CONSTS-IN-+)))
(in-theory (disable (:REWRITE FLOOR-TYPE-3 . 2)
		    (:REWRITE FLOOR-TYPE-4 . 2)
		    (:generalize FLOOR-TYPE-4)
		    (:generalize FLOOR-TYPE-3)
		    (:generalize FLOOR-TYPE-2)
		    (:generalize FLOOR-TYPE-1)
		    (:generalize FLOOR-=-X/Y)
		    (:generalize Mod-type)
; Matt K. mod: Comment out runes that no longer exist.
		    ;; (:generalize Mod-bounds)
		    ;; (:generalize MOD-X-Y-=-X+Y)
		    ;; (:generalize MOD-X-Y-=-X)
                    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Miscellaneous Lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;'
; Basic lemmas about Mod.
(defthm mod-+-distribute-1
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (> d 0)
		  (equal (mod x d) x1)
		  (syntaxp (equal (car x1) 'quote)))
	     (equal (mod (+ x y) d) (mod (+ x1 y) d))))

(defthm mod-+-distribute-2
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (> d 0)
		  (equal (mod y d) y1)
		  (syntaxp (equal (car y1) 'quote)))
	     (equal (mod (+ x y) d) (mod (+ x y1) d))))

(defthm mod-+-distribute-3
    (implies (and (integerp x)
		  (integerp y)
		  (integerp z)
		  (integerp d)
		  (> d 0)
		  (equal (mod z d) z1)
		  (syntaxp (equal (car z1) 'quote)))
	     (equal (mod (+ x y z) d) (mod (+ x y z1) d)))
  :hints (("Goal" :use (:instance mod-+-distribute-2
				  (x (+ x y))
				  (y z) (y1 z1)))))

(defthm logcons-x-to-0
    (equal (logcons x 0) (bfix x))
  :hints (("goal" :in-theory (enable logcons))))

(defthm loghead-16-word-p
    (implies (word-p w)
	     (equal (loghead 16 w) w))
  :hints (("Goal" :in-theory (enable word-p))))

(local
 (defthm logbitp-0
    (implies (integerp vector)
	     (equal (logbitp 0 vector)
		    (equal (logcar vector) 1)))
  :hints (("goal" :in-theory (e/d (logbitp*) (logbitp))))))

(local
 (defun loghead-induction (n vector)
  (if (zp n) (list n vector)
      (loghead-induction (1- n) (logcdr vector)))))

; Another recursive definition of loghead. Another recursive definition of
; loghead recurses from the least significant bit.  This new version
; recurses from the most significant bit.
(defthm loghead**
    (implies (and (integerp vector)
		  (integerp n)
		  (>= n 0))
	     (equal (loghead n vector)
		    (if (zp n)
			0
			(logapp (1- n)
				(loghead (1- n) vector)
				(logbit (1- n) vector)))))
  :hints (("Goal" :induct (loghead-induction n vector)
		  :in-theory (e/d (loghead* logapp* logbit*)
				  (EXPONENTS-ADD))))
  :rule-classes :definition)

(in-theory (disable loghead**))

(defthm unsigned-byte-p-logcons
    (implies (and (integerp n)
		  (>= n 0)
		  (unsigned-byte-p n v)
		  (bitp c)
		  (integerp v))
	     (unsigned-byte-p (1+ n) (logcons c v)))
  :hints (("goal" :in-theory (enable unsigned-byte-p*))))

(defthm unsigned-byte-p-<
    (implies (and (integerp k)
		  (unsigned-byte-p n a)
		  (integerp n)
		  (< n k))
	     (unsigned-byte-p k a))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p)
				  (EXPT-IS-INCREASING-FOR-BASE>1))
		  :use (:instance EXPT-IS-INCREASING-FOR-BASE>1
				  (r 2) (I n) (J k)))))

(defthm unsigned-byte-p-+
     (implies (and (unsigned-byte-p n a)
		   (unsigned-byte-p n b))
	      (unsigned-byte-p (1+ n) (+ a b)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;; Removing redundant the type-enforcing function "word" in additions. 
(defthm word-add-word-1
    (implies (and (integerp x) (integerp y))
	     (equal (word (+ (word x) y)) (word (+ x y))))
  :hints (("goal" :in-theory (enable word loghead))))

(defthm word-add-word-2
    (implies (and (integerp x) (integerp y))
	     (equal (word (+ x (word y))) (word (+ x y))))
  :hints (("goal" :in-theory (enable word loghead))))

(defun expr-enforced-word-p (exp)
    (and (consp exp)
	 (equal (car exp) 'word))) 

(defun expr-addition-with-word-in-it-p (exp)
  (if (consp exp)
      (if (equal (car exp) 'binary-+)
	  (or (expr-enforced-word-p (cadr exp))
	      (expr-enforced-word-p (caddr exp))
	      (expr-addition-with-word-in-it-p (caddr exp)))
	  nil)
      nil))

(defthm ferment-word-to-add
    (implies (and (integerp x) (integerp y)
		  (syntaxp (expr-addition-with-word-in-it-p y)))
	     (equal (word (+ x y)) (word (+ x (word y)))))
  :hints (("goal" :in-theory (enable word loghead))))

(deftheory word-enforcer-remover
    '(ferment-word-to-add word-add-word-1 word-add-word-2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Here we prove the CSA actually adds numbers.  The strategy is as follows: 
; First we define a standard adder, and prove that CSA works as
; the standard adder.  We also prove that the standard adder adds.
; Finally we combine the fact together to show that CSA is an adder.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun b-maj (b1 b2 b3)
  (bs-ior (b-and b1 b2)
	  (b-and b1 b3)
	  (b-and b2 b3)))

; A definition of the standard adder.
(defun n-adder (n a b c)
  (if (zp n)
      (b-xor (b-xor (logcar a) (logcar b)) c)
      (logcons (b-xor (b-xor (logcar a) (logcar b)) c)
	       (n-adder (1- n)
			(logcdr a)
			(logcdr b)
			(b-maj (logcar a) (logcar b) c)))))

; Recursive definition of CSA-out.
(defthm CSA-out*
    (implies (and (force (integerp X))
		  (force (integerp Y))
		  (force (integerp Z)))
	     (equal (CSA-out x y z)
		    (logcons (b-xor (b-xor (logcar x) (logcar y)) (logcar z))
			     (CSA-out (logcdr x)
				      (logcdr y)
				      (logcdr z)))))
  :hints (("Goal" :in-theory (enable CSA-out logxor*)))
  :rule-classes ((:definition :clique (CSA-out)
		              :controller-alist ((CSA-out t t t)))))

; Recursive definition of CSA-carry.
(defthm CSA-carry*
    (implies (and (force (integerp X))
		  (force (integerp Y))
		  (force (integerp Z)))
	     (equal (CSA-carry x y z)
		    (logcons (b-maj (logcar x) (logcar y) (logcar z))
			     (CSA-carry (logcdr x)
					(logcdr y)
					(logcdr z)))))
  :hints (("Goal" :in-theory (enable CSA-carry logior* logand*)))
  :rule-classes ((:definition :clique (CSA-carry)
		              :controller-alist ((CSA-carry t t t)))))

; In future, the user has to specify which definition they want to use. 
(in-theory (disable CSA-out CSA-carry CSA-out* CSA-carry*))

;; Proof of the correctness of the standard adder.
(defthm logcar-plus
    (implies (and (bitp c)
		  (integerp x)
		  (integerp y))
	     (equal (logcar (+ c x y))
		    (b-xor c (b-xor (logcar x) (logcar y)))))
  :hints (("goal" :in-theory (e/d (logcar b-xor bitp)
				  (MOD-=-0 )))))

; Matt K. mod: The proof of logcdr-plus below now fails without the preceding
; events.  Note that rune floor-bounds no longer exists.
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (in-theory (disable (:rewrite |(equal (if a b c) x)|))))
  (local (in-theory (disable (:rewrite |(equal x (if a b c))|))))

  (defthm logcdr-plus
    (implies (and (bitp c)
		  (integerp x)
		  (integerp y))
	     (equal (logcdr (+ c x y))
		    (+ (logcdr x)
		       (logcdr y)
		       (b-maj (logcar x) (logcar y) c))))
    :hints (("goal"
             :use floor-+
             :in-theory (e/d (logcdr logcar bitp)
                             (MOD-=-0
                              ;; floor-bounds
                              ))))))

; Matt K. mod: This trivial consequence of logcar-plus is now needed for the
; proof of standard-adder-adds.
(defthm logcar-plus-simple
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logcar (+ x y))
		    (b-xor (logcar x) (logcar y))))
  :hints (("Goal"
           :use ((:instance logcar-plus (c 0)))
           :in-theory (disable logcar-plus))))

; Matt K. mod: This trivial consequence of logcdr-plus is now needed for the
; proof of standard-adder-adds.
(defthm logcdr-plus-simple
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logcdr (+ x y))
		    (+ (logcdr x)
		       (logcdr y)
		       (b-maj (logcar x) (logcar y) 0))))
    :hints (("Goal"
             :use ((:instance logcdr-plus (c 0)))
             :in-theory (disable logcdr-plus))))

(defthm standard-adder-adds
    (implies (and (integerp n)
		  (>= n 0)
		  (unsigned-byte-p n x)
		  (unsigned-byte-p n y)
		  (bitp c))
	     (equal (n-adder n x y c)
		    (+ x y c)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p*))))
		  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Now we build the framework of the main proof.

(defun three-bitvector-induction (n a b c)
  (if (zp n)
      (list a b c)
      (three-bitvector-induction (1- n) (logcdr a) (logcdr b) (logcdr c))))

(defthm unsigned-byte-p-CSA-out
    (implies (and (unsigned-byte-p n a)
		  (unsigned-byte-p n b)
		  (unsigned-byte-p n c))
	     (unsigned-byte-p n (CSA-out a b c)))
  :hints (("Goal" :in-theory (enable CSA-out* unsigned-byte-p*)
		  :induct (three-bitvector-induction n a b c))
	  ("Subgoal *1/1" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-CSA-carry
    (implies (and (unsigned-byte-p n a)
		  (unsigned-byte-p n b)
		  (unsigned-byte-p n c))
	     (unsigned-byte-p n (CSA-carry a b c)))
  :hints (("Goal" :in-theory (enable CSA-carry* unsigned-byte-p*)
		  :induct (three-bitvector-induction n a b c))
	  ("Subgoal *1/1" :in-theory (enable unsigned-byte-p))))

(defun CSA-adder-induction (n x y z c1 c2 d1 d2) 
  (if (zp n)
      (list n x y z c1 c2 d1 d2)
      (CSA-adder-induction (1- n)
			   (logcdr x)
			   (logcdr y)
			   (logcdr z)
			   (b-maj (logcar x) (logcar y) (logcar z))
			   (b-maj (b-xor (b-xor (logcar x) (logcar y))
					 (logcar z))
				  c1 c2)
			   (b-maj (logcar y) (logcar z) d1)
			   (b-maj (logcar x)
				  (b-xor (b-xor (logcar y) (logcar z)) d1)
				  d2))))

(defthm CSA-adder-rec
    (implies (and (integerp n)
		  (>= n 0)
		  (unsigned-byte-p n x) 
		  (unsigned-byte-p n y) 
		  (unsigned-byte-p n z) 
		  (bitp c1)
		  (bitp c2)
		  (bitp d1)
		  (bitp d2)
		  (equal (b-xor c1 c2) (b-xor d1 d2))
		  (equal (b-and c1 c2) (b-and d1 d2)))
	     (equal (n-adder (1+ n)
			     (CSA-out x y z)
			     (logcons c1 (CSA-carry x y z))
			     c2)
		    (n-adder (1+ n) x (n-adder n y z d1) d2)))
  :hints (("Goal" :in-theory (enable loghead* 
				     unsigned-byte-p* CSA-out* CSA-carry*)
		  :induct (CSA-adder-induction n x y z c1 c2 d1 d2))
	  ("subgoal *1/2.3" :in-theory (enable b-xor b-ior b-and)
			    :bdd (:vars nil :bdd-constructors nil))
	  ("subgoal *1/2.2''" :in-theory (enable b-xor b-ior b-and)
			      :bdd (:vars nil :bdd-constructors nil))
	  ("subgoal *1/2.1" :in-theory (enable b-xor b-ior b-and)
			    :bdd (:vars nil :bdd-constructors nil))
	  ("subgoal *1/1" :in-theory (enable bitp)))
  :rule-classes nil)

(defthm CSA-is-adder
    (implies (and (word-p a) (word-p b) (word-p c))
	     (equal (+ (CSA-out a b c) (logcons 0 (CSA-carry a b c)))
		    (+ a b c)))
  :hints (("Goal" :use (:instance CSA-adder-rec (x a) (y b) (z c)
				  (c1 0) (c2 0) (d1 0) (d2 0) (n 16))
		  :in-theory (enable word-p))))
				  

(defthm CSA-is-word-adder
    (implies (and (word-p a) (word-p b) (word-p c))
	     (equal (word (+ (CSA-out a b c) (shift-1 (CSA-carry a b c))))
		    (word (+ a b c))))
  :hints (("Goal" :in-theory (enable shift-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Here, we define a standard multiplier with a function add-n-shift. 
; We prove that (add-n-shift 16 m1 m2) is a 16-bit multiplier.
; This is a stepping-stone for proving the correctness of CSA-multiplier.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
(defun add-n-shift (n multiplicand multiplier)
  (if (zp n)
      0
      (word (+ (shifter (1- n) multiplicand multiplier)
	       (add-n-shift (1- n) multiplicand multiplier)))))

(defthm word-add-n-shift
    (equal (word (add-n-shift n m1 m2))
	   (add-n-shift n m1 m2)))

(encapsulate nil
(local
 (defthm logbit-1-or-0
     (implies (not (equal (logbit n multiplier) 0))
	      (equal (logbit n multiplier) 1))
   :hints (("Goal" :in-theory (enable logbit)))))

(local
 (defthm shifter-to-multiply
     (implies (and (integerp n)
		   (>= n 0)
		   (integerp multiplicand)
		   (integerp multiplier))
	      (equal (shifter n multiplicand multiplier)
		     (word (* multiplicand (expt 2 n) (logbit n multiplier)))))
   :hints (("goal" :cases ((equal (logbit n multiplier) 0))
		   :in-theory (enable shifter logapp)))))

(defthm add-n-shift-mult-rec
    (implies (and (integerp multiplier)
		  (integerp multiplicand)
		  (integerp n)
		  (>= n 0))
	     (equal (add-n-shift n multiplicand multiplier)
		    (word (* multiplicand
			     (loghead n multiplier)))))
  :hints (("Goal" :in-theory (e/d (loghead** logapp)
				  (EXPONENTS-ADD)))))
) ; encapsulate

(defthm add-n-shift-mult
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (equal (add-n-shift 16 multiplicand multiplier)
		    (word (* multiplicand multiplier))))
  :hints (("goal" :in-theory (enable word))))

(in-theory (disable add-n-shift-mult-rec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proving the CSA-multiplier.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm CSA-1-1-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-1-1-out m1 m2)
			     (shift-1 (CSA-1-1-carry m1 m2))))
		    (word (+ (shifter 15 m1 m2)
			     (shifter 14 m1 m2)
			     (shifter 13 m1 m2)))))
  :hints (("Goal" :in-theory (enable CSA-1-1-out CSA-1-1-carry))))

(defthm CSA-1-2-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-1-2-out m1 m2)
			     (shift-1 (CSA-1-2-carry m1 m2))))
		    (word (+ (shifter 12 m1 m2)
			     (shifter 11 m1 m2)
			     (shifter 10 m1 m2)))))
  :hints (("Goal" :in-theory (enable CSA-1-2-out CSA-1-2-carry))))

(defthm CSA-1-3-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-1-3-out m1 m2)
			     (shift-1 (CSA-1-3-carry m1 m2))))
		    (word (+ (shifter 9 m1 m2)
			     (shifter 8 m1 m2)
			     (shifter 7 m1 m2)))))
  :hints (("Goal" :in-theory (enable CSA-1-3-out CSA-1-3-carry))))

(defthm CSA-1-4-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-1-4-out m1 m2)
			     (shift-1 (CSA-1-4-carry m1 m2))))
		    (word (+ (shifter 6 m1 m2)
			     (shifter 5 m1 m2)
			     (shifter 4 m1 m2)))))
  :hints (("Goal" :in-theory (enable CSA-1-4-out CSA-1-4-carry))))

(defthm CSA-1-5-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-1-5-out m1 m2)
			     (shift-1 (CSA-1-5-carry m1 m2))))
		    (word (+ (shifter 3 m1 m2)
			     (shifter 2 m1 m2)
			     (shifter 1 m1 m2)))))
  :hints (("Goal" :in-theory (enable CSA-1-5-out CSA-1-5-carry))))

(defthm CSA-2-1&2-sum-hint-1
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-1-2-out m1 m2)
				      (shift-1 (CSA-1-2-carry m1 m2))))
			     (word (+ (CSA-1-3-out m1 m2)
				      (shift-1 (CSA-1-3-carry m1 m2))))
			     (word (+ (CSA-1-4-out m1 m2)
				      (shift-1 (CSA-1-4-carry m1 m2))))))
		    (word (+ (word (+ (shifter 12 m1 m2)
				      (shifter 11 m1 m2)
				      (shifter 10 m1 m2)))
			     (word (+ (shifter 9 m1 m2)
				      (shifter 8 m1 m2)
				      (shifter 7 m1 m2)))
			     (word (+ (shifter 6 m1 m2)
				      (shifter 5 m1 m2)
				      (shifter 4 m1 m2)))))))
  :rule-classes nil)

(in-theory (disable (:REWRITE CSA-1-2-SUM)
		    (:REWRITE CSA-1-3-SUM)
		    (:REWRITE CSA-1-4-SUM)))
			     
(defthm CSA-2-1&2-sum-hint-2 
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-2-1-out m1 m2)
				      (shift-1 (CSA-2-1-carry m1 m2))))
			     (word (+ (CSA-2-2-out m1 m2)
				      (shift-1 (CSA-2-2-carry m1 m2))))))
		    (word (+ (word (+ (CSA-1-2-out m1 m2)
				      (shift-1 (CSA-1-2-carry m1 m2))
				      (CSA-1-3-out m1 m2)))
			     (word (+ (shift-1 (CSA-1-3-carry m1 m2))
				      (CSA-1-4-out m1 m2)
				      (shift-1 (CSA-1-4-carry m1 m2))))))))
  :hints (("goal" :in-theory (e/d (CSA-2-1-out CSA-2-1-carry
				     CSA-2-2-out CSA-2-2-carry)
				  (word-enforcer-remover))))
  :rule-classes nil)

(defthm CSA-2-1&2-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-2-1-out m1 m2)
			     (CSA-2-2-out m1 m2)
			     (shift-1 (CSA-2-1-carry m1 m2))
			     (shift-1 (CSA-2-2-carry m1 m2))))
		    (word (+ (shifter 12 m1 m2)
			     (shifter 11 m1 m2)
			     (shifter 10 m1 m2)
			     (shifter 9 m1 m2)
			     (shifter 8 m1 m2)
			     (shifter 7 m1 m2)
			     (shifter 6 m1 m2)
			     (shifter 5 m1 m2)
			     (shifter 4 m1 m2)))))
  :hints (("goal" :use ((:instance CSA-2-1&2-sum-hint-1)
			(:instance CSA-2-1&2-sum-hint-2)))))

(defthm CSA-2-3-sum-hint
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-1-5-out m1 m2)
				      (shift-1 (CSA-1-5-carry m1 m2))))
			     (shifter 0 m1 m2)))
		    (word (+ (word (+ (shifter 3 m1 m2)
				      (shifter 2 m1 m2)
				      (shifter 1 m1 m2)))
			     (shifter 0 m1 m2)))))
  :rule-classes nil)

				      
(defthm CSA-2-3-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-2-3-out m1 m2)
			     (shift-1 (CSA-2-3-carry m1 m2))))
		    (word (+ (shifter 3 m1 m2)
			     (shifter 2 m1 m2)
			     (shifter 1 m1 m2)
			     (shifter 0 m1 m2)))))
  :hints (("Goal" :use (:instance CSA-2-3-sum-hint)
		  :in-theory (e/d (CSA-2-3-out CSA-2-3-carry)
				  (CSA-1-5-SUM)))))

(defthm CSA-3-1&2-sum-hint-1
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-3-1-out m1 m2)
				      (shift-1 (CSA-3-1-carry m1 m2))))
			     (word (+ (CSA-3-2-out m1 m2)
				      (shift-1 (CSA-3-2-carry m1 m2))))))
		    (word (+ (word (+ (CSA-1-1-out m1 m2)
				      (shift-1 (CSA-1-1-carry m1 m2))
				      (CSA-2-1-out m1 m2)))
			     (word (+ (shift-1 (CSA-2-1-carry m1 m2))
				      (CSA-2-2-out m1 m2)
				      (shift-1 (CSA-2-2-carry m1 m2))))))))
  :hints (("goal" :in-theory (e/d (CSA-3-1-out CSA-3-1-carry
				     CSA-3-2-out CSA-3-2-carry)
				  (word-enforcer-remover))))
  :rule-classes nil)

(defthm CSA-3-1&2-sum-hint-2
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-1-1-out m1 m2)
				      (shift-1 (CSA-1-1-carry m1 m2))))
			     (word (+ (CSA-2-1-out m1 m2)
				      (shift-1 (CSA-2-1-carry m1 m2))
				      (CSA-2-2-out m1 m2)
				      (shift-1 (CSA-2-2-carry m1 m2))))))
		    (word (+ (word (+ (shifter 15 m1 m2)
				      (shifter 14 m1 m2)
				      (shifter 13 m1 m2)))
			     (word (+ (shifter 12 m1 m2)
				      (shifter 11 m1 m2)
				      (shifter 10 m1 m2)
				      (shifter 9 m1 m2)
				      (shifter 8 m1 m2)
				      (shifter 7 m1 m2)
				      (shifter 6 m1 m2)
				      (shifter 5 m1 m2)
				      (shifter 4 m1 m2)))))))
  :hints (("goal" :in-theory (disable word-enforcer-remover)))
  :rule-classes nil)

(defthm CSA-3-1&2-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-3-1-out m1 m2)
			     (CSA-3-2-out m1 m2)
			     (shift-1 (CSA-3-1-carry m1 m2))
			     (shift-1 (CSA-3-2-carry m1 m2))))
		    (word (+ (shifter 15 m1 m2)
			     (shifter 14 m1 m2)
			     (shifter 13 m1 m2)
			     (shifter 12 m1 m2)
			     (shifter 11 m1 m2)
			     (shifter 10 m1 m2)
			     (shifter 9 m1 m2)
			     (shifter 8 m1 m2)
			     (shifter 7 m1 m2)
			     (shifter 6 m1 m2)
			     (shifter 5 m1 m2)
			     (shifter 4 m1 m2)))))
  :hints (("Goal" :use ((:instance CSA-3-1&2-sum-hint-1)
			(:instance CSA-3-1&2-sum-hint-2))
		  :in-theory (disable CSA-2-1&2-SUM CSA-1-1-SUM))))

(defthm CSA-4-1-sum
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (equal (word (+ (CSA-4-1-out s1 s2 s3 s4 s5 s6)
			     (shift-1 (CSA-4-1-carry s1 s2 s3 s4 s5 s6))))
		    (word (+ s1 s2 s3))))
  :hints (("goal" :in-theory (enable CSA-4-1-out CSA-4-1-carry))))

(defthm CSA-4-2-sum
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (equal (word (+ (CSA-4-2-out s1 s2 s3 s4 s5 s6)
			     (shift-1 (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))
		    (word (+ s4 s5 s6))))
  :hints (("goal" :in-theory (enable CSA-4-2-out CSA-4-2-carry))))

(defthm CSA-5-1-sum-hint-1
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
     (equal (word (+ (CSA-4-1-out s1 s2 s3 s4 s5 s6)
		     (word (+ (CSA-5-1-out s1 s2 s3 s4 s5 s6)
			      (shift-1 (CSA-5-1-carry s1 s2 s3 s4 s5 s6))))))
	    (word (+ (CSA-4-1-out s1 s2 s3 s4 s5 s6)
		     (word (+ (shift-1 (CSA-4-1-carry s1 s2 s3 s4 s5 s6))
			      (CSA-4-2-out s1 s2 s3 s4 s5 s6)
			      (shift-1 (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))))))
  :hints (("goal" :in-theory (enable CSA-5-1-out CSA-5-1-carry)))
  :rule-classes nil)

(defthm CSA-5-1-sum-hint-2
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
     (equal (word (+ (word (+ (CSA-4-1-out s1 s2 s3 s4 s5 s6)
			      (shift-1 (CSA-4-1-carry s1 s2 s3 s4 s5 s6))))
		     (word (+ (CSA-4-2-out s1 s2 s3 s4 s5 s6)
			      (shift-1 (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))))
	    (word (+ (word (+ s1 s2 s3)) (word (+ s4 s5 s6))))))
  :rule-classes nil)

(in-theory (disable (:REWRITE CSA-4-2-SUM) (:REWRITE CSA-4-1-SUM)))

(defthm CSA-5-1-sum
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (equal (word (+ (CSA-4-1-out s1 s2 s3 s4 s5 s6)
			     (CSA-5-1-out s1 s2 s3 s4 s5 s6)
			     (shift-1 (CSA-5-1-carry s1 s2 s3 s4 s5 s6))))
		    (word (+ s1 s2 s3 s4 s5 s6))))
  :hints (("Goal" :use ((:instance CSA-5-1-sum-hint-1)
			(:instance CSA-5-1-sum-hint-2)))))

(defthm CSA-6-1-sum
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (equal (word (+ (CSA-6-1-out s1 s2 s3 s4 s5 s6)
			     (shift-1 (CSA-6-1-carry s1 s2 s3 s4 s5 s6))))
		    (word (+ s1 s2 s3 s4 s5 s6))))
  :hints (("Goal" :in-theory (enable CSA-6-1-out CSA-6-1-carry))))

(defthm CSA-3-all-sum-hint
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (word (+ (CSA-3-1-out m1 m2)
				      (CSA-3-2-out m1 m2)
				      (shift-1 (CSA-3-1-carry m1 m2))
				      (shift-1 (CSA-3-2-carry m1 m2))))
			     (word (+ (CSA-2-3-out m1 m2)
				      (shift-1 (CSA-2-3-carry m1 m2))))))
		    (word (+ (word (+ (shifter 15 m1 m2)
				      (shifter 14 m1 m2)
				      (shifter 13 m1 m2)
				      (shifter 12 m1 m2)
				      (shifter 11 m1 m2)
				      (shifter 10 m1 m2)
				      (shifter 9 m1 m2)
				      (shifter 8 m1 m2)
				      (shifter 7 m1 m2)
				      (shifter 6 m1 m2)
				      (shifter 5 m1 m2)
				      (shifter 4 m1 m2)))
			     (word (+ (shifter 3 m1 m2)
				      (shifter 2 m1 m2)
				      (shifter 1 m1 m2)
				      (shifter 0 m1 m2)))))))
  :rule-classes nil)

(in-theory (disable CSA-2-3-sum CSA-3-1&2-sum))

(defthm CSA-3-all-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (CSA-2-3-out m1 m2)
			     (CSA-3-1-out m1 m2)
			     (CSA-3-2-out m1 m2)
			     (shift-1 (CSA-2-3-carry m1 m2))
			     (shift-1 (CSA-3-1-carry m1 m2))
			     (shift-1 (CSA-3-2-carry m1 m2))))
		    (word (+ (shifter 15 m1 m2)
			     (shifter 14 m1 m2)
			     (shifter 13 m1 m2)
			     (shifter 12 m1 m2)
			     (shifter 11 m1 m2)
			     (shifter 10 m1 m2)
			     (shifter 9 m1 m2)
			     (shifter 8 m1 m2)
			     (shifter 7 m1 m2)
			     (shifter 6 m1 m2)
			     (shifter 5 m1 m2)
			     (shifter 4 m1 m2)
			     (shifter 3 m1 m2)
			     (shifter 2 m1 m2)
			     (shifter 1 m1 m2)
			     (shifter 0 m1 m2)))))
  :hints (("Goal" :use (:instance CSA-3-all-sum-hint))))

(defthm ML1-sums-sum
    (implies (and (word-p m1) (word-p m2))
	     (equal (word (+ (ML1-sum1 m1 m2) (ML1-sum2 m1 m2)
			     (ML1-sum3 m1 m2) (ML1-sum4 m1 m2)
			     (ML1-sum5 m1 m2) (ML1-sum6 m1 m2)))
		    (word (add-n-shift 16 m1 m2))))
  :hints (("Goal" :in-theory (e/d (ML1-sum1 ML1-sum2 ML1-sum3 ML1-sum4
				     ML1-sum5 ML1-sum6)
				  (ADD-N-SHIFT-MULT))))) 

(defthm ML2-sums-sum
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (equal (word (+ (ML2-sum1 s1 s2 s3 s4 s5 s6)
			     (ML2-sum2 s1 s2 s3 s4 s5 s6)))
		    (word (+ s1 s2 s3 s4 s5 s6))))
  :hints (("Goal" :in-theory (enable ML2-sum1 ML2-sum2))))

; Finally the proof of the multiplier.
(defthm correctness-of-multiplier
    (implies (and (word-p m1) (word-p m2))
     (let ((s1 (ML1-sum1 m1 m2)) (s2 (ML1-sum2 m1 m2)) (s3 (ML1-sum3 m1 m2))
	   (s4 (ML1-sum4 m1 m2)) (s5 (ML1-sum5 m1 m2)) (s6 (ML1-sum6 m1 m2)))
       (let ((sum1 (ML2-sum1 s1 s2 s3 s4 s5 s6))
	     (sum2 (ML2-sum2 s1 s2 s3 s4 s5 s6)))
	 (equal (word (+ sum1 sum2))
		(word (* m1 m2)))))))

; Using the result of this file, we can prove something like: 
;(defthm ML-output-correct
;    (implies (and (word-p ra) (word-p rb))
;	     (equal (ML3-output (ML2-output (ML1-output ra rb)))
;		    (word (* ra rb)))))

;(defthm ML3-output-correct
;    (word-p (ML3-output data)))
