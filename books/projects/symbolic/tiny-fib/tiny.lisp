#|

This file contains an interpreter for the "tiny" machine, an
experimental machine loosely based on Boyer's and Moore's small
machine, as described in "High-Speed Analyzable Simulators", Chapter 8
of the book "Computer-Aided Reasoning: ACL2 Case Studies".  We also
include a small benchmark program that calculates the remainder of two
integers.  This file is the latest in a series of experiments to build
a toy interpreter that can be analyzed and run fast using many
different methods of constructing fast interpreters.

Several of the changes made in Fall 1999 to reflect improvements in
ACL2, or highlight something in the chapter.  In particular, we

  - Added symbolic field names.

  - Updated the model to use STOBJ.  (STOBJ names were also
subsequently changed to comply with the name changes in the draft and
released versions of ACL2 2.4.)

  - Changed the definition of 32-bit add in order to avoid compiler
replacements altogether, as described in the chapter.

Dave Greve and Matt Wilding

September 1999
(updated January 2000)

Updates by David Hardin on 2004-04-01 (ha ha)

  - Re-enabled nu-rewriter; it's stable now.

  - Got rid of most of the linear arithmetic "hacks"; ACL2's
    linear arithmetic processing is now much improved.

  - Deleted other unused rules, redundant hypotheses, etc.  Not a
    complete job by any means, but tiny now has 10% fewer lines, which
    seemed a decent enough "spring cleaning".

  - Eliminated macros that provided symbolic names for fields;
    defstobj now generates these automatically (e.g., *baz* for field baz).

  - Corrected comment on how to run the example outside of the ACL2
    read-eval-print loop (a stobj named foo is now accessed as *the-live-foo*).

  - Used the new (as of ACL2 2.8) include-book :dir :system keywords
    to make the file more portable.
|#

(in-package "ACL2")
(include-book "defstobj+")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(include-book "data-structures/list-defthms" :dir :system)
;(include-book "meta/meta" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system)

(disable-theory (theory 'logops-functions))

(set-verify-guards-eagerness 2)

(defstobj+ tiny-state
  (progc :type (unsigned-byte 10) :initially 0)
  (mem :type (array (signed-byte 32) (1024)) :initially 0)
  (dtos :type (unsigned-byte 10) :initially 0)
  (ctos :type (unsigned-byte 10) :initially 0)
  :inline t)

;; Some proof speedup lemmas
;; Changed after Version 6.1 by Matt Kaufmann to replace obsolete the-error by
;; the-check.
;; Removed 11/2021 by Matt Kaufmann with the addition of the-check to
;; guard-holcers.
;(defthm the-check-noop
;  (equal (the-check g x y) y))

(defthm nth-update-nth-const
  (implies
   (and
    (syntaxp (quotep n1))
    (syntaxp (quotep n2)))
   (equal (nth n1 (update-nth n2 v l))
	  (if (equal (nfix n1) (nfix n2)) v (nth n1 l))))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; Removed disabling of 11/2021 by Matt Kaufmann with the addition of the-check
;; to guard-holcers.
;(in-theory (disable the-check nth update-nth))
(in-theory (disable nth update-nth))

;; Some macros for convenient expression of declarations
(defmacro Int32 (x) `(the   (signed-byte 32) ,x))
(defmacro Nat10 (x) `(the (unsigned-byte 10) ,x))
(defmacro MAX_INT<32>   ()  2147483647)
(defmacro MIN_INT<32>   () -2147483648)
(defmacro MIN_INT<32>+1   () -2147483647)
(defmacro MAX_NAT<10>   ()  1023)
(defmacro MAX_NAT-1<10> ()  1022)

(defmacro fix|10| (x)
  `(Nat10 (logand (MAX_NAT<10>) ,x)))

(defmacro max<32> (x y)
  `(Int32 (max ,x ,y)))

(defmacro +<32> (x y)
  `(Int32 (+ ,x ,y)))

;; We introduce a speedy add function for 32-bit quantities, then a
;; not-so-speedy 32-bit add function that uses IHS library function
;; about which much has been previously proved.  We show their
;; equivalence to make use of the proofs in the IHS library.

;; The plus<32> guard proof requires 3 minutes on an Ultra 10, a long
;; time for a little theorem.

(defun plus<32> (a b)
  (declare (type (signed-byte 32) a)
	   (type (signed-byte 32) b)
           ;; Added by Matt K. for v2-7:
           (xargs :guard-hints (("Goal" :in-theory (enable signed-byte-p)))))
  (Int32
   (if (< a 0)
       (if (>= b 0) (+<32> a b)
	 (let ((psum (+<32> (+<32> (+<32> a (MAX_INT<32>)) 1) b)))
	   (declare (type (signed-byte 32) psum))
	   (if (< psum 0)
	       (+<32> (+<32> (MAX_INT<32>) psum) 1)
	     (+<32> psum (MIN_INT<32>)))))
     (if (< b 0) (+<32> a b)
       (let ((psum (+<32> (+<32> a (MIN_INT<32>)) b)))
	 (declare (type (signed-byte 32) psum))
	 (if (>= psum 0)
	     (+<32> (MIN_INT<32>) psum)
	   (+<32> (+<32> psum (MAX_INT<32>)) 1)))))))

(defun +bv32 (x y)
   (declare (type (signed-byte 32) x y))
   (logext 32 (+ x y)))

(defthm plus<32>-works
  (implies
   (and
    (signed-byte-p 32 a)
    (signed-byte-p 32 b))
  (equal
   (plus<32> a b)
   (+bv32 a b)))
  :hints (("goal" :use ((:instance logext-+-logext (size 32) (i (+ a b)) (j (- (expt 2 32))))
			(:instance logext-+-logext (size 32) (i (+ a b)) (j (expt 2 32))))
	   :in-theory (set-difference-theories (enable signed-byte-p) '(logext-+-logext)))))

(defthm integerp-means-rationalp
  (implies (integerp x) (rationalp x))
  :rule-classes nil)

(defthm integerp-plus
  (implies
   (and (integerp a) (integerp b))
   (integerp (+ a b)))
  :rule-classes nil)

;; Handy facts about 32-bit addition
(defthm +bv32-representable-as-32-bits
  (and
   (integerp (+bv32 a b))
   (< (+bv32 a b) 2147483648) ; modified by Matt K. for v2-7
   (>= (+bv32 a b) -2147483648))
  :hints (("goal"
	   :in-theory (set-difference-theories (enable signed-byte-p) '(signed-byte-p-logext))
	   :use
	   ((:instance integerp-means-rationalp
		       (x (+bv32 a b)))
	    (:instance signed-byte-p-logext (size 32) (size1 32) (i (+ a b)))
	    (:instance integerp-plus
		       (a (LOGAND A 4294967295))
		       (b (LOGAND B 4294967295)))))))

(in-theory (disable plus<32> +bv32))
(in-theory (enable signed-byte-p))

;; Macros for convenient arithmetic
(defmacro +|10| (x y)
  `(Nat10 (logand (+<32> ,x ,y) (MAX_NAT<10>))))

(defmacro add<32> (x y)
  `(Int32 (plus<32> ,x ,y)))

(defmacro negate_32 (x)
  `(let ((x ,x))
     (declare (type (signed-byte 32) x))
     (Int32 (if (= x (MIN_INT<32>)) (MIN_INT<32>) (Int32 (- x))))))

(defun sub<32> (x y)
  (declare (type (signed-byte 32) x)
	   (type (signed-byte 32) y))
  (add<32> x (negate_32 y)))


(defthm integerp--
  (implies
   (integerp x)
   (integerp (- x))))

; Modified for Version 2.6 and further for v2-7 by Matt Kaufmann:
(defthm update-nth-memp
  (implies
   (and
    (memp mem)
    (< n (len mem))
    (integerp n)
    (>= n 0))
   (equal (memp (update-nth n val mem))
	  (and
	   (<= (- (expt 2 31)) val)
	   (< val (expt 2 31)) ; modified by Matt K. for v2-7
	   (integerp val))))
  :hints (("goal" :in-theory (enable update-nth))))

; Modified by Matt Kaufmann for ACL2 Version 2.6.
(defthm arb-memory-proof
  (implies
   (and
    (memp mem)
    (< n2 (len mem))
    (<= 0 n2))
   (and
    (<= (nth n2 mem) (MAX_INT<32>))
    (<= (MIN_INT<32>) (nth n2 mem))
    (integerp (nth n2 mem))))
  :hints (("goal" :in-theory (enable nth)))
  :rule-classes nil)

;; an element of memory is a 32-bit quantity.  Really.
; Modified by Matt Kaufmann for ACL2 Version 2.6.
(defthm arb-memory
  (implies
   (and
    (memp mem)
    (< n2 (len mem))
    (<= 0 n2))
   (and
    (<= (nth n2 mem) (MAX_INT<32>))
    (< (nth n2 mem) 2147483648)
    (not (< 2147483648 (NTH n2 mem))) ; needed later on.
    (<= (MIN_INT<32>) (nth n2 mem))
    (implies (not (equal (min_int<32>) (nth n2 mem)))
	     (< (MIN_INT<32>) (nth n2 mem)))
    (integerp (nth n2 mem))
    (rationalp (nth n2 mem))
    (acl2-numberp (nth n2 mem))))
  :hints (("goal" :use arb-memory-proof)))

; Always move the negation to the constant
(defthm less-neg-const
  (implies
   (syntaxp (quotep y))
   (and
    (iff (< (- x) y) (> x (- y)))
    (iff (< y (- x)) (> (- y) x))
    (iff (<= (- x) y) (>= x (- y)))
    (iff (<= y (- x)) (>= (- y) x))))
  :rule-classes ((:rewrite :loop-stopper nil)))

; Added by Matt K. for v2-7 to help with some guard proofs.
(in-theory (enable unsigned-byte-p))

;; Push a value onto the user stack.
(defun pushus (val tiny-state)
  (declare (type (signed-byte 32) val)
	   (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)))
  (let ((dtos (dtos tiny-state)))
    (declare (type (unsigned-byte 10) dtos))
    (let ((tiny-state (update-memi dtos (Int32 val) tiny-state)))
      (update-dtos (+|10| dtos -1) tiny-state))))

;; Pop a value off the user stack.
(defun popus (address tiny-state)
  (declare (type (unsigned-byte 10) address)
	   (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)))
  (let ((ndtos (+|10| (dtos tiny-state) 1)))
    (declare (type (unsigned-byte 10) ndtos))
    (let ((tiny-state (update-memi address (memi ndtos tiny-state) tiny-state)))
      (update-dtos ndtos tiny-state))))

;; Push a value on the call stack.
(defun pushcs (val tiny-state)
  (declare (type (signed-byte 32) val)
	   (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)))
  (let ((ctos (ctos tiny-state)))
    (declare (type (unsigned-byte 10) ctos))
    (let ((tiny-state (update-memi ctos (Int32 val) tiny-state)))
     (update-ctos (+|10| ctos -1) tiny-state))))

;; Pop a value off the call stack
(defun popcs (address tiny-state)
  (declare (type (unsigned-byte 10) address)
	   (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)))
  (let ((nctos (+|10| (ctos tiny-state) 1)))
    (declare (type (unsigned-byte 10) nctos))
    (let ((tiny-state (update-memi address (memi nctos tiny-state) tiny-state)))
      (update-dtos nctos tiny-state))))

;; Define the TINY instructions by defining the effect of executing
;; the current instruction.
(defun next (tiny-state)
  (declare (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)
		  :guard-hints (("goal" :in-theory
				 (disable hard-error pushus popus pushcs)))))
  (let ((progc (progc tiny-state))
	(dtos  (dtos tiny-state))
	(ctos  (ctos tiny-state)))
    (declare (type (unsigned-byte 10) progc dtos ctos))

    (let ((ins (memi progc tiny-state)))
      (declare (type (signed-byte 32) ins))

      (case ins
	; pop
	(0 (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
	    (popus (fix|10| (memi (+|10| progc 1) tiny-state)) tiny-state)))

	; pushs
	(1 (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
	    (pushus (memi (fix|10| (memi (+|10| progc 1) tiny-state)) tiny-state) tiny-state)))

	; pushsi
	(2 (let ((tiny-state (update-progc (+|10| progc 2) tiny-state)))
	    (pushus (memi (+|10| progc 1) tiny-state) tiny-state)))

	; add
	(3 (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
	     (let ((tiny-state (update-dtos (+|10| dtos 2) tiny-state)))
	       (pushus (add<32> (Int32 (memi (+|10| dtos 1) tiny-state))
				(Int32 (memi (+|10| dtos 2) tiny-state)))
		       tiny-state))))

	; jump
	(4 (update-progc (fix|10| (memi (+|10| progc 1) tiny-state)) tiny-state))

	; jumpz
	(5 (let ((nprogc (if (= (memi (+|10| dtos 1) tiny-state) 0)
			     (fix|10| (memi (+|10| progc 1) tiny-state))
			   (+|10| progc 2))))
	     (declare (type (unsigned-byte 10) nprogc))
	     (let ((tiny-state (update-progc nprogc tiny-state)))
	       (update-dtos (+|10| dtos 1) tiny-state))))

	; call
	(6 (let ((nadd (fix|10| (memi (+|10| progc 1) tiny-state))))
	     (declare (type (unsigned-byte 10) nadd))
	     (let ((tiny-state (update-progc nadd tiny-state)))
	      (pushcs (+|10| progc 2) tiny-state))))

	; return
	(7 (let ((nadd (fix|10| (memi (+|10| ctos 1) tiny-state))))
	     (declare (type (unsigned-byte 10) nadd))
	     (let ((tiny-state (update-progc nadd tiny-state)))
	      (update-ctos (+|10| ctos 1) tiny-state))))

	; sub
	(8 (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
	     (let ((tiny-state (update-dtos (+|10| dtos 2) tiny-state)))
	       (pushus (max<32> 0 (sub<32> (memi (+|10| dtos 2) tiny-state)
					   (memi (+|10| dtos 1) tiny-state)))
		       tiny-state))))

	; dup
	(9 (let ((tiny-state (update-progc (+|10| progc 1) tiny-state)))
	    (pushus (memi (+|10| dtos 1) tiny-state) tiny-state)))

	; halt
	(otherwise tiny-state)))))

(defthm tiny-statep-next
  (implies
   (tiny-statep tiny-state)
   (tiny-statep (next tiny-state))))

(defun tiny (tiny-state n)
  (declare (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)
		  :guard-hints (("goal" :in-theory (disable next tiny-statep))))
	   (type (signed-byte 32) n))
  (if (or (not (integerp (Int32 n))) (<= (Int32 n) (Int32 0)))   ; ifix inefficient
      tiny-state
    (let ((tiny-state (next tiny-state)))
      (tiny tiny-state (Int32 (1- (Int32 n)))))))


;;;;;
;; Functions for creating Tiny state

;; Note: recursive functions involving s.t. objects must have a base
;; case listed first.  Presumably ACL2 has this restriction in order
;; to allow ACL2 a simpler approach for determining whether a function
;; returns all the s.t. objects it needs to return, since every base
;; case must return every potentially-modified s.t. object.

(defun load-memory-block (address list tiny-state)
  (declare (xargs :stobjs (tiny-state)
		  :guard (tiny-statep tiny-state)
		  :verify-guards nil))
  (if (not (consp list)) tiny-state
      (let ((tiny-state (update-memi address (car list) tiny-state)))
	(load-memory-block (+|10| address 1) (cdr list) tiny-state))))

(defun load-memory (assoc tiny-state)
  (declare (xargs :stobjs (tiny-state)
		  :verify-guards nil))
  (if (not (consp assoc)) tiny-state
    (let ((tiny-state (load-memory-block (caar assoc) (cdar assoc) tiny-state)))
      (load-memory (cdr assoc) tiny-state))))

(defun load-tiny (pc memlist tiny-state)
  (declare (xargs :stobjs (tiny-state)
		  :verify-guards nil))
  (let ((tiny-state (update-progc pc tiny-state)))
    (let ((tiny-state (update-dtos 900 tiny-state)))
      (let ((tiny-state (update-ctos 1000 tiny-state)))
	(load-memory memlist tiny-state)))))

(defun encode (op)
  (declare (xargs :verify-guards nil))
  (case op
    ('pop 0)
    ('pushs 1)
    ('pushsi 2)
    ('add 3)
    ('jump 4)
    ('jumpz 5)
    ('call 6)
    ('ret 7)
    ('sub 8)
    ('dup 9)
    ('halt 10)))

(defun assemble (code)
  (declare (xargs :verify-guards nil))
  (if (consp code)
      (cons
       (if (integerp (car code)) (car code) (encode (car code)))
       (assemble (cdr code)))
    nil))

(defconst *mod-caller-prog* (assemble '(pushsi 0 pushsi 1 add pushsi 100 call 20 jump 6)))

(defconst *mod-prog* (assemble '(pop 19   ;20
				 pop 18
				 pushs 18 ;24
				 pushs 19
				 sub
				 dup
				 jumpz 36
				 pop 18
				 jump 24
				 pushs 19 ;36
				 pushs 18
				 sub
				 jumpz 45
                                 jump 49
				 pushsi 0 ;45
				 pop 18
				 pop 19   ;49
				 pushs 18
				 ret
				 )))

(defun run-example-tiny-state (n tiny-state)
  (declare (xargs :verify-guards nil :stobjs (tiny-state)))
  (let ((tiny-state (load-tiny 4 (list (cons 4 *mod-caller-prog*) (cons 20 *mod-prog*)) tiny-state)))
    (tiny tiny-state n)))

#|
ACL2 !>:q

Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
ACL2>(time (run-example-tiny-state 10000000 *the-live-tiny-state*))
real time : 12.000 secs
run time  : 12.010 secs
(#(9)
 #(0 0 0 0 2 0 2 1 3 2 100 6 20 4 6 0 0 0 50 0 0 19 0 18 1 18 1 19 8 9
   5 36 0 18 4 24 1 19 1 18 8 5 45 4 49 2 0 0 18 0 19 1 18 7 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 50 1 51 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0)
 #(899) #(1000))

ACL2>

|#

;;;;;
;;;;;  Proof about the benchmark program
;;;;;

;;; The proof begins with many preliminaries that help us reason about
;;; programs of this type.

;;; We are not interested in guard-proofs about functions we
;;; use for specification and proof
;(set-verify-guards-eagerness 0)

;; Is "program" loaded at "location" in Tiny state?
(defun program-loaded (tiny-state program location)
  (declare (xargs :stobjs (tiny-state)
		  :guard (and (integerp location)
			      (<= 0 location)
			      (< location (- 1024 (len program)))
			      (true-listp program))))
  (or (endp program)
      (and (equal (memi location tiny-state) (car program))
	   (program-loaded tiny-state (cdr program) (1+ location)))))

(set-verify-guards-eagerness 0)

(defthm prog-lookup
  (implies (and (syntaxp (quotep n))
		(program-loaded tiny-state prog loc)
		(integerp loc)
		(<= loc (nfix n))
		(< (nfix n) (+ loc (len prog))))
	   (equal (nth n (nth *memi* tiny-state))
		  (nth (- n loc) prog)))
  :hints (("goal" :in-theory (enable len nth))))

(in-theory (disable program-loaded))

(defthm +bv32-simple
  (implies
   (and
    (integerp x) (integerp y)
    (< x (expt 2 30)) ; modified by Matt K. for v2-7
    (>= x (- (expt 2 30)))
    (< y (expt 2 30)) ; modified by Matt K. for v2-7
    (>= y (- (expt 2 30))))
   (equal (+bv32 x y) (+ x y)))
  :hints (("goal" :in-theory (enable +bv32 signed-byte-p))))

(defthm +bv32-simple2
  (implies
   (and
    (integerp x) (integerp y)
    (< x (expt 2 31)) ; modified by Matt K. for v2-7
    (>= x 0)
    (< y (expt 2 31)) ; modified by Matt K. for v2-7
    (>= y 0))
   (equal (+bv32 x (- y)) (+ x (- y))))
  :hints (("goal" :in-theory (enable +bv32 signed-byte-p))))

(defthm +bv32-0
  (implies
   (and
    (integerp x)
    (< x (expt 2 31)) ; modified by Matt K. for v2-7
    (<= (- (expt 2 31)) x))
   (equal (+bv32 x 0) x))
  :hints (("goal" :in-theory  (enable +bv32 signed-byte-p))))

(defthm tiny-straightline
  (implies
   (syntaxp (quotep n))
   (equal (tiny tiny-state n)
	  (if (zp n) tiny-state (tiny (next tiny-state) (1- n)))))
  :hints (("goal" :in-theory (disable next))))

(defun c+ (x y) (+ (nfix x) (nfix y)))

(defthm tiny-c+
  (equal (tiny s (c+ x y))
	 (tiny (tiny s x) y))
  :hints (("goal" :induct (tiny s x)
	   :in-theory (set-difference-theories (enable tiny) '(next)))))

(in-theory (disable c+))

(defthm integerp-max
  (implies
   (and (integerp a) (integerp b))
   (integerp (max a b))))

(defthm max-less
  (and
   (equal
    (< (max a b) c)
    (and (< a c) (< b c)))
   (equal
    (< c (max a b))
    (or (< c a) (< c b)))))

(defthm equal-max-x-x
  (implies
   (and (integerp b) (integerp a))
  (and
   (equal (equal (max a b) a) (<= b a))
   (equal (equal (max b a) a) (<= b a))))
  :hints (("goal" :in-theory (enable max))))

(in-theory (disable max))

(defthm equal-plus-x-x
  (implies
   (and (integerp b) (integerp a))
   (equal (equal (+ a b) b) (equal a 0))))

(defthm integerp-unary--
  (implies
   (integerp x)
   (integerp (unary-- x))))

(defthm integerp-+
  (implies
   (and
    (integerp x)
    (integerp y))
   (integerp (+ x y))))

(in-theory (disable tiny))

(defthm lessp-minus-hack4
 (implies
  (and
   (<= a n)
   (<= b n)
   (<= 0 b)
   (integerp a)
   (integerp b)
   (integerp n))
  (<= (+ a (- b)) n)))


(defthm max-0-a-b
  (and
   (implies (<= a b) (equal (max 0 (+ a (- b))) 0))
   (implies (>= a b) (equal (max 0 (+ a (- b))) (+ a (- b)))))
  :hints (("goal" :in-theory (enable max))))

(defthm max-open
  (implies
   (and
    (<= a b)
    (integerp a) (integerp b))
   (equal (max a b) b)))

;; Try to backchain on nth-update-nth before casesplitting
(defthm nth-update-nth2
   (equal
    (nth n1 (update-nth n2 v l))
    (if (equal (nfix n1) (nfix n2))
	v
      (nth n1 l)))
  :hints (("goal" :in-theory (enable update-nth nth))))

(defthm nth-update-nth-1
  (implies
    (not (equal (nfix n1) (nfix n2)))
   (equal
    (nth n1 (update-nth n2 v l))
    (nth n1 l))))

(defthm nth-update-nth-2
  (implies
    (equal (nfix n1) (nfix n2))
   (equal
    (nth n1 (update-nth n2 v l))
    v)))

(defun repeat (n v)
  (if (zp n)
      nil
    (cons v (repeat (1- n) v))))

(defthm update-nth-nil
  (equal (update-nth i v nil)
	 (append (repeat i nil) (list v)))
  :hints (("goal" :in-theory (enable update-nth))))

(defthm update-nth-nth-noop-helper
  (implies
   (and (<= 0 n) (< n (len l)))
   (equal (update-nth n (nth n l) l) l))
  :hints (("goal" :in-theory (enable nth update-nth))))

(defthm update-nth-nth-noop
  (implies
   (and (<= 0 n) (< n (len l1)) (equal (nth n l1) (nth n l2)))
   (equal (update-nth n (nth n l2) l1) l1)))

;; order update-nth terms based on update field value
(defthm update-nth-update-nth-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth i1 v1 (update-nth i2 v2 l))
	  (update-nth i2 v2 (update-nth i1 v1 l))))
  :hints (("goal" :in-theory (enable update-nth)))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2)))))

(defthm update-nth-update-nth-same
  (equal (update-nth i v1 (update-nth i v2 l))
	 (update-nth i v1 l))
  :hints (("goal" :in-theory (enable update-nth))))

(defthm len-repeat
  (equal (len (repeat i v)) (nfix i)))

(defthm len-update-nth-better
  (equal (len (update-nth i v l)) (max (1+ (nfix i)) (len l)))
  :hints (("goal" :in-theory (enable update-nth max))))

(defthm car-update-nth
  (equal (car (update-nth i v l)) (if (zp i) v (car l)))
  :hints (("goal" :in-theory (enable update-nth))))

(defthm len-pushus
  (implies
   (equal (len tiny-state) 4)
   (equal (len (pushus val tiny-state)) 4))
  :hints (("goal" :in-theory (disable logand-with-mask))))

(defthm car-append
  (equal (car (append x y))
	 (if (consp x) (car x) (car y))))

(defthm cdr-append
  (equal (cdr (append x y))
	 (if (consp x) (append (cdr x) y) (cdr y))))

(defthm equal-plus-0
  (implies
   (and (integerp a) (integerp b) (<= 0 a) (<= 0 b))
   (equal (equal 0 (+ a b)) (and (equal a 0) (equal b 0)))))

(defthm equal-nat-neg-0
  (implies
   (and
   (integerp n1)
   (integerp n2)
   (<= 0 n1)
   (<= 0 n2))
   (and
    (equal (equal (+ n1 (- n2)) 0) (equal n1 n2))
    (equal (equal (+ (- n2) n1) 0) (equal n1 n2)))))

(defthm car-nthcdr
  (equal (car (nthcdr n l)) (nth n l))
  :hints (("goal" :in-theory (enable nth))))

(in-theory (disable next logand floor len update-nth max))

(in-theory (enable +bv32))

;; We start proving facts about the benchmark

;; Effect of running loop once (taken from theorem prover output)
(defun mod-loop-once-effect (tiny-state)
  (update-nth *progc* 24
	   (update-nth *memi*
		    (update-nth 18
			     (+ (nth 18 (nth *memi* tiny-state))
				(- (nth 19 (nth *memi* tiny-state))))
			     (update-nth (nth *dtos* tiny-state)
				      (+ (nth 18 (nth *memi* tiny-state))
					 (- (nth 19 (nth *memi* tiny-state))))
				      (update-nth (+ -1 (nth *dtos* tiny-state))
					       (+ (nth 18 (nth *memi* tiny-state))
						  (- (nth 19 (nth *memi* tiny-state))))
					       (nth *memi* tiny-state))))
		    (update-nth *dtos* (nth *dtos* tiny-state) tiny-state))))

(in-theory (disable update-nth-update-nth))
(in-theory (enable len))

(defthm mod-loop-repeat
  (implies
   (and
    (tiny-statep tiny-state)
    (< (dtos tiny-state) 1000) (>= (dtos tiny-state) 100)
    (equal (progc tiny-state) 24)
    (program-loaded tiny-state *mod-prog* 20)
    (<= 0 (memi 19 tiny-state))
    (<= 0 (memi 18 tiny-state))
    (< (memi 19 tiny-state) (memi 18 tiny-state))
    (not (= (memi 19 tiny-state) (memi 18 tiny-state)))) ;;redundant, but simplifies proof
   (equal (tiny tiny-state 7)
	  (mod-loop-once-effect tiny-state)))
  :hints (("goal''" :in-theory (enable next signed-byte-p len))))

;; Effect of loop when it ends with no adjust needed (expression taken
;;from theorem prover output)
(defthm mod-loop-end1
  (implies
   (and
    (tiny-statep tiny-state)
    (< (dtos tiny-state) 1000) (>= (dtos tiny-state) 100)
    (<= (ctos tiny-state) 1020) (> (ctos tiny-state) 1010)
    (equal (progc tiny-state) 24)
    (program-loaded tiny-state *mod-prog* 20)
    (<= 0 (memi 19 tiny-state))
    (< 0 (memi 18 tiny-state))
    (> (memi 19 tiny-state) (memi 18 tiny-state))
    (not (= (memi 19 tiny-state) (memi 18 tiny-state)))) ;;redundant
   (equal (tiny tiny-state 13)
	  (update-nth *progc*
             (logand (nth (+ 1 (nth *ctos* tiny-state)) (nth *memi* tiny-state))
                     1023)
             (update-nth *memi*
                      (update-nth 19 0
                               (update-nth (nth *dtos* tiny-state)
                                        (nth 18 (nth *memi* tiny-state))
                                        (update-nth (+ -1 (nth *dtos* tiny-state))
                                                 (+ (- (nth 18 (nth *memi* tiny-state)))
                                                    (nth 19 (nth *memi* tiny-state)))
                                                 (update-nth (+ -2 (nth *dtos* tiny-state))
                                                          (nth 18 (nth *memi* tiny-state))
                                                          (nth *memi* tiny-state)))))
                      (update-nth *dtos* (+ -1 (nth *dtos* tiny-state))
                               (update-nth *ctos* (+ 1 (nth *ctos* tiny-state)) tiny-state))))))
  :hints (("goal''" :in-theory (enable next signed-byte-p))))

;; Effect of loop when it ends with an adjust needed (expression taken
;;from theorem prover output)
(defthm mod-loop-end2
  (implies
   (and
    (tiny-statep tiny-state)
    (< (dtos tiny-state) 1000) (>= (dtos tiny-state) 100)
    (<= (ctos tiny-state) 1020) (> (ctos tiny-state) 1010)
    (equal (progc tiny-state) 24)
    (program-loaded tiny-state *mod-prog* 20)
    (<= 0 (memi 19 tiny-state))
    (< 0 (memi 18 tiny-state))
    (= (memi 19 tiny-state) (memi 18 tiny-state)))
   (equal (tiny tiny-state 14)
	  (update-nth
	   *progc*
	   (logand (nth (+ 1 (nth *ctos* tiny-state)) (nth *memi* tiny-state))
		   1023)
	   (update-nth *memi*
		    (update-nth 18 0
			     (update-nth 19 0
				      (update-nth (nth *dtos* tiny-state)
					       0
					       (update-nth (+ -1 (nth *dtos* tiny-state))
							0
							(update-nth (+ -2 (nth *dtos* tiny-state))
								 (nth 18 (nth *memi* tiny-state))
								 (nth *memi* tiny-state))))))
		    (update-nth *dtos* (+ -1 (nth *dtos* tiny-state))
			     (update-nth *ctos* (+ 1 (nth *ctos* tiny-state)) tiny-state))))))
  :hints (("goal''" :in-theory (enable next signed-byte-p))))

;; number of instructions needed to execute loop for values x and y.
(defun modloop-clock-helper (x y)
  (if (or (not (integerp x)) (not (integerp y)) (>= 0 y) (<= x y))
      (if (equal x y) 14 13)
    (c+ 7 (modloop-clock-helper (- x y) y))))

(defun modloop-clock (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (let ((x (memi 18 tiny-state)) (y (memi 19 tiny-state)))
    (modloop-clock-helper x y)))

(defun remainder-prog-result (n p)
  (if (or (zp p) (zp n) (< n p))
      (nfix n)
    (remainder-prog-result (- n p) p)))

(set-irrelevant-formals-ok :warn)

(defun mod-loop-repeat-induct (x y s)
  (if (or (not (integerp x)) (not (integerp y)) (>= 0 y) (<= x y))
      t
    (mod-loop-repeat-induct (- x y) y (mod-loop-once-effect s))))

; Modified by Matt Kaufmann for ACL2 Version 2.6.
(defthm memp-update-nth
  (implies
   (and
    (memp l)
    (integerp a)
    (<= 0 a)
    (< a (len l)))
   (equal (memp (update-nth a v l))
	  (AND (INTEGERP v) (<= -2147483648 v) (<= v 2147483647))))
  :hints (("goal" :in-theory (enable update-nth))))

(in-theory (enable max))

(defun sub1-add1-cdr (n1 n2 l)
  (if (consp l)
      (sub1-add1-cdr (1- n1) (1+ n2) (cdr l))
    t))

(defthm update-nth-equal
  (implies
   (and
    (< n (len l))
    (<= 0 n) (integerp n))
   (equal (update-nth n (nth n l) l) l))
  :hints (("goal" :in-theory (enable nth update-nth len))))

(defthm program-loaded-irrelevant
  (implies
   (not (equal n 1))
   (equal (program-loaded (update-nth n v tiny-state) prog loc)
	  (program-loaded tiny-state prog loc)))
  :hints (("goal" :in-theory (enable update-nth program-loaded))))


;; such a screwy rule.  It's inelegant because program-loaded is a function
;; of state.
(defthm program-loaded-cons
  (implies
   (and
    (or (< n loc) (< (+ (len prog) loc) n) (equal val (nth n mem)))
    (integerp n) (<= 0 n) (integerp loc) (<= 0 loc)
    (program-loaded (update-nth 1 mem tiny-state) prog loc))
   (program-loaded (update-nth 1 (update-nth n val mem) tiny-state) prog loc))
  :hints (("goal" :in-theory (enable program-loaded update-nth nth len))))

(defthm mod-loop-calculates-mod
  (implies
   (and
    (tiny-statep tiny-state)
    (< (dtos tiny-state) 1000) (>= (dtos tiny-state) 100)
    (<= (ctos tiny-state) 1020) (> (ctos tiny-state) 1010)
    (equal (progc tiny-state) 24)
    (program-loaded tiny-state *mod-prog* 20)
    (equal a (memi 18 tiny-state))
    (equal b (memi 19 tiny-state))
    (< 0 a) (< 0 b)
    (equal s2 (tiny tiny-state (modloop-clock-helper a b))))
   (equal (memi (1+ (dtos s2)) s2) (remainder-prog-result a b)))
  :rule-classes nil
  :hints (("goal" :in-theory (set-difference-theories
			      (enable tiny-statep len)
			      '(tiny-straightline))
			      :induct (mod-loop-repeat-induct a b tiny-state))
	  ("Subgoal *1/1.1'" :expand (REMAINDER-PROG-RESULT (NTH 18 (NTH 1 TINY-STATE))
                       (NTH 19 (NTH 1 TINY-STATE))))))

(defun remclock (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (modloop-clock-helper (memi 18 tiny-state) (memi 19 tiny-state)))

(defun good-initial-remainder-state (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
   (and
    (tiny-statep tiny-state)
    (< (dtos tiny-state) 1000) (>= (dtos tiny-state) 100)
    (<= (ctos tiny-state) 1020) (> (ctos tiny-state) 1010)
    (equal (progc tiny-state) 24)
    (program-loaded tiny-state *mod-prog* 20)
    (< 0 (memi 18 tiny-state))
    (< 0 (memi 19 tiny-state))))

(defthm remainder-correct
  (let ((s2 (tiny tiny-state (remclock tiny-state))))
  (implies
    (good-initial-remainder-state tiny-state)
    (equal (memi (1+ (dtos s2)) s2)
           (remainder-prog-result (memi 18 tiny-state) (memi 19 tiny-state)))))
  :rule-classes nil
  :hints (("goal"
	   :use ((:instance mod-loop-calculates-mod
			    (s2 (tiny tiny-state (modloop-clock-helper (memi 18 tiny-state) (memi 19 tiny-state))))
			    (a (memi 18 tiny-state))
			    (b (memi 19 tiny-state))))
	   :in-theory (disable tiny-straightline))))

;;; Show that our recursive version of remainder is identical to mod.
;;; Fortunately, Bishop Brock's been here before.

(include-book "ihs/quotient-remainder-lemmas" :dir :system)

(defthm remainder-is-mod
  (implies
   (and
    (integerp x)
    (<= 0 x)
    (integerp y)
    (<= 0 y))
   (equal (remainder-prog-result x y) (mod x y))))

(defthm mod-correct
  (let ((s2 (tiny tiny-state (remclock tiny-state))))
  (implies
    (good-initial-remainder-state tiny-state)
    (equal (memi (1+ (dtos s2)) s2)
           (mod (memi 18 tiny-state) (memi 19 tiny-state)))))
  :rule-classes nil
  :hints (("goal" :use ((:instance remainder-correct)))))

