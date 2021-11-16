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

|#

(in-package "ACL2")
(include-book "../../../arithmetic/top")
(include-book "../../../data-structures/list-defthms")
(include-book "../../../meta/meta")
(include-book "../../../ihs/logops-lemmas")

(disable-theory (theory 'logops-functions))

(set-verify-guards-eagerness 2)

(defstobj st
          (progc :type (unsigned-byte 10) :initially 0)
	  (mem :type (array (signed-byte 32) (1024)) :initially 0)
	  (dtos :type (unsigned-byte 10) :initially 0)
	  (ctos :type (unsigned-byte 10) :initially 0))

;; We define symbolic names for the location of the stobj fields for
;; use in theorems.

(defmacro progcloc () 0)
(defmacro memloc ()   1)
(defmacro dtosloc ()  2)
(defmacro ctosloc ()  3)

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

;; The plus<32> guard proof require 3 minutes on an Ultra 10, a long
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
   (rationalp (+bv32 a b))
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


(defthm integerp-minus
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
(defun pushus (val st)
  (declare (type (signed-byte 32) val)
	   (xargs :stobjs (st)
		  :guard (stp st)))
  (let ((dtos (dtos st)))
    (declare (type (unsigned-byte 10) dtos))
    (let ((st (update-memi dtos (Int32 val) st)))
      (update-dtos (+|10| dtos -1) st))))

;; Pop a value off the user stack.
(defun popus (address st)
  (declare (type (unsigned-byte 10) address)
	   (xargs :stobjs (st)
		  :guard (stp st)))
  (let ((ndtos (+|10| (dtos st) 1)))
    (declare (type (unsigned-byte 10) ndtos))
    (let ((st (update-memi address (memi ndtos st) st)))
      (update-dtos ndtos st))))

;; Push a value on the call stack.
(defun pushcs (val st)
  (declare (type (signed-byte 32) val)
	   (xargs :stobjs (st)
		  :guard (stp st)))
  (let ((ctos (ctos st)))
    (declare (type (unsigned-byte 10) ctos))
    (let ((st (update-memi ctos (Int32 val) st)))
     (update-ctos (+|10| ctos -1) st))))

;; Pop a value off the call stack
(defun popcs (address st)
  (declare (type (unsigned-byte 10) address)
	   (xargs :stobjs (st)
		  :guard (stp st)))
  (let ((nctos (+|10| (ctos st) 1)))
    (declare (type (unsigned-byte 10) nctos))
    (let ((st (update-memi address (memi nctos st) st)))
      (update-dtos nctos st))))

;; Define the TINY instructions by defining the effect of executing
;; the current instruction.
(defun next (st)
  (declare (xargs :stobjs (st)
		  :guard (stp st)
		  :guard-hints (("goal" :in-theory
				 (disable hard-error pushus popus pushcs)))))
  (let ((progc (progc st))
	(dtos  (dtos st))
	(ctos  (ctos st)))
    (declare (type (unsigned-byte 10) progc dtos ctos))

    (let ((ins (memi progc st)))
      (declare (type (signed-byte 32) ins))

      (case ins
	; pop
	(0 (let ((st (update-progc (+|10| progc 2) st)))
	    (popus (fix|10| (memi (+|10| progc 1) st)) st)))

	; pushs
	(1 (let ((st (update-progc (+|10| progc 2) st)))
	    (pushus (memi (fix|10| (memi (+|10| progc 1) st)) st) st)))

	; pushsi
	(2 (let ((st (update-progc (+|10| progc 2) st)))
	    (pushus (memi (+|10| progc 1) st) st)))

	; add
	(3 (let ((st (update-progc (+|10| progc 1) st)))
	     (let ((st (update-dtos (+|10| dtos 2) st)))
	       (pushus (add<32> (Int32 (memi (+|10| dtos 1) st))
				(Int32 (memi (+|10| dtos 2) st)))
		       st))))

	; jump
	(4 (update-progc (fix|10| (memi (+|10| progc 1) st)) st))

	; jumpz
	(5 (let ((nprogc (if (= (memi (+|10| dtos 1) st) 0)
			     (fix|10| (memi (+|10| progc 1) st))
			   (+|10| progc 2))))
	     (declare (type (unsigned-byte 10) nprogc))
	     (let ((st (update-progc nprogc st)))
	       (update-dtos (+|10| dtos 1) st))))

	; call
	(6 (let ((nadd (fix|10| (memi (+|10| progc 1) st))))
	     (declare (type (unsigned-byte 10) nadd))
	     (let ((st (update-progc nadd st)))
	      (pushcs (+|10| progc 2) st))))

	; return
	(7 (let ((nadd (fix|10| (memi (+|10| ctos 1) st))))
	     (declare (type (unsigned-byte 10) nadd))
	     (let ((st (update-progc nadd st)))
	      (update-ctos (+|10| ctos 1) st))))

	; sub
	(8 (let ((st (update-progc (+|10| progc 1) st)))
	     (let ((st (update-dtos (+|10| dtos 2) st)))
	       (pushus (max<32> 0 (sub<32> (memi (+|10| dtos 2) st)
					   (memi (+|10| dtos 1) st)))
		       st))))

	; dup
	(9 (let ((st (update-progc (+|10| progc 1) st)))
	    (pushus (memi (+|10| dtos 1) st) st)))

	; halt
	(otherwise st)))))

(defthm stp-next
  (implies
   (stp st)
   (stp (next st))))

(defun tiny (st n)
  (declare (xargs :stobjs (st)
		  :guard (stp st)
		  :guard-hints (("goal" :in-theory (disable next stp))))
	   (type (signed-byte 32) n))
  (if (or (not (integerp (Int32 n))) (<= (Int32 n) (Int32 0)))   ; ifix inefficient
      st
    (let ((st (next st)))
      (tiny st (Int32 (1- (Int32 n)))))))


;;;;;
;; Functions for creating Tiny state

;; Note: recursive functions involving s.t. objects must have a base
;; case listed first.  Presumably ACL2 has this restriction in order
;; to allow ACL2 a simpler approach for determining whether a function
;; returns all the s.t. objects it needs to return, since every base
;; case must return every potentially-modified s.t. object.

(defun load-memory-block (address list st)
  (declare (xargs :stobjs (st)
		  :guard (stp st)
		  :verify-guards nil))
  (if (not (consp list)) st
      (let ((st (update-memi address (car list) st)))
	(load-memory-block (+|10| address 1) (cdr list) st))))

(defun load-memory (assoc st)
  (declare (xargs :stobjs (st)
		  :verify-guards nil))
  (if (not (consp assoc)) st
    (let ((st (load-memory-block (caar assoc) (cdar assoc) st)))
      (load-memory (cdr assoc) st))))

(defun load-tiny (pc memlist st)
  (declare (xargs :stobjs (st)
		  :verify-guards nil))
  (let ((st (update-progc pc st)))
    (let ((st (update-dtos 900 st)))
      (let ((st (update-ctos 1000 st)))
	(load-memory memlist st)))))

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

(defun run-example-tiny-state (n st)
  (declare (xargs :verify-guards nil :stobjs (st)))
  (let ((st (load-tiny 4 (list (cons 4 *mod-caller-prog*) (cons 20 *mod-prog*)) st)))
    (tiny st n)))

#|
ACL2 !>:q

Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
ACL2>(time (run-example-tiny-state 10000000 st))
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
(set-verify-guards-eagerness 0)

;; Is "program" loaded at "location" in Tiny state?
(defun program-loaded (st program location)
  (declare (xargs :stobjs (st)))
  (if (consp program)
      (and
       (equal (memi location st) (car program))
       (program-loaded st (cdr program) (1+ location)))
    t))

(defthm prog-lookup
  (implies
   (and
    (syntaxp (quotep n))
    (program-loaded st prog loc)
    (integerp loc)
    (<= loc (nfix n))
    (< (nfix n) (+ loc (len prog))))
   (equal (nth n (nth (memloc) st))
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

(defthm logand-1023-hack
  (implies
   (and
    (<= 0 x)
    (<= x 1023)
    (integerp x))
   (equal (logand x 1023) x))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

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
   (equal (tiny st n)
	  (if (zp n) st (tiny (next st) (1- n)))))
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

(defthm less-minus-hack
  (implies
   (and
    (integerp a)
    (integerp b)
    (< 0 a)
    (<= 0 b))
   (not (< a (- b)))))

(defthm lessp-minus-hack3
 (implies
  (and
   (<= a n)
   (<= b n)
   (< 0 b)
   (integerp a)
   (integerp b)
   (integerp n))
  (equal (< n (+ (- b) a)) nil)))

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
   (equal (len st) 4)
   (equal (len (pushus val st)) 4))
  :hints (("goal" :in-theory (disable logand-with-mask))))

(defthm cancel-plus-hack
  (implies
   (and (integerp x) (integerp y))
   (equal (equal (+ y x) y) (equal (fix x) 0))))

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

(defthm cancel-hack
  (implies
   (rationalp x)
   (equal (< (+ x y) (+ x z)) (< y z)))
  :rule-classes nil)

(defthm less-quoted-hack
  (implies
   (and
    (rationalp x)
    (syntaxp (quotep a))
    (syntaxp (quotep b))
    (rationalp b))
   (equal (< a (+ b x)) (< (- a b) x)))
  :hints (("goal" :use ((:instance cancel-hack (x (- b)) (y a) (z (+ b x))))
	   :in-theory (disable CANCEL_PLUS-LESSP-CORRECT))))

(defthm less-quoted-hack2
  (implies
   (and
    (rationalp x)
    (syntaxp (quotep a))
    (syntaxp (quotep b))
    (rationalp b))
   (equal (< (+ b x) a) (< x (- a b))))
  :hints (("goal" :use ((:instance cancel-hack (x (- b)) (z a) (y (+ b x))))
	   :in-theory (disable CANCEL_PLUS-LESSP-CORRECT))))

(defthm lessp-hack-of-hacks
  (implies
   (and
    (not (< i1 i2))
    (<= i3 i2))
   (equal (< i1 i3) nil)))

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

;; From J's library
(defthm iff-equal
   (implies (and (iff x y)
                 (booleanp x)
                 (booleanp y))
            (equal x y))
   :rule-classes nil)

(defthm lessp-unary---hack
  (implies
   (and
    (syntaxp (quotep n2))
    (integerp n1) (integerp n2))
   (equal
    (< (unary-- n1) n2)
    (< (unary-- n2) n1)))
  :hints (("goal" :use (:instance iff-equal (x (< (unary-- n1) n2)) (y (< (unary-- n2) n1))))))

;; We start proving facts about the benchmark

;; Effect of running loop once (taken from theorem prover output)
(defun mod-loop-once-effect (st)
  (update-nth (progcloc) 24
	   (update-nth (memloc)
		    (update-nth 18
			     (+ (nth 18 (nth (memloc) st))
				(- (nth 19 (nth (memloc) st))))
			     (update-nth (nth (dtosloc) st)
				      (+ (nth 18 (nth (memloc) st))
					 (- (nth 19 (nth (memloc) st))))
				      (update-nth (+ -1 (nth (dtosloc) st))
					       (+ (nth 18 (nth (memloc) st))
						  (- (nth 19 (nth (memloc) st))))
					       (nth (memloc) st))))
		    (update-nth (dtosloc) (nth (dtosloc) st) st))))

(in-theory (disable update-nth-update-nth))
(in-theory (enable len))

(defthm mod-loop-repeat
  (implies
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (equal (progc st) 24)
    (program-loaded st *mod-prog* 20)
    (<= 0 (memi 19 st))
    (<= 0 (memi 18 st))
    (< (memi 19 st) (memi 18 st))
    (not (= (memi 19 st) (memi 18 st)))) ;;redundant, but simplifies proof
   (equal (tiny st 7)
	  (mod-loop-once-effect st)))
  :hints (("goal''" :in-theory (enable next signed-byte-p len))))

;; Effect of loop when it ends with no adjust needed (expression taken
;;from theorem prover output)
(defthm mod-loop-end1
  (implies
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (<= (ctos st) 1020) (> (ctos st) 1010)
    (equal (progc st) 24)
    (program-loaded st *mod-prog* 20)
    (<= 0 (memi 19 st))
    (< 0 (memi 18 st))
    (> (memi 19 st) (memi 18 st))
    (not (= (memi 19 st) (memi 18 st)))) ;;redundant
   (equal (tiny st 13)
	  (update-nth (progcloc)
             (logand (nth (+ 1 (nth (ctosloc) st)) (nth (memloc) st))
                     1023)
             (update-nth (memloc)
                      (update-nth 19 0
                               (update-nth (nth (dtosloc) st)
                                        (nth 18 (nth (memloc) st))
                                        (update-nth (+ -1 (nth (dtosloc) st))
                                                 (+ (- (nth 18 (nth (memloc) st)))
                                                    (nth 19 (nth (memloc) st)))
                                                 (update-nth (+ -2 (nth (dtosloc) st))
                                                          (nth 18 (nth (memloc) st))
                                                          (nth (memloc) st)))))
                      (update-nth (dtosloc) (+ -1 (nth (dtosloc) st))
                               (update-nth (ctosloc) (+ 1 (nth (ctosloc) st)) st))))))
  :hints (("goal''" :in-theory (enable next signed-byte-p))))

;; Effect of loop when it ends with an adjust needed (expression taken
;;from theorem prover output)
(defthm mod-loop-end2
  (implies
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (<= (ctos st) 1020) (> (ctos st) 1010)
    (equal (progc st) 24)
    (program-loaded st *mod-prog* 20)
    (<= 0 (memi 19 st))
    (< 0 (memi 18 st))
    (= (memi 19 st) (memi 18 st)))
   (equal (tiny st 14)
	  (update-nth
	   (progcloc)
	   (logand (nth (+ 1 (nth (ctosloc) st)) (nth (memloc) st))
		   1023)
	   (update-nth (memloc)
		    (update-nth 18 0
			     (update-nth 19 0
				      (update-nth (nth (dtosloc) st)
					       0
					       (update-nth (+ -1 (nth (dtosloc) st))
							0
							(update-nth (+ -2 (nth (dtosloc) st))
								 (nth 18 (nth (memloc) st))
								 (nth (memloc) st))))))
		    (update-nth (dtosloc) (+ -1 (nth (dtosloc) st))
			     (update-nth (ctosloc) (+ 1 (nth (ctosloc) st)) st))))))
  :hints (("goal''" :in-theory (enable next signed-byte-p))))

;; number of instructions needed to execute loop for values x and y.
(defun modloop-clock-helper (x y)
  (if (or (not (integerp x)) (not (integerp y)) (>= 0 y) (<= x y))
      (if (equal x y) 14 13)
    (c+ 7 (modloop-clock-helper (- x y) y))))

(defun modloop-clock (st)
  (declare (xargs :stobjs (st)))
  (let ((x (memi 18 st)) (y (memi 19 st)))
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

(defthm less-+-1024-hack
  (implies
   (and
    (integerp n)
    (integerp p))
   (iff (< (+ p n) 1024) (< n (+ (- p) 1024)))))

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

(defthm lessp-minus-hack5
  (implies
   (and
    (not (> b (- n)))
    (<= 0 a)
    (integerp a)
    (integerp b)
    (integerp c))
   (not (< (+ a (- b)) n))))

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
   (equal (program-loaded (update-nth n v st) prog loc)
	  (program-loaded st prog loc)))
  :hints (("goal" :in-theory (enable update-nth program-loaded))))


;; such a screwy rule.  It's inelegant because program-loaded is a function
;; of state.
(defthm program-loaded-cons
  (implies
   (and
    (or (< n loc) (< (+ (len prog) loc) n) (equal val (nth n mem)))
    (integerp n) (<= 0 n) (integerp loc) (<= 0 loc)
    (program-loaded (update-nth 1 mem st) prog loc))
   (program-loaded (update-nth 1 (update-nth n val mem) st) prog loc))
  :hints (("goal" :in-theory (enable program-loaded update-nth nth len))))

(defthm lessp-hack1
  (implies
   (and
    (<= a b)
    (< c a))
   (equal (< c b) t)))

(defthm mod-loop-calculates-mod
  (implies
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (<= (ctos st) 1020) (> (ctos st) 1010)
    (equal (progc st) 24)
    (program-loaded st *mod-prog* 20)
    (equal a (memi 18 st))
    (equal b (memi 19 st))
    (< 0 a) (< 0 b)
    (equal s2 (tiny st (modloop-clock-helper a b))))
   (equal (memi (1+ (dtos s2)) s2) (remainder-prog-result a b)))
  :rule-classes nil
  :hints (("goal" :in-theory (set-difference-theories
			      (enable stp len)
			      '(tiny-straightline))
			      :induct (mod-loop-repeat-induct a b st))
	  ("Subgoal *1/1.1'" :expand (REMAINDER-PROG-RESULT (NTH 18 (NTH 1 ST))
                       (NTH 19 (NTH 1 ST))))))

(defun remclock (st)
  (declare (xargs :stobjs (st)))
  (modloop-clock-helper (memi 18 st) (memi 19 st)))

(defun good-initial-remainder-state (st)
  (declare (xargs :stobjs (st)))
   (and
    (stp st)
    (< (dtos st) 1000) (>= (dtos st) 100)
    (<= (ctos st) 1020) (> (ctos st) 1010)
    (equal (progc st) 24)
    (program-loaded st *mod-prog* 20)
    (< 0 (memi 18 st))
    (< 0 (memi 19 st))))

(defthm remainder-correct
  (let ((s2 (tiny st (remclock st))))
  (implies
    (good-initial-remainder-state st)
    (equal (memi (1+ (dtos s2)) s2)
           (remainder-prog-result (memi 18 st) (memi 19 st)))))
  :rule-classes nil
  :hints (("goal"
	   :use ((:instance mod-loop-calculates-mod
			    (s2 (tiny st (modloop-clock-helper (memi 18 st) (memi 19 st))))
			    (a (memi 18 st))
			    (b (memi 19 st))))
	   :in-theory (disable tiny-straightline))))

;;; Show that our recursive version of remainder is identical to mod.
;;; Fortunately, Bishop Brock's been here before.

(include-book "../../../ihs/quotient-remainder-lemmas")

(defthm remainder-is-mod
  (implies
   (and
    (integerp x)
    (<= 0 x)
    (integerp y)
    (<= 0 y))
   (equal (remainder-prog-result x y) (mod x y))))

(defthm mod-correct
  (let ((s2 (tiny st (remclock st))))
  (implies
    (good-initial-remainder-state st)
    (equal (memi (1+ (dtos s2)) s2)
           (mod (memi 18 st) (memi 19 st)))))
  :rule-classes nil
  :hints (("goal" :use ((:instance remainder-correct)))))

