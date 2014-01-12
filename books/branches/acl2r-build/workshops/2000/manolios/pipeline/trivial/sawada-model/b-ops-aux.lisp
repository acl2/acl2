;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; b-ops-aux.lisp:
;;  This file contains auxiliary lemmas to assist the IHS library
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "b-ops-aux-def")

(deflabel begin-b-ops-aux)

;; Type of b-if
(defthm bitp-b-if
    (implies (and (bitp y) (bitp z))
	     (bitp (b-if x y z)))
  :hints (("goal" :in-theory (enable bitp))))

(defthm integerp-b-if
    (implies (and (integerp y) (integerp z))
	     (integerp (b-if x y z)))
  :hints (("goal" :in-theory (enable bitp))))

(defthm b-not-b-not
    (equal (b-not (b-not i)) (bfix i))
  :hints (("goal" :in-theory (enable b-not bfix zbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here are several basic lemmas about bit operations.

;; If bit vector X is longer than (p+s), bits between the p'th and (p+s)'th
;; bits of the concatenation of x and y is equal to that of x.
(defthm rdb-logapp-1
    (implies (and (integerp x) (integerp y) (integerp i) (<= 0 i) 
		  (integerp s) (<= 0 s) (integerp p) (<= 0 p)
		  (<= (+ s p) i))
	     (equal (rdb (cons s p) (logapp i x y))
		    (rdb (cons s p) x)))
  :hints (("Goal" :in-theory (enable logapp* rdb bsp-size bsp-position))))

;; If bit vector X is shorter than p, bits from the p'th LSB to (p+s)'th
;; LSB of the concatenation of x and y is equal to that of y.
(defthm rdb-logapp-2
    (implies (and (integerp x) (integerp y)
		  (integerp s) (<= 0 s) (integerp p) (<= 0 p)
		  (integerp i) (<= 0 i)
		  (<= i p))
	     (equal (rdb (cons s p) (logapp i x y))
		    (rdb (cons s (- p i)) y)))
  :hints (("Goal" :in-theory (enable logapp* rdb bsp-size bsp-position))))


(defthm loghead-0
    (equal (loghead x 0) 0)
  :hints (("Goal" :in-theory (enable loghead))))

(defthm loghead-1
    (equal (loghead 1 vector) (logcar vector))
  :hints (("Goal" :in-theory (enable logcar loghead))))

(defthm logcar-bitp
    (implies (bitp x)
	     (equal (logcar x) x))
  :hints (("Goal" :in-theory (enable bitp logcar))))

(defthm logbit-0-bitp
    (implies (bitp x)
	     (equal (logbit 0 x) x))
    :hints (("Goal" :in-theory (enable bitp logbit))))

(defthm loghead-bitp
    (implies (bitp x)
	     (equal (loghead 1 x) x))
  :hints (("Goal" :in-theory (enable rdb))))


(defthm logcons-0
    (implies (bitp x)
	     (equal (logcons x 0) x))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm rdb-bitp
    (implies (bitp x)
	     (equal (rdb (cons 1 0) x) x))
  :hints (("Goal" :in-theory (enable rdb))))

(defthm rdb-0
    (equal (rdb (cons 0 n) x) 0)
  :hints (("Goal" :in-theory (enable rdb bsp-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here begins a basic theory about lobops
; Recursive definition of Logbit*.
(defthm logbit*
    (implies (and (integerp pos)
		  (>= pos 0)
		  (integerp i))
	     (equal (logbit pos i)
		    (if (equal pos 0)
			(logcar i)
			(logbit (1- pos) (logcdr i)))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (e/d (logbit logbitp*) (logbitp)))))

(in-theory (disable logbit*))

(local
(defun logtail-induct (pos i)
  (if (zp pos)
      i
      (logtail-induct (1- pos) (logcdr i)))))


(defthm logcar-logtail
    (implies (and (integerp n) (<= 0 n)
		  (integerp x))
	     (equal (logcar (logtail n x))
		    (logbit n x)))
  :hints (("Goal" :in-theory (e/d (logtail* logbit logbitp*)
				  (logbitp))
		  :induct (logtail-induct n x))))

(defthm logcdr-logtail
    (implies (and (integerp n) (<= 0 n)
		  (integerp x))
	     (equal (logcdr (logtail n x))
		    (logtail (1+ n) x)))
  :hints (("Goal" :in-theory (enable logtail*)
		    :induct (logtail-induct n x))))

;; The following two lemmas are for expansion before BDD
(deflabel begin-bv-expand)
(defthm rdb-expand
   (implies (and (syntaxp (and (quoted-constant-p s) (quoted-constant-p n)))
		 (integerp s) (< 0 s)
		 (integerp n) (<= 0 n)
		 (integerp x))
	    (equal (rdb (cons s n) x)
		   (logcons (logbit n x) (rdb (cons (1- s) (1+ n)) x))))
  :hints (("Goal" :in-theory (enable rdb bsp-position bsp-size loghead*
				     logtail*))))


;; logops supplement for logxxx operations. There are bunch of
;; definition rules logior* and so on, but they are definition rules.
;; We rewrite rules to forcibly open up the expressions before applying
;; BDD techniques.  We redefine the same lemma as a rewrite rule.
(defthm open-logior-right-const
    (implies (and (bitp i1)
		  (integerp i2)
		  (integerp j))
	     (equal (logior (logcons i1 i2) j)
		    (logcons (b-ior i1 (logcar j)) (logior i2 (logcdr j)))))
  :hints (("Goal" :in-theory (enable logior*))))


(defthm open-logior-left-const
    (implies (and (bitp j1)
		  (integerp j2)
		  (integerp i))
	     (equal (logior i (logcons j1 j2))
		    (logcons (b-ior (logcar i) j1) (logior (logcdr i) j2))))
  :hints (("Goal" :in-theory (enable logior*))))

(defthm open-logior
    (implies (and (bitp i1)
		  (bitp j1)
		  (integerp i2)
		  (integerp j2))
	     (equal (logior (logcons i1 i2) (logcons j1 j2))
		    (logcons (b-ior i1 j1) (logior i2 j2))))
  :hints (("Goal" :in-theory (enable logior*))))

(defthm open-logxor-right-const
    (implies (and (bitp i1)
		  (integerp i2)
		  (integerp j))
	     (equal (logxor (logcons i1 i2) j)
		    (logcons (b-xor i1 (logcar j)) (logxor i2 (logcdr j)))))
  :hints (("Goal" :in-theory (enable logxor*))))


(defthm open-logxor-left-const
    (implies (and (bitp j1)
		  (integerp j2)
		  (integerp i))
	     (equal (logxor i (logcons j1 j2))
		    (logcons (b-xor (logcar i) j1) (logxor (logcdr i) j2))))
  :hints (("Goal" :in-theory (enable logxor*))))

(defthm open-logxor
    (implies (and (bitp i1)
		  (bitp j1)
		  (integerp i2)
		  (integerp j2))
	     (equal (logxor (logcons i1 i2) (logcons j1 j2))
		    (logcons (b-xor i1 j1) (logxor i2 j2))))
  :hints (("Goal" :in-theory (enable logxor*))))




(defthm open-logand-right-const
    (implies (and (bitp i1)
		  (integerp i2)
		  (integerp j))
	     (equal (logand (logcons i1 i2) j)
		    (logcons (b-and i1 (logcar j)) (logand i2 (logcdr j)))))
  :hints (("Goal" :in-theory (enable logand*))))


(defthm open-logand-left-const
    (implies (and (bitp j1)
		  (integerp j2)
		  (integerp i))
	     (equal (logand i (logcons j1 j2))
		    (logcons (b-and (logcar i) j1) (logand (logcdr i) j2))))
  :hints (("Goal" :in-theory (enable logand*))))

(defthm open-logand
    (implies (and (bitp i1)
		  (bitp j1)
		  (integerp i2)
		  (integerp j2))
	     (equal (logand (logcons i1 i2) (logcons j1 j2))
		    (logcons (b-and i1 j1) (logand i2 j2))))
  :hints (("Goal" :in-theory (enable logand*))))

(defthm open-lognot
    (implies (and (bitp i1)
		  (integerp i2))
	     (equal (lognot (logcons i1 i2))
		    (logcons (b-not i1) (lognot i2))))
  :hints (("Goal" :in-theory (enable lognot*))))

(defthm fold-logcdr-vector
    (implies (and (integerp x)
		  (syntaxp (or (not (consp x))
			       (not (equal (car x) 'logcons)))))
	     (equal (logcdr x) (logtail 1 x)))
  :hints (("goal" :in-theory (enable logtail*))))
(in-theory (disable fold-logcdr-vector))

(defthm fold-logcar-vector
    (implies (and (integerp x)
		  (syntaxp (or (not (consp x))
			       (not (equal (car x) 'logcons)))))
	     (equal (logcar x) (logbit 0 x)))
  :hints (("goal" :in-theory (enable logbit logbitp*))))
(in-theory (disable fold-logcar-vector))	   
(deflabel end-bv-expand)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bv-eqv rules
(defthm bv-eqv*
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n)
		  (>= n 0))
	     (equal (bv-eqv n x y)
		    (if (zp n)
			1
			(b-and (b-eqv (logcar x) (logcar y))
			       (bv-eqv (1- n) (logcdr x) (logcdr y))))))
  :hints (("goal" :in-theory (enable bv-eqv loghead*)))
  :rule-classes :definition)

(in-theory (disable bv-eqv*))

;; Following lemma is useful in converting a formula with 'bv-eqv' to one
;; with 'equal'.
;; This can cause BDD simplification to fail, especially if when the words 
;; need to be open up.
(defthm bv-eqv-iff-equal
  (implies (and (unsigned-byte-p n x) (unsigned-byte-p n y))
	   (equal (b1p (bv-eqv n x y))
		  (equal x y)))
  :hints (("Goal" :in-theory (enable bv-eqv b1p))))

(defthm bv-eqv-0
    (equal (bv-eqv 0 x y) 1)
  :Hints (("Goal" :in-theory (enable bv-eqv))))

(defthm bv-x-x
    (equal (bv-eqv n x x) 1)
  :hints (("goal" :in-theory (enable bv-eqv))))

(defthm bv-eqv-assoc
    (equal (bv-eqv n x y) (bv-eqv n y x))
  :hints (("Goal" :in-theory (enable bv-eqv))))

(defthm bv-eqv-bits
    (implies (and (bitp x) (bitp y) (integerp n) (> n 0))
	     (equal (bv-eqv n x y) (b-eqv x y)))
  :hints (("Goal" :in-theory (enable bv-eqv* bitp bv-eqv-iff-equal))))

(defthm bv-eqv-expand
    (implies (and (integerp x) (integerp y)
		  (integerp n) (> n 0)
		  (syntaxp (quoted-constant-p n)))
	     (equal (bv-eqv n x y)
		    (b-and (b-eqv (logcar x) (logcar y))
			   (bv-eqv (1- n) (logcdr x) (logcdr y)))))
  :hints (("Goal" :in-theory (enable bv-eqv*))))

;; Following lemma is a schematic lemma which will be used in BDD proof.
;; We noticed that several lemmas is a tautology under the property that
;; (bv-eqv x y) and (bv-eqv x z) are not simultaneously asserted, if y and  
;; z are not equal. We instantiate the following lemma and add it to BDD
;; proof as a hint.
(defthm bv-eqv-transitivity
    (implies (and (unsigned-byte-p n x)
		  (unsigned-byte-p n y)
		  (unsigned-byte-p n z)
		  (b1p (b-and (bv-eqv n x z) (bv-eqv n y z))))
	     (equal x y))
  :hints (("Goal" :in-theory (enable bv-eqv )))
  :rule-classes nil)

;; Bv-expander is the theory to be enabled to expand bit vectors before
;; applying bdd's.
(deftheory bv-expander 
    '(rdb-expand
      open-lognot
      open-logand open-logand-right-const open-logand-left-const
      open-logior open-logior-right-const open-logior-left-const
      open-logxor open-logxor-right-const open-logxor-left-const
      fold-logcar-vector fold-logcdr-vector
      bv-eqv-bits
      bv-eqv-0
      bv-eqv-expand))

(in-theory (disable bv-expander))

(local (in-theory (enable b1p)))

;; Bit-boolean-converter converting expressions of form (equal x 1) to
;; expressions using bitp, lest BDD package assigns different boolean values
;; to (b1p x) and (equal x 1).  It also converts (equal x 0) to (not (b1p x)).
(defthm equal-to-1-to-b1p
    (implies (bitp x)
	     (equal (equal x 1)
		    (b1p x)))
  :Hints (("Goal" :In-theory (enable bitp))))

(defthm equal-to-0-to-not-b1p
    (implies (bitp x)
	     (equal (equal x 0)
		    (not (b1p x))))
  :Hints (("Goal" :In-theory (enable bitp))))

(defthm equal-to-b1p-b-eqv
    (implies (and (bitp x) (bitp y))
	     (equal (equal x y) (b1p (b-eqv x y))))
  :hints (("Goal" :in-theory (enable b-eqv b1p zbp bitp))))

(deftheory equal-b1p-converter
    '(equal-to-1-to-b1p equal-to-0-to-not-b1p))

(in-theory (disable equal-b1p-converter))
(in-theory (disable  equal-to-b1p-b-eqv))

;; From here, we define bit-to-boolean converter, especially for BDD
;; operation. 
(deflabel begin-lift-b-ops)

(defthm zbp-b-and
    (equal (zbp (b-and x y))
	   (or (zbp x) (zbp y)))
  :Hints (("Goal" :in-theory (enable b-and))))

(defthm zbp-b-ior
    (equal (zbp (b-ior x y))
	   (and (zbp x) (zbp y)))
  :Hints (("Goal" :in-theory (enable b-ior))))

(defthm zbp-b-xor
    (equal (zbp (b-xor x y))
	   (or (and (zbp x) (zbp y))
	       (and (not (zbp x)) (not (zbp y)))))
  :Hints (("Goal" :in-theory (enable b-xor))))

(defthm zbp-b-not
    (equal (zbp (b-not x))
	   (not (zbp x)))
  :Hints (("Goal" :in-theory (enable b-not))))

(defthm zbp-b-eqv
    (equal (zbp (b-eqv x y))
	   (not (iff (zbp x) (zbp y))))
  :Hints (("Goal" :in-theory (enable b-eqv))))



(defthm b1p-b-and
    (equal (b1p (b-and x y))
	   (and (b1p x) (b1p y)))
  :Hints (("Goal" :in-theory (enable b-and))))

(defthm b1p-b-ior
    (equal (b1p (b-ior x y))
	   (or (b1p x) (b1p y)))
  :Hints (("Goal" :in-theory (enable b-ior))))

(defthm b1p-b-xor
    (equal (b1p (b-xor x y))
	   (or (and (b1p x) (not (b1p y)))
	       (and (not (b1p x)) (b1p y))))
  :Hints (("Goal" :in-theory (enable b-xor))))

(defthm b1p-b-not
    (equal (b1p (b-not x))
	   (not (b1p x)))
  :Hints (("Goal" :in-theory (enable b-not))))

(defthm b1p-b-eqv
    (equal (b1p (b-eqv x y))
	   (iff (b1p x) (b1p y)))
  :Hints (("Goal" :in-theory (enable b-eqv))))

(defthm b1p-nand (equal (b1p (b-nand x y)) (not (and (b1p x) (b1p y))))
  :hints (("Goal" :in-theory (enable b-nand))))

(defthm b1p-nor (equal (b1p (b-nor x y)) (not (or (b1p x) (b1p y))))
    :hints (("Goal" :in-theory (enable b-nor))))

(defthm b1p-andc1 (equal (b1p (b-andc1 x y)) (and (not (b1p x)) (b1p y)))
  :hints (("Goal" :in-theory (enable b-andc1))))

(defthm b1p-andc2 (equal (b1p (b-andc2 x y)) (and (b1p x) (not (b1p y))))
  :hints (("Goal" :in-theory (enable b-andc2))))

(defthm b1p-orc1 (equal (b1p (b-orc1 x y)) (or (not (b1p x)) (b1p y)))
  :hints (("Goal" :in-theory (enable b-orc1))))

(defthm b1p-orc2 (equal (b1p (b-orc2 x y)) (or (b1p x) (not (b1p y))))
  :hints (("Goal" :in-theory (enable b-orc2))))  

(defthm zbp-to-b1p
    (equal (zbp x) (not (b1p x)))
  :hints (("Goal" :in-theory (enable b1p))))

(deflabel end-lift-b-ops)

(deftheory lift-b-ops 
    (set-difference-theories (universal-theory 'end-lift-b-ops)
			     (universal-theory 'begin-lift-b-ops)))

(in-theory (disable lift-b-ops))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; New Simplifier
; This simplifier simplifies bit terms into 1 and 0's using information
; represented by b1p.  
; Origianl Simplify-Bit-Functions can simplify expressions with bit-functions
; if its arguments are 0 or 1's.  For instance, it can reduce expressions
; with a rule like:
;  (EQUAL (B-AND 1 X) (BFIX X))
; In the new simplifier reduces the expressions if hypothesis satisfies
; certain conditions, like
;	 (implies (and (bitp x) (bitp y) (not (b1p y)))
;		  (equal (b-and x y) 0))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-b1p-bit-rewriter)

(defthm b1p-bit-forward
    (implies (and (b1p b) (force (bitp b))) (equal b 1))
  :hints (("goal" :in-theory (enable b1p bitp zbp)))
  :rule-classes :forward-chaining)

(defthm not-b1p-bit-forward
    (implies (and (not (b1p b)) (force (bitp b))) (equal b 0))
  :hints (("goal" :in-theory (enable b1p bitp zbp)))
  :rule-classes :forward-chaining)

(defthm simplify-bit-functions-2
    (and (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-and x y) 0))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-and x y) 0))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-and x y) y))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-and x y) x))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-ior x y) y))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-ior x y) x))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-ior x y) 1))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-ior x y) 1))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-xor x y) y))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-xor x y) x))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-xor x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-xor x y) (b-not x)))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-eqv x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-eqv x y) (b-not x)))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-eqv x y) y))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-eqv x y) x))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-nand x y) 1))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-nand x y) 1))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-nand x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-nand x y) (b-not x)))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-nor x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-nor x y) (b-not x)))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-nor x y) 0))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-nor x y) 0))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-andc1 x y) y))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-andc1 x y) 0))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-andc1 x y) 0))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-andc1 x y) (b-not x)))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-andc2 x y) 0))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-andc2 x y) x))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-andc2 x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-andc2 x y) 0))

	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-orc1 x y) 1))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-orc1 x y) (b-not x)))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-orc1 x y) y))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-orc1 x y) 1))
	 
	 (implies (and (bitp x) (bitp y) (not (b1p x)))
		  (equal (b-orc2 x y) (b-not y)))
	 (implies (and (bitp x) (bitp y) (not (b1p y)))
		  (equal (b-orc2 x y) 1))
	 (implies (and (bitp x) (bitp y) (b1p x))
		  (equal (b-orc2 x y) 1))
	 (implies (and (bitp x) (bitp y) (b1p y))
		  (equal (b-orc2 x y) x)))
  :hints (("Goal" :in-theory (enable b1p zbp b-and bitp))))

(deflabel end-b1p-bit-rewriter)

(deftheory b1p-bit-rewriter
    (set-difference-theories (universal-theory 'end-b1p-bit-rewriter)
			     (universal-theory 'begin-b1p-bit-rewriter)))

(in-theory (disable b1p-bit-rewriter))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; BDD helps
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftheory pre-bdd-disables
    '(bv-eqv-iff-equal simplify-bit-functions))

(deftheory bdd-disables
    '(bv-eqv-iff-equal simplify-bit-functions))

(theory-invariant (incompatible (:rewrite bv-eqv-iff-equal)
				(:rewrite rdb-expand)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; range of unsigned-byte-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; theories about the range of unsigned-byte-p
(defthm plus-unsigned-byte-p-lt-2-*-expt-2-width
    (implies (and (unsigned-byte-p width val1)
		  (unsigned-byte-p width val2))
	     (< (+ val1 val2) (* 2 (expt 2 width))))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defun logbit-induction (pos val)
    (if (zp pos)
	val
	(logbit-induction (1- pos) (logcdr val))))
	
; If a value are in the range  0 <= val < 2^width 
; then the width'th bit of val is not set.
(defthm logbit-0-if-val-lt-expt-2-width
    (implies (and (integerp width) (<= 0 width)
		  (integerp val)
		  (<= 0 val) (< val (expt 2 width)))
	     (equal (logbit width val) 0))
  :hints (("goal" :in-theory (e/d (logbit* expt logcar logcdr)
				  (exponents-add))
		  :induct (logbit-induction width val)))
  :rule-classes nil)


(encapsulate nil
(local
 (defthm logbit-1-if-val-gt-expt-2-width-help1
     (IMPLIES (AND (INTEGERP WIDTH)
		   (< 0 WIDTH)
		   (INTEGERP VAL)
		   (<= (* 2 (EXPT 2 (+ -1 WIDTH))) VAL)
		   (< (/ VAL 2) (* 2 (EXPT 2 (+ -1 WIDTH)))))
	      (> (* 2 (EXPT 2 (+ -1 WIDTH)))
		 (FLOOR VAL 2)))
 :rule-classes nil))

(local
 (defthm logbit-1-if-val-gt-expt-2-width-help2
     (implies  (and (integerp val) 
		    (integerp width) (< 0 width)
		    (< VAL (* 2 2 (EXPT 2 (+ -1 WIDTH)))))
	       (< (/ VAL 2) (* 2 (EXPT 2 (+ -1 WIDTH)))))
   :hints (("goal" :in-theory (e/d (expt) (exponents-add))))
   :rule-classes nil))

(local
(defthm logbit-1-if-val-gt-expt-2-width-help
    (IMPLIES (AND (INTEGERP WIDTH)
		  (INTEGERP VAL)
		  (< 0 WIDTH)
		  (<= (* 2 (EXPT 2 (+ -1 WIDTH))) (FLOOR VAL 2)))
	     (<= (* 2 2 (EXPT 2 (+ -1 WIDTH))) VAL))
  :hints (("goal" :in-theory (e/d (exponents-add) (expt))
		  :use ((:instance logbit-1-if-val-gt-expt-2-width-help1)
			(:instance logbit-1-if-val-gt-expt-2-width-help2))))))


; If a value are in the range  2^width <= val < 2^width * 2,
; then the width'th bit of val is set.
(defthm logbit-1-if-val-gt-expt-2-width
    (implies (and (integerp width) (<= 0 width)
		  (integerp val)
		  (<= (expt 2 width) val)
		  (< val (* 2 (expt 2 width))))
	     (equal (logbit width val) 1))
  :hints (("goal" :in-theory (e/d (logbit* expt logcar logcdr)
				  (exponents-add))
		  :induct (logbit-induction width val)))
  :rule-classes nil)
)

; Suppose val1 and val2 are unsigned-byte-p whose width is w.
; If w'th bit of the sum (+ val1 val2) is not set,
; (+ val1 val2) < 2^w.
(defthm plus-unsigned-byte-lt-expt-2-width-if-logbit
    (implies (and (unsigned-byte-p width val1)
		  (unsigned-byte-p width val2)
		  (not (b1p (logbit width (+ val1 val2)))))
	     (< (+ val1 val2) (expt 2 width)))
  :hints (("goal" :in-theory (enable unsigned-byte-p)
		  :use (:instance logbit-1-if-val-gt-expt-2-width
				  (val (+ val1 val2))))))



; Suppose val1 and val2 are unsigned-byte-p whose width is w.
; If w'th bit of the sum (+ val1 val2) is set, then
;   2^w < (+ val1 val2).
(defthm plus-unsigned-byte-gt-expt-2-width-if-logbit
    (implies (and (unsigned-byte-p width val1)
		  (unsigned-byte-p width val2)
		  (b1p (logbit width (+ val1 val2))))
	     (<= (expt 2 width) (+ val1 val2)))
  :hints (("goal" :in-theory (enable unsigned-byte-p)
		  :use (:instance logbit-0-if-val-lt-expt-2-width
				  (val (+ val1 val2))))))

; Suppose val1 and val2 are unsigned-byte-p whose width is w.
; If the sum of val1 and val2 does not carry out to w'th bit,
;  (loghead w (+ val1 val2)) = (+ val1 val2)
(defthm loghead-unsigned-byte-+-if-not-carry
    (implies (and (integerp width)
		  (<= 0 width)
		  (unsigned-byte-p width val1)
		  (unsigned-byte-p width val2)
		  (not (b1p (logbit width (+ val1 val2)))))
	     (equal (loghead width (+ val1 val2)) (+ val1 val2)))
  :hints (("goal" :in-theory (enable loghead)
		  :do-not-induct t)))

(encapsulate nil
(local
(defthm j*k-ge-2*k-if-j-gt-1
    (implies (and (integerp j)
		  (< 1 j)
		  (integerp k)
		  (< 0 k))
	     (<= (* 2 k) (* j k)))
  :hints (("Goal" :in-theory (enable <-*-right-cancel)))
  :rule-classes :linear))

; A trivia theorem.
; If y < x < 2*y, then (x mod y) = x - y
(defthm mod-x-y-=-minux-x-y
 (implies (and (integerp x) (integerp y) (< 0 y)
	       (<= y x) (< x (* 2 y)))
	  (equal (mod x y) (- x y)))
 :Hints (("goal" :in-theory (disable (:generalize floor-bounds)))
	 ("subgoal 1" :cases ((<= j 1)))))
)

(in-theory (disable mod-x-y-=-minux-x-y))

; Suppose val1 and val2 are unsigned-byte-p whose width is w.
; If the sum of val1 and val2 does not carry out to w'th bit,
;  (loghead w (+ val1 val2)) = (+ val1 val2)
(defthm loghead-unsigned-byte-+-if-carry
    (implies (and (integerp width)
		  (<= 0 width)
		  (unsigned-byte-p width val1)
		  (unsigned-byte-p width val2)
		  (b1p (logbit width (+ val1 val2))))
	     (equal (loghead width (+ val1 val2))
		    (- (+ val1 val2) (expt 2 width))))
  :hints (("goal" :in-theory (enable loghead mod-x-y-=-minux-x-y)
		  :do-not-induct t)))

