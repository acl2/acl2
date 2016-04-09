(in-package "ACL2")

#|

Matt Wilding (http://hokiepokie.org) Feb 2002

This ACL2 script solves a challenge posed by Bill Legato, to prove
that a program written for the Mostek 6502 microprocessor correctly
implements multiplication.  The program is described in

A Weakest Precondition Model for Assembly Language Programs

by Bill Legato, dated June 19, 2000.  (A later version of this paper
also containing the program is available, which is currently FOUO.)

Comments from the 2.5x version of this script:

xx In this script we solve this challenge in the following steps:
xx
xx
xx 1. Model the program in ACL2 using a stobj to represent state,
xx adding a definition for each line of the program, and combining the
xx lines into a program.
xx
xx 2. Describe the algorithm abstractly in a function "loop-spec".
xx
xx 3. Prove the loop-spec works.
xx
xx 4. Prove that our Mostek 6502 program model works like loop-spec.
xx
xx 5. Combine the lemmas of 3. and 4. into the final theorem.
xx
xx Solving the challenge problem required 15 hours.
xx
xx   1. Understanding the algorithm                1 hr
xx   2. Modeling the program in ACL2               2 hrs
xx   3. Wasting time working on the proof before
xx      remembering yet again that decomposing
xx      proofs is *always* the right thing to do   4 hrs.
xx   4. Proving that loop-spec works               3 hrs
xx   5. Proving that loop-spec works like the
xx      real program                               3.5 hrs
xx   6. Cleaning and documenting                   1.5 hrs
xx                                                 -------
xx                                                 15 hrs
xx
xx
xx The proof runs in under a minute under ACL2 2.5x, a version of ACL2
xx 2.5 enhanced with nu-rewriter patches.  The proof uses Super-IHS,
xx the Rockwell Collins ACL2 book that extends IHS.  It would take a
xx couple hours of work to port this proof to just-released 2.6, since
xx I'd have to identify the handful of Super-IHS lemmas that are
xx employed here and add their proof to the proof script.  (If anyone
xx wants me to do this, please let me know.)

The proof has now been ported to ACL2 2.6.  The port to 2.6 required
about 3.5 hours of work, plus 1 hour for rearranging the lemmas
sensibly and documenting.  Some Super-IHS rules were ripped out of
Super-IHS and put here so as to make this script depend only on
distibuted books.

While I was at porting the proof, I spent some time reorganizing and
simplifying.  Most importantly, I eliminated the use of a spec
function to decompose the proof in this version.  The spec function
was important to me during the proof development, and is generally the
right thing to do on these kinds of proofs.  But once I knew what the
inductions were, etc., I was able to combine the two proof steps in
this case into one.  The resulting proof is far less pedagogical, but
it's so much shorter that I could not resist.

It's great to see that the techniques Greve and I use for microcode
proofs apply so directly to assembly code reasoning.

Matt Wilding
Christmas 2001
(ported to ACL2 2.6 - 3 Jan 2002)
(updated to avoid nu-rewriter use - 27 Feb 2002)

|#

;; Set up ACL2 how we like.

(set-irrelevant-formals-ok t)

;; We load the IHS book, and some other useful books, that are part of
;; the standard 2.6 distribution.
(include-book "arithmetic/top-with-meta"     :dir :system)
(include-book "ihs/ihs-definitions"          :dir :system)
(include-book "ihs/ihs-lemmas"               :dir :system)
(include-book "data-structures/structures"   :dir :system)
(include-book "data-structures/array1"       :dir :system)
(include-book "ihs/@logops"                  :dir :system)
(include-book "data-structures/list-defuns"  :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "data-structures/deflist"      :dir :system)
(include-book "data-structures/defalist"     :dir :system)
(include-book "meta-lemmas")   ;Always include last!

(minimal-ihs-theory)

(in-theory (enable @logops-theory array1-lemmas meta-lemma-theory))

(enable-theory (definition-free-theory (theory 'list-defuns)))
(enable-theory (definition-free-theory (theory 'alist-defuns)))

(in-theory (disable (force)))

(in-theory (enable nth-update-nth))

;;
;; Some induction schemes we'll need, courtesy of the Super-IHS book.
;;

(defun sub1-induction (x)
  (if (zp x)
      x
    (sub1-induction (1- x))))

(defun sub1-logcdr-induction (m x)
  (if (zp m)
      x
    (sub1-logcdr-induction (1- m) (logcdr x))))

(defun logcdr-logcdr-induction (b c)
  (declare (xargs :measure (abs (ifix b))
                  :hints (("goal" :in-theory (enable logcdr)))))
  (if (or (equal b -1) (zip b))
      c
    (logcdr-logcdr-induction (logcdr b) (logcdr c))))

(defun sub1-sub1-logcdr-induction (a b v)
  (if (zp b)
      (or a v)
    (sub1-sub1-logcdr-induction (1- a) (1- b) (logcdr v))))

(defun sub1-logcdr-logcdr-induction (m x y)
  (if (zp m)
      (or x y)
    (sub1-logcdr-logcdr-induction (1- m) (logcdr x) (logcdr y))))

(defun sub1-sub1-induction (m n)
  (if (zp m)
      n
    (sub1-sub1-induction (1- m) (1- n))))

(defun sub1-logcdr-logcdr-carry-induction (m x y c)
  (if (zp m)
      (or x y c)
    (sub1-logcdr-logcdr-carry-induction
     (1- m)
     (logcdr x)
     (logcdr y)
     (if (or (and (equal (logcar x) 1) (equal (logcar y) 1))
             (and (equal (logcar x) 1) (equal c 1))
             (and (equal (logcar y) 1) (equal c 1)))
         1 0))))

;; A couple definitions used in the reader-generated type rules,
;; courtesy of the Super-IHS book
(defthm unsigned-byte-p-<=
  (equal (unsigned-byte-p bits i)
         (and (integerp bits)
              (>= bits 0)
              (integerp i)
              (>= i 0)
              (<= i (1- (expt 2 bits)))))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defthm signed-byte-p-<=
  (equal (signed-byte-p bits i)
         (and (integerp bits)
              (> bits 0)
              (integerp i)
              (>= i (- (expt 2 (- bits 1))))
              (<= i (1- (expt 2 (- bits 1))))))
  :rule-classes :definition :hints
  (("goal" :in-theory (enable signed-byte-p))))

(in-theory (disable unsigned-byte-p-<= signed-byte-p-<=))

;; The following ~30 rules are IHS-related.  Some were in the earlier
;; version of this proof.  Many are stolen from Super-IHS.  Some of
;; the more important Super-IHS rules have names starting with *ark*.

(defthm ash-*2-simplify
  (implies
   (and
    (integerp x)
    (integerp n)
    (<= 0 n))
   (equal (ash (* 2 x) n) (* 2 (ash x n))))
  :hints (("goal" :in-theory (enable ash))))

(in-theory (disable ash-*2-simplify))

(defthm *ark*-ifix-ash
  (equal (ifix (ash x y)) (ash x y)))

(defthm *ark*-open-logcons
  (implies (syntaxp (constant-syntaxp b))
           (equal (logcons b i)
                  (let ((b (bfix b)) (i (ifix i)))
                    (+ b (* 2 i)))))
  :hints
  (("goal" :in-theory (enable logcons))))

(defthm *ark*-sum-constants
  (implies (and (syntaxp (constant-syntaxp x))
                (syntaxp (constant-syntaxp y))
                (equal sum (+ x y)))
           (equal (+ x y z) (+ sum z))))

(defthm *ark*-ash-+-pos
  (implies (and (integerp x)
                (integerp y)
                (integerp m)
                (<= 0 m))
           (equal (ash (+ x y) m)
                  (+ (ash x m) (ash y m))))
  :hints
  (("goal" :in-theory
    (enable logops-recursive-definitions-theory)
    :induct (sub1-induction m))))

(in-theory (disable *ARK*-ASH-+-POS))

(defthm logtail-+-ash
  (implies
   (and (integerp n1) (integerp n2) (integerp x) (integerp y)
        (<= 0 n1) (<= n1 n2) )
  (equal
   (logtail n1 (+ x (ash y n2)))
   (+ (logtail n1 x) (ash y (- n2 n1)))))
  :hints (("goal" :in-theory
           (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY logtail*)
           :induct (sub1-sub1-logcdr-induction n2 n1 x))))

(defthm logcdr-logapp
  (implies
   (and
    (integerp n)
    (integerp x)
    (integerp y)
    (< 0 n))
   (equal (logcdr (logapp n x y))
          (logapp (1- n) (logcdr x) y)))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-induction n x))))

(defthm logcdr-loghead
  (implies
   (and
    (integerp n)
    (integerp x)
    (< 0 n))
   (equal (logcdr (loghead n x))
          (loghead (1- n) (logcdr x))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-induction n x))))


(defthm *ark*-logcar-i+j+2*k
     (implies
      (and (integerp i)
           (integerp j)
           (integerp k))
      (equal (logcar (+ i j (* 2 k)))
             (logcar (+ i j))))
     :hints
     (("Goal"
       :use ((:instance logcar-i+2*j (i (+ i j)) (j k))))))

(defthm *ark*-logcar-+
     (implies
      (and (integerp i)
           (integerp j))
      (equal (logcar (+ i j))
             (b-xor (logcar i) (logcar j))))
     :hints
     (("Goal" :in-theory (enable b-xor))))

(defthm *ark*-loghead-1
  (implies
   (integerp x)
   (equal (loghead 1 x) (logcar x)))
  :hints (("goal" :in-theory (enable loghead logcons))))

(defthm unsigned-byte-p-+
  (implies
   (and
    (unsigned-byte-p n x)
    (unsigned-byte-p n y))
   (unsigned-byte-p (1+ n) (+ x y)))
  :hints (("goal" :in-theory (enable unsigned-byte-p expt))))

(defthm unsigned-byte-p-logcdr-bridge
  (implies
   (unsigned-byte-p 9 x)
   (unsigned-byte-p 8 (logcdr x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-logcdr-bridge-2
  (implies
   (unsigned-byte-p 8 x)
   (unsigned-byte-p 7 (logcdr x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defthm *ark*-+*
  (implies
   (and (not (zip a)) (not (equal a -1))
        (not (zip b)))
   (equal
    (+ a b)
    (logcons
     (b-xor (logcar a) (logcar b))
     (+ (b-and (logcar a) (logcar b))
        (logcdr a) (logcdr b)))))
   :hints (("goal" :induct (logcdr-logcdr-induction a b)
            :in-theory (e/d (LOGOPS-RECURSIVE-DEFINITIONS-THEORY b-and b-xor)

; Modified April 2016 by Matt K. upon the addition of a type-set bit for the
; set {1}.  (Same change made in books/coi/super-ihs/super-ihs.lisp.)

                            (BITP-COMPOUND-RECOGNIZER)))))

(in-theory (disable *ark*-+*))

(defthm *ark*-logcdr-+1
  (implies
   (integerp x)
  (and
   (implies
    (equal (logcar x) 0)
    (equal (logcdr (+ 1 x)) (logcdr x)))
   (implies
    (equal (logcar x) 1)
    (equal (logcdr (+ 1 x)) (+ 1 (logcdr x))))
   (implies
    (and
     (equal (logcar x) 1)
     (integerp y))
    (equal (logcdr (+ 1 x y)) (+ 1 (logcdr x) (logcdr y))))
   (implies
    (and
     (equal (logcar x) 1)
     (integerp y))
    (equal (logcdr (+ 1 y x)) (+ 1 (logcdr x) (logcdr y))))))
  :hints (("goal" :in-theory (enable *ark*-+*))))

(defthm unsigned-byte-p-+-helper
  (implies
   (and
    (unsigned-byte-p n x)
    (unsigned-byte-p n y)
    (unsigned-byte-p 1 c)
    (integerp n)
    (< 0 n))
   (equal
    (unsigned-byte-p n (+ x y c))
    (not (logbitp n (+ x y c)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable logops-recursive-definitions-theory *ark*-+* logbitp*)
           :induct (sub1-logcdr-logcdr-carry-induction n x y c))))

(defthm *ark*-unsigned-byte-p-+
  (implies
   (and
    (unsigned-byte-p n x)
    (unsigned-byte-p n y)
    (integerp n)
    (< 0 n))
   (equal
    (unsigned-byte-p n (+ x y))
    (not (logbitp n (+ x y)))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-helper (c 0)))))

(in-theory (disable associativity-of-logapp))

;; Super-IHS associates logapp in a way that now seems backwards to
;; me.  I shut off associativity-of-logapp, and prove a rule that
;; works "forwards", just to keep myself sane.
(defthm logapp-logapp
  (implies
   (and
    (integerp n1) (integerp n2)
    (integerp a) (integerp b) (integerp c)
    (<= 0 n2) (<= n2 n1))
   (equal
    (logapp n1 (logapp n2 a b) c)
    (logapp n2 a (logapp (- n1 n2) b c))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-sub1-logcdr-induction n1 n2 a))))

(defthm equal-logapp-x
  (implies
   (and (integerp n) (integerp x) (integerp y) (integerp z) (<= 0 n)
        (equal (loghead n z) (loghead n x)))
   (equal
    (equal (logapp n x y) z)
    (equal y (logtail n z))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-logcdr-induction n x z))))

(defthm loghead-+-simple
  (implies
   (and
    (integerp x) (integerp y) (integerp n)
    (<= 0 n)
    (equal (loghead n x) 0))
   (equal
    (loghead n (+ x y))
    (loghead n y)))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-logcdr-induction n x y))))

(defthm logtail-+-simple
  (implies
   (and
    (integerp x) (integerp y) (integerp n)
    (<= 0 n)
    (equal (loghead n x) 0))
   (equal
    (logtail n (+ x y))
    (+ (logtail n x) (logtail n y))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-logcdr-induction n x y))))

(defthm *ark*-loghead-ash-pos-rewrite
  (implies
   (and
    (integerp n1)
    (integerp n2)
    (integerp x)
    (<= 0 n1)
    (<= 0 n2))
  (equal (loghead n1 (ash x n2))
         (if (<= n1 n2)
             0
           (ash (loghead (- n1 n2) x) n2))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-sub1-induction n1 n2))))

(defthm logtail-ash-pos-rewrite
  (implies
   (and
    (integerp n1)
    (integerp n2)
    (integerp x)
    (<= 0 n1)
    (<= 0 n2))
  (equal (logtail n1 (ash x n2))
         (if (<= n1 n2)
             (ash x (- n2 n1))
           (logtail (- n1 n2) x))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-sub1-induction n1 n2))))

(defthm loghead-*2
  (implies
   (and
    (integerp n) (< 0 n) (integerp x))
   (equal
    (equal (loghead n (* 2 x)) 0)
    (equal (loghead (1- n) x) 0)))
  :hints (("goal" :in-theory (enable loghead*))))


(defthm logcar-identity
  (implies (unsigned-byte-p 1 x)
           (equal (logcar x) x))
  :hints
  (("goal" :in-theory
    (enable unsigned-byte-p logcar))))

(defthm unsigned-byte-p-logcar
  (unsigned-byte-p 1 (logcar x))
  :hints
  (("goal" :in-theory
    (enable unsigned-byte-p logcar))))

(defthm logapp-1-logcar-logcdr
  (implies
   (integerp x)
   (equal (logapp 1 (logcar x) (logcdr x))
          x))
  :hints (("goal" :in-theory (enable logapp))))

(defthm unsigned-byte-p-1-
  (implies
   (and
    (integerp n) (<= 0 n)
    (unsigned-byte-p n x))
   (equal
    (unsigned-byte-p n (1- x))
    (< 0 x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defthm +-ash-logapp
  (implies
   (and (integerp x) (integerp n) (integerp a) (integerp b)
        (<= 0 n))
   (equal (+ (ash x n) (logapp n a b))
          (logapp n a (+ x b))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (sub1-logcdr-induction n a))))

(defthm equal-logcar-1
  (equal (equal (logcar x) 1)
         (not (equal (logcar x) 0)))
  :hints (("goal" :in-theory (enable logcar))))

(defthm logapp-loghead
  (implies
   (and (integerp n1) (integerp n2) (integerp x) (integerp y)
        (<= 0 n1) (<= n1 n2))
   (equal
    (logapp n1 (loghead n2 x) y)
    (logapp n1 x y)))
  :hints (("goal" :induct (sub1-sub1-logcdr-induction n1 n2 x)
           :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm logtail-almost-all
  (implies
   (and
    (unsigned-byte-p (1+ n) x)
    (integerp n) (<= 0 n))
   (equal (logtail n x) (logbit n x)))
  :hints (("goal" :induct (sub1-logcdr-induction n x)
           :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY logbit))))

(defthm equal-x-logapp-x
  (implies
   (and (integerp x) (integerp y) (integerp n) (<= 0 n))
   (equal
    (equal x (logapp n x y))
    (equal (logtail n x) y)))
  :hints (("goal" :induct (sub1-logcdr-induction n x)
           :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm equal-x-loghead-x
  (implies
   (and (integerp x) (integerp n) (<= 0 n))
   (equal
    (equal x (loghead n x))
    (unsigned-byte-p n x)))
  :hints (("goal" :induct (sub1-logcdr-induction n x)
           :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm equal-logbit-logbit-logcdr-bridge
  (implies
   (and (integerp x) (integerp n) (<= 0 n))
   (equal
    (equal (logbit n (logcdr x)) (logbit (1+ n) x))
    t))
  :hints (("goal" :in-theory (enable logbit logbitp*))))

(defthm unsigned-byte-p-logcdr
  (implies
   (unsigned-byte-p n x)
   (unsigned-byte-p n (logcdr x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-1-logbit
  (unsigned-byte-p 1 (logbit n x))
  :hints (("goal" :in-theory (enable logbit))))

(defthm unsigned-byte-p-1-b-xor
  (unsigned-byte-p 1 (b-xor x y))
  :hints (("goal" :in-theory (enable b-xor))))

(defthm ash-0-arg2
  (implies
   (integerp x)
   (equal (ash x 0) x))
  :hints (("goal" :in-theory (enable ash))))

;;;;;;;;;;;;;;;;;;;;
;; Finally, we're ready to model the problem and do the proof...

;; We model the relevant parts of the Mostek 6502 state
(defstobj st
  (f1 :type (unsigned-byte 8) :initially 0)
  (f2 :type (unsigned-byte 8) :initially 0)
  (f1save :type (unsigned-byte 8) :initially 0)
  (a :type (unsigned-byte 8) :initially 0)
  (low :type (unsigned-byte 8) :initially 0)
  (cflg :type (unsigned-byte 1) :initially 0)
  (zflg :type (unsigned-byte 1) :initially 0)
  (x :type (unsigned-byte 8) :initially 0))

;; Now, we prove some rules about the types of the Mostek 6502 state.
;; Normally the following "type" lemmas would be generated
;; automatically by our READER, but we want to share this example
;; without distributing the READER so we take a shortcut: we steal
;; some automatically generated update/accessor lemmas from another
;; example that does use the READER and edit them a little.

;; Most of these are not necessary, but the simplest thing for me to
;; do is put them all in.  Fortunately, the state is small!

(DEFTHM F1-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 0 ST)) (<= (NTH 0 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP F1P)))))
(DEFTHM F1-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 0 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 0 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= F1P))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM F1-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 0 V ST)) (F1P V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM F1-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 0 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P F1P)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE F1-UPDATE-TYPE-HELPER)))

(DEFTHM F2-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 1 ST)) (<= (NTH 1 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP F2P)))))
(DEFTHM F2-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 1 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 1 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= F2P))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM F2-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 1 V ST)) (F2P V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM F2-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 1 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P F2P)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE F2-UPDATE-TYPE-HELPER)))
(DEFTHM F1SAVE-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 2 ST)) (<= (NTH 2 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP F1SAVEP)))))
(DEFTHM F1SAVE-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 2 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 2 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= F1SAVEP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM F1SAVE-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 2 V ST)) (F1SAVEP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM F1SAVE-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 2 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P F1SAVEP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE F1SAVE-UPDATE-TYPE-HELPER)))
(DEFTHM A-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 3 ST)) (<= (NTH 3 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP AP)))))
(DEFTHM A-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 3 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 3 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= AP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM A-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 3 V ST)) (AP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM A-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 3 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P AP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE A-UPDATE-TYPE-HELPER)))
(DEFTHM LOW-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 4 ST)) (<= (NTH 4 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP LOWP)))))
(DEFTHM LOW-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 4 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 4 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= LOWP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM LOW-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 4 V ST)) (LOWP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM LOW-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 4 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P LOWP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE LOW-UPDATE-TYPE-HELPER)))
(DEFTHM CFLG-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 5 ST)) (<= (NTH 5 ST) 1)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP CFLGP)))))
(DEFTHM CFLG-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 5 ST))
                      (UNSIGNED-BYTE-P 1 (NTH 5 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= CFLGP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM CFLG-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 5 V ST)) (CFLGP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM CFLG-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 5 V ST))
                      (UNSIGNED-BYTE-P 1 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P CFLGP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE CFLG-UPDATE-TYPE-HELPER)))
(DEFTHM ZFLG-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 6 ST)) (<= (NTH 6 ST) 1)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP ZFLGP)))))
(DEFTHM ZFLG-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 6 ST))
                      (UNSIGNED-BYTE-P 1 (NTH 6 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= ZFLGP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM ZFLG-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 6 V ST)) (ZFLGP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM ZFLG-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 6 V ST))
                      (UNSIGNED-BYTE-P 1 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P ZFLGP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE ZFLG-UPDATE-TYPE-HELPER)))
(DEFTHM X-LINEAR
        (IMPLIES (STP ST)
                 (AND (<= 0 (NTH 7 ST)) (<= (NTH 7 ST) 255)))
        :RULE-CLASSES (:LINEAR :REWRITE) :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(STP XP)))))
(DEFTHM X-TYPE
        (IMPLIES (STP ST)
                 (AND (INTEGERP (NTH 7 ST))
                      (UNSIGNED-BYTE-P 8 (NTH 7 ST))))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(SIGNED-BYTE-P-<= UNSIGNED-BYTE-P-<= XP))
          :EXPAND (STP ST)))
        :rule-classes (:rewrite :type-prescription))
(DEFTHM X-UPDATE-TYPE-HELPER
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 7 V ST)) (XP V)))
        :HINTS
        (("goal" :EXPAND (:FREE (X) (STP X)) :IN-THEORY
          (SET-DIFFERENCE-THEORIES (CURRENT-THEORY 'GROUND-ZERO)
              '(NTH UPDATE-NTH))))
        :RULE-CLASSES NIL)
(DEFTHM X-UPDATE-TYPE
        (IMPLIES (STP ST)
                 (IFF (STP (UPDATE-NTH 7 V ST))
                      (UNSIGNED-BYTE-P 8 V)))
        :HINTS
        (("goal" :IN-THEORY
          (UNION-THEORIES '(UNSIGNED-BYTE-P SIGNED-BYTE-P XP)
              (CURRENT-THEORY 'GROUND-ZERO))
          :USE X-UPDATE-TYPE-HELPER)))

;; We now model the algorithm contained in Legato's paper.  We use the
;; line numbers from page 7 of his note.

;; We use an awkward modeling style to avoid use of the reader.  This
;; means that

;; 1.  We employ IHS functions directly.  logapp, loghead, logtail,
;;     ash, logcdr, unsigned-byte-p etc. are all described in the IHS
;;     library that comes with the ACL2 distribution.
;; 2.  We employ an awkward, multiple-let-binding style.
;;
;; Note also that the Mostek 6502 microprocessor commands of this
;; program assume a big-endian byte, while we prefer a small-endian
;; style for proofs.  We model the operations how we like, but this
;; sometimes makes the model confusing.  Note for example that a
;; "right shift" command is implemented using the IHS function logcdr.

;; ldx #8
(defun line1 (st)
  (declare (xargs :stobjs st))
  (let ((st (update-x 8 st)))
    st))

;; lda #0
(defun line2 (st)
  (declare (xargs :stobjs st))
  (let ((st (update-a 0 st)))
    st))

; Added by Matt K. for v2-7; needed for several guard proofs below.
(local (in-theory (enable unsigned-byte-p logbitp)))

;; loop ror f1
(defun line3 (st)
  (declare (xargs :stobjs st
                  :guard-hints (("goal" :in-theory
                                 (enable logapp loghead logcar stp)))))
  (let ((temp (cflg st)))
    (let ((st (update-cflg (logcar (f1 st)) st)))
      (let ((st (update-f1 (logapp 7 (logcdr (f1 st)) temp) st)))
        st))))

;; bcc zcoef

;; clc
(defun line5 (st)
  (declare (xargs :stobjs st))
  (let ((st (update-cflg 0 st)))
    st))

;; adc f2 - set a to a + f2 + c
(defun line6 (st)
  (declare (xargs :stobjs st
                  :guard-hints (("goal" :in-theory
                                 (enable logapp loghead
                                         logcar logbit)))))
  (let ((temp (+ (a st) (f2 st) (cflg st))))
    (let ((st (update-a (loghead 8 temp) st)))
      (let ((st (update-cflg (logbit 8 temp) st)))
        st))))

;; zcoef ror a
(defun line7 (st)
  (declare (xargs :stobjs st
                  :guard-hints (("goal" :in-theory
                                 (enable logapp loghead logcar)))))
  (let ((temp (cflg st)))
    (let ((st (update-cflg (logcar (a st)) st)))
      (let ((st (update-a (logapp 7 (logcdr (a st)) temp) st)))
        st))))

;; ror low
(defun line8 (st)
  (declare (xargs :stobjs st
                  :guard-hints (("goal" :in-theory
                                 (enable logapp loghead logcar)))))
  (let ((temp (cflg st)))
    (let ((st (update-cflg (logcar (low st)) st)))
      (let ((st (update-low (logapp 7 (logcdr (low st)) temp) st)))
        st))))

;; dex
(defun line9 (st)
  (declare (xargs :stobjs st
                  :guard-hints (("goal" :in-theory
                                 (enable logapp loghead logcar)))))
  (let ((temp (loghead 8 (1- (x st)))))
    (let ((st (update-zflg (if (equal temp 0) 1 0) st)))
      (let ((st (update-x temp st)))
        st))))

;; bne loop

;;; Now, compose line models into a program
(defun multloop (st)
  (declare (xargs :stobjs st
                  :measure (nfix (x st))
                  :hints (("goal" :in-theory
                           (enable unsigned-byte-p nfix)))))
  (if (and (integerp (x st)) (< 0 (x st)))
      (let ((st (line3 st)))
        (let ((st (if (equal (cflg st) 1)
                      (let ((st (line5 st)))
                        (line6 st))
                    st)))
          (let ((st (line7 st)))
            (let ((st (line8 st)))
              (let ((st (line9 st)))
                (if (equal (zflg st) 0)
                    (multloop st)
                  st))))))
    st))

(defun multprog (st)
  (declare (xargs :stobjs st))
  (let ((st (line1 st)))
    (let ((st (line2 st)))
      (multloop st))))

;; Here's the result of the computation - a 16 bit product that winds
;; up in two 8-bit registers.
(defun result (st)
  (declare (xargs :stobjs st))
  (logapp 8 (low st) (a st)))

#|

Let's test our program!

ACL2 !>:q

Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
ACL2>(update-f2 79 st)
(#(0) #(79) #(0) #(0) #(0) #*0 #*0 #(0))

ACL2>(update-f1 84 st)
(#(84) #(79) #(0) #(0) #(0) #*0 #*0 #(0))

ACL2>(multprog st)
(#(0) #(79) #(0) #(25) #(236) #*0 #*1 #(0))

ACL2>(result st)
6636

ACL2>(* 79 84)
6636

ACL2>

|#

(in-theory (disable stp))

;; We're finally ready to do the proof.

;; The following rules instruct the prover to open up the
;; multiplication in a way consistent with how the 6502 program
;; calculates the product.

(defthm ash-*-casesplit-v1
  (implies
   (and
    (equal (logcar x) 0)
    (integerp x) (integerp y) (integerp n) (<= 0 n))
   (equal (ash (* y x) n) (ash (* y (logcdr x)) (1+ n))))
  :hints (("goal" :in-theory (enable ash-*2-simplify ash*))))

(defthm ash-*-casesplit-v2
  (implies
   (and
    (equal (logcar x) 1)
    (integerp x) (integerp y) (integerp n) (<= 0 n))
   (equal (ash (* y x) n) (+ (ash y n) (ash (* y (logcdr x)) (1+ n)))))
  :hints (("goal" :in-theory
           (enable *ARK*-ASH-+-POS ash-*2-simplify ash*))))

(defthm *-logcar-casesplit
  (implies
   (and (integerp x) (integerp y))
   (equal
    (* (logcar x) y)
    (if (equal (logcar x) 0) 0 y)))
  :hints (("goal" :in-theory (enable logcar))))

;; The symbolic result of the loop leaves our result a mess.  We use
;; this rule to put the result "back together" again so that we can
;; reason about the effect of one iteration of the loop.
(defthm +-reconstruct-bridge
  (implies
   (and
    (equal (logcdr (+ x y)) z)
    (integerp x) (integerp y))
   (equal
    (logapp
     1
     (b-xor (logcar x) (logcar y))
     z)
    (+ x y)))
  :hints (("goal" :in-theory (enable logapp*))))

;; simplify result function if the upper byte is set to 0
(defthm result-update-nth
  (implies
   (stp st)
   (equal
    (result (update-nth 3 0 st))
    (low st))))

; Added by Matt K. for v2-7:
(local (in-theory (disable unsigned-byte-p logbitp)))

;; Prove that the loop works.  Note that the theorem's conclusion is a
;; generalization of the needed behavior that allows for induction.
(defthm loop-works
  (implies
   (and
    (stp st)
    (<= (x st) 8))
   (equal (result (multloop st))
          (+
           (logtail (x st) (result st))
           (ash (* (loghead (x st) (f1 st)) (f2 st)) (- 8 (x st))))))
  :hints (("goal" :in-theory (enable logtail* logbitp* ash*))))

;; With the loop proved, the program's proof is straightforward.
(defthm prog-works
  (implies
   (stp st)
   (equal (result (multprog st))
          (* (f1 st) (f2 st))))
  :hints (("goal" :in-theory (disable multloop result))))

