; logops-definitions.lisp  --  extensions to Common Lisp logical operations
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    "logops-definitions.lisp"
;;;
;;;    This book, along with "logops-lemmas", includes a theory of the Common
;;;    Lisp logical operations on numbers, a portable implementation of the
;;;    Common Lisp byte operations, extensions to those theories, and some
;;;    useful macros.  This book contains only definitions, lemmas
;;;    necessary to admit those definitions, and selected type lemmas.
;;;
;;;    Large parts of this work were inspired by Yuan Yu's Nqthm
;;;    specification of the Motorola MC68020.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;    Modified for ACL2 Version_2.6 by:
;;;    Jun Sawada, IBM Austin Research Lab. sawada@us.ibm.com
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;    Modified for ACL2 Version_2.7 by:
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;    Modified July 2012 by Jared Davis <jared@centtech.com>
;;;    Moved many definitions into new basic-definitions.lisp file.
;;;
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")
;;;  Global rules.

(include-book "ihs-init")
(include-book "ihs-theories")
(include-book "std/util/defval" :dir :system)

(local (include-book "math-lemmas"))
(local (include-book "quotient-remainder-lemmas"))

; From ihs-theories
(local (in-theory (enable basic-boot-strap)))

; From math-lemmas
(local (in-theory (enable ihs-math)))

; From integer-quotient-lemmas
(local (in-theory (enable quotient-remainder-rules)))

(local (in-theory (disable floor mod)))

(deflabel begin-logops-definitions)

(include-book "basic-definitions")


;;;****************************************************************************
;;;
;;;    Local Lemmas.
;;;
;;;****************************************************************************

(local (defthm x*y->-1
         (implies (and (force (real/rationalp x))
                       (force (real/rationalp y))
                       (or (and (> x 1) (>= y 1))
                           (and (>= x 1) (> y 1))))
                  (> (* x y) 1))
         :rule-classes :linear
         :hints (("Goal"
                  :in-theory (enable x*y>1-positive)
                  :cases ((equal y 1)
                          (equal x 1))))))

(local (defthm x*y->=-1
         (implies (and (force (real/rationalp x))
                       (force (real/rationalp y))
                       (>= x 1)
                       (>= y 1))
                  (>= (* x y) 1))
         :rule-classes :linear
         :hints (("Goal" :in-theory (disable <-*-left-cancel
                                             commutativity-of-*)
                  :use ((:instance <-*-left-cancel (z y) (x 1) (y x)))))))

(local (defthm x-<-y*z
         (implies (and (force (real/rationalp x))
                       (force (real/rationalp y))
                       (force (real/rationalp z))
                       (or (and (<= 0 y) (< x y) (<= 1 z))
                           (and (< 0 y) (<= x y) (< 1 z))))
                  (and (< x (* y z))
                       (< x (* z y))))
         :hints (("Goal" :in-theory (disable <-*-left-cancel <-y-*-y-x)
                  :use ((:instance <-*-left-cancel (z y) (x 1) (y z)))))))

(local (defthm x-<=-y*z
         (implies (and (force (real/rationalp x))
                       (force (real/rationalp y))
                       (force (real/rationalp z))
                       (<= x y)
                       (<= 0 y)
                       (<= 1 z))
                  (and (<= x (* y z))
                       (<= x (* z y))))
         :hints (("Goal" :in-theory (disable <-*-left-cancel <-y-*-y-x)
                  :use ((:instance <-*-left-cancel (z y) (x 1) (y z)))))))

;; [Jared]: I eliminated the type-prescription rules saying logand, logandc1,
;; and logandc2 produce integers, since ACL2 now automatically knows this.

;; [Jared]: I moved definitions like bitp, bfix, etc., into
;; basic-definitions.lisp.

(defsection bitp-basics
  :parents (bitp)

  ;; [Jared] 2016-04-08: I think we shouldn't need this now that bitp is
  ;; more deeply known to type-set.
  ;; (defthm bitp-forward
  ;;   (implies (bitp i)
  ;;            (and (integerp i)
  ;;                 (>= i 0)
  ;;                 (< i 2)))
  ;;   :rule-classes :forward-chaining)

  (defthm bitp-mod-2
    (implies (integerp i)
             (bitp (mod i 2)))
    :rule-classes ((:rewrite)
                   (:generalize :corollary (implies (integerp i)
                                                    (or (equal (mod i 2) 0)
                                                        (equal (mod i 2) 1)))))
    :hints (("Goal" :in-theory (enable linearize-mod)))))

(local (in-theory (enable unsigned-byte-p signed-byte-p integer-range-p)))
(local (in-theory (disable bitp)))
(local (in-theory (disable bfix)))


(defsection unsigned-byte-p-basics
  :parents (unsigned-byte-p)

  (defthm unsigned-byte-p-forward
    (implies (unsigned-byte-p bits i)
             (and (integerp i)
                  (>= i 0)
                  (< i (expt 2 bits))))
    :rule-classes :forward-chaining)

  (defthmd unsigned-byte-p-unsigned-byte-p
    (implies (and (unsigned-byte-p size i)
                  (integerp size1)
                  (>= size1 size))
             (unsigned-byte-p size1 i))
    :hints (("Goal" :in-theory (disable expt-is-weakly-increasing-for-base>1)
             :use ((:instance expt-is-weakly-increasing-for-base>1
                    (r 2) (i size) (j size1)))))))

(local (in-theory (disable unsigned-byte-p)))

(defxdoc unsigned-byte-p-discussion
  :parents (unsigned-byte-p)
  :short "Discussion on how to use unsigned-byte-p"
  :long "<p>@(csee unsigned-byte-p) (and @(see signed-byte-p) for that matter) are
  tricky enough that there is no one-size-fits-all solution that everyone
  should use to reason about them.  Depending on your problem you might try any
  of these strategies:</p>

  <ol>

  <li><i>Arithmetic</i> -- Leave unsigned-byte-p's regular definition enabled
  and try to reason about the resulting inequalities.  This sometimes works and
  may be a good approach if you have goals involving \"non bit-vector
  functions\" like +, *, /, etc.  I usually don't use this approach but I
  haven't done a lot of proofs about true arithmetic functions.</li>

  <li><i>Induction</i> -- Disable unsigned-byte-p's regular definition but
  instead enable an alternate definition, e.g., the
  centaur/bitops/ihsext-basics book has unsigned-byte-p**, which is a recursive
  version that works well for induction.  This definition is in the
  ihsext-recursive-redefs ruleset and also works well with other ** definitions
  like logand**.  This is often a good strategy when proving lemmas about
  unsigned-byte-p but is probably mainly useful when reasoning about new
  recursive functions.</li>

  <li><i>Vector</i> -- Leave @(see unsigned-byte-p) disabled except to prove
  lemmas, and expect to reason about (unsigned-byte-p n x) via lemmas.  I think
  I usually prefer this strategy as it feels more reliable/less magical than
  reasoning about arithmetic inequalities.  Some useful books:

    <ol>

      <li>bitops/ihsext-basics proves the nice/obvious lemmas about
      signed/unsigned-byte-p on many bit-vector functions like logior,
      logand, etc.</li>

      <li>bitops/signed-byte-p has lemmas about signed/unsigned-byte-p for
      some arithmetic functions (+, -, *) and also extended lemmas about
      bit-vector stuff.  It's often very handy for the kinds of guard
      obligations that arise from things like (the (unsigned-byte 32)
      x).</li>

    </ol></li>
  </ol>

  <p>We have occasionally written wrapper functions like @('u32p'), but, I
  think that perhaps the only reason we did this was for macros like @(see
  def-typed-record), where we needed a unary predicate to introduce a fancier
  data structure.  Once we had the typed records in place, we just enabled
  these wrappers and did all our reasoning about @(see unsigned-byte-p).
  (I don't think you'd want to reason about a each various u32p, u64p, etc.,
  individually.)</p>

  <p>In the context of FTY, I don't think you need wrappers, but if for some
  reason you do want to use them then that is probably basically fine.  Note
  here that you have some choice for your fixing function.  You can fix to 0 as
  you've done in your examples, but you might instead prefer to fix to
  @'(loghead n x)').  Why?  When you use loghead, it preserves the lower @('N')
  bits, and this may interact much more nicely with rules about true bit-vector
  functions.  This approach is also good for GL, where loghead is supported in
  an especially good way.</p>

  <p>That said, it should be possible to get by without wrappers; see for
  instance the definition of sizednum in centaur/fty/deftypes-tests.lisp, or
  the definition of vl-constint in centaur/vl/expr.lisp, both of which use a
  loghead-based approach to do the fixing.  (The vl-constint example has
  a :require that is an inequality instead of an unsigned-byte-p term, but I
  don't think there's any particular reason to do it this way instead of the
  other.)</p>

  <p>In general there is good reason to expect it to sometimes be hard to work
  with unsigned-byte-p.  For instance, consider a theorem like the following,
  from @('centaur/bitops/signed-byte-p.lisp'):</p>

  @({
   (defthm lousy-unsigned-byte-p-of-*-mixed
     ;; Probably won't ever unify with anything.
     (implies (and (unsigned-byte-p n1 a)
                   (unsigned-byte-p n2 b))
              (unsigned-byte-p (+ n1 n2) (* a b)))
     :hints((\"Goal\" :use ((:instance upper-bound)))))
  })

  <p>This would be a good rule to try on goals like @('(unsigned-byte-p 10 (* a
  b))'), but without some insight into @('a') and @('b') it's hard to know how
  to successfully instantiate @('N1/N2').  So you end up resorting to @(':use')
  hints, or special-case variants of this theorem (e.g., another theorem that
  says 7 bits * 3 bits --&gt; 10 bits), or you do something more sophisticated
  with bind-free or similar.</p>

  <p>If you find yourself going down this road, you might see in particular Dave
  Greve's \"Parameterized Congruences\" paper from the 2006 workshop, which is
  implemented in the coi/nary/nary.lisp book.  You could also look at Sol
  Swords' book to do something similar, see @(see contextual-rewriting).</p>")


(defsection signed-byte-p-basics
  :parents (signed-byte-p)

  (defthm signed-byte-p-forward
    (implies (signed-byte-p bits i)
             (and (integerp i)
                  (>= i (- (expt 2 (- bits 1))))
                  (< i (expt 2 (- bits 1)))))
    :rule-classes :forward-chaining))

(local (in-theory (disable signed-byte-p)))


;; [Jared]: I moved definitions like ifloor, expt, logcar, logbit, etc., into
;; basic-definitions.lisp.  I also moved the most basic type theorems.  But I
;; didn't move various theorems about these functions, e.g., bounds theorems,
;; and I didn't move the guard macros.


;;;Matt: You will find instances of these throughout "logops-lemmas". These
;;;should all be redundant now, but in case they aren't I'll leave them in.

(defsection logbit-guard
  :parents (logops-definitions)
  :short "@(call logbit-guard) is a macro form of the guards for @(see logbit)."

  (defmacro logbit-guard (pos i)
    `(and (force (integerp ,pos))
          (force (>= ,pos 0))
          (force (integerp ,i)))))

(defsection logmask-guard
  :parents (logops-definitions)
  :short "@(call logmask-guard) is a macro form of the guards for @(see logmask)."

  (defmacro logmask-guard (size)
    `(and (force (integerp ,size))
          (force (>= ,size 0)))))

(defsection loghead-guard
  :parents (logops-definitions)
  :short "@(call loghead-guard) is a macro form of the guards for @(see loghead)."

  (defmacro loghead-guard (size i)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i)))))

(defsection logtail-guard
  :parents (logops-definitions)
  :short "@(call logtail-guard) is a macro form of the guards for @(see logtail)."

  (defmacro logtail-guard (pos i)
    `(and (force (integerp ,pos))
          (force (>= ,pos 0))
          (force (integerp ,i)))))

(defsection logapp-guard
  :parents (logops-definitions)
  :short "@(call logapp-guard) is a macro form of the guards for @(see logapp)."

  (defmacro logapp-guard (size i j)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i))
          (force (integerp ,j)))))

(defsection logrpl-guard
  :parents (logops-definitions)
  :short "@(call logrpl-guard) is a macro form of the guards for @(see logrpl)."

  (defmacro logrpl-guard (size i j)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i))
          (force (integerp ,j)))))

(defsection logext-guard
  :parents (logops-definitions)
  :short "@(call logext-guard) is a macro form of the guards for @(see logext)."

  (defmacro logext-guard (size i)
    `(and (force (integerp ,size))
          (force (> ,size 0))
          (force (integerp ,i)))))

(defsection logrev-guard
  :parents (logops-definitions)
  :short "@(call logrev-guard) is a macro form of the guards for @(see logrev)."

  (defmacro logrev-guard (size i)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i)))))

(defsection logextu-guard
  :parents (logops-definitions)
  :short "@(call logextu-guard) is a macro form of the guards for @(see logextu)."

  (defmacro logextu-guard (final-size ext-size i)
    `(and (force (integerp ,final-size))
          (force (>= ,final-size 0))
          (force (integerp ,ext-size))
          (force (> ,ext-size 0))
          (force (integerp ,i)))))

(defsection lognotu-guard
  :parents (logops-definitions)
  :short "@(call lognotu-guard) is a macro form of the guards for @(see lognotu)."

  (defmacro lognotu-guard (size i)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i)))))

(defsection ashu-guard
  :parents (logops-definitions)
  :short "@(call ashu-guard) is a macro form of the guards for @(see ashu)."

  (defmacro ashu-guard (size i cnt)
    `(and (force (integerp ,size))
          (force (> ,size 0))
          (force (integerp ,i))
          (force (integerp ,cnt)))))

(defsection lshu-guard
  :parents (logops-definitions)
  :short "@(call lshu-guard) is a macro form of the guards for @(see lshu)."

  (defmacro lshu-guard (size i cnt)
    `(and (force (integerp ,size))
          (force (>= ,size 0))
          (force (integerp ,i))
          (force (integerp ,cnt)))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Type Lemmas for the new LOGOPS.  Each function is DISABLEd after we
;;;    have enough information about it (except for IFLOOR, IMOD, and EXPT2,
;;;    which are considered abbreviations).  We prove even the most obvious
;;;    type lemmas because you never know what theory this book will be
;;;    loaded into, and unless the theory is strong enough you may not get
;;;    everthing you need.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(local (in-theory (disable logcar)))

(defsection logcdr-basics
  :parents (logcdr)

  (defthm logcdr-<-0
    (equal (< (logcdr i) 0)
           (and (integerp i)
                (< i 0))))

  (defthm justify-logcdr-induction
    (and (implies (> i 0)
                  (< (logcdr i) i))
         (implies (< i -1)
                  (< i (logcdr i))))
    :hints (("Goal" :in-theory (enable logcdr)))))

(local (in-theory (disable logcdr)))


(defsection logcons-basics
  :parents (logcons)

  (defthm logcons-<-0
    (equal (< (logcons b i) 0)
           (and (integerp i)
                (< i 0)))
    :hints (("Goal" :in-theory (enable bfix)))))

(local (in-theory (disable logcons)))


(local (in-theory (disable logmaskp)))

;;;  LOGHEAD

(defsection loghead-basics
  :parents (loghead)

  (defthm unsigned-byte-p-loghead
    (implies (and (>= size1 size)
                  (integerp size)
                  (>= size 0)
                  (integerp size1))
             (unsigned-byte-p size1 (loghead size i)))
    :hints (("Goal" :in-theory (e/d (unsigned-byte-p)
                                    (expt-is-weakly-increasing-for-base>1))
             :use ((:instance expt-is-weakly-increasing-for-base>1
                    (r 2) (i size) (j size1))))))

  (defthm loghead-upper-bound
    (< (loghead size i) (expt 2 size))
    :rule-classes (:linear :rewrite)))


(defmacro lloghead (n x)
  ;; bozo maybe should be a function?
  ;; Useful for guard of (unsigned-byte-p n x).
  `(mbe :logic (loghead ,n ,x)
        :exec ,x))


(local (in-theory (disable loghead)))

(local (in-theory (disable logtail)))

(defsection logapp-basics
  :parents (logapp)

  (defthm logapp-<-0
    (implies (logapp-guard size i j)
             (equal (< (logapp size i j) 0)
                    (< j 0)))
    :hints (("Goal"
             :in-theory (e/d (loghead) (x-<-y*z))
             :use ((:instance x-<-y*z
                    (x (mod i (expt 2 size)))
                    (y (expt 2 size)) (z (abs j))))))))

(local (in-theory (disable logapp)))

(local (in-theory (disable logrpl)))


;;;4 Misplaced Lemmas
(defthm expt-with-violated-guards
  (and (implies (not (integerp i))
                (equal (expt r i) 1))
       (implies (not (acl2-numberp r))
                (equal (expt r i)
                       (expt 0 i))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm reduce-integerp-+-constant
  (implies (and (syntaxp (constant-syntaxp i))
                (integerp i))
           (iff (integerp (+ i j))
                (integerp (fix j)))))

(defthm how-could-this-have-been-left-out??
  (equal (* 0 x) 0))

(defthm this-needs-to-be-added-to-quotient-remainder-lemmas
  (implies (zerop y)
           (equal (mod x y)
                  (fix x)))
  :hints (("Goal" :in-theory (enable mod))))

(defsection logext-basics
  :parents (logext)

  (defthm logext-bounds
    (implies (< 0 size)
             (and (>= (logext size i) (- (expt 2 (1- size))))
                  (< (logext size i) (expt 2 (1- size)))))
    :rule-classes ((:linear :trigger-terms ((logext size i)))
                   (:rewrite))
    :hints (("Goal"
             :in-theory (e/d (logapp loghead)
                             (expt-is-increasing-for-base>1 exponents-add))
             :use ((:instance expt-is-increasing-for-base>1
                    (r 2) (i (1- size)) (j size))))))

  (defthm signed-byte-p-logext
    (implies (and (>= size1 size)
                  (> size 0)
                  (integerp size1)
                  (integerp size))
             (signed-byte-p size1 (logext size i)))
    :hints (("Goal"
             :in-theory (e/d (signed-byte-p logapp loghead)
                             (expt-is-weakly-increasing-for-base>1 exponents-add))
             :do-not '(eliminate-destructors)
             :use ((:instance expt-is-weakly-increasing-for-base>1
                    (r 2) (i (1- size)) (j (1- size1))))))))

(local (in-theory (disable logext)))


(defsection logrev-basics
  :parents (logrev)

  (local
   (defun crock-induction (size size1 i j)
     (cond
      ((zp size) (+ size1 i j))		;To avoid irrelevance
      (t (crock-induction (1- size) (1+ size1) (logcdr i)
			  (logcons (logcar i) j))))))

  ;; This lemma could have used one of the deleted Type-Prescriptions, I
  ;; think the one for LOGCDR.

  (local
   (defthm unsigned-byte-p-logrev1
     (implies
      (and (unsigned-byte-p size1 j)
	   (integerp size)
	   (>= size 0))
      (unsigned-byte-p (+ size size1) (logrev1 size i j)))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (e/d (expt logcar logcons unsigned-byte-p) (exponents-add))
       :induct (crock-induction size size1 i j)))))

  (defthm unsigned-byte-p-logrev
    (implies
     (and (>= size1 size)
	  (>= size 0)
	  (integerp size)
	  (integerp size1))
     (unsigned-byte-p size1 (logrev size i)))
    :hints
    (("Goal"
      :use ((:instance unsigned-byte-p-logrev1
		       (size size) (size1 0) (i i) (j 0))
	    (:instance unsigned-byte-p-unsigned-byte-p
		       (size size) (size1 size1) (i (logrev size i))))))))

(local (in-theory (disable logrev)))


(defsection logsat-basics
  :parents (logsat)

  ;; Added for Version_2.6.  Without it the following defthm appears to loop,
  ;; though not within a single goal -- rather, by creating subgoal after subgoal
  ;; after ....
  (local (in-theory (enable exponents-add-unrestricted)))

  (defthm logsat-bounds
    (implies (< 0 size)
             (and (>= (logsat size i) (- (expt 2 size)))
                  (< (logsat size i) (expt 2 size))))
    :rule-classes ((:linear :trigger-terms ((logsat size i)))
                   (:rewrite)))

  ;; Now we disable this rule; necessary for signed-byte-p-logsat.
  (local (in-theory (disable exponents-add-unrestricted)))

  (defthm signed-byte-p-logsat
    (implies (and (>= size1 size)
                  (> size 0)
                  (integerp size1)
                  (integerp size))
             (signed-byte-p size1 (logsat size i)))
    :hints (("Goal" :in-theory (e/d (signed-byte-p)
                                    (expt-is-weakly-increasing-for-base>1 exponents-add))
             :do-not '(eliminate-destructors)
             :use ((:instance expt-is-weakly-increasing-for-base>1
                    (r 2) (i (1- size)) (j (1- size1))))))))

(local (in-theory (disable logsat)))


(defsection logextu-basics
  :parents (logextu)

  (defthm unsigned-byte-p-logextu
    (implies (and (>= size1 final-size)
                  (>= final-size 0)
                  (integerp final-size)
                  (integerp size1))
             (unsigned-byte-p size1 (logextu final-size ext-size i)))))

(local (in-theory (disable logextu)))



(defsection lognotu-basics
  :parents (lognotu)

  (defthm unsigned-byte-p-lognotu
    (implies (and (>= size1 size)
                  (>= size 0)
                  (integerp size)
                  (integerp size1))
             (unsigned-byte-p size1 (lognotu size i)))))

(local (in-theory (disable lognotu)))


(defsection ashu-basics
  :parents (ashu)

  (defthm unsigned-byte-p-ashu
    (implies (and (>= size1 size)
                  (>= size 0)
                  (integerp size)
                  (integerp size1))
             (unsigned-byte-p size1 (ashu size i cnt)))))

(local (in-theory (disable ashu)))


(defsection lshu-basics
  :parents (lshu)

  (defthm unsigned-byte-p-lshu
    (implies (and (>= size1 size)
                  (>= size 0)
                  (integerp size)
                  (integerp size1))
             (unsigned-byte-p size1 (lshu size i cnt)))))

(local (in-theory (disable lshu)))


;;;****************************************************************************
;;;
;;;    DEFINITIONS -- Round 3.
;;;
;;;    A portable implementation and extension of the CLTL byte operations.
;;;    After the function definitions, we introduce a guard macro for those
;;;    with non-trivial guards.
;;;
;;;  BSP size pos
;;;  BSPP bsp
;;;  BSP-SIZE bsp
;;;  BSP-POS bsp
;;;  RDB bsp i
;;;  WRB i bsp j
;;;  RDB-TEST bsp i
;;;  RDB-FIELD bsp i
;;;  WRB-FIELD i bsp j
;;;
;;;****************************************************************************

(defxdoc logops-byte-functions
  :parents (logops-definitions)
  :short "A portable implementation and extension of Common Lisp byte
  functions."

  :long "<p>The proposed Common Lisp standard [<a
href='http://en.wikipedia.org/wiki/X3J13'>X3J13</a> Draft 14.10] defines a
number of functions that operate on subfields of integers.  These subfields are
specified by @('(BYTE size position)'), which \"indicates a byte of width size
and whose bits have weights @($2^{position+size-1}$) through @($2^{pos}$), and
whose representation is implementation dependent\".  Unfortunately, the
standard does not specify what BYTE returns, only that whatever is returned is
understood by the byte manipulation functions LDB, DPB, etc.</p>

<p>This lack of complete specification makes it impossible for ACL2 to specify
the byte manipulation functions of Common Lisp in a portable way.  For example
AKCL uses @('(cons size position)') as a byte specifier, whereas another
implementation might use a special data structure to represent @('(byte size
position)').  Since any theorem about the ACL2 built-ins is meant to be a
theorem for all Common Lisp implementations, ACL2 cannot define BYTE.</p>

<p>Therefore, we have provided a portable implementation of the byte operations
specified by the draft standard.  This behavior of this implementation should
be consistent with every Common Lisp that provides the standard byte
operations.  Our byte specifier @('(bsp size pos)') is analogous to CLTL's
@('(byte size pos)'), where size and pos are nonnegative integers.  Note that
the standard indicates that reading a byte of size 0 returns 0, and writing a
byte of size 0 leaves the destination unchanged.</p>

<p>This table indicates the correspondance between the Common Lisp byte
operations and our portable implementation:</p>

@({
  Common Lisp                               This Implementation
  ------ ----                               ---- --------------

  (BYTE size position)                      (BSP size position)
  (BYTE-SIZE bytespec)                      (BSP-SIZE bsp)
  (BYTE-POSITION bytespec)                  (BSP-POSITION bsp)
  (LDB bytespec integer)                    (RDB bsp integer)
  (DPB newbyte bytespec integer)            (WRB newbyte bsp integer)
  (LDB-TEST bytespec integer)               (RDB-TEST bsp integer)
  (MASK-FIELD bytespec integer)             (RDB-FIELD bsp integer)
  (DEPOSIT-FIELD newbyte bytespec integer)  (WRB-FIELD newbyte bsp integer)
})

<p>For more information, see the documentation for the functions listed above.
If you are concerned about the efficiency of this implementation, see the file
@('ihs/logops-efficiency-hack.lsp') for some notes.</p>")

(defsection bsp
  :parents (logops-byte-functions)
  :short "@(call bsp) returns a byte-specifier."
  :long "<p>This specifier designates a byte whose width is size and whose bits have
weights 2^(pos) through 2^(pos+size-1). Both size and pos must be
nonnegative integers.</p>

<p>BSP is mnemonic for Byte SPecifier or Byte Size and Position, and is
analogous to Common Lisp's @('(byte size position)').</p>

<p>BSP is implemented as a macro for simplicity and convenience.  One should
always use BSP in preference to CONS, however, to ensure compatibility with
future releases.</p>

@(def bsp)"

  (defmacro bsp (size pos)
    `(cons ,size ,pos)))

(define bspp (bsp)
  :parents (logops-byte-functions)
  :short "@(call bspp) recognizes objects produced by @(see bsp)."
  :returns bool
  :enabled t
  (and (consp bsp)
       (integerp (car bsp))
       (>= (car bsp) 0)
       (integerp (cdr bsp))
       (>= (cdr bsp) 0))
  ///
  (defthm bspp-bsp
    (implies (and (integerp size)
                  (>= size 0)
                  (integerp pos)
                  (>= pos 0))
             (bspp (bsp size pos)))
    :hints (("Goal" :in-theory (enable bspp)))))

(define bsp-size ((bsp bspp))
  :returns (size (and (integerp size)
                      (>= size 0))
                 :rule-classes :type-prescription
                 :hyp (bspp bsp) ;; BOZO not good for type prescription
                 :name bsp-size-type)
  :parents (logops-byte-functions)
  :short "@('(bsp-size (bsp size pos)) = size')"
  :long "<p>This is analogous to Common Lisp's @('(byte-size bytespec)').</p>"
  :enabled t
  (car bsp))

(define bsp-position ((bsp bspp))
  :returns (pos (and (integerp pos)
                     (>= pos 0))
                :rule-classes :type-prescription
                :hyp (bspp bsp) ;; BOZO not good for type prescription
                :name bsp-position-type)
  :parents (logops-byte-functions)
  :short "@('(bsp-position (bsp size pos)) = pos')"
  :long "<p>This is analogous to Common Lisp's @('(byte-position bytespec)').</p>"
  :enabled t
  (cdr bsp))

(define rdb ((bsp bspp)
             (i   integerp))
  :returns (nat (and (integerp nat)
                     (>= nat 0))
                :rule-classes :type-prescription
                :name rdb-type)
  :parents (logops-byte-functions)
  :short "@(call rdb) returns the byte of @('i') specified by @('bsp')."
  :long "<p>This is analogous to Common Lisp's @('(ldb bytespec integer)').</p>"
  :enabled t
  (loghead (bsp-size bsp) (logtail (bsp-position bsp) i))
  ///
  (defthm unsigned-byte-p-rdb
    (implies (and (>= size (bsp-size bsp))
                  (force (>= size 0))
                  (force (integerp size))
                  (force (bspp bsp)))
             (unsigned-byte-p size (rdb bsp i))))

  (defthm rdb-upper-bound
    (implies (force (bspp bsp))
             (< (rdb bsp i) (expt 2 (bsp-size bsp))))
    :rule-classes (:linear :rewrite))

  (defthm bitp-rdb-bsp-1
    (implies (equal (bsp-size bsp) 1)
             (bitp (rdb bsp i)))
    :hints (("Goal" :in-theory (enable bitp loghead)))))

(define wrb ((i   integerp)
             (bsp bspp)
             (j   integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name wrb-type)
  :parents (logops-byte-functions)
  :short "@(call wrb) writes the @('(bsp-size bsp)') low-order bits of @('i')
into the byte of @('j') specified by @('bsp')."
  :long "<p>This is analogous to Common Lisp's @('(dpb newbyte bytespec
integer)').</p>"
  :enabled t
  (logapp (bsp-position bsp)
          (loghead (bsp-position bsp) j)
          (logapp (bsp-size bsp)
                  i
                  (logtail (+ (bsp-size bsp) (bsp-position bsp)) j))))

(define rdb-test ((bsp bspp)
                  (i   integerp))
  :returns bool
  :parents (logops-byte-functions)
  :short "@(call rdb-test) is true iff the field of @('i') specified by
  @('bsp') is nonzero."
  :long "<p>This is analogous to Common Lisp's @('(ldb-test bytespec
  integer)').</p>"
  :enabled t
  (not (eql (rdb bsp i) 0)))

(define rdb-field ((bsp bspp)
                   (i   integerp))
  :returns nat
  :parents (logops-byte-functions)
  :short "@(call rdb-field) is analogous to Common Lisp's @('(mask-field bytespec integer)')."
  :enabled t
  (logand i (wrb -1 bsp 0)))

(define wrb-field ((i   integerp)
                   (bsp bspp)
                   (j   integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name wrb-field-type)
  :parents (logops-byte-functions)
  :short "@(call wrb-field) is analogous to Common Lisp's @('(deposit-field
  newbyte bytespec integer)')."
  :enabled t
  (wrb (rdb bsp i) bsp j))

;  Guard macros.

(defsection rdb-guard
  :parents (logops-byte-functions)
  :short "@(call rdb-guard) is a macro form of the guards for @(see rdb), @(see
  rdb-test), and @(see rdb-field)."
  :long "@(def rdb-guard)"

  (defmacro rdb-guard (bsp i)
    `(and (force (bspp ,bsp))
          (force (integerp ,i)))))

(defsection wrb-guard
  :parents (logops-byte-functions)
  :short "@(call wrb-guard) is a macro form of the guards for @(see wrb) and @(see wrb-field)."
  :long "@(def wrb-guard)"

  (defmacro wrb-guard (i bsp j)
    `(and (force (integerp ,i))
          (force (bspp ,bsp))
          (force (integerp ,j)))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  Type lemmas for the byte functions.  Each function is DISABLED after we
;;;  have enough information about it.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(local (in-theory (disable bspp)))
(local (in-theory (disable bsp-size)))
(local (in-theory (disable bsp-position)))
(local (in-theory (disable rdb)))
(local (in-theory (disable wrb)))
(local (in-theory (disable rdb-test)))          ;An obvious predicate.

;;;  RDB-FIELD

#|

Need Type-Prescriptions to prove this.  I don't think we ever use this
function.

(defthm rdb-field-type
  (and (integerp (rdb-field bsp i))
       (>= (rdb-field bsp i) 0))
  :rule-classes :type-prescription)

|#

(local (in-theory (disable rdb-field)))
(local (in-theory (disable wrb-field)))


;; [Jared]: I moved the bit functions like B-NOT into basic-definitions.lisp.


;;;****************************************************************************
;;;
;;;    Theories
;;;
;;;****************************************************************************

(defval *logops-functions*
  :parents (logops-definitions)
  :short "A list of all functions considered to be part of the theory of logical
          operations on numbers."
  '(binary-LOGIOR
    binary-LOGXOR binary-LOGAND binary-LOGEQV LOGNAND LOGNOR LOGANDC1
    LOGANDC2 LOGORC1 LOGORC2 LOGNOT LOGTEST LOGBITP ASH
    LOGCOUNT INTEGER-LENGTH
    BITP
    SIGNED-BYTE-P
    UNSIGNED-BYTE-P
    LOGCAR$inline
    LOGCDR$inline
    LOGCONS$inline
    LOGBIT$inline
    LOGMASK$inline
    LOGMASKP
    LOGHEAD$inline
    LOGTAIL$inline
    LOGAPP
    LOGRPL
    LOGEXT
    LOGREV1
    LOGREV$inline
    LOGSAT
    LOGNOTU$inline
    LOGEXTU$inline
    ASHU
    LSHU
    BSPP BSP-SIZE BSP-POSITION RDB WRB RDB-TEST RDB-FIELD WRB-FIELD
    B-NOT$inline
    B-AND$inline
    B-IOR$inline
    B-XOR$inline
    B-EQV$inline
    B-NAND$inline
    B-NOR$inline
    B-ANDC1$inline
    B-ANDC2$inline
    B-ORC1$inline
    B-ORC2$inline
    ))

(defsection logops-functions
  :parents (logops-definitions)
  :short "A theory consisting of all function names of functions considered to
          be logical operations on numbers."
  :long "<p>If you are using the book @('logops-lemmas'), you will need to
  DISABLE this theory in order to use the lemmas contained therein, as most of
  the logical operations on numbers are non-recursive.</p>"

  (deftheory logops-functions *logops-functions*))

(defsection logops-definitions-theory
  :parents (logops-definitions)
  :short "The \"minimal\" theory for the book \"logops-definitions\"."
  :long "<p>This theory contains the DEFUN-TYPE/EXEC-THEORY (which see) of all
functions considered to be logical operations on numbers, and all
lemmas (predominately `type lemmas') proved in this book.  All functions in the
list *LOGOPS-FUNCTIONS* are DISABLEd.</p>"

  (deftheory logops-definitions-theory
    (union-theories
     (set-difference-theories
      (set-difference-theories            ;Everything in this book ...
       (universal-theory :here)
       (universal-theory 'begin-logops-definitions))
      *logops-functions*)                 ;Minus all of the definitions.
     (defun-type/exec-theory *logops-functions*))        ;Plus basic type info
    ))



;;;****************************************************************************
;;;
;;;  DEFBYTETYPE name size s/u &key saturating-coercion doc.
;;;
;;;****************************************************************************

(defsection defbytetype
  :parents (logops-definitions)
  :short "A macro for defining integer subrange types."
  :long "<p>The \"byte types\" defined by DEFBYTETYPE correspond to the Common
Lisp concept of a \"byte\", that is, an integer with a fixed number of bits.
We extend the Common Lisp concept to allow signed bytes.</p>

<p>Example:</p>

@({
    (DEFBYTETYPE WORD 32 :SIGNED)
})

<p>Defines a new integer type of 32-bit signed integers, recognized by
@('(WORD-P i)').</p>

<p>General Form:</p>

@({
   (DEFBYTETYPE name size s/u &key saturating-coercion)
})

<p>The argument name should be a symbol, size should be a constant
expression (suitable for DEFCONST) for a positive integer, s/u is
either :SIGNED or :UNSIGNED, saturating-coercion should be a symbol (default
NIL).</p>

<p>Each data type defined by DEFBYTETYPE produces a number of events:</p>

<ul>

<li>A constant @('*<name>-MAX*'), set to the maximum value of the type.</li>

<li>A constant @('*<name>-MIN*'), set to the minimum value of the type.</li>

<li>A predicate, @('(<pred> x)'), that recognizes either @('(UNSIGNED-BYTE-P
size x)') or @('(SIGNED-BYTE-P size x)'), depending on whether s/u
was :UNSIGNED or :SIGNED respectively. This predicate is DISABLED.  The name of
the predicate will be @('<name>-p').</li>

<li>A coercion function, @('(<name> i)'), that coerces any object @('i') to the
correct type by LOGHEAD and LOGEXT for unsigned and signed integers
respectively.  This function is DISABLED.</li>

<li>A lemma showing that the coercion function actually does the correct
coercion.</li>

<li>A lemma that reduces calls of the coercion function when its argument
satisfies the predicate.</li>

<li>A forward chaining lemma from the predicate to the appropriate type
information.</li>

<li>If :SATURATING-COERCION is specified, the value of this keyword argument
should be a symbol.  A function of this name will be defined to provide a
saturating coercion.  `Saturation' in this context means that values outside of
the legal range for the type are coerced to the type by setting them to the
nearest legal value, which will be either the minimum or maximum value of the
type. This function will be DISABLEd, and a lemma will be generated that proves
that this function returns the correct type.  Note that
the :SATURATING-COERCION option is only valid for :SIGNED types.</li>

<li>A theory named @('<name>')-THEORY that includes the lemmas and the
DEFUN-TYPE/EXEC-THEORY of the functions.</li>

</ul>")

(defmacro defbytetype (name size s/u &key saturating-coercion doc)
  (declare (xargs :guard (and (symbolp name)
                              ;; How to say that SIZE is a constant expression?
                              (or (eq s/u :SIGNED) (eq s/u :UNSIGNED))
                              (implies saturating-coercion
				       (and (symbolp saturating-coercion)
					    (eq s/u :SIGNED)))
                              (implies doc (stringp doc)))))

  (let*
    ((max-constant (pack-intern name "*" name "-MAX*"))
     (min-constant (pack-intern name "*" name "-MIN*"))
     (predicate (pack-intern name name "-P"))
     (predicate-lemma (pack-intern name predicate "-" name))
     (coercion-lemma (pack-intern name "REDUCE-" name))
     (forward-lemma (pack-intern predicate predicate "-FORWARD"))
     (sat-lemma (pack-intern name predicate "-" saturating-coercion))
     (theory (pack-intern name name "-THEORY")))

    `(ENCAPSULATE ()
       (LOCAL (IN-THEORY (THEORY 'BASIC-BOOT-STRAP)))
       (LOCAL (IN-THEORY (ENABLE LOGOPS-DEFINITIONS-THEORY)))

       ;;  NB! These two ENABLEs mean that we have to have "logops-lemmas"
       ;;  loaded to do a DEFBYTETYPE.

       (LOCAL (IN-THEORY (ENABLE LOGHEAD-IDENTITY LOGEXT-IDENTITY)))

       (DEFCONST ,max-constant ,(case s/u
                                  (:SIGNED `(- (EXPT2 (- ,size 1)) 1))
                                  (:UNSIGNED `(- (EXPT2 ,size) 1))))
       (DEFCONST ,min-constant ,(case s/u
                                  (:SIGNED `(- (EXPT2 (- ,size 1))))
                                  (:UNSIGNED 0)))
       (DEFUN ,predicate (X)
	 (DECLARE (XARGS :GUARD T))
         ,(case s/u
            (:SIGNED `(SIGNED-BYTE-P ,size X))
            (:UNSIGNED `(UNSIGNED-BYTE-P ,size X))))
       (DEFUN ,name (I)
         ,@(when$cl doc (list doc))
         (DECLARE (XARGS :GUARD (INTEGERP I)))
         ,(case s/u
            (:SIGNED `(LOGEXT ,size I))
            (:UNSIGNED `(LOGHEAD ,size I))))
       (DEFTHM ,predicate-lemma
	 (,predicate (,name I)))
       (DEFTHM ,coercion-lemma
	 (IMPLIES
	  (,predicate I)
	  (EQUAL (,name I) I)))
       (DEFTHM ,forward-lemma
         (IMPLIES
          (,predicate X)
          ,(case s/u
             (:SIGNED `(INTEGERP X))
             (:UNSIGNED `(AND (INTEGERP X)
			      (>= X 0)))))
         :RULE-CLASSES :FORWARD-CHAINING)
       ,@(when$cl saturating-coercion
           (list
            `(DEFUN ,saturating-coercion (I)
               (DECLARE (XARGS :GUARD (INTEGERP I)))
	       (LOGSAT ,size I))
            `(DEFTHM ,sat-lemma
	       (,predicate (,saturating-coercion I)))))
       (IN-THEORY (DISABLE ,predicate ,name ,@(when$cl saturating-coercion
                                                (list saturating-coercion))))
       (DEFTHEORY ,theory
         (UNION-THEORIES
          (DEFUN-TYPE/EXEC-THEORY
            '(,predicate ,name ,@(when$cl saturating-coercion
                                   (list saturating-coercion))))
          '(,predicate-lemma ,coercion-lemma ,forward-lemma
			     ,@(when$cl saturating-coercion
				 (list sat-lemma))))))))

;;;****************************************************************************
;;;
;;;  DEFWORD
;;;
;;;****************************************************************************

;;;  Recognizers for valid structure definitions and code generators.  See
;;;  the grammar in the :DOC for DEFWORD.

(defun defword-tuple-p (tuple)
  (or (and (true-listp tuple)
	   (or (equal (length tuple) 3)
	       (equal (length tuple) 4))
	   (symbolp (first tuple))
	   (integerp (second tuple))
	   (> (second tuple) 0)
	   (integerp (third tuple))
	   (>= (third tuple) 0)
	   (implies (fourth tuple) (stringp (fourth tuple))))
      (er hard 'defword
	  "A field designator for DEFWORD must be a list, the first ~
             element of which is a symbol, the second a positive integer, ~
             and the third a non-negative integer.  If a fouth element is ~
             provided it must be a string.  This object violates these ~
             constraints: ~p0" tuple)))

(defun defword-tuple-p-listp (struct)
  (cond
   ((null struct) t)
   (t (and (defword-tuple-p (car struct))
	   (defword-tuple-p-listp (cdr struct))))))

(defun defword-struct-p (struct)
  (cond
   ((true-listp struct) (defword-tuple-p-listp struct))
   (t (er hard 'defword
	  "The second argument of DEFWORD must be a true list. ~
           This object is not a true list: ~p0" struct))))

(defun defword-guards (name struct conc-name set-conc-name keyword-updater
			    doc)
  (and
   (or (symbolp name)
       (er hard 'defword
	   "The name must be a symbol.  This is not a symbol: ~p0" name))
   (defword-struct-p struct)
   (or (symbolp conc-name)
       (er hard 'defword
	   "The :CONC-NAME must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (symbolp set-conc-name)
       (er hard 'defword
	   "The :SET-CONC-NAME must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (symbolp keyword-updater)
       (er hard 'defword
	   "The :KEYWORD-UPDATER must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (implies doc (stringp doc))
       (er hard 'defword
	   "The :DOC must be a string.  This is not a string: ~p0" doc))))

(defun defword-accessor-name (name conc-name field)
  (pack-intern name conc-name field))

(defun defword-updater-name (name set-conc-name field)
  (pack-intern name set-conc-name field))

(defun defword-accessor-definitions (rdb name conc-name tuples)
  (cond ((consp tuples)
	 (let*
	   ((tuple (car tuples))
	    (field (first tuple))
	    (size (second tuple))
	    (pos (third tuple))
	    (doc (fourth tuple))
	    (accessor (defword-accessor-name name conc-name field)))
	   (cons
	    `(DEFMACRO ,accessor (WORD)
	       ,@(if doc (list doc) nil)
	       (LIST ',rdb (LIST 'BSP ,size ,pos) WORD))
	    (defword-accessor-definitions rdb name conc-name (cdr tuples)))))
	(t ())))

(defun defword-updater-definitions (wrb name set-conc-name tuples)
  (cond ((consp tuples)
	 (let*
	   ((tuple (car tuples))
	    (field (first tuple))
	    (size (second tuple))
	    (pos (third tuple))
	    (updater (defword-updater-name name set-conc-name field)))
	   (cons
	    `(DEFMACRO ,updater (VAL WORD)
	       (LIST ',wrb VAL (LIST 'BSP ,size ,pos) WORD))
	    (defword-updater-definitions wrb name set-conc-name
	      (cdr tuples)))))
	(t ())))

(defloop defword-keyword-field-alist (name set-conc-name field-names)
  (for ((field-name in field-names))
    (collect (cons (intern-in-package-of-symbol (string field-name) :keyword)
		   (defword-updater-name name set-conc-name field-name)))))

(defun defword-keyword-updater-body (val args keyword-field-alist)
  (cond
   ((atom args) val)
   (t `(,(cdr (assoc (car args) keyword-field-alist)) ,(cadr args)
	,(defword-keyword-updater-body val (cddr args) keyword-field-alist)))))

(defun defword-keyword-updater-fn (form val args keyword-updater
					keyword-field-alist)
  (declare (xargs :mode :program))
  (let*
    ((keyword-field-names (strip-cars keyword-field-alist)))
    (cond
     ((not (keyword-value-listp args))
      (er hard keyword-updater
	  "The argument list in the macro invocation ~p0 ~
           does not match the syntax of a keyword argument ~
           list because ~@1."
	  form (reason-for-non-keyword-value-listp args)))
     ((not (subsetp (evens args) keyword-field-names))
      (er hard keyword-updater
	  "The argument list in the macro invocation ~p0 is not ~
           a valid keyword argument list because it contains the ~
           ~#1~[keyword~/keywords~] ~&1, which ~#1~[is~/are~] ~
            not the keyword ~#1~[form~/forms~] of any of the ~
            field names ~&2."
	  FORM (set-difference-equal (evens args) keyword-field-names)
	  keyword-field-names))
     (t (defword-keyword-updater-body val args keyword-field-alist)))))

(defun defword-keyword-updater (name keyword-updater set-conc-name
				     field-names)
  `(DEFMACRO ,keyword-updater (&WHOLE FORM VAL &REST ARGS)
     (DEFWORD-KEYWORD-UPDATER-FN
       FORM VAL ARGS ',keyword-updater
       ',(defword-keyword-field-alist name set-conc-name field-names))))


(defsection defword
  :parents (logops-definitions)
  :short "A macro to define packed integer data structures."
  :long "<p>Example:</p>

@({
    (DEFWORD FM9001-INSTRUCTION-WORD
      ((RN-A 4 0) (MODE-A 2 4) (IMMEDIATE 9 0) (A-IMMEDIATE 1 9)
       (RN-B 4 10) (MODE-B 2 14)
       (SET-FLAGS 4 16) (STORE-CC 4 20) (OP-CODE 4 24))
      :CONC-NAME ||
      :SET-CONC-NAME SET-)
})

<p>The above example defines the instruction word layout for the FM9001.  The
macro defines accessing macros (RN-A i), ... ,(OP-CODE i), updating
macros (SET-RN-A val i), ... ,(SET-OP-CODE val i), and a keyword updating
macro @('(UPDATE-FM9001-INSTRUCTION-WORD val &rest args)').</p>

<p>General form:</p>

@({
    (DEFWORD name struct &key conc-name set-conc-name keyword-updater)
})

<p>The DEFWORD macro defines a packed integer data structure, for example an
instruction word for a programmable processor or a status word.  DEFWORD is a
simple macro that defines accessing and updating macros for the fields of the
data structure. The utility of DEFWORD is mainly to simplify the specification
of packed integer data structures, and to improve the readability of code
manipulating these data structures without affecting performance. As long as
the book \"logops-lemmas\" is loaded all of the important facts about the macro
expansions should be available to the theorem prover.</p>

<p>Arguments</p>

@({
  name:  The name of the data structure, a symbol.

  struct : The field structure of the word. The form of this argument is
  given by the following grammar:

  <tuple>  := (<field> <size> <pos> [ <doc> ])
  <struct> := () | (<tuple> . <struct>)

  where:

  (SYMBOLP <field>)
  (AND (INTEGERP <size>) (> <size> 0))
  (AND (INTEGERP <pos>) (>= <pos> 0))
  (STRINGP <doc>)
})

<p>In other words, a list of tuples, the first element being a symbol, the
second a positive integer, the third a nonnegative integer, and the optional
fourth a string.</p>

<p>Note that there are few other requirements on the @('<struct>') other than
the syntactic ones above.  For example, the FM9001 DEFWORD shows that a word
may have more than one possible structure - the first 9 bits of the FM9001
instruction word are either an immediate value, or they include the RN-A and
MODE-A fields.</p>

<p>conc-name, set-conc-name: These are symbols whose print names will be
concatenated with the field names to produce the name of the accessors and
updaters respectively.  The default is @('<name>')- and @('SET-<name>')-
respectively.  The access and update macro names will be interned in the
package of name.</p>

<p>keyword-updater:  This is a symbol, and specifies the name of the keyword
updating macro (see below).  The default is @('UPDATE-<name>').</p>


<h3>Interpretation</h3>

<p>DEFWORD creates an ACL2 DEFLABEL event named @('<name>').</p>

<p>Each tuple @('(<field> <size> <pos>)') represents a @('<size>')-bit field of
a word at the bit position indicated.  Each field tuple produces an accessor
macro</p>

@({
  (<accessor> word)
})

<p>where @('<accessor>') is computed from the :conc-name (see above).  This
accessor will expand into:</p>

@({
  (RDB (BSP <size> <pos>) word).
})

<p>DEFWORD also generates an updating macro</p>

@({
  (<updater> val word)
})

<p>where @('<updater>') is computed from the :set-conc-name (see above).  This
macro will expand to</p>

@({
     (WRB val (BSP <size> <pos>) word)
})

<p>The keyword updater</p>

@({
  (<keyword-updater> word &rest args)
})

<p>is equivalent to multiple nested calls of the updaters on the initial word.
 For example,</p>

@({
  (UPDATE-FM9001-INSTRUCTION-WORD WORD :RN-A 10 :RN-B 12)
})

<p>is the same as @('(SET-RN-A 10 (SET-RN-B 12 WORD))').</p>")

(defmacro defword (name struct &key conc-name set-conc-name keyword-updater doc)
  (cond
   ((not
     (defword-guards name struct conc-name set-conc-name keyword-updater doc)))
   (t
    (let*
      ((conc-name (if conc-name
                      conc-name
                    (pack-intern name name "-")))
       (set-conc-name (if set-conc-name
                          set-conc-name
                        (pack-intern name "SET-" name "-")))
       (keyword-updater (if keyword-updater
			    keyword-updater
			  (pack-intern name "UPDATE-" name)))
       (accessor-definitions
        (defword-accessor-definitions 'RDB name conc-name struct))
       (updater-definitions
        (defword-updater-definitions 'WRB name set-conc-name struct))
       (field-names (strip-cars struct)))

      `(ENCAPSULATE ()                  ;Only to make macroexpansion pretty.
         (DEFLABEL ,name ,@(if doc `(:DOC ,doc) nil))
         ,@accessor-definitions
         ,@updater-definitions
         ,(defword-keyword-updater
	    name keyword-updater set-conc-name field-names))))))

#||
Example:

(DEFWORD FM9001-INSTRUCTION
  ((RN-A 4 0) (MODE-A 2 4) (IMMEDIATE 9 0) (A-IMMEDIATE 1 9)
   (RN-B 4 10) (MODE-B 2 14)
   (SET-FLAGS 4 16) (STORE-CC 4 20) (OP-CODE 4 24))
  :CONC-NAME ||
  :SET-CONC-NAME SET-
  :DOC "Instruction word layout for the FM9001.")

||#

;;;****************************************************************************
;;;
;;;  Word/Bit Macros
;;;
;;;****************************************************************************

(defxdoc word/bit-macros
  :parents (logops-definitions)
  :short "Macros for manipulating integer words defined as contiguous bits."
  :long "<p>These macros were defined to support the functions produced by
  translating SPW .eqn files to ACL2 functions.</p>")

(defun bind-word-to-bits-fn (bit-names n word)
  (cond
   ((endp bit-names) ())
   (t (cons `(,(car bit-names) (LOGBIT ,n ,word))
	    (bind-word-to-bits-fn (cdr bit-names) (1+ n) word)))))

(defsection bind-word-to-bits
  :parents (word/bit-macros)
  :short "Bind variables to the contiguous low-order bits of word."
  :long "<p>Example:</p>

@({
  (BIND-WORD-TO-BITS (A B C) I (B-AND A (B-IOR B C)))
})

<p>The above macro call will bind A, B, and C to the 0th, 1st, and 2nd bit of
I, and then evaluate the logical expression under those bindings.  The list of
bit names is always interpreted from low to high order.</p>"

  (defmacro bind-word-to-bits (bit-names word &rest forms)
    (declare (xargs :guard (and (symbol-listp bit-names)
                                (no-duplicatesp bit-names))))
    `(LET ,(bind-word-to-bits-fn bit-names 0 word) ,@forms)))

(defsection make-word-from-bits
  :parents (word/bit-macros)
  :short "Update the low-order bits of word with the indicated values."
  :long "<p>Example:</p>

@({
    (MAKE-WORD-FROM-BITS A B C)
})

<p>The above macro call will build an unsigned integer from the bits A B, and
C.  The list of bits is always interpreted from low to high order. Note that
the expression generated by this macro will coerce the values to bits before
building the word.</p>"

  (defmacro make-word-from-bits (&rest bits)
    (cond
     ((endp bits) 0)
     (t `(LOGAPP 1 ,(car bits) (MAKE-WORD-FROM-BITS ,@(cdr bits)))))))
