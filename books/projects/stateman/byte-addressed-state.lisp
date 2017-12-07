; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Symbolic State Management -- Version 22
; J Strother Moore
; Fall/Winter, 2014/2015
; Georgetown, TX and Edinburgh, Scotland

#|| Certification:

; (ld "byte-addressed-state.lisp" :ld-pre-eval-print t)
; (certify-book "byte-addressed-state")

||#

; This file started out as

; B-Code model by Warren A. Hunt, Jr with changes by J Strother Moore

; Bcode5 became b-code5x to accommodate slight changes in the machine model to
; facilitate DES codewalks.  B-code5 became B-code5x-reduced to eliminate all
; lemmas unnecessary for codewalks and to add the lemmas (some formerly from
; cw-exp-lemmas.lisp) to canonicalize states.

; Most comments have been stripped out to keep this file as simple as possible.

(in-package "SMAN")

(local (include-book "arithmetic-5/top" :dir :system))

; Some miscellaneous definitions.

(defmacro !nth (key val l)
 `(update-nth ,key ,val ,l))

(add-macro-fn !nth update-nth)

; The PCODE machine state

; The length of the memory in the stobj is given by the function ml.  Memory is
; not resizeable.  That makes our bounds proofs faster.  ML will not be
; disabled.  The constant value of (ML st) is given by the following constant.

(defconst *m-size*  5312)

(defstobj st                                     ; Machine state
  (i  :type unsigned-byte :initially 0)          ; program counter
  (s  :initially nil)                            ; status
  (m  :type (array (unsigned-byte 8) (*m-size*)) ; memory
      :initially 0
      :resizable nil
      )
  :inline t
  :renaming
  ((update-i   !i)
   (update-s   !s)
   (update-mi  !mi) (m-length   ml)))

; Before we define the machine itself we want to prove lemmas to canonicalize
; state expressions.  A few of these lemmas are used in the guard proofs for
; the machine model -- provided the accessors and updaters are disabled.  So
; we'll prove their basic properties and disable them so we can treat the state
; and its accessors and updaters as abstract functions with certain nice
; properties when we do the guard proofs.

; The basic accessors are i, s, and mi and the basic updaters are !i, !s, and
; !mi.

; However, we will then define r and !r to read from and write to m in
; n-byte chunks.  All uses of mi and !mi will be hidden inside r and !r,
; which will ultimately be disabled.  In the final state expressions we'll
; never see m or !mi, just r and !r.  Thus, far all intents and purposes the
; basic accessors are i, s, and r and the basic updaters are !i, !s, and !r.

; The general strategy for canonicalizing state expressions is to prove a
; ``Standard Series'' of lemmas about the state recognizer, accessors, and
; updaters.  In our case, we'll prove the Standard Series first about the true
; primitives (including mi and !mi).  Then we'll disable those functions and
; prove the Standard Series ``again'' except for r and !r.  We'll limit our
; r/!r lemmas to the situation when the same number of bytes are read or
; written and not consider reading from within or overlapping with a sequence
; of bytes written.

; The Standard Series is sketched here:

; - Accessor Types: what sort of object do the accessors return?  E.g., (natp
;   (i st)).

; - State Invariance: when does an updater preserve the state recognizer?  For
;   memory this involves proving an intermediate fact about (mp (!mi i v lst))
;   We also include on odd duck lemma in this category: the forward chaining
;   rule from the state recognizer to its conjuncts, so that the recognizer can
;   generally be disabled.

; - Access/Update Expressions: what do you get if you apply an arbitrary
;   accessor to an arbitrary updater?  E.g., what can you say about (i (!i v
;   st)) and (i (!s v st))?  For memory this involves (mi i1 (!mi i2 v
;   st))-like questions.

; - Update/Update Expressions: what happens if you compose two arbitrary
;   updaters in either order?  E.g., what is (!i i1 (!i i2 st)), (!i i (!s s
;   st)) or (!s s (!i i st))?  For memory this involves (!mi i1 v1 (!mi i2 v2
;   st)).

; - Update/Access Expressions: what happens if you update a field with its
; - current value?  E.g., what is (!i (i st) st)?

; About our use of LOCAL: in our final canonical form there will be no
; occurrences of mi, !mi, !nth, or update-nth.  Furthermore, the only
; occurrences of nth will be to access the components of the stobj; during the
; proofs in this book we'll use car/cdr/cons to represent the stobj and so will
; expand nth and update-nth on indices 0, 1, and 2.  Outside this book all
; these functions will be disabled.  Therefore, we lose nothing and sometimes
; get marginal efficiency gains by making LOCAL any lemmas that target these
; functions.  (The marginal efficiency comes from not even trying to match a
; lemma that rewrites, say, (i (!mi ma v st)) because there will be no !mi
; terms in our goals.)

; Before building the Standard Series for the true primitives, we prove a
; few lemmas about nth and !nth.

(local
 (defthm natp-nth-mp
   (implies (and (mp x)
                 (integerp n)
                 (<= 0 n)
                 (< n (len x)))
            (natp (nth n x)))
   :rule-classes :type-prescription))

(local
 (defthm bytep-nth-mp
   (implies (and (mp x)
                 (integerp n)
                 (<= 0 n)
                 (< n (len x)))
            (< (nth n x) 256))
   :rule-classes :linear))

(local
 (defthm mp-!nth
   (implies (and (mp x)
                 (< ma (len x))
                 (integerp v)
                 (<= 0 v)
                 (< v 256))
            (mp (!nth ma v x)))))

(local
 (defthm !nth-nth
   (implies (and (integerp n)
                 (<= 0 n)
                 (< n (len x))
                 (equal (nth n x) v))
            (equal (!nth n v x)
                   x))))

(local
 (defthm !nth-!nth-same
  (equal (!nth i v1 (!nth i v2 x))
         (!nth i v1 x))))

(local
 (defthm !nth-!nth-diff
   (implies (and (integerp i1)
                 (<= 0 i1)
                 (integerp i2)
                 (<= 0 i2)
                 (not (equal i1 i2)))
            (equal (!nth i1 v1 (!nth i2 v2 lst))
                   (!nth i2 v2 (!nth i1 v1 lst))))))

; These two lemmas force nth and update-nth to expand on the stobj indices,
; during the proofs of the Standard Series.

(local
 (defthm nth-0-1-2
   (and (equal (nth 0 x) (car x))
        (equal (nth 1 x) (cadr x))
        (equal (nth 2 x) (caddr x)))
   :hints (("Goal" :expand ((:free (x) (nth 1 x))
                            (:free (x) (nth 2 x)))))))

(local
 (defthm update-nth-0-1-2
   (and (equal (update-nth 0 v x) (cons v (cdr x)))
        (equal (update-nth 1 v x) (cons (car x) (cons v (cddr x))))
        (equal (update-nth 2 v x) (cons (car x) (cons (cadr x) (cons v (cdddr x))))))
   :hints (("Goal" :expand ((:free (v x) (update-nth 1 v x))
                            (:free (v x) (update-nth 2 v x)))))))

(in-theory (disable nth update-nth))

; Standard Series for True Primitives

; Accessor Types:

(defthm natp-i
  (implies (stp st)
           (natp (i st)))
  :rule-classes :type-prescription)

; no restriction on (s st)

(local
 (defthm natp-mi
   (implies (and (stp st)
                 (integerp ma)
                 (<= 0 ma)
                 (< ma *m-size*))   ; = (ml st) but no need to expand ml
            (natp (mi ma st)))
   :rule-classes :type-prescription))

(local
 (defthm bytep-mi
   (implies (and (stp st)
                 (integerp ma)
                 (<= 0 ma)
                 (< ma *m-size*))
            (< (mi ma st) 256))
   :rule-classes :linear))

; State Invariance:

(defthm stp-!i
  (implies (and (integerp pc)
                (<= 0 pc)
                (stp st))
           (stp (!i pc st))))

(defthm stp-!s
  (implies (stp st)
           (stp (!s flg st))))

(defthm stp-!mi
  (implies (and (stp st)
                (< ma *m-size*)
                (integerp v)
                (<= 0 v)
                (< v 256))
           (stp (!mi ma v st))))

(defthm st-properties ; (``Odd Duck'')
  (implies (stp st)
           (and (consp st)
                (true-listp st)
                (equal (len st) 3)
                (integerp  (nth 0 st))
                (<= 0  (nth 0 st))
                (mp    (nth 2 st))
                (equal (len (nth 2 st)) *m-size*)
                ))
  :rule-classes :forward-chaining)

; Access/Update Expressions:

(defthm i-!i
  (equal (i (!i pc st)) pc))

(defthm i-!s
  (equal (i (!s flg st)) (i st)))

(defthm i-!mi
  (equal (i (!mi ma v st)) (i st)))

(defthm s-!i
  (equal (s (!i pc st)) (s st)))

(defthm s-!s
  (equal (s (!s flg st)) flg))

(defthm s-!mi
  (equal (s (!mi ma v st)) (s st)))


(local
 (defthm mi-!i
   (equal (mi ma (!i pc st))
          (mi ma st))))

(local
 (defthm mi-!s
   (equal (mi ma (!s flg st))
          (mi ma st))))

(local
 (defthm mi-!mi
   (implies (and (integerp ma1)
                 (<= 0 ma1)
                 (integerp ma2)
                 (<= 0 ma2))
            (equal (mi ma1 (!mi ma2 v2 st))
                   (if (equal ma1 ma2)
                       v2
                       (mi ma1 st))))))

; Update/Update Expressions:

(defthm !i-!i
  (equal (!i pc1 (!i pc2 st))
         (!i pc1 st)))

; We leave (!i ... (!s ...)) and (!i ... (!mi ...)) unchanged.


(defthm !s-!i
  (equal (!s s (!i pc st))
         (!i pc (!s s st))))

(defthm !s-!s
  (equal (!s flg1 (!s flg2 st))
         (!s flg1 st)))

; We leave (!s ... (!mi ...)) unchanged.


(local
 (defthm !mi-!i
   (equal (!mi ma v (!i pc st))
          (!i pc (!mi ma v st)))))

(local
 (defthm !mi-!s
   (equal (!mi ma v (!s s st))
          (!s s (!mi ma v st)))))

(defthm !mi-!mi-same
  (implies (and (integerp ma)
                (<= 0 ma))
           (equal (!mi ma v1 (!mi ma v2 st))
                  (!mi ma v1 st))))

(defthm !mi-!mi-diff
  (implies (and (integerp ma1)
                (<= 0 ma1)
                (integerp ma2)
                (<= 0 ma2)
                (not (equal ma1 ma2)))
           (equal (!mi ma1 v1 (!mi ma2 v2 st))
                  (!mi ma2 v2 (!mi ma1 v1 st))))
  :rule-classes ((:rewrite :loop-stopper ((ma1 ma2 !mi)))))


; Update/Access Expressions:

(defthm !i-i
  (implies (and (stp st)
                (equal (i st) pc))
           (equal (!i pc st) st)))

(defthm !s-s
  (implies (and (stp st)
                (equal (s st) flg))
           (equal (!s flg st) st)))

(defthm !mi-mi
  (implies (and (stp st)
                (integerp ma)
                (<= 0 ma)
                (< ma *m-size*)
                (equal (mi ma st) v))
           (equal (!mi ma v st)
                  st)))

; End of Standard Series for True Primitives.

(in-theory (disable stp i !i s !s mp mi !mi))

; Definitios of R and !R

; R -- ReaD Memory (sz bytes)

(defun r (ma sz st)
  (declare (xargs :guard (and (integerp ma)
                              (<= 0 ma)
                              (integerp sz)
                              (<= 0 sz)
                              (<= (+ ma sz) *m-size*))
                  :verify-guards t
                  :stobjs (st)))
  (if (zp sz)
      0
      (let ((byte (mbe :logic (logand 255 (mi ma st))
                       :exec  (mi ma st)))
            (rest (ash (r (1+ ma) (1- sz) st) 8)))
        (+ byte rest))))

; !R -- WRite Memory (sz bytes, thus v may be truncated)

(defun !r (ma sz v st)
 (declare (xargs :guard (and (integerp ma)
                             (<= 0 ma)
                             (integerp sz)
                             (<= 0 sz)
                             (<= (+ ma sz) *m-size*)
                             (integerp v)
                             (<= 0 v))
                 :stobjs (st)))
 (if (zp sz)
     st
   (let ((byte (logand v 255))
         (rest (ash v -8)))
     (let ((st (!mi ma byte st)))
       (!r (1+ ma) (1- sz) rest st)))))

; Standard Series Redux -- with r/!r instead of mi/!mi

; We repeat the Standard Series, except that we only re-state lemmas that
; involve mi and/or !mi.  Those lemmas are re-stated in terms of r and !r.

; Accessor Types:

; From the defun of r we know (integerp (r ma sz st)).

(defthm r-bound ; in place of natp-mi and bytep-mi
  (and (<= 0 (r ma sz st))
       (< (r ma sz st)
          (expt 256 sz)))
  :hints (("Goal"
           :expand ((expt 256 sz))
           :in-theory (disable acl2::normalize-factors-gather-exponents)
           ))
  :rule-classes :linear)

; State Invariance:

(defthm stp-!r ; in place of stp-!mi
  (implies (and (stp st)
                (integerp ma)
                (<= 0 ma)
                (integerp sz)
                (<= 0 sz)
                (<= (+ ma sz) *m-size*))
           (stp (!r ma sz v st))))

; Access/Update Expressions:

(defthm i-!r ; in place of i-!mi
  (equal (i (!r ma sz v st)) (i st)))

(defthm s-!r ; in place of s-!mi
  (equal (s (!r ma sz v st)) (s st)))

(defthm r-!i ; in place of mi-!i
  (equal (r ma sz (!i pc st))
         (r ma sz st)))

(defthm r-!s ; in place of mi-!s
  (equal (r ma sz (!s flg st))
         (r ma sz st)))

; We take time away from the standard series to prove the lemmas necessary for
; r-!r-same and r-!r-diff lemmas (in place of mi-!mi).

; This lemma should be among the Logical/Arithmetic Lemmas below because it is
; useful in code analysis.  But it is needed now.

(defthm unnecessary-mod
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                (< i j))
           (equal (mod i j) i)))

(local
 (defthm unnecessary-floor
   (implies (and (integerp i)
                 (<= 0 i)
                 (integerp j)
                 (<= 0 j)
                 (< i j))
            (equal (floor i j) 0))))

; To prove the r-!r lemmas we have to first relate mi and !r: what do you
; get when you read a byte from a memory in which multiple bytes have been
; written?  We split it into two cases: reading above the write and below the
; write.  We'll call such lemmas ``mixed'' because they involve symbols from
; two different levels of abstraction.  Mixed lemmas can be local.

(local ; mixed
 (defthm mi-!r+
   (implies (and (integerp ra)
                 (<= 0 ra)
                 (integerp wa)
                 (<= 0 wa)
                 (< ra wa)) ;; write-above
            (equal (mi ra (!r wa wz v st))
                   (mi ra st)))))

(local ; mixed
 (defthm mi-!r-
   (implies (and (integerp ra)
                 (<= 0 ra)
                 (integerp wa)
                 (<= 0 wa)
                 (<= (+ wa wz) ra) ;; Write below
;                (< ra (ml st))
                 )
            (equal (mi ra (!r wa wz v st))
                   (mi ra st)))))

; Now we proved some r-1-!mi lemmas...  These are needed later but this is the
; right environment to prove them.  We disable them after proof just to show we
; don't need them.

(defthm r-1-!mi
  (implies (natp a)
           (equal (r a 1 (!mi b v st))
                  (cond ((natp b)
                         (cond ((< a b) (r a 1 st))
                               ((= a b) (logand 255 v))
                               (t (r a 1 st))))
                        ((equal a 0) (logand 255 v))
                        (t (r a 1 st)))))
  :hints (("Goal" :in-theory (enable mi !mi)
                  :expand ((:free (a st) (r a 1 st))))))

(in-theory (disable r-1-!mi))

; Now we return to standard series...

#||
; We used to use this, but writing a metafunction to manage r-!r is easier
; if we don't constrain the values being stored:

(defthm r-!r-same ; in place of mi-!mi
  (implies (and (integerp ma)
                (<= 0 ma)
                (<= (+ ma sz) *m-size*)
                (integerp v)
                (<= 0 v)
                (< v (expt 256 sz)))
           (equal (r ma sz (!r ma sz v st))
                  v)))

; So now we use:
||#

; This is just a subgoal of the r-!r-same, except we've generalized a r-!r
; inductive hyp to the variable r.

(local
 (defthm r-!r-same-lemma
   (implies (and (not (zp sz))
                 (not (integerp (* 1/256 v)))
                 (equal (- (floor v 256)
                           (* (expt 256 (+ -1 sz))
                              (floor v (expt 256 sz))))
                        r)
;                (integerp ma)
;                (<= 0 ma)
;                (<= (+ ma sz) 5312)
                 (integerp v))
            (equal (equal (+ (mod v 256)
                             (* 256
                                r))
                          (mod v (expt 256 sz)))
                   t))
   :hints (("Goal" :in-theory (enable floor mod)))))

(defthm r-!r-same ; in place of mi-!mi
  (implies (and (integerp ma)
                (<= 0 ma)
		(integerp sz)
                (<= 0 sz))
           (equal (r ma sz (!r ma sz v st))
                  (mod (ifix v) (expt 256 sz)))))

; We prove two lemmas to handle read-over-write, one where the read is below
; the write and one where the read is above the write.  No analysis has been
; done to determine which of the two is used more often -- and hence we have
; no certainty that they should be stored in this order!

(defthm r-!r-diff-below ; in place of mi-!mi

; This is READ-over-WRITE lemma for different non-overlapping addresses where
; the R is below the write.

 (implies (and (<= (+ ra sz) wa) ; we check the `below' hyp first!
               (integerp ra)
               (<= 0 ra)
               (integerp wa)
               (<= 0 wa))
          (equal (r ra sz (!r wa wz v st))
                 (r ra sz st))))

(defthm r-!r-diff-above ; in place of mi-!mi

; This is READ-over-WRITE lemma for different non-overlapping addresses where
; the R is above the write.

 (implies (and (<= (+ wa wz) ra) ; we check the `above' hyp first!
               (integerp ra)
               (<= 0 ra)
;              (<= (+ ra sz) (ml st))
               (integerp wa)
               (<= 0 wa)
;              (<= (+ wa wz) (ml st))
               )
          (equal (r ra sz (!r wa wz v st))
                 (r ra sz st))))

; Update/Update Expressions:

(defthm !r-!i ; in place of !mi-!i
  (equal (!r ma sz v (!i pc st))
         (!i pc (!r ma sz v st))))

(defthm !r-!s ; in place of !mi-!s
  (equal (!r ma sz v (!s s st))
         (!s s (!r ma sz v st))))


(local
 (defun !r-!r-same-hint (ma sz v1 v2 st)
   (declare (xargs :stobjs (st)
                   :measure (acl2-count sz)
                   :verify-guards nil))
   (if (zp sz)
       (mv st v2)
       (let ((byte1 (logand v1 255))
             (rest1 (ash v1 -8))
             (rest2 (ash v2 -8))
             )
         (let ((st (!mi ma byte1 st)))
           (!r-!r-same-hint (1+ ma) (1- sz) rest1 rest2 st))))))

(local ; mixed
 (defthm !r-!mi-below
   (implies (and (integerp sz1)
                 (<= 0 sz1)
                 (integerp ma1)
                 (<= 0 ma1)
                 (integerp ma2)
                 (<= 0 ma2)
                 (< ma2 ma1))
            (equal (!R MA1 SZ1 VAL1
                        (!MI ma2 VAL2 ST))
                   (!MI ma2 val2
                        (!r ma1 sz1 val1 st))))
   :hints (("Goal" :in-theory (enable !r)))))

#||
; We used to use:
(defthm !r-!r-same ; in place of !mi-!mi-same
  (implies (and (integerp ma)
                (<= 0 ma)
                (integerp sz)
                (<= 0 sz)
                (integerp v1)
                (<= 0 v1)
                (integerp v2)
                (<= 0 v2)
                )
           (equal (!r ma sz v1
                       (!r ma sz v2 st))
                  (!r ma sz v1 st)))
  :hints (("Goal" :induct (!r-!r-same-hint ma sz v1 v2 st))
          ("Subgoal *1/2''"
           :expand ((!R MA SZ V1 ST)
                    (!R MA SZ V2 ST)))
          ("Subgoal *1/2'''"
           :expand ((!R MA SZ V1
                         (!MI MA (MOD V2 256)
                              (!R (+ 1 MA)
                                   (+ -1 SZ)
                                   (FLOOR V2 256)
                                   ST)))))))
; but abandoned it because it requires testing that the v1 and v2 are integers; that
; makes the metafunction approach harder.  Now we use:
||#

(defthm !r-!r-same ; in place of !mi-!mi-same
  (implies (and (integerp ma)
                (<= 0 ma)
                (integerp sz)
                (<= 0 sz))
           (equal (!r ma sz v1
                       (!r ma sz v2 st))
                  (!r ma sz v1 st)))
  :hints (("Goal" :induct (!r-!r-same-hint ma sz v1 v2 st))
          ("Subgoal *1/2.4"
           :expand ((!R MA SZ V1 ST)
                    (!R MA SZ V2 ST)))
          ("Subgoal *1/2.4'"
           :expand ((!R MA SZ V1
                         (!MI MA (MOD V2 256)
                              (!R (+ 1 MA)
                                   (+ -1 SZ)
                                   (FLOOR V2 256)
                                   ST)))))
          ("Subgoal *1/2.3"
           :expand ((!R MA SZ V1 ST)
                    (!R MA SZ V2 ST)))
          ("Subgoal *1/2.3'"
           :expand ((!R MA SZ V1
                         (!MI MA (MOD V2 256)
                              (!R (+ 1 MA)
                                   (+ -1 SZ)
                                   (FLOOR V2 256)
                                   ST)))))
          ("Subgoal *1/2.2"
           :expand ((!R MA SZ V1 ST)
                    (!R MA SZ V2 ST)))
          ("Subgoal *1/2.2'"
           :expand ((!R MA SZ V1
                         (!MI MA 0
                              (!R (+ 1 MA)
                                   (+ -1 SZ)
                                   0
                                   ST)))))
          ("Subgoal *1/2.1"
           :expand ((!R MA SZ V1 ST)
                    (!R MA SZ V2 ST)))
          ))




; The replacement for !mi-!mi-diff is really two lemmas, depending on whether
; the outer write is above or below the inner write.  Technically the two
; lemmas below are variants of one another, but both must be stated so we try
; both instantations.

(defthm !r-!r-diff-below ; in place of !mi-!mi-diff
  (implies (and (integerp ma1)
                (<= 0 ma1)
                (integerp ma2)
                (<= 0 ma2)
                (integerp sz1)
                (<= 0 sz1)
                (integerp sz2)
                (<= 0 sz2)
                (<= (+ ma2 sz2) ma1))
           (equal (!r ma1 sz1 val1
                       (!r ma2 sz2 val2 st))
                  (!r ma2 sz2 val2
                       (!r ma1 sz1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((ma1 ma2 !r)))))

(defthm !r-!r-diff-above ; in place of !mi-!mi-diff
  (implies (and (integerp ma1)
                (<= 0 ma1)
                (integerp ma2)
                (<= 0 ma2)
                (integerp sz1)
                (<= 0 sz1)
                (integerp sz2)
                (<= 0 sz2)
                (<= (+ ma1 sz1) ma2))
           (equal (!r ma1 sz1 val1
                       (!r ma2 sz2 val2 st))
                  (!r ma2 sz2 val2
                       (!r ma1 sz1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((ma1 ma2 !r)))))

; Update/Access Expressions:

(defthm !r-r ; in place of !mi-mi
  (implies (and (stp st)
                (integerp ma)
                (<= 0 ma)
                (integerp sz)
                (<= 0 sz)
                (<= (+ ma sz) (ml st))
                (equal v (r ma sz st)))
           (equal (!r ma sz v st)
                  st)))

; End of Standard Series Redux

(in-theory (disable r !r))

; Pick a Point State Equivalence Theorem

; -----------------------------------------------------------------
; Theorems about NTH and NTHCDR

(local (in-theory (enable nth update-nth)))

;(defthm update-nth-update-nth-diff
;  (implies (and (natp a)
;                (natp b)
;                (not (equal a b)))
;           (equal (update-nth a x (update-nth b y s))
;                  (update-nth b y (update-nth a x s))))
;  :rule-classes ((:rewrite :loop-stopper ((b a)))))

(local
 (defthm nthcdr-is-last
   (implies (and (equal (len s1) (+ 1 i))
                 (integerp i)
                 (<= 0 i)
                 (true-listp s1))
            (equal (nthcdr i s1)
                   (list (nth (- (len s1) 1) s1))))))

(local
 (defthm nthcdr-update-nth
   (implies (and (natp i)
                 (natp j)
                 (< j i)
                 (< i (len a)))
            (equal (nthcdr i (update-nth j v a))
                   (nthcdr i a)))))

(local
 (defthm nthcdr-to-end
   (implies (and (natp i)
                 (<= (len x) i)
                 (true-listp x))
            (equal (nthcdr i x)
                   nil))))

; (encapsulate
;  nil
;  (local
;   (defthm nthcdr-cdr-update-nth-lemma
;     (implies (and (natp i)
;                   (natp min)
;                   (<= min i)
;                   (< (+ i 1) (len s1)))
;              (equal (nthcdr i (cdr (update-nth min v s1)))
;                     (nthcdr i (cdr s1))))))
;
;  (defthm nthcdr-cdr-update-nth
;    (implies (and (natp i)
;                  (natp min)
;                  (<= min i)
;                  (true-listp s1))
;             (equal (nthcdr i (cdr (update-nth min v s1)))
;                    (if (< (+ i 1) (len s1))
;                        (nthcdr i (cdr s1))
;                        nil)))))

(local
 (defthm nth-and-nthcdr-make-cons
   (implies (and (natp i)
                 (< i (len s1))
                 (equal (nth i s1) (nth i s2))
                 (equal (nthcdr i (cdr s1)) (nthcdr i (cdr s2)))
                 (equal (len s1) (len s2)))
            (equal (equal (nthcdr i s1) (nthcdr i s2))
                   t))))

; -----------------------------------------------------------------
; Random Basic Lemmas

(local
 (defthm mp-implies-true-listp
   (implies (mp x) (true-listp x))
   :hints (("Goal" :in-theory (enable mp)))
   :rule-classes :forward-chaining))

(local
 (defthm equal-len-0
   (equal (equal (len x) 0)
          (not (consp x)))))

; -----------------------------------------------------------------

; If there are no divergent addresses, the two ``states'' are equal.
; We quote ``states'' because memory may have been extended!  We define
; a weaker version of stp to develop this.

(defun weak-ml (st)
  (len (nth 2 st)))

(defun weak-stp (st)
  (and (true-listp st)
       (= (length st) 3)
;      (ip (nth 0 st))
;      (sp (nth 1 st))

       (< 0 (weak-ml st))   ; The strong r-1-!r hits address 0 so it better exist!
       (true-listp (nth 2 st))

;      (equal (len (nth 2 st)) 5312)
       t))



(defun-nx divergent-addr (i st1 st2)
  (declare (xargs :measure (nfix (- (min (weak-ml st1) (weak-ml st2)) (nfix i)))))
  (cond
   ((not (natp i)) 0)
   ((>= i (min (weak-ml st1) (weak-ml st2)))
    0)
   ((not (equal (mi i st1) (mi i st2)))
    i)
   (t (divergent-addr (+ 1 i) st1 st2))))

(defthm divergent-addr-legal
  (implies (and (weak-stp st1)
                (weak-stp st2))
           (< (divergent-addr i st1 st2)
              (min (weak-ml st1) (weak-ml st2))))
  :rule-classes :linear)

(defthm no-divergence-implies-m1=m2
  (implies (and (natp i)
                (weak-stp st1)
                (weak-stp st2)
                (equal (weak-ml st1) (weak-ml st2))
                (equal (mi (divergent-addr i st1 st2) st1)
                       (mi (divergent-addr i st1 st2) st2)))
           (equal (nthcdr i (nth 2 st1))
                  (nthcdr i (nth 2 st2))))
  :hints (("Goal" :in-theory (enable r mi)))
  :rule-classes nil)

(defthm no-divergence-implies-st1=st2
  (implies (and (weak-stp st1)
                (weak-stp st2)
                (equal (i st1) (i st2))
                (equal (s st1) (s st2))
                (equal (weak-ml st1) (weak-ml st2))
                (equal (mi (divergent-addr 0 st1 st2) st1)
                       (mi (divergent-addr 0 st1 st2) st2)))
           (equal st1 st2))
  :hints (("Goal" :use ((:instance no-divergence-implies-m1=m2 (i 0)))
           :in-theory (e/d (i s) (divergent-addr))))
  :rule-classes nil)

(encapsulate
 nil
 (local
  (defthm mi-!r-overlap
    (implies (and (natp a)
                  (natp b)
                  (natp sz)
                  (<= b a)
                  (< a (+ b sz)))
             (equal (mi a (!r b sz v st))
                    (logand 255 (ash v (* -8 (- a b))))))
    :hints (("Goal" :in-theory (enable !r)))))

; This theorem is useful when you we prove that two states have no divergent addresses.

 (defthm one-byte-read
   (implies (and (natp a)
                 (natp b)
                 (natp sz))
            (equal (mi a (!r b sz v st)) ; Note that we are reading one byte!
                   (if (< a b)
                       (mi a st)
                       (if (< a (+ b sz))
                           (logand 255 (ash v (* -8 (- a b))))
                           (mi a st)))))))

(in-theory (disable divergent-addr one-byte-read))

; -----------------------------------------------------------------
; Demonstration of a Drop Thm Proof

; To prove that two states, st1 and st2, are equal, prove they do not diverge
; on an arbitrary legal address, da.  Really, you need to prove they do not
; diverge on (divergent-addr 0 st1 st2), but when st1 and st2 are large
; expressions its faster to just use a variable.

(local
 (defthm demo-thm--no-divergence
   (implies (and (natp a)              ;;
                 (natp sz)             ;
                 (natp b)              ;   these hyps ensure that
                 (stp st)              ;   the writes are legal
                 (<= (+ a sz) (ml st)) ;
                 (<= (+ b sz) (ml st)) ;;

                 (natp da) ;;    and this is our arbitrary
                 )         ;;    divergent address

            (equal (mi da
                       (!r a sz v1
                           (!r b sz v2
                               (!r a sz v3 st))))
                   (mi da
                       (!r a sz v1
                           (!r b sz v2
                               st)))
                   ))
   :hints (("Goal" :in-theory (enable one-byte-read))))) ; <--- enable the one-byte read theorem

(defthm stp-implies-weak-stp
  (implies (stp st) (weak-stp st))
  :hints (("Goal" :in-theory (enable stp))))

(defthm weak-ml-!mi
  (implies (natp a)
           (equal (weak-ml (!mi a v st))
                  (max (+ 1 a) (weak-ml st))))
  :hints (("Goal" :in-theory (enable !mi))))

(defthm weak-ml-!r
  (implies (natp a)
           (equal (weak-ml (!r a sz v st))
                  (if (zp sz)
                      (weak-ml st)
                      (max (weak-ml st)
                           (+ (nfix a) sz)))))
  :hints (("Goal" :in-theory (enable !r !mi))))

(in-theory (disable weak-stp weak-ml))


; So they're equal:
(defthm demo-thm
  (implies (and (natp a)
                (natp sz)
                (natp b)
                (stp st)
                (<= (+ a sz) (ml st))
                (<= (+ b sz) (ml st)))
           (equal (!r a sz v1
                      (!r b sz v2
                          (!r a sz v3 st)))
                  (!r a sz v1
                      (!r b sz v2
                          st))))
  :hints (("Goal" :use (:instance no-divergence-implies-st1=st2
                                  (st1 (!r a sz v1
                                           (!r b sz v2
                                               (!r a sz v3 st))))
                                  (st2 (!r a sz v1
                                           (!r b sz v2
                                               st))))))
  :rule-classes nil)

; -----------------------------------------------------------------
; A Stronger One-Byte Read Theorem

(local
 (defthm !mi-default-1
   (implies (not (natp a))
            (equal (!mi a v st) (!mi 0 v st)))
   :hints (("Goal" :in-theory (enable !mi update-nth)))))

(local
 (encapsulate
  nil
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm !r-default-1-non-number
    (implies (and (not (acl2-numberp a))
                  (natp sz))
             (equal (!r a sz v st)
                    (!r 0 sz v st)))
    :hints (("Goal"
             :induct (!r a sz v st)
             :in-theory (e/d (!r) nil)))
    :rule-classes nil)

  (defthm !r-default-1-number-not-integer
    (implies (and (acl2-numberp a)
                  (not (integerp a))
                  (natp sz))
             (equal (!r a sz v st)
                    (if (zp sz)
                        st
                        (!mi 0 (logand (ash v (* -8 (- sz 1))) 255) st))))
    :hints (("Goal"
             :induct (!r a sz v st)
             :in-theory (e/d (!r) nil)))
    :rule-classes nil)

  (local
   (defthm !r-default-1-negative-integer-case-1
     (implies (and (integerp a)
                   (< a 0)
                   (natp sz)
                   (<= (+ a sz) 0))
              (equal (!r a sz v st)
                     (if (zp sz)
                         st
                         (!mi 0 (logand (ash v (* -8 (+ -1 sz))) 255) st))))
     :hints (("Goal"
              :induct (!r a sz v st)
              :in-theory (e/d (!r) nil)))))

  (defthm ash-0
    (equal (ash v 0) (ifix v)))

  (local
   (defthm ash-ash-lemma1
     (implies (and (integerp a) (< a 0))
              (equal (ASH (ASH V -8) (+ 8 (* 8 A)))
                     (ASH V (* 8 A))))))

  (defthm ash-ash-lemma2
    (implies (and (natp a) (natp b))
             (equal (ash (ash v (* -8 a)) (* -8 b))
                    (ash v (* -8 (+ a b))))))

  (defthm logand-commutes1
    (and (equal (logand x y)(logand y x))
         (equal (logand x (logand y z))
                (logand y (logand x z)))))
  (defthm logand-absorbtion
    (equal (logand x (logand x y))
           (logand x y))
    :hints (("Goal" :in-theory (enable logand))))

  (local
   (defthm !r-default-1-negative-integer-case-2
     (implies (and (integerp a)
                   (< a 0)
                   (natp sz)
                   (not (<= (+ a sz) 0)))
              (equal (!r a sz v st)
                     (!r 0 (+ a sz)
                         (ash v (* -8 (- a)))
                         (!mi 0 (logand 255 (ash v (* -8 (- (- a) 1)))) st)
                         )))
     :hints (("Goal"
              :induct (!r a sz v st)
              :in-theory (e/d (!r) (ash-to-floor))))))

  (defthm !r-default-1-negative-integer
    (implies (and (integerp a)
                  (< a 0)
                  (natp sz))
             (equal (!r a sz v st)
                    (if (<= (+ a sz) 0)
                        (if (zp sz)
                            st
                            (!mi 0 (logand (ash v (* -8 (+ -1 sz))) 255) st))
                        (!r 0 (+ a sz)
                            (ash v (* -8 (- a)))
                            (!mi 0 (logand 255 (ash v (* -8 (- (- a) 1)))) st)
                            ))))
    :rule-classes nil)))

(local
 (defthm !r-default-1
   (implies (and (not (natp a))
                 (natp sz))
            (equal (!r a sz v st)
                   (if (acl2-numberp a)
                       (if (integerp a)
                           (if (<= (+ a sz) 0)
                               (if (zp sz)
                                   st
                                   (!mi 0 (logand (ash v (* -8 (+ -1 sz))) 255) st))
                               (!r 0 (+ a sz)
                                   (ash v (* -8 (- a)))
                                   (!mi 0 (logand 255 (ash v (* -8 (- (- a) 1)))) st)
                                   ))
                           (if (zp sz)
                               st
                               (!mi 0 (logand (ash v (* -8 (- sz 1))) 255) st)))
                       (!r 0 sz v st))))
   :hints (("Goal"
            :use (!r-default-1-non-number
                  !r-default-1-number-not-integer
                  !r-default-1-negative-integer)))))


; In the following version of one-byte-read, we have no hypotheses about b.  In
; the regular version, we require b to be a natural.  Both versions are
; disabled by default.

(defthm one-byte-read-stronger
  (implies (and (natp a)
                (natp sz))
           (equal (mi a (!r b sz v st))
                  (if (natp b)
                      (if (< a b)
                          (mi a st)
                          (if (< a (+ b sz))
                              (logand 255 (ash v (* -8 (- a b))))
                              (mi a st)))
                      (if (acl2-numberp b)
                          (if (integerp b)
                              (if (<= (+ b sz) 0)
                                  (if (zp sz)
                                      (mi a st)
                                      (mi a (!r 0 1 (logand (ash v (* -8 (+ -1 sz))) 255) st)))
                                  (if (equal a 0)
                                      (logand 255 (ash v (* -8 (- b))))
                                      (if (< a (+ b sz))
                                          (logand 255 (ash v (* -8 (+ a (- b)))))
                                         (mi a st))))
                              (if (zp sz)
                                  (mi a st)
                                  (if (zp a)
                                      (logand 255 (ash v (* -8 (- sz 1))))
                                      (mi a st))))
                          (if (equal a 0)
                              (if (zp sz)
                                  (mi 0 st)
                                  (logand 255 v))
                              (if (< a sz)
                                  (logand 255 (ash v (* -8 a)))
                                  (mi a st)))))))

; The odd collection of runes disabled below is due to the evolutionary history
; of this proof.  We first developed in after certifying
; byte-addressed-state.lisp and so various arithmetic lemmas were not available
; during the original proof.  The lemmas developed then for the proof were
; seeing a slightly different normal form.  Rather than change the lemmas, we
; just shut down certain arithmetic rules.

  :hints (("Goal" :in-theory (e/d (one-byte-read r-1-!mi)
                                  (mod floor ash logior logxor
                                       ash-to-floor
                                       acl2::logand-constant-mask
                                       acl2::|(* x (- y))|)))
          ("Subgoal 12" :cases ((< b 0)))
          ("Subgoal 11" :cases ((< b 0)))))

(defthm weak-stp-implies-weak-ml-non-zero
  (implies (weak-stp st)
           (< 0 (weak-ml st)))
  :hints (("Goal" :in-theory (enable weak-stp weak-ml)))
  :rule-classes :linear)

(defthm weak-ml-!r-stronger
  (implies (and (weak-stp st)
                (natp sz))
           (equal (weak-ml (!r a sz v st))
                  (if (acl2-numberp a)
                      (if (integerp a)
                          (if (natp a)
                              (if (zp sz)
                                  (weak-ml st)
                                  (max (weak-ml st)
                                       (+ a sz)))
                              (if (<= (+ a sz) 0)
                                  (if (zp sz)
                                      (weak-ml st)
                                      (max (+ 1 a) (weak-ml st)))
                                  (max (+ a sz)
                                       (max 1 (weak-ml st)))))
                          (if (zp sz)
                              (weak-ml st)
                              (max 1 (weak-ml st))))
                      (max sz (weak-ml st)))))
  :hints (("Subgoal 2'" :in-theory (enable !r))))

; -----------------------------------------------------------------
; Demonstration of a Stronger Drop Thm Proof

; Here we reprise the previous demo, without hypotheses about the writes, other
; than the sizes.

; To prove that two states, st1 and st2, are equal, prove they do not diverge
; on an arbitrary legal address, da.  Really, you need to prove they do not
; diverge on (divergent-addr 0 st1 st2), but when st1 and st2 are large
; expressions its faster to just use a variable.

; Again, the lemmas in the theory below were just those actually used in the
; original proof of this theorem OUTSIDE of this book.

(local
 (defthm stronger-demo-thm--no-divergence
   (implies (and (natp sz)

                 (natp da)       ;;    this is our arbitrary
                 )               ;;    divergent address

            (equal (mi da
                       (!r a sz v1
                           (!r b sz v2
                               (!r a sz v3 st))))
                   (mi da
                       (!r a sz v1
                           (!r b sz v2
                               st)))
                   ))
   :hints (("Goal" :in-theory '((:COMPOUND-RECOGNIZER acl2::NATP-COMPOUND-RECOGNIZER)
                                (:COMPOUND-RECOGNIZER acl2::ZP-COMPOUND-RECOGNIZER)
                                (:DEFINITION ASH)
                                (:DEFINITION FIX)
                                (:DEFINITION FLOOR)
                                (:DEFINITION IFIX)
                                (:DEFINITION ML)
                                (:DEFINITION NATP)
                                (:DEFINITION NOT)
                                (:EXECUTABLE-COUNTERPART <)
                                (:EXECUTABLE-COUNTERPART ACL2-NUMBERP)
                                (:EXECUTABLE-COUNTERPART BINARY-*)
                                (:EXECUTABLE-COUNTERPART BINARY-+)
                                (:EXECUTABLE-COUNTERPART EQUAL)
                                (:EXECUTABLE-COUNTERPART NATP)
                                (:EXECUTABLE-COUNTERPART NOT)
                                (:EXECUTABLE-COUNTERPART RATIONALP)
                                (:EXECUTABLE-COUNTERPART UNARY--)
                                (:EXECUTABLE-COUNTERPART UNARY-/)
                                (:EXECUTABLE-COUNTERPART ZP)
                                (:REWRITE ASH-0)
                                (:REWRITE COMMUTATIVITY-OF-*)
                                (:REWRITE COMMUTATIVITY-OF-+)
                                (:REWRITE DISTRIBUTIVITY)
                                (:REWRITE LOGAND-ABSORBTION)
                                (:REWRITE LOGAND-COMMUTES1)
                                (:REWRITE ONE-BYTE-READ-STRONGER)
                                (:REWRITE UNICITY-OF-0)
                                (:REWRITE UNICITY-OF-1)
                                (:TYPE-PRESCRIPTION BINARY-LOGAND)
                                (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)
                                (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))))))



(defthm weak-stp-!mi
  (implies (and (weak-stp st)
                (natp v)
                (< v 256))
           (weak-stp (!mi a v st)))
  :hints (("Goal" :in-theory (enable weak-stp weak-ml !mi))))


(defthm weak-stp-!r
  (implies (weak-stp st)
           (weak-stp (!r a sz v st)))
  :hints (("Goal" :in-theory (enable weak-stp !r))))

; So they're equal:   <------------ this claim isn't true.
(defthm stronger-demo-thm
  (implies (and (natp sz)
                (stp st)

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

; These hyps are undesirable because they constrain the writes but they are
; necessary if we go through the weaker right now because no-divergence-implies-st1=st2 requires the two
; ``states'' to be stps.  I would like to weaken stp to only require that they
; be the right shape: (* * (* * * ...)) and have the same len mem.  Let's call
; the shape predicate weak-stp and the length function weak-ml.  Now we need
; the theorems that !r preserves weak-stp and that the weak-ml of !r is the max
; of that of the initial state and the obvious.  Then we need to extend the
; no-divergence-implies-st1=st2 to give us the same weak-mls.

;               (natp a)
;               (natp b)
;               (natp sz)
;               (< (+ a sz) (ml st))
;               (< (+ b sz) (ml st))
;
; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
                )
           (equal (!r a sz v1
                      (!r b sz v2
                          (!r a sz v3 st)))
                  (!r a sz v1
                      (!r b sz v2
                          st))))

  :hints (("Goal" :use (:instance no-divergence-implies-st1=st2
                                  (st1 (!r a sz v1
                                           (!r b sz v2
                                               (!r a sz v3 st))))
                                  (st2 (!r a sz v1
                                           (!r b sz v2
                                               st))))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Absorbtion Theorems

(encapsulate
 nil
 (local
  (defthm !r-simple-absorbtion-lemma1
    (equal (!nth addr byte1 (!nth addr byte2 lst))
           (!nth addr byte1 lst))
    :hints (("Goal" :in-theory (enable !nth)))))

 (local
  (defthm !r-simple-absorbtion-lemma2
    (equal (!mi addr byte1 (!mi addr byte2 st))
           (!mi addr byte1 st))
    :hints (("Goal" :in-theory (enable !mi)))))

 (local
  (defthm !r-simple-absorbtion-lemma3
    (implies (not (zp sz))
             (equal (!r addr sz val (!mi addr byte st))
                    (!r addr sz val st)))
    :hints (("Goal" :in-theory (enable !r)))))

 (defthm !r-simple-absorbtion
   (implies (natp sz)
            (equal (!r addr1 sz val1 (!r addr1 sz val2 st))
                   (!r addr1 sz val1 st)))
   :hints (("Goal"
            :cases ((natp addr1))))))

(encapsulate
 nil
 (local
  (defthm lemma1
    (IMPLIES (AND (INTEGERP A1)
                  (<= 0 A1)
                  (INTEGERP N1)
                  (<= 0 N1)
                  (INTEGERP A2)
                  (<= 0 A2)
                  (EQUAL (!R A1 N1 V1 ST1)
                         (!R A1 N1 V1 ST2)))
             (equal (EQUAL (!R A1 N1 V1 (!MI A2 i ST1))
                           (!R A1 N1 V1 (!MI A2 i ST2)))
                    t))
    :hints (("Goal"
             :in-theory (enable !r))

            ("Subgoal *1/7.2'"
             :cases ((< a1 a2)
                     (equal a1 a2)
                     (< a2 a1)))
            ("Subgoal *1/7.1'"
             :cases ((< a1 a2)
                     (equal a1 a2)
                     (< a2 a1))))))

 (local
  (defthm !r-inner-absorbtion-natp-case
    (implies (and (natp a1)
                  (natp n1)
                  (natp a2)
                  (natp n2)
                  (equal (!r a1 n1 v1 st1)
                         (!r a1 n1 v1 st2)))
             (equal (equal (!r a1 n1 v1
                               (!r a2 n2 v2 st1))
                           (!r a1 n1 v1
                               (!R a2 n2 v2 st2)))
                    t))
    :hints (("Goal"
             :in-theory (enable !r)
             :induct (list (!r a2 n2 v2 st1)
                           (!r a2 n2 v2 st2))))))

 (local
  (defthm !m-simple-absorbtion-lemma
    (IMPLIES (EQUAL (CDR lst1)
                    (CDR lst2))
             (equal (EQUAL (CDR (!NTH A W lst1))
                           (CDR (!NTH A W lst2)))
                    t))))

 (defthm !m-simple-absorbtion
   (implies (equal (!mi 0 v st1)
                   (!mi 0 v st2))
            (equal (equal (!mi 0 v (!mi a w st1))
                          (!mi 0 v (!mi a w st2)))
                   t))
   :hints (("Goal" :in-theory (enable !mi))))

 (defthm !m-inner-absorbtion
   (implies (equal (!mi 0 v st1)
                   (!mi 0 v st2))
            (equal (equal (!mi 0 v (!r a n w st1))
                          (!mi 0 v (!r a n w st2)))
                   t))
   :hints (("Goal"
            :in-theory (enable !r))))

 (local
  (defthm !r-0-!m-0
    (implies (natp sz)
             (equal (!r 0 sz v (!mi 0 w st))
                    (if (zp sz)
                        (!mi 0 w st)
                        (!r 0 sz v st))))
    :hints (("Goal" :in-theory (enable !r)))))


 (defthm !r-base-case
   (equal (!r a 0 v st) st)
   :hints (("Goal" :in-theory (enable !r))))


 (defthm !r-inner-absorbtion
   (implies (and (natp n1)
                 (natp n2)
                 (equal (!r a1 n1 v1 st1)
                        (!r a1 n1 v1 st2)))
            (equal (equal (!r a1 n1 v1
                              (!r a2 n2 v2 st1))
                          (!r a1 n1 v1
                              (!R a2 n2 v2 st2)))
                   t))
   :hints (("Goal"
            :cases ((and (natp a1) (natp a2))
                    (and (natp a1) (not (natp a2)))
                    (and (not (natp a1)) (natp a2))
                    (and (not (natp a1)) (not (natp a2))))))))

; To prove mx-rover correct we need the basic read-over-write theorems but for
; the mixed cases.  (r a n ...) peels off one byte at a time but the function
; above does peels off varying numbers of bytes, so the lemmas we need about R
; and !R are inductive.  Here they are:

(defthm integerp-product-by-expt
  (implies (and (integerp (* v (expt base n)))
                (<= n m)
                (natp base)
                (integerp v)
                (integerp n)
                (integerp m))
           (integerp (* v (expt base m))))
  :hints (("Goal"
           :use (:instance (:theorem (implies (and (natp base)
                                                   (integerp v)
                                                   (integerp n)
                                                   (natp delta)
                                                   (integerp (* v (expt base n))))
                                              (integerp (* v (expt base (+ n delta))))))
                           (delta (- m n)))
           :in-theory (e/d (acl2::scatter-exponents-theory)
                           (acl2::gather-exponents-theory)))))

; We need to express (expt 2 (* 8 sum)) as (expt 256 sum), except the product
; is distributed over the sum, there are 1, 2, or 3 terms in the sums in
; question, and some of the summed terms are negative, turning the factor of 8
; into -8.  That means that we need several first order patterns to catch the
; relevant combinations.  It turns out six lemmas are needed!  Of course, we
; could express the general pattern with a hypothesis of (mod sum 8) = 0, but
; that is probably slow.  This is a natural application of metafunctions --
; recognizing a sum of products by +/-8 -- but I'll just prove the six rules
; and get on with it.

; Because I had a hard time recognizing if my rules were all distinct I imposed
; a naming discipline.  When the suffix starts with P8 or or N8 it means the
; sum-of-products starts with positive or negative 8.  Absent P8 or N8, no
; leading constant is present.  Next follows a sequence of Ps and/or Ns, where
; P means a factor of 8 and N means a factor of -8.

(defthm expt-2-8*sum-PN
  (implies (and (integerp a) (integerp b))
           (equal (expt 2 (+ (* 8 a) (* -8 b)))
                  (expt 256 (+ a (- b))))))

(defthm expt-2-*-sum-N8P
  (implies (integerp a)
           (equal (expt 2 (+ -8 (* 8 a)))
                  (expt 256 (+ -1 a)))))

(defthm expt-2-*-sum-PPN
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (expt 2 (+ (* 8 A) (* 8 b) (* -8 c)))
                  (expt 256 (+ a b (- c))))))

(defthm expt-2-*-sum-PNN
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (expt 2 (+ (* 8 A) (* -8 B) (* -8 c)))
                  (expt 256 (+ a (- b) (- c))))))

(defthm expt-2-*-sum-P8PNN
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (expt 2 (+ 8 (* 8 A) (* -8 B) (* -8 c)))
                  (expt 256 (+ 1 a (- b) (- c))))))

(defthm expt-2-*-sum-N8PPN
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (expt 2 (+ -8 (* 8 a) (* 8 b) (* -8 c)))
                  (expt 256 (+ -1 a b (- c))))))

; The following two lemmas were originally named from the names of the subgoals
; in mx-rover-correct-lemma1 for which they were needed.  In fact, these two
; lemmas are exactly those subgoals except certain irrelevant details have been
; dropped.  These lemmas are provable by simplification -- but not in the
; context of the induction done in the proof mx-rover-correct-lemma1!  So I
; had to lift them out of that proof and prove them at the top-level.
; Subsequently I changed the statement of mx-rover-correct-lemma1, by
; replacing a (not (zp n)) hyp with (natp n), and that renamed the subgoals.
; So these lemmas are not actually used at the points in that proof that their
; names suggest.  But they are used.  Indeed, the second of these lemmas is
; used in a subsequent proof too.

(local
  (defthm |MX-ROVER-CORRECT-SUBGOAL-*1/8.1'''|

; This is just the indicated subgoal of (the old version of)
; mx-rover-correct-lemma1, which is not provable within the larger proof
; attempt but is provable at the top-level.  I have eliminated hyps that
; introduce free vars.

    (IMPLIES (AND ;(INTEGERP I)
                  ;(NOT (INTEGERP (* R (EXPT 256 (+ (- A) B (- N))))))
                  ;(<= 0 (EXPT 256 (+ A (- B) N)))
                  (<= 0 R)
                  ;(< R (EXPT 256 (+ A (- B) N)))
                  (NOT (EQUAL R 0))
                  ;(< (* R (EXPT 256 (+ (- A) B (- N)))) 1)
                  ;(NOT (ZP N))
                  (INTEGERP R)
                  (NOT (INTEGERP (* R (EXPT 256 (+ -1 (- A) B)))))
                  ;(EQUAL (FLOOR R (EXPT 256 (+ 1 A (- B))))
                  ;       (R (+ 1 A)
                  ;          (+ -1 N)
                  ;          (!R B K (+ R (* I (EXPT 256 (+ A (- B) N))))
                  ;              ST)))
                  (INTEGERP A)
                  (<= 0 A)
                  (INTEGERP B)
                  (<= 0 B)
                  ;(NOT (ZP K))
                  (<= B A)
                  ;(<= (+ A N) (+ B K))
                  ;(< A (+ B K))
                  (INTEGERP (* R (EXPT 256 (+ (- A) B))))
                  (INTEGERP (* (EXPT 256 (+ (- A) B))
                               (MOD R (EXPT 256 (+ 1 A (- B)))))))
             (equal
              (EQUAL (* R (EXPT 256 (+ (- A) B)))
                     (+ (* 256 (FLOOR R (EXPT 256 (+ 1 A (- B)))))
                        (* 256
                           (MOD (* (EXPT 256 (+ -1 (- A) B))
                                   (MOD R (EXPT 256 (+ 1 A (- B)))))
                                1))))
              t))))

(local  ; Note: This lemma is actually used in the proofs of both
        ; mx-rover-correct-lemma1 and mx-rover-correct-lemma2.
        ; Do not encapsulate it around just the first one!

  (defthm |MX-ROVER-CORRECT-SUBGOAL-*1/7.1'''|
    (IMPLIES (AND ;(INTEGERP I)
                  ;(NOT (INTEGERP (* R (EXPT 256 (+ (- A) B (- N))))))
                  ;(<= 0 (EXPT 256 (+ A (- B) N)))
                  (<= 0 R)
                  ;(< R (EXPT 256 (+ A (- B) N)))
                  (NOT (EQUAL R 0))
                  ;(< (* R (EXPT 256 (+ (- A) B (- N)))) 1)
                  ;(NOT (ZP N))
                  (INTEGERP R)
                  (NOT (INTEGERP (* R (EXPT 256 (+ -1 (- A) B)))))
                  ;(EQUAL (FLOOR R (EXPT 256 (+ 1 A (- B))))
                  ;       (R (+ 1 A)
                  ;          (+ -1 N)
                  ;          (!R B K (+ R (* I (EXPT 256 (+ A (- B) N))))
                  ;              ST)))
                  (INTEGERP A)
                  (<= 0 A)
                  (INTEGERP B)
                  (<= 0 B)
                  ;(NOT (ZP K))
                  (<= B A)
                  ;(<= (+ A N) (+ B K))
                  ;(< A (+ B K))
                  (INTEGERP (* R (EXPT 256 (+ (- A) B)))))
             (INTEGERP (* (EXPT 256 (+ (- A) B))
                          (MOD R (EXPT 256 (+ 1 A (- B)))))))))

(defthm mx-rover-correct-lemma1
   (implies (and (natp a)
                 (natp n)
                 (natp b)
                 (not (zp k))
                 (<= b a)
                 (<= (+ a n) (+ b k)))
            (equal (r a n (!r b k v st))
                   (mod (ash v (* -8 (- a b))) (expt 256 n))))
   :hints (("Goal" :in-theory (enable r)
            :induct (R A N (!R B K V ST)))))

(defthm mx-rover-correct-lemma2
  (implies (and (natp a)
                (natp n)
                (natp b)
                (not (zp k))
                (<= b a)
                (< a (+ b k))
                (< (+ b k) (+ a n)))
           (equal (r a n (!r b k v st))
                  (+ (mod (ash v (* -8 (- a b)))
                          (expt 256 (- (+ b k) a)))
                     (ash (r (+ b k) (- n (- (+ b k) a)) st)
                          (* 8 (- (+ b k) a))))))
  :hints (("Goal" :in-theory (enable r)
           :induct (R A N (!R B K V ST)))))

(defthm mx-rover-correct-lemma3
  (implies (and (natp a)
                (natp n)
                (natp b)
                (not (zp k))
                (< a b)
                (< b (+ a n)))
           (equal (r a n (!r b k v st))
                  (+ (r a (- b a) st)
                     (ash (r b (- n (- b a))
                             (!r b k v st)) (* 8 (- b a))))))
  :hints (("Goal" :in-theory (enable r)
           :induct (R A N (!R B K V ST)))))

(in-theory (disable mx-rover-correct-lemma1
                    mx-rover-correct-lemma2
                    mx-rover-correct-lemma3))
