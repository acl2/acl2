; Defabsstobj Example 1
; Copyright (C) 2012, Regents of the University of Texas
; Written by Matt Kaufmann, July, 2012 (updated Nov. and Dec., 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Warning: If you change this book, then make corresponding changes to the
; discussion of this book in :doc defabsstobj.

; Note: A separate example, one which is perhaps slightly more advanced and is
; probably more interesting, may be found in the book
; defabsstobj-example-2.lisp.  That example focuses especially on avoiding an
; expensive guard-check that would be needed if using a concrete stobj.  The
; present example presents, at the end of this file, a different advantage of
; abstract stobjs: avoidance of hypotheses in rewrite rules.

; Also see defabsstobj-example-3.lisp for a discussion of :protect t.

(in-package "ACL2")

; Below, I typically use the suffix "$c" to suggest "concrete", for the
; concrete foundational stobj that will be used in our defabsstobj event.
; Similarly, I typically use the suffix "$a" to denote "abstract", for logical
; definitions to use for our desired stobj.  If one prefers, one can think of
; "$c" as suggesting "computational" and "$a" as suggesting "alternate".

(defstobj st$c

; This is the concrete stobj, to correspond to the abstract stobj ultimately
; defined below.  Note that it is a separate stobj in its own right.  We will
; write various single-threaded functions that access and update this
; structure, some of which will become :EXEC fields for functions defined for
; the abstract stobj.

  (mem$c :type (array (integer 0 *) (100))
         :initially 0 :resizable nil)
  (misc$c :initially 0))

; To spice things up, let's consider an invariant on the concrete stobj saying
; that entry 0 is even, and let's make an even stronger invariant on the
; abstract stobj saying that every entry is even.

(defund mem$c-entryp (v)
  (declare (xargs :guard (integerp v)))
  (evenp v))

; The function st$cp+ has no special "standing", but we use it in the
; correspondence predicate (st$corr) defined below.

(defun st$cp+ (st$c)
  (declare (xargs :stobjs st$c))
  (and (st$cp st$c)
       (mem$c-entryp (mem$ci 0 st$c))))

; We now introduce the logical recognizer for the MAP component of the abstract
; stobj, to serve as an alternate implementation of memory.  Just for fun, we
; restrict the domain to numbers less than 50 (not just 100 as for st$c) and
; the range to natural numbers that are even (not just natural numbers as for
; st$c).

(defun map$ap (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((atom (car x)) nil)
        (t (and (natp (caar x))
                (< (caar x) 50)
                (natp (cdar x))
                (mem$c-entryp (cdar x))
                (map$ap (cdr x))))))

; The following function recognizes our abstract stobj, which has a MISC field
; unchanged from st$c but has a MAP field instead of a MEM field.  Just for
; fun, we switch the order of fields in our abstract stobj from the
; corresponding concrete stobj (i.e., the foundational stobj for the abstract
; stobj): here, misc before mem rather than mem before misc.  But note that
; there are no a priori restrictions on the shape of an abstract stobj; it need
; not have the same number of "fields" as the concrete stobj, and its
; organization need not be a list of "fields" at all!  In the example in
; defabsstobj-example-2.lisp, the abstract stobj is actually empty!

(defun st$ap (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (map$ap (nth 1 x))))

(defun misc$a (st$a)
  (declare (xargs :guard (st$ap st$a)))
  (nth 0 st$a))

(defun update-misc$a (v st$a)
  (declare (xargs :guard (st$ap st$a)))
  (update-nth 0 v st$a))

; The following lemma is used in guard verification for lookup$a (below).

(defthm map$ap-forward-to-eqlable-alistp
  (implies (map$ap x)
           (eqlable-alistp x))
  :rule-classes :forward-chaining)

; We will export read and write functions for our abstract stobj, defined using
; alist-based functions lookup$a and update$a, respectively.

(defun lookup$a (k st$a)
  (declare (type (integer 0 49) k)
           (xargs :guard (st$ap st$a)))
  (let* ((map (nth 1 st$a))
         (pair (assoc k map)))
    (if pair (cdr pair) 0)))

(defun update$a (k val st$a)
  (declare (type (integer 0 49) k)
           (type (integer 0 *) val)
           (xargs :guard (and (st$ap st$a)
                              (mem$c-entryp val))))
  (update-nth 1
              (put-assoc k val (nth 1 st$a))
              st$a))

; Our next task is to define a required function, which we call st$corr.  We
; have a choice in how it is defined, provided we can discharge the
; corresponding proof obligations, which are labeled below using names that end
; in a suffix of the form {...}.

(defun corr-mem (n st$c st$a)

; This user-defined function supports the definition of st$corr, below.  This
; is of logical interest only, so no guard is considered.

  (declare (xargs :stobjs st$c :verify-guards nil))
  (cond ((zp n) t)
        (t (let ((i (1- n)))
             (and (equal (mem$ci i st$c)
                         (lookup$a i st$a))
                  (corr-mem i st$c st$a))))))

(defun st$corr (st$c st$a)
; This is of logical interest only, so no guard is given.
  (declare (xargs :stobjs st$c :verify-guards nil))
  (and (st$cp+ st$c)
       (st$ap st$a)
       (equal (misc$c st$c) (misc$a st$a))
       (corr-mem 50 st$c st$a)))

; We use defun-nx below so that we can call create-st$c.  But we could just as
; well use the alternate form, 0, as indicated below.

(defun-nx create-st$a ()
  (declare (xargs :guard t))
  (list (nth 1 (create-st$c)) ; or: initial value of misc$c, i.e., 0
        nil                   ; mem
        ))

; Nice theorem, but we don't need it:
(defthm st$corr-implies-st$cp+
  (implies (st$corr st$c st$a)
           (st$cp+ st$c))
  :rule-classes nil)

; The next theorem is also a nice theorem that we don't need.  Note that the
; {preserved} theorems guarantee that all abstract stobjs encountered during
; evaluation satisfy st$a.

(defthm st$corr-thm
  (implies (st$corr st$c st)
           (st$ap st))
  :rule-classes nil)

; We now start proving the theorems expected by our defabsstobj event.  It is
; not expected that we know in advance exactly what form they should take.
; Rather, we can evaluate the defabsstobj event here, and it will print out all
; necessary defthm events (before failing).  We can then copy those defthm
; events into the file, for example starting with the following.

(DEFTHM CREATE-ST{CORRESPONDENCE}
  (ST$CORR (CREATE-ST$C) (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-ST{PRESERVED}
  (ST$AP (CREATE-ST$A))
  :RULE-CLASSES NIL)

; The hypothesis (st$ap st) below is not needed for the following formula to be
; a theorem; similarly for update-misc{correspondence} as well.  However, this
; hypothesis is expected by defabsstobj.

(DEFTHM MISC{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST)
                (ST$AP ST))
           (EQUAL (MISC$C ST$C)
                  (MISC$A ST)))
  :RULE-CLASSES NIL)

(defthm update-misc{correspondence}-lemma
  (implies (corr-mem k st$c st)
           (corr-mem k
                     (update-misc$c v st$c)
                     (update-misc$a v st)))
  :rule-classes nil)

(DEFTHM UPDATE-MISC{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST)
                (ST$AP ST))
           (ST$CORR (UPDATE-MISC$C V ST$C)
                    (UPDATE-MISC$A V ST)))
  :hints (("Goal" :use ((:instance update-misc{correspondence}-lemma
                                   (k 50)))))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-MISC{PRESERVED}
  (IMPLIES (ST$AP ST)
           (ST$AP (UPDATE-MISC$A V ST)))
  :RULE-CLASSES NIL)

; There could have been defthm events named misc{guard-thm} and
; update-misc{guard-thm} for us to prove.  However, they are recognized as
; trivial by ACL2, because the guards of misc$c and update-misc$c are (st$cp
; st$c), which is optimized away since ACL2 knows that this will hold during
; evaluation.

; The proof of lookup{correspondence} requires an inductive lemma.

(encapsulate
 ()
 (local
  (defthm corr-mem-memi
    (implies (and (corr-mem bound st$c st)
                  (natp bound)
                  (natp i) (< i bound))
             (equal (mem$ci i st$c)
                    (lookup$a i st)))
    :rule-classes nil))

 (DEFTHM LOOKUP{CORRESPONDENCE}
   (IMPLIES (AND (ST$CORR ST$C ST)
                 (INTEGERP I) (<= 0 I) (<= I 49)
                 (ST$AP ST))
            (EQUAL (MEM$CI I ST$C)
                   (LOOKUP$A I ST)))
   :hints (("Goal" :use ((:instance corr-mem-memi
                                    (bound 50)))))
   :RULE-CLASSES NIL))

; There is no particular reason to make the following required theorem local.
; But we do in order to illustrate that it is OK to do so (because required
; events are allowed to be missing when skipping proofs).

(local
 (DEFTHM LOOKUP{GUARD-THM}
   (IMPLIES (AND (ST$CORR ST$C C)
                 (INTEGERP I)
                 (<= 0 I)
                 (<= I 49)
                 (ST$AP ST))
            (AND (INTEGERP I)
                 (<= 0 I)
                 (< I (MEM$C-LENGTH ST$C))))
   :RULE-CLASSES NIL)
 )

; The following theorem was originally local to an encapsulate surrounding
; corr-mem-update-memi, but it is also useful for st-equal, later, and it's a
; pretty theorem.  So we make it global here.

(defthm assoc-equal-put-assoc-equal
  (equal (assoc-equal k1 (put-assoc-equal k2 v a))
         (if (equal k1 k2) (cons k1 v) (assoc-equal k1 a))))

; Several lemmas contribute to the proof of our next required theorem,
; update{correspondence}.

(encapsulate
 ()

 (local
  (defthm mem$cp-update-nth
    (implies (and (natp i)
                  (< i (len mem))
                  (natp v)
                  (mem$cp mem))
             (mem$cp (update-nth i v mem)))))

 (local
  (defthm map$ap-put-assoc-equal
    (implies (and (natp i)
                  (< i 50)
                  (natp v)
                  (mem$c-entryp v)
                  (map$ap mem))
             (map$ap (put-assoc-equal i v mem)))))

 (local
  (defthm corr-mem-update-memi
    (implies (and (natp bound)
                  (<= bound 50)
                  (equal rest$c (cdr st$c))
                  (equal rest$a (cdr st))
                  (st$cp+ st$c)
                  (st$ap st)
                  (corr-mem bound st$c st)
                  (natp i)
                  (natp v))
             (corr-mem bound
                       (update-nth *mem$ci*
                                   (update-nth i v (nth *mem$ci* st$c))
                                   st$c)
                       (update-nth 1
                                   (put-assoc-equal i v (nth 1 st))
                                   st)))))

 (DEFTHM UPDATE{CORRESPONDENCE}
   (IMPLIES (AND (ST$CORR ST$C ST)
                 (INTEGERP I) (<= 0 I) (<= I 49)
                 (INTEGERP V) (<= 0 V)
                 (ST$AP ST)
                 (MEM$C-ENTRYP V))
            (ST$CORR (UPDATE-MEM$CI I V ST$C)
                     (UPDATE$A I V ST)))
   :hints (("Goal" :in-theory (disable nth update-nth)))
   :RULE-CLASSES NIL))

(DEFTHM UPDATE{PRESERVED}
  (IMPLIES (AND (INTEGERP I) (<= 0 I) (<= I 49)
                (INTEGERP V) (<= 0 V)
                (ST$AP ST)
                (MEM$C-ENTRYP V))
           (ST$AP (UPDATE$A I V ST)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE{GUARD-THM}
  (IMPLIES (AND (ST$CORR ST$C C)
                (INTEGERP I) (<= 0 I) (<= I 49)
                (INTEGERP V) (<= 0 V)
                (ST$AP ST)
                (MEM$C-ENTRYP V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (MEM$C-LENGTH ST$C))
                (INTEGERP V)
                (<= 0 V)))
  :RULE-CLASSES NIL)

; Finally, here is our stobj definition.  First we present a compact version;
; then we present a more verbose definition.

(DEFABSSTOBJ ST
  :EXPORTS ((LOOKUP :EXEC MEM$CI)
            (UPDATE :EXEC UPDATE-MEM$CI)
            MISC UPDATE-MISC))

; Here is a more verbose version of the form above.  The parts retained from
; the short form above are in CAPS.  We change the names because redundancy
; would require the two defabsstobj events to be syntactically identical, which
; they are not.

(DEFABSSTOBJ ST2
  :foundation st$c ; the foundational (corresponding concrete) stobj
  :recognizer (st2p :logic st$ap :exec st$cp)
  :creator (create-st2 :logic create-st$a :EXEC create-st$c
                       :correspondence create-st{correspondence}
                       :preserved create-st{preserved})
  :corr-fn st$corr ; a correspondence function (st$corr st$c st)
  :EXPORTS (

; The following entry defines lookup2 to be lookup$a in the logic (with the
; same guard as lookup$a), and defines lookup2 to be mem$ci in the
; implementation (actually, using a macro definition).  Moroever, lookup2 will
; be given a signature "matching" that of the :EXEC, mem$ci, where "matching"
; means that st$c is replaced by st.  (Note that we are not restricted to
; matching up with a stobj accessor such as mem$ci; any defined function with
; suitable signature could be specified.)  Note that the body of lookup2 will
; never be executed on a live stobj, just as the logical definition of a
; concrete stobj accessor is never executed on a live stobj; rather, lookup2 is
; defined in raw Lisp to be mem$ci.

            (LOOKUP2 :logic lookup$a
                     :EXEC MEM$CI
                     :correspondence lookup{correspondence}
                     :guard-thm lookup{guard-thm})
            (UPDATE2 :logic update$a
                     :EXEC UPDATE-MEM$CI
                     :correspondence update{correspondence}

; For functions that return a stobj, like update (and update-mem$ci), we have
; not only a :correspondence theorem but also a :preserved theorem.  It can be
; omitted with explicit :preserved nil.

                     :preserved update{preserved}
                     :guard-thm update{guard-thm})

; Note that renaming is not handled as with defstobj.  So for example, if the
; :exec ("concrete") updater for the misc$c field is !misc$c, then we need to
; use a long form such as the one below.

            (MISC2 :logic misc$a
                   :exec misc$c
                   :correspondence misc{correspondence})
            (UPDATE-MISC2 :logic update-misc$a
                          :exec update-misc$c
                          :correspondence update-misc{correspondence}
                          :preserved update-misc{preserved})))

; Finally, we show that the use of a logical stobj can result in improvements
; to rewrite rules by way of eliminating hypotheses.

; First, for the original stobj we have the following lemma.  Without the type
; hypotheses on both i and j, it fails -- see mem$ci-update-mem$ci-failure.

(defthm mem$ci-update-mem$ci
  (implies (and (st$cp+ st$c)
                (natp i)
                (natp j))
           (equal (mem$ci i (update-mem$ci j v st$c))
                  (if (equal i j)
                      v
                    (mem$ci i st$c)))))

; Here is evidence of the failure promised above.  The theorem above can be
; salvaged without the natp hypotheses by replacing (equal i j) with (equal
; (nfix i) (nfix j)), but that would introduce a case split, which might be
; undesirable.

(defthm mem$ci-update-mem$ci-failure
  (let* ((st$c (create-st$c))
         (i 0)
         (j 'a))
    (not (implies (and (st$cp+ st$c)
                       (natp i)
                       ;; (natp j)
                       )
                  (equal (mem$ci i (update-mem$ci j 1 st$c))
                         (if (equal i j)
                             v
                           (mem$ci i st$c))))))
  :rule-classes nil)

; But for our abstract stobj, both natp hypotheses can be eliminated.

(defthm lookup-update
  (equal (lookup i (update j v st))
         (if (equal i j)
             v
           (lookup i st))))

; We conclude with some examples of congruent abstract stobjs.  The first two
; below, st3 and st4, are designated as congruent to st; the fifth one is
; designated as congruent to st3.  Thus all four of those should be usable
; interchangeably; we test that below.

(defabsstobj st3
  :foundation st$c
  :recognizer (st3p :logic st$ap :exec st$cp)
  :creator (create-st3 :logic create-st$a :exec create-st$c
                       :correspondence create-st{correspondence}
                       :preserved create-st{preserved})
  :corr-fn st$corr
  :exports ((lookup3 :logic lookup$a
                     :exec mem$ci)
            (update3 :logic update$a
                     :exec update-mem$ci)
            (misc3 :logic misc$a
                   :exec misc$c)
            (update-misc3 :logic update-misc$a
                          :exec update-misc$c))
  :congruent-to st)

(defabsstobj st4
  :foundation st$c
  :recognizer (st4p :logic st$ap :exec st$cp)
  :creator (create-st4 :logic create-st$a :exec create-st$c
                       :correspondence create-st{correspondence}
                       :preserved create-st{preserved})
  :corr-fn st$corr
  :exports ((lookup4 :logic lookup$a
                     :exec mem$ci)
            (update4 :logic update$a
                     :exec update-mem$ci)
            (misc4 :logic misc$a
                   :exec misc$c)
            (update-misc4 :logic update-misc$a
                          :exec update-misc$c))
  :congruent-to st)

(defabsstobj st5
  :foundation st$c
  :recognizer (st5p :logic st$ap :exec st$cp)
  :creator (create-st5 :logic create-st$a :exec create-st$c
                       :correspondence create-st{correspondence}
                       :preserved create-st{preserved})
  :corr-fn st$corr
  :exports ((lookup5 :logic lookup$a
                     :exec mem$ci)
            (update5 :logic update$a
                     :exec update-mem$ci)
            (misc5 :logic misc$a
                   :exec misc$c)
            (update-misc5 :logic update-misc$a
                          :exec update-misc$c))
  :congruent-to st3)

; Now let's see if they really are interchangable.

(defun foo (st st3 st4 st5)
  (declare (xargs :stobjs (st st3 st4 st5)))
  (list (lookup 7 st)
        (lookup 7 st3)
        (lookup 7 st4)
        (lookup 7 st5)
        (lookup3 7 st)
        (lookup3 7 st3)
        (lookup3 7 st4)
        (lookup3 7 st5)
        (lookup4 7 st)
        (lookup4 7 st3)
        (lookup4 7 st4)
        (lookup4 7 st5)
        (lookup5 7 st)
        (lookup5 7 st3)
        (lookup5 7 st4)
        (lookup5 7 st5)))

(local (make-event
        (let* ((st (update 7 10 st))
               (st3 (update 7 30 st3))
               (st4 (update 7 40 st4))
               (st5 (update 7 50 st5)))
          (mv nil '(value-triple nil) state st st3 st4 st5))))

(local
 (assert-event
  (equal (foo st st3 st4 st5)
         '(10 30 40 50 10 30 40 50
              10 30 40 50 10 30 40 50))))

(local
 (assert-event
  (equal (foo st5 st4 st3 st)
         '(50 40 30 10 50 40 30 10 50 40 30 10 50 40 30 10))))
