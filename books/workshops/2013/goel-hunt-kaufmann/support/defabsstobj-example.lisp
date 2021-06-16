; Defabsstobj Example
; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; Based on misc/defabsstobj-example-1.lisp (but the present example is simpler)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note: In June 2021 the notion of "corresponding concrete stobj" for an
; abstract stobjs, represented by keyword :concrete of defabsstobj, was
; replaced by the notion of "foundational stobj" (or "foundation"), now
; represented by keyword :foundation.  Since this book was provided as
; supporting materials for a workshop paper, we have left everything below
; unchanged except for the line where :concrete was replaced by :foundation.

(in-package "ACL2")

; A nice convention, observed below, is to use the suffixes "$c" and "$a" to
; suggest "concrete" and "abstract" for the concrete and abstract stobjs,
; respectively, that will be used in our defabsstobj event.

; We begin by defining a concrete stobj, with two fields: a memory of 100
; natural number values (initially 100 zeroes), and a ``miscellaneous'' field
; initialized to 0.

(defstobj st$c
  (mem$c :type (array t (100))
         :initially 0)
  misc$c)

; We next introduce the logical recognizer for the MEM-MAP component of the
; abstract stobj, to serve as an alternate implementation of memory based on an
; association list.  Just for fun, we add an invariant beyond what is required
; of the concrete stobj: all memory values are even natural numbers.

(defun mem-map$ap (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((atom (car x)) nil)
        (t (and (natp (caar x)) (< (caar x) 100) ; index is in range
                (natp (cdar x)) (evenp (cdar x))
                (mem-map$ap (cdr x))))))

; Now we define a recognizer for the abstract stobj.  Note that in general, an
; abstract stobj needn't have ``fields'' in the sense that a concrete stobj has
; fields.  Instead, there is a recognizer for the abstract stobj, a creator for
; making an initial object, and exported functions for reading and writing the
; object.  We begin by defining the recognizer.  In our simple example, it is
; convenient to think of two ``fields'' but, just to add a bit of interest, in
; the opposite order from their order in the concrete stobj.

; To make things interesting, we use an entirely different shape for our
; abstract stobj than for our concrete stobj.  Here we use a cons whose cdr is
; the memory.

(defun st$ap (x)
  (declare (xargs :guard t))
  (and (consp x)
       (mem-map$ap (cdr x))))

; We next define read and write functions for our abstract stobj, first for the
; MISC component and then for the memory.

(defun misc$a (st$a)
  (declare (xargs :guard (st$ap st$a)))
  (car st$a))

(defun update-misc$a (v st$a)
  (declare (xargs :guard (st$ap st$a)))
  (cons v (cdr st$a)))

(defun lookup$a (k st$a)
  (declare (xargs :guard (and (natp k)
                              (< k 100)
                              (st$ap st$a))))
  (let* ((mem-map (cdr st$a))
         (pair (assoc k mem-map)))
    (if pair (cdr pair) 0)))

(defun update$a (k val st$a)
  (declare (xargs :guard (and (st$ap st$a)
                              (natp k) (< k 100)
                              (natp val) (evenp val))))
  (cons (car st$a)
        (put-assoc k val (cdr st$a))))

; Our next task is to define a required function, which we call st$corr, that
; defines a correspondence relation between our concrete and abstract stobjs.
; This relation is used in the proof obligations that follow.  Since this
; relation is of logical interest only, we avoid guards and guard verification.

(defun corr-mem (n st$c st$a) ; auxiliary to st$corr, defined below
  (declare (xargs :stobjs st$c :verify-guards nil))
  (cond ((zp n) t)
        (t (let ((i (1- n)))
             (and (equal (mem$ci i st$c) (lookup$a i st$a))
                  (corr-mem i st$c st$a))))))

(defun st$corr (st$c st$a)
  (declare (xargs :stobjs st$c :verify-guards nil))
  (and (st$cp st$c)
       (st$ap st$a)
       (equal (misc$c st$c) (misc$a st$a))
       (corr-mem 100 st$c st$a)))

; Next we define the function that creates our abstract stobj.

(defun create-st$a ()
  (declare (xargs :guard t))
  (cons nil nil)) ; (cons misc mem)

; At this point we execute our defabsstobj event in order to get proof
; obligations, pasted into the file below as shown in CAPITAL LETTERS.
; If you think about the expected proof obligations, you might be surprised to
; find that MISC{GUARD-THM} and UPDATE-MISC{GUARD-THM} are missing (analogous
; to other {GUARD-THM} lemmas).  ACL2 notices that these missing ones hold
; trivially, and spares us the trouble of considering them.

#||
(DEFABSSTOBJ ST
  :EXPORTS ((LOOKUP :EXEC MEM$CI)
            (UPDATE :EXEC UPDATE-MEM$CI)
            MISC UPDATE-MISC))
||#

(DEFTHM CREATE-ST{CORRESPONDENCE}
        (ST$CORR (CREATE-ST$C) (CREATE-ST$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST{PRESERVED}
        (ST$AP (CREATE-ST$A))
        :RULE-CLASSES NIL)

; Lemmas for lookup and update are printed next, but it takes a bit more effort
; than some others so we defer them.

; The hypothesis (st$ap st) below is not needed for the following formula to be
; a theorem; similarly for update-misc{correspondence} as well.  However, this
; hypothesis is expected by defabsstobj.

(DEFTHM MISC{CORRESPONDENCE}
        (IMPLIES (AND (ST$CORR ST$C ST) (ST$AP ST))
                 (EQUAL (MISC$C ST$C) (MISC$A ST)))
        :RULE-CLASSES NIL)

(defthm update-misc{correspondence}-lemma
  (implies (corr-mem k st$c st)
           (corr-mem k
                     (update-misc$c v st$c)
                     (update-misc$a v st)))
  :rule-classes nil)

(DEFTHM UPDATE-MISC{CORRESPONDENCE}
        (IMPLIES (AND (ST$CORR ST$C ST) (ST$AP ST))
                 (ST$CORR (UPDATE-MISC$C V ST$C)
                          (UPDATE-MISC$A V ST)))
        :hints (("Goal" :use ((:instance update-misc{correspondence}-lemma
                                         (k 100)))))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-MISC{PRESERVED}
        (IMPLIES (ST$AP ST)
                 (ST$AP (UPDATE-MISC$A V ST)))
        :RULE-CLASSES NIL)

; The proof of lookup{correspondence} requires an inductive lemma.

(encapsulate
 ()

 (local (defthm corr-mem-memi
          (implies (and (corr-mem bound st$c st)
                        (natp bound)
                        (natp i) (< i bound))
                   (equal (mem$ci i st$c)
                          (lookup$a i st)))
          :rule-classes nil))

 (DEFTHM LOOKUP{CORRESPONDENCE}
         (IMPLIES (AND (ST$CORR ST$C ST)
                       (NATP I)
                       (< I 100)
                       (ST$AP ST))
                  (EQUAL (MEM$CI I ST$C)
                         (LOOKUP$A I ST)))
         :hints (("Goal" :use ((:instance corr-mem-memi
                                          (bound 100)))))
         :RULE-CLASSES NIL))

(DEFTHM LOOKUP{GUARD-THM}
        (IMPLIES (AND (ST$CORR ST$C ST)
                      (NATP I)
                      (< I 100)
                      (ST$AP ST))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (MEM$C-LENGTH ST$C))))
        :RULE-CLASSES NIL)

; Several lemmas contribute to the proof of our next required theorem,
; update{correspondence}.

(local (defthm assoc-equal-put-assoc-equal
         (equal (assoc-equal k1 (put-assoc-equal k2 v a))
                (if (equal k1 k2) (cons k1 v) (assoc-equal k1 a)))))

(local (defthm mem$cp-update-nth
         (implies (and (natp i) (< i (len mem))
                       (natp v)
                       (mem$cp mem))
                  (mem$cp (update-nth i v mem)))))

(local (defthm mem-map$ap-put-assoc-equal
         (implies (and (natp i) (< i 100)
                       (natp v) (evenp v)
                       (mem-map$ap mem))
                  (mem-map$ap (put-assoc-equal i v mem)))))

(local (defthm corr-mem-update-memi
         (implies (and (natp bound) (<= bound 100)
                       (corr-mem bound st$c st)
                       (natp i))
                  (corr-mem bound
                            (cons (update-nth i v (car st$c))
                                  (cdr st$c))
                            (cons (car st)
                                  (put-assoc-equal i v (cdr st)))))))

(DEFTHM UPDATE{CORRESPONDENCE}
        (IMPLIES (AND (ST$CORR ST$C ST)
                      (ST$AP ST)
                      (NATP I)
                      (< I 100)
                      (NATP V)
                      (EVENP V))
                 (ST$CORR (UPDATE-MEM$CI I V ST$C)
                          (UPDATE$A I V ST)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE{GUARD-THM}
        (IMPLIES (AND (ST$CORR ST$C ST)
                      (ST$AP ST)
                      (NATP I)
                      (< I 100)
                      (NATP V)
                      (EVENP V))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (MEM$C-LENGTH ST$C))))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE{PRESERVED}
        (IMPLIES (AND (ST$AP ST)
                      (NATP I)
                      (< I 100)
                      (NATP V)
                      (EVENP V))
                 (ST$AP (UPDATE$A I V ST)))
        :RULE-CLASSES NIL)

; Now we are ready to submit our defabsstobj event.  We present it in a more
; verbose form this time.  The few parts retained from the short form above are
; in CAPITAL LETTERS.

(DEFABSSTOBJ ST
  :foundation st$c ; the corresponding foundational ("concrete") stobj
  :recognizer (stp :logic st$ap :exec st$cp)
  :creator (create-st :logic create-st$a :exec create-st$c
                      :correspondence create-st{correspondence}
                      :preserved create-st{preserved})
  :corr-fn st$corr ; a correspondence function (st$corr st$c st)
  :EXPORTS (

; The following entry defines lookup to be lookup$a in the logic (with the
; same guard as lookup$a), and defines lookup to be mem$ci in the
; implementation (actually, using a macro definition).  Moroever, lookup will
; be given a signature "matching" that of the :EXEC, mem$ci, where "matching"
; means that st$c is replaced by st.  (Note that we are not restricted to
; matching up with a stobj accessor such as mem$ci; any defined function with
; suitable signature could be specified.)  Note that the body of lookup will
; never be executed on a live stobj, just as the logical definition of a
; concrete stobj accessor is never executed on a live stobj; rather, lookup is
; defined in raw Lisp to be mem$ci.

            (LOOKUP :logic lookup$a
                    :EXEC MEM$CI
                    :correspondence lookup{correspondence}
                    :guard-thm lookup{guard-thm})
            (UPDATE :logic update$a
                    :EXEC UPDATE-MEM$CI
                    :correspondence update{correspondence}

; For functions that return a stobj, like update (and update-mem$ci), we have
; not only a :correspondence theorem but also a :preserved theorem.  It can be
; omitted with explicit :preserved nil.

                    :preserved update{preserved}
                    :guard-thm update{guard-thm})

; Note that renaming is not handled as with defstobj.  So for example, if the
; concrete updater for the misc$c field is !misc$c, then we need to use a long
; form such as the one below.

            (MISC :logic misc$a
                  :exec misc$c
                  :correspondence misc{correspondence})
            (UPDATE-MISC :logic update-misc$a
                         :exec update-misc$c
                         :correspondence update-misc{correspondence}
                         :preserved update-misc{preserved}))

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form below.
; :doc ; nil is OK, but we test the use of an actual :doc string
; ":Doc-Section defabsstobj
;
; a defabsstobj example~/
;
; This :DOC string is just a stub.  ~l[defabsstobj].~/~/"
  )

(include-book "xdoc/top" :dir :system)

(defxdoc st
  :parents (defabsstobj)
  :short "A defabsstobj example"
  :long "<p>This :DOC string is just a stub.  See @(see defabsstobj).</p>

 ")

; Finally, we show that the use of a logical stobj can result in improvements
; to rewrite rules by way of eliminating hypotheses.

; First, for the original stobj we have the following lemma.  Without the type
; hypotheses on both i and j, it fails -- see mem$ci-update-mem$ci-failure.

(defthm mem$ci-update-mem$ci
  (implies (and (st$cp st$c)
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
    (not (implies (and (st$cp st$c)
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
