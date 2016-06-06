; Copyright (C) 2015, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Example of Well-Formedness Guarantee for a Metafunction
; Matt Kaufmann and J Strother Moore
; June, 2015

; To Recertify:
; (certify-book "meta-wf-guarantee-example" ? nil)

; SBCL does not have the capacity to handle this book as of June 2015:
; cert_param: (non-sbcl)

; About this Book

; We define a metafunction, prove its guards, prove a well-formedness guarantee
; for it, and prove it correct.  But in proving it correct we store it two
; different ways, once without the well-formedness guarantee and once with the
; guarantee.  We give these two metatheorems different names and disable them
; both, so that by enabling exactly one we can run the metafunction with or
; without the guarantee.

; Then we export three macros for testing the options so that you can see the
; metafunctions in action.

; One macro attempts to prove a certain test theorem without the metafunctions
; at all.  That will fail, thereby demonstrating that we do not have rewrite
; rules around sufficient to solve the problem.  Indeed, no finite set of
; rewrite rules -- or at least no such set we know! -- will do what our
; metafunction does.  Another purpose of this macro is to show you what the
; test theorem looks like.  You probably won't have the patience to watch
; the checkpoint print in full.  It contains about a million (boringly
; repetitious) function calls.

; The second macro proves the test theorem using the metafunction without
; guarantees.  The last macro proves it with the guarantee.  Both of the
; successful proofs print profiling information about the proofs.

; At the end of this book we define a clause-processor, prove a well-formedness
; guarantee for it, and prove it correct.

; How to Use This Book

; The best way to use it is first to read it and understand the metafunction we
; define, see how the well-formedness guarantee is proved, and how we can store
; the metafunction with or without a guarantee.  But then to test the
; metafunction you should do this:

; (include-book "meta-wf-guarantee-example" :load-compiled-file nil)
; (test-without-meta)   ; <--- WARNING: This fails and prints a huge checkpoint
; (test-without-guarantee)
; (test-with-guarantee)

; In each of the last two, search backwards for
; Summary
; Form:  ( THM ...)
; to find the Time taken for each proof.

; Summary of The Successful Macros

; We summarize below what we saw when running the two successful tests on a
; MacBook Pro laptop with a 2.8 GHz Intel Core i7 processor and 16 GB of 1600
; MHZ DDR3 memory, running Clozure Common Lisp.

; Proof without the Well-Formedness Guarantee
; Time:  1.64 seconds (prove: 1.64, print: 0.00, other: 0.00)
; (TERMP
;  Calls                                                                  4.96E+6
;  Time of all outermost calls                                               0.43
;  Time per call                                                          8.60E-8
;  From other functions                        4.96E+6 calls took 4.26E-1; 100.0%)
; (META-WR
;  Calls                                                                        7
;  Time of all outermost calls                                            8.93E-5
;  Time per call                                                         1.276E-5
;  Heap bytes allocated                                           1.06E+3; 100.0%
;  Heap bytes allocated per call                                           150.86
;  From other functions                            7.00E+0 calls took 8.93E-5; ?%)

; Proof with the Well-Formedness Guarantee
; Time:  1.20 seconds (prove: 1.20, print: 0.00, other: 0.00)
; (META-WR
;  Calls                                                                        7
;  Time of all outermost calls                                            8.59E-5
;  Time per call                                                         1.227E-5
;  Heap bytes allocated                                           1.06E+3; 100.0%
;  Heap bytes allocated per call                                           150.86
;  From other functions                            7.00E+0 calls took 8.59E-5; ?%)
; (TERMP
;  Calls                                                                        1
;  Time of all outermost calls                                            1.00E-6
;  Time per call                                                          2.54E-7
;  From other functions                            1.00E+0 calls took 2.54E-7; ?%)

; What we see from the above is that when run without guarantee, TERMP is
; called about 5 million times.  When run with the guarantee, TERMP is called 1
; time.  Every event causes at least 1 call of TERMP because of the way events
; macroexpand.

; We also see that the metafunction, which is named META-WR, is called 7 times
; in each proof.

; Furthermore, we see that in both proofs the 7 calls of META-WR took trivial
; time, when compared to the time of 0.43 seconds spent in TERMP in the proof
; without the well-formedness test: over four thousand times longer in TERMP
; than in the metafunction.

; The difference in the total proof times is not so dramatic, just 1.64 seconds
; versus 1.20 seconds.  That difference is almost entirely explained by the
; 0.43 seconds in TERMP.  Most of the proof time is spent in the rewriter,
; expanding the definitions that make the test theorem large.

; About the Metafunction Defined Here

; We first define a ``memory write'' function, (wr addr val mem) that
; deposits val at location addr in the linear list mem.

; (wr 5 'five '(0 I II III IV V VI VII VIII IX))
; = '(0 I II III IV FIVE VI VII VIII IX)

; An interesting property of this function is that if a new write shadows an
; old write to the same location, the old write can be eliminated, no matter
; what addresses might also have been written -- even if some of those other
; writes were to the same address.

; For example, suppose you have an ``old memory'' and you build a ``new memory''
; by doing a write that shadows one of the old ones:

; old mem:  (wr a2 v2 (wr a3 v3 (wr a1 v1 mem)))
; new mem:  (wr a1 new-v1 old-mem)

; Note that the write to a1 shadows the deepest write in the old memory.
; But we don't know whether the writes to a2 or a3 are shadowed or not.

; Logically the new memory is

; (wr a1 new-v1 (wr a2 v2 (wr a3 v3 (wr a1 v1 mem))))
;                                   ^^^^^^^^^
;                                   this write is
;                                   shadowed out by
;                                   the new wr

; and the challenge is to write a metafunction that reduces this to
; the simpler expression:

; (wr a1 new-v1 (wr a2 v2 (wr a3 v3 mem)))

; in which the shadowed write is eliminated.

; In our metafunction, which is called META-WR, we use a trick exploited in the
; Stateman book, to HIDE every write already processed so we don't resimplify
; an already processed memory expression.  Thus, a more accurate portrayal of
; what we'll see is:

; old mem:  (HIDE (wr a2 v2 (wr a3 v3 (wr a1 v1 mem))))
; new mem:  (wr a1 new-v1 old-mem)

; Logically this turns into

; (wr a1 new-v1 (HIDE (wr a2 v2 (wr a3 v3 (wr a1 v1 mem)))))
; =
; (HIDE (wr a1 new-v1 (wr a2 v2 (wr a3 v3 mem)))

; [Note: The use of this HIDE trick here is sloppily implemented in this
; example.  One should not put a HIDE on the answer term until there's reason
; to believe that the address expressions thus hidden will not change under
; further rewriting, but we don't worry about that here.]

(in-package "ACL2")

(defun wr (addr val mem)
  (let ((addr (nfix addr)))
    (cond
     ((equal addr 0) (cons val (cdr mem)))
     (t (cons (car mem) (wr (- addr 1) val (cdr mem)))))))

; (wr 5 'five '(0 I II III IV V VI VII VIII IX))
; = '(0 I II III IV FIVE VI VII VIII IX)

; Now we define our metafunction, meta-wr, which relies on this recursive
; function which eliminates the first write to address expression a found in
; the WR-term term.

(defun rem-shadowed (a term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (eq (car term) 'WR))
    (cond ((equal a (cadr term))
           (cadddr term))
          (t (list 'WR
                   (cadr term)
                   (caddr term)
                   (rem-shadowed a (cadddr term))))))
   (t term)))

; So here's our metafunction, which uses case-match to look for its main
; trigger, an input term of the form (WR a v (HIDE mem)) and transforms it to
; (HIDE (WR a v mem')) where mem' has (possibly) had a shadowed write removed.
; If there is no HIDE on the mem, meta-wr puts a HIDE around the input term to
; get the process started.  On an inside-out pass through a nest of n WR calls,
; meta-wr is fired n times and propagates a HIDE to the top.

(defun meta-wr (term)
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
    (('WR a v ('HIDE mem))
     (list 'HIDE (list 'WR a v (rem-shadowed a mem))))
    (('WR & & &)
     (list 'HIDE term))
    (& term)))

;(meta-wr '(WR A1 NEW-V1 (HIDE (WR A2 V2 (WR A3 V3 (WR A1 V1 MEM))))))
; = (HIDE (WR A1 NEW-V1 (WR A2 V2 (WR A3 V3 MEM))))

; Here is the evaluator and arity-alist we will need:

(defevaluator evl evl-lst ((hide x) (wr a v mem)))
(defconst *arity-alist* '((HIDE . 1) (WR . 3)))

; Next we prove the well-formedness guarantee.  We must first prove that the
; recursive rem-shadowed preserves termp and then we can prove that meta-wr
; does too:

(defthm termp-rem-shadowed
  (implies (and ; (termp a w)  ; See Note below
                (termp mem w)
                (arities-okp *arity-alist* w))
           (termp (rem-shadowed a mem) w)))

; Note: In general a well-formedness lemma or theorem about a function requires
; well-formedness hypotheses about each argument.  But in the case of
; rem-shadowed, the argument a does not appear in the answer and so it doesn't
; really matter if it is well-formed or not!

(defthm logic-fnsp-rem-shadowed
  (implies (and ; (termp mem w)
                (logic-fnsp mem w)
                ; (arities-okp *arity-alist* w)
                )
           (logic-fnsp (rem-shadowed a mem) w)))

; The following lemma isn't needed (because the two above are sufficient), but
; it's still nice to prove.

(defthm logic-termp-rem-shadowed
  (implies (and (termp mem w)
                (logic-termp mem w)
                (arities-okp *arity-alist* w))
           (logic-termp (rem-shadowed a mem) w)))

(defthm termp-meta-wr
  (implies (and (termp x w)
                (arities-okp *arity-alist* w))
           (termp (meta-wr x) w)))

(defthm logic-fnsp-meta-wr
  (implies (and ;(termp x w)
                (logic-fnsp x w)
                (arities-okp *arity-alist* w))
           (logic-fnsp (meta-wr x) w)))

(defthm logic-termp-meta-wr
  (implies (and (logic-termp x w)
                (arities-okp *arity-alist* w))
           (logic-termp (meta-wr x) w)))

; This next event is entirely irrelevant to the point of this book but is
; probably the most interesting mathematical step!  We need to prove that it is
; sound to remove a shadowed write without knowing anything about the values of
; the intervening writes.  This is the inductively proved lemma named
; shadowing-justifies-rem-shadowed below.  But to prove that lemma we need another
; inductively proved lemma stating that if two memories are equal after writing
; to a1 they're equal if first you write to a2.

(encapsulate
 nil
 (local
  (defthm lemma
    (implies (equal (wr a1 v1 mem1)
                    (wr a1 v1 mem2))
             (equal (equal (wr a1 v1
                               (wr a2 v2 mem1))
                           (wr a1 v1
                               (wr a2 v2 mem2)))
                    t))))

 (defthm shadowing-justifies-rem-shadowed
    (equal (wr (evl addr a)
               val
               (evl (rem-shadowed addr mem)
                    a))
           (wr (evl addr a)
               val
               (evl mem a)))))

; The next two events are the two metatheorems, one without a guarantee and one
; with a guarantee.  The two metatheorems are identical and we must provide a
; hint to each proof to expand the HIDEs.  The only difference between these
; two events is that the first does not provide a well-formedness guarantee and
; the second one does.

(defthmd meta-wr-correct-without-guarantee
  (implies (pseudo-termp x)
           (equal (evl x a)
                  (evl (meta-wr x) a)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (wr))))

(defthmd meta-wr-correct-with-guarantee
  (implies (pseudo-termp x)
           (equal (evl x a)
                  (evl (meta-wr x) a)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (wr)
                        :well-formedness-guarantee logic-termp-meta-wr)))

; Now we disable shadowing-justifies-rem-shadowed just so there is no
; rewrite rule that hits WR expressions (although this rule will never
; fire anyway because we'll never see rem-shadowed in a goal again!).

(in-theory (disable shadowing-justifies-rem-shadowed))

; The progn below provides the mechanism for constructing exponentially
; large terms and burying them inside the functions addr1, addr2, ...
; The idea is that we want our test theorem to be small looking so we
; can read it but to expand to a big formula.

(progn
 (defstub G (x y) t)

 (defun big-fn (n)
   (if (zp n)
       'x
       (list 'G
             (big-fn (- n 1))
             (big-fn (- n 1)))))

 (comp 'big-fn) ; speeds things up somewhat

 (defmacro big (n) (time$ (big-fn n)))
                               ; fn calls
 (defun addr1 (x)    (big 12)) ;   4095
 (defun addr2 (x)    (big 13)) ;   8191
 (defun addr3 (x)    (big 14)) ;  16383
 (defun val1  (x)    (big 15)) ;  32767
 (defun new-val1 (x) (big 16)) ;  65535
 (defun val2 (x)     (big 17)) ; 131071
 (defun val3 (x)     (big 18)) ; 262143
 )

; Our test theorem will be (equal lhs rhs), where lhs and rhs are
; as shown below.  FYI, they have the indicated number of function
; calls in them, so their equality has about 1 million calls.

; lhs:                                          fn calls
; (wr (addr1 x) (new-val1 x)                    (+ 1 4095 65535
;     (wr (addr2 x) (val2 x)                       (+ 1 8181 131071
;         (wr (addr3 x) (val3 x)                      (+ 1 16383 262143
;             (wr (addr1 x) (val1 x)                     (+ 1 4095 32767
;                 mem))))                                   0))))
;                                               = 524274
; rhs
; (wr (addr1 x) (new-val1 x)                    (+ 1 4095 65535
;     (wr (addr2 x) (val2 x)                       (+ 1 8181 131071
;         (wr (addr3 x) (val3 x)                      (+ 1 16383 262143
;             mem))))                                    0)))
;                                               = 487411

; And here are our three macros allowing the user of this book to test
; these metafunctions.

(defmacro test-without-meta nil
  '(thm
    (equal (wr (addr1 x) (new-val1 x)
               (wr (addr2 x) (val2 x)
                   (wr (addr3 x) (val3 x)
                       (wr (addr1 x) (val1 x) mem))))
           (wr (addr1 x) (new-val1 x)
               (wr (addr2 x) (val2 x)
                   (wr (addr3 x) (val3 x)
                       mem))))))

(defmacro test-without-guarantee nil
  '(er-progn
    (profile 'meta-wr)
    (profile 'termp)
    (profile 'logic-fnsp)
    (profile 'logic-termp)
    (value (clear-memoize-statistics))
    (thm
     (equal (wr (addr1 x) (new-val1 x)
                (wr (addr2 x) (val2 x)
                    (wr (addr3 x) (val3 x)
                        (wr (addr1 x) (val1 x) mem))))
            (wr (addr1 x) (new-val1 x)
                (wr (addr2 x) (val2 x)
                    (wr (addr3 x) (val3 x)
                        mem))))
     :hints (("Goal" :in-theory (enable meta-wr-correct-without-guarantee)))
     )
    (value (memsum))
    (value (clear-memoize-statistics))))

(defmacro test-with-guarantee nil
  '(er-progn
    (profile 'meta-wr)
    (profile 'termp)
    (profile 'logic-fnsp)
    (profile 'logic-termp) ; still expect some from translate-cmp
    (value (clear-memoize-statistics))
    (thm
     (equal (wr (addr1 x) (new-val1 x)
                (wr (addr2 x) (val2 x)
                    (wr (addr3 x) (val3 x)
                        (wr (addr1 x) (val1 x) mem))))
            (wr (addr1 x) (new-val1 x)
                (wr (addr2 x) (val2 x)
                    (wr (addr3 x) (val3 x)
                        mem))))
     :hints (("Goal" :in-theory (enable meta-wr-correct-with-guarantee)))
     )
    (value (memsum))
    (value (clear-memoize-statistics))))

; We conclude with a small example that illustrates well-formedness-guarantees
; for clause-processors.  It is based on the example for function strengthen-cl
; in community book books/clause-processors/basic-examples.lisp.

(defevaluator evl2 evl2-list
  ((if x y z) (length x) (member-equal x y) (equal x y) (not x)))

(defconst *arity-alist2* '((if . 3) (length . 1) (member-equal . 2)
                           (equal . 2) (not . 1)))

; Next we introduce an alternative to termp, termp*, that takes an arity-alist
; rather than a world.  There are quite a few events here, culminating in key
; lemmas termp*-implies-termp and termp*-implies-logic-fnsp.

(verify-termination arity-alistp)

(defthm arity-alistp-implies-symbol-alistp
  (implies (arity-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

(verify-guards arity-alistp)

(defun termp* (flg x aa)
  (declare (xargs :guard (arity-alistp aa)
                  :verify-guards nil))
  (cond (flg ; x is a list of terms
         (cond ((atom x) (null x))
               (t (and (termp* nil (car x) aa)
                       (termp* t (cdr x) aa)))))
        ((atom x) (legal-variablep x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((arity (cdr (assoc-eq (car x) aa))))
           (and arity
                (true-listp (cdr x))
                (eql (length (cdr x)) arity)
                (termp* t (cdr x) aa))))
        ((and (consp (car x))
              (true-listp (car x))
              (eq (car (car x)) 'lambda)
              (equal 3 (length (car x)))
              (arglistp (cadr (car x)))
              (termp* nil (caddr (car x)) aa)
              (null (set-difference-eq
                     (all-vars (caddr (car x)))
                     (cadr (car x))))
              (termp* t (cdr x) aa)
              (equal (length (cadr (car x)))
                     (length (cdr x))))
         t)
        (t nil)))

(defthm arglistp1-implies-symbol-listp
  (implies (arglistp1 x)
           (symbol-listp x)))

(defthm termp*-implies-pseudo-termp
  (implies (termp* flg x aa)
           (if flg
               (pseudo-term-listp x)
             (pseudo-termp x)))
  :rule-classes :forward-chaining)

(defun true-listp-all-vars1-induction (flg x ans)
  (cond
   (flg
    (cond
     ((endp x) ans)
     (t (list
         (true-listp-all-vars1-induction nil (car x) ans)
         (true-listp-all-vars1-induction t
                                         (cdr x)
                                         (all-vars1 (car x) ans))))))
   ((variablep x)
    (add-to-set-eq x ans))
   ((fquotep x) ans)
   (t (true-listp-all-vars1-induction t (fargs x) ans))))

(defthm true-listp-all-vars1-lemma
  (implies (true-listp ans)
           (true-listp (if flg
                           (all-vars1-lst x ans)
                         (all-vars1 x ans))))
  :hints (("Goal"
           :induct (true-listp-all-vars1-induction flg x ans)))
  :rule-classes nil)

(defthm true-listp-all-vars1
  (true-listp (all-vars1 x nil))
  :hints (("Goal" :use ((:instance true-listp-all-vars1-lemma
                                   (flg nil)
                                   (ans nil))))))

(verify-guards termp*)

(defthm termp*-implies-termp-lemma
  (implies (and (termp* flg x arity-alist)
                (arities-okp arity-alist w))
           (if flg
               (term-listp x w)
             (termp x w)))
  :rule-classes nil)

(defthm termp*-implies-termp
  (implies (and (termp* nil x arity-alist)
                (arities-okp arity-alist w))
           (termp x w))
  :hints (("Goal" :use ((:instance termp*-implies-termp-lemma
                                   (flg nil))))))

(defthm termp*-implies-logic-fnsp-lemma
  (implies (and (termp* flg x arity-alist)
                (arities-okp arity-alist w))
           (if flg
               (logic-fns-listp x w)
             (logic-fnsp x w)))
  :rule-classes nil)

(defthm termp*-implies-logic-fnsp
  (implies (and (termp* nil x arity-alist)
                (arities-okp arity-alist w))
           (logic-fnsp x w))
  :hints (("Goal" :use ((:instance termp*-implies-logic-fnsp-lemma
                                   (flg nil))))))

; Finally we define our clause-processor.

(defun split-cl (cl term)
  (declare (xargs :guard t))
  (cond ((termp* nil term *arity-alist2*)
         (list (cons (list 'not term)
                     cl)
               (list term)))
        (t (prog2$ (er hard? 'split-cl
                       "Not a logic-termp:~|~x0"
                       term)
                   (list cl)))))

(defthmd logic-term-list-listp-split-cl
  (implies (and (logic-term-listp cl w)
                (arities-okp *arity-alist2* w))
           (logic-term-list-listp (split-cl cl term) w))
  :hints (("Goal" :in-theory (disable logic-termp))))

(defthm correctness-of-split-cl
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl2 (conjoin-clauses (split-cl cl term))
                      a))
           (evl2 (disjoin cl) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-split-cl)))
