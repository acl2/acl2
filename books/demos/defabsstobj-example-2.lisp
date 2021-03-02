; Defabsstobj Example 2
; Copyright (C) 2012, Regents of the University of Texas
; Written by Matt Kaufmann, July, 2012 (updated Dec., 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This example uses abstract stobjs to save values in a memo table.  It
; illustrates how to avoid guard checks using abstract stobjs.  It also
; illustrates the use of keywords :PROTECT and :PROTECT-DEFAULT.

; Note: A separate example, which has more comments and is perhaps a bit more
; elementary, may be found in the book defabsstobj-example-1.lisp.  I suggest
; reading through that book before reading through this one.

; The idea of using stobjs for a memo table is not new here; in particular, the
; distributed book from Rob Sumners, books/defexec/other-apps/misc/memos.lisp,
; implements such an idea.  Moreover, the particular function we memoize here,
; a Fibonacci function, is very fast to compute with memoization even if we
; start with an empty memo table each time; thus, with-local-stobj provides a
; means for using an ordinary stobj, as shown in the above book memos.lisp.
; One could, however, imagine wanting to save previous results between
; top-level invocations, in which case a local stobj is not helpful.  In that
; case, it would be really great that we don't have to check the guard on the
; memo table every time we want to run the memoized function.

; In summary: Even though our particular Fibonacci example could be done with
; ordinary stobjs, if you imagine a function whose values you want to save
; between top-level invocations, then you can imagine how the approach
; illustrated below, using abstract stobjs, is potentially very useful.

; Our basic approach is not surprising for a memo table: we keep values in a
; (concrete) stobj array, and keep an invariant that the stobj array maps
; indices to appropriate values, in this case, values from the Fibonnaci
; sequence.  Interestingly, the corresponding abstract stobj will be empty, as
; seen below.

(in-package "ACL2")

; Introduce the concrete stobj that we will use.

(defstobj memo$c
  (ar :type (array t (100)) :resizable t))

; Now comes the recognizer for the abstract stobj, which is logically empty!
; In the logic, we don't use any sort of memo-table.

(defun memo$ap (x)
  (declare (xargs :guard t))
  (null x))

; Here is a standard Fibonacci function.

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
        ((eql n 1) 1)
        (t (+ (fib (- n 1))
              (fib (- n 2))))))

; Next, we develop the invariant (recognizer) on our concrete stobj: the
; function good-memo$cp.

(defun good-arp (n memo$c)
  (declare (xargs :stobjs memo$c
                  :guard (and (natp n)
                              (<= n (ar-length memo$c)))))
  (cond ((zp n) t)
        (t (let* ((n (1- n))
                  (v (ari n memo$c)))
             (and (or (null v)
                      (eql v (fib n)))
                  (good-arp n memo$c))))))

(defun good-memo$cp (memo$c)
  (declare (xargs :stobjs memo$c))
  (good-arp (ar-length memo$c) memo$c))

; Next we define the correspondence function for our concrete and abstract
; stobj, followed by the abstract creator function and the two lemmas about
; creators that will be required when we execute our defabsstobj event.  If we
; don't know the form of those two lemmas, we could find them by evaluating
; (defabsstobj memo :exports (fib2)) after defining all necessary :LOGIC and
; :EXEC: if any lemmas are missing, it prints them out.  But after a little
; experience with defabsstobj, we can easily know what these lemmas are.

(defun-nx memo$corr (memo$c memo$a)
  (declare (xargs :stobjs memo$c :verify-guards nil))
  (good-memo$cp memo$c))

(defun-nx create-memo$a ()
  (declare (xargs :guard t))
  nil)

(DEFTHM CREATE-MEMO{CORRESPONDENCE}
  (MEMO$CORR (CREATE-MEMO$C) (CREATE-MEMO$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-MEMO{PRESERVED}
  (MEMO$AP (CREATE-MEMO$A))
  :RULE-CLASSES NIL)

; Our defabsstobj event will export a function fib2, to be a memoized version
; of fib.  The :LOGIC version of fib2 is easy to define, as follows.

(defun fib2$a (n memo)
  (declare (xargs :guard (natp n)))
  (mv (fib n) memo))

; Next we define the :EXEC version of fib2, fib2$c.  Our approach is to resize
; the stobj array if necessary, and then to call the following function,
; fib2$c-rec, to do the work.  There are several events leading up to fib2$c,
; in support of guard verification.

(defun fib2$c-rec (n memo$c)
  (declare (xargs :stobjs memo$c
                  :guard (and (natp n)
                              (< n (ar-length memo$c))
                              (good-memo$cp memo$c))
                  :verify-guards nil))
  (let ((v (ari n memo$c)))
    (cond ((null v)
           (cond ((zp n)
                  (let* ((v 0)
                         (memo$c (update-ari n v memo$c)))
                    (mv v memo$c)))
                 ((eql n 1)
                  (let* ((v 1)
                         (memo$c (update-ari n v memo$c)))
                    (mv v memo$c)))
                 (t (mv-let (v1 memo$c)
                            (fib2$c-rec (- n 1) memo$c)
                            (mv-let (v2 memo$c)
                                    (fib2$c-rec (- n 2) memo$c)
                                    (let* ((v (+ v1 v2))
                                           (memo$c (update-ari n v memo$c)))
                                      (mv v memo$c)))))))
          (t (mv v memo$c)))))

(local
 (defthm nth-good-arp-lemma
   (implies (and (natp n)
                 (natp k)
                 (<= k (ar-length memo$c))
                 (< n k)
                 (good-arp k memo$c))
            (or (equal (nth n (car memo$c)) nil)
                (equal (nth n (car memo$c))
                       (fib n))))
   :hints (("Goal" :induct (good-arp k memo$c)))
   :rule-classes nil))

(local
 (defthm nth-good-arp-type
   (implies (and (natp n)
                 (< n (ar-length memo$c))
                 (good-arp (ar-length memo$c) memo$c))
            (or (equal (nth n (car memo$c)) nil)
                (natp (nth n (car memo$c)))))
   :hints (("Goal" :use ((:instance nth-good-arp-lemma
                                    (k (ar-length memo$c))))))
   :rule-classes :type-prescription))

(local
 (defthm nth-good-arp-fib
   (implies (and (natp n)
                 (< n (ar-length memo$c))
                 (good-arp (ar-length memo$c) memo$c)
                 (nth n (car memo$c)))
            (equal (nth n (car memo$c))
                   (fib n)))
   :hints (("Goal" :use ((:instance nth-good-arp-lemma
                                    (k (ar-length memo$c))))))))

(local
 (defthm ar-length-mv-nth-1-fib2$c-rec
   (implies (and (force (natp n))
                 (force (< n (ar-length memo$c))))
            (equal (ar-length (mv-nth 1 (fib2$c-rec n memo$c)))
                   (ar-length memo$c)))))

(local
 (defthm ar-length-update-ari
   (implies (and (natp n)
                 (< n (ar-length memo$c)))
            (equal (ar-length (update-ari n v memo$c))
                   (ar-length memo$c)))))

(local
 (defthm good-arp-update-ari
   (implies (and (natp n)
                 (good-arp k memo$c)
                 (equal v (fib n)))
            (good-arp k (update-ari n v memo$c)))))

(local
 (in-theory (disable ar-length update-ari)))

(local
 (defthm fib2$c-rec-correctness
   (implies (and (good-memo$cp memo$c)
                 (natp n)
                 (< n (ar-length memo$c)))
            (and (equal (car (fib2$c-rec n memo$c))
                        (fib n))
                 (good-memo$cp (mv-nth 1 (fib2$c-rec n memo$c)))))))

(verify-guards fib2$c-rec)

; Start proof of good-arp-resize-ar

(local
 (defthm len-resize-list
   (equal (len (resize-list lst n default))
          (nfix n))))

(local
 (defthm ar-length-resize-ar
   (equal (ar-length (resize-ar i memo$c))
          (nfix i))
   :hints (("Goal" :in-theory (enable ar-length)))))

(local
 (defthm nth-resize-list
   (implies (and (natp n)
                 (natp k))
            (equal (nth n (resize-list lst k default))
                   (cond ((< n k)
                          (cond ((< n (len lst))
                                 (nth n lst))
                                (t default)))
                         (t nil))))
   :hints (("Goal"
            :induct ; force a merge
            (list (resize-list lst n default)
                  (resize-list lst k default))))))

(local
 (defthm good-arp-resize-ar
   (implies (and (good-arp (ar-length memo$c) memo$c)
                 (natp k1)
                 (natp k2)
                 (<= k1 k2))
            (good-arp k1 (resize-ar k2 memo$c)))
   :hints (("Goal" :in-theory (enable ar-length)))))

(local (in-theory (disable resize-ar)))

(defun fib2$c (n memo$c)
  (declare (xargs :stobjs memo$c
                  :guard (and (natp n)
                              (good-memo$cp memo$c))))
  (let ((memo$c (if (< n (ar-length memo$c))
                    memo$c
                  (resize-ar (* 2 (1+ n)) memo$c))))
    (fib2$c-rec n memo$c)))

; Now we generate the remaining proof obligations: we evaluate
;   (defabsstobj memo :exports (fib2))
; and paste in the results, which are in CAPS below.  A third potential proof
; obligations, the {GUARD-THM} theorem, is a tautology and thus will be
; dispatched automatically; so it is not printed out.

; With all the lemmas proved above, these go through automatically.

(DEFTHM FIB2{CORRESPONDENCE}
        (IMPLIES (AND (MEMO$CORR MEMO$C MEMO) (NATP N))
                 (LET ((LHS (FIB2$C N MEMO$C))
                       (RHS (FIB2$A N MEMO)))
                      (AND (EQUAL (MV-NTH 0 LHS) (MV-NTH 0 RHS))
                           (MEMO$CORR (MV-NTH 1 LHS)
                                      (MV-NTH 1 RHS)))))
        :RULE-CLASSES NIL)

(DEFTHM FIB2{PRESERVED}
        (IMPLIES (AND (MEMO$AP MEMO) (NATP N))
                 (MEMO$AP (MV-NTH 1 (FIB2$A N MEMO))))
        :RULE-CLASSES NIL)

(DEFTHM FIB2{GUARD-THM}
        (IMPLIES (AND (MEMO$CORR MEMO$C MEMO) (NATP N))
                 (AND (NATP N) (GOOD-MEMO$CP MEMO$C)))
        :RULE-CLASSES NIL)

; Finally we introduce our abstract stobj, memo.  We use the most compact form
; of defabsstobj; for example, :concrete is implicitly memo$c, obtained by
; putting the suffix "$C" on the symbol, memo.

(defabsstobj memo :exports (fib2)
  :protect-default t)

; Test other way of specifying :protect:

(defabsstobj memo-alt
  :concrete memo$c
  :recognizer (memo-alt-p :logic memo$ap :exec memo$cp)
  :creator (create-memo-alt :logic create-memo$a :exec create-memo$c)
  :exports ((fib2-alt :logic fib2$a :exec fib2$c
                                          :protect t))
  :congruent-to memo)

; The following sanity check is trivial to prove.

(defthm fib2-is-fib
  (equal (car (fib2 n memo))
         (fib n)))

; We can define a pure version of fib2 (one not taking a memo argument) using a
; local stobj.  It is still fast.  But this isn't particularly interesting in
; the context of abstract stobjs, since we could do the same thing with
; ordinary stobjs.  More interesting for abstract stobjs is the case where one
; wants to save previous results between top-level invocations, in which case a
; local stobj is not helpful and it's great that we don't have to check the
; good-memo$cp guard on fib2$c every time we want to run memoized Fibonacci.

(defun fib-fast (n)
  (declare (xargs :guard (natp n)))
  (with-local-stobj
   memo
   (mv-let (result memo)
           (fib2 n memo)
           result)))

; Here is a little test that we really are using memoization; certification
; would probably never complete otherwise.

(assert-event
 (equal (fib-fast 1000)
        43466557686937456435688527675040625802564660517371780402481729089536555417949051890403879840079255169295922593080322634775209689623239873322471161642996440906533187938298969649928516003704476137795166849228875))

