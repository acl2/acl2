; Copyright (C) 2011-2017, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines a checker for resolution proofs and proves that the checker
; is sound.  See also the supporting book zz-resolve.lisp.

(in-package "ACL2")

(include-book "centaur/aig/misc" :dir :system)
(local (include-book "zz-resolve"))

(encapsulate
 ((zzchk-debug-level () t))
 (local (defun zzchk-debug-level ()
          0))
 (defthm natp-zzchk-debug-level
   (natp (zzchk-debug-level))
   :rule-classes :type-prescription))

(defun zzchk-debug-level-0 ()
  (declare (xargs :guard t))
  0)

(defun zzchk-debug-level-1 ()
  (declare (xargs :guard t))
  1)

(defun zzchk-debug-level-2 ()
  (declare (xargs :guard t))
  2)

(defmacro set-zzchk-debug-level (n)
  `(defattach zzchk-debug-level
     ,(case n
        (0 'zzchk-debug-level-0)
        (1 'zzchk-debug-level-1)
        (2 'zzchk-debug-level-2)
        (otherwise (er hard 'set-zzchk-debug-level
                       "Illegal debug print level: only levels ~&0 are ~
                        supported."
                       '(0 1 2))))))

(set-zzchk-debug-level 1)

(defmacro zzchk-with-debug (level msg form)
  `(prog2$ (if (<= ,level (zzchk-debug-level))
               (cw "~@0~|" ,msg)
             nil)
           ,form))

(verify-termination er-cmp-fn)
(verify-guards er-cmp-fn)

(defun lookup-cl (id cl-alist ctx)
  (declare (xargs :guard t))
  (let ((pair (hons-get id cl-alist)))
    (cond (pair (mv nil (cdr pair)))
          (t (er-cmp ctx
                     "Clause id not found: ~x0"
                     id)))))


(defn weak-alistp (x)
  (cond ((atom x) x)
        ((consp (car x))
         (weak-alistp (cdr x)))
        (t nil)))

; Also in zz-resolve.lisp
(defun strip-nonnil-cars (alist ans)
  (declare (xargs :guard (weak-alistp alist)))
  (cond ((atom alist) ans)
        ((cdar alist)
         (strip-nonnil-cars (cdr alist)
                            (cons (caar alist) ans)))
        (t
         (strip-nonnil-cars (cdr alist)
                            ans))))

; From zz-resolve.lisp:
(local
 (defun aig-cl+-eval (cl+ env)
   (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                   nil)
                env)))

(defthm weak-alistp-hons-shrink-alist
  (implies (weak-alistp ans)
           (weak-alistp (hons-shrink-alist alist ans))))

(defun cl+2cl (cl+)
  (declare (xargs :guard t))
  (let ((alist (hons-shrink-alist cl+ 'cl+-final-cdr)))
    (strip-nonnil-cars (fast-alist-free alist) nil)))

; From zz-resolve.lisp:
(defmacro zzchk-negate-lit (lit)
  `(aig-not ,lit))

; From zz-resolve.lisp:
(defund zzchk-resolve1 (cl1+ cl2 lit)
  (declare (xargs :guard t))
  (cond ((atom cl2) cl1+)
        ((and lit ; presumably an optimization
              (hons-equal (car cl2) lit))
         (zzchk-resolve1 cl1+ (cdr cl2) nil))
        (t
         (zzchk-resolve1 (hons-acons (car cl2) t cl1+)
                         (cdr cl2)
                         lit))))

; From zz-resolve.lisp:
(defund zzchk-resolve (cl1+ cl2 lit)

; Cl1+ is a fast-alist: elements associated with T are those that are viewed as
; belonging to a clause, cl1.  We return the result of updating cl1+ by
; resolving it with clause cl2, removing the negation of lit from cl1+ and lit
; from cl2.  But as in Niklas's binResolve function (file
; Centaur/Main_c_demo.c), we do not check for the presence of lit or its
; negation.

  (declare (xargs :guard t))
  (zzchk-resolve1 (hons-acons (zzchk-negate-lit lit) nil cl1+)
                  cl2
                  lit))

(defun zzchk-chain1 (chain cl+ cl-alist)

; See zzchk-chain.

  (declare (xargs :guard (alistp chain)))
  (cond ((endp chain)
         (mv nil (cl+2cl cl+)))
        (t (er-let*-cmp
            ((cl2 (lookup-cl (cdar chain) cl-alist 'zzchk-chain1)))
            (zzchk-chain1 (cdr chain)
                          (zzchk-resolve cl+ cl2 (caar chain))
                          cl-alist)))))

(defun zzchk-chain (chain id cl-alist)

; Chain is of the following form, where each id is a clause id and each lit is
; a literal.

; (id0
;  (lit1 . id1) (lit2 . id2) (lit3 . id3) ... (litk . idk))

; Cl-alist is an alist mapping clause ids to clauses, where a clause is a list
; of literals.

; We "execute" the chain to produce (mv erp cl), where erp is either nil or an
; error message, and cl is the resolution result: id0 and id1 resolve on lit1
; to produce a clause, which in turn is resolved on lit2 with id2 to produce
; another clause, and so on.  The final clause will be named id, but id is only
; used by this function for constructing an error message.

  (declare (xargs :guard (and (consp chain)
                              (alistp (cdr chain)))))
  (zzchk-with-debug
   2
   (msg "~x0: chain, length ~x1"
        id (len chain))
   (er-let*-cmp
    ((cl (lookup-cl (car chain) cl-alist 'zzchk-chain)))
    (zzchk-chain1 (cdr chain)
                  (hons-put-list cl t 'cl+-final-cdr)
                  cl-alist))))

(defn hons< (x y)
; based closely on lexorder
  (cond ((atom x)
         (cond ((atom y)

; Historical Plaque:  Here once was found the comment:
;    From the VM one can conclude that ALPHORDER is a
;    total ordering when restricted to ATOMs.
; attesting to the Interlisp ancestry of this theorem prover.

                (alphorder x y))
               (t t)))
        ((atom y) nil)
        ((hons-equal (car x) (car y))
         (hons< (cdr x) (cdr y)))
        (t (hons< (car x) (car y)))))

(defn aig-norm (x)

; This function should probably be memoized.  We might want to memoize hons<
; too, but early experiments seem to suggest that it's not necessary to do so.

  (cond ((aig-atom-p x) x)
        ((null (cdr x))
         (aig-not (aig-norm (car x))))
        (t (let ((a (aig-norm (car x)))
                 (b (aig-norm (cdr x))))
             (if (hons< a b) (aig-and a b) (aig-and b a))))))

(memoize 'aig-norm :condition '(and (consp x) (cdr x)))

(defun zzchk-root0 (not-and-x-y x-or-y)

; We handle cases (a) and (b) described in zzchk-root.

  (declare (xargs :guard t))
  (and (not (aig-atom-p not-and-x-y))
       (null (cdr not-and-x-y)) ; NOT node
       (not (aig-atom-p (car not-and-x-y))) ; AND node (under the NOT)

; The following is part of (car not-and-x-y) being an AND node, but originally
; I forgot it.  I discovered my error when proving zzchk-run-proof-correct-root
; (actually a corresponding lemma I thought I might need zzchk-root0).

       (cdr (car not-and-x-y))
       (or (hons-equal (caar not-and-x-y) x-or-y)
           (hons-equal (cdar not-and-x-y) x-or-y))))

(defun zzchk-root1 (and-notx-noty x y)

; We handle case (c) described in zzchk-root.

  (declare (xargs :guard t))
  (and (not (aig-atom-p and-notx-noty))
       (cdr and-notx-noty) ; AND node
       (let ((x1 (aig-not x))
             (y1 (aig-not y)))
         (or (and (hons-equal x1 (car and-notx-noty))
                  (hons-equal y1 (cdr and-notx-noty)))
             (or (and (hons-equal x1 (cdr and-notx-noty))
                      (hons-equal y1 (car and-notx-noty))))))))

(defun zzchk-root2 (a not-a)
  (declare (xargs :guard t))
  (and (not (aig-atom-p not-a))
       (null (cdr not-a))
       (hons-equal (car not-a) a)))
       

(defun zzchk-root (cl id)

; Cl is a list of AIGs.  We return a context-message pair, which generally will
; be (mv nil cl).  We can return that result any time that (the disjunction of)
; cl is provably true, but we choose to apply the stronger "Tseitin" criterion,
; namely, that cl is one of the following clauses derived from an AND node, w =
; (u . v):

; (a) w => u, i.e., {~w, u}
; (b) w => v, i.e., {~w, v}
; (c) (u & v) => w, i.e., {~u, ~v, w}

; The returned clause will be named id, but this function only uses id for
; constructing an error message.

  (declare (xargs :guard t))
  (let ((len (len cl)))
    (zzchk-with-debug
     2
     (msg "~x0: root, length ~x1"
          id len)
     (cond ((or (and (eql len 2)
                     (or (zzchk-root0 (car cl) (cadr cl))
                         (zzchk-root0 (cadr cl) (car cl))
                         (zzchk-root2 (car cl) (cadr cl))
                         (zzchk-root2 (cadr cl) (car cl))))
                (and (eql len 3)
                     (or (zzchk-root1 (car cl) (cadr cl) (caddr cl))
                         (zzchk-root1 (cadr cl) (car cl) (caddr cl))
                         (zzchk-root1 (caddr cl) (car cl) (cadr cl)))))
            (mv nil cl))
           (t (er-cmp 'zzchk-root
                      "Found bad alleged root clause of length ~x0, ~x1:~%  ~y2"
                      len id cl))))))

(defun zzchk-run-proof-guard (proof)
  (declare (xargs :guard t))
  (cond ((atom proof) (null proof))
        (t (and (consp (car proof))
                (consp (cdr (car proof)))
                (case (cadar proof)
                  (chain (let ((chain (cddr (car proof))))
                           (and (consp chain)
                                (alistp (cdr chain)))))
                  (t t))
                (zzchk-run-proof-guard (cdr proof))))))

(defun zzchk-run-proof (proof alist)

; We return an alist that extends the given alist, associating ids with
; generated clauses.  Note that the second argument is initially a fast alist,
; and we maintain that property as we recur.

  (declare (xargs :guard (zzchk-run-proof-guard proof)
                  :guard-hints
                  (("Goal" :expand ((zzchk-run-proof-guard proof))))))
  (cond ((endp proof)
         (mv nil alist))
        (t (let* ((step (car proof))
                  (id (car step))
                  (typ (cadr step))
                  (data (cddr step)))
             (er-let*-cmp
              ((cl (case typ
                     (root (zzchk-root data id))
                     (chain (zzchk-chain data id alist))
                     (t (er-cmp 'zzchk-run-proof
                                "Unexpected type, ~x0"
                                typ)))))
              (zzchk-run-proof (cdr proof)
                               (hons-acons id cl alist)))))))

(verify-termination evisc-tuple
                    (declare (xargs :guard t)))

(defun resolution-step-count (proof acc)
  (declare (xargs :guard (and (zzchk-run-proof-guard proof)
                              (acl2-numberp acc))))
  (cond ((endp proof)
         acc)
        (t (resolution-step-count
            (cdr proof)
            (let ((step (car proof)))
              (cond ((eq (cadr step) 'chain)
                     (+ (length (cdr (cddr step))) acc))
                    (t acc)))))))

(defun zzchk-check (aig proof)

; We have considered replacing the :guard here and in all functions above by T,
; and doing the necessary consp checks as part of the proof-checking.  That
; would probably be more efficient.  However, the cost is probably in the
; noise, and this way we have executable documentation of the expected shape of
; a proof.

; We assume that aig is already normalized in the sense that there are no two
; components of the form (x . y) and (y . x).

  (declare (xargs :guard (or (null aig)
                             (zzchk-run-proof-guard proof))))
  (cond
   ((null aig)
    t)
   (t
    (let ((proof-length (len proof)))
      (mv-let (ctx val)
              (zzchk-with-debug
               1
               (msg "Note: Checking SAT proof (~x0 lines, ~x1 resolution ~
                     steps)....~|"
                    proof-length
                    (resolution-step-count proof 0))
               (time$ (zzchk-run-proof proof

; Jared Davis has pointed out that the final cdr of a fast alist is used for
; allocating the size of the initial hash table.  This fast alist will
; ultimately contain one entry for each line of the proof; we add one to the
; length just to play it safe.

                                       (1+ proof-length))
                      :msg "done; cpu ~sc; real ~st; mem ~sa~%"))
              (cond (ctx (prog2$ (cw "Error in zzchk-run-proof:~|~@0~|~%" val)
                                 nil))
                    ((not (consp val))
                     (prog2$ (cw "Error in zzchk-chk (unexpected atomic case; ~
                                  expected list of pairs, but first `pair' is ~
                                  ~x0)~%"
                                 val)
                             nil))
                    ((let* ((last-step (car val))
                            (last-cl (and (consp last-step)
                                          (cdr last-step))))
                       (cond ((not (and (consp last-cl)
                                        (null (cdr last-cl))))
                              (prog2$ (cw "Error in zzchk-chk (unexpected ~
                                           case where last clause has length ~
                                           ~x2,not `).~%"
                                          (len last-cl))
                                      nil))
                             ((zzchk-with-debug
                               1
                               (msg "Note: Checking that input AIG is what ~
                                     was proved....~|")
                               (time$
                                (hons-equal aig
                                            (aig-not (aig-norm (car last-cl))))
                                :msg "done; cpu ~sc; real ~st; mem ~sa~%")))
                             (t
                              (prog2$ (let ((evisc-tuple
                                             (evisc-tuple 3 ; print-level
                                                          4 ; print-length
                                                          nil ; alist
                                                          nil ; hiding-cars
                                                          )))
                                        (cw "Error in final ~
                                             check.~|Expected:~|~Y01~%Produced ~
                                             (but with ~
                                             renormalization):~|~Y23~%"
                                            aig
                                            evisc-tuple
                                            (aig-not (aig-norm (car last-cl)))
                                            evisc-tuple))
                                      nil)))))))))))

; Start proof of zzchk-check-correct.

(local
 (defun aig-cl-eval (cl env) ; redundant; see zz-resolve.lisp
   (cond ((atom cl) nil)
         ((aig-eval (car cl) env) t)
         (t (aig-cl-eval (cdr cl) env)))))

(local
 (defun aig-cl-lst-eval (cl-lst env) ; redundant; see zz-resolve.lisp
   (cond ((atom cl-lst) t)
         ((aig-cl-eval (car cl-lst) env)
          (aig-cl-lst-eval (cdr cl-lst) env))
         (t nil))))

; Start proof of zzchk-run-proof-correct-root.

(local (defthm equal-+-n-len
         (implies (and (syntaxp (quotep i))
                       (syntaxp (quotep j))
                       (acl2-numberp j))
                  (equal (equal (+ i (len x)) j)
                         (equal (len x) (- j i))))))

(local (defthm equal-len-k
         (implies (and (syntaxp (quotep j))
                       (posp j))
                  (equal (equal (len x) j)
                         (and (consp x)
                              (equal (len (cdr x))
                                     (1- j)))))))

(local (defthm equal-len-0
         (equal (equal (len x) 0)
                (atom x))))

(defthmd aig-eval-aig-norm
  (equal (aig-eval (aig-norm x) env)
         (aig-eval x env)))

(local
 (defthm zzchk-run-proof-correct-root-1
   (implies (and (zzchk-root0 lit2 lit1)
                 (not (aig-eval lit1 env)))
            (aig-eval lit2 env))))

(local
 (defthm zzchk-run-proof-correct-root-2
   (implies (and (zzchk-root0 lit1 lit2)
                 (not (aig-eval lit1 env)))
            (aig-eval lit2 env))))

(local
 (defthm zzchk-run-proof-correct-root-3
   (implies (and (zzchk-root1 lit1 lit2 lit3)
                 (not (aig-eval lit1 env))
                 (not (aig-eval lit2 env)))
            (aig-eval lit3 env))))

(local
 (defthm zzchk-run-proof-correct-root-4
   (implies (and (zzchk-root1 lit3 lit1 lit2)
                 (not (aig-eval lit1 env))
                 (not (aig-eval lit2 env)))
            (aig-eval lit3 env))))

(local
 (defthm zzchk-run-proof-correct-root-5
   (implies (and (zzchk-root1 lit2 lit1 lit3)
                 (not (aig-eval lit1 env))
                 (not (aig-eval lit2 env)))
            (aig-eval lit3 env))))

(local
 (defthm zzchk-run-proof-correct-root
   (implies (not (mv-nth 0 (zzchk-root cl id)))
            (aig-cl-eval (mv-nth 1 (zzchk-root cl id))
                         env))
   :hints (("Goal" :in-theory (disable zzchk-root0 zzchk-root1)))))

; Start proof of zzchk-run-proof-correct-chain-1.

; Note that aig-cl-lst-eval-implies-aig-cl-eval and aig-cl+-eval-zzchk-resolve
; are useful here (imported from zz-resolve.lisp).

(local
 (defthm zzchk-run-proof-correct-chain-1-1-1-1
   (implies (aig-cl+-eval cl+ env)
            (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+
                                                               'cl+-final-cdr)
                                            nil)
                         env))))

(local
 (in-theory (disable aig-cl+-eval)))

(local
 (defthm zzchk-run-proof-correct-chain-1-1-1
   (implies (aig-cl+-eval cl+ env)
            (mv-let (flg result)
                    (zzchk-chain1 pairs cl+ cl-alist)
                    (implies (and (aig-cl-lst-eval (strip-cdrs cl-alist) env)
                                  (not flg))
                             (aig-cl-eval result env))))
   :rule-classes nil))

(local
 (defthm zzchk-run-proof-correct-chain-1-1
   (implies (aig-cl-eval cl env)
            (let ((cl+ (hons-put-list cl t 'cl+-final-cdr)))
              (mv-let (flg result)
                      (zzchk-chain1 pairs cl+ cl-alist)
                      (implies (and (aig-cl-lst-eval (strip-cdrs cl-alist) env)
                                    (not flg))
                               (aig-cl-eval result env)))))
   :hints (("Goal" :use ((:instance zzchk-run-proof-correct-chain-1-1-1
                                    (cl+ (hons-put-list cl t 'cl+-final-cdr))))
            :in-theory (disable hons-put-list aig-cl-eval aig-cl+-eval)))))

(local
 (defthm zzchk-run-proof-correct-chain-1
   (mv-let (flg result)
           (zzchk-chain1 pairs
                         (hons-put-list (cdr (hons-assoc-equal id cl-alist))
                                        t
                                        'cl+-final-cdr)
                         cl-alist)
           (implies (and (aig-cl-lst-eval (strip-cdrs cl-alist) env)
                         (hons-assoc-equal id cl-alist)
                         (not flg))
                    (aig-cl-eval result env)))
   :rule-classes nil))

(local
 (defthm zzchk-run-proof-correct-chain
   (implies (and (aig-cl-lst-eval (strip-cdrs cl-alist) env)
                 (not (mv-nth 0 (zzchk-chain chain id cl-alist))))
            (aig-cl-eval (mv-nth 1 (zzchk-chain chain id cl-alist))
                         env))
   :hints (("Goal" :use (:instance zzchk-run-proof-correct-chain-1
                                   (id (car chain))
                                   (pairs (cdr chain)))))))

(local
 (defthm zzchk-run-proof-correct
   (implies (aig-cl-lst-eval (strip-cdrs alist) env)
            (mv-let (flg result)
                    (zzchk-run-proof proof alist)
                    (implies (null flg)
                             (aig-cl-lst-eval (strip-cdrs result) env))))
   :hints (("Goal" :in-theory (disable zzchk-root zzchk-chain)))
   :rule-classes nil))

(defthmd zzchk-check-correct-original
  (implies (zzchk-check aig proof)
           (not (aig-eval aig env)))
  :hints (("Goal"
           :use ((:instance zzchk-run-proof-correct
                            (alist (1+ (len proof)))))
           :in-theory (e/d (aig-eval-aig-norm) (zzchk-run-proof))
           :expand
           ((strip-cdrs (mv-nth 1 (zzchk-run-proof proof
                                                   (1+ (len proof)))))))))


(defthm zzchk-check-correct
  (implies (zzchk-check (aig-norm aig) proof)
           (not (aig-eval aig env)))
  :hints (("Goal"
           :use ((:instance zzchk-check-correct-original
                            (aig (aig-norm aig))))
           :in-theory (enable aig-eval-aig-norm))))

(in-theory (disable zzchk-check))
