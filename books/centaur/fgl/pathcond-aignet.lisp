; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>
 
(in-package "AIGNET")

(include-book "centaur/aignet/mark-impls" :dir :system)
(include-book "aignet-pathcond-stobj")
(include-book "centaur/aignet/deps" :dir :System)
(local (include-book "theory"))
(local (std::add-default-post-define-hook :fix))

(acl2::defstobj-clone pathcond-memo eba :prefix "PCMEMO-")
;; (acl2::defstobj-clone pathcond-memo0 eba :prefix "PCMEMO0-")


(local (in-theory (disable lookup-id-out-of-bounds
                           lookup-id-in-bounds-when-positive)))

(local (in-theory (enable aignet-idp)))

(fty::deffixtype nbalist-stobj :pred nbalistp :fix nbalist-fix :equiv nbalist-equiv)


(defsection nbalist-lookup
  (local (std::set-define-current-function nbalist-lookup))
  (local (in-theory (enable nbalist-lookup)))

  (local (defthm cdr-hons-assoc-equal-when-nbalistp
         (implies (nbalistp x)
                  (and (iff (cdr (hons-assoc-equal n x))
                            (hons-assoc-equal n x))
                       (iff (bitp (cdr (hons-assoc-equal n x)))
                            (hons-assoc-equal n x))))))

  (defret maybe-bitp-of-<fn>
    (acl2::maybe-bitp ans)
    :hints (("goal" :cases (ans)))
    :rule-classes :type-prescription)

  (defret bitp-of-<fn>
    (iff (bitp ans) ans))

  (defthm nbalist-lookup-of-cons
    (equal (nbalist-lookup id (cons (cons key val) x))
           (b* ((rest-lookup (nbalist-lookup id x)))
             (if (and (equal (nfix id) (nfix key))
                      (not rest-lookup))
                 (bfix val)
               rest-lookup)))
    :hints(("Goal" :in-theory (enable nbalist-fix))))

  (defthm nbalist-fix-of-cons
    (equal (nbalist-fix (cons pair x))
           (let* ((rest (nbalist-fix x))
                  (first-key (nfix (car pair)))
                  (first-val (bfix (cdr pair))))
             (if (or (not (consp pair))
                     (nbalist-lookup first-key x))
                 rest
               (cons (cons first-key first-val) rest))))
    :hints(("Goal" :in-theory (enable nbalist-fix))))

  (defthmd nbalist-lookup-redef
    (equal (nbalist-lookup k x)
           (b* ((x (nbalist-fix x))
                ((unless (consp x)) nil)
                ((when (equal (nfix k) (caar x))) (cdar x)))
             (nbalist-lookup k (cdr x))))
    :hints(("Goal" :expand ((hons-assoc-equal (nfix k) (nbalist-fix x)))))
    :rule-classes :definition)

  (defthm nbalist-lookup-in-cdr-when-car
    (implies (and (nbalistp x)
                  (consp x)
                  (equal (nfix k) (caar x)))
             (not (nbalist-lookup k (cdr x))))
    :hints(("Goal" :in-theory (enable nbalist-lookup nbalistp)))))

(local (in-theory (disable nbalist-fix-of-acons)))

(defsection aignet-pathcond-eval
  (defun-sk aignet-pathcond-eval (aignet
                                  nbalist
                                  invals regvals)
    (forall id 
            (implies (nbalist-lookup id nbalist)
                     (equal (nbalist-lookup id nbalist)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-pathcond-eval))

  (defthm aignet-pathcond-eval-of-nbalist-fix
    (equal (aignet-pathcond-eval aignet (nbalist-fix nbalist) invals regvals)
           (aignet-pathcond-eval aignet nbalist invals regvals))
    :hints (("goal" :cases ((aignet-pathcond-eval aignet (nbalist-fix nbalist) invals regvals)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-pathcond-eval clause)))
                   (and lit
                        `(:expand (,lit)
                          :use ((:instance aignet-pathcond-eval-necc
                                 (id (aignet-pathcond-eval-witness . ,(cdr lit)))
                                 (nbalist ,(if (eq (third lit) 'nbalist)
                                                     '(nbalist-fix nbalist)
                                                   'nbalist))))
                          :in-theory (disable aignet-pathcond-eval-necc)))))))

  (defthm aignet-pathcond-eval-of-cons-when-already-bound
    (implies (nbalist-lookup key nbalist)
             (equal (aignet-pathcond-eval aignet (cons (cons key val) nbalist)
                                          invals regvals)
                    (aignet-pathcond-eval aignet nbalist invals regvals)))
    :hints (("goal" :use ((:instance aignet-pathcond-eval-of-nbalist-fix
                           (nbalist (cons (cons key val) nbalist)))
                          (:instance aignet-pathcond-eval-of-nbalist-fix))
             :in-theory (disable aignet-pathcond-eval-of-nbalist-fix))))
             

  (defthm aignet-pathcond-eval-of-cons
    (implies (and (aignet-pathcond-eval aignet nbalist invals regvals)
                  (not (nbalist-lookup key nbalist)))
             (iff (aignet-pathcond-eval aignet (cons (cons key val) nbalist)
                                        invals regvals)
                  (equal (id-eval key invals regvals aignet) (bfix val))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'aignet-pathcond-eval clause)))
                   (if lit
                       `(:expand (,lit))
                     `(:use ((:instance aignet-pathcond-eval-necc
                              (id key)
                              (nbalist (cons (cons key val) nbalist))))
                       :in-theory (disable aignet-pathcond-eval-necc)))))))

  (defthm aignet-pathcond-eval-of-cons-when-already-false
    (implies (not (aignet-pathcond-eval aignet nbalist invals regvals))
             (not (aignet-pathcond-eval aignet (cons (cons key val) nbalist)
                                        invals regvals)))
    :hints (("goal" :cases ((nbalist-lookup key nbalist)))
            (and stable-under-simplificationp
                 (let* ((lit (assoc 'aignet-pathcond-eval clause))
                        (witness `(aignet-pathcond-eval-witness . ,(cdr lit))))
                   (and lit
                        `(:expand (,lit)
                          :cases ((equal ,witness key))
                          :use ((:instance nbalist-lookup-of-cons
                                 (id ,witness)
                                 (x nbalist)))
                          :in-theory (disable nbalist-lookup-of-cons)))))))

  (defthm aignet-pathcond-eval-implies-lookup-not-opposite
    (implies (and (aignet-pathcond-eval aignet nbalist invals regvals)
                  (equal b (b-not (id-eval id invals regvals aignet))))
             (not (equal (nbalist-lookup id nbalist) b)))
    :hints (("goal" :use aignet-pathcond-eval-necc
             :in-theory (disable aignet-pathcond-eval-necc))))

  (defcong bits-equiv equal (aignet-pathcond-eval aignet nbalist invals regvals) 3
    :hints (("Goal" :Cases ((aignet-pathcond-eval aignet nbalist invals regvals)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-pathcond-eval clause))
                      (lit-invals (fourth lit))
                      (other-invals (if (eq lit-invals 'invals)
                                        'acl2::invals-equiv
                                      'invals)))
                   `(:expand (,lit)
                     :use ((:instance aignet-pathcond-eval-necc
                            (id (aignet-pathcond-eval-witness . ,(cdr lit)))
                            (invals ,other-invals)))
                     :in-theory (disable aignet-pathcond-eval-necc)))))))



(defconst *aignet-pathcond-implies-template*
  ;; Dumb template so we don't have to write this body twice in slightly different variants.
  ;; Substitutions: 
  ;; fnname: obvious
  ;; memo-args: memo tables to pass around
  ;; returns: :returns entry
  ;; memo-guard: list of conjuncts for guard of memo-args
  ;; return-unmemo: return ANS (and memo table if applicable) without updating memo table
  ;; return-memo: return ANS while updating memo table
  ;; bind: bind ANS (and memo table if applicable) to return of recursive call
  ;; memo-lookup: b* binders for looking up id in memo table and returning if available
  '(define fnname ((id natp)
                   aignet
                   nbalist-stobj
                   . memo-args)
     :guard (and (< id (num-fanins aignet))
                 . memo-guard)
     :returns returns
     :measure (nfix id)
     :verify-guards nil
     (b* ((id (lnfix id))
          ((when (eql id 0))
           (b* ((ans 0)) return-unmemo))
          (ans (nbalist-stobj-lookup id nbalist-stobj))
          ((when ans) return-unmemo)
          (slot0 (id->slot0 id aignet))
          (type (snode->type^ slot0))
          ((unless (eql type (gate-type)))
           (b* ((ans nil))
             return-unmemo)))
       (b* memo-lookup
         (b* ((fanin0 (snode->fanin^ slot0))
              (bind (fnname (lit->var fanin0)
                            aignet nbalist-stobj . memo-args))
              (f0-res ans)
              (slot1 (id->slot1 id aignet))
              (and-gate-p (eql (snode->regp^ slot1) 0))
              ((when (and f0-res
                          (eql (b-xor f0-res (lit->neg fanin0)) 0)
                          and-gate-p))
               (b* ((ans 0))
                 return-memo))
              ((when (and (not f0-res) (not and-gate-p)))
               (b* ((ans nil))
                 return-memo))
              (fanin1 (snode->fanin^ slot1))
              (bind (fnname (lit->var fanin1)
                            aignet nbalist-stobj . memo-args))
              (f1-res ans)
              ((when (and f1-res
                          (eql (b-xor f1-res (lit->neg fanin1)) 0)
                          and-gate-p))
               (b* ((ans 0))
                 return-memo))
              ((unless (and f0-res f1-res))
               (b* ((ans nil))
                 return-memo))
              (ans (if and-gate-p
                       1 ;; (b-and f0-res f1-res)
                     (b-xor (b-xor f0-res (lit->neg fanin0))
                            (b-xor f1-res (lit->neg fanin1))))))
           return-memo)))
     ///
     (local (in-theory (disable (:d fnname))))
     (verify-guards fnname)))

(define aignet-pathcond-implies-memo-get ((var natp)
                                          pathcond-memo)
  :inline t
  :returns (mv set (val acl2::maybe-bitp :rule-classes :type-prescription))
  :guard (< (+ 1 (* 2 var)) (eba-length pathcond-memo))
  (b* ((memo-bit1 (eba-get-bit (* 2 (the integer (lnfix var))) pathcond-memo))
       (memo-bit0 (eba-get-bit (+ 1 (* 2 (the integer (lnfix var)))) pathcond-memo))
       ((unless (or (eql memo-bit1 1) (eql memo-bit0 1))) (mv nil 0))
       ((when (eql memo-bit1 memo-bit0)) (mv t nil)))
    (mv t memo-bit1)))

(define aignet-pathcond-implies-memo-set ((var natp)
                                          (val acl2::maybe-bitp)
                                          pathcond-memo)
  :inline t
  :returns new-pathcond-memo
  :guard (< (+ 1 (* 2 var)) (eba-length pathcond-memo))
  (case (acl2::maybe-bit-fix val)
    (1 (b* ((pathcond-memo (eba-set-bit (* 2 (the integer (lnfix var))) pathcond-memo)))
         (eba-clear-bit (+ 1 (* 2 (the integer (lnfix var)))) pathcond-memo)))
    (0 (b* ((pathcond-memo (eba-clear-bit (* 2 (the integer (lnfix var))) pathcond-memo)))
         (eba-set-bit (+ 1 (* 2 (the integer (lnfix var)))) pathcond-memo)))
    (t (b* ((pathcond-memo (eba-set-bit (* 2 (the integer (lnfix var))) pathcond-memo)))
         (eba-set-bit (+ 1 (* 2 (the integer (lnfix var)))) pathcond-memo))))
  ///
  (defret aignet-pathcond-implies-memo-get-of-memo-set
    (equal (aignet-pathcond-implies-memo-get var1 new-pathcond-memo)
           (if (equal (nfix var1) (nfix var))
               (mv t (acl2::maybe-bit-fix val))
             (aignet-pathcond-implies-memo-get var1 pathcond-memo)))
    :hints(("Goal" :in-theory (enable aignet-pathcond-implies-memo-get
                                      maybe-bit-fix))))

  ;; (local (in-theory (enable aignet-pathcond-implies-memo-get-of-memo-set)))

  ;; (defret aignet-pathcond-implies-memo-get-of-memo-set-same
  ;;   (equal (aignet-pathcond-implies-memo-get var new-pathcond-memo)
  ;;          (mv t (acl2::maybe-bit-fix val)))
  ;;   :hints(("Goal" :in-theory (disable aignet-pathcond-implies-memo-set))))

  ;; (defret aignet-pathcond-implies-memo-get-of-memo-set-diff
  ;;   (implies (not (equal (nfix var1) (nfix var)))
  ;;            (equal (aignet-pathcond-implies-memo-get var1 new-pathcond-memo)
  ;;                   (aignet-pathcond-implies-memo-get var1 pathcond-memo)))
  ;;   :hints(("Goal" :in-theory (disable aignet-pathcond-implies-memo-set))))

  (defret len-memo-of-<fn>
    (implies (< (+ 1 (* 2 (nfix var))) (len pathcond-memo))
             (equal (len new-pathcond-memo) (len pathcond-memo)))))


(local (defthm bitp-when-maybe-bitp
         (implies (and x (acl2::maybe-bitp x))
                  (bitp x))))

(defsection aignet-pathcond-implies-logic
  (make-event
   (sublis
    '((fnname . aignet-pathcond-implies-logic) ;; fnname: obvious
      (memo-args . nil) ;; memo-args: memo tables to pass around
      (memo-guard . nil) ;; memo-guard: list of conjuncts for guard of memo-args
      (returns . (ans acl2::maybe-bitp :rule-classes :type-prescription)) ;; returns: :returns entry
      (return-unmemo . ans) ;; return-unmemo: return ANS (and memo table if applicable) without updating memo table
      (return-memo . ans) ;; return-memo: return ANS while updating memo table
      (bind . ans) ;; bind: bind ANS (and memo table if applicable) to return of recursive call
      (memo-lookup . nil)) ;; memo-lookup: b* binders for looking up id in memo table and returning if available
    *aignet-pathcond-implies-template*))
  
  (local (std::set-define-current-function aignet-pathcond-implies-logic))
  (local (in-theory (enable (:i aignet-pathcond-implies-logic))))

  (defret eval-when-aignet-pathcond-implies-logic
    (implies (and (aignet-pathcond-eval aignet nbalist-stobj invals regvals)
                  ans)
             (equal ans (id-eval id invals regvals aignet)))
    :hints (("Goal" :induct <call>
             :expand (<call>
                      (aignet-pathcond-implies-logic 0 aignet nbalist-stobj)))
            (and stable-under-simplificationp
                 '(:expand ((id-eval id invals regvals aignet))
                   :in-theory (enable eval-and-of-lits eval-xor-of-lits lit-eval)))))

  (defret aignet-pathcond-implies-logic-not-equal-negation
    (implies (and (aignet-pathcond-eval aignet nbalist-stobj invals regvals)
                  (equal b (b-not (id-eval id invals regvals aignet))))
             (not (equal ans b)))
    :hints (("goal" :use eval-when-aignet-pathcond-implies-logic
             :in-theory (disable eval-when-aignet-pathcond-implies-logic)))))

(defsection aignet-pathcond-implies-memo
  (make-event
   (sublis
    '((fnname . aignet-pathcond-implies-memo) ;; fnname: obvious
      (memo-args . (pathcond-memo)) ;; memo-args: memo tables to pass around
      ;; memo-guard: list of conjuncts for guard of memo-args
      (memo-guard . ((< (+ 1 (* 2 id)) (eba-length pathcond-memo))))
      ;; returns: :returns entry
      (returns . (mv (ans acl2::maybe-bitp :rule-classes :type-prescription)
                     (new-pathcond-memo
                      (implies (< (+ 1 (* 2 (nfix id))) (len pathcond-memo))
                               (equal (len new-pathcond-memo) (len pathcond-memo))))))
      ;; return-unmemo: return ANS (and memo table if applicable) without updating memo table
      (return-unmemo . (mv ans pathcond-memo))
      ;; return-memo: return ANS while updating memo table
      (return-memo . (b* ((pathcond-memo (aignet-pathcond-implies-memo-set id ans pathcond-memo)))
                       (mv ans pathcond-memo)))
      ;; bind: bind ANS (and memo table if applicable) to return of recursive call
      (bind . (mv ans pathcond-memo))
      ;; memo-lookup: b* binders for looking up id in memo table and returning if available
      (memo-lookup . (((mv set ans) (aignet-pathcond-implies-memo-get id pathcond-memo))
                      ((when set) (mv ans pathcond-memo)))))
    *aignet-pathcond-implies-template*))

  (local (in-theory (enable (:i aignet-pathcond-implies-memo))))


  (defun-sk aignet-pathcond-implies-memo-cond (aignet
                                               nbalist-stobj
                                               pathcond-memo)
    (forall id
            (b* (((mv memo-set memo-val) (aignet-pathcond-implies-memo-get
                                          id pathcond-memo)))
              (implies memo-set
                       (equal memo-val
                              (aignet-pathcond-implies-logic id aignet nbalist-stobj)))))
    :rewrite :direct)

  (local (in-theory (disable aignet-pathcond-implies-memo-cond
                             b-xor not)))

  (defret aignet-pathcond-implies-memo-correct
    (implies (aignet-pathcond-implies-memo-cond aignet nbalist-stobj
                                                pathcond-memo)
             (and (equal ans (aignet-pathcond-implies-logic id aignet nbalist-stobj))
                  (aignet-pathcond-implies-memo-cond aignet nbalist-stobj new-pathcond-memo)))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-pathcond-implies-memo-cond clause))
                      (expands '(:expand (<call>
                                          (aignet-pathcond-implies-logic
                                           id aignet nbalist-stobj)
                                          (aignet-pathcond-implies-logic
                                           0 aignet nbalist-stobj)
                                          (aignet-pathcond-implies-memo
                                           0 aignet nbalist-stobj pathcond-memo)))))
                   (if lit
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               ',expands))
                         :expand (,lit)
                         :do-not-induct t)
                     expands)))))


  (defthm aignet-pathcond-implies-memo-cond-of-repeat-0
    (aignet-pathcond-implies-memo-cond aignet
                                       nbalist-stobj
                                       (acl2::repeat n 0))
    :hints(("Goal" :in-theory (enable aignet-pathcond-implies-memo-cond
                                      aignet-pathcond-implies-memo-get)))))



(local (defthm cdr-hons-assoc-under-iff-when-nbalistp
         (implies (nbalistp x)
                  (iff (cdr (hons-assoc-equal a x))
                       (hons-assoc-equal a x)))))

(defthm nbalistp-of-cons-when-lookup
  (equal (nbalistp (cons a x))
         (and (consp a)
              (natp (car a))
              (bitp (cdr a))
              (not (nbalist-lookup (car a) x))
              (nbalistp x)))
  :hints(("Goal" :in-theory (enable nbalist-lookup))))

(local (in-theory (disable nbalistp-of-cons)))

(define nbalist-extension-p ((x nbalistp) (y nbalistp))
  :measure (len (nbalist-fix x))
  (b* ((x (nbalist-fix x)))
    (or (equal x (nbalist-fix y))
        (and (consp x)
             (nbalist-extension-p (cdr x) y))))
  ///
  (defthm nbalist-extension-of-cons
    (nbalist-extension-p (cons pair x) x)
    :hints (("goal" :expand ((nbalist-extension-p (cons pair x) x)))))

  (defthm nbalist-extension-transitive
    (implies (and (nbalist-extension-p x y)
                  (nbalist-extension-p y z))
             (nbalist-extension-p x z)))

  (defthm nbalist-lookup-in-extension
    (implies (and (nbalist-extension-p x y)
                  (nbalist-lookup k y))
             (equal (nbalist-lookup k x)
                    (nbalist-lookup k y)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable nbalist-lookup-redef)))))

  (defthm nbalist-extension-implies-len-gte
    (implies (nbalist-extension-p x y)
             (>= (len (nbalist-fix x)) (len (nbalist-fix y))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-pathcond-eval-of-extension
    (implies (and (nbalist-extension-p x y)
                  (not (aignet-pathcond-eval aignet y invals regvals)))
             (not (aignet-pathcond-eval aignet x invals regvals)))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'aignet-pathcond-eval clause)))
                   `(:expand (,lit)
                     :use ((:instance aignet-pathcond-eval-necc
                            (id (aignet-pathcond-eval-witness . ,(cdr lit)))
                            (nbalist x)))
                     :do-not-induct t :in-theory (disable nbalist-extension-p))))))

  (defthm nbalist-extension-self
    (nbalist-extension-p x x)))


(define nbalist-bound ((x nbalistp))
  :measure (len (nbalist-fix x))
  :returns (bound natp :rule-classes :type-prescription)
  (b* ((x (nbalist-fix x))
       ((when (atom x)) 0))
    (max (caar x)
         (nbalist-bound (cdr x))))
  ///
  (defthmd nbalist-lookup-implies-id-lte-bound
    (implies (nbalist-lookup id nbalist)
             (<= (nfix id) (nbalist-bound nbalist)))
    :hints(("Goal" :in-theory (enable nbalist-lookup-redef)))
    :rule-classes :forward-chaining)

  (defthmd nbalist-lookup-implies-id-lte-bound-natp
    (implies (and (nbalist-lookup id nbalist)
                  (natp id))
             (<= id (nbalist-bound nbalist)))
    :hints (("goal" :use nbalist-lookup-implies-id-lte-bound))
    :rule-classes (:rewrite :forward-chaining)))

(defsection nbalist-depends-on
  (defun-sk nbalist-depends-on (v nbalist aignet)
    (exists id
            (and (nbalist-lookup id nbalist)
                 (depends-on id (innum->id v aignet) aignet))))

  (in-theory (disable nbalist-depends-on
                      nbalist-depends-on-suff))

  ;; (defthm nbalist-not-depends-on-implies-not-depends-on
  ;;   (implies (and (not (nbalist-depends-on v nbalist aignet))
  ;;                 (nbalist-lookup id aignet))
  ;;            (not (depends-on id 

  (defthm aignet-pathcond-eval-of-set-var-when-not-depends-on
    (implies (and (not (nbalist-depends-on v nbalist aignet))
                  (< (nfix v) (num-ins aignet)))
             (equal (aignet-pathcond-eval aignet nbalist (update-nth v val invals) regvals)
                    (aignet-pathcond-eval aignet nbalist invals regvals)))
    :hints (("goal" :cases ((aignet-pathcond-eval aignet nbalist invals regvals))
             :do-not-induct t)
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-pathcond-eval clause)))
                   (and lit
                        `(:expand (,lit)
                          :use ((:instance aignet-pathcond-eval-necc
                                 (id (aignet-pathcond-eval-witness . ,(cdr lit)))
                                 (invals ,(if (eq (fourth lit) 'invals)
                                               '(update-nth v val invals)
                                             'invals)))
                                (:instance nbalist-depends-on-suff
                                 (id (aignet-pathcond-eval-witness . ,(cdr lit)))))
                          :in-theory (disable aignet-pathcond-eval-necc)))))))

  (defthm nbalist-depends-on-of-cons
    (equal (nbalist-depends-on v (cons (cons key val) nbalist) aignet)
           (or (nbalist-depends-on v nbalist aignet)
               (and (not (nbalist-lookup key nbalist))
                    (depends-on key (innum->id v aignet) aignet))))
    :hints (("goal" :cases ((nbalist-depends-on v (cons (cons key val) nbalist) aignet)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'nbalist-depends-on clause))
                      (lit-nbalist (third lit))
                      (other-nbalist (if (eq lit-nbalist 'nbalist)
                                         '(cons (cons key val) nbalist)
                                       'nbalist))
                      (other-lit (update-nth 2 other-nbalist lit)))
                   `(:expand (,other-lit)
                     :use ((:instance nbalist-depends-on-suff
                            (nbalist ,lit-nbalist)
                            (id (if (depends-on key (innum->id v aignet) aignet)
                                    key
                                  (nbalist-depends-on-witness . ,(cdr other-lit))))))
                     :in-theory (disable nbalist-depends-on-suff)))))
    :otf-flg t)

  (defthm nbalist-depends-on-of-nbalist-fix
    (equal (nbalist-depends-on v (nbalist-fix nbalist) aignet)
           (nbalist-depends-on v nbalist aignet))
    :hints (("goal" :cases ((nbalist-depends-on v nbalist aignet)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'nbalist-depends-on clause))
                      (lit-nbalist (third lit))
                      (other-nbalist (if (eq lit-nbalist 'nbalist)
                                         '(nbalist-fix nbalist)
                                       'nbalist))
                      (other-lit (update-nth 2 other-nbalist lit)))
                   `(:expand (,other-lit)
                     :use ((:instance nbalist-depends-on-suff
                            (nbalist ,lit-nbalist)
                            (id (nbalist-depends-on-witness . ,(cdr other-lit)))))
                     :in-theory (disable nbalist-depends-on-suff)))))
    :otf-flg t))



;; (define nbalist-depends-on ((v natp "The input number, in this case")
;;                             (x nbalistp)
;;                             aignet)
;;   :guard (and (< (nfix v) (num-ins aignet))
;;               (< (nbalist-bound x) (num-fanins aignet)))
;;   :guard-hints (("goal" :in-theory (enable nbalist-bound)))
;;   :measure (len (nbalist-fix x))
;;   (b* ((x (nbalist-fix x))
;;        ((when (atom x)) nil))
;;     (or (depends-on (caar x) (innum->id v aignet) aignet)
;;         (nbalist-depends-on v (cdr x) aignet)))
;;   ///

;;   (defthm aignet-pathcond-eval-of-set-var-when-not-depends-on
;;     (implies (not (nbalist-depends-on v nbalist aignet))
;;              (equal (aignet-pathcond-eval nbalist aignet (update-nth v val invals) regvals)
;;                     (aignet-pathcond-eval nbalist aignet invals regvals)))
;;     :hints (("goal" :cases ((aignet-pathcond-eval aignet nbalist invals regvals))
;;              :do-not-induct t)
;;             (and stable-under-simplificationp
;;                  (b* ((lit (assoc 'aignet-pathcond-eval clause)))
;;                    (and lit
;;                         `(:expand (,lit)
;;                           :use ((:instance aignet-pathcond-eval-necc
;;                                  (id (aignet-pathcond-eval-witness . ,(cdr lit)))
;;                                  (nbalist ,(if (eq (fourth lit) 'invals)
;;                                                '(update-nth v val invals)
;;                                              'invals))))
;;                           :in-theory (disable aignet-pathcond-eval-necc))))))))

(define aignet-pathcond-assume-logic ((lit litp)
                                aignet
                                nbalist-stobj)
  :guard (< (lit->var lit) (num-fanins aignet))
  :measure (lit->var lit)
  :returns (mv contradictionp
               (new-nbalist-stobj nbalistp))
  (b* ((id (lit->var lit))
       (neg (lit->neg lit))
       (nbalist-stobj (mbe :logic (non-exec (nbalist-fix nbalist-stobj))
                           :exec nbalist-stobj))
       ((when (eql 0 id))
        (mv (eql neg 0) nbalist-stobj))
       (look (nbalist-stobj-lookup id nbalist-stobj))
       ((when look)
        (mv (eql look neg) nbalist-stobj))
       (slot0 (id->slot0 id aignet))
       (slot1 (id->slot1 id aignet))
       ((when (or (eql neg 1)
                  (not (eql (snode->type slot0) (gate-type)))
                  (eql (snode->regp slot1) 1)))
        (b* ((nbalist-stobj (nbalist-stobj-push id (b-not neg) nbalist-stobj)))
          (mv nil nbalist-stobj)))
       ;; AND node -- go down the branches
       ((mv contradictionp nbalist-stobj)
        (aignet-pathcond-assume-logic (snode->fanin slot0) aignet nbalist-stobj))
       ((when contradictionp) (mv contradictionp nbalist-stobj)))
    (aignet-pathcond-assume-logic (snode->fanin slot1) aignet nbalist-stobj))
  ///
  (defret nbalist-assume-correct
    (implies (and (aignet-pathcond-eval aignet nbalist-stobj invals regvals)
                  (equal 1 (lit-eval lit invals regvals aignet)))
             (and (not contradictionp)
                  (aignet-pathcond-eval aignet new-nbalist-stobj invals regvals)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((lit-eval lit invals regvals aignet))))
            (and stable-under-simplificationp
                 '(:expand ((id-eval (lit->var lit) invals regvals aignet))
                   :in-theory (enable eval-and-of-lits eval-xor-of-lits)))))

  (defret nbalist-assume-eval-new-calist
    (implies (not contradictionp)
             (equal (aignet-pathcond-eval aignet new-nbalist-stobj invals regvals)
                    (and (aignet-pathcond-eval aignet nbalist-stobj invals regvals)
                         (equal 1 (lit-eval lit invals regvals aignet)))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((lit-eval lit invals regvals aignet))))
            (and stable-under-simplificationp
                 '(:expand ((id-eval (lit->var lit) invals regvals aignet))
                   :in-theory (enable eval-and-of-lits eval-xor-of-lits)))))

  (defret nbalist-assume-contradictionp-correct
    (implies (and contradictionp
                  (equal (lit-eval lit invals regvals aignet) 1))
             (not (aignet-pathcond-eval aignet nbalist-stobj invals regvals))))

  (defret nbalist-extension-of-aignet-pathcond-assume-logic
      (nbalist-extension-p new-nbalist-stobj nbalist-stobj)
    :hints(("Goal"
            :induct <call>
            :expand (<call>))))

  (defret nbalist-depends-on-of-aignet-pathcond-assume-logic
    (implies (and (not (nbalist-depends-on v nbalist-stobj aignet))
                  (not (depends-on (lit->var lit) (innum->id v aignet) aignet)))
             (not (nbalist-depends-on v new-nbalist-stobj aignet)))
    :hints(("Goal"
            :induct <call>
            :expand (<call>)))))


(define nbalist-stobj-rewind ((len natp)
                              nbalist-stobj)
  :guard (<= len (nbalist-stobj-len nbalist-stobj))
  :measure (nbalist-stobj-len nbalist-stobj)
  :returns (new-nbalist-stobj nbalistp)
  (b* (((when (mbe :logic (<= (nbalist-stobj-len nbalist-stobj) (nfix len))
                   :exec (int= (nbalist-stobj-len nbalist-stobj) len)))
        (mbe :logic (non-exec (nbalist-fix nbalist-stobj))
             :exec nbalist-stobj))
       (nbalist-stobj (nbalist-stobj-pop nbalist-stobj)))
    (nbalist-stobj-rewind len nbalist-stobj))
  ///
  (local (defthm nbalist-stobj-rewind-of-extension-lemma
           (implies (nbalist-extension-p x y)
                    (equal (nbalist-stobj-rewind (len (nbalist-fix y)) x)
                           (nbalist-fix y)))
           :hints(("Goal" :induct t)
                  (and stable-under-simplificationp
                       '(:expand ((nbalist-extension-p x y)))))))

  (fty::deffixequiv nbalist-stobj-rewind)

  (defthm nbalist-stobj-rewind-of-extension
    (implies (and (nbalist-extension-p x y)
                  (equal (nfix len) (len (nbalist-fix y))))
             (equal (nbalist-stobj-rewind len x)
                    (nbalist-fix y)))
    :hints (("goal" :use ((:instance nbalist-stobj-rewind-of-extension-lemma))
             :in-theory (disable nbalist-stobj-rewind-of-extension-lemma)
             :do-not-induct t))))
                  
(defstobj aignet-pathcond$c
  (aignet-pathcond-nbalist$c :type nbalist-stobj)
  (aignet-pathcond-memo$c :type eba))

(local (include-book "std/lists/repeat" :dir :system))

(define aignet-pathcond-implies$c ((id natp)
                                   aignet aignet-pathcond$c)
  :enabled t
  :guard (< id (num-fanins aignet))
  (stobj-let
   ((nbalist-stobj (aignet-pathcond-nbalist$c aignet-pathcond$c))
    (pathcond-memo (aignet-pathcond-memo$c aignet-pathcond$c)))
   (res pathcond-memo)
   (b* ((pathcond-memo (eba-clear pathcond-memo))
        (pathcond-memo (if (<= (eba-length pathcond-memo) (+ 1 (* 2 (lnfix id))))
                           (resize-eba (max 16 (* 4 (lnfix id))) pathcond-memo)
                         pathcond-memo)))
     (aignet-pathcond-implies-memo id aignet nbalist-stobj pathcond-memo))
   (mv res aignet-pathcond$c)))

(define aignet-pathcond-implies$a ((id natp)
                                   aignet aignet-pathcond$a)
  :enabled t
  :guard (< id (num-fanins aignet))
  (mv (non-exec (aignet-pathcond-implies-logic id aignet aignet-pathcond$a))
      aignet-pathcond$a))


(define aignet-pathcond-assume$c ((lit litp)
                                   aignet aignet-pathcond$c)
  :enabled t
  :guard (< (lit->var lit) (num-fanins aignet))
  (stobj-let
   ((nbalist-stobj (aignet-pathcond-nbalist$c aignet-pathcond$c))
    (pathcond-memo (aignet-pathcond-memo$c aignet-pathcond$c)))
   (contra nbalist-stobj pathcond-memo)
   (b* (((mv contra nbalist-stobj)
         (aignet-pathcond-assume-logic lit aignet nbalist-stobj))
        (pathcond-memo (eba-clear pathcond-memo)))
     (mv contra nbalist-stobj pathcond-memo))
   (mv contra aignet-pathcond$c)))

(define aignet-pathcond-assume$a ((lit litp)
                                  aignet aignet-pathcond$a)
  :enabled t
  :guard (< (lit->var lit) (num-fanins aignet))
  (b* (((mv contra aignet-pathcond$a) (non-exec (aignet-pathcond-assume-logic lit aignet aignet-pathcond$a))))
    (mv contra aignet-pathcond$a)))

(define aignet-pathcond-len$c (aignet-pathcond$c)
  :enabled t
  (stobj-let ((nbalist-stobj (aignet-pathcond-nbalist$c aignet-pathcond$c)))
             (len)
             (nbalist-stobj-len nbalist-stobj)
             len))

(define aignet-pathcond-len$a (aignet-pathcond$a)
  :enabled t
  (len (ec-call (nbalist-fix aignet-pathcond$a))))

(define aignet-pathcond-rewind$c ((len natp) aignet-pathcond$c)
  :enabled t
  :guard (<= len (aignet-pathcond-len$c aignet-pathcond$c))
  (stobj-let ((nbalist-stobj (aignet-pathcond-nbalist$c aignet-pathcond$c)))
             (nbalist-stobj)
             (nbalist-stobj-rewind len nbalist-stobj)
             aignet-pathcond$c))

(define aignet-pathcond-rewind$a ((len natp) aignet-pathcond$a)
  :enabled t
  :guard (<= len (aignet-pathcond-len$a aignet-pathcond$a))
  (non-exec (nbalist-stobj-rewind len aignet-pathcond$a)))

(encapsulate nil
  (local (define aignet-pathcond-corr (aignet-pathcond$c aignet-pathcond$a)
           :non-executable t
           :enabled t
           (equal aignet-pathcond$a (nth *aignet-pathcond-nbalist$c* aignet-pathcond$c))))

  (local (in-theory (disable (acl2::repeat))))

  (defabsstobj-events aignet-pathcond
    :concrete aignet-pathcond$c
    :corr-fn aignet-pathcond-corr
    :recognizer (aignet-pathcondp :logic nbalist-stobj$ap
                                  :exec aignet-pathcond$cp)
    :creator (create-aignet-pathcond :logic create-nbalist-stobj$a
                                     :exec create-aignet-pathcond$c)
    :exports ((aignet-pathcond-implies :logic aignet-pathcond-implies$a
                                       :exec aignet-pathcond-implies$c
                                       :protect t)
              (aignet-pathcond-assume :logic aignet-pathcond-assume$a
                                           :exec aignet-pathcond-assume$c
                                           :protect t)
              (aignet-pathcond-len :logic aignet-pathcond-len$a
                                   :exec aignet-pathcond-len$c)
              (aignet-pathcond-rewind :logic aignet-pathcond-rewind$a
                                      :exec aignet-pathcond-rewind$c
                                      :protect t))))


