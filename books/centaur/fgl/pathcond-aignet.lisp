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
(include-book "centaur/misc/intstack" :dir :system)
(include-book "centaur/aignet/semantics" :dir :system)
(local (include-book "theory"))
(local (std::add-default-post-define-hook :fix))

(acl2::defstobj-clone pathcond-nodebits acl2::bitarr :prefix "PATHCOND-")
(acl2::defstobj-clone pathcond-nodestack acl2::intstack :prefix "PATHCOND-")
(acl2::defstobj-clone pathcond-memo eba :prefix "PCMEMO-")
;; (acl2::defstobj-clone pathcond-memo0 eba :prefix "PCMEMO0-")


(local (in-theory (disable lookup-id-out-of-bounds
                           lookup-id-in-bounds-when-positive)))

(local (in-theory (enable aignet-idp)))

(fty::defalist node-bit-alist :key-type natp :val-type bitp :true-listp t)

(define nbalistp (x)
  (and (node-bit-alistp x)
       (no-duplicatesp-equal (alist-keys x)))
  ///
  (defthm nbalistp-of-cons
    (implies (and (nbalistp 


(defstobj aignet-pathcond$c
  (pathcond-nodebits$c :type bitarr)
  (pathcond-nodestack$c :type acl2::intstack))


(define aignet-pathcond-lookup ((id natp)
                                pathcond-nodebits
                                pathcond-nodestack)
  :guard (< id (bits-length pathcond-nodebits))
  :returns (ans acl2::maybe-bitp :rule-classes :type-prescription)
  (and (acl2::intstack-member id pathcond-nodestack)
       (get-bit id pathcond-nodebits)))

(define aignet-pathcond-push ((id natp)
                              (val bitp)
                              pathcond-nodebits
                              pathcond-nodestack)
  :guard (not (acl2::intstack-member id pathcond-nodestack))
  :returns (mv new-pathcond-nodebits
               new-pathcond-nodestack)
  (b* ((pathcond-nodestack (acl2::intstack-push id pathond-nodestack))
       (pathcond-nodebits (set-bit id val pathcond-nodebits)))
    (mv pathcond-nodebits pathcond-nodestack)))
  

(defsection aignet-pathcond-eval
  (defun-sk aignet-pathcond-eval (aignet
                                  pathcond-nodebits
                                  pathcond-nodestack
                                  invals regvals)
    (forall id 
            (implies (member id pathcond-nodestack)
                     (equal (nth id pathcond-nodebits)
                            (acl2::id-eval id invals regvals aignet))))
    :rewrite :direct)

  

  )




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
                   pathcond-nodestack
                   pathcond-nodebits
                   . memo-args)
     :guard (and (< id (num-fanins aignet))
                 (< id (bits-length pathcond-nodebits))
                 . memo-guard)
     :returns returns
     :measure (nfix id)
     :verify-guards nil
     (b* ((id (lnfix id))
          ((when (eql id 0))
           (b* ((ans 0)) return-unmemo))
          (boundp (acl2::intstack-member^ id pathcond-nodestack))
          ((when boundp)
           (b* ((ans (get-bit id pathcond-nodebits)))
             return-unmemo))
          (slot0 (id->slot0 id aignet))
          (type (snode->type^ slot0))
          ((unless (eql type (gate-type)))
           (b* ((ans nil))
             return-unmemo)))
       (b* memo-lookup
         (b* ((fanin0 (snode->fanin^ slot0))
              (bind (fnname (lit->var fanin0)
                            aignet pathcond-nodestack pathcond-nodebits . memo-args))
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
                            aignet pathcond-nodestack pathcond-nodebits . memo-args))
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


(defsection aignet-pathcond-implies
  (make-event
   (sublis
    '((fnname . aignet-pathcond-implies) ;; fnname: obvious
      (memo-args . nil) ;; memo-args: memo tables to pass around
      (memo-guard . nil) ;; memo-guard: list of conjuncts for guard of memo-args
      (returns . (ans acl2::maybe-bitp :rule-classes :type-prescription)) ;; returns: :returns entry
      (return-unmemo . ans) ;; return-unmemo: return ANS (and memo table if applicable) without updating memo table
      (return-memo . ans) ;; return-memo: return ANS while updating memo table
      (bind . ans) ;; bind: bind ANS (and memo table if applicable) to return of recursive call
      (memo-lookup . nil)) ;; memo-lookup: b* binders for looking up id in memo table and returning if available
    *aignet-pathcond-implies-template*))
  
  (local (in-theory (enable (:i aignet-pathcond-implies))))

  (




  )

(local (defthm bitp-when-maybe-bitp
         (implies (and x (acl2::maybe-bitp x))
                  (bitp x))))

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
                                               pathcond-nodestack
                                               pathcond-nodebits
                                               pathcond-memo)
    (forall id
            (b* (((mv memo-set memo-val) (aignet-pathcond-implies-memo-get
                                          id pathcond-memo)))
              (implies memo-set
                       (equal memo-val
                              (aignet-pathcond-implies id aignet pathcond-nodestack pathcond-nodebits)))))
    :rewrite :direct)

  (local (in-theory (disable aignet-pathcond-implies-memo-cond
                             b-xor not)))

  (defret aignet-pathcond-implies-memo-correct
    (implies (aignet-pathcond-implies-memo-cond aignet pathcond-nodestack pathcond-nodebits
                                                pathcond-memo)
             (and (equal ans (aignet-pathcond-implies id aignet pathcond-nodestack pathcond-nodebits))
                  (aignet-pathcond-implies-memo-cond aignet pathcond-nodestack pathcond-nodebits new-pathcond-memo)))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'aignet-pathcond-implies-memo-cond clause))
                      (expands '(:expand (<call>
                                          (aignet-pathcond-implies
                                           id aignet pathcond-nodestack pathcond-nodebits)
                                          (aignet-pathcond-implies
                                           0 aignet pathcond-nodestack pathcond-nodebits)
                                          (aignet-pathcond-implies-memo
                                           0 aignet pathcond-nodestack pathcond-nodebits pathcond-memo)))))
                   (if lit
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               ',expands))
                         :expand (,lit)
                         :do-not-induct t)
                     expands)))))


  (defthm aignet-pathcond-implies-memo-cond-of-repeat-0
    (aignet-pathcond-implies-memo-cond aignet
                                       pathcond-nodestack
                                       pathcond-nodebits
                                       (acl2::repeat n 0))
    :hints(("Goal" :in-theory (enable aignet-pathcond-implies-memo-cond
                                      aignet-pathcond-implies-memo-get)))))




                                               
        


