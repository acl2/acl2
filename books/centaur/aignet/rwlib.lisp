; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
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

(include-book "centaur/truth/sizes" :dir :system)
(include-book "centaur/truth/perm4" :dir :system)
(include-book "centaur/misc/smm" :dir :system)
(include-book "tools/symlet" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "construction")
(include-book "std/stobjs/nested-stobjs" :dir :system)
(include-book "copying")

(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (in-theory (disable unsigned-byte-p signed-byte-p nth update-nth
                           acl2::resize-list-when-atom)))
(local (std::add-default-post-define-hook :fix))

; Matt K. addition: Avoid stack overflow when writing the .cert file, which has
; happened using Allegro CL (with ACL2(r) but probably would happen with ACL2
; as well).
(make-event
 (pprogn (set-serialize-character-system nil state)
         (value '(value-triple nil))))

(local (in-theory (disable nth update-nth acl2::nth-when-zp
                           acl2::nth-when-too-large-cheap
                           lookup-id-in-bounds-when-positive
                           hons-assoc-equal
                           xor)))

(defmacro defalias (x y)
  `(progn (defmacro ,x (&rest args) (cons ',y args))
          (table acl2::macro-aliases-table
                 ',x (or (cdr (assoc ',y (table-alist 'acl2::macro-aliases-table world)))
                         ',y))))

(defalias hq acl2::hq)
(defalias truth4-p truth::truth4-p)
(defalias truth4-fix truth::truth4-fix)
(defalias truth-norm truth::truth-norm)
(defalias truth-eval truth::truth-eval)
(defalias maybe-npn4-fix truth::maybe-npn4-fix)
(defalias npn4-fix truth::npn4-fix)
(defalias npn4-p truth::npn4-p)
(defalias patbind-npn4 truth::patbind-npn4)



(defstobj-clone smm acl2::smm :strsubst (("a" . "a")))
(defstobj-clone truth4arr truth::truth4arr :strsubst (("a" . "a")))
(defstobj-clone truth4arr2 truth::truth4arr :strsubst (("a" . "a")) :suffix "2")
(defstobj-clone smm acl2::smm :strsubst (("a" . "a")))
(defstobj-clone npn4arr truth::npn4arr :strsubst (("a" . "a")))

(defstobj rwlib
  (rwlib->npns :type npn4arr)
  (rwlib->truths :type truth4arr)
  (rwlib->aigs :type aignet)
  (rwlib->cands :type smm))


(defun-sk smm-contains-aignet-lits (smm aignet)
  (forall (block idx)
          (implies (and (< (nfix block) (len smm))
                        (< (nfix idx) (len (nth block smm))))
                   (aignet-litp (nth idx (nth block smm)) aignet)))
  :rewrite :direct)

(in-theory (disable smm-contains-aignet-lits))

(define rwlib-wfp (rwlib)
  (b* (((acl2::stobj-get ok)
        ((npn4arr (rwlib->npns rwlib))
         (truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib)))
        (and (eql (npn4s-length npn4arr) #x10000)
             (ec-call (truth::npn4arr-indices-all-bound npn4arr))
             (ec-call (truth::npn4arr-indices-bounded (smm-nblocks smm) npn4arr))
             (<= (smm-nblocks smm) (truth4s-length truth4arr))
             (eql (num-ins aignet) 4)
             (eql (num-regs aignet) 0)
             (ec-call (smm-contains-aignet-lits smm aignet)))))
    ok)
  ///
  (defthm rwlib-wfp-implies
    (implies (rwlib-wfp rwlib)
             (b* ((npn4arr (rwlib->npns rwlib))
                  (truth4arr (rwlib->truths rwlib))
                  (aignet (rwlib->aigs rwlib))
                  (smm (rwlib->cands rwlib)))
               (and (equal (len npn4arr) #x10000)
                    (truth::npn4arr-indices-all-bound npn4arr)
                    (truth::npn4arr-indices-bounded (len smm) npn4arr)
                    (<= (len smm) (len truth4arr))
                    (equal (aignet::stype-count :pi aignet) 4)
                    (equal (aignet::stype-count :reg aignet) 0)
                    (smm-contains-aignet-lits smm aignet)))))

  (defthm rwlib-wfp-implies-linear
    (implies (rwlib-wfp rwlib)
             (b* ((truth4arr (rwlib->truths rwlib))
                  (smm (rwlib->cands rwlib)))
               (<= (len smm) (len truth4arr))))
    :rule-classes :linear)

  (defthm rwlib-wfp-implies-aignet-litp
    (b* ((smm (rwlib->cands rwlib))
         (aignet (rwlib->aigs rwlib)))
      (implies (and (rwlib-wfp rwlib)
                    (< (nfix n) (len smm))
                    (< (nfix idx) (len (nth n smm))))
               (aignet::aignet-litp (nth idx (nth n smm)) aignet))))

  (defthm rwlib-wfp-implies-less
    (b* ((smm (rwlib->cands rwlib))
         (aignet (rwlib->aigs rwlib)))
      (implies (and (rwlib-wfp rwlib)
                    (< (nfix n) (len smm))
                    (< (nfix idx) (len (nth n smm))))
               (<= (lit->var (nth idx (nth n smm))) (fanin-count aignet))))
    :hints (("goal" :use rwlib-wfp-implies-aignet-litp
             :in-theory (e/d (aignet-idp)
                             (rwlib-wfp-implies-aignet-litp rwlib-wfp)))))

  (defthm rwlib-wfp-implies-npn4arr-indices-exist
    (b* ((npn4arr (rwlib->npns rwlib)))
      (implies (and (rwlib-wfp rwlib)
                    (truth4-p n))
               (equal (maybe-npn4-fix (nth n npn4arr))
                      (npn4-fix (nth n npn4arr)))))
    :hints(("Goal" :in-theory (enable truth4-p unsigned-byte-p))))

  (defthm rwlib-wfp-implies-npn4arr-index-upper-bound
    (b* ((npn4arr (rwlib->npns rwlib))
         (smm (rwlib->cands rwlib)))
      (implies (and (rwlib-wfp rwlib)
                    (truth4-p n))
               (< (truth::npn4->truth-idx (nth n npn4arr)) (len smm))))
    :hints(("Goal" :in-theory (e/d (truth4-p unsigned-byte-p)
                                   (truth::npn4arr-indices-bounded-necc))
            :use ((:instance truth::npn4arr-indices-bounded-necc
                   (bound (len (rwlib->cands rwlib)))
                   (npn4arr (rwlib->npns rwlib))
                   (idx n)))))
    :rule-classes (:rewrite :linear)))


(define truth4-env-from-aignet-invals (invals)
  :returns (env natp :rule-classes :type-prescription)
  :guard (<= 4 (bits-length invals))
  (b* ((0val (acl2::bit->bool (get-bit 0 invals)))
       (1val (acl2::bit->bool (get-bit 1 invals)))
       (2val (acl2::bit->bool (get-bit 2 invals)))
       (3val (acl2::bit->bool (get-bit 3 invals))))
    (truth::env-update 0 0val (truth::env-update 1 1val (truth::env-update 2 2val (truth::env-update 3 3val 0)))))
  ///
  (defret env-lookup-of-truth4-env-from-aignet-invals
    (equal (truth::env-lookup n env)
           (and (< (nfix n) 4)
                (acl2::bit->bool (get-bit n invals))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable truth::env-lookup))))))

(defun-sk aignet-truth-impls-correct (smm aignet truth4arr)
  (forall (n idx invals regvals)
          (implies (and (< (nfix n) (len smm))
                        (< (nfix idx) (len (nth n smm))))
                   (equal (aignet::lit-eval (nth idx (nth n smm)) invals regvals aignet)
                          (bool->bit (truth-eval (nth n truth4arr) (truth4-env-from-aignet-invals invals) 4)))))
  :rewrite :direct)

(in-theory (disable aignet-truth-impls-correct))

(define permuted-env-from-aignet-invals ((npn npn4-p)
                                         (invals))
  :guard (<= 4 (bits-length invals))
  :returns (env natp :rule-classes :type-prescription)
  (b* (((npn4 npn))
       (env (truth4-env-from-aignet-invals invals))
       (env (truth::env-permute-polarity 0 npn.polarity env 4)))
    (truth::env-perm 0 (truth::perm4-index-list npn.perm) env 4))
  ///
  (defret lookup-in-permuted-env-from-aignet-invals
    (implies (< (nfix n) 4)
             (equal (truth::env-lookup n env)
                    (b* (((npn4 npn))
                         (idx (truth::index-perm-rev 0 (truth::perm4-index-list npn.perm) n 4)))
                      (acl2::bit->bool
                       (b-xor
                        (logbit idx npn.polarity)
                        (nth idx invals))))))
    :hints(("Goal" :in-theory (enable b-xor bool->bit)))))

(define rwlib-correct (rwlib)
  (b* (((acl2::stobj-get ok)
        ((npn4arr (rwlib->npns rwlib))
         (truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib)))
        (and (ec-call (truth::npn4arr-correct npn4arr truth4arr))
             (ec-call (aignet-truth-impls-correct smm aignet truth4arr)))))
    ok)
  ///
  (local
   (defthm rwlib-correct-implies-eval-smm-lookup
     (b* ((truth4arr (rwlib->truths rwlib))
          (aignet (rwlib->aigs rwlib))
          (smm (rwlib->cands rwlib)))
       (implies (and (rwlib-correct rwlib)
                     (< (nfix n) (len smm))
                     (< (nfix idx) (len (nth n smm))))
                (equal (aignet::lit-eval (nth idx (nth n smm)) invals regvals aignet)
                       (bool->bit (truth-eval (nth n truth4arr) (truth4-env-from-aignet-invals invals) 4)))))))

  (defthm rwlib-correct-implies-npn4-truth-value-ok
    (b* ((npn4arr (rwlib->npns rwlib))
         (truth4arr (rwlib->truths rwlib)))
      (implies (and (rwlib-correct rwlib)
                    (truth4-p idx))
               (b* ((val (nth idx npn4arr)))
                 (and (equal (maybe-npn4-fix val)
                             (npn4-fix val))
                      (b* (((npn4 val)))
                        (equal (truth::npn4-truth-value val (nth val.truth-idx truth4arr))
                               idx))))))
    :hints(("Goal" :in-theory (enable truth4-p unsigned-byte-p))))

  (defthm rwlib-correct-implies-eval-smm-lookup-of-truth-idx
    (b* ((?truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib))
         (npn4arr (rwlib->npns rwlib))
         ((npn4 npn) (nth truth npn4arr))
         (env (permuted-env-from-aignet-invals npn invals)))
      (implies (and (rwlib-correct rwlib)
                    (rwlib-wfp rwlib)
                    (truth4-p truth)
                    (< (nfix idx) (len (nth npn.truth-idx smm))))
               (equal (aignet::lit-eval (nth idx (nth npn.truth-idx smm)) invals regvals aignet)
                      (b-xor npn.negate
                             (bool->bit (truth-eval truth env 4))))))
    :hints(("Goal" :in-theory (e/d (permuted-env-from-aignet-invals xor)
                                   (rwlib-correct
                                    rwlib->truths
                                    rwlib->aigs
                                    rwlib->cands
                                    rwlib->npns
                                    truth::eval-of-npn4-truth-value-with-permuted-env
                                    truth::eval-of-npn4-truth-value))
            :use ((:instance truth::eval-of-npn4-truth-value-with-permuted-env
                   (npn (nth truth (rwlib->npns rwlib)))
                   (truth (nth (truth::npn4->truth-idx (nth truth (rwlib->npns rwlib)))
                               (rwlib->truths rwlib)))
                   (orig-env (truth4-env-from-aignet-invals invals)))))))

  (defthm rwlib-correct-implies-id-eval-smm-lookup-of-truth-idx
    (b* ((?truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib))
         (npn4arr (rwlib->npns rwlib))
         ((npn4 npn) (nth truth npn4arr))
         (env (permuted-env-from-aignet-invals npn invals)))
      (implies (and (rwlib-correct rwlib)
                    (rwlib-wfp rwlib)
                    (truth4-p truth)
                    (< (nfix idx) (len (nth npn.truth-idx smm))))
               (equal (aignet::id-eval (aignet::lit-id (nth idx (nth npn.truth-idx smm))) invals regvals aignet)
                      (b-xor (aignet::lit-neg (nth idx (nth npn.truth-idx smm)))
                             (b-xor npn.negate
                                    (bool->bit (truth-eval truth env 4)))))))
    :hints (("goal" :use rwlib-correct-implies-eval-smm-lookup-of-truth-idx
             :in-theory (e/d (aignet::lit-eval b-xor bool->bit)
                             (rwlib-correct
                              rwlib-correct-implies-eval-smm-lookup-of-truth-idx
                              rwlib-correct-implies-eval-smm-lookup))))))


(in-theory (disable rwlibp
                    rwlib->npns
                    rwlib->cands
                    rwlib->aigs
                    rwlib->truths))

(define rwlib-num-fanins (rwlib)
  :enabled t
  (stobj-let
   ((aignet (rwlib->aigs rwlib)))
   (count)
   (num-fanins aignet)
   count))

(define rwlib-num-cands (rwlib)
  :enabled t
  (stobj-let
   ((smm (rwlib->cands rwlib)))
   (count)
   (smm-max-index smm)
   count))




;; (depends-on "abcdata.lsp")
(make-event
 (b* (((mv err val state)
       (prog2$
; Matt K. mod: avoid stack overflow in SBCL, maybe other host Lisps:
; Warning: bad-lisp-consp will remain unmemoized after evaluating this form,
; for example after LDing this file.  (However, (include-book "rwlib") will not
; unmemoize bad-lisp-consp.)
        (set-bad-lisp-consp-memoize nil)
        (acl2::read-file "abcdata.lsp" state)))
      ((when err)
       (er hard? '*abcdata* "Couldn't read abcdata.lsp")
       (mv nil nil state))
      ((unless (eql (len val) 3))
       (er hard? '*abcdata* "abcdata.lsp should contain 3 objects but found ~x0" (len val))
       (mv nil nil state)))
   (value `(defconst *abcdata* ',val))))

(defconst *abc-nodes* (cdr (assoc :nodedata *abcdata*)))
(defconst *abc-outs* (cdr (assoc :outdata *abcdata*)))
(defconst *abc-prios* (cdr (assoc :priodata *abcdata*)))

(with-output :off :all :on (error)
  (make-event
   `(progn (define abc-nodes ()
             :inline t
             :returns (nodes nat-listp)
             ',*abc-nodes*
             ///
             (defret len-even-of-abc-nodes
               (integerp (* 1/2 (len nodes)))))
           (define abc-outs ()
             :inline t
             :returns (outs nat-listp)
             ',*abc-outs*)
           (define abc-prios ()
             :inline t
             :returns (prios nat-listp)
             ',*abc-prios*)
           (in-theory (disable (abc-nodes) (abc-outs) (abc-prios))))))


#!truth
(defmacro lit-truth (lit t4arr)
  `(truth-norm4 (logxor (- (aignet::lit-neg ,lit))
                        (get-truth4 (aignet::lit-id ,lit) ,t4arr))))

(defstobj-clone truth4arr truth::truth4arr :strsubst (("a" . "a")))

; Matt K. mod: avoid Allegro CL stack overflow for a call of
; abc-nodes-wellformed.
(set-compile-fns t)

(define abc-nodes-wellformed ((num-fanins natp)
                              (nodedata nat-listp))
  :measure (len nodedata)
  (if (atom nodedata)
      t
    (and (consp (cdr nodedata))
         (< (lit->var (car nodedata)) (lnfix num-fanins))
         (< (lit->var (cadr nodedata)) (lnfix num-fanins))
         (abc-nodes-wellformed (+ 1 (lnfix num-fanins)) (cddr nodedata))))
  ///
  (with-output :off :all :on (error)
    (defthm abc-nodes-wellformed-of-abc-nodes
      (abc-nodes-wellformed 4 (abc-nodes))
      :hints(("Goal" :in-theory (enable (abc-nodes)))))))

(define maybe-grow-litarr ((size natp) litarr)
  :returns (new-litarr)
  (if (< (lits-length litarr) (lnfix size))
      (resize-lits (max 16 (* 2 (lnfix size))) litarr)
    litarr)
  ///
  (defret maybe-grow-litarr-len-gte-size
    (<= (nfix size) (len new-litarr))
    :rule-classes :linear))



(define aignet-build-abc-nodes ((next-idx natp) (nodes nat-listp) copy strash aignet)
  :guard (and (not (equal 0 (num-fanins aignet)))
              (abc-nodes-wellformed next-idx nodes)
              (aignet-copies-in-bounds copy aignet)
              (<= (+ next-idx (/ (len nodes) 2)) (lits-length copy))
              (equal (num-outs aignet) 0)
              (equal (num-nxsts aignet) 0))
  :guard-hints (("goal" :expand ((abc-nodes-wellformed next-idx nodes))))

  :prepwork ((local (defthm no-outputs-when-no-outputs
                      (implies (and (equal (stype-count :po aignet) 0)
                                    (equal (stype-count :nxst aignet) 0))
                               (not (equal (ctype (stype (car (lookup-id n aignet)))) :output)))
                      :hints(("Goal" :in-theory (enable lookup-id stype-count)
                              :induct t)
                             (and stable-under-simplificationp
                                  '(:in-theory (enable ctype))))))
             ;; (local (defthm aignet-litp-when-no-outs
             ;;          (implies (and (equal (stype-count :po aignet) 0)
             ;;                        (equal (stype-count :nxst aignet) 0))
             ;;                   (iff (aignet-litp lit aignet)
             ;;                        (< (lit-id lit) (num-fanins aignet))))
             ;;          :hints(("Goal" :in-theory (enable aignet-litp)))))
             )

  :returns (mv new-copy
               new-strash
               new-aignet)
  (b* (((when (atom nodes))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv copy strash aignet)))
       ((list fanin0 fanin1) nodes)
       ;; (copy (maybe-grow-litarr (+ 1 (lnfix next-idx)) copy))
       (lit0 (lit-copy fanin0 copy))
       (lit1 (lit-copy fanin1 copy))
       ((mv res strash aignet) (aignet-hash-and lit0 lit1 (default-gatesimp) strash aignet))
       (copy (set-lit next-idx res copy)))
    (aignet-build-abc-nodes (+ 1 (lnfix next-idx)) (cddr nodes) copy strash aignet))
  ///
  (defret stype-count-of-aignet-build-abc-nodes
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret aignet-copies-in-bounds-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet)
             (aignet-copies-in-bounds new-copy new-aignet)))

  (defret copy-length-nondecr-of-<fn>
    (<= (len copy) (len new-copy))
    :rule-classes :linear))

(define aignet-build-abc-top (copy aignet)
  :returns (mv new-copy new-aignet)
  (b* ((node-data (abc-nodes))
       ((acl2::local-stobjs strash)
        (mv copy strash aignet))
       (copy (resize-lits 0 copy))
       (copy (resize-lits (+ 5 (/ (len node-data) 2)) copy))
       (aignet (aignet-init 0 0 4 (+ 5 (/ (len node-data) 2)) aignet))
       (aignet (aignet-add-in aignet))
       (aignet (aignet-add-in aignet))
       (aignet (aignet-add-in aignet))
       (aignet (aignet-add-in aignet))
       (copy (set-lit 0 (mk-lit 1 0) copy))
       (copy (set-lit 1 (mk-lit 2 0) copy))
       (copy (set-lit 2 (mk-lit 3 0) copy))
       (copy (set-lit 3 (mk-lit 4 0) copy)))
    (aignet-build-abc-nodes 4 node-data copy strash aignet))
  ///
  (defret stype-counts-of-aignet-build-abc-top
    (and (equal (stype-count :pi new-aignet) 4)
         (equal (stype-count :reg new-aignet) 0)
         (equal (stype-count :po new-aignet) 0)
         (equal (stype-count :nxst new-aignet) 0))))

(define aignet-derive-truth4s ((n natp)
                               (aignet)
                               (truth4arr))
  :guard (and (<= (num-fanins aignet) (truth4s-length truth4arr))
              (<= (num-ins aignet) 4)
              (equal 0 (num-regs aignet))
              (<= n (num-fanins aignet)))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :returns (new-truth4arr)
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :prepwork ((local (in-theory (disable unsigned-byte-p)))
             (local (defthm unsigned-byte-p-when-truth4-p
                      (implies (truth::truth4-p x)
                               (unsigned-byte-p 16 x))
                      :hints(("Goal" :in-theory (enable truth::truth4-p)))))
             (local (defthm stype-when-ctype-input
                      (implies (equal 0 (stype-count :reg aignet))
                               (equal (equal (ctype (stype (car aignet))) :input)
                                      (equal (stype (car aignet)) :pi)))
                      :hints(("Goal" :in-theory (enable ctype))))))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        truth4arr)
       (type (id->type n aignet))
       (truth4arr
        (aignet-case type
          :in (b* ((truth (truth::var4 (ci-id->ionum n aignet))))
                (set-truth4 n truth truth4arr))
          :gate (b* ((lit0 (gate-id->fanin0 n aignet))
                     (lit1 (gate-id->fanin1 n aignet)))
                  (set-truth4 n (if (eql 1 (id->regp n aignet))
                                    (logxor (truth::lit-truth lit0 truth4arr)
                                            (truth::lit-truth lit1 truth4arr))
                                  (logand (truth::lit-truth lit0 truth4arr)
                                          (truth::lit-truth lit1 truth4arr)))
                              truth4arr))
          :const (set-truth4 n 0 truth4arr))))
    (aignet-derive-truth4s (1+ (lnfix n)) aignet truth4arr))
  ///
  (local (defun-sk truths-ok (n truth4arr aignet invals regvals)
           (forall id
                   (implies (< (nfix id) (nfix n))
                            (equal (id-eval id invals regvals aignet)
                                   (bool->bit (truth::truth-eval
                                               (nth id truth4arr)
                                               (truth4-env-from-aignet-invals invals) 4)))))
           :rewrite :direct))
  (local (in-theory (disable truths-ok)))

  (local (defthm truth-eval-of-minus-bit
           (implies (bitp x)
                    (equal (truth::truth-eval (- x) env numvars)
                           (acl2::bit->bool x)))
           :hints(("Goal" :in-theory (enable truth::truth-eval)))))

  (local (in-theory (e/d* (acl2::arith-equiv-forwarding)
                          (acl2::nfix-equal-to-nonzero))))

  (local (defret truths-ok-of-aignet-derive-truth4s
           (implies (and (truths-ok n truth4arr aignet invals regvals)
                         (equal (stype-count :reg aignet) 0)
                         (<= (stype-count :pi aignet) 4))
                    (truths-ok (+ 1 (fanin-count aignet))
                               new-truth4arr aignet invals regvals))
           :hints (("goal" :induct <call> :expand (<call>) :in-theory (enable xor))
                   (and stable-under-simplificationp
                        (let ((lit (assoc 'truths-ok clause)))
                          (and lit
                               `(:expand (,lit)))))
                   (and stable-under-simplificationp
                        '(:expand ((id-eval n invals regvals aignet))
                          :in-theory (enable eval-and-of-lits eval-xor-of-lits lit-eval))))))

  (local (defthm truths-ok-of-0
           (truths-ok 0 truth4arr aignet invals regvals)
           :hints(("Goal" :in-theory (enable truths-ok)))))

  (defret truth4arr-length-of-aignet-derive-truth4s
    (implies (<= (num-fanins aignet) (len truth4arr))
             (equal (len new-truth4arr) (len truth4arr))))

  (defthmd aignet-derive-truth4s-correct
    (b* ((new-truth4arr (aignet-derive-truth4s 0 aignet truth4arr)))
      (implies (and (equal (stype-count :reg aignet) 0)
                    (<= (stype-count :pi aignet) 4)
                    (< (nfix id) (num-fanins aignet)))
             (equal (acl2::bit->bool (id-eval id invals regvals aignet))
                    (truth::truth-eval
                     (nth id new-truth4arr)
                     (truth4-env-from-aignet-invals invals)
                     4))))
    :hints (("goal" :use ((:instance truths-ok-of-aignet-derive-truth4s
                           (n 0)))
             :in-theory (disable truths-ok-of-aignet-derive-truth4s)))))

(fty::defmap truthmap :key-type truth::truth4 :val-type lit-listp)

(define aignet-truthmap-p ((x truthmap-p) aignet)
  (if (atom x)
      t
    (if (mbt (and (consp (car x))
                  (truth::truth4-p (caar x))))
        (and (aignet-lit-listp (cdar x) aignet)
             (aignet-truthmap-p (cdr x) aignet))
      (aignet-truthmap-p (cdr x) aignet)))
  ///
  (defthm aignet-lit-listp-of-aignet-truthmap-lookup
    (implies (and (aignet-truthmap-p x aignet)
                  (truth::truth4-p k))
             (aignet-lit-listp (cdr (hons-assoc-equal k x)) aignet))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm aignet-lit-listp-of-aignet-truthmap-lookup-when-truthmap-p
    (implies (and (aignet-truthmap-p x aignet)
                  (truthmap-p x))
             (aignet-lit-listp (cdr (hons-assoc-equal k x)) aignet))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (local (defthm truthmap-fix-when-first-bad
           (implies (and (consp x)
                         (not (and (consp (car x))
                                   (truth::truth4-p (caar x)))))
                    (equal (truthmap-fix x)
                           (truthmap-fix (cdr x))))
           :hints(("Goal" :in-theory (enable truthmap-fix)))))

  (defthm aignet-truthmap-p-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-truthmap-p x orig))
             (aignet-truthmap-p x new)))

  (defthm aignet-truthmap-p-of-nil
    (aignet-truthmap-p nil aignet))

  (local (in-theory (disable (:d aignet-truthmap-p)))))

(local (defthm truth-norm-lognot-truth-norm
         (equal (truth-norm (lognot (truth-norm x numvars)) numvars)
                (truth-norm (lognot x) numvars))
         :hints(("Goal" :in-theory (enable truth-norm)))))

(define aignet-lit-list-collect-truthmap ((x lit-listp)
                                          (truth4arr)
                                          (truthmap-acc truthmap-p))
  :returns (truthmap truthmap-p)
  (b* ((truthmap-acc (truthmap-fix truthmap-acc))
       ((when (atom x)) truthmap-acc)
       (lit (lit-fix (car x)))
       ((when (<= (truth4s-length truth4arr) (lit-id lit)))
        (raise "Literal out of bounds of truth4arr~%")
        (aignet-lit-list-collect-truthmap (cdr x) truth4arr truthmap-acc))
       (truth (truth::lit-truth lit truth4arr))
       (truthmap-acc (hons-acons truth (cons lit
                                             (cdr (hons-get truth truthmap-acc)))
                                 truthmap-acc))
       (ntruth (truth::truth-norm4 (lognot truth)))
       (truthmap-acc (hons-acons ntruth (cons (lit-negate lit)
                                              (cdr (hons-get ntruth truthmap-acc)))
                                 truthmap-acc)))
    (aignet-lit-list-collect-truthmap (cdr x) truth4arr truthmap-acc))
  ///
  (local (defthm truth-norm-of-lognot-not-equal
           (not (equal (truth::truth-norm (lognot x) numvars)
                       (truth::truth-norm x numvars)))
           :hints(("Goal" :in-theory (enable truth::truth-norm)
                   :expand ((:free (x) (loghead (ash 1 (nfix numvars)) x)))))))

  (local (defthm no-outputs-when-no-outputs
           (implies (and (equal (stype-count :po aignet) 0)
                         (equal (stype-count :nxst aignet) 0))
                    (not (equal (ctype (stype (car (lookup-id n aignet)))) :output)))
           :hints(("Goal" :in-theory (enable lookup-id stype-count)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable ctype))))))
  ;; (local (defthm aignet-litp-when-no-outs
  ;;          (implies (and (equal (stype-count :po aignet) 0)
  ;;                        (equal (stype-count :nxst aignet) 0))
  ;;                   (iff (aignet-litp lit aignet)
  ;;                        (< (lit-id lit) (num-fanins aignet))))
  ;;          :hints(("Goal" :in-theory (enable aignet-p)))))

  (defret aignet-truthmap-p-of-aignet-lit-list-collect-truthmap
    (implies (and (equal (num-fanins aignet) (truth4s-length truth4arr))
                  (equal (num-outs aignet) 0)
                  (equal (num-nxsts aignet) 0)
                  (aignet-truthmap-p truthmap-acc aignet))
             (aignet-truthmap-p truthmap aignet))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((:free (a b) (aignet-truthmap-p (cons a b) aignet)))
                   :in-theory (enable aignet-idp)))))

  (defretd aignet-lit-list-collect-truthmap-correct
    (implies (and (member lit (cdr (hons-assoc-equal truth (truthmap-fix truthmap))))
                  (not (member lit (cdr (hons-assoc-equal truth (truthmap-fix truthmap-acc))))))
             (truth::truth4-equiv (nth (lit-id lit) truth4arr)
                                  (if (eql (lit-neg lit) 1)
                                      (truth::truth-norm (lognot truth) 4)
                                    truth)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (local (defthm ash-gte-loghead
           (< (loghead n x) (ash 1 (nfix n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  ;; (local (defthm truth-eval-when-equal-truth-norm-lognot
  ;;          (implies (equal (truth::truth-norm (lognot x) nvars) (truth::truth-norm y nvars))
  ;;                   (equal (truth::truth-eval x env nvars)
  ;;                          (not (truth::truth-eval y env nvars))))
  ;;          :hints(("Goal" :use ((:instance truth::truth-eval-of-truth-norm
  ;;                                (truth (lognot x)) (numvars nvars) (env env))
  ;;                               (:instance truth::truth-eval-of-truth-norm
  ;;                                (truth y) (numvars nvars) (env env)))
  ;;                  :in-theory (disable truth::truth-eval-of-truth-norm)))))

  (local (defthm truth-eval-normalize-truth-norm
           (implies (and (equal y (truth::truth-norm x nvars))
                         (bind-free
                          (case-match y
                            (('truth::truth-norm yy &) `((yy . ,yy)))
                            (& `((yy . y))))
                          (yy))
                         (syntaxp (not (equal yy x)))
                         (equal (truth::truth-norm yy nvars) y))
                    (equal (truth::truth-eval x env nvars)
                           (truth::truth-eval yy env nvars)))
         :hints(("Goal" :use ((:instance truth::truth-eval-of-truth-norm
                               (truth x) (numvars nvars) (env env))
                              (:instance truth::truth-eval-of-truth-norm
                               (truth yy) (numvars nvars) (env env)))
                   :in-theory (disable truth::truth-eval-of-truth-norm)))))

  ;; (local (in-theory (disable truth::truth-eval-of-lognot)))

  (local (defthmd aignet-litp-member-of-aignet-lit-list
           (implies (and (aignet-lit-listp x aignet)
                         (member lit x))
                    (aignet-litp lit aignet))
           :hints(("Goal" :in-theory (enable aignet-lit-listp)))))

  (defthmd aignet-lit-list-collect-truthmap-of-aignet-derive-truth4s
    (b* ((truth4arr (aignet-derive-truth4s 0 aignet truth4arr-orig))
         (truthmap (aignet-lit-list-collect-truthmap x truth4arr nil)))
      (implies (and (member lit (cdr (hons-assoc-equal truth truthmap)))
                    (equal (stype-count :reg aignet) 0)
                    (equal (stype-count :po aignet) 0)
                    (equal (stype-count :nxst aignet) 0)
                    (<= (stype-count :pi aignet) 4)
                    (equal (len truth4arr-orig) (num-fanins aignet)))
               (equal (truth::truth-eval truth
                                         (truth4-env-from-aignet-invals invals)
                                         4)
                      (acl2::bit->bool (lit-eval lit invals regvals aignet)))))
    :hints (("goal" :use ((:instance aignet-lit-list-collect-truthmap-correct
                           (truthmap-acc nil) (truth4arr (aignet-derive-truth4s 0 aignet truth4arr-orig)))
                          (:instance aignet-derive-truth4s-correct
                           (truth4arr truth4arr-orig)
                           (id (lit-id lit)))
                          (:instance aignet-litp-member-of-aignet-lit-list
                           (x (cdr (hons-assoc-equal truth (aignet-lit-list-collect-truthmap
                                                            x (aignet-derive-truth4s 0 aignet truth4arr-orig)
                                                            nil))))))
             :expand ((lit-eval lit invals regvals aignet))
             :in-theory (enable hons-assoc-equal aignet-idp)))))

(define smm-write-lit ((block natp)
                       (idx natp)
                       (lit litp)
                       (smm))
  :guard (and (< block (smm-nblocks smm))
              (< idx (smm-block-size block smm)))
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  :enabled t
  (mbe :logic (smm-write block idx (lit-fix lit) smm)
       :exec (if (<= lit #xffffffff)
                 (smm-write block idx lit smm)
               (ec-call (smm-write block idx lit smm)))))

(define smm-write-lits ((block natp)
                        (idx natp)
                        (lits lit-listp)
                        (smm))
  :guard (and (< block (smm-nblocks smm))
              (<= (+ idx (len lits)) (smm-block-size block smm)))
  :prepwork ((local (defthm true-listp-when-u32-list-listp
                      (implies (acl2::u32-list-listp smm)
                               (true-listp smm))
                      :hints(("Goal" :in-theory (enable acl2::u32-list-listp))))))
  :returns (new-smm)
  (b* (((when (atom lits))
        (mbe :logic (non-exec (acl2::list-fix smm))
             :exec smm))
       (smm (smm-write-lit block idx (car lits) smm)))
    (smm-write-lits block (+ 1 (lnfix idx)) (cdr lits) smm))
  ///
  (defret read-diff-block-of-smm-write-lits
    (implies (not (equal (nfix block) (nfix n)))
             (equal (nth n new-smm)
                    (nth n smm))))

  (local (defret read-lesser-idx-of-smm-write-lits
           (implies (< (nfix n) (nfix idx))
                    (equal (nth n (nth block new-smm))
                           (nth n (nth block smm))))))

  (defret read-in-block-of-smm-write-lits
    (equal (nth n (nth block new-smm))
           (cond ((< (nfix n) (nfix idx)) (nth n (nth block smm)))
                 ((< (nfix n) (+ (nfix idx) (len lits)))
                  (lit-fix (nth (- (nfix n) (nfix idx)) lits)))
                 (t (nth n (nth block smm)))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((nth (+ n (- (nfix idx))) lits))))))

  (defret len-of-smm-write-lits
    (implies (< (nfix block) (len smm))
             (equal (len new-smm) (len smm))))

  (defret len-of-smm-write-lits-nondecreasing
    (<= (len smm) (len new-smm))
    :rule-classes :linear)

  (defret block-size-of-smm-write-lits
    (implies (<= (+ (nfix idx) (len lits)) (len (nth block smm)))
             (equal (len (nth block new-smm))
                    (len (nth block smm)))))

  ;; (local (include-book "std/lists/nth" :dir :system))

  ;; (defret true-listp-of-smm-write-lits
  ;;   (implies (true-listp smm)
  ;;            (true-listp new-smm)))

  ;; (defret block-of-smm-write-lits
  ;;   (implies (and (equal (len (nth block smm))
  ;;                        (len lits))
  ;;                 (< (nfix block) (len smm)))
  ;;            (equal (smm-write-lits block 0 lits smm)
  ;;                   (update-nth block (lit-list-fix lits)
  ;;                               (list-fix smm))))
  ;;   :hints (("goal" :do-not-induct t :in-theory (disable smm-write-lits))
  ;;           (and stable-under-simplificationp
  ;;                (acl2::equal-by-nths-hint))
  ;;           (and stable-under-simplificationp
  ;;                (acl2::equal-by-nths-hint))))
  )


(encapsulate nil
  (local (in-theory (enable hons-assoc-equal)))
  (fty::defmap nat-val-alistp :val-type natp :true-listp t))

;; Priorities: in abc src/opt/dar/darLib.c, pPriosMem is basically the same as
;; our abc-prios.  Each chunk (indexed by pPrios) is a permutation of indices
;; 0:n-1 which indicate the the ranking of outputs for a given truth value.  For example,
;; the first chunk of priodata (for truth index 1 of 222) is
;; 10  9  12  6  11  14  4  1  7  5  2  3  13  8  0
;; which means there are 15 outputs implementing that truth table,
;; and the "best" one is number 10, followed by 9, 12, etc.  We want to put the
;; outputs into our smm in that order.

(include-book "centaur/misc/numlist" :dir :system)
(include-book "defsort/defsort" :dir :system)

(define nat< ((x natp) (y natp))
  :inline t
  :enabled t
  (mbe :logic (< (nfix x) (nfix y))
       :exec (< x y)))

(acl2::defsort sort-nats
  :prefix natsort
  :compare< nat<
  :comparablep natp
  :comparable-listp nat-listp
  :true-listp t
  :weak nil)


(define lits-to-litarr-aux ((idx natp)
                            (lits lit-listp)
                            (litarr))
  :enabled t
  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (include-book "std/lists/len" :dir :system))
             (local (include-book "std/lists/nthcdr" :dir :system))
             (local (defthm litarr$ap-is-lit-listp
                      (equal (litarr$ap x)
                             (lit-listp x))))
             (local (defthm take-of-update-last
                      (implies (equal (nfix idx) (+ 1 (nfix last)))
                               (equal (take idx (update-nth last val x))
                                      (append (take last x)
                                              (list val))))
                      :hints(("Goal" :in-theory (enable update-nth)))))
             (local (defthm nthcdr-of-update-nth
                      (implies (< (nfix m) (nfix n))
                               (equal (nthcdr n (update-nth m val x))
                                      (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable update-nth))))))
  :guard (<= (+ idx (len lits)) (lits-length litarr))
  :returns (new-litarr)
  :guard-hints (("goal" :in-theory (e/d (update-nth-lit)
                                        (satlink::lit-list-fix-of-append
                                         ;; acl2::nthcdr-of-cdr
                                         acl2::open-small-nthcdr
                                         acl2::nthcdr-when-zp
                                         acl2::nthcdr-of-cdr)))
                (and stable-under-simplificationp
                     '(:expand (;; (:free (litarr) (take idx litarr))
                                (update-nth idx (car lits) litarr)
                                (:free (n litarr) (lits-to-litarr-aux n (cdr lits) litarr)))))
                )
  (mbe :logic (non-exec (lit-list-fix (append (take idx litarr)
                                              lits
                                              (nthcdr (+ (nfix idx) (len lits)) litarr))))
       :exec (if (atom lits)
                 litarr
               (b* ((litarr (set-lit idx (lit-fix (car lits)) litarr)))
                 (lits-to-litarr-aux (1+ (lnfix idx)) (cdr lits) litarr)))))


(define lits-to-litarr ((lits lit-listp)
                        (litarr))
  :prepwork ((local (defthm nthcdr-of-resize-list
                      (equal (nthcdr n (resize-list list n val)) nil)
                      :hints(("Goal" :in-theory (enable nthcdr resize-list)))))
             (local (defthm len-of-resize-list
                      (equal (len (resize-list list n val)) (nfix n))
                      :hints(("Goal" :in-theory (enable resize-list))))))
  :enabled t
  (mbe :logic (non-exec (lit-list-fix lits))
       :exec
       (b* ((litarr (resize-lits (len lits) litarr)))
         (lits-to-litarr-aux 0 lits litarr))))

(define nat-list-max ((x nat-listp))
  ;; BOZO this is the same as max-nats from vl/util/sum-nats.lisp and nat-list-max from sv/mods/moddb.lisp
  :returns (max natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (lnfix (car x))
         (nat-list-max (cdr x))))
  ///
  (defret nat-list-max-of-numlist
    (implies (natp n)
             (equal (nat-list-max (acl2::numlist n 1 len))
                    (if (zp len) 0 (+ -1 n len)))))

  (defret nat-list-max-of-natsort-insert
    (equal (nat-list-max (natsort-insert elt x))
           (max (nfix elt) (nat-list-max x)))
    :hints(("Goal" :in-theory (enable natsort-insert))))

  (defret nat-list-max-of-natsort-insertsort
    (equal (nat-list-max (natsort-insertsort x))
           (nat-list-max x))
    :hints(("Goal" :in-theory (enable natsort-insertsort)))))

(define reorder-lits-by-prios-aux ((prios nat-listp)
                                   (litarr))
  :guard (< (nat-list-max prios) (lits-length litarr))
  :guard-hints (("goal" :in-theory (enable nat-list-max)))
  :returns (lits lit-listp)
  (if (atom prios)
      nil
    (cons (get-lit (car prios) litarr)
          (reorder-lits-by-prios-aux (cdr prios) litarr)))
  ///
  (defret len-of-reorder-lits-by-prios-aux
    (equal (len lits) (len prios)))

  (local (defthm member-nth-lit
           (implies (< (nfix n) (len x))
                    (member (nth-lit n x) (lit-list-fix x)))
           :hints(("Goal" :in-theory (enable nth-lit nth)))))

  ;; (defretd member-of-reorder-lits-by-prios-aux
  ;;   (implies (and (not (member x (lit-list-fix litarr)))
  ;;                 (< (nat-list-max prios) (lits-length litarr)))
  ;;            (not (member x lits)))
  ;;   :hints(("Goal" :in-theory (enable nat-list-max))))

  (defret nth-of-reorder-lits-by-prios-aux
    (implies (< (nfix n) (len prios))
             (equal (nth n lits)
                    (nth-lit (nth n prios) litarr)))
    :hints (("goal" :induct (nth n prios)
             :expand ((reorder-lits-by-prios-aux prios litarr))
             :in-theory (enable nth)))))

(define reorder-lits-by-prios ((prios nat-listp)
                               (lits lit-listp))
  :guard (< (nat-list-max prios) (len lits))
  :returns (new-lits lit-listp)
  (b* (((local-stobjs litarr) (mv litarr new-lits))
       (litarr (lits-to-litarr lits litarr))
       (new-lits
        (reorder-lits-by-prios-aux prios litarr)))
    (mv litarr new-lits))
  ///
  (defret len-of-reorder-lits-by-prios
    (equal (len new-lits) (len prios)))

  ;; (defretd member-of-reorder-lits-by-prios
  ;;   (implies (and (not (member x (lit-list-fix lits)))
  ;;                 (< (nat-list-max prios) (len lits)))
  ;;            (not (member x new-lits)))
  ;;   :hints(("Goal" :in-theory (enable member-of-reorder-lits-by-prios-aux))))

  ;; (defret member-nth-of-reorder-lits-by-prios
  ;;   (implies (and (< (nfix n) (len prios))
  ;;                 (< (nat-list-max prios) (len lits))
  ;;                 (lit-listp lits))
  ;;            (member (nth n new-lits) lits))
  ;;   :hints (("goal" :use ((:instance member-of-reorder-lits-by-prios
  ;;                          (x (nth n new-lits))))
  ;;            :in-theory (disable reorder-lits-by-prios))))

  (defret nth-of-reorder-lits-by-prios
    (implies (< (nfix n) (len prios))
             (equal (nth n new-lits)
                    (lit-fix (nth (nth n prios) (lit-list-fix lits)))))
    :hints(("Goal" :in-theory (enable nth-lit)))))


(define prios-are-permutation ((prios))
  :returns (permp)
  (b* ((len (len prios)))
    (and (nat-listp prios)
         (equal (sort-nats prios) (acl2::numlist 0 1 len))))
  ///
  (defret nat-listp-when-prios-are-permutation
    (implies permp (nat-listp prios))
    :rule-classes :forward-chaining)

  (local (defthm nat-list-max-when-sort-equals-numlist
           (implies (equal (natsort-insertsort x) (acl2::numlist 0 1 len))
                    (equal (nat-list-max x)
                           (if (zp len) 0 (+ -1 len))))
           :hints(("Goal" :use ((:instance nat-list-max-of-natsort-insertsort))
                   :in-theory (disable nat-list-max-of-natsort-insertsort acl2::numlist)))))

  (defretd nat-list-max-when-prios-are-permutation
    (implies (and permp (consp prios))
             (equal (nat-list-max prios) (+ -1 (len prios))))
    :hints(("Goal" :in-theory (disable acl2::numlist)))))

(define lits-max-id ((x lit-listp))
  :returns (max natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (lit-id (car x))
         (lits-max-id (cdr x))))
  ///
  (defret lit-id-lte-max-id
    (implies (member (lit-fix lit) (lit-list-fix x))
             (<= (lit-id lit) (lits-max-id x)))
    :rule-classes (:rewrite (:linear :trigger-terms ((lits-max-id x))))))


(define remove-lits-with-duplicate-ids-aux ((bitarr)
                                   (x lit-listp))
  :guard (<= (+ 1 (lits-max-id x)) (bits-length bitarr))
  :returns (mv new-bitarr (new-x lit-listp))
  :guard-hints (("goal" :expand ((lits-max-id x))))
  (b* (((when (atom x)) (mv bitarr nil))
       ((when (eql 1 (get-bit (lit-id (car x)) bitarr)))
        (remove-lits-with-duplicate-ids-aux bitarr (cdr x)))
       ((mv bitarr rest) (remove-lits-with-duplicate-ids-aux bitarr (cdr x))))
    (mv bitarr (cons (lit-fix (car x)) rest)))
  ///
  (defret member-of-remove-lits-with-duplicate-ids-aux
    (implies (not (member lit (lit-list-fix x)))
             (not (member lit new-x)))))

(define remove-lits-with-duplicate-ids ((x lit-listp))
  :returns (new-x lit-listp)
  (b* (((acl2::local-stobjs bitarr)
        (mv bitarr new-x))
       (bitarr (resize-bits (+ 1 (lits-max-id x)) bitarr)))
    (remove-lits-with-duplicate-ids-aux bitarr x))
  ///
  (defret member-of-remove-lits-with-duplicate-ids
    (implies (not (member lit (lit-list-fix x)))
             (not (member lit new-x)))))

(local (include-book "std/lists/index-of" :dir :system))

(local
 (define remove-lits-with-duplicate-ids-index ((k natp) (x lit-listp))
   :returns (index)
   :verify-guards nil
   (b* ((new-x (remove-lits-with-duplicate-ids x))
        (elt (nth k new-x)))
     (acl2::index-of elt (lit-list-fix x)))
   ///
   (defret nth-of-remove-lits-with-duplicate-ids
     (implies (< (nfix k) (len (remove-lits-with-duplicate-ids x)))
              (equal (nth k (remove-lits-with-duplicate-ids x))
                     (nth index (lit-list-fix x))))
     :hints (("goal" :use ((:instance member-of-remove-lits-with-duplicate-ids
                            (lit (nth k (remove-lits-with-duplicate-ids x)))))
              :in-theory (disable member-of-remove-lits-with-duplicate-ids))))

   (defret remove-lits-with-duplicate-ids-index-bound
     (implies (< (nfix k) (len (remove-lits-with-duplicate-ids x)))
              (< index (len x)))
     :hints (("goal" :use ((:instance member-of-remove-lits-with-duplicate-ids
                            (lit (nth k (remove-lits-with-duplicate-ids x)))))
              :in-theory (disable member-of-remove-lits-with-duplicate-ids
                                  nth-of-remove-lits-with-duplicate-ids)))
     :rule-classes (:rewrite :linear))

   (defret remove-lits-with-duplicate-ids-index-natp
     (implies (< (nfix k) (len (remove-lits-with-duplicate-ids x)))
              (natp index))
     :hints (("goal" :use ((:instance member-of-remove-lits-with-duplicate-ids
                            (lit (nth k (remove-lits-with-duplicate-ids x)))))
              :in-theory (disable member-of-remove-lits-with-duplicate-ids
                                  nth-of-remove-lits-with-duplicate-ids)))
     :rule-classes (:rewrite :type-prescription))))



(define truthmap-to-smm ((truthmap truthmap-p)
                         (truth4arr)
                         (priodata nat-listp)
                         (smm))
  :guard (<= (smm-nblocks smm) (truth4s-length truth4arr))
  :measure (nfix (- (truth4s-length truth4arr) (acl2::smm-nblocks smm)))
  :returns (new-smm)
  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (defthm nat-listp-of-nthcdr
                      (implies (nat-listp x)
                               (nat-listp (nthcdr n x)))))
             (local (defthm lit-listp-of-rev
                      (implies (lit-listp x)
                               (lit-listp (acl2::rev x)))
                      :hints(("Goal" :in-theory (enable acl2::rev)))))
             (local (in-theory (enable nat-list-max-when-prios-are-permutation))))
  (b* ((n (acl2::smm-nblocks smm))
       ((when (mbe :logic (zp (- (truth4s-length truth4arr) n))
                   :exec (eql (truth4s-length truth4arr) n)))
        smm)
       (lits (cdr (hons-get (get-truth4 n truth4arr) (truthmap-fix truthmap))))
       (len (len lits))
       ((when (eql len 0))
        (b* ((smm (acl2::smm-addblock 0 smm)))
          (truthmap-to-smm truthmap truth4arr priodata smm)))
       (prios (take len priodata))
       (prios-ok (prios-are-permutation prios))
       (- (and (not prios-ok)
               (raise "Bad priorities for block ~x0: ~x1~%"
                      n prios)))
       (lits (if prios-ok
                 ;; Lits are reversed when we collect them in the truthmap!!
                 (reorder-lits-by-prios prios (acl2::rev lits))
               lits))
       (lits (remove-lits-with-duplicate-ids lits))
       (smm (acl2::smm-addblock (len lits) smm))
       (smm (smm-write-lits n 0 lits smm)))
    (truthmap-to-smm truthmap truth4arr (nthcdr len priodata) smm))
  ///
  (defret nblocks-of-truthmap-to-smm
    (implies (<= (len smm) (len truth4arr))
             (equal (len new-smm) (len truth4arr))))

  (local (defret nth-of-truthmap-to-smm
           (implies (< (nfix n) (len smm))
                    (equal (nth n new-smm) (nth n smm)))))

  (local (in-theory (disable acl2::nth-of-append)))

  (local (defthm my-nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))
           :hints (("goal" :use ((:instance acl2::nth-of-append
                                  (n (nfix n)) (x x) (y y)))
                    :do-not-induct t))))

  (local (defthm litp-nth-of-lit-list
           (implies (and (lit-listp x)
                         (< (nfix n) (len x)))
                    (litp (nth n x)))
           :hints(("Goal" :in-theory (enable lit-listp nth)))))

  (local (in-theory (disable acl2::nth-of-take)))


  (local (defthmd nth-bounded-by-nat-list-max
           (implies (and (< (nfix n) (len x)))
                    (<= (nfix (nth n x)) (nat-list-max x)))
           :hints(("Goal" :in-theory (enable nth nat-list-max)))))

  (local (defthm nth-bounded-by-nat-list-max-special
           (implies (< (nfix n) (nfix m))
                    (<= (nfix (nth n (take m x))) (nat-list-max (take m x))))
           :hints(("Goal" :in-theory (enable nth-bounded-by-nat-list-max)))
           :rule-classes :linear))

  (local (in-theory (disable acl2::inequality-with-nfix-hyp-2)))

  (defret member-lit-of-truthmap-to-smm
    (implies (and (<= (smm-nblocks smm) (nfix n))
                  (< (nfix n) (smm-nblocks new-smm))
                  (< (nfix k) (smm-block-size n new-smm))
                  (truthmap-p truthmap))
             (member (nth k (nth n new-smm))
                     (cdr (hons-assoc-equal (truth::truth-norm (nth n truth4arr) 4) truthmap))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthm aignet-litp-nth-of-aignet-lit-list
           (implies (and (aignet-lit-listp x aignet)
                         (< (nfix n) (len x)))
                    (aignet-litp (nth n x) aignet))
           :hints(("Goal" :in-theory (enable aignet-lit-listp nth)))))

  (defret aignet-litp-of-truthmap-to-smm-lookup
    (implies (and (aignet-truthmap-p truthmap aignet)
                  (<= (smm-nblocks smm) (nfix n))
                  (< (nfix n) (smm-nblocks new-smm))
                  (< (nfix k) (smm-block-size n new-smm)))
             (aignet-litp (nth k (nth n new-smm)) aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))





(defstobj-clone truth4arr2 truth::truth4arr :strsubst (("a" . "a")) :suffix "2")
(defstobj-clone npn4arr truth::npn4arr :strsubst (("a" . "a")))


(define map-ids ((x nat-listp) copy)
  :returns (lits lit-listp)
  (if (atom x)
      nil
    (cons (b* ((id (lnfix (car x))))
            (if (< id (lits-length copy))
                (get-lit id copy)
              (prog2$ (raise "ID out of bounds for map-ids") 0)))
          (map-ids (cdr x) copy)))
  ///
  (defret aignet-lit-listp-of-map-ids
    (implies (aignet-copies-in-bounds copy aignet)
             (aignet-lit-listp lits aignet))))


(define setup-abc-rwlib (npn4arr
                         truth4arr
                         aignet
                         smm) ;; all emptied
  :returns (mv new-npn4arr
               new-truth4arr
               new-smm
               new-aignet)
  (b* (((mv ?count npn4arr truth4arr) (truth::record-all-npn4-perms-top npn4arr truth4arr))
       ((acl2::local-stobjs copy)
        (mv copy npn4arr truth4arr smm aignet))
       ((mv copy aignet) (aignet-build-abc-top copy aignet))
       (smm (smm-clear smm))
       ((acl2::local-stobjs truth4arr2)
        (mv copy npn4arr truth4arr smm aignet truth4arr2))
       (truth4arr2 (resize-truth4s (num-fanins aignet) truth4arr2))
       (truth4arr2 (aignet-derive-truth4s 0 aignet truth4arr2))
       ;; cons 0 to include the constant-0 node in the outputs
       (truthmap (aignet-lit-list-collect-truthmap (cons 0 (map-ids (abc-outs) copy)) truth4arr2 nil))
       (smm (truthmap-to-smm truthmap truth4arr (cons 0 (abc-prios)) smm)))
    (fast-alist-free truthmap)
    (mv copy npn4arr truth4arr smm aignet truth4arr2))
  ///
  (local (include-book "std/lists/resize-list" :dir :system))
  (local (in-theory (disable resize-list)))

  (defret npn4arr-length-of-setup-abc-rwlib
    (equal (len new-npn4arr) #x10000))

  (defret npn4arr-indices-bounded-of-setup-abc-rwlib
    (truth::npn4arr-indices-bounded (len new-smm) new-npn4arr)
    :hints (("goal" :use ((:instance truth::npn4arr-indices-bounded-of-record-all-npn4-perms-top
                           (npn4arr npn4arr) (truth4arr truth4arr)))
             :in-theory (disable truth::npn4arr-indices-bounded-of-record-all-npn4-perms-top))))

  (defret npn4arr-correct-of-setup-abc-rwlib
    (truth::npn4arr-correct new-npn4arr new-truth4arr))

  (defret num-ins-of-setup-abc-rwlib-aignet
    (equal (stype-count :pi new-aignet) 4))

  (defret num-regs-of-setup-abc-rwlib-aignet
    (equal (stype-count :reg new-aignet) 0))

  (defret aignet-litp-smm-lookup-of-setup-abc-rwlib
    (implies (and (< (nfix n) (len new-smm))
                  (< (nfix idx) (len (nth n new-smm))))
             (aignet-litp (nth idx (nth n new-smm)) new-aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret smm-contains-aignet-lits-of-setup-abc-rwlib
    (smm-contains-aignet-lits new-smm new-aignet)
    :hints (("goal" :in-theory (e/d (smm-contains-aignet-lits) (setup-abc-rwlib)))))

  (defret truth4arr-length-of-setup-abc-rwlib
    (<= (len new-smm) (len new-truth4arr))
    :rule-classes :linear)

  (defret eval-smm-lookup-of-setup-abc-rwlib
    (implies (and (< (nfix n) (len new-smm))
                  (< (nfix idx) (len (nth n new-smm))))
             (equal (lit-eval (nth idx (nth n new-smm)) invals regvals new-aignet)
                    (bool->bit (truth::truth-eval (nth n new-truth4arr)
                                                  (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                    (member-lit-of-truthmap-to-smm)))
           (acl2::use-termhint
            (b* (((mv ?count ?npn4arr truth4arr) (truth::record-all-npn4-perms-top npn4arr truth4arr))
                 (copy (create-litarr))
                 ((mv copy aignet) (aignet-build-abc-top copy aignet))
                 (smm-orig (smm-clear smm))
                 (truth4arr2-orig (resize-truth4s (num-fanins aignet) (create-truth4arr)))
                 (truth4arr2 (aignet-derive-truth4s 0 aignet truth4arr2-orig))
                 (outs (cons 0 (map-ids (abc-outs) copy)))
                 (prios (cons 0 (abc-prios)))
                 (truthmap (aignet-lit-list-collect-truthmap outs truth4arr2 nil))
                 (smm (truthmap-to-smm truthmap truth4arr prios smm-orig))
                 (lit (nth idx (nth n smm))))
              `'(:use ((:instance aignet-lit-list-collect-truthmap-of-aignet-derive-truth4s
                        (lit ,(hq lit))
                        (truth4arr-orig ,(hq truth4arr2-orig))
                        (aignet ,(hq aignet))
                        (x ,(hq outs))
                        (truth ,(hq (truth::truth-norm (nth n truth4arr) 4))))
                       (:instance member-lit-of-truthmap-to-smm
                        (k idx)
                        (truthmap ,(hq truthmap))
                        (truth4arr ,(hq truth4arr))
                        (priodata ,(hq prios))
                        (smm ,(hq smm-orig)))))))))

  (defret aignet-truth-impls-correct-of-setup-abc-rwlib
    (aignet-truth-impls-correct new-smm new-aignet new-truth4arr)
    :hints(("Goal" :in-theory (e/d (aignet-truth-impls-correct)
                                   (setup-abc-rwlib)))))

  (defret npn4arr-indices-all-bound-of-setup-abc-rwlib
    (truth::npn4arr-indices-all-bound new-npn4arr)))

(define rwlib-init-abc (rwlib)
  :returns (initialized-rwlib)
  (b* (((acl2::stobj-get npn4arr truth4arr smm aignet)
        ((npn4arr (rwlib->npns rwlib))
         (truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib)))
        (setup-abc-rwlib npn4arr truth4arr aignet smm)))
    rwlib)
  ///
  (local (in-theory (enable rwlib->npns
                            rwlib->cands
                            rwlib->aigs
                            rwlib->truths)))

  (defret rwlib-wfp-of-rwlib-init-abc
    (rwlib-wfp initialized-rwlib)
    :hints(("Goal" :in-theory (enable rwlib-wfp))))

  (defret rwlib-correct-of-rwlib-init-abc
    (rwlib-correct initialized-rwlib)
    :hints(("Goal" :in-theory (enable rwlib-correct)))))
