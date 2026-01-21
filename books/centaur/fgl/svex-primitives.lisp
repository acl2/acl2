; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "centaur/sv/svex/symbolic" :dir :system)
(include-book "bfr-arithmetic")
(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "def-fgl-rewrite")
(include-book "bitops")
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))




(encapsulate nil
  
  (local
   (encapsulate nil
     (local (in-theory (disable sv::svex-fix-redef)))
     (flag::make-flag sv::svex-fix-flag sv::svex-fix$inline
                      :hints (("goal" :expand ((sv::svex-kind x))))
                      :defthm-macro-name defthm-svex-fix-flag-local
                      :expand-with-original-defs t)))

  (def-formula-checks svex-formula-checks
    (sv::4vmask-to-a4vec-rec-env
     sv::4vec-from-bitlist
     sv::svex-varmasks/env->aig-env-rec)))

(define fgl-4vmask-to-a4vec-rec-env ((mask sv::4vmask-p)
                                     (boolmask integerp)
                                     (upper true-listp) ;; bfr-list
                                     (lower true-listp) ;; bfr-list
                                     (nextvar natp))
  :returns (aig-env fgl-object-alist-p)
  :guard (not (bitops::sparseint-< mask 0))
  :measure (bitops::sparseint-length (sv::sparseint-nfix mask))
  :hints(("Goal" :in-theory (enable sv::4vmask-fix)
          :expand ((integer-length (bitops::sparseint-val mask)))))
  (b* ((mask (sv::sparseint-nfix (sv::4vmask-fix mask)))
       (nextvar (lnfix nextvar))
       ((when (bitops::sparseint-equal mask 0)) nil)
       (rest-env
        (fgl-4vmask-to-a4vec-rec-env (bitops::sparseint-rightshift 1 mask)
                                     (logcdr boolmask)
                                     (scdr upper)
                                     (scdr lower)
                                 (if (eql 1 (bitops::sparseint-bit 0 mask))
                                     (if (logbitp 0 boolmask)
                                         (+ 1 nextvar)
                                       (+ 2 nextvar))
                                   nextvar))))
    (if (eql 1 (bitops::sparseint-bit 0 mask))
        (cons (cons nextvar (g-boolean (car upper)))
              (if (logbitp 0 boolmask)
                  rest-env
                (cons (cons (1+ nextvar) (g-boolean (car lower)))
                      rest-env)))
      rest-env))
  ///
  (local (defthmd gobj-bfr-list-eval-expand
           (equal (bools->int (gobj-bfr-list-eval x env))
                  (intcons (gobj-bfr-eval (car x) env)
                           (bools->int (gobj-bfr-list-eval (scdr x) env))))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval
                                             scdr
                                             bools->int
                                             bool->bit)
                   :do-not-induct t))
           :otf-flg t
           :rule-classes ((:definition :install-body nil :controller-alist ((bools->int t))))))

  (defret eval-of-<fn>
    (equal (fgl-object-alist-eval aig-env env)
           (sv::4vmask-to-a4vec-rec-env mask
                                    boolmask
                                    (bools->int (gobj-bfr-list-eval upper env))
                                    (bools->int (gobj-bfr-list-eval lower env))
                                    nextvar))
    :hints (("goal" :induct <call>
             :expand ((:free (upper lower) (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
                      (:with gobj-bfr-list-eval-expand (bools->int (gobj-bfr-list-eval upper env)))
                      (:with gobj-bfr-list-eval-expand (bools->int (gobj-bfr-list-eval lower env)))))))


  (local (defthm bfr-listp-of-scdr
           (implies (bfr-listp x)
                    (bfr-listp (scdr x)))
           :hints(("Goal" :in-theory (enable scdr)))))
  
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-listp upper)
                  (bfr-listp lower))
             (bfr-listp (fgl-object-alist-bfrlist aig-env)))))


(defsection 4vmask-to-a4vec-rec-env-of-loghead-mask-len
  (local
   (defthm 4vmask-to-a4vec-rec-env-of-loghead-mask-len-upper-lemma
     (equal (sv::4vmask-to-a4vec-rec-env mask boolmask
                                         (loghead (bitops::sparseint-length (sv::sparseint-nfix (sv::4vmask-fix mask))) upper)
                                         lower
                                         nextvar)
            (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
     :hints(("Goal" :in-theory (enable (:i sv::4vmask-to-a4vec-rec-env))
             :induct (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)
             :expand ((:free (x) (LOGHEAD (+ 1 (INTEGER-LENGTH x)) UPPER))
                      (logbitp 0 upper)
                      (INTEGER-LENGTH (BITOPS::SPARSEINT-VAL (SV::4VMASK-FIX MASK)))
                      (:free (upper) (SV::4VMASK-TO-A4VEC-REC-ENV MASK BOOLMASK upper LOWER NEXTVAR)))))))

  (local
   (defthm 4vmask-to-a4vec-rec-env-of-loghead-mask-len-lower-lemma
     (equal (sv::4vmask-to-a4vec-rec-env mask boolmask
                                         upper
                                         (loghead (bitops::sparseint-length (sv::sparseint-nfix (sv::4vmask-fix mask))) lower)
                                         nextvar)
            (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar))
     :hints(("Goal" :in-theory (enable (:i sv::4vmask-to-a4vec-rec-env))
             :induct (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)
             :expand ((:free (x) (LOGHEAD (+ 1 (INTEGER-LENGTH x)) LOWER))
                      (logbitp 0 lower)
                      (INTEGER-LENGTH (BITOPS::SPARSEINT-VAL (SV::4VMASK-FIX MASK)))
                      (:free (lower) (SV::4VMASK-TO-A4VEC-REC-ENV MASK BOOLMASK upper LOWER NEXTVAR)))))))

  
  (defthm 4vmask-to-a4vec-rec-env-of-loghead-mask-len-upper
    (implies (<= (bitops::sparseint-length (sv::sparseint-nfix (sv::4vmask-fix mask))) (nfix len))
             (equal (sv::4vmask-to-a4vec-rec-env mask boolmask
                                                 (loghead len upper)
                                                 lower
                                                 nextvar)
                    (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)))
    :hints(("Goal" :use ((:instance 4vmask-to-a4vec-rec-env-of-loghead-mask-len-upper-lemma)
                         (:instance 4vmask-to-a4vec-rec-env-of-loghead-mask-len-upper-lemma
                          (upper (loghead len upper))))
            :in-theory (disable 4vmask-to-a4vec-rec-env-of-loghead-mask-len-upper-lemma))))

  (defthm 4vmask-to-a4vec-rec-env-of-loghead-mask-len-lower
    (implies (<= (bitops::sparseint-length (sv::sparseint-nfix (sv::4vmask-fix mask))) (nfix len))
             (equal (sv::4vmask-to-a4vec-rec-env mask boolmask
                                                 upper
                                                 (loghead len lower)
                                                 nextvar)
                    (sv::4vmask-to-a4vec-rec-env mask boolmask upper lower nextvar)))
    :hints(("Goal" :use ((:instance 4vmask-to-a4vec-rec-env-of-loghead-mask-len-lower-lemma)
                         (:instance 4vmask-to-a4vec-rec-env-of-loghead-mask-len-lower-lemma
                          (lower (loghead len lower))))
            :in-theory (disable 4vmask-to-a4vec-rec-env-of-loghead-mask-len-lower-lemma)))))

(define gen-unsigned-integer-bits ((n natp)
                                   (x fgl-object-p)
                                   (interp-st)
                                   (state))
  :returns (mv (bits true-listp) new-interp-st)
  :guard (interp-st-nvars-ok interp-st)
  (b* (((when (zp n)) (mv (list nil) interp-st))
       (x-arglist (hons x nil))
       (x0 (hons-copy (g-apply 'intcar x-arglist)))
       ((mv bit0 interp-st) (interp-st-add-term-bvar-unique x0 interp-st state))
       (xr (hons-copy (g-apply 'intcdr x-arglist)))
       ((mv bitsr interp-st) (gen-unsigned-integer-bits (1- n) xr interp-st state)))
    (mv (cons bit0 bitsr) interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (Equal (interp-st-field-fix key) :logicman))
                  (not (Equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$c (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$c (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))


  (local (defret bfr-nvars-of-interp-st-add-term-bvar-unique
           (<= (bfr-nvars (interp-st->logicman interp-st))
               (bfr-nvars (interp-st->logicman new-interp-st)))
           :hints(("Goal" :in-theory (enable <fn>)))
           :rule-classes :linear
           :fn interp-st-add-term-bvar-unique))

  (defret bfr-nvars-of-<fn>
    (>= (bfr-nvars (interp-st->logicman new-interp-st))
        (bfr-nvars (interp-st->logicman interp-st)))
    :rule-classes :linear)

  (local
   (defret base-bvar-of-<fn>
     (equal (base-bvar$c (interp-st->bvar-db new-interp-st))
            (base-bvar$c (interp-st->bvar-db interp-st)))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn interp-st-add-term-bvar-unique))
  
  (defret base-bvar-of-<fn>
    (equal (base-bvar$c (interp-st->bvar-db new-interp-st))
           (base-bvar$c (interp-st->bvar-db interp-st))))

  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key (interp-st->logicman new-interp-st))
                    (logicman-get key (interp-st->logicman interp-st)))))

  (local
   (defret get-bvar->term-old-of-<fn>
     (b* ((bvar-db (interp-st->bvar-db interp-st)))
       (implies (< (nfix n) (next-bvar$c bvar-db))
                (equal (get-bvar->term$c n (interp-st->bvar-db new-interp-st))
                       (get-bvar->term$c n (interp-st->bvar-db interp-st)))))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn interp-st-add-term-bvar-unique))

  (local
   (defret next-bvar-of-<fn>
     (>= (next-bvar$c (interp-st->bvar-db new-interp-st))
         (next-bvar$c (interp-st->bvar-db interp-st)))
     :hints(("Goal" :in-theory (enable <fn>)))
     :fn interp-st-add-term-bvar-unique
     :rule-classes :linear))

  (defret next-bvar-of-<fn>
    (>= (next-bvar$c (interp-st->bvar-db new-interp-st))
        (next-bvar$c (interp-st->bvar-db interp-st)))
    :rule-classes :linear)
  
  (defret get-bvar->term-old-of-<fn>
    (b* ((bvar-db (interp-st->bvar-db interp-st)))
      (implies (< (nfix k) (next-bvar$c bvar-db))
               (equal (get-bvar->term$c k (interp-st->bvar-db new-interp-st))
                      (get-bvar->term$c k (interp-st->bvar-db interp-st))))))

  (defret interp-st-bvar-db-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-object-bfrlist x) interp-st))
             (implies (not (interp-st-bvar-db-ok interp-st env))
                      (not (interp-st-bvar-db-ok new-interp-st env)))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok new-interp-st)))

  (defret bfr-listp-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st)))
             (lbfr-listp bits
                         (interp-st->logicman new-interp-st))))

  (defret consp-of-<fn>
    (consp bits))

  (local
   (defret interp-st-bvar-db-ok-of-<fn>-rw
     (implies (and (interp-st-bfrs-ok interp-st)
                   (interp-st-bfr-listp (fgl-object-bfrlist x) interp-st))
              (iff (interp-st-bvar-db-ok new-interp-st env)
                   (and (hide (interp-st-bvar-db-ok new-interp-st env))
                        (interp-st-bvar-db-ok interp-st env))))
     :hints (("goal" :expand ((:free (x) (hide x)))))))

  ;; (local (defthm interp-st-bvar-db-ok-necc-rev
  ;;          (implies (interp-st-bvar-db-ok interp-st env)
  ;;                   (b* ((bvar-db (interp-st->bvar-db interp-st))
  ;;                        (logicman (interp-st->logicman interp-st)))
  ;;                     (implies (and (<= (base-bvar$c bvar-db) (nfix n))
  ;;                                   (< (nfix n) (next-bvar$c bvar-db)))
  ;;                              (iff* (gobj-bfr-eval (bfr-var n) env logicman)
  ;;                                    (fgl-object-eval (get-bvar->term$c n bvar-db) env logicman)))))))
  (local (in-theory (disable interp-st-bvar-db-ok-necc)))

  (local (defret eval-of-interp-st-add-term-bvar-unique
           (implies (and (interp-st-bvar-db-ok new-interp-st env)
                         (lbfr-listp (fgl-object-bfrlist x)
                                     (interp-st->logicman interp-st)))
                    (iff* (gobj-bfr-eval bfr env (interp-st->logicman new-interp-st))
                          (fgl-object-eval x env (interp-st->logicman interp-st))))
           :hints(("Goal" :in-theory (enable <fn>)
                   :use ((:instance interp-st-bvar-db-ok-necc
                          (n (get-term->bvar$c x (interp-st->bvar-db interp-st)))
                          (interp-st new-interp-st))
                         (:instance interp-st-bvar-db-ok-necc
                          (n (next-bvar$c (interp-st->bvar-db interp-st)))
                          (interp-st new-interp-st)))))
           :hints-sub-returnnames t
           :fn interp-st-add-term-bvar-unique))

  (defret eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bvar-db-ok new-interp-st env)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st)))
             (equal (bools->int (gobj-bfr-list-eval bits env (interp-st->logicman new-interp-st)))
                    (loghead n (fgl-object-eval x env (interp-st->logicman interp-st)))))
    :hints (("Goal" :induct <call>
             :in-theory (enable bitops::equal-logcons-strong)
             :expand ((:free (x) (loghead n x)))))))
       
(define gobj-n-bit-unsigned-integer-fix ((n natp)
                                         (x fgl-object-p)
                                         (interp-st)
                                         (state))
  :returns (mv ok (new-x fgl-object-p) new-interp-st)
  :measure (fgl-object-count x)
  :guard (and (interp-st-bfrs-ok interp-st)
              (interp-st-bfr-listp (fgl-object-bfrlist x)))
  :verify-guards nil
  (fgl-object-case x
    :g-concrete (mv t (g-concrete (loghead n (ifix x.val))) interp-st)
    :g-boolean (mv t 0 interp-st)
    :g-integer (mv t (mk-g-integer (s-append (extend-bits n x.bits) '(nil))) interp-st)
    :g-cons (mv t 0 interp-st)
    :g-ite (b* (((unless (fgl-object-case x.test :g-boolean))
                 (mv nil nil interp-st))
                ((mv ok1 new-then interp-st) (gobj-n-bit-unsigned-integer-fix n x.then interp-st state))
                ((unless ok1) (mv nil nil interp-st))
                ((mv ok2 new-else interp-st) (gobj-n-bit-unsigned-integer-fix n x.else interp-st state))
                ((unless ok2) (mv nil nil interp-st))
                (then-bits (gobj-syntactic-integer->bits new-then))
                (else-bits (gobj-syntactic-integer->bits new-else)))
             (stobj-let ((logicman (interp-st->logicman interp-st)))
                        (bits logicman)
                        (bfr-ite-bss-fn (g-boolean->bool x.test) then-bits else-bits logicman)
                        (mv t (mk-g-integer bits) interp-st)))
    :otherwise ;; g-apply, g-var
    (b* (((mv bits interp-st)
          (gen-unsigned-integer-bits n x interp-st state)))
      (mv t (mk-g-integer bits) interp-st)))
  ///
  
  (local (in-theory (disable acl2::member-of-append
                             bfrlist-of-g-ite-accessors
                             member-equal
                             bfr-listp-when-not-member-witness
                             equal-of-booleans-rewrite)))

  (local (defthm gobj-syntactic-integerp-of-mk-g-integer
           (gobj-syntactic-integerp (mk-g-integer bits))
           :hints(("Goal" :in-theory (enable gobj-syntactic-integerp mk-g-integer)))))

  (local (defthm gobj-syntactic-integerp-of-g-concrete
           (equal (gobj-syntactic-integerp (g-concrete x))
                  (integerp x))
           :hints(("Goal" :in-theory (enable gobj-syntactic-integerp)))))
  
  (defret gobj-syntactic-integerp-of-<fn>
    (implies ok
             (gobj-syntactic-integerp new-x)))
  
  (defret interp-st-get-of-<fn>
    (implies (and (not (Equal (interp-st-field-fix key) :logicman))
                  (not (Equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$c (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$c (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))


  (local (defret bfr-nvars-of-interp-st-add-term-bvar-unique
           (<= (bfr-nvars (interp-st->logicman interp-st))
               (bfr-nvars (interp-st->logicman new-interp-st)))
           :hints(("Goal" :in-theory (enable <fn>)))
           :rule-classes :linear
           :fn interp-st-add-term-bvar-unique))

  (defret bfr-nvars-of-<fn>
    (>= (bfr-nvars (interp-st->logicman new-interp-st))
        (bfr-nvars (interp-st->logicman interp-st)))
    :rule-classes :linear)
  
  (defret base-bvar-of-<fn>
    (equal (base-bvar$c (interp-st->bvar-db new-interp-st))
           (base-bvar$c (interp-st->bvar-db interp-st))))

  ;; (defret logicman-get-of-<fn>
  ;;   (implies (not (equal (logicman-field-fix key) :aignet))
  ;;            (equal (logicman-get key (interp-st->logicman new-interp-st))
  ;;                   (logicman-get key (interp-st->logicman interp-st)))))

  (defret next-bvar-of-<fn>
    (>= (next-bvar$c (interp-st->bvar-db new-interp-st))
        (next-bvar$c (interp-st->bvar-db interp-st)))
    :rule-classes :linear)

  (defret get-bvar->term-old-of-<fn>
    (b* ((bvar-db (interp-st->bvar-db interp-st)))
      (implies (< (nfix k) (next-bvar$c bvar-db))
               (equal (get-bvar->term$c k (interp-st->bvar-db new-interp-st))
                      (get-bvar->term$c k (interp-st->bvar-db interp-st))))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok new-interp-st)))

  (defret interp-st-bvar-db-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-object-bfrlist x) interp-st))
             (implies (not (interp-st-bvar-db-ok interp-st env))
                      (not (interp-st-bvar-db-ok new-interp-st env)))))

  (defret bfr-listp-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st)))
             (lbfr-listp (fgl-object-bfrlist new-x)
                         (interp-st->logicman new-interp-st)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-listp-when-not-member-witness)))))
  
  (verify-guards gobj-n-bit-unsigned-integer-fix)


  (local (Defthm loghead-when-zip
           (implies (zip x)
                    (equal (loghead n x) 0))
           :hints(("Goal" :in-theory (enable bitops::loghead**)))))

  (local (defthm bools->int-of-syntactic-integer->bits
           (implies (gobj-syntactic-integerp x)
                    (equal (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits x) env))
                           (fgl-object-eval x env)))))

  (local (in-theory (disable FGL-OBJECT-EVAL-WHEN-GOBJ-SYNTACTIC-INTEGERP)))
  
  (defret eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bvar-db-ok new-interp-st env)
                  (lbfr-listp (fgl-object-bfrlist x)
                              (interp-st->logicman interp-st))
                  ok)
             (equal (fgl-object-eval new-x env (interp-st->logicman new-interp-st))
                    (loghead n (fgl-object-eval x env (interp-st->logicman interp-st)))))
    :hints (("goal" :induct <call>)))

  (defretd interp-st-bvar-db-ok-of-<fn>-rw
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-object-bfrlist x) interp-st))
             (iff (interp-st-bvar-db-ok new-interp-st env)
                  (and (hide (interp-st-bvar-db-ok new-interp-st env))
                       (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :expand ((:free (x) (hide x))))))
  
  )

(local
 (defthm bfr-listp-of-bvar->term-bfrlist-when-interp-st-bfrs-ok
   (implies (and (interp-st-bfrs-ok interp-st)
                 (<= (base-bvar$c (interp-st->bvar-db interp-st)) (nfix n))
                 (< (nfix n) (bfr-nvars (interp-st->logicman interp-st))))
            (lbfr-listp (fgl-object-bfrlist (get-bvar->term$c n (interp-st->bvar-db interp-st)))
                        (interp-st->logicman interp-st)))))


(local (in-theory (disable bfr-listp-when-not-member-witness)))


(local (in-theory (enable interp-st-bvar-db-ok-of-gobj-n-bit-unsigned-integer-fix-rw)))

(local (defthm bools->int-of-syntactic-integer->bits
         (implies (gobj-syntactic-integerp x)
                  (equal (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits x) env))
                         (fgl-object-eval x env)))))

(local (in-theory (disable FGL-OBJECT-EVAL-WHEN-GOBJ-SYNTACTIC-INTEGERP)))

(local (defthm sv::sparseint-nfix-idem
         (equal (sv::sparseint-nfix (sv::sparseint-nfix x))
                (sv::sparseint-nfix x))
         :hints(("Goal" :in-theory (enable sv::sparseint-nfix)))))

(local (defthm 4vmask-to-a4vec-rec-env-of-fix-mask
         (equal (sv::4vmask-to-a4vec-rec-env
                 (sv::sparseint-nfix (sv::4vmask-fix mask))
                 boolmask upper lower nextvar)
                (sv::4vmask-to-a4vec-rec-env
                 mask boolmask upper lower nextvar))
         :hints(("Goal" :in-theory (enable (:i sv::4vmask-to-a4vec-rec-env))
                 :induct (sv::4vmask-to-a4vec-rec-env
                          mask boolmask upper lower nextvar)
                 :expand ((:free (mask) (sv::4vmask-to-a4vec-rec-env
                 mask boolmask upper lower nextvar)))))))


(define fgl-4vmask-to-a4vec-rec-env-top ((mask bitops::sparseint-p)
                                         (boolmask integerp)
                                         (upper fgl-object-p)
                                         (lower fgl-object-p)
                                         (nextvar natp)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
  :guard (and (not (bitops::sparseint-< mask 0))
              (interp-st-bfr-listp (fgl-object-bfrlist upper))
              (interp-st-bfr-listp (fgl-object-bfrlist lower)))
  :returns (mv ok
               (ans fgl-object-alist-p)
               new-interp-st)
  :hooks nil
  (b* ((masklen (bitops::sparseint-length (sv::4vmask-fix mask)))
       ((mv ok upper-fix interp-st) (gobj-n-bit-unsigned-integer-fix masklen upper interp-st state))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok lower-fix interp-st) (gobj-n-bit-unsigned-integer-fix masklen lower interp-st state))
       ((unless ok) (mv nil nil interp-st))
       (map
        (fgl-4vmask-to-a4vec-rec-env mask boolmask
                                     (gobj-syntactic-integer->bits upper-fix)
                                     (gobj-syntactic-integer->bits lower-fix)
                                     nextvar)))
    (mv t map interp-st))
  ///
  
  
  (defret interp-st-get-of-<fn>
    (implies (and (not (Equal (interp-st-field-fix key) :logicman))
                  (not (Equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$c (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$c (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bfr-nvars-of-<fn>
    (>= (bfr-nvars (interp-st->logicman new-interp-st))
        (bfr-nvars (interp-st->logicman interp-st)))
    :rule-classes :linear)
  
  (defret base-bvar-of-<fn>
    (equal (base-bvar$c (interp-st->bvar-db new-interp-st))
           (base-bvar$c (interp-st->bvar-db interp-st))))

  (defret next-bvar-of-<fn>
    (>= (next-bvar$c (interp-st->bvar-db new-interp-st))
        (next-bvar$c (interp-st->bvar-db interp-st)))
    :rule-classes :linear)

  (defret get-bvar->term-old-of-<fn>
    (b* ((bvar-db (interp-st->bvar-db interp-st)))
      (implies (< (nfix k) (next-bvar$c bvar-db))
               (equal (get-bvar->term$c k (interp-st->bvar-db new-interp-st))
                      (get-bvar->term$c k (interp-st->bvar-db interp-st))))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist upper)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-bfrlist lower)
                              (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok new-interp-st)))

  (defret interp-st-bvar-db-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist upper)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-bfrlist lower)
                              (interp-st->logicman interp-st)))
             (implies (not (interp-st-bvar-db-ok interp-st env))
                      (not (interp-st-bvar-db-ok new-interp-st env)))))

  (defret bfr-listp-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist upper)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-bfrlist lower)
                              (interp-st->logicman interp-st)))
             (lbfr-listp (fgl-object-alist-bfrlist ans)
                         (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness))))
  
  (defret eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bvar-db-ok new-interp-st env)
                  (lbfr-listp (fgl-object-bfrlist upper)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-bfrlist lower)
                              (interp-st->logicman interp-st))
                  (<= 0 (bitops::sparseint-val (sv::4vmask-fix mask)))
                  ;; (svex-formula-checks state)
                  ok)
             (equal (fgl-object-alist-eval ans env (interp-st->logicman new-interp-st))
                    (sv::4vmask-to-a4vec-rec-env
                     mask boolmask
                     (fgl-object-eval upper env (interp-st->logicman interp-st))
                     (fgl-object-eval lower env (interp-st->logicman interp-st))
                     nextvar))))

  (local (defretd interp-st-bvar-db-ok-of-<fn>-lemma
           (implies (and (interp-st-bfrs-ok interp-st)
                         (lbfr-listp (fgl-object-bfrlist upper)
                                     (interp-st->logicman interp-st))
                         (lbfr-listp (fgl-object-bfrlist lower)
                                     (interp-st->logicman interp-st)))
                    (iff (interp-st-bvar-db-ok new-interp-st env)
                         (and (interp-st-bvar-db-ok new-interp-st env)
                              (interp-st-bvar-db-ok interp-st env))))))

  
  (defretd interp-st-bvar-db-ok-of-<fn>-rw
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-bfrlist upper)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-bfrlist lower)
                              (interp-st->logicman interp-st)))
             (iff (interp-st-bvar-db-ok new-interp-st env)
                  (and (hide (interp-st-bvar-db-ok new-interp-st env))
                       (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :in-theory nil
             :expand ((:free (x) (hide x)))
             :use interp-st-bvar-db-ok-of-<fn>-lemma)))

  (defret true-listp-of-<fn>
    (true-listp ans)))
  

(def-fgl-primitive sv::4vmask-to-a4vec-rec-env (mask boolmask upper lower nextvar)
  (b* (((unless (and (fgl-object-case mask :g-concrete)
                     (fgl-object-case boolmask :g-concrete)
                     (fgl-object-case nextvar :g-concrete)))
        (mv nil nil interp-st))
       (mask (ec-call (sv::sparseint-nfix (ec-call (sv::4vmask-fix (g-concrete->val mask))))))
       (boolmask (ifix (g-concrete->val boolmask)))
       (nextvar (nfix (g-concrete->val nextvar)))
       ((mv ok map interp-st)
        (fgl-4vmask-to-a4vec-rec-env-top
         mask boolmask upper lower nextvar interp-st state)))
    (mv ok (g-map '(:g-map) map) interp-st))
  :formula-check svex-formula-checks)


(define fgl-4vec->upper ((x fgl-object-p))
  :returns (mv ok (upper fgl-object-p))
  (fgl::fgl-object-case x
    :g-concrete (mv t (g-concrete (ec-call (sv::4vec->upper x.val))))
    :g-integer (mv t (fgl-object-fix x))
    :g-boolean (mv t -1)
    :g-cons (fgl::fgl-object-case x.car
              :g-concrete (mv t (g-concrete (ifix x.car.val)))
              :g-integer (mv t x.car)
              :g-boolean (mv t 0)
              :g-cons (mv t 0)
              :otherwise (mv nil nil))
    :g-apply (if (and (eq x.fn 'sv::4vec)
                      (eql (len x.args) 2))
                 (let ((arg1 (car x.args)))
                   (fgl::fgl-object-case arg1
                     :g-concrete (mv t (g-concrete (ifix arg1.val)))
                     :g-integer (mv t arg1)
                     :g-boolean (mv t 0)
                     :g-cons (mv t 0)
                     :otherwise (mv nil nil)))
               (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS)
                  (SVEX-FORMULA-CHECKS STATE))
             (equal (fgl-object-eval upper env)
                    (sv::4vec->upper (fgl-object-eval x env))))
    :hints(("Goal" :in-theory (enable sv::4vec->upper))))

  (defret bfr-listp-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp (fgl-object-bfrlist upper)))))

(define fgl-4vec->lower ((x fgl-object-p))
  :returns (mv ok (lower fgl-object-p))
  (fgl::fgl-object-case x
    :g-concrete (mv t (g-concrete (ec-call (sv::4vec->lower x.val))))
    :g-integer (mv t (fgl-object-fix x))
    :g-boolean (mv t 0)
    :g-cons (fgl::fgl-object-case x.cdr
              :g-concrete (mv t (g-concrete (ifix x.cdr.val)))
              :g-integer (mv t x.cdr)
              :g-boolean (mv t 0)
              :g-cons (mv t 0)
              :otherwise (mv nil nil))
    :g-apply (if (and (eq x.fn 'sv::4vec)
                      (eql (len x.args) 2))
                 (let ((arg2 (cadr x.args)))
                   (fgl::fgl-object-case arg2
                     :g-concrete (mv t (g-concrete (ifix arg2.val)))
                     :g-integer (mv t arg2)
                     :g-boolean (mv t 0)
                     :g-cons (mv t 0)
                     :otherwise (mv nil nil)))
               (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret eval-of-<fn>
    (implies (and ok
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS)
                  (SVEX-FORMULA-CHECKS STATE))
             (equal (fgl-object-eval lower env)
                    (sv::4vec->lower (fgl-object-eval x env))))
    :hints(("Goal" :in-theory (enable sv::4vec->lower))))

  (defret bfr-listp-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp (fgl-object-bfrlist lower)))))
    

(define fgl-svex-varmasks/env->aig-env-rec ((vars sv::svarlist-p)
                                            (masks sv::svex-mask-alist-p)
                                            (boolmasks sv::svar-boolmasks-p)
                                            (env-obj fgl::fgl-object-alist-p "look up variables in env to get 4vecs to assign -- symbolic")
                                            (nextvar natp)
                                            (acc fgl::fgl-object-alist-p
                                                 "aig environment accumulator")
                                            (fgl::interp-st fgl::interp-st-bfrs-ok)
                                            (state))
  :guard (and (fgl::interp-st-bfr-listp (fgl::fgl-object-alist-bfrlist acc))
              (fgl::interp-st-bfr-listp (fgl::fgl-object-alist-bfrlist env-obj)))
  :verify-guards nil
  :returns (mv (successp)
               (err)
               (aig-env fgl-object-alist-p)
               (new-nextvar)
               new-interp-st)
  (b* ((acc (fgl::fgl-object-alist-fix acc))
       ((when (atom vars))
        (mv t nil acc (lnfix nextvar) fgl::interp-st))
       (mask (sv::svex-mask-lookup (sv::svex-var (car vars)) masks))
       ((when (sv::sparseint-< mask 0))
        (mv t (msg "Negative mask: ~x0~%" (sv::svar-fix (car vars)))
            acc (lnfix nextvar) fgl::interp-st))
       (boolmask (sv::svar-boolmasks-lookup (car vars) boolmasks))
       (4vec-obj (cdr (hons-get (sv::svar-fix (car vars))
                                (fgl::fgl-object-alist-fix env-obj))))
       ((mv ok upper) (fgl::fgl-4vec->upper 4vec-obj))
       ((unless ok)
        (mv nil nil acc (lnfix nextvar) fgl::interp-st))
       ((mv ok lower) (fgl::fgl-4vec->lower 4vec-obj))
       ((unless ok)
        (mv nil nil acc (lnfix nextvar) fgl::interp-st))
       ((mv ok env-part fgl::interp-st)
        (fgl::fgl-4vmask-to-a4vec-rec-env-top mask boolmask upper lower (lnfix nextvar) fgl::interp-st state))
       ((unless ok)
        (mv nil nil acc (lnfix nextvar) fgl::interp-st))
       (nextvar (+ (lnfix nextvar)
                   (sv::4vmask-to-a4vec-varcount mask boolmask))))
    (fgl-svex-varmasks/env->aig-env-rec
     (cdr vars) masks boolmasks env-obj nextvar (append env-part acc)
     fgl::interp-st state))
  ///
  
  
  (defret interp-st-get-of-<fn>
    (implies (and (not (Equal (interp-st-field-fix key) :logicman))
                  (not (Equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$c (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$c (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bfr-nvars-of-<fn>
    (>= (bfr-nvars (interp-st->logicman new-interp-st))
        (bfr-nvars (interp-st->logicman interp-st)))
    :rule-classes :linear)
  
  (defret base-bvar-of-<fn>
    (equal (base-bvar$c (interp-st->bvar-db new-interp-st))
           (base-bvar$c (interp-st->bvar-db interp-st))))

  (defret next-bvar-of-<fn>
    (>= (next-bvar$c (interp-st->bvar-db new-interp-st))
        (next-bvar$c (interp-st->bvar-db interp-st)))
    :rule-classes :linear)

  (defret get-bvar->term-old-of-<fn>
    (b* ((bvar-db (interp-st->bvar-db interp-st)))
      (implies (< (nfix k) (next-bvar$c bvar-db))
               (equal (get-bvar->term$c k (interp-st->bvar-db new-interp-st))
                      (get-bvar->term$c k (interp-st->bvar-db interp-st))))))

  (local (defthm fgl-object-alist-bfrlist-of-append
           (equal (fgl-object-alist-bfrlist (append x y))
                  (append (fgl-object-alist-bfrlist x)
                          (fgl-object-alist-bfrlist y)))
           :hints (("goal" :induct (append x y)
                    :expand ((:free (a b)
                              (fgl-object-alist-bfrlist (cons a b)))
                             (fgl-object-alist-bfrlist x))))))

  (local (defthm bfr-listp-fgl-object-bfrlist-of-lookup
           (implies (bfr-listp (fgl-object-alist-bfrlist x))
                    (bfr-listp (fgl-object-bfrlist (cdr (hons-assoc-equal k x)))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)
                   :induct (hons-assoc-equal k x)
                   :expand (fgl-object-alist-bfrlist x)))))
  
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-alist-bfrlist acc)
                              (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable BFR-LISTP-WHEN-NOT-MEMBER-WITNESS))))

  (defret interp-st-bvar-db-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-alist-bfrlist acc)
                              (interp-st->logicman interp-st)))
             (implies (not (interp-st-bvar-db-ok interp-st env))
                      (not (interp-st-bvar-db-ok new-interp-st env)))))

  (defret bfr-listp-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-alist-bfrlist acc)
                              (interp-st->logicman interp-st)))
             (lbfr-listp (fgl-object-alist-bfrlist aig-env)
                         (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness))))

  (local (defthm fgl-object-alist-eval-of-append
           (Equal (fgl-object-alist-eval (append x y) env)
                  (append (fgl-object-alist-eval x env)
                          (fgl-object-alist-eval y env)))
           :hints(("Goal" :in-theory (enable append)
                   :expand ((fgl-object-alist-eval x env)
                            (:free (a b) (fgl-object-alist-eval (cons a b) env)))))))


  

  (local (defretd interp-st-bvar-db-ok-of-<fn>-lemma
           (implies (and (interp-st-bfrs-ok interp-st)
                         (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                                     (interp-st->logicman interp-st))
                         (lbfr-listp (fgl-object-alist-bfrlist acc)
                                     (interp-st->logicman interp-st)))
                    (iff (interp-st-bvar-db-ok new-interp-st env)
                         (and (interp-st-bvar-db-ok new-interp-st env)
                              (interp-st-bvar-db-ok interp-st env))))))

  

  
  (defretd interp-st-bvar-db-ok-of-<fn>-rw
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-alist-bfrlist acc)
                              (interp-st->logicman interp-st)))
             (iff (interp-st-bvar-db-ok new-interp-st env)
                  (and (hide (interp-st-bvar-db-ok new-interp-st env))
                       (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :in-theory nil
             :expand ((:free (x) (hide x)))
             :use interp-st-bvar-db-ok-of-<fn>-lemma)))

  (local (defthm hons-assoc-equal-of-fgl-object-alist-eval
           (Equal (cdr (hons-assoc-equal k (fgl-object-alist-eval x env)))
                  (fgl-object-eval (cdr (hons-assoc-equal k x)) env))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)
                   :expand ((fgl-object-alist-eval x env)
                            (:free (a b) (fgl-object-alist-eval (cons a b) env)))))))
  
  
  (defret eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bvar-db-ok new-interp-st env)
                  (lbfr-listp (fgl-object-alist-bfrlist env-obj)
                              (interp-st->logicman interp-st))
                  (lbfr-listp (fgl-object-alist-bfrlist acc)
                              (interp-st->logicman interp-st))
                  (FGL-EV-META-EXTRACT-GLOBAL-FACTS :state st)
                  (equal (w st) (w state))
                  (svex-formula-checks st)
                  successp)
             (b* (((mv err-spec aig-env-spec new-nextvar-spec)
                   (sv::svex-varmasks/env->aig-env-rec
                     vars masks boolmasks
                     (fgl-object-alist-eval env-obj env (interp-st->logicman interp-st))
                     nextvar
                     (fgl-object-alist-eval acc env (interp-st->logicman interp-st)))))
               (and (implies (interp-st-bvar-db-ok new-interp-st env)
                             (interp-st-bvar-db-ok interp-st env))
                    (equal err err-spec)
                    (equal (fgl-object-alist-eval aig-env env (interp-st->logicman new-interp-st))
                           aig-env-spec)
                    (equal new-nextvar new-nextvar-spec))))
    :hints(("Goal" :expand ((:free (env acc)
                             (SV::SVEX-VARMASKS/ENV->AIG-ENV-REC vars masks boolmasks env nextvar acc)))
            :in-theory (enable SV::4VMASK-TO-A4VEC-ENV
                               interp-st-bvar-db-ok-of-<fn>-rw
                               interp-st-bvar-db-ok-of-fgl-4vmask-to-a4vec-rec-env-top-rw
                               sv::svex-env-lookup)
            :induct <call>
            :do-not-induct t)))

  (Verify-guards fgl-svex-varmasks/env->aig-env-rec))
                
;; (def-fgl-primitive sv::4vmask-to-a4vec-rec-env (mask boolmask upper lower nextvar)
;;   (b* (((unless (and (fgl-object-case mask :g-concrete)
;;                      (fgl-object-case boolmask :g-concrete)
;;                      (fgl-object-case nextvar :g-concrete)))
;;         (mv nil nil interp-st))
;;        (mask (ec-call (sv::sparseint-nfix (ec-call (sv::4vmask-fix (g-concrete->val mask))))))
;;        (boolmask (ifix (g-concrete->val boolmask)))
;;        (nextvar (nfix (g-concrete->val nextvar)))
;;        ((mv ok map interp-st)
;;         (fgl-4vmask-to-a4vec-rec-env-top
;;          mask boolmask upper lower nextvar interp-st state)))
;;     (mv ok (g-map '(:g-map) map) interp-st))
;;   :formula-check svex-formula-checks)

(local (defthm svex-varmasks/env->aig-env-rec
         (b* ((ans (sv::svex-varmasks/env->aig-env-rec
                    vars masks boolmasks env-obj nextvar acc))
              ((mv a b c) ans))
           (equal (mv a b c) ans))
         :hints(("Goal" :in-theory (enable sv::svex-varmasks/env->aig-env-rec)))))


(local (defthm cdr-of-fgl-objectlist-fix
         (equal (cdr (fgl-objectlist-fix x))
                (fgl-objectlist-fix (cdr x)))
         :hints(("Goal" :expand ((fgl-objectlist-fix x))))))

(local (defthm fgl-object-eval-when-not-fix
         (implies (not (fgl-object-fix x))
                  (Equal (fgl-object-eval x env) nil))
         :hints(("Goal" :use ((:instance fgl-object-eval-of-fgl-object-fix))
                 :in-theory (disable fgl-object-eval-of-fgl-object-fix
                                     fgl-object-eval-of-fgl-object-fix-x
                                     fgl-object-eval-fgl-object-equiv-congruence-on-x)))))

(local (in-theory (disable sv::svex-varmasks/env->aig-env-accumulator-elim)))

(fgl::def-fgl-primitive sv::svex-varmasks/env->aig-env-rec
  (vars masks boolmasks env-obj nextvar acc)
  (b* (((unless (and (fgl-object-case masks :g-concrete)
                     (fgl-object-case vars :g-concrete)
                     (fgl-object-case boolmasks :g-concrete)
                     (fgl-object-case nextvar :g-concrete)
                     (fgl-object-case env-obj :g-map)
                     (or (eq (fgl-object-fix acc) nil)
                         (fgl-object-case acc :g-map))))
        (mv nil nil interp-st))
       (env-obj (g-map->alist env-obj))
       (acc (if (eq (fgl-object-fix acc) nil)
                nil
              (g-map->alist acc)))
       (vars (ec-call (sv::svarlist-fix (g-concrete->val vars))))
       (masks (ec-call (sv::svex-mask-alist-fix (g-concrete->val masks))))
       (boolmasks (ec-call (sv::svar-boolmasks-fix (g-concrete->val boolmasks))))
       (nextvar (ec-call (nfix (g-concrete->val nextvar))))
       ((mv ok err aig-env nextvar interp-st)
        (fgl-svex-varmasks/env->aig-env-rec
         vars masks boolmasks env-obj nextvar acc interp-st state)))
    (mv ok (g-cons (g-concrete err)
                   (g-cons (g-map '(:g-map)
                                  (make-fast-alist aig-env))
                           (g-cons (g-concrete nextvar) nil)))
        interp-st))
  :formula-check svex-formula-checks)
       




(define v2i-first-n-bits ((n natp) (x fgl-object-p))
  :returns (mv ok (bits true-listp))
  (if (zp n)
      (mv t nil)
    (fgl-object-case x
      :g-concrete (mv t (take n (ec-call (acl2::boolean-list-fix x.val))))
      :g-cons (b* (((mv rest-ok rest) (v2i-first-n-bits (1- n) x.cdr))
                   ((unless rest-ok) (mv nil nil)))
                (fgl-object-case x.car
                  :g-concrete (mv t (cons (and x.car.val t) rest))
                  :g-boolean (mv t (cons x.car.bool rest))
                  :g-cons (mv t (cons t rest))
                  :g-integer (mv t (cons t rest))
                  :otherwise (mv nil nil)))
      :g-boolean (mv t (acl2::repeat n nil))
      :g-integer (mv t (acl2::repeat n nil))
      :otherwise (mv nil nil)))
  ///
  (local (defthm bfr-listp-when-boolean-listp
           (implies (boolean-listp x)
                    (Bfr-listp x))
           :hints(("Goal" :in-theory (enable bfr-p boolean-listp)))))
  (defret bfr-listp-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp bits)))

  (local (defthm gobj-bfr-list-eval-of-repeat-nil
           (equal (gobj-bfr-list-eval (acl2::repeat n nil) env)
                  (acl2::repeat n nil))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval
                                             acl2::repeat)))))
  
  (defret eval-of-<fn>
    (implies ok
             (equal (gobj-bfr-list-eval bits env)
                    (acl2::boolean-list-fix (take n (fgl-object-eval x env)))))
    :hints (("goal" :induct <call>
             :in-theory (enable gl::v2i)))))
      
(local (defthm v2i-is-bools->int
         (equal (gl::v2i x)
                (bools->int x))
         :hints(("Goal" :in-theory (enable bools->int
                                           gl::v2i
                                           gl::scdr
                                           gl::s-endp
                                           gl::bool->sign)))))

(def-fgl-primitive sv::v2i-first-n (n v)
  (b* (((unless (fgl-object-case n :g-concrete))
        (mv nil nil interp-st))
       (n (nfix (g-concrete->val n)))
       ((mv ok bits) (v2i-first-n-bits n v))
       ((unless ok)
        (mv nil nil interp-st)))
    (mv t (g-integer bits) interp-st))
  :formula-check svex-formula-checks)





(local (install-fgl-metafns svexprims))

