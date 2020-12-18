; Centaur SV Hardware Verification Package
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "cycle-base")
(include-book "../svex/rewrite")
(include-book "../svex/unroll")

(encapsulate nil
  (local (defthm member-of-cons
           (iff (member k (cons a b))
                (or (equal k a)
                    (member k b)))))
  (local (in-theory (disable cons-equal member-equal)))
  (local (defthmd svex-alist-extract-when-not-present
           (implies (not (member-equal (caar x) (svarlist-fix keys)))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (svarlist-fix keys)
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthmd svex-alist-extract-when-bad-pair
           (implies (or (not (consp (car x)))
                        (not (svar-p (caar x))))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthm svex-alist-extract-of-cons
           (equal (svex-alist-extract (cons key rest) x)
                  (cons (cons (svar-fix key)
                              (or (svex-lookup key x)
                                  (svex-x)))
                        (svex-alist-extract rest x)))
           :hints(("Goal" :in-theory (enable svex-alist-extract)))))

  (defthm svex-alist-extract-when-same-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-extract (svex-alist-keys x) x)
                    (svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-extract-when-bad-pair
                                      svex-alist-extract-when-not-present
                                      svex-alist-fix
                                      svex-alist-keys
                                      no-duplicatesp-equal
                                      svex-lookup)))))


(local (in-theory (disable hons-dups-p)))

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append x y))
                (or (hons-assoc-equal k x)
                    (hons-assoc-equal k y)))))

(define svtv-fsm-step-subst ((in svex-alist-p)
                             (prev-st svex-alist-p)
                             (x svtv-fsm-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (subst svex-alist-p)
  (b* (((svtv-fsm x)))
    (make-fast-alist
     (append (mbe :logic (svex-alist-extract (svex-alist-keys x.nextstate)
                                             prev-st)
                  :exec prev-st)
             (svex-alist-fix in))))
  ///
  (defret eval-of-svtv-fsm-step-subst
    (equal (svex-alist-eval subst env)
           (svtv-fsm-step-env (svex-alist-eval in env)
                              (svex-alist-eval prev-st env)
                              x))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-env))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append x y))
                  (or (svex-lookup k x)
                      (svex-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret eval-lookup-of-svtv-fsm-step-subst
    (equal (svex-eval (svex-lookup k subst) env)
           (svex-env-lookup k (svtv-fsm-step-env (svex-alist-eval in env)
                                                 (svex-alist-eval prev-st env)
                                                 x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-env))))

  (defret normalize-svtv-fsm-fields-of-<fn>
    (implies (syntaxp (not (and (equal values ''nil)
                                (equal design ''((modalist) (top . "default-modname")))
                                (equal user-names ''nil)
                                (equal namemap ''nil))))
             (equal (let ((x (svtv-fsm values nextstate design user-names namemap))) <call>)
                    (let ((x (svtv-fsm nil nextstate '((modalist) (top . "default-modname")) nil nil)))
                      <call>)))))

(define svex-env-to-subst ((x svex-env-p))
  :returns (subst svex-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x)
                    (svex-quote (cdar x)))
              (svex-env-to-subst (cdr x)))
      (svex-env-to-subst (cdr x))))
  ///
  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key subst) env)
           (svex-env-lookup key x))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-fix)))))
       

(define svtv-cycle-step-phase-exprs ((prev-st svex-alist-p)
                                     (phase svtv-cyclephase-p)
                                     (x svtv-fsm-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextsts svex-alist-p))
  (b* (((svtv-cyclephase phase))
       (subst (svtv-fsm-step-subst (svex-env-to-subst phase.constants)
                                   prev-st x))
       ((svtv-fsm x))
       (outs (and phase.outputs-captured
                  (if phase.inputs-free
                      (svex-alist-compose-rw x.values subst)
                    (svex-alist-subst-rw x.values subst))))
       (nextsts (if phase.inputs-free
                    (svex-alist-compose-rw x.nextstate subst)
                  (svex-alist-subst-rw x.nextstate subst))))
    (fast-alist-free subst)
    (clear-memoize-table (if phase.inputs-free 'svex-compose-rw 'svex-subst-rw))
    (mv outs nextsts))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (and (svtv-cyclephase->outputs-captured phase)
                (svtv-cycle-step-phase-outs env
                                            (svex-alist-eval prev-st env)
                                            phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs
                                      svtv-fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextsts env)
           (svtv-cycle-step-phase-nextsts env
                                          (svex-alist-eval prev-st env)
                                          phase x))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts
                                      svtv-fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (local (defthm svex-eval-of-svex-lookup
           (equal (svex-eval (svex-lookup k x) env)
                  (svex-env-lookup k (svex-alist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup svex-lookup
                                             svex-env-fix svex-alist-fix)))))

  (defret eval-outs-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k outs) env)
           (if (svtv-cyclephase->outputs-captured phase)
               (svex-env-lookup k
                                (svtv-cycle-step-phase-outs env
                                                            (svex-alist-eval prev-st env)
                                                            phase x))
             (svex-x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret eval-nextsts-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k nextsts) env)
           (svex-env-lookup k
                            (svtv-cycle-step-phase-nextsts env
                                                           (svex-alist-eval prev-st env)
                                                           phase x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret svex-alist-keys-of-<fn>-nextst
    (equal (svex-alist-keys nextsts)
           (svex-alist-keys (svtv-fsm->nextstate x))))

  (defret normalize-svtv-fsm-fields-of-<fn>
    (implies (syntaxp (not (and (equal design ''((modalist) (top . "default-modname")))
                                (equal user-names ''nil)
                                (equal namemap ''nil))))
             (equal (let ((x (svtv-fsm values nextstate design user-names namemap))) <call>)
                    (let ((x (svtv-fsm values nextstate '((modalist) (top . "default-modname")) nil nil)))
                      <call>)))))



;; (define svtv-cycle-compile-outs ((ins svex-alist-p)
;;                                  (prev-st svex-alist-p)
;;                                  (phases svtv-cyclephaselist-p)
;;                                  (x svtv-fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
;;   :returns (outs svex-alist-p)
;;   :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
;;                       (implies (svex-alist-p x)
;;                                (true-listp x)))))
;;   (b* (((when (atom phases)) nil)
;;        ((mv outs1 nextst) (svtv-cycle-step-phase-exprs ins prev-st (car phases) x))
;;        (rest-outs (svtv-cycle-compile-outs ins nextst (cdr phases) x)))
;;     (mbe :logic (append outs1 rest-outs)
;;          :exec (if rest-outs
;;                    (append outs1 rest-outs)
;;                  outs1)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-cycle-eval-outs (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env))))))


;; (define svtv-cycle-compile-nextst ((ins svex-alist-p)
;;                                 (prev-st svex-alist-p)
;;                                 (phases svtv-cyclephaselist-p)
;;                                 (x svtv-fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
;;   :returns (nextst svex-alist-p)
;;   (b* (((when (atom phases))
;;         (mbe :logic (svex-alist-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
;;              :exec prev-st))
;;        (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
;;     (svtv-cycle-compile-nextst ins nextst (cdr phases) x))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval nextst env)
;;            (svtv-cycle-eval-nextst (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env)))))

;;   (defret svex-alist-keys-of-<fn>
;;     (equal (svex-alist-keys nextst)
;;            ()


(define svtv-cycle-compile ((prev-st svex-alist-p)
                            (phases svtv-cyclephaselist-p)
                            (x svtv-fsm-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextst svex-alist-p))
  :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
                      (implies (svex-alist-p x)
                               (true-listp x)))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-alist-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
                 :exec prev-st)))
       ((mv outs1 nextst) (svtv-cycle-step-phase-exprs prev-st (car phases) x))
       ((mv rest-outs final-st) (svtv-cycle-compile nextst (cdr phases) x)))
    (mv (if (svtv-cyclephase->outputs-captured (car phases))
            outs1
          rest-outs)
        final-st))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (svtv-cycle-eval-outs env
                                 (svex-alist-eval prev-st env)
                                 phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextst env)
           (svtv-cycle-eval-nextst env
                                   (svex-alist-eval prev-st env)
                                   phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys nextst)
           (svex-alist-keys (svtv-fsm->nextstate x)))
    :hints (("goal" :in-theory (disable <fn>
                                        alist-keys-of-svex-alist-eval)
             :use ((:instance alist-keys-of-svex-alist-eval
                    (x nextst))))))

  (defret normalize-svtv-fsm-fields-of-<fn>
    (implies (syntaxp (not (and (equal design ''((modalist) (top . "default-modname")))
                                (equal user-names ''nil)
                                (equal namemap ''nil))))
             (equal (let ((x (svtv-fsm values nextstate design user-names namemap))) <call>)
                    (let ((x (svtv-fsm values nextstate '((modalist) (top . "default-modname")) nil nil)))
                      <call>)))))


(define svex-identity-subst ((x svarlist-p))
  :returns (subst svex-alist-p)
  (pairlis$ (svarlist-fix x) (svarlist->svexes x))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst) (svarlist-fix x)))

  (local (defthm nth-of-svarlist->svexes
           (equal (nth n (svarlist->svexes x))
                  (and (< (nfix n) (len x))
                       (svex-var (nth n x))))
           :hints(("Goal" :in-theory (enable svarlist->svexes nth)))))


  (local (defthm hons-assoc-equal-of-pairlis
           (equal (hons-assoc-equal var (pairlis$ (svarlist-fix x)
                                                  (svarlist->svexes x)))
                  (and (member-equal var (svarlist-fix x))
                       (cons var (svex-var var))))
           :hints(("Goal" :in-theory (enable pairlis$ svarlist-fix svarlist->svexes)))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup var subst)
           (and (member-equal (svar-fix var) (svarlist-fix x))
                (svex-var var)))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (len) ;; svarlist-fix svarlist->svexes
                                   ))))

  (local (include-book "std/lists/sets" :dir :system))

  (local
   (deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil))

  (defcong set-equiv svex-alist-eval-equiv (svex-identity-subst x) 1
    :hints (("goal" :in-theory (disable set-equiv svex-identity-subst))
            (witness))))


(define svtv-fsm-to-cycle ((phases svtv-cyclephaselist-p)
                           (x svtv-fsm-p))
  :returns (cycle svtv-fsm-p)
  :guard (not (hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x))))
  (b* (((svtv-fsm x))
       (statevars (svex-alist-keys x.nextstate))
       (prev-st (svex-identity-subst statevars))
       ((mv outs nextst)
        (with-fast-alist prev-st
          (svtv-cycle-compile prev-st phases x))))
    (change-svtv-fsm x :values outs :nextstate nextst))
  ///
  (defret normalize-svtv-fsm-fields-of-<fn>
    (implies (syntaxp (not (and (equal design ''((modalist) (top . "default-modname")))
                                (equal user-names ''nil)
                                (equal namemap ''nil))))
             (and (equal (let ((x (svtv-fsm values nextstate design user-names namemap)))
                           (svtv-fsm->nextstate <call>))
                         (let ((x (svtv-fsm values nextstate '((modalist) (top . "default-modname")) nil nil)))
                           (svtv-fsm->nextstate <call>)))
                  (equal (let ((x (svtv-fsm values nextstate design user-names namemap)))
                           (svtv-fsm->values <call>))
                         (let ((x (svtv-fsm values nextstate '((modalist) (top . "default-modname")) nil nil)))
                           (svtv-fsm->values <call>))))))

  (defret nextst-svex-alist-keys-of-<fn>
    (equal (svex-alist-keys (svtv-fsm->nextstate cycle))
           (svex-alist-keys (svtv-fsm->nextstate x)))))
