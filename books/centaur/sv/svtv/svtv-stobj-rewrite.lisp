; Centaur SV Hardware Verification Tutorial
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

(include-book "svtv-stobj")


(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))

(local (fty::deflist svexlist :elt-type svex :true-listp t))

(local (defthm svex-lookup-of-pairlis
         (equal (svex-lookup var (pairlis$ x y))
                (b* ((index (index-of (svar-fix var) x)))
                  (and index
                       (svex-fix (nth index y)))))
         :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix index-of)))))



(local
 (encapsulate nil
   ;; (local (defthm svex-eval-of-nth-split
   ;;          (equal (svex-eval (nth n x) env)
   ;;                 (if (< (nfix n) (len x))
   ;;                     (nth n (svexlist-eval x env))
   ;;                   (4vec-x)))
   ;;          :hints(("Goal" :in-theory (enable nth svexlist-eval)))))
   (local (defcong svexlist-eval-equiv equal (consp x) 1
            :hints (("goal" :use ((:instance consp-of-svexlist-eval (x x))
                                  (:instance consp-of-svexlist-eval (x x-equiv)))
                     :in-theory (disable consp-of-svexlist-eval)))))

   (local (defun ind (n x x-equiv)
            (if (zp n)
                (list x x-equiv)
              (ind (1- n) (cdr x) (cdr x-equiv)))))

   (defcong svexlist-eval-equiv svex-eval-equiv (nth n x) 2
     :hints (("goal" :induct (ind n x x-equiv) :in-theory (enable nth))))))

(local (defcong svexlist-eval-equiv svex-alist-eval-equiv! (pairlis$ x y) 2
         :hints ((witness))))

(local (defcong svexlist-eval-equiv svexlist-eval-equiv (nthcdr n x) 2))

(local (defcong svexlist-eval-equiv svexlist-eval-equiv (take n x) 2))

(local (defthm svexlist-rewrite-fixpoint-under-svexlist-eval-equiv
         (svexlist-eval-equiv (svexlist-rewrite-fixpoint x :count count :verbosep verbosep)
                              x)
         :hints ((witness))))

(local (defthm pairlis-svex-alist-keys-svex-alist-vals
         (equal (pairlis$ (svex-alist-keys x) (svex-alist-vals x))
                (svex-alist-fix x))
         :hints(("Goal" :in-theory (enable pairlis$ svex-alist-keys svex-alist-vals svex-alist-fix)))))


(local (defthm nthcdr-of-append-len
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y)) y))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::nthcdr-of-cdr))
                 :expand ((append x y) (len x))
                 :induct (nthcdr n x)))))






(define svtv-data-rewrite-base-fsm (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap))))
  :returns new-svtv-data
  (b* ((values (svtv-data->base-values svtv-data))
       (nextstate (svtv-data->base-nextstate svtv-data))
       (svexes (append (svex-alist-vals values) (svex-alist-vals nextstate)))
       (svexes-rw (svexlist-rewrite-fixpoint svexes :count count :verbosep verbosep))
       (values-keys (svex-alist-keys values))
       (values-len (len values-keys))
       (values-rw (pairlis$ values-keys (take values-len svexes-rw)))
       (nextstate-keys (svex-alist-keys nextstate))
       (nextstate-rw (pairlis$ nextstate-keys (nthcdr values-len svexes-rw)))
       (svtv-data (update-svtv-data->base-values values-rw svtv-data)))
    (update-svtv-data->base-nextstate nextstate-rw svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :base-values))
                  (not (equal key :base-nextstate)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))

(define svtv-data-maybe-rewrite-base-fsm (do-it svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  :returns new-svtv-data
  (if do-it
      (svtv-data-rewrite-base-fsm svtv-data :count count :verbosep verbosep)
    svtv-data)
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :base-values))
                  (not (equal key :base-nextstate)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))





(define svtv-data-rewrite-cycle-fsm (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  :returns new-svtv-data
  (b* ((values (svtv-data->cycle-values svtv-data))
       (nextstate (svtv-data->cycle-nextstate svtv-data))
       (svexes (append (svex-alist-vals values) (svex-alist-vals nextstate)))
       (svexes-rw (svexlist-rewrite-fixpoint svexes :count count :verbosep verbosep))
       (values-keys (svex-alist-keys values))
       (values-len (len values-keys))
       (values-rw (pairlis$ values-keys (take values-len svexes-rw)))
       (nextstate-keys (svex-alist-keys nextstate))
       (nextstate-rw (pairlis$ nextstate-keys (nthcdr values-len svexes-rw)))
       (svtv-data (update-svtv-data->cycle-values values-rw svtv-data)))
    (update-svtv-data->cycle-nextstate nextstate-rw svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-values))
                  (not (equal key :cycle-nextstate)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))


(define svtv-data-maybe-rewrite-cycle-fsm (do-it svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  :returns new-svtv-data
  (if do-it
      (svtv-data-rewrite-cycle-fsm svtv-data :count count :verbosep verbosep)
    svtv-data)
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-values))
                  (not (equal key :cycle-nextstate)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))



(local (defthm eval-lookup-of-svex-alist-rewrite-fixpoint
         (equal (svex-eval (svex-lookup v (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)) env)
                (svex-eval (svex-lookup v x) env))
         :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                                (k v) (x (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)))
                               (:instance svex-env-lookup-of-svex-alist-eval
                                (k v) (x x)))
                  :in-theory (disable svex-env-lookup-of-svex-alist-eval)))))

(local (defthm svex-alist-rewrite-fixpoint-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)
                              x)
         :hints ((witness) (witness))))

(define svtv-data-rewrite-pipeline (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  :returns new-svtv-data
  (b* ((results (svtv-data->pipeline-results svtv-data))
       (results-rw (svex-alist-rewrite-fixpoint results :count count :verbosep verbosep)))
    (update-svtv-data->pipeline-results results-rw svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :pipeline-results)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))


(define svtv-data-maybe-rewrite-pipeline (do-it svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  :returns new-svtv-data
  (if do-it
      (svtv-data-rewrite-pipeline svtv-data :count count :verbosep verbosep)
    svtv-data)
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :pipeline-results)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data)))))
       
