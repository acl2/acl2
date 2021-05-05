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

(include-book "../svex/lists")
(include-book "std/basic/two-nats-measure" :dir :system)

(defprod svtv-evaldata
  ((nextstate svex-alist-p)
   (inputs svex-envlist-p)
   (initst svex-env-p))
  :layout :tree)

(local (defthm svex-env-p-of-nth
         (implies (svex-envlist-p x)
                  (svex-env-p (nth n x)))))

(defines svex-eval-svtv-phases
  :flag-local nil
  (define svex-eval-svtv-phases ((x svex-p)
                                    (phase natp)
                                    (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 1))
    :returns (val 4vec-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x.val
        :var (b* (((svtv-evaldata data))
                  (look (svex-fastlookup x.name data.nextstate))
                  ((when look)
                   ;; state var
                   (if (zp phase)
                       (svex-env-lookup x.name data.initst)
                     (svex-eval-svtv-phases look (1- phase) data))))
               ;; input var
               (svex-env-lookup x.name (nth phase data.inputs)))
        :call (svex-eval-svtv-phases-call x phase data))))

  (define svex-eval-svtv-phases-call ((x svex-p)
                                      (phase natp)
                                      (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 0))
    :returns (val 4vec-p)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) (4vec-x))
         ((svex-call x)))
      (mbe :logic (b* ((args (svexlist-eval-svtv-phases x.args phase data)))
                    (svex-apply x.fn args))
           :exec
           (case x.fn
             ((? ?*)
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (3vec-fix (svex-eval-svtv-phases (first x.args) phase data)))
                   ((4vec test))
                   ((when (eql test.upper 0))
                    (svex-eval-svtv-phases (third x.args) phase data))
                   ((when (not (eql test.lower 0)))
                    (svex-eval-svtv-phases (second x.args) phase data))
                   (then (svex-eval-svtv-phases (second x.args) phase data))
                   (else (svex-eval-svtv-phases (third x.args) phase data)))
                (case x.fn
                  (? (4vec-? test then else))
                  (?* (4vec-?* test then else)))))
             (?!
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((4vec test))
                   (testvec (logand test.upper test.lower))
                   ((when (eql testvec 0))
                    (svex-eval-svtv-phases (third x.args) phase data)))
                (svex-eval-svtv-phases (second x.args) phase data)))
             (bit?
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test 0))
                    (svex-eval-svtv-phases (third x.args) phase data))
                   ((when (eql test -1))
                    (svex-eval-svtv-phases (second x.args) phase data)))
                (4vec-bit? test
                           (svex-eval-svtv-phases (second x.args) phase data)
                           (svex-eval-svtv-phases (third x.args) phase data))))
             (bit?!
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test -1))
                    (svex-eval-svtv-phases (second x.args) phase data))
                   ((4vec test))
                   ((when (eql (logand test.upper test.lower) 0))
                    (svex-eval-svtv-phases (third x.args) phase data)))
                (4vec-bit?! test
                            (svex-eval-svtv-phases (second x.args) phase data)
                            (svex-eval-svtv-phases (third x.args) phase data))))
             (bitand
              (b* (((unless (eql (len x.args) 2))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test 0)) 0))
                (4vec-bitand test
                             (svex-eval-svtv-phases (second x.args) phase data))))
             (bitor
              (b* (((unless (eql (len x.args) 2))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test -1)) -1))
                (4vec-bitor test
                            (svex-eval-svtv-phases (second x.args) phase data))))
             (otherwise
              (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))))))

  (define svexlist-eval-svtv-phases ((x svexlist-p)
                                        (phase natp)
                                        (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svexlist-count x) 1))
    :returns (vals 4veclist-p)
    (if (atom x)
        nil
      (cons (svex-eval-svtv-phases (car x) phase data)
            (svexlist-eval-svtv-phases (cdr x) phase data))))
  ///

  (local (defthm consp-of-svexlist-eval-svtv-phases
           (equal (consp (svexlist-eval-svtv-phases x phase data))
                  (consp x))
           :hints (("goal" :expand ((svexlist-eval-svtv-phases x phase data))))))

  ;; (local (defthm len-of-svexlist-eval-svtv-phases
  ;;          (equal (len (svexlist-eval-svtv-phases x phase data))
  ;;                 (len x))
  ;;          :hints(("Goal" :in-theory (enable len)))))
  (local (in-theory (disable (tau-system))))

    (local (defthm upper-lower-of-3vec-fix
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm 4vec-?-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-? test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (equal test 0)
                         (equal (4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit?)))))

  (local (defthm 4vec-bit?!-cases
           (and (implies (equal (logand (4vec->upper test)
                                        (4vec->lower test))
                                0)
                         (equal (4vec-bit?! test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit?! test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit?!)))))

  (local (defthm 4vec-?*-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))

  (local (defthm 4vec-bitand-case
           (implies (equal test 0)
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand)))))

  (local (defthm 4vec-bitor-case
           (implies (equal test -1)
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor)))))

  (verify-guards svex-eval-svtv-phases
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply len 4veclist-nth-safe nth 4vec-?!)
                                  (svex-eval))
                  :expand ((svexlist-eval-svtv-phases (svex-call->args x) phase data)
                           (svexlist-eval-svtv-phases (cdr (svex-call->args x)) phase data)
                           (svexlist-eval-svtv-phases (cddr (svex-call->args x)) phase data))))))
  (memoize 'svex-eval-svtv-phases-call)

  (deffixequiv-mutual svex-eval-svtv-phases))






;; (defthm-svex-eval-svtv-phases-flag
;;   (defthm svex-eval-svtv-phases-correct
;;     (equal (svex-eval-svtv-phases x phase data)
;;            (b* (((svtv-evaldata data)))
;;              (svex-eval-unroll-multienv x phase data.nextstate data.inputs data.initst)))
;;     :hints ('(:expand ((svex-eval-svtv-phases x phase data)
;;                        (:free (ins initst nextstate phase) (svex-eval-unroll-multienv x phase nextstate ins initst)))))
;;     :flag svex-eval-svtv-phases)
;;   (defthm svex-eval-svtv-phases-call-correct
;;     (implies (svex-case x :call)
;;              (equal (svex-eval-svtv-phases-call x phase data)
;;                     (b* (((svtv-evaldata data)))
;;                       (svex-eval-unroll-multienv x phase data.nextstate data.inputs data.initst))))
;;     :hints ('(:expand ((svex-eval-svtv-phases-call x phase data)
;;                        (:free (ins initst nextstate phase) (svex-eval-unroll-multienv x phase nextstate ins initst))))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable svex-eval))))
;;     :flag svex-eval-svtv-phases-call)
;;   (defthm svexlist-eval-svtv-phases-correct
;;     (equal (svexlist-eval-svtv-phases x phase data)
;;            (b* (((svtv-evaldata data)))
;;              (svexlist-eval-unroll-multienv x phase data.nextstate data.inputs data.initst)))
;;     :hints ('(:expand ((svexlist-eval-svtv-phases x phase data)
;;                        (:free (nextstate ins initst) (svexlist-eval-unroll-multienv x phase nextstate ins initst)))))
;;     :flag svexlist-eval-svtv-phases))
