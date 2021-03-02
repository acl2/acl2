; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
;                   Jared Davis <jared@centtech.com>

(in-package "SV")

(include-book "../svex/unroll")
(include-book "../svex/rewrite")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defthm svex-alist-p-of-nth
  (implies (svex-alistlist-p x)
           (svex-alist-p (nth n x)))
  :hints(("Goal" :in-theory (enable svex-alistlist-p nth))))



(deffixcong svex-alistlist-equiv svex-alist-equiv (nth n x) x
  :hints(("Goal" :in-theory (enable svex-alistlist-fix nth))))

(defprod svtv-composedata
  ((rewrite booleanp)
   (nextstates svex-alist-p)
   (input-substs svex-alistlist-p)
   (initst svex-alist-p))
  :layout :tree)


(defines svex-compose-svtv-phases
  (define svex-compose-svtv-phases ((x svex-p)
                                    (phase natp)
                                    (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 1))
    :returns (new-x svex-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x
        :var (b* (((svtv-composedata data))
                  (look (svex-fastlookup x.name data.nextstates))
                  ((when look)
                   ;; state var
                   (if (zp phase)
                       (b* ((look (svex-fastlookup x.name data.initst)))
                         (or look (svex-x)))
                     (svex-compose-svtv-phases look (1- phase) data))))
               ;; input var
               (b* ((inalist (nth phase (svex-alistlist-fix data.input-substs)))
                    (look (svex-fastlookup x.name inalist)))
                 (or look (svex-x)
                     ;; (svex-var (svex-phase-var x.name phase))
                     )))
        :call (svex-compose-svtv-phases-call x phase data))))

  (define svex-compose-svtv-phases-call ((x svex-p)
                                         (phase natp)
                                         (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 0))
    :returns (new-x svex-p)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) (svex-fix x))
         ((svex-call x))
         (args (svexlist-compose-svtv-phases x.args phase data)))
      (if (svtv-composedata->rewrite data)
          (svex-rewrite-fncall 1000 -1 x.fn args t t)
        (svex-call x.fn args))))

  (define svexlist-compose-svtv-phases ((x svexlist-p)
                                        (phase natp)
                                        (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svexlist-count x) 1))
    :returns (new-x svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose-svtv-phases (car x) phase data)
            (svexlist-compose-svtv-phases (cdr x) phase data))))
  ///
  (verify-guards svex-compose-svtv-phases)
  (memoize 'svex-compose-svtv-phases-call)

  (defthm-svex-compose-svtv-phases-flag
    (defthm svex-compose-svtv-phases-correct
      (equal (svex-eval (svex-compose-svtv-phases x phase data) env)
             (b* (((svtv-composedata data)))
               (svex-eval-unroll-multienv x phase data.nextstates
                                          (svex-alistlist-eval data.input-substs env)
                                          (svex-alist-eval data.initst env))))
      :hints ('(:expand ((svex-compose-svtv-phases x phase data)
                         (:free (ins initst nextstates phase) (svex-eval-unroll-multienv x phase nextstates ins initst))))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable svex-eval)))
              )
      :flag svex-compose-svtv-phases)
    (defthm svex-compose-svtv-phases-call-correct
      (implies (svex-case x :call)
               (equal (svex-eval (svex-compose-svtv-phases-call x phase data) env)
                      (b* (((svtv-composedata data)))
                        (svex-eval-unroll-multienv x phase data.nextstates
                                                   (svex-alistlist-eval data.input-substs env)
                                                   (svex-alist-eval data.initst env)))))
      :hints ('(:expand ((svex-compose-svtv-phases-call x phase data)
                         (:free (ins initst nextstates phase) (svex-eval-unroll-multienv x phase nextstates ins initst))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-eval))))
      :flag svex-compose-svtv-phases-call)
    (defthm svexlist-compose-svtv-phases-correct
      (equal (svexlist-eval (svexlist-compose-svtv-phases x phase data) env)
             (b* (((svtv-composedata data)))
               (svexlist-eval-unroll-multienv x phase data.nextstates
                                          (svex-alistlist-eval data.input-substs env)
                                          (svex-alist-eval data.initst env))))
      :hints ('(:expand ((svexlist-compose-svtv-phases x phase data)
                         (:free (nextstates ins initst) (svexlist-eval-unroll-multienv x phase nextstates ins initst)))))
      :flag svexlist-compose-svtv-phases))

  (deffixequiv-mutual svex-compose-svtv-phases))

(define svex-alist-compose-svtv-phases ((x svex-alist-p)
                                        (phase natp)
                                        (data svtv-composedata-p))
  :returns (new-x svex-alist-p)
  :hooks nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (cons (caar x) (svex-compose-svtv-phases (cdar x) phase data))
              (svex-alist-compose-svtv-phases (cdr x) phase data))
      (svex-alist-compose-svtv-phases (cdr x) phase data)))
  ///
  (defretd svex-alist-compose-svtv-phases-correct
    (equal new-x
           (pairlis$ (svex-alist-keys x)
                     (svexlist-compose-svtv-phases (svex-alist-vals x) phase data)))
    :hints(("Goal" :in-theory (enable svexlist-compose-svtv-phases svex-alist-keys svex-alist-vals))))

  (deffixequiv svex-alist-compose-svtv-phases :hints(("Goal" :in-theory (enable svex-alist-fix)))))





