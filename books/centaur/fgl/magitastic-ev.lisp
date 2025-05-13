; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(local (std::add-default-post-define-hook :fix))


(define magitastic-ev-override-definition ((fn pseudo-fnsym-p) state)
  :returns (mv ok
               (formals symbol-listp)
               (body pseudo-termp))
  :prepwork ((local (in-theory (disable pseudo-termp symbol-listp pseudo-term-listp))))
  (b* ((tab (table-alist 'magitastic-ev-definitions (w state)))
       (fn (pseudo-fnsym-fix fn))
       (look (cdr (hons-assoc-equal fn tab)))
       ((when (and (eql (len look) 2)
                   (symbol-listp (first look))
                   (pseudo-termp (second look))))
        (mv t (first look) (second look))))
    (mv nil nil nil)))

(define magitastic-ev-definition ((fn pseudo-fnsym-p) state)
  :returns (mv ok
               (formals symbol-listp)
               (body pseudo-termp))
  :prepwork ((local (in-theory (disable pseudo-termp symbol-listp pseudo-term-listp))))
  (b* ((fn (pseudo-fnsym-fix fn))
       ((mv ok formals body) (acl2::fn-get-def fn state))
       ((unless (and ok (pseudo-termp body)))
        (mv nil nil nil)))
    (mv t formals body)))



(defines magitastic-ev
  (define magitastic-ev ((x pseudo-termp)
                         (alist symbol-alistp)
                         (reclimit natp)
                         state hard-errp aokp)
    :well-founded-relation acl2::nat-list-<
    :measure (list reclimit (pseudo-term-count x))
    :returns (mv errmsg val)
    :verify-guards nil
    (pseudo-term-case x
      :const (mv nil x.val)
      :var (mv nil (cdr (hons-assoc-equal x.name alist)))
      :lambda (b* (((mv err args)
                    (magitastic-ev-list x.args alist reclimit state hard-errp aokp))
                   ((when err) (mv err nil)))
                (magitastic-ev x.body
                               (pairlis$ x.formals args)
                               reclimit state hard-errp aokp))
      :fncall (b* (((when (and** (eq x.fn 'if) (eql (len x.args) 3)))
                    (b* (((mv err test) (magitastic-ev (first x.args) alist reclimit state hard-errp aokp))
                         ((when err) (mv err nil)))
                      (if test
                          (magitastic-ev (second x.args) alist reclimit state hard-errp aokp)
                        (magitastic-ev (third x.args) alist reclimit state hard-errp aokp))))
                   ((when (and** (eq x.fn 'return-last) (eql (len x.args) 3)))
                    (b* ((arg1 (first x.args)))
                      (prog2$
                       (pseudo-term-case arg1
                         :const (and (eq arg1.val 'progn)
                                     (b* (((mv ?err ?arg1)
                                           (magitastic-ev (second x.args) alist reclimit state hard-errp aokp)))
                                       nil))
                         :otherwise nil)
                       (magitastic-ev (third x.args) alist reclimit state hard-errp aokp))))
                   ((mv err args) (magitastic-ev-list x.args alist reclimit state hard-errp aokp))
                   ((when err) (mv err nil)))
                (magitastic-ev-fncall x.fn args reclimit state hard-errp aokp))))

  (define magitastic-ev-fncall ((fn pseudo-fnsym-p)
                                (args true-listp)
                                (reclimit natp)
                                state hard-errp aokp)
    :measure (list reclimit 0)
    :returns (mv errmsg val)
    (b* (((mv ovr-ok formals body)
          (magitastic-ev-override-definition fn state))
         ((when ovr-ok)
          (b* (((unless (eql (len formals) (len args)))
                (mv (msg "Wrong arity for ~x0 call" (pseudo-fnsym-fix fn)) nil))
               ((when (zp reclimit))
                (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil)))
            (magitastic-ev body (pairlis$ formals args) (1- reclimit) state hard-errp aokp)))
         ((mv ev-err val)
          (acl2::magic-ev-fncall (pseudo-fnsym-fix fn)
                                 (mbe :logic (true-list-fix args)
                                      :exec args)
                                 state hard-errp aokp))
         ((unless ev-err) (mv nil val))
         ((mv def-ok formals body) (magitastic-ev-definition fn state))
         ((unless def-ok)
          (mv (msg "No definition for ~x0" (pseudo-fnsym-fix fn)) nil))
         ((unless (eql (len formals) (len args)))
          (mv (msg "Wrong arity for ~x0 call" (pseudo-fnsym-fix fn)) nil))
         ((when (zp reclimit))
          (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil)))
      (magitastic-ev body (pairlis$ formals args) (1- reclimit) state hard-errp aokp)))

  (define magitastic-ev-list ((x pseudo-term-listp)
                              (alist symbol-alistp)
                              (reclimit natp)
                              state hard-errp aokp)
    :measure (list reclimit (pseudo-term-list-count x))
    :returns (mv errmsg (vals true-listp))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv err first) (magitastic-ev (car x) alist reclimit state hard-errp aokp))
         ((when err) (mv err nil))
         ((mv err rest) (magitastic-ev-list (cdr x) alist reclimit state hard-errp aokp))
         ((when err) (mv err nil)))
      (mv nil (cons first rest))))
  ///
  (verify-guards magitastic-ev)

  (local (in-theory (disable magitastic-ev magitastic-ev-list magitastic-ev-fncall
                             pseudo-term-listp pseudo-termp)))

  (fty::deffixequiv-mutual magitastic-ev))
