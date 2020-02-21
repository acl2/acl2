
; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "svexl")

(acl2::defines
 svexl-fasteval-aux
 :flag-local nil
 :flag-defthm-macro defthm-svexl-fasteval-aux
 :prepwork
 ((local
   (in-theory (e/d (svexl-node-kind
                    svex-env-fastlookup-wog
                    sv::svexlist-p
                    svexl-node-p
                    svexl-node-alist-p
                    sv::svex-p)
                   ())))
  (local
   (defthm lemma1
     (implies (and (node-env-p node-env)
                   (hons-assoc-equal x node-env))
              (4vec-p (cdr (hons-assoc-equal x node-env))))
     :hints (("goal"
              :in-theory (e/d (node-env-p) ())))))

  (local
   (defthm lemma2
     (implies (and (node-env-p rest)
                   (natp key)
                   (4vec-p val))
              (node-env-p (cons (cons key val)
                                rest)))
     :hints (("Goal"
              :in-theory (e/d (node-env-p) ()))))))

 (define svexl-fasteval-aux ((x svexl-node-p)
                             (nodes-alist svexl-node-alist-p)
                             (node-env node-env-p)
                             (env sv::svex-env-p)
                             (limit natp))
   :measure (nfix limit)
   :verify-guards nil
   :returns (mv (res sv::4vec-p :hyp (and (svexl-node-p x)
                                          (svexl-node-alist-p nodes-alist)
                                          (node-env-p node-env)
                                          (sv::svex-env-p env)))
                (new-node-env  node-env-p :hyp (and (svexl-node-p x)
                                                    (svexl-node-alist-p nodes-alist)
                                                    (node-env-p node-env)
                                                    (sv::svex-env-p env)))
                (valid booleanp))
   (if (zp limit)
       (mv (sv::4vec-x) node-env nil)
     (svexl-node-case
      x
      :var (mv (svex-env-fastlookup-wog x.name env) node-env t)
      :quote (mv x.val node-env t)
      :node (b* ((node-env-entry (hons-get x.node-id node-env))
                 ((when node-env-entry)
                  (mv (cdr node-env-entry) node-env t))
                 (node-entry (hons-get x.node-id nodes-alist))
                 ((mv val node-env valid)
                  (if node-entry
                      (svexl-fasteval-aux (cdr node-entry)
                                          nodes-alist
                                          node-env
                                          env
                                          (1- limit))
                    (mv (sv::4vec-x) node-env t))))
              (mv val (hons-acons x.node-id val node-env) valid))
      :call
      (b* (((mv args node-env valid)
            (svexllist-fasteval-aux x.args nodes-alist node-env env (1- limit))))
        (mv (sv::svex-apply x.fn args) node-env valid)))))

 (define svexllist-fasteval-aux ((lst svexl-nodelist-p)
                                 (nodes-alist svexl-node-alist-p)
                                 (node-env node-env-p)
                                 (env sv::svex-env-p)
                                 (limit natp))
   :returns (mv (res sv::4veclist-p :hyp (and (svexl-nodelist-p lst)
                                              (svexl-node-alist-p nodes-alist)
                                              (node-env-p node-env)
                                              (sv::svex-env-p env)))
                (new-node-env  node-env-p :hyp (and (svexl-nodelist-p lst)
                                                    (svexl-node-alist-p nodes-alist)
                                                    (node-env-p node-env)
                                                    (sv::svex-env-p env)))
                (valid booleanp))
   :measure (nfix limit)
   (cond
    ((zp limit)
     (mv nil node-env nil))
    ((atom lst)
     (mv nil node-env t))
    (t 
     (b* (((mv cur node-env valid1)
           (svexl-fasteval-aux (car lst) nodes-alist node-env env (1- limit)))
          ((mv rest node-env valid2)
           (svexllist-fasteval-aux (cdr lst) nodes-alist node-env env (1- limit))))
       (mv (cons cur rest) node-env (and valid1 valid2))))))

 ///

 (verify-guards svexl-fasteval-aux))

(define svexl-fasteval ((svexl svexl-p)
                        (env sv::svex-env-p))
  (b* (((svexl svexl) svexl)
       (svexl.node-alist (make-fast-alist svexl.node-alist))
       ((mv res node-env valid)
        (svexl-fasteval-aux svexl.top-node
                            svexl.node-alist
                            nil
                            env
                            (expt 2 50)))
       (- (fast-alist-free node-env))
       (- (fast-alist-free svexl.node-alist)))
    (if valid
        res
      (progn$
       (hard-error 'svexl-fasteval
                   "Somehow the limit for svexl-fasteval-aux is exhausted! ~%"
                   nil)
       (svexl-eval svexl env)))))


(define svexllist-fasteval ((svexllist svexllist-p)
                            (env sv::svex-env-p))
  (b* (((svexllist svexllist) svexllist)
       (svexllist.node-alist (make-fast-alist svexllist.node-alist))
       ((mv res node-env valid)
        (svexllist-fasteval-aux svexllist.top-nodelist
                                svexllist.node-alist
                                nil
                                env
                                (expt 2 50)))
       (- (fast-alist-free node-env))
       (- (fast-alist-free svexllist.node-alist)))
    (if valid
        res
      (progn$
       (hard-error 'svexl-fasteval
                   "Somehow the limit for svexl-fasteval-aux is exhausted! ~%"
                   nil)
       (svexllist-eval svexllist env)))))
