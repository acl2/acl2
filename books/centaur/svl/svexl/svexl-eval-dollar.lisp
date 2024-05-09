
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

(include-book "../svex-eval-dollar-wog")
(include-book "svexl")

(acl2::defines
  svexl-node-eval$
  :flag-local nil
  :flag-defthm-macro defthm-svexl-node-eval$
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-kind
                     svex-env-fastlookup-wog
                     sv::svexlist-p
                     svexl-node-p
                     svexl-node-array-p
                     sv::svex-p)
                    ())))
   (local
    (defthm lemma1
      (implies (and (node-env-p node-env)
                    (hons-assoc-equal x node-env))
               (4vec-p (cdr (hons-assoc-equal x node-env))))
      :hints (("goal"
               :in-theory (e/d (node-env-p) ()))))))

  (define svexl-node-eval$ ((x svexl-node-p)
                            (node-env node-env-p)
                            (env sv::svex-env-p))
    :measure (svexl-node-count x)
    :verify-guards nil
    :returns (res sv::4vec-p :hyp (and (svexl-node-p x)
                                       (node-env-p node-env)
                                       (sv::svex-env-p env)))
    (svexl-node-case
     x
     :var (sv::svex-env-fastlookup x.name env)
     :quote x.val
     :node (svex-env-fastlookup-wog x.node-id node-env)
     :call (sv::svex-apply$
            x.fn
            (svexl-nodelist-eval$ x.args
                                  node-env
                                  env))))

  (define svexl-nodelist-eval$ ((lst svexl-nodelist-p)
                                (node-env node-env-p)
                                (env sv::svex-env-p))
    :returns (res sv::4veclist-p :hyp (and (svexl-nodelist-p lst)
                                           (node-env-p node-env)
                                           (sv::svex-env-p env)))
    :measure (svexl-nodelist-count lst)
    (if (atom lst)
        nil
      (cons (svexl-node-eval$ (car lst) node-env env)
            (svexl-nodelist-eval$ (cdr lst) node-env env))))

  ///

  (verify-guards svexl-node-eval$))



(define svexl-node-alist-eval$ ((alist svexl-node-alist-p)
                               (node-env node-env-p)
                               (env sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (svexl-node-alist-p alist)
                                         (node-env-p node-env)
                                         (sv::svex-env-p env)))
  (if (atom alist)
      nil
    (acons (caar alist)
           (svexl-node-eval$ (cdar alist)
                            node-env env)
           (svexl-node-alist-eval$ (cdr alist)
                                  node-env
                                  env))))


(define svexl-eval$-aux ((x svexl-node-array-p)
                        (node-env node-env-p)
                        (env sv::svex-env-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-array-p
                     node-env-p)
                    ()))))
  :returns (res-node-env node-env-p :hyp (and (svexl-node-array-p x)
                                              (node-env-p node-env)
                                              (sv::svex-env-p env)))
  (if (atom x)
      node-env
      (b* ((node-id (caar x))
           (node (cdar x))
           (eval-res (svexl-node-eval$ node node-env env)))
        (svexl-eval$-aux (cdr x)
                        (hons-acons node-id eval-res node-env)
                        env)))
  ///
  (verify-guards svexl-eval$-aux))

(define svexl-eval$ ((x svexl-p)
                    (env sv::svex-env-p))
  :returns (res sv::4vec-p :hyp (and (svexl-p x)
                                     (sv::svex-env-p env)))
  (b* ((node (svexl->top-node x))
       (node-array (svexl->node-array x))
       (node-env (svexl-eval$-aux node-array nil env))
       (res (svexl-node-eval$ node node-env env))
       (- (fast-alist-free node-env)))
    res))

(define svexllist-eval$ ((x svexllist-p)
                        (env sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (svexllist-p x)
                                         (sv::svex-env-p env)))
  (b* ((node-lst (svexllist->top-nodelist x))
       (node-array (svexllist->node-array x))
       (node-env (svexl-eval$-aux node-array nil env))
       (res (svexl-nodelist-eval$ node-lst node-env env))
       (- (fast-alist-free node-env)))
    res))

(define svexl-alist-eval$ ((x svexl-alist-p)
                          (env sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (svexl-alist-p x)
                                         (sv::svex-env-p env)))
  (b* ((top-node-alist (svexl-alist->top-node-alist x))
       (node-array (svexl-alist->node-array x))
       (node-env (svexl-eval$-aux node-array nil env))
       (res (svexl-node-alist-eval$ top-node-alist node-env env))
       (- (fast-alist-free node-env)))
    res))




;; Example:
#|
(b* ((svex #!SV'(bitor (bitand (binary-logior a b)
                               (bitor (binary-logior a b)
                                      (binary-logior a b)))
                       (bitor (binary-logior a b)
                              (binary-logior a b))))
     (env (make-fast-alist #!SV`((a . 12312321) (b . 331312312))))
     (svexl (svex-to-svexl svex)))
  `((svex-eval$$ ,(sv::svex-eval$$ svex env))
    (svexl-eval$$ ,(svexl-eval$$ svexl env))
    (svexl ,svexl)))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Eval functions without guards:


(acl2::defines
    svexl-node-eval$-wog
    :flag-local nil
    :flag-defthm-macro defthm-svexl-node-eval$-wog
    :prepwork
    ((local
      (in-theory (e/d (svexl-node-kind
                       sv::svexlist-p
                       svexl-node-p
                       svexl-node-array-p
                       svexl-node-kind-wog-is-svexl-node-kind
                       sv::svex-p)
                      ()))))
    (define svexl-node-eval$-wog ((x)
                                 (node-env)
                                 (env))
      :measure (acl2-count x)
      :verify-guards nil
      (b* ((kind (svexl-node-kind-wog x)))
        (cond ((eq kind :var)
               (svex-env-fastlookup-wog x env))
              ((eq kind :quote) x)
              ((eq kind :node)
               (svex-env-fastlookup-wog (cadr x) node-env))
              (t
               (b* ((x.fn (car x))
                    (x.args (cdr x)))
                 (svex-apply$-wog
                  x.fn
                  (svexl-nodelist-eval$-wog x.args node-env env)))))))

    (define svexl-nodelist-eval$-wog ((lst)
                                     (node-env)
                                     (env))
      :measure (acl2-count lst)
      (if (atom lst)
          nil
          (cons (svexl-node-eval$-wog (car lst) node-env env)
                (svexl-nodelist-eval$-wog (cdr lst) node-env env))))

    ///

    ;; openers:
    (def-rp-rule svexl-eval$-node-of-var
        (implies (eq (svexl-node-kind-wog x) ':var)
                 (equal (svexl-node-eval$-wog x node-env env-wires)
                        (let ((entry (hons-get x env-wires)))
                          (if entry (cdr entry)
                              (sv::4vec-x)))))
      :hints (("goal"
               :expand (svexl-node-eval$-wog x node-env env-wires)
               :in-theory (e/d (svex-env-fastlookup-wog) ()))))

    (def-rp-rule svexl-eval$-node-of-node
        (implies (eq (svexl-node-kind-wog x) ':node)
                 (equal (svexl-node-eval$-wog x node-env env-wires)
                        (let ((entry (hons-get (cadr x) node-env)))
                          (if entry (cdr entry)
                              (sv::4vec-x)))))
      :hints (("goal"
               :expand (svexl-node-eval$-wog x node-env env-wires)
               :in-theory (e/d (svex-env-fastlookup-wog) ()))))

    (def-rp-rule svexl-eval$-node-of-quoted
        (implies (eq (svexl-node-kind-wog x) ':quote)
                 (equal (svexl-node-eval$-wog x node-env env-wires)
                        x))
      :hints (("goal"
               :expand (svexl-node-eval$-wog x node-env env-wires)
               :in-theory (e/d (svex-env-fastlookup-wog) ()))))

    (def-rp-rule svexl-eval$-node-of-call
        (implies (eq (svexl-node-kind-wog x) ':call)
                 (equal (svexl-node-eval$-wog x node-env env)
                        (svex-apply$-wog
                         (car x)
                         (svexl-nodelist-eval$-wog (cdr x) node-env env))))
      :hints (("goal"
               :expand (svexl-node-eval$-wog x node-env env)
               :in-theory (e/d (svex-env-fastlookup-wog) ()))))

    (def-rp-rule svexl-nodelist-eval$-wog-of-cons
        (equal (svexl-nodelist-eval$-wog (cons x rest) node-env env)
               (cons (svexl-node-eval$-wog x node-env env)
                     (svexl-nodelist-eval$-wog rest node-env env)))
      :hints (("Goal"
               :expand (svexl-nodelist-eval$-wog (cons x rest) node-env env)
               :in-theory (e/d () ()))))

    (def-rp-rule svexl-nodelist-eval$-wog-of-nil
        (equal (svexl-nodelist-eval$-wog nil node-env env)
               nil)
      :hints (("Goal"
               :expand (svexl-nodelist-eval$-wog nil node-env env)
               :in-theory (e/d () ()))))

    (verify-guards svexl-node-eval$-wog))

(define svexl-node-alist-eval$-wog ((alist alistp)
                                   (node-env)
                                   (env))
  :measure (acl2-count alist)
  (if (atom alist)
      nil
      (acons
       (caar alist)
       (svexl-node-eval$-wog (cdar alist) node-env env)
       (svexl-node-alist-eval$-wog (cdr alist) node-env env)))
  ///
  (def-rp-rule svexl-node-alist-eval$-wog-of-cons
      (equal (svexl-node-alist-eval$-wog (cons x rest) node-env env)
             (acons
              (car x)
              (svexl-node-eval$-wog (cdr x) node-env env)
              (svexl-node-alist-eval$-wog rest node-env env)))
    :hints (("Goal"
             :expand (svexl-node-alist-eval$-wog (cons x rest) node-env env)
             :in-theory (e/d () ()))))

  (def-rp-rule svexl-node-alist-eval$-wog-of-nil
      (equal (svexl-node-alist-eval$-wog nil node-env env)
             nil)
    :hints (("Goal"
             :expand (svexl-node-alist-eval$-wog nil node-env env)
             :in-theory (e/d () ()))))
  )

(defthm-svexl-node-eval$-wog
    (defthm svexl-node-eval$-is-svexl-node-eval$-wog
        (implies (and (svexl-node-p x)
                      (sv::svex-env-p env))
                 (equal (svexl-node-eval$ x node-env env)
                        (svexl-node-eval$-wog x node-env env)))
      :flag svexl-node-eval$-wog)
    (defthm svexl-nodelist-eval$-is-svexl-nodelist-eval$-wog
        (implies (and (svexl-nodelist-p lst)
                      (sv::svex-env-p env))
                 (equal (svexl-nodelist-eval$ lst node-env env)
                        (svexl-nodelist-eval$-wog lst node-env env)))
      :flag svexl-nodelist-eval$-wog)
  :hints (("goal"
           :expand ((svexl-node-eval$ x node-env env))
           :in-theory (e/d (svex-call->fn
                            svexl-nodelist-fix
                            svexl-node-var->name
                            svexl-node-quote->val
                            svexl-node-call->args
                            svexl-nodelist-p
                            svexl-node-call->fn
                            svexl-node-node->node-id
                            svexl-node-p
                            svex-kind
                            svex-env-fastlookup-wog
                            svex-eval$-wog
                            SVEX-APPLY$-IS-SVEX-APPLY$-WOG
                            svex-env-lookup-is-svex-env-fastlookup-wog
                            svexl-node-kind-wog-is-svexl-node-kind
                            svexlist-eval$-wog
                            svexl-node-eval$
                            svexl-node-kind
                            svexl-node-eval$-wog
                            svex-p
                            sv::svar-p
                            svex-eval$
                            svex-var->name
                            sv::svex-quote->val
                            svex-call->args
                            svexl-nodelist-eval$
                            svexl-nodelist-eval$-wog)
                           ()))))

(rp::add-rp-rule svexl-node-eval$-is-svexl-node-eval$-wog)
(rp::add-rp-rule svexl-nodelist-eval$-is-svexl-nodelist-eval$-wog)

(def-rp-rule svexl-node-alist-eval$-is-svexl-node-alist-eval$-wog
    (implies (and (svexl-node-alist-p alist)
                  (sv::svex-env-p env))
             (equal (svexl-node-alist-eval$ alist node-env env)
                    (svexl-node-alist-eval$-wog alist node-env env)))
  :hints (("Goal"
           :in-theory (e/d (svexl-node-alist-eval$
                            svexl-node-alist-p
                            svexl-node-alist-eval$-wog)
                           ()))))

(define svexl-eval$-aux-wog ((x alistp)
                            (node-env)
                            (env))
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-array-p
                     node-env-p)
                    ()))))
  (if (atom x)
      node-env
    (b* ((node-id (caar x))
         (node (cdar x))
         (eval-res (svexl-node-eval$-wog node node-env env)))
      (svexl-eval$-aux-wog (cdr x)
                          (hons-acons node-id eval-res node-env)
                          env)))
  ///

  (def-rp-rule :disabled-for-acl2 t
    svexl-eval$-aux-is-svexl-eval$-aux-wog
    (implies (and (svexl-node-array-p x)
                  (sv::svex-env-p env))
             (equal (svexl-eval$-aux x node-env env)
                    (svexl-eval$-aux-wog x node-env env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-eval$-aux
                              svexl-eval$-aux-wog) ()))))

  (def-rp-rule
    svexl-eval$-aux-wog-cons
    (equal (svexl-eval$-aux-wog (cons (cons node-id node) rest) node-env env)
           (b* ((eval-res (svexl-node-eval$-wog node node-env env)))
             (svexl-eval$-aux-wog rest
                                 (hons-acons node-id eval-res node-env)
                                 env))))

  (def-rp-rule
    svexl-eval$-aux-wog-nil
    (equal (svexl-eval$-aux-wog nil node-env env)
           node-env)))

(define svexl-eval$-wog ((x)
                        (env))
  :verify-guards nil
  (b* ((node (cdar x))
       (node-array (cdr (cadr x)))
       (node-env (svexl-eval$-aux-wog node-array nil env))
       (res (svexl-node-eval$-wog node node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///

  (def-rp-rule :disabled-for-acl2 t
    svexl-eval$-is-svexl-eval$-wog
    (implies (and (svexl-p x)
                  (sv::svex-env-p env))
             (equal (svexl-eval$ x env)
                    (svexl-eval$-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-eval$
                              svexl->top-node
                              svexl->node-array
                              svexl-p
                              svexl-eval$-wog
                              SVEXL-EVAL$-AUX-IS-SVEXL-EVAL$-AUX-WOG)
                             ()))))

  (defthmd svexl-eval$-wog-is-svexl-eval$
      (implies (and (svexl-p x)
                    (sv::svex-env-p env))
               (equal (svexl-eval$-wog x env)
                      (svexl-eval$ x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-eval$-is-svexl-eval$-wog)
                             ()))))

  (set-ignore-ok t)
  (add-rp-rule svexl-eval$-wog :lambda-opt t))

(define svexllist-eval$-wog ((x)
                            (env))
  :verify-guards nil
  (b* ((node-lst (cdr (car x)))
       (node-array (cdr (cadr x)))
       (node-env (svexl-eval$-aux-wog node-array nil env))
       (res (svexl-nodelist-eval$-wog node-lst node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///
  (def-rp-rule :disabled-for-acl2 t
    svexllist-eval$-is-svexllist-eval$-wog
    (implies (and (svexllist-p x)
                  (sv::svex-env-p env))
             (equal (svexllist-eval$ x env)
                    (svexllist-eval$-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexllist-eval$
                              SVEXLLIST->TOP-NODELIST
                              SVEXLLIST->NODE-ARRAY
                              SVEXLLIST-P
                              svexllist-eval$-wog
                              SVEXL-EVAL$-AUX-IS-SVEXL-EVAL$-AUX-WOG)
                             ()))))
  (set-ignore-ok t)
  (add-rp-rule svexllist-eval$-wog :lambda-opt t))

(define svexl-alist-eval$-wog ((x)
                              (env))
  :verify-guards nil
  (b* ((top-node-alist (cdar x))
       (node-array (cdr (cadr x)))
       (- (cw "Now rewriting svexl-alist (~p0 nodes) for eval$... ~%"
              (len node-array)))
       
       (node-env (svexl-eval$-aux-wog node-array nil env))
       (res (svexl-node-alist-eval$-wog top-node-alist node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///
  (def-rp-rule :disabled-for-acl2 t
    svexl-alist-eval$-is-svexl-alist-eval$-wog
    (implies (and (svexl-alist-p x)
                  (sv::svex-env-p env))
             (equal (svexl-alist-eval$ x env)
                    (svexl-alist-eval$-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-alist-eval$
                              SVEXL-ALIST-P
                              SVEXL-ALIST->NODE-ARRAY
                              svexl-alist-eval$-wog
                              SVEXL-ALIST->TOP-NODE-ALIST
                              svexl-node-alist-eval$-is-svexl-node-alist-eval$-wog
                              SVEXL-EVAL$-AUX-IS-SVEXL-EVAL$-AUX-WOG)
                             ()))))
  (set-ignore-ok t)
  (add-rp-rule svexl-alist-eval$-wog :lambda-opt t))

