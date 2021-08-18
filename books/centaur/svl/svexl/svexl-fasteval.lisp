
; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "svexl")

(define equal-len (lst (size natp))
  (if (zp size)
      (atom lst)
      (and (not (atom lst))
           (equal-len (cdr lst)
                      (1- size))))
  ///
  (defthm equal-len-opener
      (implies (not (zp size))
               (equal (equal-len lst size)
                      (and (not (atom lst))
                           (equal-len (cdr lst)
                                      (1- size))))))

  (defthm equal-len-opener-size-0
      (implies t
               (equal (equal-len lst 0)
                      (atom lst)))))
        



(defines
    svexl-fasteval-aux
    :flag-local nil
    :flag-defthm-macro defthm-svexl-fasteval-aux
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
                 :in-theory (e/d (node-env-p) ())))))

     (local
      (defthm lemma2
          (implies (and (node-env-p rest)
                        (natp key)
                        (4vec-p val))
                   (node-env-p (cons (cons key val)
                                     rest)))
        :hints (("Goal"
                 :in-theory (e/d (node-env-p) ())))))

     (local
      (defthm lemma3
          (implies (and (SVEXL-NODELIST-P lst))
                   (and (implies (consp (cdr lst)) (SVEXL-NODE-P (CADR lst)))
                        (implies (consp (cddr lst)) (SVEXL-NODE-P (CADdR lst)))
                        (implies (consp lst) (SVEXL-NODE-P (CAR lst)))))))

     (local
      (defthm dummy-measure-lemma
          (and (IMPLIES (AND 
                         (NOT (ZP LIMIT))
                         (CONSP X)
                         (NOT (EQUAL (CAR X) :VAR))
                         (NOT (EQUAL (CAR X) :NODE))
                         (NOT (INTEGERP (CAR X)))
                         (NOT (CONSP (SVEXL-NODE-CALL->ARGS X))))
                        (not (EQUAL (SVEXL-NODE-COUNT X) 1)))
               (IMPLIES (AND 
                             (NOT (ZP LIMIT))
                             (CONSP X)
                             (NOT (EQUAL (CAR X) :VAR))
                             (NOT (CONSP (CDR X)))
                             (NOT (INTEGERP (CAR X)))
                             (NOT (CONSP (SVEXL-NODE-CALL->ARGS X))))
                        (not (EQUAL (SVEXL-NODE-COUNT X) 1)))
               (IMPLIES (AND 
                             (NOT (ZP LIMIT))
                             (CONSP X)
                             (NOT (EQUAL (CAR X) :VAR))
                             (CDDR X)
                             (NOT (INTEGERP (CAR X)))
                             (NOT (CONSP (SVEXL-NODE-CALL->ARGS X))))
                        (not (EQUAL (SVEXL-NODE-COUNT X) 1))))
        :hints (("Goal"
                 :in-theory (e/d (SVEXL-NODE-COUNT) ()))))))

    (define svexl-fasteval-aux ((x svexl-node-p)
                                (nodes-alist svexl-node-array-p)
                                (node-env node-env-p)
                                (env sv::svex-env-p)
                                (limit natp))
      :measure (acl2::nat-list-measure (list (nfix limit) (svexl-node-count x)))
      :verify-guards nil
      :returns (mv (res sv::4vec-p :hyp (and (svexl-node-p x)
                                             (svexl-node-array-p nodes-alist)
                                             (node-env-p node-env)
                                             (sv::svex-env-p env)))
                   (new-node-env node-env-p :hyp (and (svexl-node-p x)
                                                      (svexl-node-array-p nodes-alist)
                                                      (node-env-p node-env)
                                                      (sv::svex-env-p env))))
      (if (zp limit)
          (mv (sv::4vec-x) node-env)
          (svexl-node-case
           x
           :var (mv (svex-env-fastlookup-wog x.name env) node-env )
           :quote (mv x.val node-env )
           :node (b* ((node-env-entry (hons-get x.node-id node-env))
                      ((when node-env-entry)
                       (mv (cdr node-env-entry) node-env ))
                      (node-entry (hons-get x.node-id nodes-alist))
                      ((mv val node-env)
                       (if node-entry
                           (svexl-fasteval-aux (cdr node-entry)
                                               nodes-alist
                                               node-env
                                               env
                                               (1- limit))
                           (mv (sv::4vec-x) node-env))))
                   (mv val (hons-acons x.node-id val node-env)))
           :call
           (cond
             ((and (or (equal x.fn 'sv::?)
                       (equal x.fn 'sv::?*))
                   (equal-len x.args 3))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   (test (sv::3vec-fix test))
                   ((sv::4vec test))
                   ((when (eql test.upper 0))
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit))
                   ((when (not (eql test.lower 0)))
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))

                   ((mv then node-env )
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))
                       
                   ((mv else node-env )
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit)))
                (mv (case x.fn
                      (sv::? (sv::4vec-? test then else))
                      (sv::?* (sv::4vec-?* test then else)))
                    node-env)))
             ((and (equal x.fn 'sv::?!)
                   (equal-len x.args 3))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   ((sv::4vec test))
                   (testvec (logand test.upper test.lower))
                   ((when (eql testvec 0))
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit)))
                (svexl-fasteval-aux (second x.args) nodes-alist
                                    node-env env limit)))
             ((and (equal x.fn 'sv::bit?)
                   (equal-len x.args 3))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   ((when (eql test 0))
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit))
                   ((when (eql test -1))
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))
                   ((mv then node-env)
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))
                   ((mv else node-env)
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit)))
                (mv (sv::4vec-bit? test then else) node-env)))
             ((and (equal x.fn 'sv::bit?!)
                   (equal-len x.args 3))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   ((when (eql test -1))
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))
                   ((sv::4vec test))
                   ((when (eql (logand test.upper test.lower) 0))
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit))
                   ((mv then node-env)
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit))
                   ((mv else node-env)
                    (svexl-fasteval-aux (third x.args) nodes-alist
                                        node-env env limit)))
                (mv (sv::4vec-bit?! test then else) node-env)))
             ((and (equal x.fn 'sv::bitand)
                   (equal-len x.args 2))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   ((when (eql test 0))
                    (mv 0 node-env))
                   ((mv other node-env)
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit)))
                (mv (sv::4vec-bitand test other) node-env)))
             ((and (equal x.fn 'sv::bitor)
                   (equal-len x.args 2))
              (b* (((mv test node-env)
                    (svexl-fasteval-aux (first x.args) nodes-alist
                                        node-env env limit))
                   ((when (eql test -1))
                    (mv -1 node-env))
                   ((mv other node-env)
                    (svexl-fasteval-aux (second x.args) nodes-alist
                                        node-env env limit)))
                (mv (sv::4vec-bitor test other) node-env)))
             (t
              (b* (((mv args node-env)
                    (svexllist-fasteval-aux x.args nodes-alist node-env env limit)))
                (mv (sv::svex-apply x.fn args) node-env))))

           
           
           
           #|(mbe :logic
                (b* (((mv args node-env )
                      (svexllist-fasteval-aux x.args nodes-alist node-env env limit)))
                  (mv (sv::svex-apply x.fn args) node-env ))
                :exec
                )||#)))

    (define svexllist-fasteval-aux ((lst svexl-nodelist-p)
                                    (nodes-alist svexl-node-array-p)
                                    (node-env node-env-p)
                                    (env sv::svex-env-p)
                                    (limit natp))
      :returns (mv (res sv::4veclist-p :hyp (and (svexl-nodelist-p lst)
                                                 (svexl-node-array-p nodes-alist)
                                                 (node-env-p node-env)
                                                 (sv::svex-env-p env)))
                   (new-node-env  node-env-p :hyp (and (svexl-nodelist-p lst)
                                                       (svexl-node-array-p nodes-alist)
                                                       (node-env-p node-env)
                                                       (sv::svex-env-p env)))
                   )
      :measure (acl2::nat-list-measure (list (nfix limit) (svexl-nodelist-count lst)))
      (cond
        ((atom lst)
         (mv nil node-env ))
        (t
         (b* (((mv cur node-env )
               (svexl-fasteval-aux (car lst) nodes-alist node-env env limit))
              ((mv rest node-env )
               (svexllist-fasteval-aux (cdr lst) nodes-alist node-env env limit)))
           (mv (cons cur rest) node-env )))))

    ///


    (local
     (defthm svexllist-fasteval-aux-opener-when-consp
         (implies (and (consp lst)
                       (case-split (not (zp limit))))
                  (equal (SVEXLLIST-FASTEVAL-AUX lst
                                                 NODES-ALIST NODE-ENV ENV limit)
                         (b* (((mv cur node-env )
                               (svexl-fasteval-aux (car lst) nodes-alist node-env env limit))
                              ((mv rest node-env )
                               (svexllist-fasteval-aux (cdr lst) nodes-alist node-env env limit)))
                           (mv (cons cur rest) node-env ))))))

    #|(local
     (defret-mutual svexl-fasteval-aux-when-not-valid
         (defret svexl-fasteval-aux-when-not-valid
             (implies (not valid)
                      (equal new-node-env node-env))
           :fn svexl-fasteval-aux)
       (defret svexllist-fasteval-aux-when-not-valid
           (implies (not valid)
                    (equal new-node-env node-env))
         :fn svexllist-fasteval-aux)))||#


    #|(local
     (defthm stupid-lemma-1
         (equal (list (mv-nth 0 (svexl-fasteval-aux arg1 arg2 arg3
                                                    arg4 arg5))
                      (mv-nth 1 (svexl-fasteval-aux arg1 arg2 arg3
                                                    arg4 arg5)))
                (svexl-fasteval-aux arg1 arg2 arg3 arg4 arg5))
       :hints (("Goal"
                :expand ((svexl-fasteval-aux arg1 arg2 arg3 arg4 arg5))
                :in-theory (e/d () ())))))||#
        
    
    (verify-guards svexl-fasteval-aux
        :hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d (SVEXL-NODE-CALL->ARGS
                                  4VEC-?
                                  SV::3VEC-?
                                  equal-len
                                  sv::SVEX-APPLY)
                                 ())))))

(define svexl-alist-fasteval-aux ((alist svexl-node-alist-p)
                                  (nodes-alist svexl-node-array-p)
                                  (node-env node-env-p)
                                  (env sv::svex-env-p)
                                  (limit natp))
  :returns (mv (res sv::svex-env-p :hyp (and (svexl-node-alist-p alist)
                                             (svexl-node-array-p nodes-alist)
                                             (node-env-p node-env)
                                             (sv::svex-env-p env)))
               (new-node-env  node-env-p :hyp (and (svexl-node-alist-p alist)
                                                   (svexl-node-array-p nodes-alist)
                                                   (node-env-p node-env)
                                                   (sv::svex-env-p env))))
  :measure (nfix limit)
  :verify-guards :after-returns
  :prepwork ((local
              (defthm svex-env-p-implies-alistp
                  (implies (sv::svex-env-p env)
                           (alistp env)))))
  (cond
    ((zp limit)
     (mv nil node-env))
    ((atom alist)
     (mv nil node-env))
    (t
     (b* (((mv cur node-env)
           (svexl-fasteval-aux (cdar alist) nodes-alist node-env env (1- limit)))
          ((mv rest node-env)
           (svexl-alist-fasteval-aux (cdr alist) nodes-alist node-env env (1- limit))))
       (mv (acons (caar alist) cur rest) node-env)))))

(define svexl-fasteval ((svexl svexl-p)
                        (env sv::svex-env-p))
  :returns (res sv::4vec-p :hyp (and (svexl-p svexl)
                                     (sv::svex-env-p env)))
  (b* (((svexl svexl) svexl)
       (svexl.node-array (make-fast-alist svexl.node-array))
       ((mv res node-env)
        (svexl-fasteval-aux svexl.top-node
                            svexl.node-array
                            nil
                            env
                            (* (len svexl.node-array) 500)))
       (- (fast-alist-free node-env))
       (- (fast-alist-free svexl.node-array)))
    res))

(define svexllist-fasteval ((svexllist svexllist-p)
                            (env sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (svexllist-p svexllist)
                                         (sv::svex-env-p env)))
  (b* (((svexllist svexllist) svexllist)
       (svexllist.node-array (make-fast-alist svexllist.node-array))
       ((mv res node-env)
        (svexllist-fasteval-aux svexllist.top-nodelist
                                svexllist.node-array
                                nil
                                env
                                (* (len svexllist.node-array) 500)))
       (- (fast-alist-free node-env))
       (- (fast-alist-free svexllist.node-array)))
    res))

(define svexl-alist-fasteval ((svexl-alist svexl-alist-p)
                              (env sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (svexl-alist-p svexl-alist)
                                         (sv::svex-env-p env)))
  (b* (((svexl-alist svexl-alist) svexl-alist)
       (svexl-alist.node-array (make-fast-alist svexl-alist.node-array))
       ((mv res node-env)
        (svexl-alist-fasteval-aux svexl-alist.top-node-alist
                                  svexl-alist.node-array
                                  nil
                                  env
                                  (* (len svexl-alist.node-array) 500)))
       (- (fast-alist-free node-env))
       (- (fast-alist-free svexl-alist.node-array)))
    res))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; wog definitions.



(defines
    svexl-fasteval-aux-wog
    :flag-local nil
    :flag-defthm-macro defthm-svexl-fasteval-aux-wog
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

    (define svexl-fasteval-aux-wog ((x)
                                    (nodes-alist)
                                    (node-env)
                                    (env)
                                    (limit natp))
      :measure (nfix limit)
      :verify-guards nil
      :returns (mv res new-node-env)
      (if (zp limit)
          (mv (sv::4vec-x) node-env)

          (b* ((kind (svexl-node-kind-wog x)))
            (cond ((eq kind :var)
                   (mv (svex-env-fastlookup-wog x env) node-env))
                  ((eq kind :quote) (mv x node-env))
                  ((eq kind :node)
                   (b* ((x.node-id (cadr x)) 
                        (node-env-entry (hons-get x.node-id node-env))
                        ((when node-env-entry)
                         (mv (cdr node-env-entry) node-env))
                        (node-entry (hons-get x.node-id nodes-alist))
                        ((mv val node-env)
                         (if node-entry
                             (svexl-fasteval-aux-wog (cdr node-entry)
                                                     nodes-alist
                                                     node-env
                                                     env
                                                     (1- limit))
                             (mv (sv::4vec-x) node-env))))
                     (mv val (hons-acons x.node-id val node-env))))
                  (t (b* ((x.fn (car x))
                          (x.args (cdr x))
                          ((mv args node-env)
                           (svexllist-fasteval-aux-wog x.args nodes-alist node-env env (1- limit))))
                       (mv (svex-apply-wog x.fn args) node-env)))))))

    (define svexllist-fasteval-aux-wog ((lst )
                                        (nodes-alist )
                                        (node-env )
                                        (env )
                                        (limit natp))
      :returns (mv res new-node-env valid)
      :measure (nfix limit)
      (cond
        ((zp limit)
         (mv nil node-env))
        ((atom lst)
         (mv nil node-env))
        (t
         (b* (((mv cur node-env )
               (svexl-fasteval-aux-wog (car lst) nodes-alist node-env env (1- limit)))
              ((mv rest node-env )
               (svexllist-fasteval-aux-wog (cdr lst) nodes-alist node-env env (1- limit))))
           (mv (cons cur rest) node-env )))))

    

    )



(define svexl-alist-fasteval-aux-wog ((alist )
                                      (nodes-alist )
                                      (node-env )
                                      (env)
                                      (limit natp))
  :returns (mv res new-node-env)
  :measure (nfix limit)
  :verify-guards nil
  :prepwork ((local
              (defthm svex-env-p-implies-alistp
                  (implies (sv::svex-env-p env)
                           (alistp env)))))
  (cond
    ((zp limit)
     (mv nil node-env))
    ((atom alist)
     (mv nil node-env))
    (t
     (b* (((mv cur node-env)
           (svexl-fasteval-aux-wog (cdar alist) nodes-alist node-env env (1- limit)))
          ((mv rest node-env)
           (svexl-alist-fasteval-aux-wog (cdr alist) nodes-alist node-env env (1- limit))))
       (mv (acons (caar alist) cur rest) node-env)))))


;;openers
(def-rp-rule svexl-fasteval-aux-wog-of-var
    (implies (and (not (zp limit))
                  (eq (svexl-node-kind-wog x) ':var))
             (equal (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
                    (mv (svex-env-fastlookup-wog x env) node-env)))
  :hints (("Goal"
           :expand (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
           :in-theory (e/d () ()))))

(def-rp-rule svexl-fasteval-aux-wog-of-quoted
    (implies (and (not (zp limit))
                  (eq (svexl-node-kind-wog x) ':quote))
             (equal (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
                    (mv x node-env)))
  :hints (("Goal"
           :expand (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
           :in-theory (e/d () ()))))

(def-rp-rule svexl-fasteval-aux-wog-of-node
    (implies (and (not (zp limit))
                  (eq (svexl-node-kind-wog x) ':node))
             (equal (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
                    (b* ((x.node-id (cadr x)) 
                         (node-env-entry (hons-get x.node-id node-env))
                         ((when node-env-entry)
                          (mv (cdr node-env-entry) node-env))
                         (node-entry (hons-get x.node-id nodes-alist))
                         ((mv val node-env)
                          (if node-entry
                              (svexl-fasteval-aux-wog (cdr node-entry)
                                                      nodes-alist
                                                      node-env
                                                      env
                                                      (1- limit))
                              (mv (sv::4vec-x) node-env))))
                      (mv val (hons-acons x.node-id val node-env)))))
  :hints (("Goal"
           :expand (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
           :in-theory (e/d () ()))))

(def-rp-rule svexl-fasteval-aux-wog-of-call
    (implies (and (not (zp limit))
                  (eq (svexl-node-kind-wog x) ':call))
             (equal (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
                    (b* (((mv args node-env)
                          (svexllist-fasteval-aux-wog (cdr x) nodes-alist node-env env (1- limit))))
                      (mv (svex-apply-wog (car x) args) node-env))))
  :hints (("Goal"
           :expand (svexl-fasteval-aux-wog x nodes-alist node-env env limit)
           :in-theory (e/d () ()))))

(def-rp-rule svexllist-fasteval-aux-wog-of-cons
    (implies (not (zp limit))
             (equal (svexllist-fasteval-aux-wog (cons x rest) nodes-alist node-env env limit)
                    (b* (((mv cur node-env)
                          (svexl-fasteval-aux-wog x nodes-alist node-env env (1- limit)))
                         ((mv rest node-env)
                          (svexllist-fasteval-aux-wog rest nodes-alist node-env env (1- limit))))
                      (mv (cons cur rest) node-env))))
   :hints (("Goal"
            :expand (svexllist-fasteval-aux-wog (cons x rest) nodes-alist node-env env limit)
            :in-theory (e/d () ()))))


(def-rp-rule svexllist-fasteval-aux-wog-of-nil
    (implies (not (zp limit))
             (equal (svexllist-fasteval-aux-wog nil nodes-alist node-env env limit)
                    (mv nil node-env)))
   :hints (("Goal"
            :expand (svexllist-fasteval-aux-wog nil nodes-alist node-env env limit)
            :in-theory (e/d () ()))))
             

(def-rp-rule svexl-alist-fasteval-aux-wog-of-cons
    (implies (not (zp limit))
             (equal (svexl-alist-fasteval-aux-wog (cons x rest) nodes-alist node-env env limit)
                    (b* (((mv cur node-env)
                          (svexl-fasteval-aux-wog (cdr x) nodes-alist node-env env (1- limit)))
                         ((mv rest node-env)
                          (svexl-alist-fasteval-aux-wog rest nodes-alist node-env env (1- limit))))
                      (mv (acons (car x) cur rest) node-env))))
   :hints (("Goal"
            :expand (svexl-alist-fasteval-aux-wog (cons x rest) nodes-alist node-env env limit)
            :in-theory (e/d () ()))))


(def-rp-rule svexl-alist-fasteval-aux-wog-of-nil
    (implies (not (zp limit))
             (equal (svexl-alist-fasteval-aux-wog nil nodes-alist node-env env limit)
                    (mv nil node-env)))
   :hints (("Goal"
            :expand (svexl-alist-fasteval-aux-wog nil nodes-alist node-env env limit)
            :in-theory (e/d () ()))))

(local
 (defthm SVEXL-NODE-P-when-x-is-call
     (implies (and (svexl-node-p x)
                   (not (equal (svexl-node-kind x) :var))
                   (not (equal (svexl-node-kind x) :quote))
                   (not (equal (svexl-node-kind x) :node)))
              (and (equal (svexl-node-kind x) :call)
                   (SVEXL-NODELIST-P (CDR X))
                   (fnsym-p (CAR X))))
   :hints (("Goal"
            :in-theory (e/d (svexl-node-p
                             svexl-node-kind) ())))))

(local
 (defthm SVEXL-NODE-P-when-x-is-node
     (implies (and (svexl-node-p x)
                   (equal (svexl-node-kind x) :node))
              (and (INTEGERP (CADR X))
                   (natp (CADR X))
                   (not (< (CADR X) 0))
                   (>= (CADR X) 0)))
   :hints (("Goal"
            :in-theory (e/d (svexl-node-p
                             svexl-node-kind) ())))))

(local
 (defthm SVEXL-NODE-P-when-x-is-quote
     (implies (and (svexl-node-p x)
                   (equal (svexl-node-kind x) :quote))
              (and (sv::4vec-p x)))
   :hints (("Goal"
            :in-theory (e/d (svexl-node-p
                             svexl-node-kind) ())))))


(local
 (defthm SVEXL-NODE-P-when-x-is-var
     (implies (and (svexl-node-p x)
                   (equal (svexl-node-kind x) :var))
              (and (sv::svar-p x)))
   :hints (("Goal"
            :in-theory (e/d (svexl-node-p
                             svexl-node-kind) ())))))

;; (skip-proofs
;;  (defthm-svexl-fasteval-aux-wog
;;      (defthmd svexl-fasteval-aux-is-svexl-fasteval-aux-wog
;;          (implies (and (svexl-node-p x)
;;                        (svexl-node-array-p nodes-alist))
;;                   (equal (svexl-fasteval-aux x nodes-alist node-env env limit)
;;                          (svexl-fasteval-aux-wog x nodes-alist node-env env limit)))
;;        :flag svexl-fasteval-aux-wog)

;;      (defthmd svexllist-fasteval-aux-is-svexllist-fasteval-aux-wog
;;          (implies (and (svexl-nodelist-p lst)
;;                        (svexl-node-array-p nodes-alist))
;;                   (equal (svexllist-fasteval-aux lst nodes-alist node-env
;;                                                  env limit)
;;                          (svexllist-fasteval-aux-wog lst nodes-alist node-env
;;                                                      env limit)))
;;        :flag svexllist-fasteval-aux-wog)
;;    :hints (("Goal"
;;             :do-not-induct t
;;             :expand ((svexl-fasteval-aux x nodes-alist node-env env limit))
;;             :in-theory (e/d (svexl-fasteval-aux
;;                              svexl-fasteval-aux-wog
;;                              svexllist-fasteval-aux
;;                              svexllist-fasteval-aux-wog
;;                              SVEXL-NODE-KIND-WOG-IS-SVEXL-NODE-KIND
;;                              SVEXL-NODE-CALL->FN
;;                              SVEXL-NODE-CALL->ARGS
;;                              SVEXL-NODELIST-FIX
;;                              SVEXL-NODE-NODE->NODE-ID
;;                              SVEXL-NODE-QUOTE->VAL
;;                              SVEXL-NODE-VAR->NAME
;;                              svex-apply-is-svex-apply-wog
;;                              )
;;                             ())))))

;; (defthmd svexl-alist-fasteval-aux-is-svexl-alist-fasteval-aux-wog
;;     (implies (and (svexl-node-alist-p alist)
;;                   (svexl-node-array-p nodes-alist))
;;              (equal (svexl-alist-fasteval-aux alist nodes-alist node-env env limit)
;;                     (svexl-alist-fasteval-aux-wog alist nodes-alist node-env env limit)))
;;   :hints (("Goal"
;;            :induct (svexl-alist-fasteval-aux alist nodes-alist node-env env
;;                                              limit)
;;            :do-not-induct t
;;            :expand ((SVEXL-ALIST-FASTEVAL-AUX-WOG ALIST NODES-ALIST NODE-ENV ENV LIMIT))
;;            :in-theory (e/d (svexl-alist-fasteval-aux
;;                             svexl-alist-fasteval-aux-wog
;;                             svexl-fasteval-aux-is-svexl-fasteval-aux-wog)
;;                            ()))))

;; (rp::add-rp-rule svexl-fasteval-aux-is-svexl-fasteval-aux-wog)
;; (rp::add-rp-rule svexllist-fasteval-aux-is-svexllist-fasteval-aux-wog)
;; (rp::add-rp-rule svexl-alist-fasteval-aux-is-svexl-alist-fasteval-aux-wog)

;; (def-rp-rule svexl-fasteval-wog-opener
;;     (implies (and (svexl-p svexl))
;;              (equal (svexl-fasteval svexl env)
;;                     (b* (((svexl svexl) svexl)
;;                          (svexl.node-array (make-fast-alist svexl.node-array))
;;                          ((mv res node-env)
;;                           (svexl-fasteval-aux-wog svexl.top-node
;;                                                   svexl.node-array
;;                                                   nil
;;                                                   env
;;                                                   (* (len svexl.node-array) 500)))
;;                          (- (fast-alist-free node-env))
;;                          (- (fast-alist-free svexl.node-array)))
;;                       res)))
;;   :hints (("Goal"
;;            :expand ((svexl-fasteval svexl env))
;;            :in-theory (e/d (svexl-fasteval-aux-is-svexl-fasteval-aux-wog
;;                             svexllist-fasteval-aux-is-svexllist-fasteval-aux-wog)
;;                            ()))))

;; (def-rp-rule svexllist-fasteval-wog-opener
;;     (implies (svexllist-p svexllist)
;;              (equal (svexllist-fasteval svexllist env)
;;                      (b* (((svexllist svexllist) svexllist)
;;                           (svexllist.node-array (make-fast-alist svexllist.node-array))
;;                           ((mv res node-env)
;;                            (svexllist-fasteval-aux-wog svexllist.top-nodelist
;;                                                        svexllist.node-array
;;                                                        nil
;;                                                        env
;;                                                        (* (len svexllist.node-array) 500)))
;;                           (- (fast-alist-free node-env))
;;                           (- (fast-alist-free svexllist.node-array)))
;;                        res)))
;;   :hints (("Goal"
;;            :expand ((svexllist-fasteval svexllist env))
;;            :in-theory (e/d (svexl-fasteval-aux-is-svexl-fasteval-aux-wog
;;                             svexllist-fasteval-aux-is-svexllist-fasteval-aux-wog)
;;                            ()))))


;; (def-rp-rule svexl-alist-fasteval-wog-opener
;;     (implies (and (svexl-alist-p svexl-alist))
;;              (equal (svexl-alist-fasteval svexl-alist env)
;;                     (b* (((svexl-alist svexl-alist) svexl-alist)
;;                          (svexl-alist.node-array (make-fast-alist svexl-alist.node-array))
;;                          ((mv res node-env)
;;                           (svexl-alist-fasteval-aux-wog svexl-alist.top-node-alist
;;                                                         svexl-alist.node-array
;;                                                         nil
;;                                                         env
;;                                                         (* (len svexl-alist.node-array) 500)))
;;                          (- (fast-alist-free node-env))
;;                          (- (fast-alist-free svexl-alist.node-array)))
;;                       res)))
;;   :hints (("Goal"
;;            :expand ((svexl-alist-fasteval svexl-alist env))
;;            :in-theory (e/d (svexl-fasteval-aux-is-svexl-fasteval-aux-wog
;;                             svexllist-fasteval-aux-is-svexllist-fasteval-aux-wog
;;                             svexl-alist-fasteval-aux-is-svexl-alist-fasteval-aux-wog)
;;                            ()))))
