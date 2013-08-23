; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")

(include-book "bfr-sat")
(include-book "../aig/bddify")
(local (include-book "../aig/bddify-correct"))
(local (include-book "../aig/eval-restrict"))



(defun vars-to-bdd-bindings (x n)
  (declare (xargs :guard (natp n)))
  (let ((n (lnfix n)))
    (if (atom x)
        nil
      (hons-acons (car x) (qv n)
                  (vars-to-bdd-bindings (cdr x) (1+ n))))))


(defun bfr-sat-bddify (prop)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (mv nil nil nil) ;; fail
   :aig
   (b* ((vars (acl2::aig-vars prop))
        (bindings (vars-to-bdd-bindings vars 0))
        ((mv bdd & exact)
         (ec-call
          (acl2::aig-bddify acl2::*bddify-default-tries*
                            prop bindings nil)))
        (sat? (acl2::eval-bdd bdd (acl2::bdd-sat-dfs bdd))))
     (mv sat? exact bdd))))



(local (defthm ubddp-val-alistp-vars-to-bdd-bindings
         (acl2::ubddp-val-alistp (vars-to-bdd-bindings x n))))


(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm hons-assoc-equal-vars-to-bdd-bindings
  (implies (member-equal x vars)
           (equal (cdr (hons-assoc-equal x (vars-to-bdd-bindings vars n)))
                  (qv (+ (nfix n) (- (len vars) (len (member-equal x
                                                                   vars))))))))


(defun vars-to-bdd-env (vars aig-env)
  (if (atom vars)
      nil
    (cons (let ((look (hons-get (car vars) aig-env)))
            (or (not look) (cdr look)))
          (vars-to-bdd-env (cdr vars) aig-env))))

(defthm nth-vars-to-bdd-env
  (implies (< (nfix n) (len vars))
           (equal (nth n (vars-to-bdd-env vars aig-env))
                  (if (hons-assoc-equal (nth n vars) aig-env)
                      (cdr (hons-assoc-equal (nth n vars) aig-env))
                    t)))
  :hints(("Goal" :in-theory (enable nth))))

(defthm len-member-equal
  (implies (member-equal x vars)
           (and (< 0 (len (member-equal x vars)))
                (<= (len (member-equal x vars)) (len vars))))
  :rule-classes :linear)

(defthm nth-of-index
  (implies (member-equal x lst)
           (equal (nth (+ (len lst) (- (len (member-equal x lst)))) lst)
                  x)))

(defthm idx-rewrite
  (implies (member-equal x vars)
           (< (nfix (+ (len vars) (- (len (member-equal x vars)))))
              (len vars))))

(defthm nth-append
  (equal (nth n (append a b))
         (if (< (nfix n) (len a))
             (nth n a)
           (nth (- (nfix n) (len a)) b))))

(defthm aig-q-compose-vars-to-bdd-env
  (implies (subsetp-equal (acl2::aig-vars x) vars)
           (equal (acl2::eval-bdd (acl2::aig-q-compose
                                   x (vars-to-bdd-bindings vars n))
                                  (append (make-list n)
                                          (vars-to-bdd-env vars aig-env)))
                  (acl2::aig-eval x aig-env)))
  :hints (("goal" :induct (acl2::aig-eval x aig-env)
           :in-theory (e/d (subsetp-equal
                            acl2::aig-env-lookup) (nfix)))
          (and stable-under-simplificationp
               '(:in-theory (enable nfix)))))


(defthm bfr-sat-bddify-unsat
  (mv-let (sat succeeded ctrex)
    (bfr-sat-bddify prop)
    (declare (ignore ctrex))
    (implies (and succeeded (not sat))
             (not (bfr-eval prop env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval)
                                 (aig-q-compose-vars-to-bdd-env
                                  acl2::bdd-sat-dfs-correct))
          :use ((:instance aig-q-compose-vars-to-bdd-env
                           (x prop) (n 0) (vars (acl2::aig-vars prop))
                           (aig-env env))
                (:instance acl2::bdd-sat-dfs-correct
                 (x (MV-NTH 0
                            (ACL2::AIG-BDDIFY acl2::*bddify-default-tries*
                                              PROP
                                              (VARS-TO-BDD-BINDINGS (ACL2::AIG-VARS PROP)
                                                                    0)
                                              NIL)))
                 (acl2::vars (vars-to-bdd-env (acl2::aig-vars prop) env)))))))


(defsection gl-aig-bddify-mode
  :parents (modes reference)
  :short "GL: use AIGs as the Boolean function representation and solve queries
by transforming them to BDDs."

  (defmacro gl-aig-bddify-mode ()
    '(progn (acl2::defattach bfr-mode bfr-aig)
            (acl2::defattach bfr-counterex-mode bfr-counterex-bdd)
            (acl2::defattach
             (bfr-sat bfr-sat-bddify)
             :hints (("goal" :in-theory '(bfr-sat-bddify-unsat))
                     (and stable-under-simplificationp
                          '(:in-theory (enable bfr-sat-bddify))))))))

(local (gl-aig-bddify-mode))

