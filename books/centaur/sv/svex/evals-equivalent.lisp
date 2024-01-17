; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "symbolic")
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/bfr" :dir :system)
(include-book "centaur/fgl/simplify-defs" :dir :system)
(include-book "centaur/fgl/checks" :dir :system)
(include-book "centaur/fgl/make-isomorphic-def" :dir :system)
;; (include-book "centaur/aignet/transforms" :dir :System)

(define svexlist-evals-equal ((x svexlist-p)
                              (env1 svex-env-p)
                              (env2 svex-env-p))
  (equal (svexlist-eval x env1)
         (svexlist-eval x env2)))



(define svexlist-mask-alist/toposort-memo ((x svexlist-p))
  :enabled t
  (svexlist-mask-alist/toposort x)
  ///
  (memoize 'svexlist-mask-alist/toposort-memo))


(define svexlists->a4vec-top ((x svexlist-p) (y svexlist-p) (env svex-a4vec-env-p) (masks svex-mask-alist-p))
  ;; note: env must be fast
  ;; :prepwork ((local (defthm svexlist->a4vec-decomp
  ;;                     (equal (list (mv-nth 0 (svexlist->a4vec x env masks memo))
  ;;                                  (mv-nth 1 (svexlist->a4vec x env masks memo)))
  ;;                            (svexlist->a4vec x env masks memo))
  ;;                     :hints (("goal" :expand ((svexlist->a4vec x env masks memo)))))))
  :enabled t
  (mbe :logic (mv (svexlist->a4vec x env masks)
                  (svexlist->a4vec y env masks))
       :exec
       (b* (((mv x-res y-res memo)
             (with-local-stobj acl2::nrev
               (mv-let (x-res y-res memo acl2::nrev)
                 (b* (((mv acl2::nrev memo)
                       (svexlist->a4vec-nrev x env masks nil acl2::nrev))
                      ((mv x-res acl2::nrev) (acl2::nrev-finish acl2::nrev))
                      ((mv acl2::nrev memo)
                       (svexlist->a4vec-nrev y env masks memo acl2::nrev))
                      ((mv y-res acl2::nrev) (acl2::nrev-finish acl2::nrev)))
                   (mv x-res y-res memo acl2::nrev))
                 (mv x-res y-res memo)))))
         (fast-alist-free memo)
         (mv x-res y-res))))

(define svexlist->a4vecs-for-varlist-with-subexprs ((x svexlist-p)
                                                    (vars svarlist-p)
                                                    (boolmasks svar-boolmasks-p))
  :returns (mv (err (iff err (not (svex-maskbits-ok vars (svexlist-mask-alist x)))))
               (x-a4vecs a4veclist-p)
               (subexp-a4vecs a4veclist-p))
  :short "Creates a symbolic bit-level representation for x, assuming that vars
          are the only vars relevant to x and that the bits of vars given in boolmasks
          are Boolean-valued."
  :long "<p>Steps: First creates a symbolic environment mapping the variables
to a4vec structures, each bit of which is a free variable.  (For bits
constrained to be Boolean by boolmasks, the same variable is shared for
upper/lower.)  Then uses @('svexlist->a4vec-top') to generate a4vecs corresponding
to the svexes.</p>"

  (b* (;; (- (sneaky-push 'svexlist x))
       ((mv masks toposort) (svexlist-mask-alist/toposort-memo x))
       ((mv err a4env) (svex-varmasks->a4env vars masks boolmasks))
       ((when err) (mv err nil nil))
       (a4env (make-fast-alist a4env))
       ((mv x-res sub-res) (svexlists->a4vec-top x toposort a4env masks))
       (?ign (fast-alist-free a4env)))
    (mv nil x-res sub-res))
  ///
  (memoize 'svexlist->a4vecs-for-varlist-with-subexprs)

  (defret <fn>-equals-svexlist->a4vecs-for-varlist
    (b* (((mv err-spec a4vec-spec) (svexlist->a4vecs-for-varlist x vars boolmasks)))
      (and (equal err err-spec)
           (equal x-a4vecs a4vec-spec)))
    :hints(("Goal" :in-theory (enable svexlist->a4vecs-for-varlist)))))


(local (defthm true-listp-nthcdr
         (implies (true-listp x)
                  (true-listp (nthcdr n x)))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))
         :rule-classes :type-prescription))

(local (defthm nthcdr-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y))
                         y))
         :hints(("Goal" :in-theory (e/d (nthcdr)
                                        (acl2::cdr-nthcdr))
                 :induct (nthcdr n x)))))

(local (defthm nthcdr-of-append-2-equal-len
         (implies (equal (nfix n) (+ (len x) (len y)))
                  (equal (nthcdr n (append x y z))
                         z))
         :hints(("Goal" :use ((:instance nthcdr-of-append-equal-len
                               (x (append x y)) (y z)))))))

(local (defthm take-of-append-equal-len
         (implies (equal (nfix n) (len x))
                  (equal (take n (append x y))
                         (list-fix x)))
         :hints(("Goal" :in-theory (e/d (acl2::take))
                 :induct (nthcdr n x)))))

(define my-replace-assoc ((key symbolp) val alist)
  (if (atom alist)
      alist
    (if (and (consp (car alist))
             (eq key (caar alist)))
        (cons (cons key val) (cdr alist))
      (cons (car alist) (my-replace-assoc key val (cdr alist))))))
        


(define transforms-update-fraig-configs-for-n-outputs ((n natp) transforms)
  ;; BOZO We don't want to load the fraig book just to be able to write an updater for its config.
  ;; So we're going to assume the basic form of a fraig config object which is (:fraig . alist)
  (if (atom transforms)
      nil
    (cons (b* ((x (car transforms))
               ((unless (and (consp x)
                             (eq (car x) :fraig-config)
                             (alistp (cdr x))))
                x)
               ;; Change the config: find the AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES entry
               ;; and replace it with `(AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES . ,n)
               (alist (cdr x))
               (alist (my-replace-assoc 
                       'AIGNET::N-OUTPUTS-ARE-INITIAL-EQUIV-CLASSES (lnfix n) alist))
               (alist (my-replace-assoc
                       'AIGNET::INITIAL-EQUIV-CLASSES-LAST t alist)))
            (cons :fraig-config alist))
          (transforms-update-fraig-configs-for-n-outputs n (cdr transforms)))))

;; (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "std/lists/nth" :dir :system))

;; (define fgl-fix-boolean-list-to-g-booleans-rec (n x rest)
;;   :enabled t
;;   (append (ec-call (take n x)) rest)
;;   ///
;;   (local (in-theory (enable bitops::logtail**)))
;;   (local (defthm logcar-plus-logcdr
;;            (implies (natp x)
;;                     (<= (+ (logcar x) (logcdr x)) x))
;;            :hints (("goal" :use ((:instance bitops::logcons-destruct))
;;                     :in-theory (e/d (logcons)
;;                                     (bitops::logcons-destruct
;;                                      acl2::logcar-logcdr-elim))))
;;            :rule-classes :linear))
;;   (local (defthm logcar-plus-logcdr-gte-1
;;            (implies (posp x)
;;                     (<= 1 (+ (logcar x) (logcdr x))))
;;            :hints (("goal" :use ((:instance bitops::logcons-destruct))
;;                     :in-theory (e/d (logcons)
;;                                     (bitops::logcons-destruct
;;                                      acl2::logcar-logcdr-elim))))
;;            :rule-classes :linear))
;;   (local (defthm append-take-nthcdr
;;            (equal (append (take n x) (take m (nthcdr n x)))
;;                   (take (+ (nfix n) (nfix m)) x))
;;            :hints(("Goal" :in-theory (enable take nthcdr)
;;                    :induct (take m (nthcdr n x))))))
;;   (local (defthm cdr-of-nthcdr
;;            (equal (cdr (nthcdr n x))
;;                   (nthcdr n (cdr x)))))
;;   (local (in-theory (disable acl2::cdr-nthcdr)))

;;   (local (defthm append-take-nthcdr-2
;;            (equal (append (take n x) (take m (nthcdr n x)) y)
;;                   (append (take (+ (nfix n) (nfix m)) x) y))
;;            :hints (("goal" :use ((:instance ACL2::ASSOCIATIVITY-OF-APPEND
;;                                   (a (take n x)) (b (take m (nthcdr n x))) (c y)))
;;                     :in-theory (disable acl2::associativity-of-append)))))
  
;;   (fgl::def-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-rec-impl
;;     (equal (fgl-fix-boolean-list-to-g-booleans-rec n x rest)
;;            (b* (((When (zp n)) rest)
;;                 (first (b* ((x1 (car x))
;;                             ((when (fgl::check-equal x1-is-t x1 t))
;;                              (fgl::symbolic-t))
;;                             ((when (fgl::check-equal x-is-nil x1 nil))
;;                              (fgl::symbolic-nil)))
;;                          x1))
;;                 (x (cdr x))
;;                 (n (1- n))
;;                 (halfn (ash n -1))
;;                 (restn (- n halfn))
;;                 (rest (fgl-fix-boolean-list-to-g-booleans-rec restn (nthcdr halfn x) rest))
;;                 (rest (fgl-fix-boolean-list-to-g-booleans-rec halfn x rest)))
;;              (cons first rest)))
;;     :hints (("goal" :in-theory (enable fgl::check-equal))))

;;   (fgl::remove-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-rec))
    


;; (define fgl-fix-boolean-list-to-g-booleans (x)
;;   :enabled t
;;   (true-list-fix x)
;;   ///
;;   (fgl::def-fgl-rewrite fgl-fix-boolean-list-to-g-booleans-impl
;;     (equal (fgl-fix-boolean-list-to-g-booleans x)
;;            (fgl-fix-boolean-list-to-g-booleans-rec (len x) x nil)))

;;   (fgl::remove-fgl-rewrite fgl-fix-boolean-list-to-g-booleans))



;; (define a4veclist-eval-for-evals-equal ((x a4veclist-p) (sub a4veclist-p) (env1) (env2) (transforms))
;;   ;; Flattens sub and x (a4veclists) into AIG lists, evaluates them under two
;;   ;; envs, orders them so that the respective evaluations of y can be used as
;;   ;; simplifies them with the special form of the FRAIG transform, then
;;   ;; recovers those from x and transforms it back to an a4veclist.
;;   :enabled t
;;   (declare (ignorable sub transforms))
;;   (mv (a4veclist-eval x env1)
;;       (a4veclist-eval x env2))
;;   ///
;;   (fgl::def-fgl-rewrite a4veclist-eval-for-evals-equal-fgl
;;     (equal (a4veclist-eval-for-evals-equal x sub env1 env2 transforms)
;;            (b* ((sub-aiglist (time$ (a4veclist->aiglist sub)
;;                                     :msg "; SV bit-blasting: a4veclist->aiglist (sub): ~st sec, ~sa bytes.~%"))
;;                 (sub-len (time$ (len sub-aiglist)
;;                                 :msg "; SV bit-blasting: len(sub): ~st sec, ~sa bytes.~%"))
;;                 (x-aiglist (time$ (a4veclist->aiglist x)
;;                                   :msg "; SV bit-blasting: a4veclist->aiglist (x): ~st sec, ~sa bytes.~%"))
;;                 (x-len (time$ (len x-aiglist)
;;                               :msg "; SV bit-blasting: len(x): ~st sec, ~sa bytes.~%"))
;;                 (env1 (make-fast-alist env1))
;;                 (env2 (make-fast-alist env2))
;;                 (sub-bits1 (time$ (fgl-fix-boolean-list-to-g-booleans
;;                                    (aig-eval-list sub-aiglist env1))
;;                                   :msg "; SV bit-blasting: aig-eval-list (sub, env1): ~st sec, ~sa bytes.~%"))
;;                 (sub-bits2 (time$ (fgl-fix-boolean-list-to-g-booleans
;;                                    (aig-eval-list sub-aiglist env2))
;;                                   :msg "; SV bit-blasting: aig-eval-list (sub, env2): ~st sec, ~sa bytes.~%"))
;;                 (x-bits1 (time$ (aig-eval-list x-aiglist env1)
;;                                 :msg "; SV bit-blasting: aig-eval-list (x, env1): ~st sec, ~sa bytes.~%"))
;;                 (x-bits2 (time$ (aig-eval-list x-aiglist env2)
;;                                 :msg "; SV bit-blasting: aig-eval-list (x, env2): ~st sec, ~sa bytes.~%"))
;;                 (?ign (fast-alist-free env1))
;;                 (?ign (fast-alist-free env2))
;;                 (full-bits (append sub-bits1 sub-bits2 x-bits1 x-bits2))
;;                 (transforms (transforms-update-fraig-configs-for-n-outputs sub-len transforms))
;;                 (full-bits-simp (fgl::fgl-simplify-ordered full-bits transforms :use-pathcond nil :use-constraint nil))
;;                 (x-bits-simp (nthcdr (* 2 sub-len) full-bits-simp))
;;                 (x-bits1 (take x-len x-bits-simp))
;;                 (x-bits2 (nthcdr x-len x-bits-simp))
;;                 (x-4vecs1 (time$ (4veclist-from-bitlist x x-bits1)
;;                                  :msg "; bits->4vecs 1: ~st sec, ~sa bytes.~%"))
;;                 (x-4vecs2 (time$ (4veclist-from-bitlist x x-bits2)
;;                                  :msg "; bits->4vecs 1: ~st sec, ~sa bytes.~%"))
;;                 (?ign (fgl::fgl-gatecount 4vecs (cons x-4vecs1 x-4vecs2))))
;;              (mv x-4vecs1 x-4vecs2))))
  
;;   (fgl::remove-fgl-rewrite a4veclist-eval-for-evals-equal))

(local (include-book "std/lists/sets" :dir :system))

(local (defthm setp-of-svexlist-vars-for-symbolic-eval
         (set::setp (svexlist-vars-for-symbolic-eval
                     x env symbolic-params))
         :hints(("Goal" :in-theory (enable svexlist-vars-for-symbolic-eval)))))

(local (defthm subsetp-of-append-1
         (implies (subsetp x y)
                  (subsetp x (append y z)))))

(local (defthm subsetp-of-append-2
         (implies (subsetp x z)
                  (subsetp x (append y z)))))


(local (defthm subsetp-maybe-svexlist-rewrite-fixpoint-of-x-out-unused-vars
         (subsetp-equal (svexlist-vars (maybe-svexlist-rewrite-fixpoint
                                        (svexlist-x-out-unused-vars x vars params)
                                        simp))
                        (svexlist-vars x))
         :hints ((set-reasoning))))

(local (defthm subsetp-intersection-maybe-svexlist-rewrite-fixpoint-of-x-out-unused-vars
         (implies (subsetp (intersection-equal
                            (svexlist-vars x) envkeys)
                           vars2)
                  (subsetp (intersection-equal
                            (svexlist-vars (maybe-svexlist-rewrite-fixpoint
                                        (svexlist-x-out-unused-vars x vars params)
                                        simp))
                            envkeys)
                           vars2))
         :hints ((set-reasoning))))



(define svexlist-evals-equal-with-transforms ((x svexlist-p)
                                              (env1 svex-env-p)
                                              (env2 svex-env-p)
                                              (symbolic-params alistp)
                                              (transforms))
  (declare (ignorable symbolic-params transforms))
  (svexlist-evals-equal x env1 env2)
  ///


  ;; (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl
  ;;   (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
  ;;          (b* (((mv ?masks toposort) (svexlist-mask-alist/toposort-memo x))
  ;;               (x-len (len x))
  ;;               (full-svexes (append x toposort))
  ;;               (eval1 (svexlist-eval-for-symbolic full-svexes env1 symbolic-params))
  ;;               (eval2 (svexlist-eval-for-symbolic full-svexes env2 symbolic-params))
  ;;               (x-eval1 (take x-len eval1))
  ;;               (x-eval2 (take x-len eval2))
  ;;               (hint-eval1 (nthcdr x-len eval1))
  ;;               (hint-eval2 (nthcdr x-len eval2))
  ;;               ((mv iso-ok hint-eval1 hint-eval2) (fgl::fgl-make-isomorphic iso-ok hint-eval1 hint-eval2))
  ;;               ((unless iso-ok)
  ;;                (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
  ;;                     (?foo (break$)))
  ;;                  (fgl::abort-rewrite (svexlist-evals-equal x env1 env2))))
  ;;               (evals-equal (equal x-eval1 x-eval2))
  ;;               (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval1)))))
  ;;               (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval2)))))
  ;;               ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
  ;;                (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
  ;;                                equivalence hint objects wasn't equal after ~
  ;;                                they were made isomorphic!~%"))
  ;;                     (?foo (break$)))
  ;;                  (fgl::abort-rewrite (svexlist-evals-equal x env1 env2))))
  ;;               (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
  ;;            (fgl::fgl-simplify-ordered evals-equal transforms
  ;;                                       :tracked-obj
  ;;                                       (cons hint-eval1 hint-eval2))))
  ;;   :hints(("Goal" :in-theory (enable svexlist-evals-equal)))))

  
  (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl
    (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))

                (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                                :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                                  :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                                :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                                  :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal (equal x-eval1 x-eval2))
                ((mv iso-ok hint-eval1 hint-eval2) (fgl::fgl-make-isomorphic iso-ok hint-eval1 hint-eval2))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (svexlist-evals-equal orig-x env1 env2))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal transforms
                                        :tracked-obj
                                        (cons hint-eval1 hint-eval2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))






(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))


(define 4veclist-separate-upper-lower-rec-log ((n natp)
                                               (x 4veclist-p)
                                               (rest-upper integer-listp)
                                               (rest-lower integer-listp))
  :measure (nfix n)
  :guard (<= n (len x))
  :returns (mv (uppers integer-listp :hyp (integer-listp rest-upper))
               (lowers integer-listp :hyp (integer-listp rest-lower)))
  :verify-guards nil
  :hints(("Goal" :in-theory (enable bitops::logtail**)))
  :prepwork ((local (defthm logcar-plus-logcdr
                      (implies (natp x)
                               (<= (+ (logcar x) (logcdr x)) x))
                      :hints (("goal" :use ((:instance bitops::logcons-destruct))
                               :in-theory (e/d (logcons)
                                               (bitops::logcons-destruct
                                                acl2::logcar-logcdr-elim))))
                      :rule-classes :linear)))
  (if (zp n)
      (mv rest-upper rest-lower)
    (b* (((4vec x1) (car x))
         (n (1- n))
         (x (cdr x))
         (halfn (ash n -1))
         (restn (- n halfn))
         ((mv rest-upper rest-lower) (4veclist-separate-upper-lower-rec-log
                                      restn (nthcdr halfn x) rest-upper rest-lower))
         ((mv rest-upper rest-lower) (4veclist-separate-upper-lower-rec-log
                                      halfn x rest-upper rest-lower)))
      (mv (cons x1.upper rest-upper)
          (cons x1.lower rest-lower))))
  ///
  (verify-guards 4veclist-separate-upper-lower-rec-log
    :hints(("Goal" :in-theory (enable bitops::logtail** len)))))


(define 4veclist-separate-upper-lower ((x 4veclist-p))
  :returns (mv (uppers integer-listp)
               (lowers integer-listp))
  (if (atom x)
      (mv nil nil)
    (b* (((mv rest-up rest-low) (4veclist-separate-upper-lower (cdr x)))
         ((4vec x1) (car X)))
      (mv (cons x1.upper rest-up)
          (cons x1.lower rest-low))))

  ///
  (local (in-theory (enable bitops::logtail**)))
  (local (defthm logcar-plus-logcdr
           (implies (natp x)
                    (<= (+ (logcar x) (logcdr x)) x))
           :hints (("goal" :use ((:instance bitops::logcons-destruct))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct
                                     acl2::logcar-logcdr-elim))))
           :rule-classes :linear))
  (local (defthm logcar-plus-logcdr-gte-1
           (implies (posp x)
                    (<= 1 (+ (logcar x) (logcdr x))))
           :hints (("goal" :use ((:instance bitops::logcons-destruct))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct
                                     acl2::logcar-logcdr-elim))))
           :rule-classes :linear))
  (local (defthm append-take-nthcdr
           (equal (append (take n x) (take m (nthcdr n x)))
                  (take (+ (nfix n) (nfix m)) x))
           :hints(("Goal" :in-theory (enable take nthcdr)
                   :induct (take m (nthcdr n x))))))
  (local (defthm cdr-of-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr n (cdr x)))))
  (local (in-theory (disable acl2::cdr-nthcdr)))

  (local (defthm append-take-nthcdr-2
           (equal (append (take n x) (take m (nthcdr n x)) y)
                  (append (take (+ (nfix n) (nfix m)) x) y))
           :hints (("goal" :use ((:instance ACL2::ASSOCIATIVITY-OF-APPEND
                                  (a (take n x)) (b (take m (nthcdr n x))) (c y)))
                    :in-theory (disable acl2::associativity-of-append)))))

  (local (in-theory (disable acl2::nthcdr-of-cdr)))

  (local (defthm equal-list
           (equal (equal x (list y z))
                  (and (true-listp x)
                       (Equal (len x) 2)
                       (equal (mv-nth 0 x) y)
                       (equal (mv-nth 1 x) z)))
           :hints(("Goal" :in-theory (enable mv-nth len)))))

  (local (defthm 4veclist-separate-upper-lower-append-take
           (b* (((mv upper1 lower1) (4veclist-separate-upper-lower (take n x)))
                ((mv upper2 lower2) (4veclist-separate-upper-lower (take m (nthcdr n x))))
                ((mv upper lower) (4veclist-separate-upper-lower (take (+ (nfix n) (nfix m)) x))))
             (and (equal (append upper1 upper2 rest)
                         (append upper rest))
                  (equal (append lower1 lower2 rest)
                         (append lower rest))))))
  
  (defthm 4veclist-separate-upper-lower-rec-log-elim
    (equal (4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)
           (b* (((mv uppers lowers) (4veclist-separate-upper-lower (take n x))))
             (mv (append uppers rest-upper)
                 (append lowers rest-lower))))
    :hints(("Goal" :in-theory (enable (:i 4veclist-separate-upper-lower-rec-log))
            :induct (4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)
            :expand ((4veclist-separate-upper-lower-rec-log n x rest-upper rest-lower)))))

  (fgl::def-fgl-rewrite 4veclist-separate-upper-lower-fgl
    (equal (4veclist-separate-upper-lower x)
           (4veclist-separate-upper-lower-rec-log (len x) x nil nil)))
)



(define svexlist-eval-integer-listp-with-transforms ((x svexlist-p)
                                                      (env svex-env-p)
                                                      (symbolic-params alistp)
                                                      (transforms))
  (declare (ignorable symbolic-params transforms))
  (integer-listp (svexlist-eval x env))
  ///


  
  (fgl::def-fgl-rewrite svexlist-eval-integer-listp-with-transforms-fgl
    (equal (svexlist-eval-integer-listp-with-transforms x env symbolic-params transforms)
           (b* ((orig-x x)

                (env (make-fast-alist (svex-env-fix env)))
                (svars (svexlist-vars-for-symbolic-eval x env symbolic-params))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (svex-env-check-boolmasks boolmasks env))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))

                ((mv ?err aig-env)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env (make-fast-alist aig-env))

                (?ign (fast-alist-free env))

                (x-eval (time$ (a4veclist-eval x-a4vecs aig-env)
                                :msg "; a4veclist-eval x: ~st sec, ~sa bytes.~%"))
                (hint-eval (time$ (a4veclist-eval hint-a4vecs aig-env)
                                  :msg "; a4veclist-eval sub: ~st sec, ~sa bytes.~%"))
                (?ign (fgl::fgl-prog2 (fgl::syntax-interp (prog2$ (cw "x-eval: ~x0~%" x-eval)
                                                (cw "hint-eval: ~x0~%" hint-eval)))
                                 nil))
                (evals-integer-listp (integer-listp x-eval))
                ((mv hint-upper hint-lower) (4veclist-separate-upper-lower hint-eval))
                ((mv iso-ok hint-upper hint-lower) (fgl::fgl-make-isomorphic iso-ok hint-upper hint-lower))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-upper)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-lower)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (integer-listp (svexlist-eval orig-x env)))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-integer-listp transforms
                                        :tracked-obj
                                        (cons hint-upper hint-lower))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))



(define hons-aig-accumulate-nodes (x acc)
  (b* (((when (atom x))
        (if (or (booleanp x)
                (hons-get x acc))
            acc
          (hons-acons x t acc)))
       ((when (eq (cdr x) nil))
        (hons-aig-accumulate-nodes (car x) acc))
       ((when (hons-get x acc)) acc)
       (acc (hons-acons x t acc))
       (acc (hons-aig-accumulate-nodes (car x) acc)))
    (hons-aig-accumulate-nodes (cdr x) acc)))

(define hons-aiglist-accumulate-nodes (x acc)
  (if (atom x)
      acc
    (hons-aiglist-accumulate-nodes
     (cdr x) (hons-aig-accumulate-nodes (car x) acc))))

(define a4vec-accumulate-nodes ((x a4vec-p) acc)
  (b* (((a4vec x)))
    (hons-aiglist-accumulate-nodes x.upper (hons-aiglist-accumulate-nodes x.lower acc))))

 (define a4veclist-accumulate-nodes ((x a4veclist-p) acc)
  (if (atom x)
      acc
    (a4veclist-accumulate-nodes (cdr x) (a4vec-accumulate-nodes (car x) acc))))


(define a4veclist-subnodes ((x a4veclist-p))
  (b* ((acc (a4veclist-accumulate-nodes x nil)))
    (fast-alist-free acc)
    (alist-keys acc)))


(define a4veclist-accumulate-upper-nodes ((x a4veclist-p) acc)
  (if (atom x)
      acc
    (a4veclist-accumulate-nodes (cdr x)
                                (hons-aiglist-accumulate-nodes (a4vec->upper (car x))
                                                               acc))))


(define a4veclist-upper-subnodes ((x a4veclist-p))
  (b* ((acc (a4veclist-accumulate-upper-nodes x nil)))
    (fast-alist-free acc)
    (alist-keys acc)))



(define 4veclist->upper-4vecs ((x 4veclist-p))
  :returns (new-x 4veclist-p)
  (if (Atom x)
      nil
    (cons (2vec (4vec->upper (car x)))
          (4veclist->upper-4vecs (cdr x))))
  ///
  (defret 4veclist->upper-4vecs-when-integer-listp
    (implies (integer-listp x)
             (equal (4veclist->upper-4vecs x) x))
    :hints(("Goal" :in-theory (enable 4vec->upper 2vec 4vec)))))

(define a4veclist->upper-a4vecs-acc ((x a4veclist-p) (acc true-listp))
  (if (atom x)
      (reverse (llist-fix acc))
    (a4veclist->upper-a4vecs-acc (cdr x)
                                 (cons (b* ((upper (a4vec->upper (car x))))
                                         (a4vec upper upper))
                                       acc))))

(define a4veclist->upper-a4vecs ((x a4veclist-p))
  :returns (new-x a4veclist-p)
  :verify-guards nil
  (mbe :logic (if (atom x)
                  nil
                (cons (b* ((upper (a4vec->upper (car x))))
                        (a4vec upper upper))
                      (a4veclist->upper-a4vecs (cdr x))))
       :exec (a4veclist->upper-a4vecs-acc x nil))
  ///
  (local (defthm a4veclist->upper-a4vecs-acc-elim
           (equal (a4veclist->upper-a4vecs-acc x acc)
                  (revappend acc (a4veclist->upper-a4vecs x)))
           :hints(("Goal" :in-theory (enable a4veclist->upper-a4vecs-acc)))))

  (verify-guards a4veclist->upper-a4vecs)

  (defret eval-of-<fn>
    (equal (a4veclist-eval new-x env)
           (4veclist->upper-4vecs (a4veclist-eval x env)))
    :hints(("Goal" :in-theory (enable a4veclist-eval
                                      4veclist->upper-4vecs)))))
       

(define eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
  ((x-a4vecs a4veclist-p)
   (hint-a4vecs a4veclist-p)
   (subnodes)
   (env))
  :returns (mv (x-eval 4veclist-p)
               (hint-eval 4veclist-p)
               (subnodes-eval boolean-listp))
  (b* ((x-aiglist (sv::a4veclist->aiglist x-a4vecs))
       (hint-aiglist (sv::a4veclist->aiglist hint-a4vecs))
       (all-aigs (append x-aiglist hint-aiglist subnodes))
       (bitlist (time$ (acl2::aig-eval-list all-aigs env)
                       :msg "; SV bit-blasting: aig-eval-list: ~st sec, ~sa bytes.~%"))
       (x-aig-len (length x-aiglist))
       (hint-aig-len (length hint-aiglist))
       ;; 4veclist-from-bitlist doesn't care about extra bits so we don't need to use take.
       (hint-bitlist (nthcdr x-aig-len bitlist))
       (subnodes-bitlist (nthcdr hint-aig-len hint-bitlist)))
    (mv (time$ (sv::4veclist-from-bitlist x-a4vecs bitlist) :msg "; bits->4vecs: ~st sec, ~sa bytes.~%")
        (time$ (sv::4veclist-from-bitlist hint-a4vecs hint-bitlist) :msg "; bits->4vecs: ~st sec, ~sa bytes.~%")
        subnodes-bitlist))
  ///
  (local (include-book "std/lists/nthcdr" :dir :system))
  (local (include-book "std/lists/take" :dir :system))

  (local (defthm take-of-nthcdr
           (equal (take n (nthcdr m x))
                  (nthcdr m (take (+ (nfix n) (nfix m)) x)))
           :hints(("Goal" :in-theory (e/d (take nthcdr)
                                          ())))))

  (local (defthm nthcdr-less-than-first-len-of-append
           (implies (<= (nfix n) (len a))
                    (equal (nthcdr n (append a b))
                           (append (nthcdr n a) b)))))
  (local (defthm 4vec-from-bitlist-of-append
           (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
                    (Equal (4vec-from-bitlist upper-len lower-len (append a b))
                           (b* (((mv 4vec rest)
                                 (4vec-from-bitlist upper-len lower-len a)))
                             (mv 4vec (append rest b)))))
           :hints(("Goal" :in-theory (enable 4vec-from-bitlist)
                   :do-not-induct t)
                  (and stable-under-simplificationp
                       '(:cases ((natp upper-len)))))))

  (local (defthm len-of-4vec-from-bitlist-rest
           (implies (<= (+ (nfix upper-len) (nfix lower-len)) (len a))
                    (equal (len (mv-nth 1 (4vec-from-bitlist upper-len lower-len a)))
                           (- (len a) (+ (nfix upper-len) (nfix lower-len)))))
           :hints(("Goal" :in-theory (enable 4vec-from-bitlist)))))
  
  (local (defthm 4veclist-from-bitlist-of-append
           (implies (<= (len (a4veclist->aiglist x)) (len a))
                    (equal (4veclist-from-bitlist x (append a b))
                           (4veclist-from-bitlist x a)))
           :hints(("Goal" :in-theory (enable 4veclist-from-bitlist a4veclist->aiglist
                                             a4vec->aiglist)))))
  
  (defret <fn>-correct
    (and (equal x-eval (a4veclist-eval x-a4vecs env))
         (equal hint-eval (a4veclist-eval hint-a4vecs env))
         (equal subnodes-eval (acl2::aig-eval-list subnodes env)))))


(define svexlist-evals-equal-and-integerp-with-transforms ((x svexlist-p)
                                                           (env1 svex-env-p)
                                                           (env2 svex-env-p)
                                                           (symbolic-params alistp)
                                                           (transforms))
  (declare (ignorable symbolic-params transforms))
  (and (svexlist-evals-equal x env1 env2)
       (integer-listp (svexlist-eval x env1)))
  ///


  ;; (fgl::def-fgl-rewrite svexlist-evals-equal-with-transforms-fgl
  ;;   (equal (svexlist-evals-equal-with-transforms x env1 env2 symbolic-params transforms)
  ;;          (b* (((mv ?masks toposort) (svexlist-mask-alist/toposort-memo x))
  ;;               (x-len (len x))
  ;;               (full-svexes (append x toposort))
  ;;               (eval1 (svexlist-eval-for-symbolic full-svexes env1 symbolic-params))
  ;;               (eval2 (svexlist-eval-for-symbolic full-svexes env2 symbolic-params))
  ;;               (x-eval1 (take x-len eval1))
  ;;               (x-eval2 (take x-len eval2))
  ;;               (hint-eval1 (nthcdr x-len eval1))
  ;;               (hint-eval2 (nthcdr x-len eval2))
  ;;               ((mv iso-ok hint-eval1 hint-eval2) (fgl::fgl-make-isomorphic iso-ok hint-eval1 hint-eval2))
  ;;               ((unless iso-ok)
  ;;                (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
  ;;                     (?foo (break$)))
  ;;                  (fgl::abort-rewrite (svexlist-evals-equal x env1 env2))))
  ;;               (evals-equal (equal x-eval1 x-eval2))
  ;;               (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval1)))))
  ;;               (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-eval2)))))
  ;;               ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
  ;;                (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
  ;;                                equivalence hint objects wasn't equal after ~
  ;;                                they were made isomorphic!~%"))
  ;;                     (?foo (break$)))
  ;;                  (fgl::abort-rewrite (svexlist-evals-equal x env1 env2))))
  ;;               (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
  ;;            (fgl::fgl-simplify-ordered evals-equal transforms
  ;;                                       :tracked-obj
  ;;                                       (cons hint-eval1 hint-eval2))))
  ;;   :hints(("Goal" :in-theory (enable svexlist-evals-equal)))))

  
  (fgl::def-fgl-rewrite svexlist-evals-equal-and-integerp-with-transforms-fgl
    (equal (svexlist-evals-equal-and-integerp-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))

                (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                                :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                                  :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                                :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                                  :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal-and-integerp (and (equal x-eval1 x-eval2) (integer-listp x-eval1)))
                ((mv hint1-upper hint1-lower) (4veclist-separate-upper-lower hint-eval1))
                ((mv hint2-upper hint2-lower) (4veclist-separate-upper-lower hint-eval2))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.
                (hint1 (list hint1-upper hint1-lower hint1-upper))
                (hint2 (list hint2-upper hint2-lower hint1-lower))
                ((mv iso-ok hint-iso1 hint-iso2) (fgl::fgl-make-isomorphic iso-ok hint1 hint2))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal-and-integerp transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct)))))


  
  

  (fgl::def-fgl-rewrite svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
    (equal (svexlist-evals-equal-and-integerp-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))
                (aigs (a4veclist-subnodes (append x-a4vecs hint-a4vecs)))
                ((mv x-eval1 hint-eval1 aigs-eval1)
                 (eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
                  x-a4vecs hint-a4vecs aigs aig-env1))
                ((mv x-eval2 hint-eval2 aigs-eval2)
                 (eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
                  x-a4vecs hint-a4vecs aigs aig-env2))
                ;; (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                ;;                 :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                ;;                   :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                ;; (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                ;;                 :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                ;;                   :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal-and-integerp (and (equal x-eval1 x-eval2) (integer-listp x-eval1)))
                ((mv hint1-upper hint1-lower) (4veclist-separate-upper-lower hint-eval1))
                ((mv hint2-upper hint2-lower) (4veclist-separate-upper-lower hint-eval2))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.  
                (hint1 (list hint1-upper hint1-lower hint1-upper aigs-eval1))
                (hint2 (list hint2-upper hint2-lower hint1-lower aigs-eval2))
                ((mv iso-ok hint-iso1 hint-iso2) (fgl::fgl-make-isomorphic iso-ok hint1 hint2))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal-and-integerp transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct)))))

  (fgl::def-fgl-rewrite svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme-2
    (equal (svexlist-evals-equal-and-integerp-with-transforms x env1 env2 symbolic-params transforms)
           (b* ((orig-x x)

                (env1 (make-fast-alist (svex-env-fix env1)))
                (env2 (make-fast-alist (svex-env-fix env2)))
                (svars (set::union
                        (svexlist-vars-for-symbolic-eval x env1 symbolic-params)
                        (svexlist-vars-for-symbolic-eval x env2 symbolic-params)))
                (x (svexlist-x-out-unused-vars x svars
                                               (symbolic-params-x-out-cond symbolic-params)))
                (x (maybe-svexlist-rewrite-fixpoint x (cdr (assoc :simplify symbolic-params))))
                (boolmasks (make-fast-alist
                            (hons-copy
                             (ec-call
                              (svar-boolmasks-fix (cdr (assoc :boolmasks symbolic-params)))))))
         
                ((unless (and (svex-env-check-boolmasks boolmasks env1)
                              (svex-env-check-boolmasks boolmasks env2)))
                 (b* ((?ign (cw "ERROR: some bits assumed to be Boolean were not~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv err x-a4vecs hint-a4vecs)
                 (time$ (svexlist->a4vecs-for-varlist-with-subexprs x svars boolmasks)
                        :msg "; svex->aigs: ~st sec, ~sa bytes.~%"))
                ((when err)
                 (b* ((?ign (cw "ERROR gathering AIG bits for variables: ~@0~%" err)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))

                ((mv ?err aig-env1)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env1)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env1 (make-fast-alist aig-env1))
                
                ((mv ?err aig-env2)
                 ;; ignore the error; it can't exist if the above doesn't
                 (time$ (svexlist->a4vec-aig-env-for-varlist x svars boolmasks env2)
                        :msg "; env -> aig env: ~st sec, ~sa bytes.~%"))
                (aig-env2 (make-fast-alist aig-env2))

                (?ign (fast-alist-free env1))
                (?ign (fast-alist-free env2))
                (aigs (a4veclist-upper-subnodes (append x-a4vecs hint-a4vecs)))
                ;; (x-upper-a4vecs (a4veclist->upper-a4vecs x-a4vecs))
                ((mv x-eval1 hint-eval1 aigs-eval1)
                 (eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
                  x-a4vecs hint-a4vecs aigs aig-env1))
                ((mv x-eval2 hint-eval2 aigs-eval2)
                 (eval-collection-for-svexlist-evals-equal-and-integerp-with-transforms-fgl-extreme
                  x-a4vecs hint-a4vecs aigs aig-env2))
                ;; (x-eval1 (time$ (a4veclist-eval x-a4vecs aig-env1)
                ;;                 :msg "; a4veclist-eval (x, env1): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval1 (time$ (a4veclist-eval hint-a4vecs aig-env1)
                ;;                   :msg "; a4veclist-eval (sub, env1): ~st sec, ~sa bytes.~%"))
                ;; (x-eval2 (time$ (a4veclist-eval x-a4vecs aig-env2)
                ;;                 :msg "; a4veclist-eval (x, env2): ~st sec, ~sa bytes.~%"))
                ;; (hint-eval2 (time$ (a4veclist-eval hint-a4vecs aig-env2)
                ;;                   :msg "; a4veclist-eval (sub, env2): ~st sec, ~sa bytes.~%"))
                (evals-equal-and-integerp (and (equal x-eval1 x-eval2) (integer-listp x-eval1)))
                ((mv hint1-upper hint1-lower) (4veclist-separate-upper-lower hint-eval1))
                ((mv hint2-upper hint2-lower) (4veclist-separate-upper-lower hint-eval2))
                ;; We are going to allow equivalences between the two
                ;; evaluations as well as the upper/lowers of the same
                ;; evaluation.  
                (hint1 (list hint1-upper hint2-upper aigs-eval1))
                (hint2 (list hint1-lower hint2-lower aigs-eval2))
                ((mv iso-ok hint-iso1 hint-iso2) (fgl::fgl-make-isomorphic iso-ok hint1 hint2))
                ((unless iso-ok)
                 (b* ((?ign (cw "ERROR: the equivalence hint objects couldn't be made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (len1 (fgl::syntax-bind len1 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso1)))))
                (len2 (fgl::syntax-bind len2 (fgl::g-concrete (len (fgl::fgl-object-bfrlist hint-iso2)))))
                ((unless (fgl::syntax-bind lens-equal (equal len1 len2)))
                 (b* ((?ign (cw "ERROR: the number of BFR objects in the ~
                                 equivalence hint objects wasn't equal after ~
                                 they were made isomorphic!~%"))
                      (?foo (break$)))
                   (fgl::abort-rewrite (and (svexlist-evals-equal orig-x env1 env2)
                                            (integer-listp (svexlist-eval orig-x env1))))))
                (transforms (transforms-update-fraig-configs-for-n-outputs len1 transforms)))
                
             (fgl::fgl-simplify-ordered evals-equal-and-integerp transforms
                                        :tracked-obj
                                        (cons hint-iso1 hint-iso2))))
    :hints(("Goal" :in-theory (e/d (svexlist-evals-equal
                                    SVEXLIST->A4VECS-FOR-VARLIST
                                    svexlist->a4vec-aig-env-for-varlist)
                                   (svexlist->a4vec-correct))))))
