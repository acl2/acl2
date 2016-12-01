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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "rsh-concat")
(include-book "../mods/lhs")
(include-book "rewrite-base")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (std::add-default-post-define-hook :fix))


(fty::deftagsum svex-select
  :parents (svex) ;; bozo what should this be?
  :layout :tree
  (:var ((name svar-p)
         (width natp)))
  (:part ((lsb svex-p)
          (width natp)
          (subexp svex-select-p))))

(local (xdoc::set-default-parents svex-select))

(define svex-select->width ((x svex-select-p))
  :returns (width natp :rule-classes :type-prescription)
  (svex-select-case x
    :var x.width
    :part x.width))


(define svex-select-to-svex ((x svex-select-p))
  :measure (svex-select-count x)
  :returns (svex-x svex-p)
  :verify-guards nil
  (svex-select-case x
    :var (svex-var x.name)
    :part (svcall partsel x.lsb (svex-int x.width)
                  (svex-concat (svex-select->width x.subexp)
                               (svex-select-to-svex x.subexp)
                               (svex-x))))
  ///
  (verify-guards svex-select-to-svex))

(define svex-select-to-svex-with-substitution ((x svex-select-p)
                                               (subst svex-p))
  :measure (svex-select-count x)
  :returns (svex-x svex-p)
  :verify-guards nil
  (svex-select-case x
    :var (svex-fix subst)
    :part (svcall partsel x.lsb (svex-int x.width)
                  (svex-concat (svex-select->width x.subexp)
                               (svex-select-to-svex-with-substitution x.subexp subst)
                               (svex-x))))
  ///
  (verify-guards svex-select-to-svex-with-substitution))
   




;; Procedure for performing an assignment.
;; We have an RHS expression (any svex), an LHS select,
;; (svex-select-p), and a state (bindings for variables).

;; Compose the state into the RHS and all LHS select indices -- in
;; particular, not the variable that the selects are selecting from (which in
;; the dynamic part is *svex-longest-static-prefix-var*, but in the static
;; part might be any variable).

;; Simplify the indices so that as many of them are constant as possible.

;; Split the LHS select into two LHS parts:
;; -- static: the outermost sub-select whose indices are all quotes
;; -- dynamic: the result of replacing the static part of the whole with a particular variable, *svex-longest-static-prefix-var*.

;; Crunch the static part into a lhs, and get the writemask from it.

;; Crunch the dynamic part with the RHS to produce the final expression to be
;; assigned to the static select.



(define svex-select->indices ((x svex-select-p))
  :guard (svex-select-p x)
  :returns (indices svexlist-p)
  :measure (svex-select-count x)
  (svex-select-case x
   :var nil
   :part (cons x.lsb (svex-select->indices x.subexp))))

(define svex-select-replace-indices ((x svex-select-p)
                                     (indices svexlist-p))
  :guard (equal (len indices) (len (svex-select->indices x)))
  :returns (new-x svex-select-p)
  :verify-guards nil
  :measure (svex-select-count x)
  (b* ((x (svex-select-fix x)))
    (svex-select-case x
      :var x
      :part (change-svex-select-part
             x :lsb (car indices)
             :subexp (svex-select-replace-indices x.subexp (cdr indices)))))
  ///
  (verify-guards svex-select-replace-indices
    :hints (("goal" :expand ((svex-select->indices x)
                             (svex-select-p x)))))

  ;; (local (in-theory (enable fty::equal-of-len)))

  (defthm svex-select-replace-indices-of-svex-select->indices
    (equal (svex-select-replace-indices x (svex-select->indices x))
           (svex-select-fix x))
    :hints(("Goal" :in-theory (enable (:i svex-select->indices))
            :induct (svex-select->indices x)
            :expand ((svex-select->indices x)
                     (:free (indices) (svex-select-replace-indices x indices)))
            :do-not-induct t)))

  (defthm svex-select->indices-of-replace-indices
    (implies (equal (len indices) (len (svex-select->indices x)))
             (equal (svex-select->indices (svex-select-replace-indices x indices))
                    (svexlist-fix indices)))
    :hints(("Goal" :induct (svex-select-replace-indices x indices)
            :expand ((svex-select->indices x)
                     (svex-select-replace-indices x indices)
                     (:free (name) (svex-select->indices (svex-select-var name width)))
                     (:free (lsb width subexp)
                      (svex-select->indices (svex-select-part lsb width subexp)))))))
            


  (deffixequiv svex-select-replace-indices
    :hints (("goal" :induct (svex-select-replace-indices x indices)
             :expand ((:free (indices) (svex-select-replace-indices x indices)))))))



(define svex-select-inner-var ((x svex-select-p))
  :returns (var svar-p)
  :measure (svex-select-count x)
  (svex-select-case x
    :var x.name
    :part (svex-select-inner-var x.subexp))
  ///
  (defthm svex-select-inner-var-of-replace-indices
    (equal (svex-select-inner-var (svex-select-replace-indices x indices))
           (svex-select-inner-var x))
    :hints(("Goal" :in-theory (enable svex-select-replace-indices)))))

(define svex-select-inner-width ((x svex-select-p))
  :returns (width natp :rule-classes :type-prescription)
  :measure (svex-select-count x)
  (svex-select-case x
    :var x.width
    :part (svex-select-inner-width x.subexp)))


(define svex-select-vars ((x svex-select-p))
  :returns (vars svarlist-p)
  (cons (svex-select-inner-var x)
        (svexlist-vars (svex-select->indices x)))
  ///
  (defthm svexlist-vars-of-svex-select->indices
    (implies (not (member v (svex-select-vars x)))
             (not (member v (svexlist-vars (svex-select->indices x))))))

  (defthm svex-select-not-inner-var-when-not-member-select-vars
    (implies (not (member v (svex-select-vars x)))
             (not (equal v (svex-select-inner-var x)))))

  (defthm svex-select-vars-of-replace-indices
    (implies (and (not (equal v (svex-select-inner-var x)))
                  (not (member v (svexlist-vars indices))))
             (not (member v (svex-select-vars (svex-select-replace-indices x indices)))))
    :hints(("Goal" :in-theory (enable svex-select-replace-indices
                                      svex-select-inner-var
                                      svex-select->indices)
            :induct (svex-select-replace-indices x indices)
            :expand ((svex-select-replace-indices x indices)))))

  (defthm svex-vars-of-svex-select-to-svex
    (implies (not (member v (svex-select-vars x)))
             (not (member v (svex-vars (svex-select-to-svex x)))))
    :hints(("Goal" :in-theory (enable svex-select-to-svex
                                      svex-select->indices
                                      svex-select-inner-var)
            :induct (svex-select-to-svex x))))

  (defthm svex-vars-of-svex-select-to-svex-with-substitution
    (implies (and (not (member v (svex-select-vars x)))
                  (not (member v (svex-vars subst))))
             (not (member v (svex-vars (svex-select-to-svex-with-substitution x subst)))))
    :hints(("Goal" :in-theory (enable svex-select-to-svex-with-substitution
                                      svex-select->indices
                                      svex-select-inner-var)
            :induct (svex-select-to-svex-with-substitution x subst)))))





(local (defthm-svex-eval-flag
         (defthm svex-eval-of-cons-non-var
           (implies (not (member (svar-fix v) (svex-vars x)))
                    (equal (svex-eval x (cons (cons v val) env))
                           (svex-eval x env)))
           :hints((and stable-under-simplificationp
                       '(:in-theory (enable svex-env-lookup
                                            svex-vars))))
           :flag expr)
         (defthm svexlist-eval-of-cons-non-var
           (implies (not (member (svar-fix v) (svexlist-vars x)))
                    (equal (svexlist-eval x (cons (cons v val) env))
                           (svexlist-eval x env)))
           :flag list)
         :hints ((fty::deffixequiv-mutual-default-default-hint 'svex-eval id world))))

(define svex-selects-merge ((outer svex-select-p)
                            (inner svex-select-p))
  :short "Apply one select operation to the result of another."
  :returns (composition svex-select-p)
  :measure (svex-select-count outer)
  :verify-guards nil
  (svex-select-case outer
      :var (svex-select-fix inner)
      :part (change-svex-select-part
             outer
             :subexp (svex-selects-merge outer.subexp inner)))
  ///
  ;; (deffixequiv svex-selects-merge
  ;;   :hints (("goal" :expand ((:free (outer) (svex-selects-merge outer inner))
  ;;                            (:free (inner) (svex-selects-merge outer inner))))))
  (verify-guards svex-selects-merge
    :hints (("goal" :expand ((svex-select-p outer)))))  
  
  (defthm svex-select->width-of-svex-select-merge
    (implies (equal (svex-select-inner-width outer) (svex-select->width inner))
             (equal (svex-select->width (svex-selects-merge outer inner))
                    (svex-select->width outer)))
    :hints(("Goal" :in-theory (enable svex-select-inner-width)
            :induct (svex-selects-merge outer inner)
            :expand ((svex-select->width outer)
                     (:free (lsb width subexp)
                      (svex-select->width (svex-select-part lsb width subexp)))))))

  (defret svex-selects-merge-is-svex-compose
    (b* ((inner-var (svex-select-inner-var outer)))
      (implies (and (not (member inner-var (svexlist-vars (svex-select->indices outer))))
                    (equal (svex-select-inner-width outer) (svex-select->width inner)))
               (equal (svex-eval (svex-select-to-svex (svex-selects-merge outer inner)) env)
                      (svex-eval (svex-select-to-svex outer)
                                 (cons (cons inner-var
                                             (svex-eval (svex-select-to-svex inner) env))
                                       env)))))
    :hints(("Goal" :in-theory (enable svexlist-eval)
            :induct (svex-selects-merge outer inner) 
            :expand ((svex-selects-merge outer inner)
                     (svex-select-inner-var outer)
                     (svex-select->indices outer)
                     (svex-select-to-svex outer)
                     (svex-select-inner-width outer)
                     (:free (lsb width subexp)
                      (svex-select-to-svex (svex-select-part lsb width subexp)))))
           (and stable-under-simplificationp
                '(:expand ((:free (name env) (svex-eval (svex-var name) env)))
                  :in-theory (enable svex-env-lookup)))))

  (defret svex-select->indices-of-svex-selects-merge
    (equal (svex-select->indices composition)
           (append (svex-select->indices outer)
                   (svex-select->indices inner)))
    :hints (("goal" :induct (svex-selects-merge outer inner)
             :expand ((svex-selects-merge outer inner)
                      (svex-select->indices outer)
                      (:free (lsb width subexp)
                       (svex-select->indices (svex-select-part lsb width subexp))))))))



(define svex-select-staticp ((x svex-select-p))
  :measure (svex-select-count x)
  (svex-select-case x
    :var t
    :part (and (svex-case x.lsb
                 :quote (4vec-index-p x.lsb.val)
                 :otherwise nil)
               (svex-select-staticp x.subexp)))
  ///
  (defthm svex-select-staticp-when-var
    (implies (svex-select-case x :var)
             (svex-select-staticp x)))

  (defthm svex-select-vars-when-staticp
    (implies (svex-select-staticp x)
             (equal (svex-select-vars x)
                    (list (svex-select-inner-var x))))
    :hints(("Goal" :in-theory (enable svex-select-vars
                                      svex-select-inner-var
                                      svex-select->indices
                                      svexlist-vars)))))

(define svex-select-split-static ((x svex-select-p))
  :returns (mv (staticp (equal staticp (svex-select-staticp x))
                        :hints(("Goal" :in-theory (enable svex-select-staticp))))
               (dynamic-part svex-select-p)
               (static-part svex-select-p))
  :measure (svex-select-count x)
  :verify-guards nil
  (svex-select-case x
    :var (mv t
             (svex-select-var *svex-longest-static-prefix-var*
                              x.width)
             (svex-select-fix x))
    :part (b* (((mv rest-staticp rest-dyn rest-stat)
                (svex-select-split-static x.subexp))
               ((when (and rest-staticp
                           (svex-case x.lsb
                             :quote (4vec-index-p x.lsb.val)
                             :otherwise nil)))
                (mv t
                    (svex-select-var *svex-longest-static-prefix-var*
                                     x.width)
                    (change-svex-select-part x :subexp rest-stat))))
            (mv nil (change-svex-select-part x :subexp rest-dyn) rest-stat)))
  ///
  (verify-guards svex-select-split-static)

  (local (in-theory (enable svex-select-staticp)))

  (defret svex-select-inner-var-of-split-static
    (and (equal (svex-select-inner-var dynamic-part) *svex-longest-static-prefix-var*)
         (equal (svex-select-inner-var static-part)
                (svex-select-inner-var x)))
    :hints (("goal" :induct t
             :expand ((svex-select-inner-var x)
                      (:free (lsb width subexp)
                       (svex-select-inner-var (svex-select-part lsb width subexp)))
                      (:free (name width)
                       (svex-select-inner-var (svex-select-var name width)))))))

  (defret svex-select-split-static-dynamic-type-when-staticp
    (implies staticp
             (equal (svex-select-kind dynamic-part) :var)))

  (defret svex-selects-merge-of-split-static
    (equal (svex-selects-merge dynamic-part static-part)
           (svex-select-fix x))
    :hints(("Goal" :in-theory (enable svex-selects-merge)
            :induct (svex-select-split-static x)
            :expand ((svex-select-split-static x))))))


(define svex-select-staticify-assignment ((x svex-select-p)
                                          (rhs svex-p)
                                          (lhs-var-value svex-p))
  :returns (mv (static-lhs svex-select-p)
               (static-rhs svex-p))
  :measure (svex-select-count x)
  :hints(("Goal" :in-theory (enable svex-select-staticp)))
  :verify-guards nil
  (b* (((when (svex-select-staticp x))
        (mv (svex-select-fix x)
            (svex-fix rhs)))
       ;; not a var because not static
       ((svex-select-part x)))
    ;; lhs[lsb +: width] = rhs
    ;; -->
    ;;  lhs = (part-install 0 innerwidth lhs (part-install lsb width lhs[innerwidth-1:0] rhs)
    (svex-select-staticify-assignment
     x.subexp
     (svcall partinst x.lsb (svex-int x.width)
             (svex-select-to-svex-with-substitution x.subexp lhs-var-value)
             rhs)
     lhs-var-value))
  ///
  (verify-guards svex-select-staticify-assignment)

  (defret svex-select-staticify-assignment-lhs-staticp
    (svex-select-staticp static-lhs))

  (defret svex-vars-of-svex-select-staticify-assignmane
    (implies (and (not (member v (svex-select-vars x)))
                  (not (member v (svex-vars rhs)))
                  (not (member v (svex-vars lhs-var-value))))
             (not (member v (svex-vars static-rhs))))
    :hints(("Goal" :in-theory (enable svex-select-vars
                                      svex-select-inner-var
                                      svex-select->indices))))

  (defret svex-select-vars-of-svex-select-staticify-assignment-lhs
    (implies (not (equal v (svex-select-inner-var x)))
             (not (member v (svex-select-vars static-lhs))))
    :hints(("Goal" :in-theory (enable svex-select-vars
                                      svex-select-inner-var
                                      svex-select->indices))))

  (defret svex-select-inner-var-of-svex-select-staticify-assignment
    (equal (svex-select-inner-var static-lhs)
           (svex-select-inner-var x))
    :hints(("Goal" :in-theory (enable svex-select-inner-var)))))


(define svex-select-to-lhs ((x svex-select-p))
  :guard (svex-select-staticp x)
  :returns (lhs lhs-p)
  :measure (svex-select-count x)
  :verify-guards nil
  (svex-select-case x
    :var (if (eql x.width 0)
             nil
           (list (make-lhrange
                  :atom (make-lhatom-var :name x.name
                                         :rsh 0)
                  :w x.width)))
    :part (b* ((inner-lhs (svex-select-to-lhs x.subexp))
               (rsh (2vec->val (svex-quote->val x.lsb))))
            (lhs-rsh rsh (lhs-concat (+ rsh x.width) inner-lhs nil))))
  ///
  (verify-guards svex-select-to-lhs
    :hints (("Goal" :expand ((svex-select-staticp x)))))

  (defret lhs-vars-of-svex-select-to-lhs
    (implies (not (equal v (svex-select-inner-var x)))
             (not (member v (lhs-vars lhs))))
    :hints(("Goal" :in-theory (enable lhatom-vars
                                      svex-select-inner-var)))))
  




;; (define match-partsel ((x svex-p))
;;   :returns (mv (matchedp)
;;                (lsb svex-p)
;;                (width natp :rule-classes :type-prescription)
;;                (in svex-p))
;;   (svex-case x
;;     :call
;;     (b* (((unless (and (eq x.fn 'partsel)
;;                        (eql (len x.args) 3)))
;;           (mv nil (svex-x) 0 (svex-x)))
;;          ((acl2::list lsb width in) x.args))
;;       (svex-case width
;;         :quote (if (and (2vec-p width.val)
;;                         (natp (2vec->val width.val)))
;;                    (mv t lsb (2vec->val width.val) in)
;;                  (mv nil (svex-x) 0 (svex-x)))
;;         :otherwise
;;         (mv nil (svex-x) 0 (svex-x))))
;;     :otherwise
;;     (mv nil (svex-x) 0 (svex-x)))
;;   ///
;;   (defret match-partsel-correct
;;     (implies matchedp
;;              (equal (4vec-part-select (svex-eval lsb env)
;;                                       (2vec width)
;;                                       (svex-eval in env))
;;                     (svex-eval x env)))
;;     :hints(("Goal" :in-theory (enable svex-apply
;;                                       4veclist-nth-safe))))

;;   (defret vars-of-match-partsel
;;     (implies (not (member v (svex-vars x)))
;;              (and (not (member v (svex-vars lsb)))
;;                   (not (member v (svex-vars in)))))
;;     :hints(("Goal" :in-theory (enable svexlist-vars)
;;             :expand ((svexlist-vars (cddr (svex-call->args x)))
;;                      (svexlist-vars (cdr (svex-call->args x)))
;;                      (svexlist-vars (svex-call->args x))))))


;;   (defretd match-partsel-correct-rewrite-svex-eval-of-x
;;     (implies matchedp
;;              (equal (svex-eval x env)
;;                     (4vec-part-select (svex-eval lsb env)
;;                                       (2vec width)
;;                                       (svex-eval in env))))
;;     :hints(("Goal" :in-theory (enable svex-apply
;;                                       4veclist-nth-safe))))

;;   (defret svex-count-of-match-partsel-lsb
;;     (implies matchedp
;;              (< (svex-count lsb) (svex-count x)))
;;     :rule-classes :linear)

;;   (defret svex-count-of-match-partsel-in
;;     (implies matchedp
;;              (< (svex-count in) (svex-count x)))
;;     :rule-classes :linear))
                    
               


;; ;; This is the format of an svex produced by any sort of variable access,
;; ;; proven in ../vl/expr.lisp (see
;; ;; vl-operandinfo-to-svex-longest-static-prefix).  In compiling procedural
;; ;; statements we take advantage of the restrictions on the form of these
;; ;; expressions to allow us to process assignments to dynamic selects.
;; (define svex-select-p ((x svex-p))
;;   :measure (svex-count x)
;;   :prepwork ((local (defthm svex-count-of-nth
;;                       (implies (< (nfix n) (len x))
;;                                (< (svex-count (nth n x))
;;                                   (svexlist-count x)))
;;                       :hints(("Goal" :in-theory (enable svexlist-count nth)
;;                               :induct (nth n x)))
;;                       :rule-classes :linear)))
;;   (svex-case x
;;     :var t
;;     :quote t ;; sometimes maybe a variable access reduces to just a quote
;;     :call
;;     (b* (((mv matched ?width lsbs msbs) (match-concat x))
;;          ((when matched)
;;           (and (equal msbs (svex-x))
;;                (svex-select-p lsbs)))
;;          ((mv matched ?lsb ?width in) (match-partsel x))
;;          ((when matched)
;;           (svex-select-p in)))
;;       nil))
;;   ///
;;   (deffixequiv svex-select-p)
;;   (defthmd svex-select-p-of-svex-call
;;     (equal (svex-select-p (svex-call x.fn x.args))
;;            (b* ((x.fn (fnsym-fix x.fn))
;;                 (x.args (sv::svexlist-fix x.args)))
;;              (case x.fn
;;                (concat (b* (((unless (eql (len x.args) 3)) nil)
;;                             ((acl2::nths width low high) x.args)
;;                             ((unless (svex-case width
;;                                        :quote (and (2vec-p width.val)
;;                                                    (natp (2vec->val width.val)))
;;                                        :otherwise nil))
;;                              nil)
;;                             ((unless (equal high (svex-x)))
;;                              nil))
;;                          (svex-select-p low)))
;;                (partsel (b* (((unless (eql (len x.args) 3)) nil)
;;                              ((acl2::nths ?lsb width in) x.args)
;;                              ((unless (svex-case width
;;                                         :quote (and (2vec-p width.val)
;;                                                     (natp (2vec->val width.val)))
;;                                         :otherwise nil))
;;                               nil))
;;                           ;; lsb can be whatever.
;;                           (svex-select-p in))))))
;;     :hints (("goal" :expand ((:free (fn args) (svex-select-p (svex-call fn args))))
;;              :in-theory (enable match-concat match-partsel))))

;;   (defthm svex-select-p-of-svex-quote
;;     (svex-select-p (svex-quote val)))

;;   (defthm svex-select-p-of-svex-var
;;     (svex-select-p (svex-var name)))

;;   (local
;;    (defthm match-ext-when-svex-select-p
;;      (implies (svex-select-p x)
;;               (not (mv-nth 0 (match-ext x))))
;;      :hints(("Goal" :in-theory (enable match-ext match-concat match-partsel)))))
    

;;   (local
;;    (defthm match-concat-when-svex-var
;;      (implies (svex-case x :var)
;;               (not (mv-nth 0 (match-concat x))))
;;      :hints(("Goal" :in-theory (enable match-concat)))))

;;   (defthm svex-select-p-of-svex-concat
;;     (implies (svex-select-p base)
;;              (svex-select-p (svex-concat size base (svex-x))))
;;     :hints(("Goal" :in-theory (e/d ((:i svex-concat)
;;                                     svex-select-p-of-svex-call)
;;                                    (default-car default-cdr nth
;;                                      svex-select-p
;;                                      svex-p-when-maybe-svex-p))
;;             :induct (svex-concat size base y)
;;             :do-not-induct t
;;             :expand ((svex-concat size base (svex-x))
;;                      (svex-concat 0 base (svex-x))
;;                      (svex-select-p base)))))

;;   (defthm svex-select-p-of-partsel-in
;;     (implies (and (svex-select-p x)
;;                   (mv-nth 0 (match-partsel x)))
;;              (svex-select-p (mv-nth 3 (match-partsel x))))
;;     :hints(("Goal" :in-theory (enable match-partsel match-concat))))

;;   (defthm svex-select-p-of-concat-lsbs
;;     (implies (and (svex-select-p x)
;;                   (mv-nth 0 (match-concat x)))
;;              (svex-select-p (mv-nth 2 (match-concat x))))
;;     :hints(("Goal" :in-theory (enable match-concat)))))




;; (define svex-select->indices ((x svex-p))
;;   :guard (svex-select-p x)
;;   :returns (indices svexlist-p)
;;   :measure (svex-count x)
;;   (svex-case x
;;    :var nil
;;    :quote nil
;;    :call (b* (((mv match ?width lsbs ?msbs) (match-concat x))
;;               ((when match) (svex-select->indices lsbs))
;;               ((mv match lsb ?width in) (match-partsel x)))
;;            (and match
;;                 (cons lsb (svex-select->indices in)))))
;;   ///
;;   (defret svex-select->indices-of-svex-concat
;;     (implies (svex-select-p lsbs)
;;              (equal (svex-select->indices (svex-concat width lsbs (svex-x)))
;;                     (if (zp width)
;;                         nil
;;                       (svex-select->indices lsbs))))
;;     :hints(("Goal" :in-theory (enable svex-concat match-concat match-partsel match-ext)
;;             :induct (svex-concat width lsbs msbs)
;;             :expand ((svex-select-p lsbs))))))

;; (define svex-select-replace-indices ((x svex-p)
;;                                      (indices svexlist-p))
;;   :guard (and (svex-select-p x)
;;               (equal (len indices) (len (svex-select->indices x))))
;;   :returns (new-x (and (svex-p new-x)
;;                        (implies (svex-select-p x)
;;                                 (svex-select-p new-x)))
;;                   :hints(("Goal" :in-theory (enable svex-select-p-of-svex-call
;;                                                     svex-int))))
;;   :verify-guards nil
;;   :measure (svex-count x)
;;   (b* ((x (svex-fix x)))
;;     (svex-case x
;;       :var x
;;       :quote x
;;       :call (b* (((mv match width lsbs ?msbs) (match-concat x))
;;                  ((when match)
;;                   (b* ((new-lsbs (svex-select-replace-indices lsbs indices)))
;;                     (svcall concat (svex-int width) new-lsbs (svex-x))))
;;                  ((mv match ?lsb width in) (match-partsel x))
;;                  ((unless (mbt (and match t))) x)
;;                  (new-in (svex-select-replace-indices in (cdr indices))))
;;               (svcall partsel (car indices) (svex-int width) new-in))))
;;   ///
;;   (verify-guards svex-select-replace-indices
;;     :hints (("goal" :expand ((svex-select->indices x)
;;                              (svex-select-p x)))))

;;   (local (defthmd equal-of-cons-rw
;;            (equal (equal (cons a b) c)
;;                   (and (consp c)
;;                        (equal (car c) a)
;;                        (equal (cdr c) b)))))

;;   ;; (local (defthm equal-const
;;   ;;          (implies (and (syntaxp (and (quotep c) (quotep a)))
;;   ;;                        (acl2-numberp a)
;;   ;;                        (acl2-numberp c))
;;   ;;                   (equal (equal (+ c x) a)
;;   ;;                          (equal (fix x) (- a c))))))

;;   ;; (local (defthm len-equal-0
;;   ;;          (equal (equal (len x) 0)
;;   ;;                 (atom x))))

;;   (local (in-theory (enable fty::equal-of-len)))

;;   (defthm svex-select-replace-indices-of-svex-select->indices
;;     (implies (svex-select-p x)
;;              (equal (svex-select-replace-indices x (svex-select->indices x))
;;                     (svex-fix x)))
;;     :hints(("Goal" :in-theory (enable svex-select-p-of-svex-call
;;                                       (:i svex-select->indices)
;;                                       match-concat
;;                                       match-partsel)
;;             :induct (svex-select->indices x)
;;             :expand ((svex-select->indices x)
;;                      (:free (indices) (svex-select-replace-indices x indices))
;;                      (svex-select-p x))
;;             :do-not-induct t)
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable equal-of-cons-rw
;;                                      svex-int)))))


;;   (deffixequiv svex-select-replace-indices
;;     :hints (("goal" :induct (svex-select-replace-indices x indices)
;;              :expand ((:free (indices) (svex-select-replace-indices x indices)))))))


;; (define svex-constselect-p ((x svex-p))
;;   :guard (svex-select-p x)
;;   :returns (constp)
;;   :measure (svex-count x)
;;   (svex-case x
;;    :var t
;;    :quote t
;;    :call (b* (((mv match ?width lsbs ?msbs) (match-concat x))
;;               ((when match) (svex-constselect-p lsbs))
;;               ((mv match lsb ?width in) (match-partsel x)))
;;            (or (not match)
;;                (and (svex-case lsb :quote)
;;                     (svex-constselect-p in)))))
;;   ///
;;   (defthm svex-constselect-p-is-quotesp-of-indices
;;     (equal (svex-constselect-p x)
;;            (svexlist-quotesp (svex-select->indices x)))
;;     :hints(("Goal" :in-theory (enable svex-select->indices
;;                                       svexlist-quotesp)))))

;; (define svex-select-inner-expr ((x svex-p))
;;   :guard (svex-select-p x)
;;   :measure (svex-count x)
;;   :returns (inner (and (svex-p inner)
;;                        (not (equal (svex-kind inner) :call))))
;;   :guard-hints (("goal" :expand ((svex-select-p x))))
;;   (b* ((x (svex-fix x)))
;;     (svex-case x
;;       :var x
;;       :quote x
;;       :call (b* (((mv match ?width lsbs ?msbs) (match-concat x))
;;                  ((when match) (svex-select-inner-expr lsbs))
;;                  ((mv match ?lsb ?width in) (match-partsel x))
;;                  ((unless (mbt (and match t))) (svex-x)))
;;               (svex-select-inner-expr in)))))




;; (define svex-selects-merge ((outer svex-p)
;;                             (inner svex-p))
;;   :short "Apply one select operation to the result of another."
;;   :returns (composition svex-p)
;;   :guard (svex-select-p outer)
;;   :measure (svex-count outer)
;;   :verify-guards nil
;;   (b* ((outer (svex-fix outer))
;;        (inner (svex-fix inner)))
;;     (svex-case outer
;;       :var inner
;;       :quote outer
;;       :call (b* (((mv match width lsbs ?msbs) (match-concat outer))
;;                  ((when match) (svex-concat width (svex-selects-merge lsbs inner) (svex-x)))
;;                  ((mv match lsb width in) (match-partsel outer))
;;                  ((unless (mbt (and match t))) outer))
;;               (svcall partsel lsb (svex-int width) (svex-selects-merge in inner)))))
;;   ///
;;   (deffixequiv svex-selects-merge
;;     :hints (("goal" :expand ((:free (outer) (svex-selects-merge outer inner))
;;                              (:free (inner) (svex-selects-merge outer inner))))))
;;   (verify-guards svex-selects-merge
;;     :hints (("goal" :expand ((svex-select-p outer)))))

;;   (defret svex-select-p-of-svex-selects-merge
;;     (implies (and (svex-select-p outer)
;;                   (svex-select-p inner))
;;              (svex-select-p composition))
;;     :hints(("Goal" :in-theory (enable svex-select-p-of-svex-call
;;                                       svex-int))))

;;   (local (in-theory (enable fty::equal-of-len)))
  
  
;;   (defret svex-selects-merge-is-svex-compose
;;     (b* ((inner-var (svex-select-inner-expr outer)))
;;       (implies (and (equal (svex-kind inner-var) :var)
;;                     (not (member (svex-var->name inner-var)
;;                                  (svexlist-vars (svex-select->indices outer))))
;;                     (svex-select-p outer))
;;                (equal (svex-eval (svex-selects-merge outer inner) env)
;;                       (svex-eval outer (cons (cons (svex-var->name inner-var)
;;                                                    (svex-eval inner env))
;;                                              env)))))
;;     :hints(("Goal" :in-theory (enable svexlist-eval
;;                                       match-partsel
;;                                       match-concat)
;;             :induct (svex-selects-merge outer inner) 
;;             :expand ((svex-selects-merge outer inner)
;;                      (svex-select-inner-expr outer)
;;                      (svex-select->indices outer)
;;                      (svex-select-p outer)))
;;            (and stable-under-simplificationp
;;                 '(:expand ((:free (env) (svex-eval outer env)))
;;                   :in-theory (enable svex-env-lookup)))))

;;   (defret svex-selects-merge-when-inner-quote
;;     (b* ((inner-var (svex-select-inner-expr outer)))
;;       (implies (and (equal (svex-kind inner-var) :quote)
;;                     (svex-select-p outer))
;;                (equal (svex-eval (svex-selects-merge outer inner) env)
;;                       (svex-eval outer env))))
;;     :hints(("Goal" :in-theory (enable svexlist-eval
;;                                       match-partsel
;;                                       match-concat)
;;             :induct (svex-selects-merge outer inner) 
;;             :expand ((svex-selects-merge outer inner)
;;                      (svex-select-inner-expr outer)
;;                      (svex-select->indices outer)
;;                      (svex-select-p outer)))
;;            (and stable-under-simplificationp
;;                 '(:expand ((:free (env) (svex-eval outer env)))
;;                   :in-theory (enable svex-env-lookup)))))

;;   (defret svex-selects-merge-static-preserves-constselectp-static
;;     (implies (and (svexlist-quotesp (svex-select->indices outer))
;;                   (svexlist-quotesp (svex-select->indices inner))
;;                   (svex-select-p outer)
;;                   (svex-select-p inner))
;;              (svexlist-quotesp (svex-select->indices composition)))
;;     :hints(("Goal" :induct (svex-selects-merge outer inner)
;;             :expand ((svex-selects-merge outer inner)
;;                      (svex-select-p outer)
;;                      (:free (fn args) (svex-select->indices (svex-call fn args)))
;;                      (:free (a b) (svexlist-quotesp (cons a b))))
;;             :in-theory (enable svex-select->indices match-concat match-partsel)))))
                 


;; (define svex-selects-remerge-static ((dynamic svex-p)
;;                                      (static svex-p))
;;   :guard (and (svex-select-p dynamic)
;;               (svex-select-p static))
;;   :measure (svex-count dynamic)
;;   :returns (mv (new-dynamic svex-p)
;;                (new-static svex-p))
;;   :verify-guards nil
;;   :short "Move some constant selects out of dynamic and onto static."
;;   :long "<p>Dynamic and static are assumed to be parts of a variable select,
;; where static is a select operation on the actual variable and dynamic is a
;; select on @(see *svex-longest-static-prefix-var*) which is a stand-in for
;; static.  We remove any inner static selects from dynamic and put them onto the
;; outside of static, preserving the composition of dynamic and static.</p>"
;;   (b* ((dynamic (svex-fix dynamic))
;;        (static (svex-fix static)))
;;     (svex-case dynamic
;;       :var (mv dynamic static)
;;       :quote (mv dynamic static)
;;       :call (b* (((when (svex-constselect-p dynamic))
;;                   (mv *svex-longest-static-prefix-var*
;;                       (svex-selects-merge dynamic static)))
;;                  ((mv match width lsbs ?msbs) (match-concat dynamic))
;;                  ((when match)
;;                   (b* (((mv new-dynamic new-static) (svex-selects-remerge-static lsbs static)))
;;                     (mv (svex-concat width new-dynamic (svex-x)) new-static)))
;;                  ((mv match lsb width in) (match-partsel dynamic))
;;                  ((unless (mbt (and match t))) (mv dynamic static))
;;                  ((mv new-dynamic new-static) (svex-selects-remerge-static in static)))
;;               (mv (svcall partsel lsb (svex-int width) new-dynamic) new-static))))
;;   ///
;;   (verify-guards svex-selects-remerge-static
;;     :hints(("Goal" :expand ((svex-select-p dynamic)))))

;;   (local (in-theory (enable fty::equal-of-len)))

;;   (defret svex-selects-remerge-static-is-compose
;;     (implies (and (equal (svex-select-inner-expr dynamic) *svex-longest-static-prefix-var*)
;;                   (not (member *svex-longest-static-prefix-var*
;;                                (svexlist-vars (svex-select->indices dynamic))))
;;                   (svex-select-p dynamic))
;;              (equal (svex-eval new-dynamic
;;                                (cons (cons *svex-longest-static-prefix-var*
;;                                            (svex-eval new-static env))
;;                                      env))
;;                     (svex-eval dynamic
;;                                (cons (cons *svex-longest-static-prefix-var*
;;                                            (svex-eval static env))
;;                                      env))))
;;     :hints(("Goal" :in-theory (enable svexlist-eval
;;                                       match-partsel
;;                                       match-concat)
;;             :induct (svex-selects-remerge-static dynamic static) 
;;             :expand ((svex-selects-remerge-static dynamic static)
;;                      (svex-select-inner-expr dynamic)
;;                      (svex-select->indices dynamic)
;;                      (svex-select-p dynamic)))
;;            (and stable-under-simplificationp
;;                 '(:expand ((:free (env) (svex-eval dynamic env)))
;;                   :in-theory (enable svex-env-lookup)))))


;;   (defret svex-selects-remerge-static-preserves-constselectp-static
;;     (implies (and (svexlist-quotesp (svex-select->indices static))
;;                   (svex-select-p dynamic)
;;                   (svex-select-p static))
;;              (svexlist-quotesp (svex-select->indices new-static)))
;;     :hints(("Goal" :induct (svex-selects-remerge-static dynamic static)
;;             :expand ((svex-selects-remerge-static dynamic static))))))

;; example:
;;      (lhs[i1 +: w1])[i2 +: w2] = rhs
;;  lhs[i1 +: w1] = 


;; (define svex-select-assignment-expr ((select svex-p "dynamic select expression from LHS")
;;                                      (rhs-expr svex-p "expression to assign")
;;                                      (static-lhs svex-p "static expression on which the dynamic select operates"))
;;   :guard (svex-select-p select)
;;   :guard-hints (("goal" :expand ((svex-select-p select))))
;;   :measure (svex-count select)
;;   :returns (new-rhs svex-p)
;;   (b* ((rhs-expr (svex-fix rhs-expr)))
;;     (svex-case select
;;       :var rhs-expr
;;       :quote (svex-x) ;; shouldn't happen
;;       :call (b* (((mv match width lsbs ?msbs) (match-concat select))
;;                  ;; a[5:0] = b  -->   a = { b[5:0], a >> 5 }
;;                  ((when match)
;;                   (svex-select-assignment-expr
;;                    lsbs
;;                    (svcall partinst
;;                            (svex-int 0)
;;                            (svex-int width)
;;                            (svex-selects-merge lsbs static-lhs)
;;                            rhs-expr)
;;                    static-lhs))
;;                  ((mv match lsb width in) (match-partsel select))
;;                  ((unless (mbt (and match t))) (svex-x)))
;;               (svex-select-assignment-expr
;;                in
;;                (svcall partinst lsb (svex-int width)
;;                        (svex-selects-merge in static-lhs)
;;                        rhs-expr)
;;                static-lhs)))))



