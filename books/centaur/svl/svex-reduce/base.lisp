
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
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "SVL")

(include-book "projects/rp-rewriter/top" :dir :system)
(include-book "../fnc-defs")
(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "centaur/sv/svex/eval-dollar" :dir :system)
(include-book "tools/templates" :dir :system)

(defun hons-list-macro (acl2::lst)
  (declare (xargs :guard t))
  (if (consp acl2::lst)
      (cons 'hons
            (cons (car acl2::lst)
                  (cons (hons-list-macro (cdr acl2::lst))
                        nil)))
    nil))

(DEFMACRO hons-list (&REST ARGS)
  (hons-list-macro ARGS))

(defmacro svex-eval-lemma-tmpl (form)
  `(progn
     ,(acl2::template-subst
       form
       :features '(:normal-eval)
       :str-alist '(("<$>" . ""))
       :pkg-sym 'pkg
       )
     ,(acl2::template-subst
       form
       :features '(:dollar-eval)
       :atom-alist '((svex-eval . svex-eval$)
                     (svex-apply . svex-apply$)
                     (svexlist-eval . svexlist-eval$)
                     (svex-alist-eval . svex-alist-eval$)
                     (svexl-alist-eval . svexl-alist-eval$)
                     (svexl-node-eval . svexl-node-eval$)
                     (svexl-eval . svexl-eval$)
                     (svexl-nodelist-eval . svexl-nodelist-eval$))
       :str-alist '(("<$>" . "$")
                    ("SVEX-EVAL" . "SVEX-EVAL$")
                    ("SVEX-APPLY" . "SVEX-APPLY$")
                    ("SVEXLIST-EVAL" . "SVEXLIST-EVAL$")
                    ("SVEX-ALIST-EVAL" . "SVEX-ALIST-EVAL$")
                    ("SVEXL-ALIST-EVAL" . "SVEXL-ALIST-EVAL$")
                    ("SVEXL-NODE-EVAL" . "SVEXL-NODE-EVAL$")
                    ("SVEXL-EVAL" . "SVEXL-EVAL$")
                    ("SVEXL-NODELIST-EVAL" . "SVEXL-NODELIST-EVAL$"))
       :pkg-sym 'pkg
       )
     ))

(defsection integerp-of-svex-extn

  (define svex-foreign-fnsym-p (fn)
    (and (sv::fnsym-p fn)
         (not (assoc-equal fn
                           sv::*svex-op-table*)))
    ///
    (define svex-foreign-fnsym-fix ((x svex-foreign-fnsym-p))
      :enabled t
      (mbe :exec x
           :logic (if (svex-foreign-fnsym-p x) x 'identity)))
    (local
     (in-theory (enable svex-foreign-fnsym-fix)))
    (fty::deffixtype svex-foreign-fnsym
      :pred svex-foreign-fnsym-p
      :fix svex-foreign-fnsym-fix
      :equiv svex-foreign-fnsym-equiv
      :define t))

  (fty::defprod integerp-of-svex-extn
    ((fn svex-foreign-fnsym)
     (arg-len posp :rule-classes (:rewrite :type-prescription)))
    :layout :fulltree)

  (fty::deflist integerp-of-svex-extn-list
    :elt-type integerp-of-svex-extn
    :true-listp t
    )

  (defthm integerp-of-svex-extn-listp-is-alist-p
    (implies (integerp-of-svex-extn-list-p lst)
             (alistp lst))
    :rule-classes (:rewrite :forward-chaining :type-prescription))

  (svex-eval-lemma-tmpl
   (defun-sk integerp-of-svex-extn-correct<$> (obj)
     ;;(declare (xargs :guard (integerp-of-svex-extn-p obj)))
     (forall (args env)
             (b* (((integerp-of-svex-extn obj)))
               (implies (and (equal (len args) obj.arg-len)
                             (integer-listp (svexlist-eval args env)))
                        (integerp (svex-eval `(,obj.fn . ,args) env)))))))

  (svex-eval-lemma-tmpl
   (defun integerp-of-svex-extn-correct<$>-lst (lst)
     (if (atom lst)
         (equal lst nil)
       (and (integerp-of-svex-extn-correct<$> (car lst))
            (integerp-of-svex-extn-correct<$>-lst (cdr lst))))))

  ;; (define ha-s (x y)
  ;;   :verify-guards nil
  ;;   :returns (res integerp :hyp (and (integerp x)
  ;;                                    (integerp y)))
  ;;   (sv::4vec-bitxor x y)
  ;;   ///
  ;;   (defwarrant ha-s))

  ;; (local
  ;;  (defthm equal-of-len-with-contant
  ;;    (implies (and (syntaxp (quotep c))
  ;;                  (posp c))
  ;;             (equal (equal (len x) c)
  ;;                    (and (consp x)
  ;;                         (equal (len (cdr x)) (1- c)))))))

  ;; (defthm integerp-of-svex-extn-for-ha-s-correct
  ;;   (implies (APPLY$-WARRANT-HA-S)
  ;;            (integerp-of-svex-extn-correct$ 'ha-s 2))
  ;;   :hints (("Goal"
  ;;            :do-not-induct t
  ;;            :in-theory (e/d (ha-s
  ;;                             SVEX-EVAL$
  ;;                             svex-kind
  ;;                             SVEX-CALL->FN
  ;;                             SVEX-CALL->ARGS
  ;;                             SVEXLIST-EVAL$
  ;;                             svex-apply$)
  ;;                            (RP::DUMMY-LEN-EQUIV
  ;;                             len)))))

  (in-theory (disable (:e SVL::INTEGERP-OF-SVEX-EXTN-CORRECT$-LST)
                      (:e SVL::INTEGERP-OF-SVEX-EXTN-CORRECT$)))
  )

(defsection width-of-svex-extn

  #!acl2
  (local (flag::make-flag all-vars1-flag all-vars1))
  #!acl2
  (local (defthm-all-vars1-flag
           (defthm true-listp-of-all-vars1
             (implies (true-listp ans)
                      (true-listp (all-vars1 term ans)))
             :hints ('(:expand ((all-vars1 term ans))))
             :flag all-vars1)
           (defthm true-listp-of-all-vars1-lst
             (implies (true-listp ans)
                      (true-listp (all-vars1-lst lst ans)))
             :hints ('(:expand ((all-vars1-lst lst ans))))
             :flag all-vars1-lst)))

  #!acl2(defthm true-listp-of-all-fnnames1-type
          (implies (true-listp acc)
                   (true-listp (all-fnnames1 flg x acc)))
          :rule-classes :type-prescription)

  (local
   (in-theory (disable acl2::all-vars1
                       acl2::all-fnnames1
                       subsetp-equal)))

  (define safe-max (x y)
    (and (natp x)
         (natp y)
         (max x y)))

  (define safe-min (x y)
    (and (natp x)
         (natp y)
         (min x y)))

  (define width-of-svex-extn-formula-p (x)
    (and (pseudo-termp x)
         (subsetp-equal
          (acl2::all-fnnames x)
          '(if + bitp equal safe-max safe-min nth > < not))
         (subsetp-equal
          (acl2::all-vars x)
          '(widths args)))
    ///
    (define width-of-svex-extn-formula-fix ((x width-of-svex-extn-formula-p))
      :enabled t
      (mbe :exec x
           :logic (if (width-of-svex-extn-formula-p x) x ''nil)))
    (local
     (in-theory (enable width-of-svex-extn-formula-fix)))
    (fty::deffixtype width-of-svex-extn-formula
      :pred width-of-svex-extn-formula-p
      :fix width-of-svex-extn-formula-fix
      :equiv width-of-svex-extn-formula-equiv
      :define t))

  (fty::defprod width-of-svex-extn
    ((fn svex-foreign-fnsym)
     (arg-len posp :rule-classes (:rewrite :type-prescription))
     (formula width-of-svex-extn-formula)
     )
    :layout :fulltree)

  (fty::deflist width-of-svex-extn-list
    :elt-type width-of-svex-extn
    :true-listp t
    )

  #|(define maybe-nat-listp (lst)
  (if (atom lst)
  (equal lst nil)
  (and (acl2::maybe-natp (car lst))
  (maybe-nat-listp (cdr lst)))))|#

  (define 4vec-correct-width-p (width val)
    :verify-guards nil
    (implies (natp width)
             (equal (4vec-part-select 0 width val)
                    val)))

  (define 4vec-correct-widths-p (widths vals )
    :verify-guards nil
    (if (or (atom widths)
            (atom vals))
        (and (equal widths nil)
             (equal vals nil))
      (and (4vec-correct-width-p (car widths)
                                 (car vals))
           (4vec-correct-widths-p (cdr widths)
                                  (cdr vals)))))

  (define width-of-svex-extn-formula-eval ((formula)
                                           (args true-listp)
                                           (widths true-listp))
    :guard-hints (("Goal"
                   :in-theory (e/d (width-of-svex-extn-formula-p) ())))
    (cond ((equal formula 'args)
           (list 'quote args))
          ((equal formula 'widths)
           (list 'quote widths))
          ((and (quotep formula)
                (consp (cdr formula)))
           (unquote formula))
          (t (case-match formula
               (('safe-max a b)
                (b* ((a (width-of-svex-extn-formula-eval a args widths))
                     (b (width-of-svex-extn-formula-eval b args widths)))
                  (safe-max a b)))
               (('safe-min a b)
                (b* ((a (width-of-svex-extn-formula-eval a args widths))
                     (b (width-of-svex-extn-formula-eval b args widths)))
                  (safe-min a b)))
               (('+ a b)
                (b* ((a (width-of-svex-extn-formula-eval a args widths))
                     (b (width-of-svex-extn-formula-eval b args widths)))
                  (and (natp a) (natp b) (+ a b))))
               (('nth a 'widths)
                (b* ((a (nfix (width-of-svex-extn-formula-eval a args widths))))
                  (nth a widths)))
               (('nth a 'args)
                (b* ((a (nfix (width-of-svex-extn-formula-eval a args widths))))
                  (nth a args)))
               (('if x y z)
                (if (width-of-svex-extn-formula-eval x args widths)
                    (width-of-svex-extn-formula-eval y args widths)
                  (width-of-svex-extn-formula-eval z args widths)))
               (('equal x y)
                (equal (width-of-svex-extn-formula-eval x args widths)
                       (width-of-svex-extn-formula-eval y args widths)))
               (('< x y)
                (b* ((x (width-of-svex-extn-formula-eval x args widths))
                     (y (width-of-svex-extn-formula-eval y args widths)))
                (and (integerp x) (integerp y) (< x y))))
               (('> x y)
                (b* ((x (width-of-svex-extn-formula-eval x args widths))
                     (y (width-of-svex-extn-formula-eval y args widths)))
                (and (integerp x) (integerp y) (> x y))))
               (('not x)
                (not (width-of-svex-extn-formula-eval x args widths)))
               (('bitp a)
                (b* ((a (width-of-svex-extn-formula-eval a args widths)))
                  (bitp a)))
               (&
                (acl2::raise
                 "Formula is in unsupported format: ~p0" formula))
               ))))

  (defun-sk width-of-svex-extn-correct$ (obj)
    ;;(declare (xargs :guard (width-of-svex-extn-p obj)))
    (forall
     (args widths env)
     (b* (((width-of-svex-extn obj) obj))
       (implies (and (equal (len args) obj.arg-len)
                     (equal (len widths) obj.arg-len)
                     (4vec-correct-widths-p widths
                                            (svexlist-eval$ args env)))
                (4vec-correct-width-p
                 (width-of-svex-extn-formula-eval obj.formula
                                                  args
                                                  widths)
                 (svex-eval$ (sv::svex-call obj.fn args)
                             env))))))

  (defun width-of-svex-extn-correct$-lst (lst)
    (if (atom lst)
        (equal lst nil)
      (and (width-of-svex-extn-correct$ (car lst))
           (width-of-svex-extn-correct$-lst (cdr lst)))))

  (in-theory (disable (:e SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST)
                      (:e SVL::WIDTH-OF-SVEX-EXTN-CORRECT$)))

  )

;; (INCLUDE-BOOK "projects/apply/top" :DIR :SYSTEM)

;; (define ha-s (x y)
;;   :verify-guards nil
;;   (sv::4vec-bitxor x y)
;;   ///
;;   (defwarrant ha-s))

;; (local
;;  (defthm equal-of-len-with-constant
;;    (implies (and (syntaxp (quotep c))
;;                  (posp c))
;;             (equal (equal (len x) c)
;;                    (and (consp x)
;;                         (equal (len (cdr x)) (1- c)))))))

;; (defconst *ha-s-width-formula*
;;   '(safe-max (nth '0 widths)
;;              (nth '1 widths)))

;; (include-book "../4vec-lemmas")

;; (defthm 4VEC-CORRECT-WIDTH-P-of-not-natp
;;   (implies (not (natp width))
;;            (4VEC-CORRECT-WIDTH-P width x))
;;   :hints (("Goal"
;;            :in-theory (e/d (4VEC-CORRECT-WIDTH-P) ()))))

;; (skip-proofs
;;  (defthm 4VEC-CORRECT-WIDTH-P-of-4VEC-BITXOR
;;   (implies (and (4VEC-CORRECT-WIDTH-P w1 a1)
;;                 (4VEC-CORRECT-WIDTH-P w2 a2))
;;            (4VEC-CORRECT-WIDTH-P (safe-max w1 w2)
;;                                  (sv::4vec-bitxor a1 a2)))
;;   :hints (("Goal"
;;            :in-theory (e/d (4VEC-CORRECT-WIDTH-P
;;                             4vec-part-select-of-4vec-bitxor-better
;;                             safe-max)
;;                            ())))))

;; (defthm width-of-svex-extn-correct$-of-ha-s
;;   (b* ((obj (make-width-of-svex-extn
;;              :fn 'ha-s
;;              :arg-len 2
;;              :formula *ha-s-width-formula*)))
;;     (implies (APPLY$-WARRANT-HA-S)
;;              (width-of-svex-extn-correct$ obj)))
;;   :hints (("Goal"
;;            :in-theory (e/d (4VEC-CORRECT-WIDTHS-P
;;                             ;;4VEC-CORRECT-WIDTH-P
;;                             ;;SAFE-MAX
;;                             nth
;;                             SVEXLIST-EVAL$
;;                             ;;SVEX-EVAL$-CORRECT-WIDTHS-P
;;                             ;;SVEX-EVAL$-CORRECT-WIDTH-P
;;                             SVEX-EVAL$
;;                             svex-kind
;;                             ;;SVEX-CALL->ARGS
;;                             ;;SVEX-CALL->fn
;;                             SVEX-APPLY$
;;                             HA-S
;;                             ;;SAFE-MAX
;;                             4vec-part-select-of-4vec-bitxor-better
;;                             WIDTH-OF-SVEX-EXTN-FORMULA-EVAL)
;;                            (;;nth
;;                             natp)))))

;;;;

(fty::defprod svex-reduce-config
  ((width-extns width-of-svex-extn-list)
   (integerp-extns integerp-of-svex-extn-list)
   (skip-bitor/and/xor-repeated :default nil)
   (keep-missing-env-vars :default nil)
   )
  :layout :tree
  )



(with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks
      svex-reduce-formula-checks
      (acl2::logbit$inline
       bits
       integerp)))
