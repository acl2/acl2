;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (January 13th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "evaluator")

(local
 (defthm acl2-count-of-car-of-pseudo-term-list-fix
   (implies (consp (pseudo-term-list-fix term-lst))
            (< (acl2-count (pseudo-term-fix (car (pseudo-term-list-fix term-lst))))
               (acl2-count (pseudo-term-list-fix term-lst))))
   :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                      pseudo-term-fix))))
 )

(local
 (defthm acl2-count-of-cadr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (cadr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm acl2-count-of-caddr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (caddr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm acl2-count-of-cadddr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (cadddr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(set-state-ok t)

(defines partial-eval-mutual-recursion
  :verify-guards nil
  :hints (("Goal" :in-theory (disable len)))
  :short "Partial-eval returns (mv err eval). Unlike magic-ev, when it can't
  evaluate a term because of lack of alist bindings, it will result in err
  being t."

  (define partial-eval ((term pseudo-termp)
                        (alst symbol-alistp)
                        state)
    :returns (mv (err booleanp) evaluation)
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         (alst (symbol-alist-fix alst))
         ((if (acl2::variablep term))
          (if (assoc-equal term alst)
              (mv nil (cdr (assoc-equal term alst)))
            (mv t nil)))
         ((if (acl2::fquotep term)) (mv nil (cadr term)))
         ((cons fn actuals) term)
         ((if (equal fn 'if))
          (b* (((unless (equal (len actuals) 3))
                (prog2$ (er hard? 'partial-eval=>simplify
                            "If statement is malformed: ~p0~%" term)
                        (mv t nil)))
               ((list cond then else) actuals)
               ((if (equal then else)) (partial-eval then alst state))
               ((mv err-cond eval-cond) (partial-eval cond alst state))
               ((mv err-then eval-then) (partial-eval then alst state))
               ((mv err-else eval-else) (partial-eval else alst state))
               ((if (and (null err-then) (null err-else)
                         (equal eval-then eval-else)))
                (mv nil eval-then))
               ((if err-cond) (mv t nil))
               ((if (null eval-cond)) (mv err-else eval-else)))
            (mv err-then eval-then)))
         ((mv err eval-actuals) (partial-eval-list actuals alst state))
         ((if err) (mv t nil))
         ((if (pseudo-lambdap fn))
          (b* ((formals (lambda-formals fn))
               (body (lambda-body fn))
               (new-alst (pairlis$ formals eval-actuals)))
            (partial-eval body new-alst state)))
         ((mv err evaled)
          (acl2::magic-ev-fncall fn eval-actuals state t nil))
         ((if err)
          (prog2$ (er hard? 'partial-eval=>partial-eval
                      "partial-eval's use of acl2::magic-ev-fncall resulted ~
                       in an error. The call is (acl2::magic-ev-fncall ~p0 ~
                       ~p1 state t nil).~%" fn eval-actuals)
                  (mv t nil))))
      (mv nil evaled)))

  (define partial-eval-list ((term-lst pseudo-term-listp)
                             (alst symbol-alistp)
                             state)
    :returns (mv (err booleanp) (evaluation true-listp))
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) (mv nil nil))
         ((cons lst-hd lst-tl) term-lst)
         ((mv err eval-hd) (partial-eval lst-hd alst state))
         ((if err) (mv err nil))
         ((mv err eval-tl) (partial-eval-list lst-tl alst state))
         ((if err) (mv err nil)))
      (mv nil (cons eval-hd eval-tl))))
  )

(verify-guards partial-eval)

#|
(partial-eval '(integerp x) '((x . x)) state)
(partial-eval '(integerp x) '((x . 1)) state)
(partial-eval '(integerp x) nil state)
(partial-eval '(if (maybe-integerp x)
                   (if (integerp x) 't 'nil)
                 'nil)
              nil state)
(partial-eval '(if (maybe-integerp y)
                   (if (integerp x) 't 'nil)
                 'nil)
              '((y . 1/2)) state)
(partial-eval '(if (maybe-integerp x)
                   (if (integerp y) 't 'nil)
                 'nil)
              '((y . 1/2)) state)
|#
