; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")
(include-book "centaur/misc/outer-local" :dir :system)
(local (include-book "eval-g-base-help"))

(local (include-book "hyp-fix"))
(local (include-book "var-bounds"))

(set-inhibit-warnings "theory")

(local (defthm eval-g-base-apply-of-equal
         (equal (eval-g-base-ev (cons 'equal (kwote-lst (list x y))) a)
                (equal x y))))

(local (defthm equal-of-components-to-number-fn
         (implies (and (integerp arn) (integerp ain)
                       (integerp brn) (integerp bin))
                  (equal (equal (components-to-number-fn
                                 arn 1 ain 1)
                                (components-to-number-fn
                                 brn 1 bin 1))
                         (and (equal arn brn)
                              (equal ain bin))))))


(local (in-theory (disable acl2-count)))

(local
 (encapsulate nil
   (local (include-book "arithmetic/top-with-meta" :dir :system))
   (defthm equal-of-components-to-number-fn2
     (implies (and (integerp arn) (natp ard)
                   (integerp brn) (natp brd)
                   (integerp ain) (integerp aid)
                   (integerp bin) (integerp bid)
                   (not (equal ard 0))
                   (not (equal brd 0))
                   (equal ard brd)
                   (not (equal arn brn)))
              (not (equal (components-to-number-fn
                           arn ard ain aid)
                          (components-to-number-fn
                           brn brd bin bid)))))

   (defthm equal-of-components-to-number-fn3
     (implies (and (integerp arn) (natp aid)
                   (integerp brn) (natp bid)
                   (integerp ain) (integerp ard)
                   (integerp bin) (integerp brd)
                   (not (equal aid 0))
                   (not (equal bid 0))
                   (equal aid bid)
                   (not (equal ain bin)))
              (not (equal (components-to-number-fn
                           arn ard ain aid)
                          (components-to-number-fn
                           brn brd bin bid)))))

   (defthm components-to-number-fn-normalize-zeros1
     (equal (components-to-number-fn rn 0 in id)
            (components-to-number-fn 0 1 in id)))

   (defthm components-to-number-fn-normalize-zeros2
     (equal (components-to-number-fn rn rd in 0)
            (components-to-number-fn rn rd 0 1)))

   (defthm components-to-number-fn-normalize-zeros3
     (implies (syntaxp (not (equal rd ''1)))
              (equal (components-to-number-fn 0 rd in id)
                     (components-to-number-fn 0 1 in id))))

   (defthm components-to-number-fn-normalize-zeros4
     (implies (syntaxp (not (equal id ''1)))
              (equal (components-to-number-fn rn rd 0 id)
                     (components-to-number-fn rn rd 0 1))))))

(local
 (define equal-of-numbers ((a general-numberp)
                           (b general-numberp)
                           hyp)
   :guard-hints (("goal" :in-theory (enable g-if-fn)))
   (b* (((mv arn ard ain aid)
         (general-number-components a))
        ((mv brn brd bin bid)
         (general-number-components b)))
     (g-if-mbe (gret (mk-g-boolean (bfr-and (bfr-=-uu ard brd)
                                            (bfr-=-uu aid bid))))
               (gret (mk-g-boolean (bfr-and (bfr-or (bfr-=-uu nil ard)
                                                    (bfr-=-ss arn brn))
                                            (bfr-or (bfr-=-uu nil aid)
                                                    (bfr-=-ss ain bin)))))
               (gret (g-apply 'equal (gl-list a b)))))
   ///
   (acl2::outer-local
    (def-hyp-congruence equal-of-numbers
      :hints(("Goal" :in-theory (enable equal-of-numbers))))

    (local (include-book "arithmetic/top-with-meta" :dir :system))
    (defthm equal-of-numbers-correct
      (implies (and (general-numberp a)
                    (general-numberp b)
                    (bfr-hyp-eval hyp (car env)))
               (equal (eval-g-base (mv-nth 0 (equal-of-numbers a b hyp)) env)
                      (equal (eval-g-base a env)
                             (eval-g-base b env))))
      :hints(("Goal" :in-theory
              (e/d* ((:ruleset general-object-possibilities)
                     boolean-list-bfr-eval-list)))))

    (defthm dependencies-of-equal-of-numbers
      (implies (and (not (gobj-depends-on k p a))
                    (not (gobj-depends-on k p b))
                    (general-numberp a)
                    (general-numberp b))
               (not (gobj-depends-on k p (mv-nth 0 (equal-of-numbers a b hyp)))))))))

(acl2::finish-with-outer-local)

(def-g-fn equal
  ;; Once we've ruled out the case where they're both atoms, start by recurring
  ;; down to non-ITEs on both a and b:
  `(let ((a x) (b y))
     (cond ((hqual a b) (gret t))
           ((and (general-concretep a) (general-concretep b))
            (gret (hons-equal (general-concrete-obj a) (general-concrete-obj b))))
           ((and (consp a) (eq (tag a) :g-ite))
            (if (zp clk)
                (gret (g-apply 'equal (gl-list a b)))
              (let* ((test (g-ite->test a))
                     (then (g-ite->then a))
                     (else (g-ite->else a)))
                (g-if (gret test)
                      (,gfn then b hyp clk config bvar-db state)
                      (,gfn else b hyp clk config bvar-db state)))))
           ((and (consp b) (eq (tag b) :g-ite))
            (if (zp clk)
                (gret (g-apply 'equal (gl-list a b)))
              (let* ((test (g-ite->test b))
                     (then (g-ite->then b))
                     (else (g-ite->else b)))
                (g-if (gret test)
                      (,gfn a then hyp clk config bvar-db state)
                      (,gfn a else hyp clk config bvar-db state)))))
           ((or (atom a)
                (not (member-eq (tag a) '(:g-var :g-apply))))
            (cond ((or (atom b)
                       (not (member-eq (tag b) '(:g-var :g-apply))))
                   (cond ((general-booleanp a)
                          (gret (and (general-booleanp b)
                                     (mk-g-boolean (bfr-iff (general-boolean-value a)
                                                            (general-boolean-value b))))))
                         ((general-numberp a)
                          (if (general-numberp b)
                              (equal-of-numbers a b hyp)
                            (gret nil)))
                         ((general-consp a)
                          (if (general-consp b)
                              (g-if (,gfn (general-consp-car a)
                                          (general-consp-car b)
                                          hyp clk config bvar-db state)
                                    (,gfn (general-consp-cdr a)
                                          (general-consp-cdr b)
                                          hyp clk config bvar-db state)
                                    (gret nil))
                            (gret nil)))
                         (t (gret nil))))
                  (t (gret (g-apply 'equal (gl-list a b))))))
           (t (gret (g-apply 'equal (gl-list a b))))))
  :hyp-hints `(("goal" :induct ,gcall
                :in-theory (disable (:d ,gfn)
                                    set::double-containment
                                    eval-g-base-alt-def
                                    equal-of-booleans-rewrite)
                :expand ((:free (hyp) ,gcall)
                         (:free (hyp) ,(subst 'x 'y gcall))))))

;; (cond ((and (general-concretep a) (general-concretep b))
;;             (hqual (general-concrete-obj a) (general-concrete-obj b)))
;;            ((zp clk)
;;             (g-apply 'equal (gl-list a b)))
;;            (t (pattern-match a
;;                 ((g-ite test then else)
;;                  (g-if test
;;                        (,gfn then b hyp clk config bvar-db state)
;;                        (,gfn else b hyp clk config bvar-db state)))
;;                 (& (pattern-match b
;;                      ((g-ite test then else)
;;                       (g-if test
;;                             (,gfn a then hyp clk config bvar-db state)
;;                             (,gfn a else hyp clk config bvar-db state)))
;;                      ((g-var &)
;;                       (or (equal a b)
;;                           (g-apply 'equal (gl-list a b))))
;;                      ((g-apply fn args)
;;                       (pattern-match a
;;                         ((g-apply !fn aargs)
;;                          (g-if (,gfn args aargs hyp clk config bvar-db state)
;;                                t
;;                                (g-apply 'equal (gl-list a b))))
;;                         (& (g-apply 'equal (gl-list a b)))))
;;                      (& (pattern-match a
;;                           ((g-var &) (g-apply 'equal (gl-list a b)))
;;                           ((g-apply & &) (g-apply 'equal (list a b)))
;;                           (& (cond
;;                               ((hqual a b) t)
;;                               ((general-booleanp a)
;;                                (if (general-booleanp b)
;;                                    (mk-g-boolean (bfr-iff (general-boolean-value a)
;;                                                         (general-boolean-value b)))
;;                                  nil))
;;                               ((general-numberp a)
;;                                (if (general-numberp b)
;;                                    (equal-of-numbers a b hyp)
;;                                  nil))
;;                               ((general-consp a)
;;                                (if (general-consp b)
;;                                    (g-if (,gfn (general-consp-car a)
;;                                                (general-consp-car b)
;;                                                hyp clk config bvar-db state)
;;                                          (,gfn (general-consp-cdr a)
;;                                                (general-consp-cdr b)
;;                                                hyp clk config bvar-db state)
;;                                          nil)
;;                                  nil))
;;                               (t nil))))))))))))



;; (def-gobjectp-thm equal
;;   :hints `(("Goal" :in-theory (e/d* ()
;;                                     ((:definition ,gfn)
;;                                      general-boolean-value
;;                                      general-boolean-value-cases
;;                                      gobjectp-def
;;                                      general-concretep-def
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      hyp-fix
;;                                      booleanp-gobjectp
;;                                      equal-of-booleans-rewrite
;;                                      tag-when-g-number-p
;;                                      tag-when-g-boolean-p
;;                                      tag-when-g-concrete-p
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)
;;                                      (:ruleset gl-tag-forward)))
;;             :induct (,gfn x y hyp clk config bvar-db state)
;;             :expand ((,gfn x y hyp clk config bvar-db state)
;;                      (,gfn x x hyp clk config bvar-db state)))
;;            (and stable-under-simplificationp
;;                 '(:in-theory (e/d* (booleanp-gobjectp)
;;                                     ((:definition ,gfn)
;;                                      general-boolean-value
;;                                      general-boolean-value-cases
;;                                      gobjectp-def
;;                                      general-concretep-def
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      hyp-fix
;;                                      equal-of-booleans-rewrite
;;                                      tag-when-g-number-p
;;                                      tag-when-g-boolean-p
;;                                      tag-when-g-concrete-p
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)
;;                                      (:ruleset gl-tag-forward)))))))

(encapsulate nil
  (local (in-theory (e/d* (g-if-fn g-or-fn)
                          (general-concretep-def
                           equal-of-booleans-rewrite
                           iff-implies-equal-not
                           (:type-prescription true-under-hyp)
                           (:type-prescription false-under-hyp)
                           (:type-prescription general-booleanp)
                           (:type-prescription general-numberp)
                           (:type-prescription general-concretep)
                           hyp-fix-of-hyp-fixedp
                           (:meta mv-nth-cons-meta)
                           zp-open default-<-2 default-<-1
                           (:type-prescription zp)
                           (:type-prescription hyp-fix)
                           default-car default-cdr
                           not
                           (:rules-of-class :type-prescription :here))
                          ((:type-prescription general-number-components)))))
  (verify-g-guards
   equal
   :hints `(("Goal" :in-theory (disable ,gfn)))))






(local (include-book "clause-processors/just-expand" :dir :System))



(def-gobj-dependency-thm equal
    :hints `((acl2::just-induct-and-expand ,gcall)
             '(:in-theory (disable ,gfn))
             (and stable-under-simplificationp
                  `(:expand (,',gcall
                             ,',(subst 'x 'y gcall)
                             (eval-g-base x env)
                             (eval-g-base y env)
                             (eval-g-base nil env)
                             (eval-g-base-list nil env)
                             (eval-g-base t env))
                    :do-not-induct t))))


(encapsulate nil
  
  (local
   (in-theory (e/d* (
                     possibilities-for-x-1

                     possibilities-for-x-2
                     possibilities-for-x-3
                     possibilities-for-x-4
                     possibilities-for-x-5
                     possibilities-for-x-6
                     possibilities-for-x-7
                     possibilities-for-x-8
                     possibilities-for-x-9

                     eval-g-base-g-apply
                     eval-g-base-of-gl-cons
                     mk-g-boolean-correct-for-eval-g-base

                     gobj-depends-on-of-g-apply
                     gobj-depends-on-of-gl-cons
                     gobj-list-depends-on-of-gl-cons

                     general-concretep-not-general-consp
                     general-concretep-not-general-booleanp
                     general-concretep-not-general-numberp
                     general-concrete-obj-when-consp-for-eval-g-base
                     general-concrete-obj-when-numberp
                     general-concrete-obj-when-booleanp
                     general-concrete-obj-when-atom
                     general-booleanp-of-atom

                     (:type-prescription bfr-eval)
                     (:type-prescription components-to-number-fn)
                     (:rules-of-class :executable-counterpart :here)
                     booleanp-compound-recognizer

                     bfr-eval-bfr-binary-and
                     bfr-eval-bfr-not
                     bfr-eval-bfr-binary-or
                     bfr-eval-booleanp
                     gtests-nonnil-correct-for-eval-g-base

                     cons-equal
                     eval-g-base-apply-of-equal
                     bfr-eval-bfr-iff
                     equal-of-numbers-correct
                     general-numberp-of-atom

                     eval-g-base-list-of-gl-cons
                     hons-equal
                     general-concrete-obj-of-atomic-constants
                     general-concretep-of-atomic-constants)
                    ((general-concrete-obj)
                     (general-concretep)
                     (kwote-lst)
                     logcons
                     set::double-containment
                     bfr-list->s
                     bfr-list->u
                     eval-g-base-alt-def))))

  (local
   (make-event
    `(in-theory
      (enable (:induction ,(gl-fnsym 'equal))))))




  (def-g-correct-thm equal eval-g-base
    :hints `((acl2::just-induct-and-expand ,gcall)
             (and stable-under-simplificationp
                  `(:expand (,',gcall
                             ,',(subst 'x 'y gcall)
                             (eval-g-base x env)
                             (eval-g-base y env)
                             (eval-g-base nil env)
                             (eval-g-base-list nil env)
                             (eval-g-base t env))
                    :do-not-induct t)))
    ;; (case-match id
    ;;   ((('0 '1) (n . &) . &)
    ;;    (if (member n '(3 4))
    ;;        `(:in-theory
    ;;          (disable possibilities-for-x-1
    ;;                   possibilities-for-x-2
    ;;                   possibilities-for-x-3
    ;;                   possibilities-for-x-4
    ;;                   possibilities-for-x-5
    ;;                   possibilities-for-x-7
    ;;                   possibilities-for-x-8
    ;;                   possibilities-for-x-9)
    ;;          :expand ((,',gfn x y hyp clk config bvar-db state)
    ;;                   (eval-g-base ,(if (eql n 3) 'x 'y) env)
    ;;                   (eval-g-base nil env)
    ;;                   (eval-g-base t env)))
    ;;      '(:use ((:instance possibilities-for-x)
    ;;              (:instance possibilities-for-x (x y)))))))
    ))
