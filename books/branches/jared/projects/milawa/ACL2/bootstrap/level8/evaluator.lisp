; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "definitions")
(%interactive)


(%autoadmit flag-generic-evaluator)
(%autoadmit generic-evaluator)
(%autoadmit generic-evaluator-list)

(%autoprove definition-of-generic-evaluator
            (%enable default generic-evaluator generic-evaluator-list)
            (%restrict default flag-generic-evaluator (equal x 'x)))

(%autoprove definition-of-generic-evaluator-list
            (%enable default generic-evaluator generic-evaluator-list)
            (%restrict default flag-generic-evaluator (equal x 'x)))

(%autoprove flag-generic-evaluator-when-term
            (%enable default generic-evaluator))

(%autoprove flag-generic-evaluator-when-list
            (%enable default generic-evaluator-list))

(%autoprove generic-evaluator-list-when-not-consp
            (%restrict default definition-of-generic-evaluator-list (equal x 'x)))

(%autoprove generic-evaluator-list-of-cons
            (%restrict default definition-of-generic-evaluator-list (equal x '(cons a x))))

(%autoprove true-listp-of-generic-evaluator-list
            (%cdr-induction x))

(%autoprove forcing-len-of-cdr-of-generic-evaluator-list
            (%cdr-induction x))

(%autoprove consp-of-generic-evaluator-list
            (%cdr-induction x))



(defmacro %flag-generic-evaluator-induction (flag x defs n)
  `(%induct (two-nats-measure ,n (rank ,x))

            ((and (equal ,flag 'term)
                  (zp ,n))
             nil)

            ((and (equal ,flag 'term)
                  (not (zp ,n))
                  (logic.functionp ,x)
                  (equal (logic.function-name ,x) 'if)
                  (equal (len (logic.function-args ,x)) '3))
             (((,flag 'term) (,x (first (logic.function-args ,x))))
              ((,flag 'term) (,x (second (logic.function-args ,x))))
              ((,flag 'term) (,x (third (logic.function-args ,x))))))

             ((and (equal ,flag 'term)
                   (not (zp ,n))
                   (logic.functionp ,x)
                   (not (and (equal (logic.function-name ,x) 'if)
                             (equal (len (logic.function-args ,x)) '3))))
              (((,flag 'list) (,x (logic.function-args ,x)))
               ((,flag 'term)
                (x
                 (logic.substitute
                  (logic.=rhs (definition-list-lookup (logic.function-name ,x) ,defs))
                  (pair-lists
                   (logic.function-args
                    (logic.=lhs (definition-list-lookup (logic.function-name ,x) ,defs)))
                   (cdr (flag-generic-evaluator 'list
                                                (logic.function-args ,x)
                                                ,defs ,n)))))
                (,n (- ,n '1)))))

             ((and (equal ,flag 'term)
                   (not (zp ,n))
                   (logic.lambdap ,x))
              (((,flag 'list) (,x (logic.lambda-actuals ,x)))
               ((,flag 'term)
                (,x (logic.substitute
                    (logic.lambda-body ,x)
                    (pair-lists (logic.lambda-formals ,x)
                                (cdr (flag-generic-evaluator 'list
                                                             (logic.lambda-actuals ,x)
                                                             ,defs ,n)))))
                (,n (- ,n '1)))))

             ((and (equal ,flag 'term)
                   (not (zp ,n))
                   (not (logic.functionp ,x))
                   (not (logic.lambdap ,x)))
              nil)

             ((and (not (equal ,flag 'term))
                   (consp ,x))
              (((,flag 'term) (,x (car ,x)))
               ((,flag 'list) (,x (cdr ,x)))))

             ((and (not (equal ,flag 'term))
                   (not (consp ,x)))
              nil)))

;; (defmacro %flag-generic-evaluator-induction (flag x defs n)
;;   `(%induct (two-nats-measure ,n (rank ,x))
;;             ((and (equal ,flag 'term)
;;                   (zp ,n))
;;              nil)
;;             ((and (equal ,flag 'term)
;;                   (not (zp ,n))
;;                   (logic.constantp ,x))
;;              nil)
;;             ((and (equal ,flag 'term)
;;                   (not (zp ,n))
;;                   (logic.variablep ,x))
;;              nil)
;;             ((and (equal ,flag 'term)
;;                   (not (zp ,n))
;;                   (logic.functionp ,x)
;;                   (equal (logic.function-name ,x) 'if)
;;                   (equal (len (logic.function-args ,x)) '3))
;;              (((,flag 'term) (,x (first (logic.function-args ,x))))
;;               ((,flag 'term) (,x (second (logic.function-args ,x))))
;;               ((,flag 'term) (,x (third (logic.function-args ,x))))))
;;              ((and (equal ,flag 'term)
;;                    (not (zp ,n))
;;                    (logic.functionp ,x)
;;                    (not (and (equal (logic.function-name ,x) 'if)
;;                              (equal (len (logic.function-args ,x)) '3))))
;;               (((,flag 'list) (,x (logic.function-args ,x)))
;;                ((,flag 'term)
;;                 (x
;;                  (logic.substitute
;;                   (logic.=rhs (definition-list-lookup (logic.function-name ,x) ,defs))
;;                   (pair-lists
;;                    (logic.function-args
;;                     (logic.=lhs (definition-list-lookup (logic.function-name ,x) ,defs)))
;;                    (cdr (flag-generic-evaluator 'list
;;                                                 (logic.function-args ,x)
;;                                                 ,defs ,n)))))
;;                 (,n (- ,n '1)))))
;;              ((and (equal ,flag 'term)
;;                    (not (zp ,n))
;;                    (logic.lambdap ,x))
;;               (((,flag 'list) (,x (logic.lambda-actuals ,x)))
;;                ((,flag 'term)
;;                 (,x (logic.substitute
;;                     (logic.lambda-body ,x)
;;                     (pair-lists (logic.lambda-formals ,x)
;;                                 (cdr (flag-generic-evaluator 'list
;;                                                              (logic.lambda-actuals ,x)
;;                                                              ,defs ,n)))))
;;                 (,n (- ,n '1)))))
;;              ((and (equal ,flag 'term)
;;                    (not (zp ,n))
;;                    (not (logic.constantp ,x))
;;                    (not (logic.variablep ,x))
;;                    (not (logic.functionp ,x))
;;                    (not (logic.lambdap ,x)))
;;               nil)
;;              ((and (not (equal ,flag 'term))
;;                    (consp ,x))
;;               (((,flag 'term) (,x (car ,x)))
;;                ((,flag 'list) (,x (cdr ,x)))))
;;              ((and (not (equal ,flag 'term))
;;                    (not (consp ,x)))
;;               nil)))

;; (defthmd open-generic-evaluator-when-zp
;;   (implies (and (syntaxp (equal x 'x))
;;                 (zp n))
;;            (equal (generic-evaluator x defs n)
;;                   nil))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable definition-of-generic-evaluator))))

;; (defthmd open-generic-evaluator-when-logic.constantp
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (zp n))
;;                 (logic.constantp x))
;;            (equal (generic-evaluator x defs n)
;;                   x))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable definition-of-generic-evaluator))))

;; (defthmd open-generic-evaluator-when-logic.variablep
;;   (implies (and (syntaxp (equal x 'x))
;;                 (logic.variablep x))
;;            (equal (generic-evaluator x defs n)
;;                   nil))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable definition-of-generic-evaluator))))

;; (defthmd open-generic-evaluator-when-if
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (zp n))
;;                 (logic.functionp x)
;;                 (equal (logic.function-name x) 'if)
;;                 (equal (len (logic.function-args x)) 3))
;;            (equal (generic-evaluator x defs n)
;;                   (let* ((args (logic.function-args x))
;;                          (eval-test (generic-evaluator (first args) defs n)))
;;                     (and eval-test
;;                          (if (logic.unquote eval-test)
;;                              (generic-evaluator (second args) defs n)
;;                            (generic-evaluator (third args) defs n))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (e/d (definition-of-generic-evaluator)
;;                                  ((:executable-counterpart ACL2::force))))))

;; (defthmd open-generic-evaluator-when-not-if
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (zp n))
;;                 (logic.functionp x)
;;                 (not (equal (logic.function-name x) 'if)))
;;            (equal (generic-evaluator x defs n)
;;                   (let* ((name (logic.function-name x))
;;                          (args (logic.function-args x))
;;                          (eval-args (generic-evaluator-list args defs n)))
;;                     (and eval-args
;;                          (let ((values (cdr eval-args)))
;;                            (if (memberp name (domain (logic.initial-arity-table)))
;;                                (and (equal (cdr (lookup name (logic.initial-arity-table))) (len values))
;;                                     (logic.base-evaluator (logic.function name values)))
;;                              (let* ((def (definition-list-lookup name defs)))
;;                                (and def
;;                                     (let ((formals (logic.function-args (logic.=lhs def)))
;;                                           (body    (logic.=rhs def)))
;;                                       (and (equal (len formals) (len values))
;;                                            (generic-evaluator (logic.substitute body (pair-lists formals values))
;;                                                               defs (- n 1))))))))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (e/d (definition-of-generic-evaluator)
;;                                  ((:executable-counterpart ACL2::force))))))

;; (defthmd open-generic-evaluator-when-not-length-three
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (zp n))
;;                 (logic.functionp x)
;;                 (not (equal (len (logic.function-args x)) 3)))
;;            (equal (generic-evaluator x defs n)
;;                   (let* ((name (logic.function-name x))
;;                          (args (logic.function-args x))
;;                          (eval-args (generic-evaluator-list args defs n)))
;;                     (and eval-args
;;                          (let ((values (cdr eval-args)))
;;                            (if (memberp name (domain (logic.initial-arity-table)))
;;                                (and (equal (cdr (lookup name (logic.initial-arity-table))) (len values))
;;                                     (logic.base-evaluator (logic.function name values)))
;;                              (let* ((def (definition-list-lookup name defs)))
;;                                (and def
;;                                     (let ((formals (logic.function-args (logic.=lhs def)))
;;                                           (body    (logic.=rhs def)))
;;                                       (and (equal (len formals) (len values))
;;                                            (generic-evaluator (logic.substitute body (pair-lists formals values))
;;                                                               defs (- n 1))))))))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal"
;;           :expand (generic-evaluator x defs n)
;;           :in-theory (e/d (definition-of-generic-evaluator)
;;                           ((:executable-counterpart ACL2::force))))))

;; (defthmd open-generic-evaluator-when-logic.lambdap
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (zp n))
;;                 (logic.lambdap x))
;;            (equal (generic-evaluator x defs n)
;;                   (let ((formals (logic.lambda-formals x))
;;                         (body    (logic.lambda-body x))
;;                         (actuals (logic.lambda-actuals x)))
;;                     (let ((eval-actuals (generic-evaluator-list actuals defs n)))
;;                       (and eval-actuals
;;                            (let ((values (cdr eval-actuals)))
;;                              (generic-evaluator (logic.substitute body (pair-lists formals values))
;;                                                 defs (- n 1))))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (e/d (definition-of-generic-evaluator)
;;                                  ((:executable-counterpart ACL2::force))))))

;; (defthmd open-generic-evaluator-when-degenerate
;;   (implies (and (syntaxp (equal x 'x))
;;                 (not (logic.constantp x))
;;                 (not (logic.variablep x))
;;                 (not (logic.functionp x))
;;                 (not (logic.lambdap x)))
;;            (equal (generic-evaluator x defs n)
;;                   nil))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable definition-of-generic-evaluator))))

;; (deftheory open-generic-evaluator-theory
;;   '(open-generic-evaluator-when-zp
;;     open-generic-evaluator-when-logic.constantp
;;     open-generic-evaluator-when-logic.variablep
;;     open-generic-evaluator-when-if
;;     open-generic-evaluator-when-not-if
;;     open-generic-evaluator-when-not-length-three
;;     open-generic-evaluator-when-logic.lambdap
;;     open-generic-evaluator-when-degenerate))







;; (%autoprove open-generic-evaluator-when-zp
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-logic.constantp
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-logic.variablep
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-if
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-not-if
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-not-length-three
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-logic.lambdap
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))

;; (%autoprove open-generic-evaluator-when-degenerate
;;             (%restrict default definition-of-generic-evaluator (equal x 'x)))


;; (%create-theory open-generic-evaluator-theory)
;; (%enable open-generic-evaluator-theory
;;          open-generic-evaluator-when-zp
;;          open-generic-evaluator-when-logic.constantp
;;          open-generic-evaluator-when-logic.variablep
;;          open-generic-evaluator-when-if
;;          open-generic-evaluator-when-not-if
;;          open-generic-evaluator-when-not-length-three
;;          open-generic-evaluator-when-logic.lambdap
;;          open-generic-evaluator-when-degenerate)



;; But I think it may be relevant to note that there wasn't much of a savings at all by
;; using the opener theory instead of the definitions themselves.  With the original
;; induction scheme, we're looking at 338K with openers versus 346K with restrict.
;;
;;  -  also consider consolidated induction schemes, and see if they are any use.
;;     (they might work using the restrict style, even if they aren't suited for openers.)
;;   -- Wow!  That reduced the proof to 110M conses.  And, the compiling time was only
;;      a minute. (of course building the skeleton took longer than that).
;;
;;  -  also try opening the functions right away, not waiting for one pass of auto
;;     to go first.  eeeeh, this seems bad.
;;
;;  - how about not forcing until we've issued the restrict hints?  hrmn, that seems to
;;    be very slow during rewriting.  i got bored and didn't let it finish.

;; 338K conses, 1306 seconds to compile.  damn.
;; (%autoprove lemma-for-forcing-logic.constantp-of-cdr-of-generic-evaluator
;;             (%flag-generic-evaluator-induction flag x defs n)
;;             (%auto :strategy (cleanup split urewrite))
;;             (%disable default  ;; speed hint
;;                       logic.termp-when-logic.formulap
;;                       logic.constantp-when-logic.variablep
;;                       logic.variablep-when-logic.constantp
;;                       logic.constantp-when-logic.functionp
;;                       same-length-prefixes-equal-cheap
;;                       not-equal-when-less
;;                       not-equal-when-less-two)
;;             (%crewrite default)
;;             (%enable default open-generic-evaluator-theory))


;; trying new induction scheme.
;; orig scheme: 346k conses this way.  bleh.  but only 1134 seconds to compile.
;; new scheme: way fewer initial goals (4500 vs 50k)

;; also, consider not forcing until we open up the definitions?
(%autoprove lemma-for-forcing-logic.constantp-of-cdr-of-generic-evaluator
            (%flag-generic-evaluator-induction flag x defs n)
            (%auto)
            (%restrict default definition-of-generic-evaluator (equal x 'x))
            (%restrict default definition-of-generic-evaluator-list (equal x 'x))
            (%auto :steps 90))


(%autoprove forcing-logic.constantp-of-cdr-of-generic-evaluator
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-generic-evaluator)
                             (flag 'term))))

(%autoprove forcing-logic.constant-listp-of-cdr-of-generic-evaluator-list
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-generic-evaluator)
                             (flag 'list))))
