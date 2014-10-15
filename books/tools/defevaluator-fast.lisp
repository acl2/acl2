; defevaluator-fast -- faster version of defevaluator
; Copyright (C) 2009-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(program)

(defxdoc defevaluator-fast
  :parents (defevaluator)
  :short "Faster alternative to @(see defevaluator)."
  :long "<p>See @(see defevaluator) and for background about evaluators, which
are used in @(see meta) rules and @(see clause-processor)s.</p>

<p>@('Defevaluator-fast') is a reimplementation of @('defevaluator').  From the
user perspective, it is nearly identical to @('defevaluator').  That is, it
produces a constrained function with the same set of constraints as the one
produced by defevaluator.  However:</p>

<ul>
<li>it is much faster when the list of recognized functions is long,</li>
<li>it can also recognize multi-valued functions and functions with stobjs,
    because the evaluator is declared non-executable (which shouldn't
    matter to the user since it's a constrained function anyway)</li>
<li>it can optionally give the constraints better names.</li>
</ul>

<p>Example:</p>
@({
    (defevaluator-fast evl evl-list
      ((length x) (member x y)))
})

<p>General Form:</p>

@({
    (defevaluator-fast ev ev-list
      ((g1 x1 ... xn_1)
       ...
       (gk x1 ... xn_k))
      :namedp flg)
})

<p>where @('ev') and @('ev')-list are new function symbols and @('g1'), ...,
@('gk') are old function symbols with the indicated number of formals, i.e.,
each @('gi') has @('n_i') formals.</p>

<h3>Constraint Naming</h3>

<p>The @('namedp') argument defaults to nil, in which case the theorems
constraining the evaluator are named the same way as in defevaluator, i.e.,</p>

@({
    [evname]-constraint-0
    [evname]-constraint-1
    [evname]-constraint-2
    ...
})

<p>If you instead give @(':namedp t'), then the theorems are given more
descriptive names,</p>

@({
    [evname]-of-quote
    [evname]-of-[fnname]-call
    ...
})

<h3>Performance Notes</h3>

<p>See the comments in @('tools/defevaluator-fast.lisp') for some performance
testing code.  We tested @('defevaluator-fast') against the constant
@('*defeval-entries-for-all-reasonable-functions*'), which contained a list of
574 function \"calls\" (such as @('(cons a b)'), @('(foo arg1 arg2)'),
etc.)</p>

<p>On one modern (ca. 2009) machine, @('defevaluator-fast') proves the
constraints for the evaluator recognizing all the listed functions in 2.2
seconds (when output is turned off.)  Empirically, runtime seems to scale
quadratically with the number of functions recognized, which is consistent with
the notion that there are linearly many theorems which each prove in linear
time.</p>

<p>In comparison, if we redefine @('defevaluator') so that it can handle MVs
and functions that take stobjs and so that it gives a @(':do-not
'(preprocess)') hint to the measure theorem for better performance, it takes
6.0 sec to define an evaluator recognizing the first 40 of these functions,
11.1 sec for the first 50, 28 sec for the first 80, and so on.  (If the
@(':do-not '(preprocess)') hint is omitted, then somewhere in the 40s the
measure conjecture begins to spend an impractically long time in
@('if-tautologyp'), part of preprocessing.)</p>

<h3>Acknowledgements</h3>

<p>Code ripped liberally from the original defevaluator macro in
defthm.lisp (in the ACL2 sources.)  Also, Jared Davis provided the idea of
defining the evaluator to call evfn-lst once on the function or lambda
arguments rather than calling evfn N times for each N-ary function
recognized (this is the main innovation that speeds up the proofs.)</p>")

(defun evfast-symname-lst (syms)
  (if (atom syms)
      nil
    (cons `(symbol-name ,(car syms))
          (evfast-symname-lst (cdr syms)))))

(defmacro evfast-thmname (evfn &rest rest-syms)
  `(intern-in-package-of-symbol
    (concatenate 'string . ,(evfast-symname-lst (cons evfn rest-syms)))
    ,evfn))

(defun defevaluator-fast-form/defthm-for-fnsym (evfn fn-args)
  (let* ((thmname (evfast-thmname evfn '-of- (car fn-args) '-call))
         (thm-body (prettyify-clause (evaluator-clause evfn fn-args) nil nil)))
    `((defthm ,thmname
        ,thm-body
        :hints (("goal" :expand
                 ((,evfn x a)
                  (:free (x) (hide x))
                  (:free (fn args)
                   (apply-for-defevaluator fn args))))))
      (local (in-theory (disable ,thmname))))))

(defun defevaluator-fast-form/defthms-for-fnsyms (evfn fn-args-list)
  (declare (xargs :mode :program))
  (if (endp fn-args-list)
      nil
    (append
     (defevaluator-fast-form/defthm-for-fnsym evfn (car fn-args-list))
     (defevaluator-fast-form/defthms-for-fnsyms evfn (cdr fn-args-list)))))


(defun defevaluator-fast-form/defthms-named (evfn evfn-lst fn-args-list)
  (declare (xargs :mode :program))
  (let* ((base-clauses (prettyify-clause-lst (evaluator-clauses evfn evfn-lst
                                                                nil) nil nil)))
    `((defthmd ,(evfast-thmname evfn '-of-fncall-args)
        ,(nth 0 base-clauses)
        :hints (("Goal" :expand
                 ((:free (x) (hide x))
                  (,evfn x a)
                  (:free (args)
                   (,evfn (cons (car x)
                                args) nil)))
                 :in-theory '(eval-list-kwote-lst
                              fix-true-list-ev-lst
                              car-cons cdr-cons))))
      (local (in-theory (disable ,(evfast-thmname evfn '-of-fncall-args))))

      (defthm ,(evfast-thmname evfn '-of-variable)
        ,(nth 1 base-clauses)
        :hints (("goal" :expand ((,evfn x a)))))
      (local (in-theory (disable ,(evfast-thmname evfn '-of-variable))))

      (defthm ,(evfast-thmname evfn '-of-quote)
        ,(nth 2 base-clauses)
        :hints (("goal" :expand ((,evfn x a)))))
      (local (in-theory (disable ,(evfast-thmname evfn '-of-quote))))

      (defthm ,(evfast-thmname evfn '-of-lambda)
        ,(nth 3 base-clauses)
        :hints (("goal" :expand ((,evfn x a)))))
      (local (in-theory (disable ,(evfast-thmname evfn '-of-lambda))))

      (defthm ,(evfast-thmname evfn-lst '-of-atom)
        ,(nth 4 base-clauses)
        :hints (("goal" :expand ((,evfn-lst x-lst a)))))
      (local (in-theory (disable ,(evfast-thmname evfn-lst '-of-atom))))

      (defthm ,(evfast-thmname evfn-lst '-of-cons)
        ,(nth 5 base-clauses)
        :hints (("goal" :expand ((,evfn-lst x-lst a)))))
      (local (in-theory (disable ,(evfast-thmname evfn-lst '-of-cons))))

      . ,(defevaluator-fast-form/defthms-for-fnsyms evfn fn-args-list))))




(defun defevaluator-fast-form/defthms (evfn evfn-lst prefix i clauses)
  (declare (xargs :mode :program))
  (cond ((null clauses) nil)
        (t (let ((thmname (genvar evfn prefix i nil)))
             (list*
              (list*
               (if (eql i 0) 'defthmd 'defthm)
               thmname
               (prettyify-clause (car clauses) nil nil)
               (case i
                 (0
;                   (implies (and (consp x)
;                                 (syntaxp (not (equal a ''nil)))
;                                 (not (equal (car x) 'quote)))
;                            (equal (evfn x a)
;                                   (evfn (cons (car x)
;                                               (kwote-lst (evfn-lst
;                                                           (cdr x) a)))
;                                         nil)))
                  `(:hints
                    (("Goal" :expand
                      ((:free (x) (hide x))
                       (,evfn x a)
                       (:free (args)
                              (,evfn (cons (car x)
                                           args) nil)))
                      :in-theory '(eval-list-kwote-lst
                                   fix-true-list-ev-lst
                                   car-cons cdr-cons)))))
                 (1
;                   (implies (symbolp x)
;                            (equal (evfn x a)
;                                   (and x (cdr (assoc-eq x a)))))
                  `(:hints (("goal" :expand ((,evfn x a))))))
                 (2
;                   (implies (and (consp x) (eq (car x) 'quote))
;                            (equal (evfn x a) (cadr x)))
                  `(:hints (("goal" :expand ((,evfn x a))))))
                 (3
;                   (implies (and (consp x) (consp (car x)))
;                            (equal (evfn x a)
;                                   (a-ev (caddar x)
;                                         (pairlis$ (cadar x)
;                                                   (evfn-lst (cdr x) a)))))
                  `(:hints (("goal" :expand ((,evfn x a))))))
                 (4
;                   (implies (not (consp x-lst))
;                            (equal (evfn-lst x-lst a) nil))
                  `(:hints (("goal" :expand ((,evfn-lst x-lst a))))))
                 (5
;                   (implies (consp x-lst)
;                            (equal (evfn-lst x-lst a)
;                                   (cons (evfn (car x-lst) a)
;                                         (evfn-lst (cdr x-lst) a))))
                  `(:hints (("goal" :expand ((,evfn-lst x-lst a))))))
                 (t
;                   (implies (and (consp x)
;                                 (eq (car x) 'foo))
;                            (equal (evfn x a)
;                                   (foo (evfn (cadr x) a)
;                                        ...)))
                  `(:hints (("goal" :expand
                             ((,evfn x a)
                              (:free (x) (hide x))
                              (:free (fn args)
                                     (apply-for-defevaluator fn args)))))))))
              `(local (in-theory (disable ,thmname)))
              (defevaluator-fast-form/defthms evfn evfn-lst prefix (1+ i)
                (cdr clauses)))))))




(defun evaluator-fast-clause/arglist (formals x)
  (if (atom formals)
      nil
    (cons `(car ,x)
          (evaluator-fast-clause/arglist (cdr formals) `(cdr ,x)))))

(defun defevaluator-fast-form/fns-clauses (fn-args-lst)
  (declare (xargs :mode :program))
; We return a list of cond clauses,
; (
;  ((equal (car x) 'fn1)
;   (fn1 (evfn (cadr x) a) ... (evfn (cad...dr x) a)))
;  ((equal (car x) 'fn2)
;   (fn2 (evfn (cadr x) a) ... (evfn (cad...dr x) a)))
;  ...
;   (t nil))

; containing a clause for each fni in fns plus a final t clause.

  (cond ((null fn-args-lst) '((t nil)))
        (t (cons
            (list (list 'equal 'fn (kwote (caar fn-args-lst)))
                  (cons (caar fn-args-lst)
                        (evaluator-fast-clause/arglist (cdar fn-args-lst)
                                                       'args)))
            (defevaluator-fast-form/fns-clauses (cdr fn-args-lst))))))

(defconst *defevaluator-fast-form-base-theory*
  (append *definition-minimal-theory*
          '(car-cdr-elim
            car-cons cdr-cons ;; fix-true-list-cdr
            o< o-finp o-first-expt o-first-coeff o-rst natp posp
            acl2-count
            alistp
            fix-true-list kwote kwote-lst pairlis$-fix-true-list
;;             (:type-prescription acl2-count)
            )))

(defun defevaluator-fast-form (evfn evfn-lst namedp fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((fns-clauses (defevaluator-fast-form/fns-clauses fn-args-lst))
         (defthms (if namedp
                      (defevaluator-fast-form/defthms-named
                        evfn evfn-lst fn-args-lst)
                    (defevaluator-fast-form/defthms
                      evfn evfn-lst
                      (symbol-name (pack2 evfn '-constraint-))
                      0
                      (evaluator-clauses evfn evfn-lst fn-args-lst)))))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      (local (in-theory *defevaluator-fast-form-base-theory*))
      . ,(sublis
          (list (cons 'evfn evfn)
                (cons 'evfn-lst evfn-lst)
                (cons 'fns-clauses fns-clauses)
                (cons 'defthms defthms))
          '((local (defun-nx apply-for-defevaluator (fn args)
                     (declare (xargs :verify-guards nil
                                     :normalize nil))
                     (cond . fns-clauses)))
            (local
             (mutual-recursion
              (defun-nx evfn (x a)
                (declare
                 (xargs :verify-guards nil
                        :measure (acl2-count x)
                        :well-founded-relation o<
                        :normalize nil
                        :hints (("goal" :in-theory
                                 (enable (:type-prescription
                                          acl2-count))))
                        :mode :logic))
                (cond
                 ((symbolp x) (and x (cdr (assoc-eq x a))))
                 ((atom x) nil)
                 ((eq (car x) 'quote) (car (cdr x)))
                 (t (let ((args (evfn-lst (cdr x) a)))
                      (cond
                       ((consp (car x))
                        (evfn (car (cdr (cdr (car x))))
                              (pairlis$ (car (cdr (car x)))
                                        args)))
                       (t (apply-for-defevaluator (car x) args)))))))
                (defun-nx evfn-lst (x-lst a)
                  (declare (xargs :measure (acl2-count x-lst)
                                  :well-founded-relation o<))
                  (cond ((endp x-lst) nil)
                        (t (cons (evfn (car x-lst) a)
                                 (evfn-lst (cdr x-lst) a)))))))
            (local (in-theory (disable evfn evfn-lst apply-for-defevaluator)))
            (local
             (defthm eval-list-kwote-lst
               (equal (evfn-lst (kwote-lst args) a)
                      (fix-true-list args))
               :hints (("goal"
                        :expand ((:free (x y) (evfn-lst (cons x y) a))
                                 (evfn-lst nil a)
                                 (:free (x)
                                        (evfn (list 'quote x) a)))
                        :induct (fix-true-list args)))))
            (local
             (defthm fix-true-list-ev-lst
               (equal (fix-true-list (evfn-lst x a))
                      (evfn-lst x a))
               :hints (("goal" :induct (len x)
                        :in-theory (e/d ((:induction len)))
                        :expand ((evfn-lst x a)
                                 (evfn-lst nil a))))))
            (local
             (defthm ev-commutes-car
               (equal (car (evfn-lst x a))
                      (evfn (car x) a))
               :hints (("goal" :expand ((evfn-lst x a)
                                        (evfn nil a))
                        :in-theory (enable default-car)))))
            (local
             (defthm ev-lst-commutes-cdr
               (equal (cdr (evfn-lst x a))
                      (evfn-lst (cdr x) a))
               :hints (("Goal" :expand ((evfn-lst x a)
                                        (evfn-lst nil a))
                        :in-theory (enable default-cdr)))))
            . defthms)))))

(defmacro defevaluator-fast (&whole x evfn evfn-lst fn-args-lst &key namedp)

; Note: It might be nice to allow defevaluator to take a :DOC string, but that
; would require allowing encapsulate to take such a string!

  (cond
   ((not (and (symbolp evfn)
              (symbolp evfn-lst)
              (symbol-list-listp fn-args-lst)))
    `(er soft '(defevaluator-fast . ,evfn)
         "The form of a defevaluator event is (defevaluator-fast evfn ~
          evfn-lst fn-args-lst), where evfn and evfn-lst are symbols ~
          and fn-args-lst is a true list of lists of symbols.  ~
          However, ~x0 does not have this form."
         ',x))
   (t
    (defevaluator-fast-form evfn evfn-lst namedp fn-args-lst))))



(logic)

(local
 ;; A test to show that ACL2 recognizes evaluators defined with
 ;; DEFEVALUATOR-FAST as valid evaluators for meta-reasoning:
 (progn
   (defevaluator-fast foo-ev foo-ev-lst
     ((XXXJOIN FN ARGS)
      (INTEGER-ABS X)
      (OR-MACRO LST)
      (AND-MACRO LST)
      (LIST-MACRO LST)
      (TRUE-LISTP X)
      (EQ X Y)
      (REWRITE-EQUIV X)
      (HIDE X)
      (NOT P)
      (IMPLIES P Q)
      (BOOLEANP X)
      (XOR P Q)
      (IFF P Q)
      (O< X Y)
      (O-P X)
      (SYMBOLP X)
      (SYMBOL-PACKAGE-NAME X)
      (SYMBOL-NAME X)
      (STRINGP X)
      (REALPART X)
      (RATIONALP X)
      (PKG-WITNESS PKG)
      (NUMERATOR X)
      (INTERN-IN-PACKAGE-OF-SYMBOL STR SYM)
      (INTEGERP X)
      (IMAGPART X)
      (IF X Y Z)
      (EQUAL X Y)
      (DENOMINATOR X)
      (CONSP X)
      (CONS X Y)
      (COERCE X Y)
      (COMPLEX-RATIONALP X)
      (COMPLEX X Y)
      (CODE-CHAR X)
      (CHARACTERP X)
      (CHAR-CODE X)
      (CDR X)
      (CAR X)
      (< X Y)
      (UNARY-/ X)
      (UNARY-- X)
      (BINARY-+ X Y)
      (BINARY-* X Y)
      (BAD-ATOM<= X Y)
      (ACL2-NUMBERP X)))

   (defun stupid-cp (x)
     (list x))

   ;; ACL2 recognizes FOO-EV as a valid evaluator:
   (defthm stupid-cp-correct
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (foo-ev
                    (conjoin-clauses (stupid-cp cl))
                    a))
              (foo-ev
               (disjoin cl) a))
     :rule-classes :clause-processor)))

(local
 ;; A test to show that ACL2 recognizes evaluators defined with
 ;; DEFEVALUATOR-FAST as valid evaluators for meta-reasoning:
 (progn
   (defevaluator-fast foo2-ev foo2-ev-lst
     ((XXXJOIN FN ARGS)
      (INTEGER-ABS X)
      (OR-MACRO LST)
      (AND-MACRO LST)
      (LIST-MACRO LST)
      (TRUE-LISTP X)
      (EQ X Y)
      (REWRITE-EQUIV X)
      (HIDE X)
      (NOT P)
      (IMPLIES P Q)
      (BOOLEANP X)
      (XOR P Q)
      (IFF P Q)
      (O< X Y)
      (O-P X)
      (SYMBOLP X)
      (SYMBOL-PACKAGE-NAME X)
      (SYMBOL-NAME X)
      (STRINGP X)
      (REALPART X)
      (RATIONALP X)
      (PKG-WITNESS PKG)
      (NUMERATOR X)
      (INTERN-IN-PACKAGE-OF-SYMBOL STR SYM)
      (INTEGERP X)
      (IMAGPART X)
      (IF X Y Z)
      (EQUAL X Y)
      (DENOMINATOR X)
      (CONSP X)
      (CONS X Y)
      (COERCE X Y)
      (COMPLEX-RATIONALP X)
      (COMPLEX X Y)
      (CODE-CHAR X)
      (CHARACTERP X)
      (CHAR-CODE X)
      (CDR X)
      (CAR X)
      (< X Y)
      (UNARY-/ X)
      (UNARY-- X)
      (BINARY-+ X Y)
      (BINARY-* X Y)
      (BAD-ATOM<= X Y)
      (ACL2-NUMBERP X))
     :namedp t)

   (defun stupid-cp2 (x)
     (list x))

   ;; ACL2 recognizes FOO-EV as a valid evaluator:
   (defthm stupid-cp2-correct
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (foo2-ev
                    (conjoin-clauses (stupid-cp cl))
                    a))
              (foo2-ev
               (disjoin cl) a))
     :rule-classes :clause-processor)))





(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))



#||

;; Infrastructure for testing this
(defun all-syms-in-world (w)
  (remove-duplicates (strip-cars w)))

(defun list-of-nilsp (x)
  (if (atom x)
      (eq x nil)
    (and (eq (car x) nil)
         (list-of-nilsp (cdr x)))))

(defun logic-function-syms (syms world)
  (if (atom syms)
      nil
    (if (and (not (eq (getprop (car syms) 'formals :none 'current-acl2-world
                               world)
                      :none))
             (member (getprop (car syms) 'symbol-class nil 'current-acl2-world world)
                     '(:ideal :common-lisp-compliant))
             (not (member (car syms)
                          (global-val 'untouchable-fns world)))
             (not (member (car syms) '(synp must-be-equal
                                            open-output-channel!)))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-out nil
                                      world))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-in nil
                                      world))
             (not (and (member (car syms) *ec-call-bad-ops*)
                       (not (equal (fgetprop (car syms) 'guard ''t
                                             world)
                                   ''t)))))
        (cons (car syms) (logic-function-syms (cdr syms) world))
      (logic-function-syms (cdr syms) world))))

(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))



(logic)

(make-event
 `(defconst *defeval-entries-for-all-reasonable-functions*
    ',(let ((world (w state)))
        (mk-defeval-entries (logic-function-syms (all-syms-in-world world)
                                                world)
                            world))))



(time$
 (make-event
  `(defevaluator-fast test-defevaluator-fast-ev test-defevaluator-fast-ev-lst
     ,*defeval-entries-for-all-reasonable-functions*)))
;; 2.2 sec with output off, 6.0 sec with output on







;; For comparison, testing with the original defevaluator (plus a couple of
;; trivial mods:)

(defttag blah)

;; Redefining the usual defevaluator so that it uses :non-executable t.
(redef!)

(defun defevaluator-form (evfn evfn-lst fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses evfn fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    (symbol-name (pack2 evfn '-constraint-))
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      (local (in-theory *defevaluator-form-base-theory*))
      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
; MODIFIED: Make the evaluator non-executable so it can handle stobjs and mvs
             (defun-nx evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
                               :mode :logic
; MODIFIED: Prevent preprocessing in the measure theorem to eliminate a drastic
; slowdown.
                               :hints (("Goal" :do-not '(preprocess)))))
               (cond
                ((symbolp x) (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
           . defthms)))))

(set-inhibit-output-lst '(proof-tree prove event expansion))

(time$
 (make-event
  `(defevaluator test-defevaluator-ev test-defevaluator-ev-lst
     ,(take 80 *defeval-entries-for-all-reasonable-functions*))))


(defthm fix-true-list-test-defevaluator-fast-ev-lst
  (equal (fix-true-list (test-defevaluator-fast-ev-lst x a))
         (test-defevaluator-fast-ev-lst x a))
  :hints (("goal" :induct (len x)
           :in-theory (e/d ((:induction len))
                           (test-defevaluator-fast-ev-commutes-car)))))

(defthm test-defevaluator-fast-ev-commutes-car
  (equal (test-defevaluator-fast-ev (car x) a)
         (car (test-defevaluator-fast-ev-lst x a))))

(defthm test-defevaluator-fast-ev-lst-commutes-cdr
  (equal (cdr (test-defevaluator-fast-ev-lst x a))
         (test-defevaluator-fast-ev-lst (cdr x) a))
  :hints(("Goal" :in-theory (disable test-defevaluator-fast-ev-commutes-car))))


:trans1 (defevaluator-fast fooev fooevl
  ((if a b c)
   (cons a b)
   (consp a)
   (car a)
   (car b)
   (binary-append c d)
   (nth n x)
   (mv-nth n x)))


(SET-INHIBIT-WARNINGS "theory")
(LOCAL (IN-THEORY *DEFEVALUATOR-FAST-FORM-BASE-THEORY*))
(LOCAL
 (MUTUAL-RECURSION
  (DEFUN-NX FOOEV (X A)
    (DECLARE (XARGS :VERIFY-GUARDS NIL
                    :MEASURE (ACL2-COUNT X)
                    :WELL-FOUNDED-RELATION O<
                    :NORMALIZE NIL
                    :MODE :LOGIC))
    (COND ((SYMBOLP X)
           (AND X (CDR (ASSOC-EQ X A))))
          ((ATOM X) NIL)
          ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
          (T (LET ((ARGS (FOOEVL (CDR X) A)))
                  (COND ((CONSP (CAR X))
                         (FOOEV (CAR (CDR (CDR (CAR X))))
                                (PAIRLIS$ (CAR (CDR (CAR X))) ARGS)))
                        ((EQUAL (CAR X) 'IF)
                         (IF (CAR ARGS)
                             (CAR (CDR ARGS))
                             (CAR (CDR (CDR ARGS)))))
                        ((EQUAL (CAR X) 'CONS)
                         (CONS (CAR ARGS) (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'CONSP)
                         (CONSP (CAR ARGS)))
                        ((EQUAL (CAR X) 'CAR) (CAR (CAR ARGS)))
                        ((EQUAL (CAR X) 'CAR) (CAR (CAR ARGS)))
                        ((EQUAL (CAR X) 'BINARY-APPEND)
                         (BINARY-APPEND (CAR ARGS)
                                        (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'NTH)
                         (NTH (CAR ARGS) (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'MV-NTH)
                         (MV-NTH (CAR ARGS) (CAR (CDR ARGS))))
                        (T NIL))))))
  (DEFUN FOOEVL (X-LST A)
    (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
                    :WELL-FOUNDED-RELATION O<))
    (COND ((ENDP X-LST) NIL)
          (T (CONS (FOOEV (CAR X-LST) A)
                   (FOOEVL (CDR X-LST) A)))))))
(LOCAL (IN-THEORY (DISABLE FOOEV FOOEVL)))
(LOCAL
 (DEFTHM EVAL-LIST-KWOTE-LST
   (EQUAL (FOOEVL (KWOTE-LST ARGS) A)
          (FIX-TRUE-LIST ARGS))
   :HINTS (("goal" :EXPAND ((:FREE (X Y) (FOOEVL (CONS X Y) A))
                            (FOOEVL NIL A)
                            (:FREE (X) (FOOEV (LIST 'QUOTE X) A)))
            :INDUCT (FIX-TRUE-LIST ARGS)))))
(LOCAL (DEFTHM FIX-TRUE-LIST-EV-LST
         (EQUAL (FIX-TRUE-LIST (FOOEVL X A))
                (FOOEVL X A))
         :HINTS (("goal" :INDUCT (LEN X)
                  :IN-THEORY (E/D ((:INDUCTION LEN)))
                  :EXPAND ((FOOEVL X A) (FOOEVL NIL A))))))
(LOCAL (DEFTHM EV-COMMUTES-CAR
         (EQUAL (CAR (FOOEVL X A))
                (FOOEV (CAR X) A))
         :HINTS (("goal" :EXPAND ((FOOEVL X A) (FOOEV NIL A))
                  :IN-THEORY (ENABLE DEFAULT-CAR)))))
(LOCAL (DEFTHM EV-LST-COMMUTES-CDR
         (EQUAL (CDR (FOOEVL X A))
                (FOOEVL (CDR X) A))
         :HINTS (("Goal" :EXPAND ((FOOEVL X A) (FOOEVL NIL A))
                  :IN-THEORY (ENABLE DEFAULT-CDR)))))



(DEFTHM FOOEV-CONSTRAINT-2
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
                   (EQUAL (FOOEV X A) (CADR X)))
          :HINTS (("goal" :EXPAND ((FOOEV X A)))))

(local (defthm fooev-lst-kwote-lst
         (equal (fooev-lst (kwote-lst x)

(DEFTHMD FOOEV-CONSTRAINT-0
  (IMPLIES (AND (CONSP X)
                (SYNTAXP (NOT (EQUAL A ''NIL)))
                (NOT (EQUAL (CAR X) 'QUOTE)))
           (EQUAL (FOOEV X A)
                  (FOOEV (CONS (CAR X)
                               (KWOTE-LST (FOOEVL (CDR X) A)))
                         NIL)))
  :HINTS (("Goal" :EXPAND ((:FREE (X) (HIDE X))
                           (FOOEV X A)
                           (:FREE (ARGS)
                                  (FOOEV (CONS (CAR X) ARGS) NIL)))
           :in-theory (e/d** (eval-list-kwote-lst
                              fix-true-list-ev-lst
                              car-cons cdr-cons)))))


||#
