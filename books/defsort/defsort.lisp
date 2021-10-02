; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "generic")
(include-book "std/util/support" :dir :system)

(defxdoc defsort
  ;; Note (Sol): I think this library should probably be moved into std/lists,
  ;; and its xdoc filed under there, maybe once the UI is made a bit nicer.
  :parents (std/lists)
  :short "Define a sorting function for a given comparator."
  :long "<h5>NOTE: Defsort's interface has a greater than average likelihood of
changing incompatibly in the future.</h5>

<p>Defsort creates a relatively-high-performance sorting function for a given
comparison function, and proves that its output is an ordered (with respect to
the comparison function) permutation of the input list.  It is currently
implemented as a mergesort on lists with some fixnum optimizations.</p>

<p>It also may optionally prove the generated mergesort function equivalent to
an insertion sort; this requires some extra properties to be proved about the
comparison function beforehand; see the discussion of @(':weak') below.</p>

<h3>Usage</h3>

<p>These forms show various ways of invoking defsort:</p>
@({
  (defsort sort-by-foo<
           :prefix foosort
           :compare< foo<
           :comparablep foo-p
           :comparable-listp foolist-p
           :true-listp nil
           :weak t)

  (defsort :comparablep rationalp
           :compare< <
           :prefix <
           :comparable-listp rational-listp
           :true-listp t
           :weak nil)

  (defsort intalist-sort
           :extra-args (alist)
           :extra-args-guard (intalistp alist)
           :compare< intalist-<
           :comparablep (lambda (x alist) (consp (assoc-equal x alist))))

  (defsort intalist-sort2 (x alist)
           :extra-args-guard (intalistp alist)
           :compare< intalist2-<
           :comparablep (lambda (x alist) (stringp x)))


})

<p>The first form is a new syntax that gives the name of the sorting function
explicitly; it is also good for etags generation since it is of the form
@('(def... name ...)').  In the first form, the prefix is optional; if it is
not provided, the sort name will be used as the prefix for generating other
function names.</p>

<p>The second form shows an older syntax in which the sort name is omitted and
every function name is generated from the prefix, so the name of the sorting
function will in this case be @('<-sort').</p>

<p>The third form shows the use of @(':extra-args') to define a parameterized
sort.</p>

<p>The fourth form shows a different syntax for specifying extra-args by giving
a formals list before the keyword arguments, which looks a bit nicer.  (Note:
In this syntax the first formal must be the symbol X, although it can be in any
package.)  Additionally, it shows how to use extra-args in conjunction with a
comparablep predicate that doesn't use them.</p>

<h4>Keyword Arguments</h4>
<ul>

<li>@(':compare<') gives the function to use to compare elements; this may be a
binary function name or a lambda such as @('(lambda (x y) (< y x))').  Defsort
needs to prove that this is a transitive relation.</li>

<li>@(':prefix') defaults to the sort name when it is provided, but otherwise
is required.  It is used to generate function and theorem names.</li>

<li>@(':comparablep') gives the type of element to be compared.  The comparison
function's guards should be satisfied by any two elements that both satisfy
this predicate.  This may be a unary function symbol or lambda.  If it is
omitted, then it is treated as @('(lambda (x) t)'), i.e. all objects are
comparable.</li>

<li>@(':comparable-listp') gives the name of a function that recognizes a list
of comparable elements.  This may be omitted, in which case such a function
will be defined (named @('<prefix>-list-p')).</li>

<li>@(':true-listp') defaults to NIL and determines whether the
comparable-listp function requires the final cdr to be NIL.  If an existing
@(':comparable-listp') function name is provided, then the value of
@(':true-listp') must correspond to that function; i.e. true-listp must be true
iff the comparable-listp function requires the final cdr to be nil.  If
@(':comparable-listp') is not provided, then the comparable-listp function will
be generated so that this is true.</li>

<li>@(':weak') defaults to NIL in the new syntax and T in the old syntax, for
historical reasons.  When @(':weak') is NIL, defsort will introduce a simple
insertion sort function in addition to the optimized mergesort, and prove the
two equivalent.  To do this, it needs a couple of extra facts about the
comparison function, in addition to its transitivity: its negation must also be
a transitive relation, and it must be strict, i.e.,
@('(not (compare< x x))').</li>

<li>@(':extra-args') may be a list of variables that are used as extra
parameters to all the functions involved.  (If some of your functions don't
require all the arguments, you must wrap them in a lambda in order to accept
the right arguments.)  When using the new syntax with a formals list,
extra-args is not accepted since the formals list already specifies them.</li>

<li>@(':extra-args-guard') may be a term giving a guard that will be required
of the extra-args.</li>

</ul>

<h5>Troubleshooting</h5>

<p>Defsort allows you to specify a lambda rather than a function for most
arguments, and doesn't require that (e.g.) the @(':extra-args-guard') be just a
function call.  But things may break if you use, e.g., a lambda containing an
IF (or AND or OR) as, say, the comparablep predicate.  It is best for
everything to be a simple function call.</p>

<p>There may also be some bad cases when the setting of @(':comparablep') is a
built-in function that ACL2 treats specially or that is in @('minimal-theory').
For example, @(':comparablep atom') used to cause defsort to fail, though now
it has a special hack for that particular case.</p>
")

; Inputs are as follows.
;
; Compare< is the name of a 2-ary function that compares objects.  It can be a
; strict or non-strict relation.  It must be known to be boolean and
; transitive.
;
; Comparablep is the name of a 1-ary function that says when objects are
; well-formed for compare<.  If compare< works on all inputs, comparablep may
; be set to t.
;
; Prefix is a symbol which will be used to create the names of all the
; functions and theorems we generate.

(defconst *defsort-keywords*
  '(:comparablep :compare< :prefix :comparable-listp :true-listp :weak :extra-args :extra-args-guard :extra-args-stobjs :extra-args-stobj-recognizers))

(defun defsort-functional-inst-subst (func-subst wrld)
  ;; this is a bit weak; it removes substitutions in which the substituted
  ;; function is not yet defined.  For lambdas, it checks only the leading
  ;; function symbol in the body.  Not smart enough for general use.
  (b* (((when (atom func-subst)) nil)
       (pair (car func-subst))
       (sub (cadr pair))
       (sym (or (and (symbolp sub) sub)
                (and (consp sub)
                     (eq (car sub) 'lambda)
                     (consp (caddr sub))
                     (symbolp (car (caddr sub)))
                     (car (caddr sub)))))
       (real-sym (or (cdr (assoc sym (macro-aliases wrld)))
                     sym))
       ((when (and real-sym
                   (eq (fgetprop real-sym 'formals :none wrld) :none)))
        (defsort-functional-inst-subst (cdr func-subst) wrld)))
    (cons pair
          (defsort-functional-inst-subst (cdr func-subst) wrld))))

(defun defsort-functional-inst-fn (thmname func-subst rest-hints state)
  (declare (xargs :mode :program :stobjs state))
  ;; Note: Rest-hints may be a list of regular hint keywords, or it may start
  ;; with :var-subst (...) in which case this is used as a variable substitution.
  (b* (((mv var-subst rest-hints)
        (if (eq (car rest-hints) :var-subst)
            (mv (cadr rest-hints) (cddr rest-hints))
          (mv nil rest-hints))))
    `(:use ((:instance
             (:functional-instance ,thmname
              . ,(defsort-functional-inst-subst func-subst (w state)))
             . ,var-subst))
      . ,rest-hints)))

(defmacro defsort-functional-inst (thmname func-subst &rest rest-hints)
  `(defsort-functional-inst-fn ',thmname ',func-subst ',rest-hints state))

(defconst *defsort-empty-ens*
  (make enabled-structure
        :index-of-last-enabling 0
        :theory-array
        (compress1 'ens0
                   (list (list :header
                               :dimensions (list 1)
                               :maximum-length 2
                               :default nil
                               :name 'ens0
                               :order nil)))
        :array-name 'ens0
        :array-length 1
        :array-name-root 'ens
        :array-name-suffix 0))

(defun fix-comparablep (comparablep)
  ;; Hack to fix the given comparablep function for some exceptional situations...
  (cond ((eq comparablep 'atom)
         ;; Atom isn't a good target for rewriting so change this to (not (consp ...))
         '(lambda (x) (not (consp x))))
        (t comparablep)))


(defun defsort-guard-for-term (term state)
  (declare (Xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       ((mv clauses &)
        (guard-obligation-clauses
         (cons :term term) nil *defsort-empty-ens* wrld state)))
    (mv (untranslate* (conjoin-clauses clauses) nil wrld)
        state)))

(defthmd defsort-len-of-cdr-strong
  (implies (consp x)
           (< (len (cdr x)) (len x)))
  :hints (("goal" :expand ((len x))))
  :rule-classes :linear)

(defthmd defsort-len-of-cdr-weak
  (<= (len (cdr x)) (len x))
  :hints (("goal" :expand ((len x))))
  :rule-classes :linear)

(defthmd defsort-nfix-when-not-zp
  (implies (not (zp x))
           (equal (nfix x) x))
  :hints (("goal" :expand ((nfix x) (zp x)))))

(defthmd defsort-o-p-when-natp
  (implies (natp x)
           (o-p x)))

(defthmd defsort-o<-of-naturals
  (implies (and (natp x) (natp y))
           (equal (o< x y)
                  (< x y))))

(defthmd defsort-len-when-not-consp
  (implies (not (consp x))
           (equal (len x) 0)))

(deftheory defsort-theory
  '(fast-mergesort-admission-1
    fast-mergesort-admission-2
    comparable-mergesort-admission-nthcdr
    comparable-mergesort-admission-take
    defsort-len-of-cdr-strong
    defsort-len-of-cdr-weak
    defsort-nfix-when-not-zp
    defsort-o-p-when-natp
    defsort-o<-of-naturals
    defsort-len-when-not-consp
    (:t len)
    (:t nfix)
    natp-compound-recognizer
    zp-compound-recognizer
    rest-n
    (eqlablep)))







(defun defsort-fn (args state)
  (declare (Xargs :mode :program :stobjs state))
  (b* ((new-syntaxp (not (keywordp (car args))))
       ((mv sort args) (if new-syntaxp
                           (mv (car args) (cdr args))
                         (mv nil args)))
       (formalsp (and new-syntaxp (consp (car args))))
       ((mv formals args) (if formalsp
                              (mv (car args) (cdr args))
                            (mv nil args)))
       ((when (and formalsp
                   (not (and (symbol-listp formals)
                             (consp formals)
                             (equal (symbol-name (car formals)) "X")))))
        (er soft 'defsort-fn
            "Defsort: The formals, if provided, must be a symbol-list whose ~
             first element is named X (standing for the list to be sorted)."))

       ((mv kwd-alist args)
        (std::extract-keywords 'defsort *defsort-keywords* args nil))

       ((when args)
        (er soft 'defsort-fn "Defsort: extra arguments"))

       (prefix           (std::getarg :prefix sort kwd-alist))
       ((unless (and prefix (symbolp prefix) (not (keywordp prefix))))
        (er soft 'defsort
            "Defsort requires either a sort name (non-keyword symbol as the ~
               first argument) or a :prefix argument, also a non-keyword ~
               symbol."))
       ((fun (mksym prefix x))
        (intern-in-package-of-symbol (concatenate 'string (symbol-name prefix) x)
                                     ;; We can't create symbols in the COMMON-LISP package,
                                     ;; so if something like < is used, switch it to the ACL2
                                     ;; package.
                                     (if (equal (symbol-package-name prefix) "COMMON-LISP")
                                         'ACL2::foo
                                       prefix)))
       (sort             (or sort (mksym prefix "-SORT")))


       (comparable-listp (std::getarg :comparable-listp nil kwd-alist))
       (compare<         (std::getarg :compare< nil kwd-alist))
       (comparablep      (std::getarg :comparablep nil kwd-alist))
       (true-listp       (std::getarg :true-listp nil kwd-alist))
       (weak             (std::getarg :weak (not new-syntaxp) kwd-alist))
       ((when (and formalsp (assoc :extra-args kwd-alist)))
        (er soft 'defsort "Don't use both formals and an :extra-args keyword."))
       (extra-args       (if formalsp
                             (cdr formals)
                           (std::getarg :extra-args nil kwd-alist)))
       (extra-args-guard (std::getarg :extra-args-guard t kwd-alist))
       (extra-args-stobjs (std::getarg :extra-args-stobjs nil kwd-alist))
       (extra-args-stobj-recognizers (std::getarg :extra-args-stobj-recognizers t kwd-alist))

       ((unless (and (symbol-listp extra-args)
                     (not (intersectp-eq '(x y z) extra-args))))
        (er soft 'defsort ":extra-args must be a symbol list not containing ~x0, ~x1, or ~x2.~%"
            'x 'y 'z))
       ((unless compare<)
        (er soft 'defsort "Defsort requires :compare< to be specified"))

       (definedp         (or comparable-listp (and (not comparablep) true-listp)))
       (comparable-listp (or comparable-listp
                             (if comparablep
                                 (mksym prefix "-LIST-P")
                               (and true-listp 'true-listp))))
       (orderedp         (mksym prefix "-ORDERED-P"))
       (merge            (mksym prefix "-MERGE"))
       (merge-tr         (mksym prefix "-MERGE-TR"))
       (fixnum           (mksym prefix "-MERGESORT-FIXNUM"))
       (integer          (mksym prefix "-MERGESORT-INTEGERS"))

       (comparablep      (fix-comparablep comparablep))
       (comparable-inst  (if comparablep
                             `(lambda (x) (,comparablep x . ,extra-args))
                           `(lambda (x) t)))
       (comparable-listp-inst (if (or comparablep true-listp)
                                  `(lambda (x) (,comparable-listp x . ,extra-args))
                                `(lambda (x) t)))
       (element-list-final-cdr-inst (if true-listp
                                        `(lambda (x) (not x))
                                      `(lambda (x) t)))

       ((mv compare-guard state) (defsort-guard-for-term `(,compare< x x . ,extra-args) state))
       ((mv comparablep-guard state)
        (if comparablep
            (defsort-guard-for-term `(,comparablep x . ,extra-args) state)
          (mv t state)))

       (subst1          `((compare<  (lambda (x y) (,compare< x y . ,extra-args)))
                          (comparablep ,comparable-inst)
                          (comparable-listp ,comparable-listp-inst)
                          (element-list-final-cdr-p
                           ,element-list-final-cdr-inst)
                          (comparable-merge (lambda (x y) (,merge x y . ,extra-args)))
                          (comparable-orderedp (lambda (x) (,orderedp x . ,extra-args)))
                          (comparable-merge-tr (lambda (x y acc) (,merge-tr x y ,@extra-args acc)))
                          (fast-comparable-mergesort-fixnums (lambda (x len) (,fixnum x ,@extra-args len)))
                          (fast-comparable-mergesort-integers (lambda (x len) (,integer x ,@extra-args len)))
                          (comparable-mergesort (lambda (x) (,sort x . ,extra-args)))))

       (events1
        `(encapsulate
           ()
           (set-ignore-ok t)

           (local (defthm ,(mksym prefix "-TYPE-OF-COMPARE<")
                    (or (equal (,compare< x y . ,extra-args) t)
                        (equal (,compare< x y . ,extra-args) nil))
                    :rule-classes :type-prescription))

           ,@(and comparablep
                  `((local (defthm ,(mksym prefix "-TYPE-OF-COMPARABLEP")
                             (or (equal (,comparablep x . ,extra-args) t)
                                 (equal (,comparablep x . ,extra-args) nil))
                             :rule-classes :type-prescription))))

           (local (defthm ,(mksym prefix "-COMPARE<-TRANSITIVE")
                    (implies (and (,compare< x y . ,extra-args)
                                  (,compare< y z . ,extra-args))
                             (,compare< x z . ,extra-args))))

           ,@(and (not weak)
                  `((local (defthm ,(mksym prefix "-COMPARE<-NEGATION-TRANSITIVE")
                             (implies (and (not (,compare< x y . ,extra-args))
                                           (not (,compare< y z . ,extra-args)))
                                      (not (,compare< x z . ,extra-args)))))
                    (local (defthm ,(mksym prefix "-COMPARE<-STRICT")
                             (not (,compare< x x . ,extra-args))))))

           ,@(and comparablep
                  (not (eq compare-guard t))
                  (not (equal compare-guard `(,comparablep x)))
                  `((local
                     (make-event
                      '(:or (defthm defsort-comparablep-sufficient
                              (implies (and (,comparablep x . ,extra-args)
                                            ,extra-args-guard
                                            ,extra-args-stobj-recognizers)
                                       ,compare-guard)
                              :rule-classes (:rewrite :forward-chaining))
                        (value-triple
                         (er hard 'defsort
                             "Couldn't prove that given setting of ~
                              :comparablep, ~x0, implies the guard of the ~
                              comparison function ~x1, which is:~%~x2"
                             ',comparablep ',compare< ',compare-guard)))))))

           ,@(and comparablep
                  (not (eq comparablep-guard t))
                  (not (equal extra-args-guard comparablep-guard))
                  `((local
                     (make-event
                      '(:or (defthm defsort-extra-args-guard-sufficient
                              (implies (and ,extra-args-guard
                                            ,extra-args-stobj-recognizers)
                                       ,comparablep-guard)
                              :rule-classes (:rewrite :forward-chaining))
                        (value-triple
                         (er hard 'defsort
                             "Couldn't prove that the guard for the extra-args, ~x0,
                              implies the guard of comparablep (~x1), which is:~%~x2"
                             ',extra-args-guard ',comparablep ',comparablep-guard)))))))

           (local (in-theory (theory 'minimal-theory)))
           (local (in-theory (enable ,(mksym prefix "-TYPE-OF-COMPARE<")
                                     ,(mksym prefix "-COMPARE<-TRANSITIVE")
                                     defsort-theory)))

           ,@(and comparablep
                  (not (eq compare-guard t))
                  (not (equal compare-guard `(,comparablep x)))
                  `((local (in-theory (enable defsort-comparablep-sufficient)))))

           ,@(and comparablep
                  (not (eq comparablep-guard t))
                  (not (equal extra-args-guard comparablep-guard))
                  `((local (in-theory (enable defsort-extra-args-guard-sufficient)))))

           ,@(and comparablep
                  `((local (in-theory (enable ,(mksym prefix "-TYPE-OF-COMPARABLEP"))))))

           ,@(and (not weak)
                  `((local (in-theory (enable ,(mksym prefix "-COMPARE<-NEGATION-TRANSITIVE")
                                              ,(mksym prefix "-COMPARE<-STRICT"))))))

           ,@(and definedp (or comparablep true-listp)
                  `((local
                     (make-event
                      '(:or (defthm defsort-comparable-list-check
                              t
                              :hints ((defsort-functional-inst
                                        comparable-listp ,subst1
                                        :in-theory (enable ,comparable-listp)))
                              :rule-classes nil)
                        (value-triple
                         (er hard 'defsort
                             "The provided value of comparable-listp, ~x0, ~
                           failed consistency checks: either it is not ~
                           defined, or the :true-listp setting was incorrect, ~
                           or the definition doesn't match what we expected."
                             ',comparable-listp)))))))

           ;; The following is a pretty gross hack.  But sometimes the guard for
           ;; compare< might not perfectly line up with comparablep.  For
           ;; instance, if you try to create a sort for NATP objects by using <,
           ;; then the real guard for < uses RATIONALP instead and you would run
           ;; into problems, in the minimal theory, of trying to show that natp
           ;; implies rationalp.

           ;; So, if one of our proofs below is just about to fail, we go back to
           ;; the user's current theroy and try to prove the remaining goals.
           ;; This allows us to see these kind of rules.

           ;; (local (defun stupid-hint (stable-under-simplificationp)
           ;;          (and stable-under-simplificationp
           ;;               '(:in-theory (current-theory ',(mksym prefix "-COMPARE<-TRANSITIVE"))))))

           ;; (set-default-hints '((stupid-hint stable-under-simplificationp)))

           ;; (local (in-theory '(natp-compound-recognizer)))

           ,@(and (or comparablep true-listp) (not definedp)
                  `((defund ,comparable-listp (x . ,extra-args)
                      (declare (xargs :guard ,extra-args-guard
                                      :stobjs ,extra-args-stobjs))
                      (if (consp x)
                          (and (,comparablep (car x) . ,extra-args)
                               (,comparable-listp (cdr x) . ,extra-args))
                        ,(if true-listp `(eq x nil) t)))))

           ,@(and comparablep
                  `((local (defthm defsort-comparablep-of-car
                             (implies (and (,comparable-listp x . ,extra-args)
                                           (consp x))
                                      (,comparablep (car x) . ,extra-args))
                             :hints(("Goal" :in-theory nil
                                     :expand ((,comparable-listp x . ,extra-args))))))))

           ,@(and (or comparablep true-listp)
                  `((local (defthm defsort-comparable-listp-of-cdr
                             (implies (,comparable-listp x . ,extra-args)
                                      (,comparable-listp (cdr x) . ,extra-args))
                             :hints(("Goal" :in-theory '(default-cdr)
                                     :expand ((,comparable-listp x . ,extra-args)
                                              (,comparable-listp nil . ,extra-args))))))

                    ;; This follows from the above two but is sometimes
                    ;; necessary if comparablep is e.g. (lambda (x extra-args)
                    ;; (foo x)), because then it needs to match extra-args as a
                    ;; free variable.  We only need to do this when comparablep is a lambda.
                    ,@(and (consp comparablep)
                           `((local (defthm defsort-comparablep-of-cadr
                                      (implies (and (,comparable-listp x . ,extra-args)
                                                    (consp x)
                                                    (consp (cdr x)))
                                               (,comparablep (cadr x) . ,extra-args))
                                      :hints(("Goal" :in-theory nil
                                              :expand ((,comparable-listp x . ,extra-args)
                                                       (,comparable-listp (cdr x) . ,extra-args))))))))))

           (defund ,orderedp (x . ,extra-args)
             (declare (xargs :guard ,(if (or comparablep true-listp)
                                         `(and ,extra-args-guard
                                               (,comparable-listp x . ,extra-args))
                                       extra-args-guard)
                             :stobjs ,extra-args-stobjs
                             :measure (len x)))
             (cond ((atom x)
                    t)
                   ((atom (cdr x))
                    t)
                   ((,compare< (first x) (second x) . ,extra-args)
                    (,orderedp (cdr x) . ,extra-args))
                   (t
                    (and (not (,compare< (second x) (first x) . ,extra-args))
                         (,orderedp (cdr x) . ,extra-args)))))


           (defund ,merge (x y . ,extra-args)
             (declare (xargs :measure (+ (len x)
                                         (len y))
                             :stobjs ,extra-args-stobjs
                             :guard ,(if (or comparablep true-listp)
                                         `(and ,extra-args-guard
                                               (,comparable-listp x . ,extra-args)
                                               (,comparable-listp y . ,extra-args))
                                       extra-args-guard)))
             (cond ((atom x)
                    y)
                   ((atom y)
                    x)
                   ((,compare< (car y) (car x) . ,extra-args)
                    (cons (car y) (,merge x (cdr y) . ,extra-args)))
                   (t
                    (cons (car x) (,merge (cdr x) y . ,extra-args)))))

           (defund ,merge-tr (x y ,@extra-args acc)
             (declare (xargs :measure (+ (len x)
                                         (len y))
                             :stobjs ,extra-args-stobjs
                             :guard ,(if (or comparablep true-listp)
                                         `(and ,extra-args-guard
                                               (,comparable-listp x . ,extra-args)
                                               (,comparable-listp y . ,extra-args))
                                       extra-args-guard)))
             (cond ((atom x)
                    (revappend-without-guard acc y))
                   ((atom y)
                    (revappend-without-guard acc x))
                   ((,compare< (car y) (car x) . ,extra-args)
                    (,merge-tr x (cdr y) ,@extra-args (cons (car y) acc)))
                   (t
                    (,merge-tr (cdr x) y ,@extra-args (cons (car x) acc)))))

           (defund ,fixnum (x ,@extra-args len)
             (declare (xargs :measure (nfix len)
                             :stobjs ,extra-args-stobjs
                             :guard (and ,extra-args-guard
                                         ,(if (or comparablep true-listp)
                                              `(,comparable-listp x . ,extra-args)
                                            t)
                                         (natp len)
                                         (<= len (len x)))
                             :verify-guards nil)
                      (type (signed-byte 30) len))
             (cond ((mbe :logic (zp len)
                         :exec (eql (the (signed-byte 30) len) 0))
                    nil)

                   ((eql (the (signed-byte 30) len) 1)
                    (list (car x)))

                   (t
                    (let* ((len1  (the (signed-byte 30)
                                    (ash (the (signed-byte 30) len) -1)))
                           (len2  (the (signed-byte 30)
                                    (- (the (signed-byte 30) len)
                                       (the (signed-byte 30) len1))))
                           (part1 (,fixnum x ,@extra-args len1))
                           (part2 (,fixnum (rest-n len1 x) ,@extra-args len2)))
                      (,merge-tr part1 part2 ,@extra-args nil)))))

           (defund ,integer (x ,@extra-args len)
             (declare (xargs :measure (nfix len)
                             :stobjs ,extra-args-stobjs
                             :guard (and ,extra-args-guard
                                         ,(if (or comparablep true-listp)
                                              `(,comparable-listp x . ,extra-args)
                                            t)
                                         (natp len)
                                         (<= len (len x)))
                             :verify-guards nil)
                      (type integer len))
             (cond ((mbe :logic (zp len)
                         :exec (eql (the integer len) 0))
                    nil)
                   ((eql (the integer len) 1)
                    (list (car x)))
                   (t
                    (let* ((len1  (the integer (ash (the integer len) -1)))
                           (len2  (the integer
                                    (- (the integer len)
                                       (the integer len1))))
                           (part1 (if (< (the integer len1) (mergesort-fixnum-threshold))
                                      (,fixnum x ,@extra-args len1)
                                    (,integer x ,@extra-args len1)))
                           (part2 (if (< (the integer len2) (mergesort-fixnum-threshold))
                                      (,fixnum (rest-n len1 x) ,@extra-args len2)
                                    (,integer (rest-n len1 x) ,@extra-args len2))))
                      (,merge-tr part1 part2 ,@extra-args nil)))))

           (defund ,sort (x . ,extra-args)
             (declare (xargs :guard ,(if (or comparablep true-listp)
                                         `(and ,extra-args-guard
                                               (,comparable-listp x . ,extra-args))
                                       extra-args-guard)
                             :measure (len x)
                             :stobjs ,extra-args-stobjs
                             :verify-guards nil))
             (mbe :logic
                  (cond ((atom x)
                         nil)
                        ((atom (cdr x))
                         (list (car x)))
                        (t
                         (let ((half (floor (len x) 2)))
                           (,merge
                            (,sort (take half x) . ,extra-args)
                            (,sort (nthcdr half x) . ,extra-args)
                            . ,extra-args))))

                  :exec
                  (let ((len (len x)))
                    (if (< len (mergesort-fixnum-threshold))
                        (,fixnum x ,@extra-args len)
                      (,integer x ,@extra-args len)))))

           ;; Prove our functional substitution ok once and for all
           (local (defthm defsort-subst1-ok
                    t
                    :rule-classes nil
                    :hints ((defsort-functional-inst
                              (:theorem (and (equal (comparable-mergesort x)
                                                    (comparable-mergesort x))
                                             (equal (comparable-orderedp x)
                                                    (comparable-orderedp x))
                                             (equal (comparable-listp x)
                                                    (comparable-listp x))))
                              ,subst1
                              :expand ((,sort x . ,extra-args)
                                       (,merge x y . ,extra-args)
                                       (,integer x ,@extra-args len)
                                       (,fixnum x ,@extra-args len)
                                       (,merge-tr x y ,@extra-args acc)
                                       (,orderedp x . ,extra-args)
                                       ,@(and (or comparablep true-listp)
                                              `((,comparable-listp x . ,extra-args))))))))

           (verify-guards ,fixnum
             :hints ((defsort-functional-inst
                       fast-comparable-mergesort-fixnums-guards
                       ,subst1)))

           (verify-guards ,integer
             :hints ((defsort-functional-inst
                       fast-comparable-mergesort-integers-guards
                       ,subst1)))

           ;; (defthm ,(mksym prefix "-FIXNUM-REDEF")
           ;;   (equal (,fixnum x (len x))
           ;;          (,sort x))
           ;;   :hints ((defsort-functional-inst
           ;;             fast-comparable-mergesort-fixnums-of-len-is-spec
           ;;             ,subst1)))

           ;; (defthm ,(mksym prefix "-INTEGER-REDEF")
           ;;   (equal (,integer x (len x))
           ;;          (,sort x))
           ;;   :hints ((defsort-functional-inst
           ;;             fast-comparable-mergesort-integers-of-len-is-spec
           ;;             ,subst1)))

           (verify-guards ,sort
             :hints ((defsort-functional-inst
                       comparable-mergesort-guard
                       ,subst1)))

           (defthm ,(mksym prefix "-SORT-PRESERVES-DUPLICITY")
             (equal (duplicity a (,sort x . ,extra-args))
                    (duplicity a x))
             :hints((defsort-functional-inst
                      duplicity-of-comparable-mergesort
                      ,subst1)))

           ,@(and (or comparablep true-listp)
                  `((defthm ,(mksym prefix "-SORT-CREATES-COMPARABLE-LISTP")
                      (implies (,comparable-listp x . ,extra-args)
                               (,comparable-listp (,sort x . ,extra-args) . ,extra-args))
                      :hints((defsort-functional-inst
                               comparable-listp-of-comparable-mergesort ,subst1)))))

           (defthm ,(mksym prefix "-SORT-SORTS")
             (,orderedp (,sort x . ,extra-args) . ,extra-args)
             :hints((defsort-functional-inst
                      comparable-orderedp-of-comparable-mergesort
                      ,subst1
                      :in-theory (enable ,orderedp))))

           (defthm ,(mksym prefix "-SORT-NO-DUPLICATESP-EQUAL")
             (equal (no-duplicatesp-equal (,sort x . ,extra-args))
                    (no-duplicatesp-equal x))
             :hints((defsort-functional-inst
                      no-duplicatesp-equal-of-comparable-mergesort
                      ,subst1)))

           (defthm ,(mksym prefix "-SORT-TRUE-LISTP")
             (true-listp (,sort x . ,extra-args))
             :rule-classes :type-prescription
             :hints((defsort-functional-inst
                      true-listp-of-comparable-mergesort
                      ,subst1)))

           (defthm ,(mksym prefix "-SORT-LEN")
             (equal (len (,sort x . ,extra-args))
                    (len x))
             :hints ((defsort-functional-inst
                       len-of-comparable-mergesort
                       ,subst1)))

           (defthm ,(mksym prefix "-SORT-CONSP")
             (equal (consp (,sort x . ,extra-args))
                    (consp x))
             :hints ((defsort-functional-inst
                       consp-of-comparable-mergesort
                       ,subst1)))

           (defthm ,(mksym prefix "-SORT-IS-IDENTITY-UNDER-SET-EQUIV")
             (set-equiv (,sort x . ,extra-args) x)
             :hints ((defsort-functional-inst
                       comparable-mergesort-is-identity-under-set-equiv
                       ,subst1)))))

       ((when weak) (value events1))

       (insert           (mksym prefix "-INSERT"))
       (insertsort       (mksym prefix "-INSERTSORT"))

       (subst2          `((compare<-negation-transitive (lambda () t))
                          (compare<-strict              (lambda () t))
                          (comparable-insert            (lambda (elt x) (,insert elt x . ,extra-args)))
                          (comparable-insertsort        (lambda (x) (,insertsort x . ,extra-args)))
                          . ,subst1))

       (events2
        `((defund ,insert (elt x . ,extra-args)
            (declare (xargs :guard ,(if (or comparablep true-listp)
                                        `(and ,extra-args-guard
                                              ,@(and comparablep
                                                     `((,comparablep elt . ,extra-args)))
                                              (,comparable-listp x . ,extra-args))
                                      extra-args-guard)
                            :stobjs ,extra-args-stobjs
                            :measure (len x)))
            (if (atom x)
                (list elt)
              (if (,compare< (car x) elt . ,extra-args)
                  (cons (car x) (,insert elt (cdr x) . ,extra-args))
                (cons elt x))))

          (defund ,insertsort (x . ,extra-args)
            (declare (xargs :guard ,(if (or comparablep true-listp)
                                        `(and ,extra-args-guard
                                              (,comparable-listp x . ,extra-args))
                                      extra-args-guard)
                            :stobjs ,extra-args-stobjs
                            :verify-guards nil
                            :measure (len x)))
            (if (atom x)
                nil
              (,insert (car x) (,insertsort (cdr x) . ,extra-args) . ,extra-args)))

          (local (defthm defsort-subst2-ok
                   t
                   :rule-classes nil
                   :hints ((defsort-functional-inst
                             (:theorem (equal (comparable-insertsort x)
                                              (comparable-insertsort x)))
                             ,subst2
                             :expand ((,insert elt x . ,extra-args)
                                      (,insertsort x . ,extra-args))))))

          (verify-guards ,insertsort
            :hints ((defsort-functional-inst
                      comparable-insertsort-guard
                      ,subst2)))

          (defthm ,(mksym prefix "-MERGESORT-EQUALS-INSERTSORT")
            (equal (,sort x . ,extra-args)
                   (,insertsort x . ,extra-args))
            :hints ((defsort-functional-inst
                      comparable-mergesort-equals-comparable-insertsort
                      ,subst2)))

          (defthm ,(mksym prefix "-INSERTSORT-PRESERVES-DUPLICITY")
             (equal (duplicity a (,insertsort x . ,extra-args))
                    (duplicity a x))
             :hints(("goal" :use ,(mksym prefix "-SORT-PRESERVES-DUPLICITY")
                     :in-theory (disable ,(mksym prefix "-SORT-PRESERVES-DUPLICITY")))))

           ,@(and (or comparablep true-listp)
                  `((defthm ,(mksym prefix "-INSERTSORT-CREATES-COMPARABLE-LISTP")
                      (implies (,comparable-listp x . ,extra-args)
                               (,comparable-listp (,insertsort x . ,extra-args) . ,extra-args))
                      :hints(("goal" :use ,(mksym prefix "-SORT-CREATES-COMPARABLE-LISTP")
                              :in-theory (disable ,(mksym prefix "-SORT-CREATES-COMPARABLE-LISTP")))))))

           (defthm ,(mksym prefix "-INSERTSORT-SORTS")
             (,orderedp (,insertsort x . ,extra-args) . ,extra-args)
             :hints(("goal" :use ,(mksym prefix "-SORT-SORTS")
                     :in-theory (disable ,(mksym prefix "-SORT-SORTS")))))

           (defthm ,(mksym prefix "-INSERTSORT-NO-DUPLICATESP-EQUAL")
             (equal (no-duplicatesp-equal (,insertsort x . ,extra-args))
                    (no-duplicatesp-equal x))
             :hints(("goal" :use ,(mksym prefix "-SORT-NO-DUPLICATESP-EQUAL")
                     :in-theory (disable ,(mksym prefix "-SORT-NO-DUPLICATESP-EQUAL")))))

           (defthm ,(mksym prefix "-INSERTSORT-TRUE-LISTP")
             (true-listp (,insertsort x . ,extra-args))
             :rule-classes :type-prescription
             :hints(("goal" :use ,(mksym prefix "-SORT-TRUE-LISTP")
                     :in-theory (disable ,(mksym prefix "-SORT-TRUE-LISTP")))))

           (defthm ,(mksym prefix "-INSERTSORT-LEN")
             (equal (len (,insertsort x . ,extra-args))
                    (len x))
             :hints (("goal" :use ,(mksym prefix "-SORT-LEN")
                     :in-theory (disable ,(mksym prefix "-SORT-LEN")))))

           (defthm ,(mksym prefix "-INSERTSORT-CONSP")
             (equal (consp (,insertsort x . ,extra-args))
                    (consp x))
             :hints (("goal" :use ,(mksym prefix "-SORT-CONSP")
                      :in-theory (disable ,(mksym prefix "-SORT-CONSP"))))))))
    (value (append events1 events2))))

(defmacro defsort (&rest args)
  `(make-event
    (defsort-fn ',args state)))
