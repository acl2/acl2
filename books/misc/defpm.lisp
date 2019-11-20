; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann, December, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file introduces two macros: Def-partial-measure (or defpm for short)
; introduces a measure and a termination predicate for a give pair of test and
; step functions, to use in admitting a corresponding definition without the
; need for a custom termination proof.  Defthm-domain then can be used to prove
; that the termination predicate holds on a specified domain.

; Note: A related utility, due to Dave Greve, may be found in community books
; directory books/coi/termination/assuming/.  The present file was developed
; independently.  Our approach seems considerably simpler than Greve's
; development, but for example, his utility handles reflexive functions --
; recursive calls like (mc91 (mc91 (+ n 11))) -- while ours probably does not.
; Another potentially related utility may be found in
; books/workshops/2004/matthews-vroon/.

; Examples are towards the end of this file.

;;; To do: Perhaps it would be useful to modify defpm and defthm-domain so that
;;; they take the test and step as terms rather than symbols, in which case
;;; their definitions would be generated, rather than requiring the user to
;;; define functions like fact-test (below).  We might also consider automating
;;; the production of additional stuff, as described in comments below.

#||
;; [Jared] this was previously a depends-on arithmetic-top-theory.cert line.
;; However that didn't seem to work right; see Issue 383 for details.  As a
;; workaround, replacing it with this phony include-book.
(include-book "arithmetic-top-theory")
||#

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defpointer defpm def-partial-measure)

(defxdoc def-partial-measure
  :parents (macro-libraries)
  :short "Introduce measure and termination predicates for a partial function
 definition"
  :long "<h3>Introduction By Way of an Example</h3>

 <p>We begin with a motivating example.  Suppose we want to admit factorial
 without the need to prove termination, as follows.</p>

 @({
 (fact x)
 =
 (if (equal x 0)
     1
   (* x (fact (1- x))))
 })

 <p>Of course, this ``definition'' is non-terminating on negative number
 inputs.  But with @('def-partial-measure'), or @('defpm') for short, we can
 admit a suitable definition for this partial function as follows.  First, we
 define a function to represent the termination test and another function to
 represent the actual parameter of the recursive call.</p>

 @({
 (defun fact-test (x)
   (equal x 0))
 (defun fact-step (x)
   (1- x))
 })

 <p>Now we can execute our utility: we provide it with the names of the two
 functions above, and it generates a measure, a termination predicate, and a
 potentially helpful theory, respectively.</p>

 @({
 (defpm fact-test fact-step
   fact-measure fact-terminates fact-theory)
 })

 <p>Here are the @(see events) exported by the @('defpm') call above.</p>

 @({
 ; The first three lemmas can be useful for reasoning about the termination
 ; predicate, FACT-TERMINATES.

 (DEFTHM FACT-TERMINATES-BASE
   (IMPLIES (FACT-TEST X)
            (FACT-TERMINATES X)))

 (DEFTHM FACT-TERMINATES-STEP
   (IMPLIES (NOT (FACT-TEST X))
            (EQUAL (FACT-TERMINATES (FACT-STEP X))
                   (FACT-TERMINATES X))))

 (DEFTHMD FACT-TERMINATES-STEP-COMMUTED
   (IMPLIES (AND (SYNTAXP (SYMBOLP X))
                 (NOT (FACT-TEST X)))
            (EQUAL (FACT-TERMINATES X)
                   (FACT-TERMINATES (FACT-STEP X)))))

 (THEORY-INVARIANT (INCOMPATIBLE (:REWRITE FACT-TERMINATES-STEP)
                                 (:REWRITE FACT-TERMINATES-STEP-COMMUTED)))

 ; The next two lemmas can be useful for defining functions whose termination
 ; is ensured by the measure just introduced.

 (DEFTHM FACT-MEASURE-TYPE
   (O-P (FACT-MEASURE X)))

 (DEFTHM FACT-MEASURE-DECREASES
   (IMPLIES (AND (FACT-TERMINATES X)
                 (NOT (FACT-TEST X)))
            (O< (FACT-MEASURE (FACT-STEP X))
                (FACT-MEASURE X))))

 ; Finally, the four enabled rewrite rules above are collected into a theory.

 (DEFTHEORY FACT-THEORY
   '(FACT-TERMINATES-BASE FACT-TERMINATES-STEP
     FACT-MEASURE-TYPE FACT-MEASURE-DECREASES))
 })

 <p>With the events above, we can introduce the following definition, which in
 effect guards the body with the termination predicate.  (Perhaps at some point
 we will extend @('defpm') to create this definition automatically.)  The
 @(':')@(tsee in-theory) hint below was carefully crafted to allow the proof to
 succeed very quickly.</p>

 @({
 (defun fact (x)
   (declare (xargs :measure (fact-measure x)
                   :hints ((\"Goal\"
                            :in-theory
                            (union-theories (theory 'fact-theory)
                                            (theory 'minimal-theory))))))
   (if (fact-terminates x)
       (if (fact-test x)
           1
         (* x (fact (fact-step x))))
     1 ; don't-care
     ))
 })

 <p>With the events above (not necessarily including the definition of
 @('fact')), we can prove that @('fact') terminates on natural number inputs.
 A second macro, @('defthm-domain'), automates much of that task:</p>

 @({
 (defthm-domain fact-terminates-holds-on-natp
   (implies (natp x)
            (fact-terminates x))
   :measure (nfix x))
 })

 <p>See @(see defthm-domain).</p>

 <h3>Detailed Documentation</h3>

 <p>General form:</p>

 @({
 (defpm ; or equivalently, def-partial-measure ; ;
   TEST STEP
   MEASURE TERMINATES THEORY
   :formals FORMALS ; default is (x)
   :verbose VERBOSE ; default is nil
   )
 })

 <p>where there is no output unless @('VERBOSE') is non-@('nil').  The
 remaining arguments are as follows.</p>

 <p>First consider the case that @('FORMALS') is the default, @('(x)').  The
 arguments @('TEST') and @('STEP') are conceptually ``inputs'': they should
 name existing functions on the indicated value for formals (which by default
 is @('(x)')).  Then @('defpm') will attempt to generate a measure and
 termination predicate on those formals, with the indicated names (@('MEASURE')
 and @('TERMINATES'), respectively).  These theorems are suitable for admitting
 a function of the following form, where capitalized names refer to those in
 the @('defpm') call above, and where additional code may appear as indicated
 with ``...''.</p>

 @({
 (defun foo (x)
   (declare (xargs :measure (MEASURE x)
                   :hints ((\"Goal\"
                            :in-theory
                            (union-theories (theory 'THEORY)
                                            (theory 'minimal-theory))))))
   (if (TERMINATES x)
       (if (TEST x)
           ...
         (... (fact (STEP x)) ...)
     ...))
 })

 <p>The generated @('THEORY') names the four rules generated by the @('defpm')
 call, as in the example above.</p>

 @({
 (defthm TERMINATES-base
   (implies (TEST x)
            (TERMINATES x)))
 (defthm TERMINATES-step
   (implies (not (TEST x))
            (equal (TERMINATES (STEP x))
                   (TERMINATES x))))
 (defthmd TERMINATES-step-commuted
   (implies (AND (syntaxp (symbolp x))
                 (not (TEST x)))
            (equal (TERMINATES x)
                   (TERMINATES (STEP x)))))
 (theory-invariant (incompatible (:rewrite TERMINATES-step)
                                 (:rewrite TERMINATES-step-commuted)))
 (defthm MEASURE-type
   (o-p (MEASURE x)))
 (defthm MEASURE-decreases
   (implies (and (TERMINATES x)
                 (not (TEST x)))
            (o< (MEASURE (STEP x))
                (MEASURE x))))
 (deftheory THEORY
   '(TERMINATES-base TERMINATES-step MEASURE-type MEASURE-decreases))
 })

 <p>For arbitrary formals the situation is similar, except that there is one
 step function per formal, obtained by adding the formal name as a suffix to
 the specified @('STEP') separated by a hyphen.  Thus we have the following
 events when @('FORMALS') is @('(y1 ... yk)').</p>

 @({
 (defthm TERMINATES-base
   (implies (TEST y1 ... yk)
            (TERMINATES y1 ... yk)))
 (defthm TERMINATES-step
   (implies (not (TEST y1 ... yk))
            (equal (TERMINATES (STEP-y1 y1 ... yk)
                               ...
                               (STEP-yk y1 ... yk))
                   (TERMINATES y1 ... yk))))
 (defthm TERMINATES-step-commuted
   (implies (AND (syntaxp (symbolp y1)) ... (syntaxp (symbolp yk))
                 (not (TEST y1 ... yk)))
            (equal (TERMINATES (STEP-y1 y1 ... yk)
                               ...
                               (STEP-yk y1 ... yk))
                   (TERMINATES y1 ... yk))))
 (theory-invariant (incompatible (:rewrite TERMINATES-step)
                                 (:rewrite TERMINATES-step-commuted)))
 (defthm MEASURE-type
   (o-p (MEASURE y1 ... yk)))
 (defthm MEASURE-decreases
   (implies (and (TERMINATES y1 ... yk)
                 (not (TEST y1 ... yk)))
            (o< (MEASURE (STEP-y1 y1 ... yk)
                         ...
                         (STEP-yk y1 ... yk))
                (MEASURE y1 ... yk))))
 (deftheory THEORY
   '(TERMINATES-base TERMINATES-step MEASURE-type MEASURE-decreases))
 })

 <h3>Implementation</h3>

 <p>The implementation of @('defpm') (i.e., @('def-partial-measure') has been
 designed to make proofs efficient.  It should be completely unnecessary to
 know anything about the implementation in order to use @('defpm') effectively.
 If however you are interested, you can execute @(':')@(tsee trans1) on your
 @('defpm') call to see the @(see events) that it generates.</p>

 <h3>More Information</h3>

 <p>The community book @('misc/defpm.lisp') illustrates how to use @('defpm')
 and @('defthm-domain') to define ``partial'' functions.  Search for calls of
 @('my-test') in that book to see examples.</p>

 <p>Related work of Dave Greve, in particular his utility @('def::ung'), may be
 found in community books directory @('books/coi/defung/').  Our utilities
 @('def-partial-measure') and @(tsee defthm-domain) were developed
 independently using an approach that seems considerably simpler than Greve's
 development.  However, his utility is much more powerful in that it generates
 a termination test, rather than requiring the user to provide it, and also it
 handles reflexive functions &mdash; definitions with recursive calls like
 @('(mc91 (mc91 (+ n 11)))') &mdash; while ours were not designed to do
 so.</p>")

(defpointer defpm def-partial-measure)

(defxdoc defthm-domain
  :parents (macro-libraries)
  :short "Prove termination on a given domain"
  :long "<p>This utility can be useful after executing a call of @('defpm');
 see @(see def-partial-measure).  Indeed, we assume that you have read the
 example in that @(see documentation) topic describing this call:</p>

 @({
 (defpm fact-test fact-step
   fact-measure fact-terminates fact-theory)
 })

 <h3>Introduction By Way of an Example</h3>

 <p>Consider the following form.</p>

 @({
 (defthm-domain trfact-terminates-holds-on-natp
   (implies (natp x)
            (trfact-terminates x acc))
   :test trfact-test ; optional test name: can be deduced by the tool ;
   :step trfact-step ; optional step name: can be deduced by the tool ;
   :measure (nfix x) ; required argument ;
   )
 })

 <p>This call produces a proof of the indicated formula, where the first
 argument of @('implies'), @('(natp x)'), provides a ``domain hypothesis.''
 You can use @(':')@(tsee trans1) to see the macroexpansion of this
 @('defthm-domain') call.  In short, @(see hints) are supplied to automate all
 ``boilerplate'' reasoning.  The @(':measure') is used to guide a proof by
 induction.  At this stage of development, the best way to use this macro is
 probably to submit the form in the hope that the proof will complete
 automatically; but if it doesn't, then use @(':')@(tsee trans1) to see what
 the form generates, and modify that event manually in order to fix the failed
 proofs.</p>

 <h3>Detailed Documentation</h3>

 <p>General form:</p>

 @({
 (defthm-domain NAME
   (implies DOMAIN-TERM
            (TERMINATES FORMAL-1 ... FORMAL-K))
   :test TEST
   :step STEP
   :measure MEASURE
   :verbose VERBOSE
   :root ROOT
   )
 })

 <p>where there is no output unless @('VERBOSE') is non-@('nil').  It is
 allowed to replace the @(tsee implies) call above by its second argument (the
 @('TERMINATES') call) if @('DOMAIN-TERM') is @('t').  The remaining arguments
 are as follows.</p>

 <p>The keywords @(':test') and @(':step') both have value @('nil') by default.
 So does @(':root'), unless @('TERMINATES') has a @(tsee symbol-name) of the
 form @('\"root-TERMINATES\"'), in which case :root is the symbol in the
 package of @('TERMINATES') whose name is that string, @('root').  If
 @(':root') has a value of @('nil'), even after taking this default into
 account, then both @(':test') and @(':step') must have a non-@('nil') value.
 The reason for this requirement is that when @(':test') and/or @(':step') is
 omitted, the value is computed from the root by adding the suffix
 @('\"-TEST\"') or @('\"-STEP\"') to the root (respectively).  The functions
 introduced for @(':test') and @(':step') are exactly as for @('defpm'); see
 @(see def-partial-measure).  Note however that the formals are those from the
 call of @('TERMINATES').</p>

 <p>See the discussion above about ``boilerplate'' reasoning for hints on how
 to deal with failures of @('defthm-domain') calls.</p>

 <h3>More Information</h3>

 <p>The community book @('misc/defpm.lisp') illustrates how to use @('defpm')
 and @('defthm-domain') to define ``partial'' functions.  Search for calls of
 @('my-test') in that book to see examples.</p>")

(defun defpm-add-suffix (sym suffix)
  (declare (xargs :guard (and (symbolp sym)
                              (or (symbolp suffix)
                                  (stringp suffix)))))
  (intern-in-package-of-symbol
   (concatenate 'string
                (symbol-name sym)
                "-"
                (if (symbolp suffix)
                    (symbol-name suffix)
                  suffix))
   sym))

(defun defpm-add-suffix-lst (sym lst)
  (declare (xargs :guard (and (symbolp sym)
                              (or (symbol-listp lst)
                                  (string-listp lst)))))
  (cond ((endp lst) nil)
        (t (cons (defpm-add-suffix sym (car lst))
                 (defpm-add-suffix-lst sym (cdr lst))))))

(defun defpm-make-suffix-lst (str lst)
  (declare (xargs :guard (and (stringp str)
                              (symbol-listp lst))))
  (cond ((endp lst) nil)
        (t (cons (concatenate 'string str (symbol-name (car lst)))
                 (defpm-make-suffix-lst str (cdr lst))))))

(defun defpm-make-calls (fns formals)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp formals))))
  (cond ((endp fns) nil)
        (t (cons (cons (car fns) formals)
                 (defpm-make-calls (cdr fns) formals)))))

(defun syntaxp-symbolp-lst (formals)
  (declare (xargs :guard (true-listp formals)))
  (cond ((endp formals) nil)
        (t (cons `(syntaxp (symbolp ,(car formals)))
                 (syntaxp-symbolp-lst (cdr formals))))))

(make-event
 (pprogn (f-put-global 'defpm-arithmetic-top-book
                       (extend-pathname (cbd) "arithmetic-top-theory" state)
                       state)
         (value '(value-triple :defpm-arithmetic-top-book-set)))
 :check-expansion t)

(defun defpm-form (test steps measure terminates theory formals)
  (declare (xargs :guard
                  (and (symbol-listp (list measure terminates theory))
                       (or (symbolp steps) ; add formals as suffixes
                           (symbol-listp steps))
                       (symbol-listp formals)
                       (not (intersectp-eq '(defpm-m defpm-n defpm-clk)
                                           formals)))))
  (let* ((steps (if (symbolp steps)
                    (if (cdr formals)
                        (defpm-add-suffix-lst steps formals)
                      (list steps))
                  steps))
         (step-calls (defpm-make-calls steps formals))
         (measure-type (defpm-add-suffix measure "TYPE"))
         (terminates-base (defpm-add-suffix terminates "BASE"))
         (terminates-step (defpm-add-suffix terminates "STEP"))
         (terminates-step-commuted (defpm-add-suffix terminates "STEP-COMMUTED"))
         (measure-decreases (defpm-add-suffix measure "DECREASES")))
    `(encapsulate
      ((,measure ,formals t)
       (,terminates ,formals t))

; Set the theory to be one that is independent of

      (local (make-event (list 'include-book (@ defpm-arithmetic-top-book))))
      (local (in-theory (theory 'arithmetic-top-theory)))
      (local (in-theory (enable natp)))

      (local
       (encapsulate
        ()

        (defun defpm-clk-rec (,@formals n)
          (declare (xargs :measure (nfix n)))
          (cond ((,test ,@formals) n)
                ((zp n) nil)
                (t (defpm-clk-rec ,@step-calls (1- n)))))

        (defchoose defpm-clk-wit (defpm-n)

; Choose n, if possible, such that the intended definition terminates.

          ,formals
          (and (natp defpm-n)
               (defpm-clk-rec ,@formals defpm-n)))

        (defun defpm-clk-bound ,formals

; If for some natp n, (defpm-clk-rec ,@formals n), then return some such n.
; Otherwise returns nil.

          (let ((defpm-n (defpm-clk-wit ,@formals)))
            (and (natp defpm-n)
                 (defpm-clk-rec ,@formals defpm-n)
                 defpm-n)))

        (defun defpm-clk ,formals

; Returns the number of steps to termination.

          (let ((defpm-n (defpm-clk-bound ,@formals)))
            (and defpm-n
                 (- defpm-n (defpm-clk-rec ,@formals defpm-n)))))

        (defthm defpm-clk-rec-decreases
          (implies (natp defpm-n)
                   (<= (defpm-clk-rec ,@formals defpm-n)
                       defpm-n))
          :rule-classes :linear)

        (defthm defpm-clk-0-implies-test-lemma-1
          (implies (and (natp defpm-n)
                        (natp defpm-m)
                        (defpm-clk-rec ,@formals defpm-n)
                        (defpm-clk-rec ,@formals defpm-m))
                   (equal (- defpm-n (defpm-clk-rec ,@formals defpm-n))
                          (- defpm-m (defpm-clk-rec ,@formals defpm-m))))
          :rule-classes nil)

        (defthm defpm-clk-suff
          (implies (and (defpm-clk-rec ,@formals defpm-n)
                        (natp defpm-n))
                   (defpm-clk ,@formals))
          :hints (("Goal" :use defpm-clk-wit)))

        (defthm defpm-tailrec-lemma-1
          (implies (and (defpm-clk ,@formals)
                        (not (,test ,@formals)))
                   (defpm-clk ,@step-calls))
          :hints (("Goal"
                   :in-theory (disable defpm-clk)
                   :expand ((defpm-clk ,@formals)
                            (defpm-clk-rec ,@formals
                              (defpm-clk-wit ,@formals))))))

        (defthm defpm-tailrec-lemma-2
          (implies (and (posp defpm-clk)
                        (defpm-clk-rec ,@formals (+ -1 defpm-clk)))
                   (equal (defpm-clk-rec ,@formals (+ -1 defpm-clk))
                          (1- (defpm-clk-rec ,@formals defpm-clk)))))

        (defthm defpm-tailrec-lemma-3
          (implies (and (posp defpm-clk)
                        (defpm-clk-rec ,@formals (+ -1 defpm-clk)))
                   (defpm-clk-rec ,@formals defpm-clk)))

        (defthm defpm-tailrec-lemma-4
          (implies (and (defpm-clk ,@formals)
                        (not (,test ,@formals)))
                   (< (defpm-clk ,@step-calls)
                      (defpm-clk ,@formals)))
          :hints (("Goal"
                   :expand ((defpm-clk ,@formals)
                            (defpm-clk-rec ,@formals
                              (defpm-clk-wit ,@formals)))
                   :use ((:instance defpm-clk-0-implies-test-lemma-1
                                    ,@(pairlis$ formals
                                                (pairlis$ step-calls nil))
                                    (defpm-m (defpm-clk-wit ,@formals))
                                    (defpm-n (defpm-clk-wit ,@step-calls))))))
          :rule-classes :linear)

        (defthm defpm-terminates-step-lemma
          (implies (not (,test ,@formals))
                   (implies (defpm-clk ,@step-calls)
                            (defpm-clk ,@formals)))
          :hints (("Goal"
                   :in-theory (disable defpm-clk-suff)
                   :use ((:instance defpm-clk-suff
                                    (defpm-n
                                      (1+ (defpm-clk-wit ,@step-calls)))))))
          :rule-classes nil)

        (defun ,measure ,formals
          (or (defpm-clk ,@formals) 0))

        (defun ,terminates ,formals
          (and (defpm-clk ,@formals) t))

        ))

      (defthm ,terminates-base
        (implies (,test ,@formals)
                 (,terminates ,@formals))
        :hints (("Goal" :use ((:instance defpm-clk-wit (defpm-n 0))))))

      (defthm ,terminates-step
        (implies (not (,test ,@formals))
                 (equal (,terminates ,@step-calls)
                        (,terminates ,@formals)))
        :hints (("Goal"
                 :in-theory (disable defpm-clk)
                 :use defpm-terminates-step-lemma)))

      (defthmd ,terminates-step-commuted
        (implies (and ,@(syntaxp-symbolp-lst formals)
                      (not (,test ,@formals)))
                 (equal (,terminates ,@formals)
                        (,terminates ,@step-calls)))
        :hints (("Goal"
                 :in-theory (disable defpm-clk)
                 :use defpm-terminates-step-lemma)))

      (defthm ,measure-type
        (o-p (,measure ,@formals)))

      (defthm ,measure-decreases
        (implies (and (,terminates ,@formals)
                      (not (,test ,@formals)))
                 (o< (,measure ,@step-calls)
                     (,measure ,@formals)))
        :hints (("Goal" :in-theory (disable defpm-clk))))

      ,@(and theory
             `((deftheory ,theory
                 '(,terminates-base
                   ,terminates-step
                   ,measure-type
                   ,measure-decreases)))))))

(defun maybe-verbose-form (form verbose)
  (cond (verbose form)
        (t `(with-output :off :all
                         :on (error)
                         :gag-mode nil
                         ,form))))

(defmacro def-partial-measure (test step measure terminates theory
                                    &key
                                    (formals '(x))
                                    (verbose 'nil))
  (maybe-verbose-form (defpm-form test step measure terminates theory formals)
                      verbose))

(defmacro defpm (test step measure terminates theory
                      &key
                      (formals '(x) formals-p)
                      (verbose 'nil verbose-p))
  `(def-partial-measure ,test ,step ,measure ,terminates ,theory
     ,@(and formals-p `(:formals ,formals))
     ,@(and verbose-p `(:verbose ,verbose))))

; Next, we introduce a utility for showing that a function terminates on its
; intended domain.

(defun defpm-root-from-terminates (terminates)
  (and (symbolp terminates)
       (let* ((term-string (symbol-name terminates))
              (tsuff "-TERMINATES")
              (len-suff (length tsuff))
              (len-term (length term-string)))
         (cond ((and (< len-suff len-term)
                     (equal (subseq term-string (- len-term len-suff) len-term)
                            tsuff))
                (intern-in-package-of-symbol
                 (subseq term-string 0 (- len-term len-suff))
                 terminates))
               (t nil)))))

(defun defthm-domain-form (thm-name
                           root
                           test step terminates
                           measure domain-term formals)
  (let* ((test (or test
                   (defpm-add-suffix root "TEST")))
         (step (or step
                   (defpm-add-suffix root "STEP")))
         (thm-name-fn
          (defpm-add-suffix thm-name "FN"))
         (thm-name-fn-main
          (defpm-add-suffix thm-name-fn "MAIN"))
         (thm-name-induction-hint
          (defpm-add-suffix thm-name "INDUCTION-HINT"))
         (steps (if (symbolp step)
                    (if (cdr formals)
                        (defpm-add-suffix-lst step formals)
                      (list step))
                  step))
         (step-calls (defpm-make-calls steps formals))
         (test-call (cons test formals))
         ;; !! Maybe share some bindings with defpm -- maybe macro based on mv-let?
         (terminates-base (defpm-add-suffix terminates "BASE"))
         (terminates-step (defpm-add-suffix terminates "STEP"))
         (domain-implies-terminates-base
          (defpm-add-suffix thm-name "BASE"))
         (domain-implies-terminates-step
          (defpm-add-suffix thm-name "STEP"))
         (step-preserves-domain
          (intern-in-package-of-symbol
           (concatenate 'string
                        (symbol-name step)
                        "-PRESERVES-"
                        (symbol-name terminates))
           step)))
    `(encapsulate
      ()

      (local
       (progn
         (defun ,thm-name-fn ,formals
           (implies ,domain-term
                    (,terminates ,@formals)))

         (defun ,thm-name-induction-hint ,formals
           (declare (xargs :measure ,measure
                           :hints (("Goal" :in-theory (enable ,test ,@steps)))))
           (if (or (not ,domain-term)
                   ,test-call)
               (list ,@formals)
             (,thm-name-induction-hint ,@step-calls)))

         (defthm ,domain-implies-terminates-base
           (implies (or (not ,domain-term)
                        ,test-call)
                    (,thm-name-fn ,@formals))
           :hints (("Goal"
                    :in-theory (union-theories '(,thm-name-fn ,terminates-base)
                                               (theory 'minimal-theory)))))

         (defthm ,step-preserves-domain
           (implies (and ,domain-term
                         (not ,test-call))
                    (let ,(pairlis$ formals (pairlis$ step-calls nil))
                      (declare (ignorable ,@formals))
                      ,domain-term))
           :hints (("Goal" :in-theory (enable ,test ,@steps)))
           :rule-classes nil)

         (defthm ,domain-implies-terminates-step
           (implies (and (not ,test-call)
                         (,thm-name-fn ,@step-calls))
                    (,thm-name-fn ,@formals))
           :hints (("Goal"
                    :use ,step-preserves-domain
                    :in-theory (union-theories '(,terminates-step ; from defpm
                                                 ,thm-name-fn)
                                               (theory 'minimal-theory)))))

         (defthm ,thm-name-fn-main
           (,thm-name-fn ,@formals)
           :hints (("Goal"
                    :induct (,thm-name-induction-hint ,@formals)
                    :in-theory (union-theories
                                '(,thm-name-induction-hint
                                  ,domain-implies-terminates-base
                                  ,domain-implies-terminates-step)
                                (theory 'minimal-theory))))
           :rule-classes nil)))

      (defthm ,thm-name
        ,(let ((term (cons terminates formals)))
           (if (eq domain-term t)
               term
             `(implies ,domain-term
                       ,term)))
        :hints (("Goal"
                 :use ,thm-name-fn-main
                 :in-theory (union-theories '(,thm-name-fn)
                                            (theory 'minimal-theory)))))

      )))

(defmacro defthm-domain (thm-name form
                                  &key
                                  root
                                  test step measure
                                  verbose)

; An example below shows how this all works without wrapping it up in a macro.

  (mv-let (domain-term terminates formals)
          (case-match form
            (('implies domain-term
                       (terminates . formals))
             (mv domain-term terminates formals))
            ((terminates . formals)
             (mv t terminates formals))
            (& (mv (er hard! 'defthm-domain
                       "Illegal form (see :doc defthm-domain):~|~x0"
                       form)
                   nil nil)))
          (let ((root (or root
                          (defpm-root-from-terminates terminates))))
            (prog2$
             (or root
                 (and test step)
                 (er hard 'defthm-domain
                     "Non-nil values are required in a defthm-domain either ~
                      for keyword :root or for for keywords :test and :step, ~
                      unless the termination predicate is a symbol whose name ~
                      ends in \"-TERMINATES\", for example, FOO-TERMINATES.  ~
                      The following form has termination predicate ~x0 is ~
                      thus illegal:~|~x1"
                     terminates
                     form))
             (maybe-verbose-form (defthm-domain-form thm-name
                                   root
                                   test step terminates
                                   measure domain-term formals)
                                 verbose)))))

; Below are little examples showing how to use defpm and defthm-domain.  These
; are local to this book, so they are run only at certification time, not at
; include-book time.

(local (defmacro my-test (label &rest forms)
         `(encapsulate ()
                       (deflabel ,label); prevent redundancy
                       (local (progn ,@forms)))))

; First, a trivial, very direct example.

(local (my-test test1

(defstub defpm-test (x) t)
(defstub defpm-step (x) t)
(defpm defpm-test defpm-step defpm-measure defpm-terminates
  defpm-theory)

(defun defpm-tailrec (x)
   (declare (xargs :measure (defpm-measure x)
                   :hints (("Goal"
                            :in-theory
                            (union-theories (theory 'defpm-theory)
                                            (theory 'minimal-theory))))))
   (if (defpm-terminates x)
       (if (defpm-test x)
           x
         (defpm-tailrec (defpm-step x)))
     x))

))

; Second (and more interesting) example, which also includes termination on a
; specified domain

(local (my-test test2

(defun trfact-test (x acc)
  (declare (ignore acc))
  (equal x 0))

(defun trfact-step-x (x acc)
  (declare (ignore acc))
  (1- x))

(defun trfact-step-acc (x acc)
  (* x acc))

(defpm trfact-test trfact-step trfact-measure trfact-terminates trfact-theory
  :formals (x acc))

; The next definition is kind of extraneous, but shows a definition using the
; wrappers like trfact-step-x.
(defun trfact-simple (x acc)
  (declare (xargs :measure (trfact-measure x acc)
                  :hints (("Goal"
                           :in-theory
                           (union-theories (theory 'trfact-theory)
                                           (theory 'minimal-theory))))))
  (if (trfact-terminates x acc)
      (if (trfact-test x acc)
          acc
        (trfact-simple (trfact-step-x x acc)
                       (trfact-step-acc x acc)))
    acc))

(defun trfact (x acc)
  (declare (xargs :measure (trfact-measure x acc)
                  :hints (("Goal"
                           :use (trfact-measure-decreases
                                 trfact-measure-type)
                           :in-theory
                           (union-theories '(trfact-test
                                             trfact-step-x
                                             trfact-step-acc)
                                           (theory 'ground-zero))))))
  (if (trfact-terminates x acc)
      (if (equal x 0)
          acc
        (trfact (1- x) (* x acc)))
    acc))

; See just below for what the following actually proves.
(defthm-domain trfact-terminates-holds-on-natp
  (implies (natp x)
           (trfact-terminates x acc))
  :test trfact-test
  :step trfact-step
  :measure (nfix x))

(encapsulate ; record what was proved by preceding event
 ()
 (set-enforce-redundancy t)
 (defthm trfact-terminates-holds-on-natp
   (implies (natp x)
            (trfact-terminates x acc))))

; Below is a manual proof similar to what is produced by the above
; defthm-domain.
 #||

 ;; Start proof of natp-implies-trfact-terminates.

 (defun natp-implies-trfact-terminates-fn (x acc)
   (implies (natp x)
            (trfact-terminates x acc)))

 ; It might be tempting to try to use the induction scheme from trfact-simple to
 ; do our termination proof.  But a base case for that induction is the case
 ; (not (trfact-terminates x acc)), which is useless in proving
 ; (trfact-terminates x acc), even assuming (natp x).  Actually, it's not
 ; surprising that we need to introduce an induction hint -- a real measure has
 ; to come into play somehow!
 (defun natp-implies-trfact-terminates-induction-hint (x acc)
   (declare (xargs :measure (nfix x)
                   :hints (("Goal" :in-theory (enable trfact-test
                                                      trfact-step-x
                                                      trfact-step-acc)))))
   (if (or (not (natp x))
           (trfact-test x acc))
       x
     (natp-implies-trfact-terminates-induction-hint (trfact-step-x x acc)
                                                    (trfact-step-acc x acc))))

 (defthm natp-implies-trfact-terminates-base
   (implies (or (not (natp x))
                (trfact-test x acc))
            (natp-implies-trfact-terminates-fn x acc))
   :hints (("Goal"
            :in-theory (union-theories '(natp-implies-trfact-terminates-fn
                                         trfact-terminates-base)
                                       (theory 'minimal-theory)))))

 (defthm trfact-step-preserves-natp
   (implies (and (natp x)
                 (not (trfact-test x acc)))
            (natp (trfact-step-x x acc))))

 (defthm natp-implies-trfact-terminates-step
   (implies (and (not (trfact-test x acc))
                 (natp-implies-trfact-terminates-fn (trfact-step-x x acc)
                                                    (trfact-step-acc x acc)))
            (natp-implies-trfact-terminates-fn x acc))
   :hints (("Goal"
            :in-theory (union-theories '(trfact-step-preserves-natp
                                         natp-implies-trfact-terminates-fn
                                         trfact-terminates-step)
                                       (theory 'minimal-theory)))))

 (defthm natp-implies-trfact-terminates-main
   (natp-implies-trfact-terminates-fn x acc)
   :hints (("Goal"
            :induct (natp-implies-trfact-terminates-induction-hint x acc)
            :in-theory (union-theories
                        '(natp-implies-trfact-terminates-induction-hint
                          natp-implies-trfact-terminates-base
                          natp-implies-trfact-terminates-step)
                        (theory 'minimal-theory)))))

 (defthm natp-implies-trfact-terminates
   (implies (natp x)
            (trfact-terminates x acc))
   :hints (("Goal"
            :use natp-implies-trfact-terminates-main
            :in-theory (union-theories '(natp-implies-trfact-terminates-fn)
                                       (theory 'minimal-theory)))))
 ||#
))

; Third example: very similar to the second, but not tail recursive

(local (my-test test3

(defund fact-test (x)
  (equal x 0))

(defund fact-step (x)
  (1- x))

(defpm fact-test fact-step fact-measure fact-terminates fact-theory)

; Unlike the defun for trfact, this time we use the wrappers fact-test and
; fact-step, which avoids the :use hint in that previous defun in favor of
; enabling rules in the theory (in this case, fact-theory).
(defun fact (x)
  (declare (xargs :measure (fact-measure x)
                  :hints (("Goal"
                           :in-theory
                           (union-theories (theory 'fact-theory)
                                           (theory 'minimal-theory))))))
  (if (fact-terminates x)
      (if (fact-test x)
          1
        (* x (fact (fact-step x))))
    1))

(defthm-domain fact-terminates-holds-on-natp
  (implies (natp x)
           (fact-terminates x))
; :test fact-test
; :step fact-step
  :measure (nfix x))

(encapsulate ; record what was proved by preceding event
 ()
 (set-enforce-redundancy t)
 (defthm fact-terminates-holds-on-natp
   (implies (natp x)
            (fact-terminates x))))

; Test of :root -- should be redundant.
(defthm-domain fact-terminates-holds-on-natp
  (implies (natp x)
           (fact-terminates x))
  :root fact
  :measure (nfix x))

; Definition rule:
(defthm fact-def
  (implies (force (natp x)) ; The force is optional.
           (equal (fact x)
                  (if (fact-test x)
                      1
                    (* x (fact (fact-step x))))))
; Hints are optional:
  :hints (("Goal" :in-theory (union-theories
                              '(fact fact-terminates-holds-on-natp)
                              (theory 'minimal-theory))))
  :rule-classes :definition)

; Below is a manual proof similar to what is produced by the above
; defthm-domain.
 #||
 (defun natp-implies-fact-terminates-fn (x)
   (implies (natp x)
            (fact-terminates x)))

 (defun natp-implies-fact-terminates-induction-hint (x)
   (declare (xargs :measure (nfix x)
                   :hints (("Goal" :in-theory (enable fact-test fact-step)))))
   (if (or (not (natp x))
           (fact-test x))
       x
     (natp-implies-fact-terminates-induction-hint (fact-step x))))

 (defthm natp-implies-fact-terminates-base
   (implies (or (not (natp x))
                (fact-test x))
            (natp-implies-fact-terminates-fn x))
   :hints (("Goal" :use fact-terminates-base
            :in-theory (e/d (fact-test)
                            (fact-terminates-base)))))

 (defthm natp-implies-fact-terminates-step
   (implies (and (and (natp x)
                      (not (fact-test x)))
                 (natp-implies-fact-terminates-fn (fact-step x)))
            (natp-implies-fact-terminates-fn x))
   :hints (("Goal" :use fact-terminates-step
            :in-theory (e/d (fact-test fact-step)
                            (fact-terminates-step)))))

 (defthm natp-implies-fact-terminates-main
   (natp-implies-fact-terminates-fn x)
   :hints (("Goal"
            :induct (natp-implies-fact-terminates-induction-hint x)
            :in-theory (union-theories
                        '(natp-implies-fact-terminates-induction-hint
                          natp-implies-fact-terminates-base
                          natp-implies-fact-terminates-step)
                        (theory 'minimal-theory)))))

 (defthm natp-implies-fact-terminates
   (implies (natp x)
            (fact-terminates x))
   :hints (("Goal"
            :use natp-implies-fact-terminates-main
            :in-theory (union-theories '(natp-implies-fact-terminates-fn)
                                       (theory 'minimal-theory)))))
 ||#
))

; Here we take advantage of the work above to define an executable function
; that terminates on a given domain.  Of course, this would be easy to do
; directly; but perhaps it's of interest to see how the framework above might
; be of use.  Eventually we might want to automate the creation of this
; definition after suitable defpm and defthm-domain events have been admitted.
; Compare with the definition of fact, above.

(local (my-test test4

(defund fact2-test (x)
  (declare (xargs :guard t))
  (equal x 0))

(defund fact2-step (x)
  (declare (xargs :guard (natp x)))
  (1- x))

(defpm fact2-test fact2-step fact2-measure fact2-terminates fact2-theory)

(defthm-domain fact2-terminates-holds-on-natp
  (implies (natp x)
           (fact2-terminates x))
  :root fact2
  :measure (nfix x))

(defthmd natp-fact2-step
  (implies (and (not (fact2-test x))
                (natp x))
           (natp (fact2-step x)))
  :hints (("Goal" :in-theory (enable fact2-test fact2-step))))

(defun fact2 (x)
  (declare (xargs :guard (natp x)
                  :measure (fact2-measure x)
                  :guard-hints (("Goal"
                                 :in-theory
                                 (union-theories
                                  '(natp-fact2-step fact2-terminates-holds-on-natp)
                                  (union-theories (theory 'fact2-theory)
                                                  (theory 'minimal-theory)))))
                  :hints (("Goal"
                           :in-theory
                           (union-theories (theory 'fact2-theory)
                                           (theory 'minimal-theory))))))
  (mbe :logic
       (if (fact2-terminates x)
           (if (fact2-test x)
               1
             (* x (fact2 (fact2-step x))))
         1)
       :exec
       (if (fact2-test x)
           1
         (* x (fact2 (fact2-step x))))))
))
