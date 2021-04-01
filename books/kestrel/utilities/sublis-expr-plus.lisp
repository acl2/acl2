; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(local (include-book "kestrel/std/system/all-vars" :dir :system))

(defxdoc sublis-expr+
  :parents (kestrel-utilities)
  :short "Replace @(see term)s by variables, even inside @(see lambda) bodies"
  :long "<p>WARNING: This utility takes an alist that maps terms to variables.
 In that sense it is more restrictive than the corresponding utility that is
 built into ACL2, @('sublis-expr').  This restriction to variables could
 probably be lifted with a little effort (but was acceptable for its initial
 purpose).</p>

 @({
 General Form:
 (sublis-expr+ alist term)
 })

 <p>where @('alist') is an alist that maps terms to variables and @('term') is
 a (translated) @(tsee term).  The value is a term that results from replacing
 occurrences of terms in the domain of @('alist') by the corresponding
 variables.  Notably, this replacement can take place in bodies of @(see
 lambda)s, with attention to avoiding so-called variable capture (as discused
 further below).</p>

 <p>Consider the following example, which for readability is expressed in terms
 of untranslated terms.</p>

 @({
 alist:
 (((nth '0 (binary-append a b)) . x)
  ((nth '1 (binary-append a b)) . y))

 term (untranslated):
 (let ((u (cons (nth 0 (append a b))
                (nth 1 (append a b)))))
   (cons (nth 0 (append a b)) u))

 result (untranslated):
 (let ((u (cons x y)))
   (cons x u))
 })

 <p>Note that substitution occurred even inside the body of the input @('let')
 expression, which corresponds to the body of the input @('lambda') expression
 below.  Here is an actual call, with translated terms, that corresponds to the
 description above.</p>

 @({
 ACL2 !>(sublis-expr+ '(((nth '0 (binary-append a b)) . x)
                        ((nth '1 (binary-append a b)) . y))
                      '((lambda (u b a)
                          (cons (nth '0 (binary-append a b)) u))
                        (cons (nth '0 (binary-append a b))
                              (nth '1 (binary-append a b)))
                        b a))
 ((LAMBDA (U B A) (CONS X U))
  (CONS X Y)
  B A)
 ACL2 !>
 })

 <p>Remark.  Notice that a simpler term that is equivalent to the one above is
 as follows.</p>

 @({
 ((LAMBDA (U) (CONS X U))
  (CONS X Y))
 })

 <p>Indeed, they both untranslate to: @('(let ((u (cons x y))) (cons x u))').
 An enhancement to consider would be to drop formals that are bound to
 themselves, like @('A') and @('B') in the example above.  End of Remark.</p>

 <p>Finally, we note that variable capture is avoided, as illustrated by the
 following example.  Consider the (untranslated) input @('(let ((u (cons x
 y))) (cons x u))'), and suppose that we try to replace @('x') with a
 ``global'' value of @('u').  Then it would be an error to replace @('x') by
 @('u') in the body of the @('let'), @('(cons x u)'), because the new
 occurrence of @('u') would reference (be ``captured by'') the bound variable
 @('u'), not the ``global'' value of @('u').  Let's see what actually
 happens.</p>

 @({
 ACL2 !>(sublis-expr+ '((x . u))
                       '((lambda (u x) (cons x u)) (cons x y) x))
 ((LAMBDA (U X) (CONS X U)) (CONS U Y) U)
 ACL2 !>(untranslate ; input
         '((lambda (u x) (cons x u)) (cons x y) x)
         nil (w state))
 (LET ((U (CONS X Y))) (CONS X U))
 ACL2 !>(untranslate ; result
         '((LAMBDA (U X) (CONS X U)) (CONS U Y) U)
         nil (w state))
 (LET ((U (CONS U Y)) (X U)) (CONS X U))
 ACL2 !>
 })

 <p>It would also be an error to replace @('u') by @('x') in that same body of
 the @('let'), @('(cons x u)'), because that new occurrence of @('u') would
 reference the bound variable @('u'), not the ``global'' value of @('u').  The
 input term is returned unchanged in this case.</p>

 @({
 ACL2 !>(sublis-expr+ '((u . x))
                      '((lambda (u x) (cons x u)) (cons x y) x))
 ((LAMBDA (U X) (CONS X U)) (CONS X Y) X)
 ACL2 !>(untranslate ; new result
         '((LAMBDA (U X) (CONS X U)) (CONS X Y) X)
         nil (w state))
 (LET ((U (CONS X Y))) (CONS X U))
 ACL2 !>
 })

 <p>It would also have been correct to rename the bound variable, to produce the
 result @('((LAMBDA (U1 X) (CONS X U1)) (CONS X Y) X)'), which untranslates to
 @('(let ((u1 (cons x y))) (cons x u1))').  Perhaps a future enhancement of
 this utility will do such renaming.</p>")

(defun sublis-expr+-restrict-alist-aux (vars formals/actuals)
  (declare (xargs :guard (and (symbol-listp vars)
                              (symbol-alistp formals/actuals))))
  (cond ((endp vars) t)
        (t (let* ((var (car vars))
                  (formal-var-pair (assoc-eq var formals/actuals)))
             (and (or (null formal-var-pair)
                      (eq (cdr formal-var-pair) var))
                  (sublis-expr+-restrict-alist-aux (cdr vars)
                                                   formals/actuals))))))

(encapsulate
  ()

  (defun sublis-expr+-restrict-alist (alist formals/actuals)

; We keep only those pairs (expr . var) from alist for which neither var nor
; any variable free in expr is bound by the given formals, with one exception:
; the variable is bound to itself in formals/actuals.

    (declare (xargs :guard (and (r-symbol-alistp alist)
                                (pseudo-term-listp (strip-cars alist))
                                (symbol-alistp formals/actuals))))
    (cond ((endp alist) nil)
          (t (let* ((pair (car alist))
                    (expr (car pair))
                    (var (cdr pair))
                    (formal-var-pair (assoc-eq var formals/actuals)))
               (cond ((and (or (null formal-var-pair)
                               (eq (cdr formal-var-pair) var))
                           (sublis-expr+-restrict-alist-aux (all-vars expr)
                                                            formals/actuals))
                      (cons (car alist)
                            (sublis-expr+-restrict-alist (cdr alist)
                                                         formals/actuals)))
                     (t (sublis-expr+-restrict-alist (cdr alist)
                                                     formals/actuals))))))))

(verify-termination make-lambda-term) ; and guards

(mutual-recursion

(defun sublis-expr+ (alist term)
  (declare (xargs :guard (and (r-symbol-alistp alist)
                              (pseudo-term-listp (strip-cars alist))
                              (pseudo-termp term))
                  :verify-guards nil))
  (let ((temp (assoc-equal term alist)))
    (cond (temp (cdr temp))
          ((variablep term) term)
          ((fquotep term) term)
          ((flambdap (ffn-symb term))
           (let* ((lam (ffn-symb term))
                  (formals (lambda-formals lam))
                  (body (lambda-body lam))
                  (actuals (fargs term))
                  (alist+ (sublis-expr+-restrict-alist
                           alist
                           (pairlis$ formals actuals))))
             (make-lambda-term formals
                               (sublis-expr+-lst alist actuals)
                               (sublis-expr+ alist+ body))))
          (t (cons-term (ffn-symb term)
                        (sublis-expr+-lst alist (fargs term)))))))

(defun sublis-expr+-lst (alist lst)
  (declare (xargs :guard (and (r-symbol-alistp alist)
                              (pseudo-term-listp (strip-cars alist))
                              (pseudo-term-listp lst))))
  (cond ((endp lst) nil)
        (t (cons (sublis-expr+ alist (car lst))
                 (sublis-expr+-lst alist (cdr lst))))))
)

(local
 (progn

   (defthm symbol-alistp-pairlis$
     (implies (symbol-listp syms)
              (symbol-alistp (pairlis$ syms lst))))

   (defthm r-symbol-alistp-forward-to-alistp
     (implies (r-symbol-alistp alist)
              (alistp alist))
; Make this a :forward-chaining rule to take advantage of the :forward-chaining
; rule, consp-assoc-equal.
     :rule-classes :forward-chaining)

   (defthm sublis-expr+-restrict-alist-preserves-pseudo-term-listp-strip-cars
     (implies
      (pseudo-term-listp (strip-cars alist))
      (pseudo-term-listp
       (strip-cars (sublis-expr+-restrict-alist alist x)))))

   (defthm sublis-expr+-restrict-alist-preserves-r-symbol-alistp
     (implies
      (r-symbol-alistp alist)
      (r-symbol-alistp (sublis-expr+-restrict-alist alist x))))

   (include-book "tools/flag" :dir :system)

   (make-flag flag-sublis-expr+
              sublis-expr+ ; any member of the clique
              ;; optional arguments:
              :flag-mapping ((sublis-expr+     term)
                             (sublis-expr+-lst list))
              :defthm-macro-name defthm-sublis-expr+
              :flag-var flag)

   (defthm r-symbol-alistp-implies-pseudo-termp-cdr-assoc
     (implies (r-symbol-alistp alist)
              (pseudo-termp (cdr (assoc-equal term alist)))))

   (defthm len-sublis-expr+-lst
     (equal (len (sublis-expr+-lst alist x))
            (len x)))

   (defthm len-append
     (equal (len (append x y))
            (+ (len x) (len y))))

   (defthm pseudo-term-listp-append
     (implies (pseudo-term-listp x)
              (equal (pseudo-term-listp (append x y))
                     (pseudo-term-listp y))))

   (defthm pseudo-term-listp-set-difference-equal
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (set-difference-equal x y))))

   (defthm symbol-listp-implies-pseudo-term-listp
     (implies (symbol-listp x)
              (pseudo-term-listp x)))

   (defthm symbol-listp-append
     (implies (symbol-listp x)
              (equal (symbol-listp (append x y))
                     (symbol-listp y))))

   (defthm symbol-listp-set-difference-equal
     (implies (symbol-listp x)
              (symbol-listp (set-difference-equal x y))))

   (defthm-sublis-expr+
     (defthm pseudo-termp-sublis-expr+
       (implies (and (pseudo-termp term)
                     (r-symbol-alistp alist))
                (pseudo-termp (sublis-expr+ alist term)))
       :flag term)
     (defthm pseudo-term-listp-sublis-expr+-lst
       (implies (and (pseudo-term-listp lst)
                     (r-symbol-alistp alist))
                (pseudo-term-listp (sublis-expr+-lst alist lst)))
       :flag list))))

(verify-guards sublis-expr+)
