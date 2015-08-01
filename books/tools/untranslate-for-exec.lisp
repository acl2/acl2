; Untranslate for Execution
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "std/util/defines" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/top" :dir :system))

(defxdoc untranslate-for-execution
  :parents (macros)
  :short "Attempt to do a kind of untranslation of a @(see pseudo-termp) in
order to restore any @(see mv-let) and @(see mv) forms, ideally so that the
term can be executed."

  :long "<p>When @(see term)s are translated into pseudo-terms, information
about their @(see mv) and @(see stobj) nature can be lost.  For instance,
suppose we start with a simple definition, @('f'):</p>

@({
     (defun f (a b) (mv a b))
})

<p>Since @(see mv) is logically just @(see list), the logical definition of
@('f') ends up being @('(list a b)').  Suppose we want to use this logical
definition to derive some new function, @('g'),</p>

@({
     (defun g (a b) (list a b))
})

<p>Now, although @('f') and @('g') are logically identical, they are
practically incompatible since @('f') returns two values and @('g') only
returns one.  This kind of mismatch can sometimes cause problems when you are
writing code that modifies existing ACL2 functions.</p>

<p>The @('untranslate-for-execution') tool tries to allow you to recover
something like the true original definition.  For example,</p>

@({
     (untranslate-for-execution

})



@({
    (list (+ a b) (+ the @(see normalize)d definition of 

<p>then translating this term yields</p>

@({
 (defun f ()
    ((LAMBDA (MV)
             ((LAMBDA (A B) (BINARY-+ A B))
              (MV-NTH '0 MV)
              (MV-NTH '1 MV)))
     (CONS '1 (CONS '2 'NIL))))
})

<p>but this translated term cannot be executed at the top-level ACL2 loop and
it cannot be put inside of function definitions, 

and this term cannot be executed because it includes calls of 



(translate '(mv-let (a b) (mv '1 '2) (+ a b)) t t t 'foo (w state) state)
           
           


  



untranslate a pseudo-termp in a format that will allow it
to be executed.")



(local (defthm pseudo-term-listp-of-append
         (equal (pseudo-term-listp (append x y))
                (and (pseudo-term-listp (list-fix x))
                     (pseudo-term-listp y)))
         :hints(("Goal" :induct (len x)))))

(local (defthm pseudo-term-listp-of-rev
         (equal (pseudo-term-listp (rev x))
                (pseudo-term-listp (list-fix x)))
         :hints(("Goal" :induct (len x)))))

(local (defthm true-listp-when-pseudo-term-listp
         (implies (pseudo-term-listp x)
                  (true-listp x))
         :rule-classes :compound-recognizer))


;; Goal: rewrite a pseudo-termp so that it can call functions with multiple
;; values.  Some examples to help understand the goal...

#||

    ;; Helpers for these examples

    (defun f (x) x)
    (defun g (x) x)
    (defun h (x y) (list x y))
    (defun mv2 (x y) (mv x y))


    ;; Basic case 1: the multiply valued expression is an explicit MV.  It
    ;; gets translated into a cons nest.  We'll need to rewrite these cons
    ;; nests into explicit MVs.

    (trans '(mv-let (x y) (mv (f 1) (f 2)) (h x y)))
      -->
    ((LAMBDA (MV)
             ((LAMBDA (X Y) (H X Y))
              (MV-NTH '0 MV)
              (MV-NTH '1 MV)))
     (CONS (F '1) (CONS (F '2) 'NIL)))


    ;; Basic case 2: the multiply valued expression is just a call of an
    ;; MV-returning function.  It just stays as a call of that function.

    (trans '(mv-let (x y) (mv2 (f 1) (f 2)) (h x y)))
      -->
    ((LAMBDA (MV)
             ((LAMBDA (X Y) (H X Y))
              (MV-NTH '0 MV)
              (MV-NTH '1 MV)))
     (MV2 (F '1) (F '2)))


    ;; Tricky case 1: an IF with different branches that return
    ;; multiple values.  We'll need to be able to descend through
    ;; an IF and rewrite the conses nests at the tips.

    (trans '(mv-let (x y) (if condition (mv a b) (mv2 c d)) (h x y)))
      -->
    ((LAMBDA (MV)
             ((LAMBDA (X Y) (H X Y))
              (MV-NTH '0 MV)
              (MV-NTH '1 MV)))
     (IF CONDITION
         (CONS A (CONS B 'NIL))
       (MV2 C D)))


    ;; Tricky case 2: a LAMBDA in the body that returns multiple
    ;; values.  We'll have to be able to descend into LAMBDA terms
    ;; to be able to handle this.

    (trans '(mv-let (a b c)
                    ((lambda (x) (mv x x x)) 1)
                    (+ a b c)))
      -->
    ((LAMBDA (MV)
             ((LAMBDA (A B C)
                      (BINARY-+ A (BINARY-+ B C)))
              (MV-NTH '0 MV)
              (MV-NTH '1 MV)
              (MV-NTH '2 MV)))
     ((LAMBDA (X)
              (CONS X (CONS X (CONS X 'NIL))))
      '1))

||#


;; Some building blocks...


;; A matcher for ((MV-NTH '0 MV) (MV-NTH '1 MV) ...):

(define match-ascending-mv-nth-list-aux
  ((x   pseudo-term-listp "Possibly a list of MV-NTHs.")
   (n   natp              "Current index we expect to match, e.g., starts with 0.")
   (rhs pseudo-termp      "RHS we expect to match, e.g., 'mv."))
  :returns (matchp booleanp :rule-classes :type-prescription)
  (b* (((when (atom x))
        t)
       (term1 (car x))
       ((unless (and (equal (len term1) 3)
                     (equal (first term1) 'mv-nth)
                     (equal (second term1) (list 'quote n))
                     (equal (third term1) rhs)))
        nil))
    (match-ascending-mv-nth-list-aux (cdr x) (+ n 1) rhs)))

(define match-ascending-mv-nth-list
  ((x   pseudo-term-listp "Possibly a list of MV-NTHs.")
   (rhs pseudo-termp      "RHS we expect to match."))
  :returns (matchp booleanp :rule-classes :type-prescription)
  (match-ascending-mv-nth-list-aux x 0 rhs))

;; (match-ascending-mv-nth-list '((MV-NTH '0 MV) (MV-NTH '1 MV)) 'mv)
;;   --> T, good, this is what we want to match
;; (match-ascending-mv-nth-list '((MV-NTH '0 MV) (MV-NTH '2 MV)) 'mv)
;;   --> NIL because the indices are wrong


;; A matcher for (CONS (F '1) (CONS (F '2) 'NIL)):

(define match-cons-nest-aux ((x   pseudo-termp)
                             (acc pseudo-term-listp))
  :parents (match-cons-nest)
  :returns (mv (matchp booleanp :rule-classes :type-prescription)
               (acc    pseudo-term-listp :hyp :guard))
  (cond ((atom x)
         (mv nil acc))
        ((equal x ''nil)
         (mv t acc))
        ((and (eq (car x) 'cons)
              (equal (length x) 3))
         (match-cons-nest-aux (third x) (cons (second x) acc)))
        (t
         (mv nil acc)))
  ///
  (defthm true-listp-of-match-cons-nest-aux
    (implies (true-listp acc)
             (true-listp (mv-nth 1 (match-cons-nest-aux x acc))))))

(define match-cons-nest ((x pseudo-termp))
  :short "Matches @('(cons x1 (cons ... (cons xn 'nil)))')."
  :returns (mv (matchp booleanp :rule-classes :type-prescription)
               (args   pseudo-term-listp :hyp :guard))
  (if (and (consp x)
           (eq (car x) 'cons))
      (mv-let (matchp acc)
        (match-cons-nest-aux x nil)
        (mv matchp (rev acc)))
    (mv nil nil)))

;; (match-cons-nest '(CONS (F '1) (CONS (F '2) 'NIL)))
;;   --> (mv t (list (f '1) (f '2)))
;; (match-cons-nest '(binary-+ (F '1) (CONS (F '2) 'NIL)))
;;   --> (mv nil nil)


(define patmatch-mv-style-lambda ((x pseudo-termp "Should be a lambda."))
  :guard (and (consp x) (consp (car x)))
  :returns (mv (matchp booleanp
                       :rule-classes :type-prescription
                       "True if this looks like an MV-LET lambda, NIL
                        if it looks like some other kind of lambda.")
               (vars   "On match, the variables bound in this mv-let."
                       (implies (pseudo-termp x)
                                (symbol-listp vars)))
               (expr   "On match, the multiply valued expression to bind
                        to these variables.  MVs not yet reincarnated."
                       (implies (and match
                                     (pseudo-termp x))
                                (pseudo-termp expr)))
               (body   "On match, the inner body of this mv-let."
                       (implies (and matchp
                                     (pseudo-termp x))
                                (pseudo-termp body))))
  ;; The goal here is to match something like this:
  ;;
  ;; ((LAMBDA (MV)             ;; Always seems to be named MV
  ;;          ((LAMBDA (X Y)   ;; MV-LET variables
  ;;                   (H X Y) ;; Body of the MV-LET, where these vars are bound
  ;;                   )
  ;;           ;; Boilerplate mv-nth nonsense
  ;;           (MV-NTH '0 MV)
  ;;           (MV-NTH '1 MV)))
  ;;  ;; The multiple-valued expression to bind to these variables.
  ;;  (CONS (F '1) (CONS (F '2) 'NIL)))

  (b* (((list & top-formals top-body) (car x))

       ;; Deconstruct the top-level/outer lambda.
       ((unless (and (equal top-formals '(mv))
                     (consp top-body)
                     (consp (car top-body))))
        (mv nil nil nil nil))

       ;; TOP-BODY is itself a lambda, so deconstruct it.
       ((list & inner-formals inner-body) (car top-body))
       (inner-args (cdr top-body))
       ((unless (match-ascending-mv-nth-list inner-args 'mv))
        ;; Inner args don't look like (mv-nth 0 mv) ..., so this doesn't
        ;; seem like an MV-LET lambda.
        (mv nil nil nil nil)))

    (mv t
        inner-formals
        (second x)
        inner-body))
  ///
  (defret acl2-count-of-patmatch-mv-style-lambda-new-body
    (implies matchp
             (< (acl2-count body)
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm horrible-awful-hack
           ;; Consider a term like (MV-NTH (X Y) (MV A B) (binary-+ X Y)).
           ;; Is this a pseudo-termp?
           ;;
           ;; Well, yes, but sort of only by accident: the variable list
           ;; (X Y) happens to look like a function call, even though it
           ;; really isn't.
           ;;
           ;; We probably shouldn't be exploiting this, but if we don't do
           ;; something like this, we don't have any good predicate laying around
           ;; to explain what kind of a term we're creating, and that's a yak we
           ;; probably don't want to try to shave yet...
           (implies (and (symbol-listp x)
                         (not (equal (car x) 'quote)))
                    (pseudo-termp x))))

  (defret pseudo-termp-of-patmatch-mv-style-lambda-mv-vars
    ;; Awful exploitation of pseudo-termp...
    (b* (((mv matchp vars ?expr ?body) (patmatch-mv-style-lambda x)))
      (implies (and matchp
                    (pseudo-termp x)
                    (not (equal (car vars) 'quote)))
               (pseudo-termp vars)))))


;; (patmatch-mv-style-lambda '((LAMBDA (MV)
;;                                     ((LAMBDA (X Y) (H X Y))
;;                                      (MV-NTH '0 MV)
;;                                      (MV-NTH '1 MV)))
;;                             (CONS (F '1) (CONS (F '2) 'NIL))))
;; --> (T (X Y)
;;        (CONS (F '1) (CONS (F '2) 'NIL))
;;        (H X Y))

(define convert-subexpression-to-mv
  :short "Rewrite an expression that occurs a multiply valued context to make
          its multiple returns explicit."
  ((n     natp         "Number of return values this expression has.")
   (x     pseudo-termp "The expression to rewrite.")
   (world plist-worldp "World, for return-value checking."))
  :guard (<= 2 n)
  :returns (mv (errmsg "NIL on success, or an error @(see msg) on failure.")
               (new-x pseudo-termp :hyp (pseudo-termp x)))

  (b* (((when (atom x))
        ;; Lone variable where expecting a multiply valued form.
        (mv (msg "Expected ~x0 return values, found ~x1." n x)
            x))
       ((when (fquotep x))
        ;; Lone quoted constant where expecting a multiply valued form.
        (mv (msg "Expected ~x0 return values, found ~x1." n x)
            x))
       (fn   (first x))
       (args (rest x))
       ((when (consp fn))
        ;; Lambda expression -- try to convert its body to return MVs.
        (b* (((list & formals body) (first x))
             ((mv err body) (convert-subexpression-to-mv n body world))
             ((when err)
              (mv err x))
             (new-x (cons (list 'lambda formals body) (cdr x))))
          (mv nil new-x)))
       ((when (eq fn 'if))
        ;; If expression -- try to convert its then/else branch to return MVs.
        (b* (((unless (equal (len args) 3))
              (mv (msg "Malformed IF: ~x0~%" x)
                  x))
             ((list test then else) args)
             ((mv err1 then) (convert-subexpression-to-mv n then world))
             ((when err1)
              (mv (msg "> In then branch of ~x0:~%~@1~%" test err1)
                  then))
             ((mv err2 else) (convert-subexpression-to-mv n else world))
             ((when err2)
              (mv (msg "> In else branch of ~x0:~%~@1~%" else err2)
                  else))
             (new-x (list 'if test then else)))
          (mv nil new-x)))
       ((when (eq fn 'cons))
        ;; Cons nest where expecting multiple values.  See if it has the right
        ;; arity and, if so, convert it into an MV.
        (b* (((mv matchp cons-args) (match-cons-nest x))
             ((unless matchp)
              (mv (msg "Expected ~x0 return values, found ~x1.~%" n x)
                  x))
             ((unless (equal (len cons-args) n))
              (mv (msg "Expected ~x0 return values, but found cons nest of size ~x1: ~x2~%"
                       n (len cons-args) x)
                  x))
             (new-x (cons 'mv cons-args)))
          (mv nil new-x)))
       ;; Else this should be an ordinary function.
       (stobjs-out (getprop fn 'acl2::stobjs-out :bad 'acl2::current-acl2-world world))
       ((when (eq stobjs-out :bad))
        (mv (msg "Don't know :stobjs-out of ~x0.~%" fn)
            x))
       ((unless (equal (len stobjs-out) n))
        (mv (msg "Expected ~x0 return values, but ~x1 returns ~x2 values."
                 n
                 (car x)
                 (len stobjs-out))
            x)))
    ;; Multiply valued function with the right arguments, nothing to do.
    (mv nil x)))


;; So that seems to be basically working:
;;
;; (convert-subexpression-to-mv 2
;;                              '(IF CONDITION
;;                                   (CONS A (CONS B 'NIL))
;;                                   (MV2 C D))
;;                              (w state))
;; -->
;; (mv nil (if condition (mv a b) (mv2 c d)))
;;
;; (convert-subexpression-to-mv 3
;;                              '((LAMBDA (X)
;;                                        (CONS X (CONS X (CONS X 'NIL))))
;;                                '1)
;;                              (w state))
;;  -->
;; (mv nil ((lambda (x) (mv x x x)) '1))


;; So now we need to recursively look for these goofy MV style lambdas and try
;; to rewrite their bodies.




(defines reincarnate-mvs
  :short "Try to convert translated MV forms back into their MV-LET/MV form."

  (define reincarnate-mvs
    ((x     pseudo-termp "The term to try to untranslate.")
     (world plist-worldp "The world, needed for stobjs-out lookups."))
    :returns (mv (errmsg "NIL on success or an error @(see msg) on failure.")
                 (new-x  "New version of @('x') with MVs restored."
                         pseudo-termp :hyp (pseudo-termp x)))
    :guard-debug t
    (b* (((when (atom x))
          ;; Variable, no way this has any MVs, totally fine, nothing to do.
          (mv nil x))
         ((when (fquotep x))
          ;; Constant, no way this has any MVs, totally fine, nothing to do.
          (mv nil x))
         ((cons fn args) x)
         ((when (symbolp fn))
          ;; We need to rewrite the arguments because, for instance, someone
          ;; can write an MV-LET within an argument to a function, e.g., say
          ;;   (myfunction (mv-let (x y) (produce-xy ...) (+ x y)) ...)
          (b* (((mv err args) (reincarnate-mvs-list args world))
               ((when err)
                (mv err x))
               (new-x (cons fn args)))
            (mv nil new-x)))
         ;; Else, a lambda, so it may be a translated MV-LET or it might just
         ;; be some other random lambda, e.g., from a regular LET binding.  Try
         ;; to figure out which case we're in.
         ((mv matchp mv-vars mv-expr mv-body)
          (patmatch-mv-style-lambda x))
         ((unless matchp)
          ;; Even though it's not an MV-LET, we still need to rewrite the
          ;; arguments and body because they may contain MV-LETs.
          (b* (((list & formals body) fn)
               ((mv err args) (reincarnate-mvs-list args world))
               ((when err)
                (mv err x))
               ((mv err body) (reincarnate-mvs body world))
               ((when err)
                (mv err x))
               (new-x (cons (list 'lambda formals body) args)))
            (mv nil new-x)))
         ;; At this point, we think that X is equivalent to:
         ;;   (mv-let mv-vars mv-expr mv-body).
         ;; However there are some things wrong with this.
         ;;  (1) mv-expr has not yet been rewritten, so any explicit
         ;;      (mv x y z) calls in it may still look like cons nests.
         (num-vars (len mv-vars))
         ((unless (<= 2 num-vars))
          (mv (msg "MV-LET style lambda has only one variable? ~x0~%" x)
              x))
         ((when (eq (car mv-vars) 'quote))
          ;; See horrible-awful-hack above; this could ruin pseudo-termp...
          (mv (msg "MV-LET style lambda has a variable named quote? ~x0~%" x)
              x))
         ((mv err mv-expr)
          (convert-subexpression-to-mv num-vars mv-expr world))
         ((when err)
          (mv err x))
         ;;  (2) the mv-body may contain further mv-lets that also
         ;;      need to get rewritten.
         ((mv err mv-body) (reincarnate-mvs mv-body world))
         ((when err)
          (mv err x))
         (new-expr (list 'mv-nth mv-vars mv-expr mv-body)))
    (mv nil new-expr)))

  (define reincarnate-mvs-list
    ((x     pseudo-term-listp "The terms to try to untranslate.")
     (world plist-worldp      "The world, needed for stobjs-out lookups."))
    :returns (mv (errmsg "NIL on success or an error @(see msg) on failure.")
                 (new-x  "New version of @('x') with MVs restored."
                         (and (implies (pseudo-term-listp x)
                                       (pseudo-term-listp new-x))
                              (equal (len new-x)
                                     (len x)))))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv err1 car) (reincarnate-mvs (car x) world))
         ((when err1)
          (mv err1 x))
         ((mv err2 cdr) (reincarnate-mvs-list (cdr x) world))
         ((when err2)
          (mv err2 x)))
      (mv nil (cons car cdr)))))

(define untranslate-for-execution
  ((x          pseudo-termp)
   (stobjs-out (and (symbol-listp stobjs-out)
                    (consp stobjs-out)))
   (world      plist-worldp))
  :returns (mv (errmsg "NIL on success or an error @(see msg) on failure.")
               (new-x  "New version of @('x'), with MVs restored."))
  (b* (((mv err x-fix1)
        (reincarnate-mvs x world))
       ((when err)
        (mv err x))
       ;; We could eventually make more sophisticated use of stobjs-out, but
       ;; for now we just use it to try to insert the right top-level MV
       ;; structure.
       (n (len stobjs-out))
       ((when (eql n 1))
        ;; Form just returns a single value, no need to MV'ify it.
        (mv nil x-fix1))
       ((mv err new-x)
        (convert-subexpression-to-mv n x-fix1 world))
       ((when err)
        (mv err x)))
    (mv nil new-x)))
