; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

#|

;; def::un : A stand-in for defun when the going gets rough.

;;   Tired of wasting time crafting cleaver measure functions or
;; adding silly count arguments just to guarantee termination, when
;; all you want to do is prove interesting properties about your
;; system of interest?

;;   Well, then, def::un is for you!

;;   def::un allows you to admit nearly arbitrary recursive function
;; definitions under the assumption that they terminate.  What you
;; end up with when it is all over:

;;   (fn args): The function you wanted to admit in the first place
;;   along with its very own "Improved Induction Scheme"!  It even
;;   does "The Right Thing" with definitions like:
;;
;;   (def::un foo (a x)
;;     (cons a
;;       (if (consp x) (foo a (cdr x)) nil)))

;;   (fn_terminates args): A predicate that allows you to assume that
;;   the function terminates on selected inputs.

;;   (fn_always_terminates): A constant function that allows you to
;;   assume termination for all inputs.

;;   (fn_measure args) : A measure function that can be used to
;;   admit other functions with similar recursive structure.

;;   How do you use it?  Just like defun:

(def::un mc91 (n)
  (if (> n 100) (- n 10)
    (mc91 (mc91 (+ n 11)))))

;;
;; Now you are ready to do proofs!  Here is a proof by induction, with
;; the help of our _terminates predicate.
;;
(defthm integerp-mc91
  (implies
   (and
    (integerp n)
    (mc91_terminates n))
   (integerp (mc91 n))))

;; Nicer still is the _always_terminates predicate .. kinda like
;; "ttags" for termination .. again with the proof by induction.

(defthm mc91-proof
  (implies
   (and
    (integerp n)
    (mc91_always_terminates))
   (equal (mc91 n)
          (if (< n 101) 91 (- n 10)))))

;; Now, unshackeled from the need to construct awkward termination
;; arguments or artificial function definitions with extra arguments,
;; go and do real proofs!

;; TODO:
;;
;; - Play well with :redundant -- DONE! via pseudo-translate
;;
;; - Make (fn args) and (fn_terminates args) executable.
;;
;; - stobj support (make intermediate functions non-executable)
;;
;; - multi-value support
;;
;; - Support for :measure argument (use enhanced induction body
;;   for the logical definition)
;;
;; - Integrate into "def::mutual" to provide support for
;;   mutual recursion.

|#
(in-package "ACL2")

(include-book "coi/syntax/syntax" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)
(include-book "compiler-proof")
(include-book "misc/eval" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/util/recursion-support" :dir :system)

(defun syn-not (x)
  (declare (type t x ))
  (cond
   ((not x) *t*)
   ((syn::truep x) nil)
   ((and (consp x)
         (consp (cdr x))
         (equal (car x) 'not))
    (cadr x))
   (t `(not ,x))))

(defun syn::conjoin-list (list)
  (declare (type t list))
  (if (consp list)
      (syn::conjoin (car list)
                    (syn::conjoin-list (cdr list)))
    *t*))

(defun syn::lazy-if (x y z)
  (declare (type t x y))
  (if (acl2::not x) z
    (if (syn::truep x) y
      `(if ,x ,y ,z))))

(defun syn::disjoin (x y)
  (declare (type t x y))
  (acl2::cond
   ((syn::truep y)
    y)
   ((syn::truep x)
    x)
   ((not x)
    y)
   ((not y)
    x)
   (acl2::t
    (syn::if x *t* y))))

(defun syn::or-fn (args)
  (declare (type t args))
  (acl2::if (acl2::consp args)
            `(syn::disjoin ,(acl2::car args) ,(syn::or-fn (acl2::cdr args)))
            acl2::nil))

(defmacro syn-or (&rest args)
  (syn::or-fn args))

;; Here we define the function that actually rips apart the body of a
;; function defintion and creates candidates for the stubbed out foo
;; functions.

(defun lambda-bod (expr)
  (caddr (car expr)))

(defun lambda-vars (expr)
  (cadr (car expr)))

(defun lambda-args (expr)
  (cdr expr))

(defun pair-assoc (key keys vals)
  (if (consp keys)
      (if (equal key (car keys)) (car vals)
        (pair-assoc key (cdr keys) (cdr vals)))
    nil))

#+joe
(skip-proofs
 (defun fn-dive (t1 n kstk vstk)
   (cond
    ((consp t1)
     (cond
      ((consp (car t1))
       (fn-dive (lambda-bod t1)
                (1+ n)
                (cons (lambda-vars t1) kstk)
                (cons (lambda-args t1) vstk)))
      (t
       (mv t t1 n kstk vstk))))
    ((consp vstk)
     (fn-dive (pair-assoc t1 (car kstk) (car vstk)) (1- n) (cdr kstk) (cdr vstk)))
    (t
     (mv nil t1 n kstk vstk))))
 )

#+joe
(defun un-dive (term n0 n kstk vstk)
  (if (or (consp vstk) (/= n0 n))
      (let ((term `((lambda ,(car kstk) ,term) ,@(car vstk))))
        (un-dive term n0 (1- n) (cdr kstk) (cdr vstk)))
    term))
;;
;;

(defun map-cond-over-cases (cond list)
  (if (consp list)
      (let ((entry (car list)))
        (cons (list (syn::and cond (car entry)) (cadr entry))
              (map-cond-over-cases cond (cdr list))))
    nil))

(defun map-lambda-over-cases (vars list args)
  (if (consp list)
      (let ((entry (car list)))
        (let ((case  (car entry))
              (value (cadr entry)))
          (let ((entry (if (syn::truep case)
                           (list *t* `((lambda ,vars ,value) ,@args))
                         (list `((lambda ,vars ,case) ,@args)
                               `((lambda ,vars ,value) ,@args)))))
            (cons entry (map-lambda-over-cases vars (cdr list) args)))))
    nil))

(defun insert-induction-condition (case value c2)
  (if (consp c2)
      (let ((entry (car c2)))
        (cons (list (syn::and case (car entry)) (syn::cons value (cadr entry)))
              (insert-induction-condition case value (cdr c2))))
    nil))

(defun merge-induction-conditions (c1 c2)
  (if (consp c1)
      (let ((entry (car c1)))
        (let ((case  (car entry))
              (value (cadr entry)))
          (let ((c2 (insert-induction-condition case value c2)))
            (merge-induction-conditions (cdr c1) c2))))
    c2))

(mutual-recursion

 (defun lift-induction-fn (fn induct term)
   (cond
    ((not (consp term)) nil)
    ((equal (car term) 'quote) nil)
    ((equal (car term) 'if)
     (let ((case (lift-induction-fn fn induct (cadr term)))
           (then (lift-induction-fn fn induct (caddr term)))
           (else (lift-induction-fn fn induct (cadddr term))))
       (append
        case
        (map-cond-over-cases (cadr term) then)
        (map-cond-over-cases (syn-not (cadr term)) else))))
    ((equal (car term) fn)
     (let ((conds (lift-induction-args fn induct (cdr term))))
       (if (consp conds)
           (insert-induction-condition *t* `(,induct ,@(cdr term)) conds)
         (list (list *t* `(,induct ,@(cdr term)))))))
    ((consp (car term))
     (let ((bcond (lift-induction-fn fn induct (lambda-bod term))))
       (let ((acond (lift-induction-args fn induct (cdr term))))
         (let ((bcond (map-lambda-over-cases (lambda-vars term) bcond (cdr term))))
           (append acond bcond)))))
    (t
     (lift-induction-args fn induct (cdr term)))))

 (defun lift-induction-args (fn induct args)
   (if (consp args)
       (let ((c1 (lift-induction-fn fn induct (car args))))
         (let ((c2 (lift-induction-args fn induct (cdr args))))
           (if (consp c2)
               (merge-induction-conditions c1 c2)
             c1)))
     nil))

 )

;;
;; Modified to return the base case condition as well.
;;

(mutual-recursion

 (defun lift-base-fn (fn term vars)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (consp term)) (mv (cdr (assoc term vars)) term))
    ((equal (car term) 'quote) (mv nil term))
    ((equal (car term) fn) (mv nil :ignore))
    ((equal (car term) 'if)
     (met ((bcase case) (lift-base-fn fn (cadr term) vars))
          (met ((bthen then) (lift-base-fn fn (caddr term) vars))
               (met ((belse else) (lift-base-fn fn (cadddr term) vars))
                    (cond
                     ((or (not bcase) (and (not bthen) (not belse)))
                      (mv nil :ignore))
                     ((and bthen belse)
                      (mv (syn::lazy-if case (syn::and bcase bthen) (syn::and bcase belse))
                          (syn::lazy-if case then else)))
                     (bthen
                      (mv (syn::and bcase case bthen) then))
                     (t ; belse
                      (mv (syn::and bcase (syn-not case) belse) else)))))))

    ((consp (car term))
     (met ((vars args) (lift-base-vars fn (lambda-vars term) (cdr term) vars))
          (met ((base body) (lift-base-fn fn (lambda-bod term) vars))
               (if base (mv `((lambda ,(strip-cars vars) ,base) ,@args) `((lambda ,(strip-cars vars) ,body) ,@args))
                 (mv nil :ignore)))))
    (t
     (met ((base args) (lift-base-args fn (cdr term) vars))
          (if base (mv base `(,(car term) ,@args))
            (mv nil :ignore))))))

 (defun lift-base-args (fn args vars)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((tbase term) (lift-base-fn fn (car args) vars))
            (met ((abase args) (lift-base-args fn (cdr args) vars))
                 (if (and tbase abase)
                     (mv (syn::and tbase abase) (cons term args))
                   (mv nil :ignore))))
     (mv t nil)))

 (defun lift-base-vars (fn vars args v0)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((tbase term) (lift-base-fn fn (car args) v0))
            (let ((var (car vars)))
              (met ((vars args) (lift-base-vars fn (cdr vars) (cdr args) v0))
                   (if tbase (mv (cons (cons var tbase) vars) (cons term args))
                     (mv vars args)))))
     (mv nil nil)))

 )

(defun pair-args-with-true (args)
  (if (consp args)
      (cons (cons (car args) *t*)
            (pair-args-with-true (cdr args)))
    nil))

;; The case returned by lift-base is actually the recursive case ..
;;
(defun lift-base (fn body args)
  (let ((vars (pair-args-with-true args)))
    (met ((case base) (lift-base-fn fn body vars))
      (let ((case (syn-not case)))
        (let ((case (or case *nil*)))
          (mv case base))))))

;; ===================================================================
;;
;; Support for lifting guarding 'ifs' into the trunk of recursive
;; bodies.
;;
;; ===================================================================

(defun lambda-conditional-args (fn cases)
  (if (consp cases)
      (let ((cond (car cases)))
        (let ((case (car cond))
              (args (cadr cond)))
          (cons `(,case (,fn ,@args))
                (lambda-conditional-args fn (cdr cases)))))
    nil))

(defun if-conditional-test (cases term1 term2)
  (if (consp cases)
      (let ((cond (car cases)))
        (let ((case (car cond))
              (test (cadr cond)))
          (cons `(,case (if ,test ,term1 ,term2))
                (if-conditional-test (cdr cases) term1 term2))))
    nil))

(defun if-cond-rec (case term cases)
  (if (consp cases)
      (let ((cond (car cases)))
        (let ((case2 (car cond))
              (term2 (cadr cond)))
          (syn::lazy-if case term (if-cond-rec case2 term2 (cdr cases)))))
    term))

(defun if-cond (cases)
  (if (consp cases)
      (let ((cond (car cases)))
        (let ((case2 (car cond))
              (term2 (cadr cond)))
          (if-cond-rec case2 term2 (cdr cases))))
    nil))

(defun map-fn-over-conditional-args (fn args)
  (if (consp args)
      (let ((cond (car args)))
        (let ((term (cons fn (cadr cond))))
          (cons `(,(car cond) ,term)
                (map-fn-over-conditional-args fn (cdr args)))))
    nil))


(defun insert-conditional-term-into-conditional-args (case term args)
  (if (consp args)
      (let ((cond (car args)))
        (let ((case (syn::and case (car cond)))
              (term (cons term (cadr cond))))
          (cons `(,case ,term)
                (insert-conditional-term-into-conditional-args case term (cdr args)))))
    nil))

(defun merge-conditional-term-with-conditional-args (term args)
  (if (consp term)
      (let ((cond (car term)))
        (append (insert-conditional-term-into-conditional-args (car cond) (cadr cond) args)
                (merge-conditional-term-with-conditional-args (cdr term) args)))
    nil))

(defun positive-conditions (terms)
  (if (consp terms)
      (let ((cond (car terms)))
        (let ((case (car cond))
              (term (cadr cond)))
          (cons (syn::and case term)
                (positive-conditions (cdr terms)))))
    nil))

(defun negative-conditions (terms)
  (if (consp terms)
      (let ((cond (car terms)))
        (let ((case (car cond))
              (term (cadr cond)))
          (cons (syn::and case (syn-not term))
                (negative-conditions (cdr terms)))))
    nil))

(defun map-case-over-conditional-terms (case terms)
  (if (consp terms)
      (let ((cond (car terms)))
        (let ((term (cadr cond)))
          (cons `(,(syn::and case (car cond)) ,term)
                (map-case-over-conditional-terms case (cdr terms)))))
    nil))

(defun map-conditions-over-conditional-terms (cases terms)
  (if (consp cases)
      (let ((case (car cases)))
        (append (map-case-over-conditional-terms case terms)
                (map-conditions-over-conditional-terms (cdr cases) terms)))
    nil))


(defun lambda-conditional-body (vars body case args)
  (if (consp body)
      (let ((cond (car body)))
        (cons `(,(syn::and case `((lambda ,vars ,(car cond)) ,@args))
                ((lambda ,vars ,(cadr cond)) ,@args))
              (lambda-conditional-body vars (cdr body) case args)))
    nil))

(defun lambda-conditional (vars body args)
  (if (consp args)
      (let ((cond (car args)))
        (append (lambda-conditional-body vars body (car cond) (cadr cond))
                (lambda-conditional vars body (cdr args))))
    nil))

;; The only problem with this is that we are leaving base case tests
;;

(mutual-recursion

 (defun lift-fn-guards-trunc (frec term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (consp term)) term)
    (t
     (let ((fn (car term)))
       (cond
        ((equal fn 'quote) term)
        ((consp fn)
         (let ((vars (lambda-vars term)))
           (met ((rec cond args) (lift-fn-guards-args frec (cdr term)))
             (declare (ignore rec))
             (let ((body (lift-fn-guards-trunc frec (lambda-bod term))))
               (cond
                ((not cond) `((lambda ,vars ,body) ,@args))
                (t (if-cond (lambda-conditional-args `(lambda ,vars ,body) args))))))))
        ((equal fn 'if)
         (met ((rec cond term1) (lift-fn-guards frec (cadr term)))
           (declare (ignore rec))
           (let ((term2 (lift-fn-guards-trunc frec (caddr term))))
             (let ((term3 (lift-fn-guards-trunc frec (cadddr term))))
               (cond
                ((not cond) (syn::lazy-if term1 term2 term3))
                (t (if-cond (if-conditional-test term1 term2 term3))))))))
        (t
         (met ((rec cond args) (lift-fn-guards-args frec (cdr term)))
           (declare (ignore rec))
           (cond
            ((not cond) `(,fn ,@args))
            (t (if-cond (lambda-conditional-args fn args)))))))))))

 (defun lift-fn-guards-args (frec args)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((rec1 cond1 term) (lift-fn-guards frec (car args)))
         (met ((rec2 cond2 args) (lift-fn-guards-args frec (cdr args)))
           (cond
            ((and (not rec1) (not rec2)) (mv nil nil (cons term args)))
            ((and (not cond1) (not cond2)) (mv t nil (cons term args)))
            (t
             (let ((term (if cond1 term `((,*t* ,term))))
                   (args (if cond2 args `((,*t* ,args)))))
               (let ((args (merge-conditional-term-with-conditional-args term args)))
                 (mv t t args)))))))
     (mv nil nil nil)))

 (defun lift-fn-guards (frec term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (consp term)) (mv nil nil term))
    (t
     (let ((fn (car term)))
       (cond
        ((equal fn 'quote) (mv nil nil term))
        ((consp fn)
         (met ((rec1 cond1 args) (lift-fn-guards-args frec (cdr term)))
           (met ((rec2 cond2 body) (lift-fn-guards frec (lambda-bod term)))
             (cond
              ((and (not cond1) (not cond2)) (mv (or rec1 rec2) nil args))
              (t
               (let ((body (if cond2 body `((,*t* ,body))))
                     (args (if cond1 args `((,*t* ,args)))))
                 (mv t t (lambda-conditional (lambda-vars term) body args))))))))
        ((equal fn 'if)
         (met ((rec1 cond1 term1) (lift-fn-guards frec (cadr term)))
           (met ((rec2 cond2 term2) (lift-fn-guards frec (caddr term)))
             (met ((rec3 cond3 term3) (lift-fn-guards frec (cadddr term)))
               (if (or cond1 rec2 rec3)
                   (let ((term1 (if cond1 term1 `((,*t* ,term1))))
                         (term2 (if cond2 term2 `((,*t* ,term2))))
                         (term3 (if cond3 term3 `((,*t* ,term3)))))
                     (let ((term1t (positive-conditions term1))
                           (term1f (negative-conditions term1)))
                       (let ((term (append (map-conditions-over-conditional-terms term1t term2)
                                           (map-conditions-over-conditional-terms term1f term3))))
                         (mv t t term))))
                 (mv rec1 nil term))))))
        ((equal fn frec)
         (met ((rec cond args) (lift-fn-guards-args frec (cdr term)))
           (declare (ignore rec))
           (if cond (mv t t (map-fn-over-conditional-args fn args))
             (mv t nil term))))
        (t
         (met ((rec cond args) (lift-fn-guards-args frec (cdr term)))
           (if cond (mv t t (map-fn-over-conditional-args fn args))
             (mv rec nil term)))))))))

 )

;; ===================================================================
;;
;; Separating the base case from the recursive cases
;;
;; ===================================================================

(defun generate-nested-if-rec (fn c0 v0 conds args)
  (if (consp conds)
      (let ((case (syn::conjoin-list (car conds))))
        (syn::lazy-if c0 v0
                      (generate-nested-if-rec fn case `(,fn ,@(car args)) (cdr conds) (cdr args))))
    v0))

(defun generate-nested-if (fn conds args)
  (if (consp conds)
      (let ((case (syn::conjoin-list (car conds))))
        (generate-nested-if-rec fn case `(,fn ,@(car args)) (cdr conds) (cdr args)))
    nil))


(defun map-cons (a list)
  (if (consp list)
      (cons (cons a (car list))
            (map-cons a (cdr list)))
    nil))

(mutual-recursion

 (defun rec-fn (frec term)
   (cond
    ((not (consp term)) nil)
    (t
     (let ((fn (car term)))
       (cond
        ((equal fn frec) t)
        ((equal fn 'quote) nil)
        (t
         (rec-args frec (cdr term))))))))

 (defun rec-args (frec args)
   (if (consp args)
       (or (rec-fn frec (car args))
           (rec-args frec (cdr args)))
     nil))

 )

(defun extract-base-fn (frec term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ;;
   ;; symbols are not recursive
   ;;
   ((not (consp term)) (mv t term))

   ;;
   ;; what about function applications?
   ;;
   (t
    (let ((fn (car term)))
      (cond
       ((equal fn frec)
        (mv nil :ignore))

       ((equal fn 'if)
        (let ((ifrec (rec-fn frec (cadr term))))
          ;;
          ;; If the test is not a base, we consider the whole term
          ;; recursive.
          ;;
          (if ifrec (mv nil :ignore)
            ;;
            ;; Otherwise we process the subterms.
            ;;
            (met ((thenbase then) (extract-base-fn frec (caddr term)))
              (met ((elsebase else) (extract-base-fn frec (cadddr term)))
                (cond
                 ((and thenbase elsebase)
                  (mv t (syn::lazy-if (cadr term) then else)))
                 ((and (not thenbase) (not elsebase))
                  (mv nil :ignore))
                 (t
                  (mv t (or (and thenbase then) (and elsebase else))))))))))

       ((equal fn 'quote)
        (mv t term))

       (t

        (let ((arec (rec-args frec (cdr term))))
          (if arec (mv nil :ignore)
            (if (consp fn)
                (met ((fbase fbody) (extract-base-fn frec (lambda-bod term)))
                  (if fbase
                      (mv t `((lambda ,(lambda-vars term) ,fbody) ,@(cdr term)))
                    (mv nil :ignore)))
              (mv t term))))))))))

(defun extract-rec-fn (frec term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ;;
   ;; symbols are not recursive
   ;;
   ((not (consp term)) (mv nil term))

   ;;
   ;; what about function applications?
   ;;
   (t
    (let ((fn (car term)))
      (cond
       ((equal fn frec)
        (mv t term))

       ((equal fn 'if)
        (let ((ifrec (rec-fn frec (cadr term))))
          ;;
          ;; If the test is ever recursive, we consider
          ;; the whole term recursive.
          ;;
          (if ifrec (mv t term)
            ;;
            ;; Otherwise we process the subterms.
            ;;
            (met ((thenrec then) (extract-rec-fn frec (caddr term)))
              (met ((elserec else) (extract-rec-fn frec (cadddr term)))
                (cond
                 ;;
                 ;; If the branches are never recursive
                 ;;
                 ((and (not thenrec) (not elserec))
                  (mv nil term))
                 ;;
                 ;; if we are always potentially recursive ..
                 ;;
                 ((and thenrec elserec)
                  (mv t (syn::lazy-if (cadr term) then else)))
                 (t
                  (mv t (if thenrec then else)))))))))

       ((equal fn 'quote)
        (mv nil term))

       (t

        (let ((arec (rec-args frec (cdr term))))
          (if arec (mv t term)
            (if (consp fn)
                (met ((brec fbody) (extract-rec-fn frec (lambda-bod term)))
                  (mv brec `((lambda ,(lambda-vars term) ,fbody) ,@(cdr term))))
              (mv nil term))))))))))

(defun extract-case-fn (frec term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ;;
   ;; symbols are not recursive
   ;;
   ((not (consp term)) (mv nil nil))

   ;;
   ;; what about function applications?
   ;;
   (t
    (let ((fn (car term)))
      (cond
       ((equal fn frec)
        (mv t *t*))

       ((equal fn 'if)
        (let ((ifrec (rec-fn frec (cadr term))))
          ;;
          ;; If the test is ever recursive, we consider
          ;; the whole term as always recursive.
          ;;
          (if ifrec (mv t *t*)
            ;;
            ;; Otherwise we process the subterms.
            ;;
            (met ((thenrec then) (extract-case-fn frec (caddr term)))
              (met ((elserec else) (extract-case-fn frec (cadddr term)))
                (cond
                 ;;
                 ;; If the branches are never recursive
                 ;;
                 ((and (not thenrec) (not elserec))
                  (mv nil nil))
                 ;;
                 ;; if we are both sometimes recursive ..
                 ;;
                 ((and thenrec elserec)
                  (mv t (syn::lazy-if (cadr term) then else)))
                 (t
                  (mv t (if thenrec (syn::and (cadr term) then)
                          (syn::and (syn-not (cadr term)) else))))))))))

       ((equal fn 'quote)
        (mv nil nil))

       (t

        (let ((arec (rec-args frec (cdr term))))
          (if arec (mv t *t*)
            (if (consp fn)
                (met ((crec cbody) (extract-case-fn frec (lambda-bod term)))
                  (if crec
                      (mv t `((lambda ,(lambda-vars term) ,cbody) ,@(cdr term)))
                    (mv nil term)))
              (mv nil term))))))))))

;; ===================================================================
;;
;; We may eventually want to do something with mv-nth .. probably
;; after all of the other processing has been done.
;;
;; ===================================================================

(defun strip-mv-nth (args symbols mv res)
  (if (consp args)
      (let ((term (car args)))
        (if (and (consp term)
                 (equal (car term) 'mv-nth))
            (strip-mv-nth (cdr args) (cdr symbols) (caddr term) (cons (car symbols) res))
          (mv mv res args symbols)))
    (mv mv res args symbols)))

(mutual-recursion

 (defun un-mv-nth-args (args)
   (declare (xargs :mode :program))
   (if (consp args)
       (cons (un-mv-nth-term (car args))
             (un-mv-nth-args (cdr args)))
     nil))

 (defun un-mv-nth-term (term)
   (declare (xargs :mode :program))
   (cond
    ((not (consp term))
     term)
    ((consp (car term))
     (let ((body (un-mv-nth-term (lambda-bod term))))
       (met ((mv res args symbols) (strip-mv-nth (cdr term) (lambda-vars term) nil nil))
         (if mv
             (let ((mv (un-mv-nth-term mv)))
               (let ((args (un-mv-nth-args args)))
                 `(mv-let ,res ,mv ((lambda ,symbols ,body) ,@args))))
           (let ((args (un-mv-nth-args (cdr term))))
             `((lambda ,(lambda-vars term) ,body) ,@args))))))
    (t
     (cons (car term) (un-mv-nth-args (cdr term))))))

 )

;; ===================================================================
;;
;; Here is where we compute the "spec" of the function body.
;;
;; ===================================================================

;; compile the function into a spec in which each symbol
;; is associated with a non-recursive body.  At symbol
;; boundaries we invoke a recursive call.
;;
;; Each function call location is replaced by a unique symbol.


;; We evaluate the arguments outside in.
;; comp-step computes either:
;; 1. a list of values which constitute the arguments to goo
;; 2. a value representing either a return value
;;    or the value of an "if" test.

;; We replace a recursive call with a reference to a
;; particular value on the return list.

(defun lambda-wrap-steps (vars steps args)
  (if (consp steps)
      (let ((step (car steps)))
        (let ((key (car step))
              (body (cadr step)))
          (cons (cons key (list `((lambda ,vars ,body) ,@args)))
                (lambda-wrap-steps vars (cdr steps) args))))
    nil))

(defun key-val (key val list)
  (declare (ignore key))
  (val val list))

(mutual-recursion

 (defun compute-fn-spec (fn key val term spec0 spec)
   (cond
    ((not (consp term))
     (mv key val term spec nil))
    ((consp (car term))
     (met ((key val args spec steps) (compute-fn-spec-args fn key val (cdr term) nil spec0 spec nil))
       (met ((key val body spec bsteps) (compute-fn-spec fn key val (lambda-bod term) spec spec))
         (let ((bsteps (lambda-wrap-steps (lambda-vars term) bsteps args)))
           (let ((steps (revappend steps bsteps)))
             (mv key val `((lambda ,(lambda-vars term) ,body) ,@args) spec steps))))))
    ((equal (car term) 'quote)
     (mv key val term spec nil))
    ((equal fn (car term))
     (met ((key ignore args argspec steps)
           (compute-fn-spec-args fn key (len spec0) (cdr term) nil spec0 spec0 nil))
       (declare (ignore ignore))
       (mv (1+ key) (1+ val) `(key-val (quote ,key) (quote ,val) gensym::vals)
           (cons (cons key (revappend argspec nil)) spec)
           (cons (cons key (list `(list ,@args))) steps))))
    (t
     (met ((key val args spec steps) (compute-fn-spec-args fn key val (cdr term) nil spec0 spec nil))
       (mv key val `(,(car term) ,@args) spec steps)))))

 (defun compute-fn-spec-args (fn key val args res spec0 spec steps)
   (if (consp args)
       (met ((key val term spec bsteps) (compute-fn-spec fn key val (car args) spec0 spec))
         (let ((steps (revappend bsteps steps)))
           (compute-fn-spec-args fn key val (cdr args) (cons term res) spec0 spec steps)))
     (mv key val (revappend res nil) spec (revappend steps nil))))

 )

;; ===================================================================
;;
;; Generating Terminates/Measure/Induction schemes from original body
;;
;; ===================================================================

(defun map-lambda-over-body-list (vars body args)
  (if (consp body)
      (cons `((lambda ,vars ,(car body)) ,@args)
            (map-lambda-over-body-list vars (cdr body) args))
    nil))

;; Don't we want to distinguish between the recursive calls?  I think
;; our induction needs to be more sensitive to the "if" structure of
;; the body of the function.  ie: if there is a case that
;; distinguishes between recursive calls, it should be made explicit.
;; For example, (let ((x (if test (foo x) (foo y)))) ..) should
;; have two inductive cases, not just one.  Perhaps this is what
;; is causing the problems in our final proof?

(mutual-recursion

 (defun alt-body (frec fn term)
   (cond
    ((not (consp term))
     nil)
    ((consp (car term))
     (let ((alt-body (alt-body frec fn (lambda-bod term))))
       (let ((alt-body (map-lambda-over-body-list (lambda-vars term) alt-body (cdr term))))
         (let ((alt-args (alt-args frec fn (cdr term))))
           (revappend alt-body alt-args)))))
    ((equal (car term) 'quote)
     nil)
    ((equal (car term) frec)
     (let ((alt (alt-args frec fn (cdr term))))
       (cons `(,fn ,@(cdr term)) alt)))
    (t
     (alt-args frec fn (cdr term)))))

 (defun alt-args (frec fn args)
   (if (consp args)
       (let ((alt1 (alt-body frec fn (car args))))
         (let ((alt2 (alt-args frec fn (cdr args))))
           (revappend alt1 alt2)))
     nil))

 )

(defun map-join-over-list (join x list)
  (if (consp list)
      `(,join ,x ,(map-join-over-list join (car list) (cdr list)))
    x))

(defun alt-body-fn (frec fn join term)
  (let ((alt (alt-body frec fn term)))
    (map-join-over-list join (car alt) (cdr alt))))

(include-book "arithmetic/top-with-meta" :dir :system)

(defund mm (key value)
  (declare (ignore key))
  value)

(defthm mm-0
  (equal (mm key 0) 0)
  :hints (("Goal" :in-theory (enable mm))))

(in-theory (enable mm))

;; ===================================================================
;;
;; Putting it all together to generate our desired result.
;;
;; ===================================================================

(set-state-ok t)

(defun bind-args (args list)
  (if (consp args)
      (cons `(,(car args) (car ,list))
            (bind-args (cdr args) `(cdr ,list)))
    nil))

(defmacro ig (&rest args)
  `(value-triple '(list ,@args)))

(defun syn-symbol-or-quote-listp (list)
  (if (syn::consp list)
      (and (or (quotep (syn::car list)) (symbolp (syn::car list)))
           (syn-symbol-or-quote-listp (syn::cdr list)))
    (quotep list)))

(defun iff-equal (x y)
  (iff x y))

(defcong iff equal (iff-equal x y) 1)
(defcong iff equal (iff-equal x y) 2)

(defthm iff-equal-id
  (iff-equal x x))

(in-theory (disable iff-equal (iff-equal) (:type-prescription iff-equal)))

(defun tlist (args)
  (if (consp args)
      (cons t (tlist (cdr args)))
    nil))

(mutual-recursion
 (defun replace-frec (frec fn term)
   (cond
    ((not (consp term)) term)
    ((consp (car term))
     `((lambda ,(lambda-vars term) ,(replace-frec frec fn (lambda-bod term)))
       ,@(replace-frec-args frec fn (cdr term))))
    ((equal frec (car term))
     `(,fn ,@(replace-frec-args frec fn (cdr term))))
    (t
     `(,(car term) ,@(replace-frec-args frec fn (cdr term))))))
 (defun replace-frec-args (frec fn args)
   (if (consp args)
       (cons (replace-frec frec fn (car args))
             (replace-frec-args frec fn (cdr args)))
     nil))
 )

(defun cond-case (cond)
  (if (consp cond)
      (let ((entry (car cond)))
        (let ((case (car entry)))
          (syn-or case
                  (cond-case (cdr cond)))))
    *nil*))


(defthm equal-booleans-reducton-alt
  (implies
   (and
    (booleanp x)
    (booleanp y))
   (equal (equal x y)
          (and (implies x y)
               (implies y x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defun construct-foo-forms (fn args body TBody spec steps)

  (let* ((goo-spec                  (symbol-fns::suffix fn `-spec))
         (goo-comp-step             (symbol-fns::suffix fn `-comp-step))
         (goo-base-step             (symbol-fns::suffix fn `-base-step))
         (goo-done                  (symbol-fns::suffix fn `-done))
         (goo-stk-1                 (symbol-fns::suffix fn `-stk-1))
         (goo-stk-1_measure         (symbol-fns::suffix fn `-stk-1_measure))
         (goo-stk-1_terminates      (symbol-fns::suffix fn `-stk-1_terminates))
         (goo                       (symbol-fns::suffix fn `-5))
         (goo_terminates            (symbol-fns::suffix fn `-5_terminates))
         (goo_terminates_type       (symbol-fns::suffix fn `-5_terminates_type))
         (goo_measure               (symbol-fns::suffix fn `-5_measure))

         (goo-call                  (symbol-fns::suffix fn `-5-call))
         (goo_terminates-call       (symbol-fns::suffix fn `-5_terminates-call))
         (goo_measure-call          (symbol-fns::suffix fn `-5_measure-call))
         (goo-call-open             (symbol-fns::suffix fn `-5-call-open))
         (goo_terminates-call-open  (symbol-fns::suffix fn `-5_terminates-call-open))
         (goo_terminates-call-type  (symbol-fns::suffix fn `-5_terminates-call-type))
         (goo_measure-call-open     (symbol-fns::suffix fn `-5_measure-call-open))
         (goo_measure-call_bound    (symbol-fns::suffix fn `-5_measure-call_bound))

         (goo_true                  (symbol-fns::suffix fn `-5_true))
         (goo_definition            (symbol-fns::suffix fn `-5_definition))
         (goo_measure_definition    (symbol-fns::suffix fn `-5_measure_definition))
         (goo_terminates_definition (symbol-fns::suffix fn `-5_terminates_definition))
         (goo_measure_natp          (symbol-fns::suffix fn `-5_measure_natp))
         (goo_measure_bound         (symbol-fns::suffix fn `-5_measure_bound))
         (functional-instance      `((goo                  ,goo)
                                     (goo_terminates       ,goo_terminates)
                                     (goo_measure          ,goo_measure)
                                     (goo-call             ,goo-call)
                                     (goo_terminates-call  ,goo_terminates-call)
                                     (goo_measure-call     ,goo_measure-call)
                                     (goo-stk-1            ,goo-stk-1)
                                     (goo-spec             ,goo-spec)
                                     (goo-comp-step        ,goo-comp-step)
                                     (goo-base-step        ,goo-base-step)
                                     (goo-done             ,goo-done)
                                     (goo-stk-1_terminates ,goo-stk-1_terminates)
                                     (goo-stk-1_measure    ,goo-stk-1_measure)))

         (fn-closed                  (symbol-fns::suffix fn `-closed))
         (fn_terminates              (symbol-fns::suffix fn `_terminates))
         (fn_always_terminates       (symbol-fns::suffix fn `_always_terminates))
         (fn_always_terminates_prop  (symbol-fns::suffix fn `_always_terminates_prop))
         (fn_measure                 (symbol-fns::suffix fn `_measure))
         (fn_terminates-closed       (symbol-fns::suffix fn `_terminates-closed))
         (fn_terminates-type         (symbol-fns::suffix fn `_terminates-type))
         (fn_measure-closed          (symbol-fns::suffix fn `_measure-closed))
         (fn_measure-bound           (symbol-fns::suffix fn `_measure-bound))
         (fn_induction               (symbol-fns::suffix fn `_induction))
         (fn_induction_rule          (symbol-fns::suffix fn `_induction_rule))
         (fn_definition              (symbol-fns::suffix fn `_definition))
         (fn_measure_definition      (symbol-fns::suffix fn `_measure_definition))
         (fn_terminates_definition   (symbol-fns::suffix fn `_terminates_definition))
         (fn_terminates_forward      (symbol-fns::suffix fn `_terminates_forward))
         (fn_terminates-closed-open  (symbol-fns::suffix fn `_terminates-closed-open))
         (fn_excess                  (symbol-fns::suffix fn `_excess))
         (fn_excess_natp             (symbol-fns::suffix fn `_excess_natp))
         (fn_closed_to_open          (symbol-fns::suffix fn `_closed_to_open))

         (ICond  (lift-induction-fn fn-closed fn_induction (replace-frec fn fn-closed TBody)))

    )

    (met ((case base) (defun::lift-base (list fn) TBody args))

     `(encapsulate
       ()

       (set-irrelevant-formals-ok t)
       (set-ignore-ok t)

       #+joe
       (in-theory
        (union-theories
         nil
         (theory 'minimal-theory)))

       (defund ,goo-spec ()
         ',spec)

       (defund ,goo-comp-step (key args gensym::vals)
         (let ,(bind-args args 'args)
           (case key
             ,@steps
             )))

       (defund ,goo-base-step (args)
         (let ,(bind-args args 'args)
           ,base))

       (defund ,goo-done (args)
         (let ,(bind-args args 'args)
           (not ,case)))

       (defminterm ,goo-stk-1 (list stk)
         (let ((args (car list))
               (fn   (cadr list))
               (spec (caddr list))
               (vals (cadddr list))
               (vstk (cadddr (cdr list))))
           (if (and
                (or (,goo-done args)
                    (not (consp spec)))
                (not (consp vstk))
                (not (consp stk)))
               (if (,goo-done args)
                   (,goo-base-step args)
                 (,goo-comp-step fn args (rev vals)))
             (if (and
                  (or (,goo-done args)
                      (not (consp spec)))
                  (not (consp vstk)))
                 (let ((arg (let ((val
                                   (if (,goo-done args) (,goo-base-step args)
                                     (,goo-comp-step fn args (rev vals)))))
                              (let ((vstk (car stk)))
                                (met ((args fn spec vals vstk) (vstk-pop vstk))
                                  (list args fn spec (cons val vals) vstk))))))
                   (,goo-stk-1 arg (cdr stk)))
               (if (or (,goo-done args)
                       (not (consp spec)))
                   (let ((val (if (,goo-done args) (,goo-base-step args)
                                (,goo-comp-step fn args (rev vals)))))
                     (let ((stk (cons vstk stk)))
                       (,goo-stk-1 (spec-args (,goo-spec) val) stk)))
                 (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
                   (,goo-stk-1 (list args (caar spec) (cdar spec) nil vstk) stk)))))))

       (local (in-theory (enable ,goo-comp-step ,goo-base-step ,goo-done)))

       (defund ,goo (args fn spec vals vstk)
         (,goo-stk-1 (list args fn spec vals vstk) nil))

       (defund ,goo_terminates (args fn spec vals vstk)
         (,goo-stk-1_terminates (list args fn spec vals vstk) nil))

       (defthm ,goo_terminates_type
         (booleanp (,goo_terminates args fn spec vals vstk))
         :hints (("Goal" :in-theory (enable ,goo_terminates))))

       (defund ,goo_measure (args fn spec vals vstk)
         (,goo-stk-1_measure (list args fn spec vals vstk) nil))

       (defund ,goo-call (val)
         (let ((spec (,goo-spec)))
           (,goo val (car spec) (cdr spec) nil nil)))

       (defun ,goo-call-open (val)
         (let ((spec (,goo-spec)))
           (,goo val (car spec) (cdr spec) nil nil)))

       (defund ,goo_terminates-call (val)
         (let ((spec (,goo-spec)))
           (,goo_terminates val (car spec) (cdr spec) nil nil)))

       (defun ,goo_terminates-call-open (val)
         (let ((spec (,goo-spec)))
           (,goo_terminates val (car spec) (cdr spec) nil nil)))

       (defthm ,goo_terminates-call-type
         (and
          (booleanp (,goo_terminates-call val))
          (booleanp (,goo_terminates-call-open val)))
         :hints (("Goal" :in-theory (enable ,goo_terminates-call))))


       (defund ,goo_measure-call (val)
         (let ((spec (,goo-spec)))
           (,goo_measure val (car spec) (cdr spec) nil nil)))

       (defun ,goo_measure-call-open (val)
         (let ((spec (,goo-spec)))
           (,goo_measure val (car spec) (cdr spec) nil nil)))

       (defthmd ,goo_true
         (true (,goo args fn spec vals vstk))
         :hints (("Goal" :in-theory (enable ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_true
                                             ,@functional-instance))))

       (defthm ,goo_definition
         (equal (,goo args fn spec vals vstk)
                (if (or (not (,goo_terminates args fn spec vals vstk))
                        (and (or (,goo-done args)
                                 (not (consp spec)))
                             (not (consp vstk))))
                    (if (,goo-done args)
                        (,goo-base-step args)
                      (,goo-comp-step fn args (rev vals)))
                  (if (or (,goo-done args)
                          (not (consp spec)))
                      (let ((val (if (,goo-done args) (,goo-base-step args)
                                   (,goo-comp-step fn args (rev vals)))))
                        (let ((val (,goo-call val)))
                          (met ((args fn spec vals vstk) (vstk-pop vstk))
                               (,goo args fn spec (cons val vals) vstk))))
                    (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
                      (,goo args (caar spec) (cdar spec) nil vstk)))))
         :hints (("Goal" :in-theory (enable ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_definition
                                             ,@functional-instance))))

       (defthm ,goo_measure_definition
         (implies
          (,goo_terminates args fn spec vals vstk)
          (equal (,goo_measure args fn spec vals vstk)
                 (cond
                  ((and
                    (,goo-done args)
                    (not (consp vstk))) (mm :base0 (o)))
                  ((and
                    (not (consp spec))
                    (not (consp vstk))) (mm :base1 (o)))
                  ((and
                    (consp vstk)
                    (,goo-done args))
                   (let ((val0 (,goo-base-step args)))
                     (let ((val (,goo-call val0)))
                       (met ((args fn spec vals vstk) (vstk-pop vstk))
                            (+ (mm :call1 1) (,goo_measure-call val0)
                               (,goo_measure args fn spec (cons val vals) vstk))))))
                  ((and
                    (consp vstk)
                    (not (,goo-done args))
                    (not (consp spec)))
                   (let ((val0 (,goo-comp-step fn args (rev vals))))
                     (let ((val (,goo-call val0)))
                       (met ((args fn spec vals vstk) (vstk-pop vstk))
                            (+ (mm :call2 1) (,goo_measure-call val0)
                               (,goo_measure args fn spec (cons val vals) vstk))))))
                  (t
                   (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
                     (+ (mm :call0 1) (,goo_measure args (caar spec) (cdar spec) nil vstk)))))))
         :hints (("Goal" :in-theory (enable mm
                                            ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_measure_definition
                                             ,@functional-instance))))

       (defthm ,goo_terminates_definition
         (and
          (implies
           (and
            (,goo-done args)
            (not (consp vstk)))
           (,goo_terminates args fn spec vals vstk))
          (implies
           (and
            (not (consp spec))
            (not (consp vstk)))
           (,goo_terminates args fn spec vals vstk))
          (implies
           (and
            (consp vstk)
            (,goo-done args))
           (iff (,goo_terminates args fn spec vals vstk)
                (let ((val0 (,goo-base-step args)))
                  (let ((val (,goo-call val0)))
                    (met ((args fn spec vals vstk) (vstk-pop vstk))
                      (and (,goo_terminates-call val0)
                           (,goo_terminates args fn spec (cons val vals) vstk)))))))
          (implies
           (and
            (consp vstk)
            (not (,goo-done args))
            (not (consp spec)))
           (iff (,goo_terminates args fn spec vals vstk)
                (let ((val0 (,goo-comp-step fn args (rev vals))))
                  (let ((val (,goo-call val0)))
                    (met ((args fn spec vals vstk) (vstk-pop vstk))
                      (and (,goo_terminates-call val0)
                           (,goo_terminates args fn spec (cons val vals) vstk)))))))
          (implies
           (and
            (not (,goo-done args))
            (consp spec))
           (iff (,goo_terminates args fn spec vals vstk)
                (let ((vstk (vstk-push args fn (cdr spec) vals vstk)))
                  (,goo_terminates args (caar spec) (cdar spec) nil vstk)))))
         :hints (("Goal" :in-theory (enable ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_terminates_definition
                                             ,@functional-instance))))

       (defthm ,goo_measure_natp
         (natp (,goo_measure args fn spec vals vstk))
         :rule-classes ((:forward-chaining
                         :trigger-terms ((,goo_measure args fn spec vals vstk))))
         :hints (("Goal" :in-theory (enable ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_measure_natp
                                             ,@functional-instance))))


       (defthm ,goo_measure_bound
         (implies
          (,goo_terminates args fn spec vals vstk)
          (< 0 (,goo_measure args fn spec vals vstk)))
         :rule-classes (:linear)
         :hints (("Goal" :in-theory (enable ,goo
                                            ,goo_terminates
                                            ,goo_measure
                                            ,goo-call
                                            ,goo_terminates-call
                                            ,goo_measure-call)
                  :use (:functional-instance goo_measure_bound
                                             ,@functional-instance))))

       (defthm ,goo_measure-call_bound
         (implies
          (,goo_terminates-call val)
          (< 0 (,goo_measure-call val)))
         :rule-classes (:linear)
         :hints (("Goal" :in-theory '(,goo_terminates-call
                                      ,goo_measure-call
                                      ,goo_measure_bound))))

       (defund ,fn_terminates ,args
	 (,goo_terminates-call-open (list ,@args)))

       (defund ,fn_measure ,args (,goo_measure-call-open (list ,@args)))

       (defund ,fn ,args
         (if (,fn_terminates ,@args)
             (,goo-call-open (list ,@args))
           ,base))

       (defun ,fn_terminates-closed ,args (,goo_terminates-call (list ,@args)))

       (defthm ,fn_terminates-type
         (and
          (booleanp (,fn_terminates ,@args))
          (booleanp (,fn_terminates-closed ,@args)))
         :hints (("Goal" :in-theory (enable ,fn_terminates))))

       (defun ,fn_measure-closed ,args (,goo_measure-call (list ,@args)))

       (defthm ,fn_measure-bound
         (<= (,fn_measure ,@args)
             (,fn_measure-closed ,@args))
         :hints (("Goal" :in-theory '(,goo_measure-call-open
                                      ,goo_measure-call
                                      ,fn_measure
                                      ,fn_measure-closed)))
         :rule-classes (:linear))

       (defun ,fn-closed ,args
         (if (,fn_terminates-closed ,@args)
             (,goo-call (list ,@args))
           ,base))


       ;;
       ;; Make sure case is not vacuously true or false
       ;;

       (must-not-prove ,case)

       (must-not-prove (not ,case))

       (local
        (defthm base_check
          (implies
           (not ,case)
           (equal ,body ,base))
          :rule-classes nil))

       (local
        (defthm body_check
          (equal ,body ,TBody)
          :rule-classes nil))

       ;; How does this work?
       (defthmd ,fn_definition
         (equal (,fn ,@args)
                (if (,fn_terminates ,@args)
                    (if ,case
                        ,(replace-frec fn fn-closed TBody)
                      ,base)
                  ,base))
         :rule-classes ((:definition :clique (,fn ,fn-closed)
                                     :controller-alist ((,fn-closed ,@(tlist args))
                                                        (,fn ,@(tlist args)))))
         :hints (("Goal" :in-theory (enable
                                     ,fn
                                     ,fn_terminates
                                     ,fn_measure
                                     ))))

       ;;
       ;; The measure is complicated by the intermediate machine.
       ;;
       (defund ,fn_excess (,@args)
         ,(syn::lazy-if case `(- (,fn_measure ,@args)
                                 (1+ ,(alt-body-fn fn-closed fn_measure-closed '+ (replace-frec fn fn-closed TBody))))
                        `0))

       (defthm ,fn_excess_natp
         (implies
          (,fn_terminates ,@args)
          (<= 0 (,fn_excess ,@args)))
         :rule-classes (:forward-chaining :linear)
         :hints (("Goal" :in-theory (enable
                                     ,fn
                                     ,fn_terminates
                                     ,fn_measure
                                     ,fn_excess
                                     ))))

       #+joe
       (defthmd ,fn_measure_definition
         (implies
          (,fn_terminates ,@args)
          (equal (,fn_measure ,@args)
                 (if ,case
                     (+ 1 ,(alt-body-fn fn-closed fn_measure-closed '+ (replace-frec fn fn-closed TBody))
                        (,fn_excess ,@args))
                   (o))))
         :rule-classes ((:definition :clique (,fn_measure ,fn_measure-closed)
                                     :controller-alist ((,fn_measure-closed ,@(tlist args))
                                                        (,fn_measure ,@(tlist args)))))
         :hints (("Goal" :in-theory (enable ,fn_excess))
                 (and stable-under-simplificationp
                      '(:in-theory (enable ,fn_measure)))))


       (defthmd ,fn_measure_definition
         (implies
          (and
           (,fn_terminates ,@args)
           (iff gensym::base (double-rewrite (not ,case))))
          (and
           (implies
            gensym::base
            (equal (,fn_measure ,@args)
                   (o)))
           (implies
            (not gensym::base)
            (equal (,fn_measure ,@args)
                   (+ 1 ,(alt-body-fn fn-closed fn_measure-closed '+ (replace-frec fn fn-closed TBody))
                      (,fn_excess ,@args))))))
         :hints (("Goal" :in-theory (enable ,fn_excess))
                 (and stable-under-simplificationp
                      '(:in-theory (enable ,fn_measure)))))

       ;; If you make terminates boolean (which I suppose it should
       ;; have been from the beginning), you should be able to
       ;; construct an executable counterpart for it here.

       #+joe
       (verify-guards ',fn_terminates
		      :hints (("Goal" :in-theory (enable
						  ,fn
						  ,fn_terminates
						  ,fn_measure
						  ))))

       (defthmd ,fn_terminates_definition
         (and
          (implies
           (not ,case)
           (equal (,fn_terminates ,@args) t))
          (implies
           ,case
           (equal (,fn_terminates ,@args)
                  ,(alt-body-fn fn-closed fn_terminates-closed 'and (replace-frec fn fn-closed TBody)))))
         :rule-classes ((:definition
                         :clique (,fn_terminates ,fn_terminates-closed)
                         :controller-alist ((,fn_terminates-closed ,@(tlist args))
					    (,fn_terminates ,@(tlist args)))
                         :corollary
                         (equal (,fn_terminates ,@args)
                                (if ,case
                                    ,(alt-body-fn fn-closed fn_terminates-closed 'and (replace-frec fn fn-closed TBody))
                                  t))
                         :hints (("Goal" :in-theory nil))))
         :hints (("Goal" :in-theory (enable
                                     ,fn
                                     ,fn_terminates
                                     ,fn_measure
                                     ))))

       (in-theory (enable
                   ,fn_terminates_definition
                   ,fn_measure_definition
                   ,fn_definition
                   ))

       (in-theory (disable
                   ,fn-closed
                   ,fn_measure-closed
                   ,fn_terminates-closed
                   ))

       (defun-sk ,fn_always_terminates ()
         (forall (,@args) (,fn_terminates ,@args))
         :rewrite :direct)

       (defthm ,fn_always_terminates_prop
         (implies
          (,fn_always_terminates)
          (,fn_terminates ,@args)))

       (in-theory (disable ,fn_always_terminates))

       ;;
       ;; we can't easily use executable counterparts.
       ;;
       (in-theory (disable
                   (,fn)
                   (,fn_measure)
                   (,fn_terminates)))

       (defun ,fn_induction ,args
         (declare (xargs :measure (,fn_measure ,@args)))
         (if (,fn_terminates ,@args)
             (if ,case
                 (cond
                  ,@ICond)
               (list ,@args))
           (list ,@args)))

       (defthmd ,fn_terminates-closed-open
         (equal (,fn_terminates-closed ,@args)
		(,fn_terminates ,@args))
         :hints (("Goal" :in-theory '(,fn-closed
                                      ,fn
                                      ,fn_measure-closed
                                      ,fn_measure
                                      ,fn_terminates-closed
                                      ,fn_terminates
                                      ,goo-call
                                      ,goo-call-open
                                      ,goo_measure-call
                                      ,goo_measure-call-open
                                      ,goo_terminates-call
                                      ,goo_terminates-call-open
                                      ))))

       (defthm ,fn_terminates_forward
         (implies
          (,fn_terminates-closed ,@args)
          (,fn_terminates ,@args))
         :rule-classes (:forward-chaining)
         :hints (("Goal" :in-theory '(,fn-closed
                                      ,fn
                                      ,fn_measure-closed
                                      ,fn_measure
                                      ,fn_terminates-closed
                                      ,fn_terminates
                                      ,goo-call
                                      ,goo-call-open
                                      ,goo_measure-call
                                      ,goo_measure-call-open
                                      ,goo_terminates-call
                                      ,goo_terminates-call-open
                                      ))))

       (defthm ,fn_closed_to_open
         (and
          (equal (,fn-closed ,@args) (,fn ,@args))

          ;; Measure is (currently) used in only one place so our
          ;; linear rule relating open and closed should be sufficient.
          ;;
          ;;(equal (,fn_measure-closed ,@args) (,fn_measure ,@args))

          ;; We have added a forward chaining rule that pretty much
          ;; does this.
          ;;
          ;;(equal (,fn_terminates-closed ,@args) (,fn_terminates ,@args))
          )
         :hints (("Goal" :in-theory '(,fn-closed
                                      ,fn
                                      ,fn_measure-closed
                                      ,fn_measure
                                      ,fn_terminates-closed
                                      ,fn_terminates
                                      ,goo-call
                                      ,goo-call-open
                                      ,goo_measure-call
                                      ,goo_measure-call-open
                                      ,goo_terminates-call
                                      ,goo_terminates-call-open
                                      ))))

       (defthm ,fn_induction_rule t
         :rule-classes ((:induction
                         :pattern (,fn ,@args)
                         :condition t
                         :scheme (,fn_induction ,@args))))

       #+joe
       (mutual-recrusion

	(defun ,fn_alt ,args
	  (declare (xargs :measure (,fn_measure ,@args)))
	  (mbe :logic (,fn ,@args)
	       :exec ))

	(defun ,fn_terminates_alt ,args
	  (declare (xargs :measure (,fn_measure ,@args)))
	  (mbe :logic (,fn_terminates ,@args)
	       :exec ))

	)


       ))))

(defun translate-extract (fn args body state)
  (declare (xargs :mode :program))
  (met ((err TBody) (pseudo-translate body (list (cons fn args)) (w state)))
    #+joe(with-ctx-summarized `(translate-extract ,fn)
			      (TRANSLATE body T T T CTX (w state) state))
       (met ((key val term spec steps) (compute-fn-spec fn 0 0 TBody nil nil))
            (declare (ignore val))
            (let ((spec  (cons key (revappend spec nil)))
                  (steps (cons (cons key (list term)) steps)))
              (let ((event (construct-foo-forms fn args body Tbody spec steps)))
                (mv err event state))))))

(defmacro def::un (fn args body)
  `(make-event (translate-extract ',fn ',args ',body state)))

(def::un mc91 (n)
  (if (> n 100) (- n 10)
    (mc91 (mc91 (+ n 11)))))

;;
;; Proof by induction, with the help of our _terminates predicate.
;;
(defthm integerp-mc91
  (implies
   (and
    (integerp n)
    (mc91_terminates n))
   (integerp (mc91 n))))

;; Even nicer is the _always_terminates predicate .. kinda like "ttags" for
;; termination .. again with the proof by induction.
;;
;; Note: this proof by induction would have used the executable
;; counterpart of (mc91 ) had it been available. (Hint, hint)
;;
(defthm mc91-proof
  (implies
   (and
    (integerp n)
    (mc91_always_terminates))
   (equal (mc91 n)
          (if (< n 101) 91 (- n 10)))))

;;
;; TARAI function: Original definition of TAK function
;;
(def::un tarai (x y z)
  (cond
   ((> x y)
    (tarai
     (tarai (1- x) y z)
     (tarai (1- y) z x)
     (tarai (1- z) x y)))
   (t y)))

(defthm tarai_unwinding
  (implies
   (tarai_terminates x y z)
   (equal (tarai x y z)
          (if (<= x y) y
            (if (<= y z) z
              x)))))

;;
;; TAK function : John Macarthy's variation of the TARAI function
;;
(def::un tak (x y z)
  (cond
   ((not (< y x)) z)
   (t
    (tak
     (tak (1- x) y z)
     (tak (1- y) z x)
     (tak (1- z) x y)))))


;;
;; A bunch of other stress tests ..
;;
(local
 (encapsulate
  ()
  (local

   (encapsulate
    ()

    (defstub zed-test (x) nil)

    (local
     (encapsulate
      ()
      (local
       (def::un zed (a b c) (if (zed-test a) (zed (1+ a) b c) (+ b c))))
      (local
       (defthm zed_check
         (implies
          (zed_terminates a b c)
          (equal (zed a b c)
                 (if (zed-test a) (zed (1+ a) b c) (+ b c))))))))


    (local
     (encapsulate
      ()
      (local
       (def::un zed (a b c)
         (if (zed-test a) (+ b c)
           (+ (zed (1+ a) (zed (+ 2 a) b c)
                   (+ (zed (+ 3 a) (+ b c) c)
                      (zed b (+ a c) a)))))))
      (local
       (defthm zed_check
         (implies
          (zed_terminates a b c)
          (equal (zed a b c)
                 (if (zed-test a) (+ b c)
                   (+ (zed (1+ a) (zed (+ 2 a) b c)
                           (+ (zed (+ 3 a) (+ b c) c)
                              (zed b (+ a c) a)))))))))
      ))

    (local
     (encapsulate
      ()
      (local
       (def::un yak (m n)
         (cond
          ((equal m 0) (+ n 1))
          ((and (< 0 m) (= n 0)) (yak (1- m) 1))
          (t (yak (1- m) (yak m (1- n)))))))
      (local
       (defthm yak_check
         (implies
          (yak_terminates m n)
          (equal (yak m n)
                 (cond
                  ((equal m 0) (+ n 1))
                  ((and (< 0 m) (= n 0)) (yak (1- m) 1))
                  (t (yak (1- m) (yak m (1- n)))))))))
      ))


    (local
     (encapsulate
      ()
      (local
       (def::un zed (a b c)
         (let ((z (+ a b c)))
           (if (zed-test z) (+ a b c)
             (zed (1- a) (1- b) (1- c))))))
      (local
       (defthm zed_check
         (implies
          (zed_terminates a b c)
          (equal (zed a b c)
                 (let ((z (+ a b c)))
                   (if (zed-test z) (+ a b c)
                     (zed (1- a) (1- b) (1- c))))))))
      ))

    ;; here it detects that the recursive call is governed by zed-test
    ;; and it produces a resonable induction scheme to go along with
    ;; it.
    (local
     (encapsulate
         ()
       (local
        (def::un zed (a b c)
          (cons (if (zed-test a) (zed (1- a) b c) (+ a b c))
                (list a b c))))
       (local
        (defthm zed_check
          (implies
           (zed_terminates a b c)
           (equal (zed a b c)
                  (cons (if (zed-test a) (zed (1- a) b c) (+ a b c))
                        (list a b c))))))
       ))

    (local
     (encapsulate
      ()
      (local
       (def::un zzed (a b c)
         (if (zed-test c) (if (zed-test a) b (zzed (1+ a) b c))
           (zzed (if (zed-test a) b (zzed (1+ a) b c))
                 (if (zed-test (if (zed-test a) b (zzed (1+ a) b c)))
                     c
                   (zzed (1+ a) (1+ b) (1+ c)))
                 (if (zed-test b)
                     (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) c
                       (zzed (1+ a) (1+ b) (1+ c)))
                   (zzed (1+ a) (1- b) c))))))
      (local
       (defthm zzed-check
         (implies
          (zzed_terminates a b c)
          (equal (zzed a b c)
                 (if (zed-test c) (if (zed-test a) b (zzed (1+ a) b c))
                   (zzed (if (zed-test a) b (zzed (1+ a) b c))
                         (if (zed-test (if (zed-test a) b (zzed (1+ a) b c)))
                             c
                           (zzed (1+ a) (1+ b) (1+ c)))
                         (if (zed-test b)
                             (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) c
                               (zzed (1+ a) (1+ b) (1+ c)))
                           (zzed (1+ a) (1- b) c))))))))
       ))

    (local
     (encapsulate
      ()
      (local
       (def::un zed (a b c)
         (let ((x (if (zed-test a) b (zed (1+ a) b c))))
           (let ((y (if (zed-test x) c (zed (1+ a) (1+ b) (1+ c)))))
             (let ((z (if (zed-test b) y (zed (1+ a) (1- b) c))))
               (if (zed-test c) x
                 (zed x y z)))))))
      (local
       (defthm zed-check
         (implies
          (zed_terminates a b c)
          (equal (zed a b c)
                 (let ((x (if (zed-test a) b (zed (1+ a) b c))))
                   (let ((y (if (zed-test x) c (zed (1+ a) (1+ b) (1+ c)))))
                     (let ((z (if (zed-test b) y (zed (1+ a) (1- b) c))))
                       (if (zed-test c) x
                         (zed x y z)))))))))
      ))

    ))))

#|
(defun insert-arg-case (case val cond2)
  (if (consp cond2)
      (let ((cond (car cond2)))
        (cons (cons (syn::and case (car cond)) (cons val (cadr cond)))
              (insert-arg-case case val (cdr cond2))))
    nil))

(defun merge-arg-conds (cond1 cond2)
  (if (consp cond1)
      (let ((cond (car cond1)))
        (let ((case (car cond))
              (val  (cadr cond)))
          (let ((cond2 (insert-arg-case case val cond2)))
            (merge-arg-conds (cdr cond1) cond2))))
    cond2))

;; - Lift guarded recursive "argument" conditions.
;;
;; - Define termination, measure, and induction bodies.
;;
;; - Why do we have to do guard verification to get
;;   the executable body?


(skip-proofs
 (defun zoo (n)
   (if (zp n) n
     (zoo (zoo (1- n))))))

(defthm zoo-n
  (equal (zoo n) (if (zp n) n 0)))

(defun zoo_measure (n)
  (if (zp n) (o)
    (+ (zoo_measure (1- n))
       (zoo_measure (zoo (1- n))))))

(defun hoo (n)
  (declare (xargs :measure (zoo_measure n)))
  (if (zp n) n
    (hoo (hoo (1- n)))))
|#

#|
(defun foo-spec ()
  `(3 (0) (1) (2)))

(defun foo-step (key args gensym::vals)
  (let ((n (car args)))
    (case key
          (3 (IF (TEST '1 N)
                 (IF (TEST '2 N)
                     (VAL '0 GENSYM::VALS)
                     (VAL '1 GENSYM::VALS))
                 (VAL '2 GENSYM::VALS)))
          (0 (LIST (STP '3 N)))
          (1 (LIST (STP '4 N)))
          (2 (LIST (STP '5 N)))
          (t nil))))


(mutual-recursion


 (defun spec-interpreter (args spec)
   (declare (xargs :measure (acl2-count spec)))
   (if (consp spec)
       (let ((key (car spec)))
         (let ((vals (spec-list-interpreter args (cdr spec))))
           (foo-step key args vals)))
     nil))


 (defun spec-list-interpreter (args spec)
   (declare (xargs :measure (acl2-count spec)))
   (if (consp spec)
       (cons (let ((args (spec-interpreter args (car spec))))
               (foo (car args)))
             (spec-list-interpreter args (cdr spec)))
     nil))

 )

;;
;; Now, just replace "foo" in the interpreter with "interpreter"
;;
(defun interpreter (args)
  (spec-interpreter args (foo-spec)))

;;
;; This is a very exciting result.
;;
(defthm spec-interpreter-reduction
  (implies
   (NOT (TEST '0 (car args)))
   (equal (spec-interpreter args (foo-spec))
          (let ((n (car args)))
            (if (test 0 n) (stp 0 n)
              (if (test 1 n)
                  (if (test 2 n) (foo (stp 3 n))
                    (foo (stp 4 n)))
                (foo (stp 5 n)))))))
  :hints (("Goal" :in-theory (enable foo-step))))

(thm
  (equal (if (if ifcase ifrec ifbase)
             (if thencase thenrec thenbase)
           (if elsecase elserec elsebase))

         (if (or ifcase
                 (and (not ifcase) ifbase thencase)
                 (and (not ifcase) (not ifbase) elsecase))
             (if (and ifcase ifrec)
                 (if thencase thenrec thenbase)
               (if (and ifcase (not ifrec))
                   (if elsecase elserec elsebase)
                 (if (and (not ifcase) ifbase) thenrec elserec)))
           (if (and (not ifcase) ifbase) thenbase elsebase))))

  )

(thm
  (equal (if (if ifcase ifrec ifbase)
             (if thencase thenrec thenbase)
           (if elsecase elserec elsebase))

         (if ifcase
             (if ifrec
                 (if thencase thenrec thenbase)
               (if elsecase elserec elsebase))
           (if (or (and ifbase thencase)
                   (and ifbase elsecase))
               (if thencase thenrec elserec)
             (if thencase elsebase thenbase)))))

dag
;; It would be nice if we isolated every unique call
;; (lifted if's out of function applications).



;; (extract-base-fn 'fn `(cons a (if (test a) (fn a b) (goo c))))

#+joe
(extract-base-fn 'BINARY-+
                 '((LAMBDA (A C AB)
                           (CONS A
                                 (IF (NATP A)
                                     (BINARY-+ A AB)
                                     (UNARY-- C))))
                   (CONS X Y)
                   C AB))

;; We need to identify:
;; - tail recursive calls.
;; - other recursive calls.
;; - base cases.

;; We need to lift if's over functions when those if's
;; govern recursive calls.

;; We need to treat conditions that make recursive calls

;; (if (test (frec zed)) a b)

;; - the recursive base case.
;; (goo-done args)
;;
;; - what do we do on the base case
;; (goo-base-step args)
;;
;; - these two kinda work together ..
;; (goo-comp-step fn args vals)
;; (goo-step-spec fn args vals)

|#
