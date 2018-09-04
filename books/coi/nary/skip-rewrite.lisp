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

(in-package "ACL2")

(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-unhidden
  (implies
   (syntaxp (or (not (consp x)) (not (equal (car x) 'hide))))
   (equal (unhide x) x)))

(defthm unhide-hide
  (equal (unhide (hide x))
         x)
  :hints (("Goal" :expand (hide x))))

(defun fix-list (list)
  (if (consp list)
      (cons (car list) (fix-list (cdr list)))
    nil))

(defthm pairlis$-fix-list
  (equal (pairlis$ x (fix-list y))
         (pairlis$ x y)))

; Delete this and use kwote-lst instead, once we move kwote-lst from
; translate.lisp to axioms.lisp and add a true-listp guard and endp check.
(defun quote-list (list)
  (declare (type t list))
  (if (consp list)
      (cons `(quote ,(car list))
            (quote-list (cdr list)))
    nil))

(defevaluator unhide-eval unhide-eval-list
  (
   (hide x)
   (unhide x)
   )
  )

(defun pseudo-termp-key (arg term)
  (declare (type t arg term))
  (if arg (pseudo-term-listp term)
    (pseudo-termp term)))

(defun nary-beta-reduce (arg term keys vals)
  (declare (type (satisfies true-listp) keys vals))
  (declare (xargs :guard (pseudo-termp-key arg term)))
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (nary-beta-reduce nil (car term) keys vals)
              (nary-beta-reduce arg (cdr term) keys vals)))))
   (t
    (cond
     ((and (symbolp term) term)
      (if (member term keys)
          (cdr (assoc-eq term (pairlis$ keys vals)))
        '(quote nil)))
     ((atom term) term)
     ((eq (car term) 'quote) term)
     ((consp (car term))
      (cons (car term) (nary-beta-reduce t (CDR term) keys vals)))
     ((equal (car term) 'hide)
      (list 'hide (nary-beta-reduce nil (cadr term) keys vals)))
     ((equal (car term) 'unhide)
      (list 'unhide (nary-beta-reduce nil (cadr term) keys vals)))
     (t
      (cons (car term) (nary-beta-reduce t (cdr term) keys vals)))))))

(defun unhide-eval-key (arg term alist)
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (unhide-eval-key nil (car term) alist)
              (unhide-eval-key arg (cdr term) alist)))))
   (t
    (cond
     ((and (symbolp term) term)
      (cdr (assoc-eq term alist)))
     ((eq (car term) 'quote) (CAR (CDR term)))
     ((consp (car term))
      (unhide-eval (CAR (CDR (CDR (CAR term)))) (PAIRLIS$ (CAR (CDR (CAR term)))
                                                          (UNHIDE-EVAL-key t (CDR term) alist))))
     (t (unhide-eval term alist))))))

(defthmd unhide-eval-key-reduction
  (equal (unhide-eval-key arg term alist)
         (if arg (unhide-eval-list term alist)
           (unhide-eval term alist))))

(defun wf-beta-term (arg term)
  (cond
   (arg
    (cond
     ((endp term) t)
     (t (and (wf-beta-term nil (car term))
             (wf-beta-term arg (cdr term))))))
   (t
    (cond
     ((symbolp term) t)
     ((atom term) nil)
     ((eq (car term) 'quote) t)
     ((consp (car term))
      (wf-beta-term t (CDR term)))
     ((equal (car term) 'hide)
      (wf-beta-term nil (cadr term)))
     ((equal (car term) 'unhide)
      (wf-beta-term nil (cadr term)))
     (t (wf-beta-term t (cdr term)))))))

(defthm append-nil-fix
  (equal (unhide-eval-list (append list nil) a1)
         (unhide-eval-list list a1)))

(defthm late-binding-reduction
  (implies
   (equal (len keys) (len vals))
   (equal (unhide-eval (cdr (assoc-eq term (pairlis$ keys vals))) a1)
          (if (member term keys)
              (cdr (assoc-eq term (pairlis$ keys (unhide-eval-list vals a1))))
            (unhide-eval nil a1)))))

(defthm assoc-eq-pairlis$-non-member
  (implies
   (not (member term keys))
   (equal (assoc-eq term (pairlis$ keys vals))
          nil)))

;; DAG -- odd that we need these now, but not before.
(defthm car-quote-list
  (equal (car (quote-list list))
         (if (consp list) `(quote ,(car list)) nil)))

(defthm car-unhide-eval-list
  (equal (car (unhide-eval-list term a))
         (if (consp term) (unhide-eval (car term) a) nil)))

(defthm consp-unhide-eval-list
  (iff (consp (unhide-eval-list term a))
       (consp term)))

(defthmd unhide-eval-key-nary-beta-reduce
  (implies
   (and
    (wf-beta-term arg term)
    (equal (len keys) (len vals)))
   (equal (unhide-eval-key arg (nary-beta-reduce arg term keys vals) a1)
          (unhide-eval-key arg term (pairlis$ keys
                                              (unhide-eval-key t vals a1)))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :do-not-induct t
            :induct (nary-beta-reduce arg term keys vals)
            :expand (:free (x) (hide x))
            :in-theory (e/d (unhide-eval-constraint-0 unhide-eval-key-reduction)
                            nil))))

;; does lambda-expr need to do anything interesting in the case of
;; a lambda application?
(defun para-lambda-expr-p (term keys vals expr)
  (declare (type t term))
  (and (consp expr)
       (consp (car expr))
       (equal (len (car expr)) 3)
       (equal (cadr (car expr)) keys)
       (equal (caddr (car expr)) term)
       (equal (cdr expr) vals)))

(defun para-map-lambda-p (term keys vals expr)
  (declare (type t term))
  (if (consp term)
      (and (consp expr)
           (para-lambda-expr-p (car term) keys vals (car expr))
           (para-map-lambda-p (cdr term) keys vals (cdr expr)))
    (not (consp expr))))

(defun para-lambda-expr-key-p (arg term keys vals expr)
  (declare (type t term))
  (if arg (para-map-lambda-p term keys vals expr)
    (para-lambda-expr-p term keys vals expr)))

(defthm unhide-eval-key-lambda-expr
  (implies
   (para-lambda-expr-key-p arg term keys vals expr)
   (equal (unhide-eval-key arg expr a1)
          (unhide-eval-key arg term (pairlis$ keys (unhide-eval-key t vals a1)))))
  :hints (("Goal" :in-theory (enable unhide-eval-key-reduction))))

(defun lambda-expr-p (term)
  (declare (type t term))
  (and (consp term)
       (consp (car term))
       (equal (len (car term)) 3)))

(defthmd lambda-expr-p-to-para-lambda-expr-key-p
  (equal (lambda-expr-p term)
         (para-lambda-expr-key-p nil (CAR (CDR (CDR (CAR term)))) (CAR (CDR (CAR term))) (cdr term) term))
  :hints (("goal" :in-theory (enable lambda-expr-p para-lambda-expr-key-p))))

(in-theory (disable lambda-expr-p para-lambda-expr-key-p))

(defthmd unhide-eval-lambda-expr-helper
  (implies
   (lambda-expr-p term)
   (equal (unhide-eval-key nil term a1)
          (unhide-eval-key nil (CAR (CDR (CDR (CAR term))))
                           (pairlis$ (CAR (CDR (CAR term)))
                                     (unhide-eval-key t (cdr term) a1)))))
  :hints (("Goal" :in-theory (e/d (lambda-expr-p-to-para-lambda-expr-key-p) (unhide-eval-key)))))

(defthm unhide-eval-lambda-expr
  (implies
   (lambda-expr-p term)
   (equal (unhide-eval term a1)
          (unhide-eval (CAR (CDR (CDR (CAR term))))
                       (pairlis$ (CAR (CDR (CAR term)))
                                 (unhide-eval-list (cdr term) a1)))))
  :hints (("Goal" :use unhide-eval-lambda-expr-helper
           :in-theory (enable unhide-eval-key-reduction))))

(defthm pseudo-termp-key-implies-wf-beta-term
  (implies
   (pseudo-termp-key arg term)
   (wf-beta-term arg term))
  :hints (("Goal" :induct (wf-beta-term arg term))))

(defthm unhide-eval-nary-beta-reduce
  (implies
   (and
    (wf-beta-term nil term)
    (equal (len keys) (len vals)))
   (equal (unhide-eval (nary-beta-reduce nil term keys vals) a1)
          (unhide-eval term (pairlis$ keys (unhide-eval-list vals a1)))))
  :hints (("Goal" :use (:instance unhide-eval-key-nary-beta-reduce
                                  (arg nil))
           :in-theory (enable unhide-eval-key-reduction))))

(defthm unide-eval-to-nary-beta-reduce
  (implies
   (and
    (lambda-expr-p term)
    (pseudo-termp term))
   (equal (unhide-eval term a1)
          (unhide-eval (nary-beta-reduce nil (CAR (CDR (CDR (CAR term))))
                                         (CAR (CDR (CAR term)))
                                         (cdr term)) a1))))

(defun nary-beta-reduce-lambda (term)
  (declare (type (satisfies lambda-expr-p) term)
           (type (satisfies pseudo-termp) term)
           (xargs :guard-hints (("Goal" :in-theory (enable lambda-expr-p)))))
  (nary-beta-reduce nil (CAR (CDR (CDR (CAR term))))
                    (CAR (CDR (CAR term)))
                    (cdr term)))

(defun unhide-p (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'unhide)
       (consp (cdr term))
       (null (cddr term))))

(defun hide-p (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'hide)
       (consp (cdr term))
       (null (cddr term))))

(defun nary-beta-reduce-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (hide-p term)
      (let ((arg (cadr term)))
        (if (lambda-expr-p arg)
            `(hide ,(nary-beta-reduce-lambda arg))
          term))
    term))

(defthmd nary-*meta*-beta-reduce-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (nary-beta-reduce-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (hide))))


(defun nary-unhide-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (unhide-p term)
      (let ((arg (cadr term)))
        (if (hide-p arg)
            (let ((arg (cadr arg)))
              (if (lambda-expr-p arg)
                  `(unhide (hide ,(nary-beta-reduce-lambda arg)))
                term))
          term))
    term))

;; We cannot turn this into a :meta rule because of our
;; additional evaluator constraints.
;;
;; But we can at least try it out:
;;   (nary-unhide-hide-wrapper '(unhide (hide ((lambda (x y z) (+ x y)) (foo a) (goo b) (foo (quote 3))))))
;;     => '(+ (FOO A) (GOO B))
;;
(defthm nary-*meta*-unhide-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (nary-unhide-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (unhide))))

(in-theory (disable unhide))

(defmacro skip-rewrite (x)
  `(unhide (hide ,x)))

(in-theory (disable unhide))

(local
(encapsulate
    ()

  ;; You can see these rules "doing their job" if you
  ;; watch this proof (and monitor nary-unhide-hide-wrapper)

  (defun foo (x) (if (zp x) 2 (foo (1- x))))

  (defthm open-foo
    (implies
     (and
      (not (zp x))
      (equal v (1- x)))
     (equal (foo x) (skip-rewrite (foo v)))))

  (defthm foo-0
    (equal (foo 0) 2))

  (in-theory (disable foo (foo)))

  ;;(trace$ nary-unhide-hide-wrapper)

  (defthm foo-10
    (equal (foo 10) 2))

  ))

#|

(defund fn (a b)
  (if (consp a)
      (fn (cdr a) b)
    (list (cons a a) b)))

(ENCAPSULATE
  (((UNHIDE-EVAL2 * *) => *)
   ((UNHIDE-EVAL2-LIST * *) => *))

  (SET-INHIBIT-WARNINGS "theory")
; Change *DEFEVALUATOR-FORM-BASE-THEORY* in sources as indicated here:
  (LOCAL (IN-THEORY (union-theories
                     '(fix-list quote-list pairlis$-fix-list)
                     *DEFEVALUATOR-FORM-BASE-THEORY*)))
  (LOCAL
    (MUTUAL-RECURSION
         (DEFUN UNHIDE-EVAL2 (X A)
                (DECLARE (XARGS :VERIFY-GUARDS NIL
                                :MEASURE (ACL2-COUNT X)
                                :WELL-FOUNDED-RELATION O<
                                :MODE :LOGIC))
                (COND ((and x (SYMBOLP X)) (CDR (ASSOC-EQ X A)))
                      ((ATOM X) NIL)
                      ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
                      ((CONSP (CAR X))
                       (UNHIDE-EVAL2 (CAR (CDR (CDR (CAR X))))
                                    (PAIRLIS$ (CAR (CDR (CAR X)))
                                              (UNHIDE-EVAL2-LIST (CDR X) A))))
                      ((EQUAL (CAR X) 'HIDE)
                       (HIDE (UNHIDE-EVAL2 (CAR (CDR X)) A)))
                      ((EQUAL (CAR X) 'UNHIDE)
                       (UNHIDE (UNHIDE-EVAL2 (CAR (CDR X)) A)))
                      ((EQUAL (CAR X) 'FN)
                       (FN (UNHIDE-EVAL2 (CAR (CDR X)) A) (UNHIDE-EVAL2 (CAR (CDDR X)) A)))
                      (T NIL)))
         (DEFUN UNHIDE-EVAL2-LIST (X-LST A)
                (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
                                :WELL-FOUNDED-RELATION O<))
                (COND ((ENDP X-LST) nil)
                      (T (CONS (UNHIDE-EVAL2 (CAR X-LST) A)
                               (UNHIDE-EVAL2-LIST (CDR X-LST) A)))))))
  (local
   (defthm unhide-eval2-list-quote-unhide-eval2-list
     (equal (unhide-eval2-list (quote-list args) a)
            (fix-list args)))) ; by induction on (quote-list args)
  ;; DAG - New constraint
  #+joe
  (defthmd unhide-eval2-constraint-0
    (implies
     (and (consp term)
          (syntaxp (not (equal a *nil*))) ; prevent looping
          (not (equal (car term) 'quote)))
     (equal (unhide-eval2 term a)
            (unhide-eval2 (cons (car term)
                                (quote-list (unhide-eval2-list (cdr term) a)))
                          nil)))
    :hints (("Goal"
             :expand ((:free (x) (hide x))
                      (unhide-eval2 term a))
             :in-theory (disable (:executable-counterpart unhide-eval2)))))
  (DEFTHM UNHIDE-EVAL2-CONSTRAINT-1
          (IMPLIES (SYMBOLP X)
                   (EQUAL (UNHIDE-EVAL2 X A)
                          (and x (CDR (ASSOC-EQ X A))))))
  (DEFTHM UNHIDE-EVAL2-CONSTRAINT-2
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
                   (EQUAL (UNHIDE-EVAL2 X A) (CADR X))))
  (DEFTHM
     UNHIDE-EVAL2-CONSTRAINT-3
     (IMPLIES (AND (CONSP X) (CONSP (CAR X)))
              (EQUAL (UNHIDE-EVAL2 X A)
                     (UNHIDE-EVAL2 (CADDAR X)
                                  (PAIRLIS$ (CADAR X)
                                            (UNHIDE-EVAL2-LIST (CDR X) A))))))
  (DEFTHM UNHIDE-EVAL2-CONSTRAINT-4
          (IMPLIES (NOT (CONSP X-LST))
                   (EQUAL (UNHIDE-EVAL2-LIST X-LST A) NIL)))
  (DEFTHM UNHIDE-EVAL2-CONSTRAINT-5
          (IMPLIES (CONSP X-LST)
                   (EQUAL (UNHIDE-EVAL2-LIST X-LST A)
                          (CONS (UNHIDE-EVAL2 (CAR X-LST) A)
                                (UNHIDE-EVAL2-LIST (CDR X-LST) A)))))
  (DEFTHM UNHIDE-EVAL2-constraint-8
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'HIDE))
                   (EQUAL (UNHIDE-EVAL2 X A)
                          (HIDE (UNHIDE-EVAL2 (CADR X) A)))))
  (DEFTHM UNHIDE-EVAL2-constraint-9
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'UNHIDE))
                   (EQUAL (UNHIDE-EVAL2 X A)
                          (UNHIDE (UNHIDE-EVAL2 (CADR X) A)))))
  (DEFTHM UNHIDE-EVAL2-constraint-10
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'FN))
                   (EQUAL (UNHIDE-EVAL2 X A)
                          (FN (UNHIDE-EVAL2 (CAR (CDR X)) A)
                              (UNHIDE-EVAL2 (CAR (CDDR X)) A)))))
  )

#-joe
(skip-proofs
(defthmd unhide-eval2-constraint-0
    (implies
     (and (consp term)
          (syntaxp (not (equal a *nil*))) ; prevent looping
          (not (equal (car term) 'quote)))
     (equal (unhide-eval2 term a)
            (unhide-eval2 (cons (car term)
                                (quote-list (unhide-eval2-list (cdr term) a)))
                          nil))))
)

(defthm *meta*-unhide-hide2
  (implies
   (pseudo-termp term)
   (equal (unhide-eval2 term a)
          (unhide-eval2 (nary-unhide-hide-wrapper term) a)))
  :hints (("Goal" :use (:functional-instance *meta*-unhide-hide
                                             (UNHIDE-EVAL UNHIDE-EVAL2)
                                             (UNHIDE-EVAL-LIST UNHIDE-EVAL2-LIST))
           :expand (:Free (x) (hide x)))
          (and stable-under-simplificationp
               '(:in-theory (enable UNHIDE-EVAL2-CONSTRAINT-0))))
;  :rule-classes ((:meta :trigger-fns (unhide))))
  )
|#
