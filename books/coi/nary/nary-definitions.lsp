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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; nary-definitions.lisp
;; John D. Powell
;(in-package "NARY")

;;
;; This file isolates nary definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the nary book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

;; (defthm COMMUTATIVITY-2-OF-+
;;   (equal (+ x (+ y z))
;;          (+ y (+ x z))))

;; (defthm integerp-*
;;   (implies
;;    (and (integerp x) (integerp y))
;;    (integerp (* x y))))

;; (in-theory (disable mod))

(in-theory (disable mod))

(defthm plus-fold-constants
  (implies
   (syntaxp (quotep c))
   (equal (+ a (+ (* c a) b))
          (+ (* (+ c 1) a) b))))

(in-theory (disable loghead))

(defthm loghead-theorem
  (implies (and (integerp x) (integerp f))
           (equal (loghead 32 (+ (* 4294967295 (loghead 32 (* x f)))
                                 (* x f)
                                 (* x (loghead 32 (* x f)))))
                  (loghead 32 (* x x f)))))

;;
;; Works much better if we disable LOGHEAD-UPPER-BOUND and MOD-X-Y-=-X+Y
;;

(defthm loghead-mod-theorem
  (implies (and (integerp x) (integerp f))
           (equal (loghead 32 (+ (* 4294967295 (loghead 32 (* x f)))
                                 (* (mod x (expt 2 32)) f)
                                 (* x (loghead 32 (* x f)))))
                  (loghead 32 (* x x f)))))


(in-theory (disable mod))

(defun loghead-equivp (x y n)
  (equal (loghead n x)
         (loghead n y)))

(defthm loghead-cong
  (implies
   (bind-contextp (x (equal a (loghead-ctx x :n n))))
   (equal (loghead n x)
          (loghead n a))))

(defthm loghead-+-cong
  (implies
   (and
    (integerp x)
    (integerp y)
    (bind-contextp ((x (equal a (loghead-ctx x :n n)))
                    (y (equal b (loghead-ctx y :n n)))))
    (integerp a)
    (integerp b))
   (loghead-equiv :lhs (+ x y)
                  :rhs (skip-rewrite (+ a b)))))

;; Currently the specification of a new equivalence relation can be
;; used to extend ACL2's notion of equivalence, .
;;
;; (defequiv (set-equal x y))
;;

;;(include-book "../syntax/syntax")

(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-unhidden
  (implies
   (syntaxp (or (not (consp x)) (not (equal (car x) 'hide))))
   (equal (unhide x) x)))

(defthm unide-hide
  (equal (unhide (hide x))
         x)
  :hints (("Goal" :expand (hide x))))

(in-theory (disable unhide))

(defun ith (i list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (car list)
        (ith (1- i) (cdr list)))
    nil))

(defun remove-ith (i list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (cdr list)
        (cons (car list) (remove-ith (1- i) (cdr list))))
    nil))

(defun replace-ith (i v list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (cons v (cdr list))
        (cons (car list) (replace-ith (1- i) v (cdr list))))
    nil))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Following are some functions that query some undocumented portions
;; of the mfc data structure looking for recursive calls of a
;; particular theorem.
;;
;; Unfortunately, the correct behavior of the final "non-recursive"
;; predicate relies on :brr t (sigh)
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun rewrite-rhs? (element)
  (and (consp element)
       (equal (car element) 'REWRITE)
       (consp (cdr element))
       (equal (cadr element) 'RHS)))

(defun rewrite-with-lemma? (lemma element)
  (and (consp element)
       (equal (car element) 'REWRITE-WITH-LEMMA)
       (member lemma (ith 4 element))))

(defun rewriting-rhs? (lemma stack)
  (and (consp stack)
       (consp (cdr stack))
       (rewrite-rhs? (cadr stack))
       (consp (cddr stack))
       (rewrite-with-lemma? lemma (caddr stack))))

;; <<<<<<< nary.lisp
;; (defun print-gstack (state)
;; =======
;; ;; jcd - added nil to cw-gstack-fn call, for ACL2 v2.9.2
;; (defun print-gstack (mfc state)
;; >>>>>>> 1.2
;;   (declare (xargs :mode :program))
;; <<<<<<< nary.lisp
;;   ;(prog2$
;;   ; (MFC-ANCESTORS mfc)
;;    (cw-gstack-fn (term-evisc-tuple t state)))
;;   ;)
;; =======
;;   (prog2$
;;    (MFC-ANCESTORS mfc)
;;    (cw-gstack-fn (term-evisc-tuple t state) nil)))
;; >>>>>>> 1.2

(defun non-recursive (lemma mfc state)
  (declare (xargs :mode :program)
           (ignore lemma mfc state)
           )
;  (prog2$
;   (cw "attempting lemma ~p0 ~%" lemma)
;   (prog2$
;    (cw "~p0 ~%" (len mfc))
;   (prog2$
;    (print-gstack state)
;    (if (rewriting-rhs? lemma (ith 9 mfc)) nil
      `((ok . 't)))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Support for defcontext, defcong+
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun symbol-term (term)
  (declare (type t term))
  (if (consp term)
      (if (consp (car term))
          (and (symbol-term (car term))
               (symbol-term (cdr term)))
        (and (symbolp (car term))
             (symbol-term (cdr term))))
    (symbolp term)))

(defun term-contains (var term)
  (declare (type t var term))
  (if (consp term)
      (if (consp (car term))
          (or (term-contains var (car term))
              (term-contains var (cdr term)))
        (or (equal var (car term))
            (term-contains var (cdr term))))
    (equal var term)))

(defun non-consp-list (list)
  (declare (type t list))
  (or (not (consp list))
      (and (not (consp (car list)))
           (non-consp-list (cdr list)))))

(defun equiv-exp (val term)
  (declare (type t val term))
  (and
   (consp term)
   (symbolp (car term))
   ;; May now be any equivalence
   ;(equal (car term) 'equal)
   (consp (cdr term))
   (symbolp (cadr term))
   (consp (cddr term))

   (term-contains val (caddr term))

   ;; Because we don't currently support evaluation of terms we need
   ;; to make sure that the user doesn't hang themselves ..
   ;; (not (cw "Bound: ~p0~%" (caddr term)))
   (non-consp-list (caddr term))

   ))

(defun wf-cong (cong)
  (declare (type t cong))
  (and (consp cong)
       (symbolp (car cong))
       (consp (cdr cong))
       (equiv-exp (car cong) (cadr cong))))

(defun wf-cong-list (congs)
  (declare (type t congs))
  (if (consp congs)
      (and (wf-cong (car congs))
           (wf-cong-list (cdr congs)))
    (null congs)))

(defun in-pkg-of (symbol witness)
  (eql (intern-in-package-of-symbol (symbol-name symbol) witness) symbol))

(defun safe-witness (symbol)
  (declare (type symbol symbol))
  (if (equal (symbol-package-name symbol) (symbol-package-name 'common-lisp::mod)) 'acl2::defthm symbol))

(defthm symbolp-safe-witness
  (implies
   (symbolp symbol)
   (symbolp (safe-witness symbol))))

(in-theory (disable safe-witness))

(defun safe-symbol (lst witness)
  (declare (xargs :mode :program))
  (packn-pos lst (safe-witness witness)))

(defun replace-var-term (ovar nvar term)
  (if (consp term)
      (if (consp (car term))
          (cons (replace-var-term ovar nvar (car term))
                (replace-var-term ovar nvar (cdr term)))
        (if (eql ovar (car term))
            (cons nvar (replace-var-term ovar nvar (cdr term)))
          (cons (car term) (replace-var-term ovar nvar (cdr term)))))
    (if (eql ovar term)
        nvar
      term)))

(defun replace-cong-term (cong term)
  (let* ((ovar (car cong))
         (eex  (cadr cong))
         (nvar (cadr eex)))
    (replace-var-term ovar nvar term)))

(defun replace-cong-terms (congs term)
  (if (consp congs)
      (let ((term (replace-cong-term (car congs) term)))
        (replace-cong-terms (cdr congs) term))
    term))

(defun prefix-list (fn oargs)
  (declare (xargs :mode :program))
  (if (consp oargs)
      (cons (safe-symbol (list fn "-" (car oargs)) (car oargs))
            (prefix-list fn (cdr oargs)))
    nil))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; The defcontext macro just defines a set of helper functions that we
;; need in order to use a particular fix function (or "context")
;; within a defcong+ theorem.
;;
;; The expression:
;;
;; (defcontext (mod x a) 1)
;;
;; tells us that we will use the "mod" function to fix our values and
;; that every position but the 1st position is considered "context".
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

;;
;; Is (dequote) needed??
;;

(defun dequote (term)
  (if (consp term)
      (if (equal (car term) 'quote)
          (cadr term)
        term)
    term))

(defun compare-args-to-term (list1 index position term)
  (if (consp list1)
      (if (equal position index)
          (compare-args-to-term (cdr list1) (1+ index) position term)
        (cons `(equal (dequote ,(car list1)) (dequote (ith ,index ,term)))
              (compare-args-to-term (cdr list1) (1+ index) position term)))
    nil))

(defun defcontext-fn (term position)
  (declare (xargs :mode :program))
  (let* ((fix-fn     (car term))
         (args       (cdr term))
         (nargs      (prefix-list fix-fn args))
         (var        (ith position term))
         (fn-witness (safe-witness fix-fn))
         (fix-fn-unfix (safe-symbol (list fix-fn "_UNFIX") fn-witness))
         (fix-fn-unfix-check (safe-symbol (list fix-fn "_UNFIX_CHECK") fn-witness))
         (fix-fn-unfix-check-reduction-1 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_1") fn-witness))
         (fix-fn-unfix-check-reduction-2 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_2") fn-witness))
         (fix-fn-unfix-check-reduction-3 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_3") fn-witness))
         (wrapped-var      (safe-symbol (list var "-wrapped") var))
         (wrapped-var?     (safe-symbol (list var "-wrapped?") var))
         (wrapped-var-hyps (safe-symbol (list var "-wrapped-hyps") var))
         )
    `(encapsulate
      ()

      (defun ,fix-fn-unfix (term ,@args wrapped unwrap hyp)
        (declare (ignore ,(ith (1- position) args)))
        (if (and (equal (len term) (1+ ,(len args)))
                 (equal (car term) ',fix-fn)
                 ,@(compare-args-to-term args 1 position 'term))
            `((,wrapped . `t)
              (,unwrap  . ,(ith ,position term))
              (,hyp     . `t))
          `((,wrapped . `nil)
            (,unwrap  . ,term)
            (,hyp     . `t))))

      (defun ,fix-fn-unfix-check (,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs)
        (declare (ignore ,wrapped-var-hyps ,(ith (1- position) nargs)))
        (if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@(replace-ith (1- position) var nargs)))
          (equal ,wrapped-var ,var)))

      (defthm ,fix-fn-unfix-check-reduction-1
        (,fix-fn-unfix-check t (,fix-fn ,@(replace-ith (1- position) var nargs))
                             ,var ,wrapped-var-hyps ,@nargs))

      (defthm ,fix-fn-unfix-check-reduction-2
        (,fix-fn-unfix-check nil ,wrapped-var ,wrapped-var ,wrapped-var-hyps ,@nargs))

      (defthm ,fix-fn-unfix-check-reduction-3
        (implies
         (in-conclusion-check (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs))
         (equal (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs)
                (if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@(replace-ith (1- position) var nargs)))
                  (equal ,wrapped-var ,var)))))

      (in-theory (disable ,fix-fn-unfix-check))

      )))

(defun locate (val list)
  (declare (type t val list))
  (if (consp list)
      (if (equal val (car list)) 0
        (1+ (locate val (cdr list))))
    0))


(defund imp (a x)
  (if x t a))

(defthm implies-imp
  (implies
   a
   (imp a x))
  :hints (("goal" :in-theory (enable imp))))

(defun appears-in-clause (fn args fapp clause)
  (declare (type t fn args clause))
  (if (consp clause)
      (if fapp
          (or (and (equal fn (car clause))
                   (equal args (cdr clause)))
              (appears-in-clause fn args nil (cdr clause)))
        (or (appears-in-clause fn args t (car clause))
            (appears-in-clause fn args nil (cdr clause))))
    nil))

(defun in-conclusion-fn (term mfc state)
  (declare (ignore state)
           (type t term))
  (if (not (acl2::mfc-ancestors mfc))
      (and (if (consp term) (appears-in-clause (car term) (cdr term) nil (acl2::mfc-clause mfc)) t)
           (list (cons 'in-conclusion-free-variable `(quote t))))
    nil))

(defun quote-list (list)
  (declare (type t list))
  (if (consp list)
      (cons `(quote ,(car list))
            (quote-list (cdr list)))
    nil))

(defun equal_len (n list)
  (declare (type (integer 0 *) n))
  (if (consp list)
      (if (zp n) nil
        (equal_len (1- n) (cdr list)))
    (and (null list) (= n 0))))

(defun syn__consp (term)
  (declare (type t term))
  (and
   (equal_len 3 term)
   (equal (car term) 'cons)))

(defun syn__cdr (term)
  (declare (type (satisfies syn__consp) term))
  (caddr term))

(defun syn__car (term)
  (declare (type (satisfies syn__consp) term))
  (cadr term))

(defun syn__quotep (term)
  (declare (type t term))
  (and (equal_len 2 term)
             (equal (car term) 'quote)))

(defun syn__dequote (term)
  (declare (type (satisfies syn__quotep) term))
  (cadr term))

(defun delist (args)
  (declare (type t args))
  (cond
   ((syn__consp args)
    (cons (syn__car args)
          (delist (syn__cdr args))))
   ((syn__quotep args)
    (quote-list (syn__dequote args)))
   (t
    nil)))

(defun check-term (negated expr term)
  (declare (type t term))
  (cond
   ((equal negated :negated)
    (equal expr term))
   ((equal negated :any)
    (or (equal expr term)
        (and (consp term)
             (equal (car term) 'not)
             (consp (cdr term))
             (equal expr (cadr term)))))
   (t
    (and (consp term)
         (equal (car term) 'not)
         (consp (cdr term))
         (equal expr (cadr term))))))

(defun member-of-clause (negated expr clause)
  (declare (type t clause))
  (if (consp clause)
      (let ((term (car clause)))
        (or (check-term negated expr term)
            (member-of-clause negated expr (cdr clause))))
    nil))

(defun in-conclusion-check-fn (top fn args mfc state)
  (declare (ignore state)
           (type t args))
  (if (not (acl2::mfc-ancestors mfc))
      (let ((args (delist args)))
        (let ((clause (mfc-clause mfc)))
          (and (if (not top) (appears-in-clause fn args nil clause)
                 (if (and (equal fn 'not)
                          (consp args))
                     (member-of-clause :negated (car args) clause)
                   (member-of-clause top (cons fn args) clause)))
               (list (cons 'in-conclusion-free-variable `(quote t))))))
    nil))

(defun backchaining-check-fn (mfc state)
  (declare (ignore state))
  (if (not (acl2::mfc-ancestors mfc)) nil
    (list (cons 'backchaining-free-variable `(quote t)))))

(defthm open-imp-in-conclusion
  (implies
   (in-conclusion-check (imp a x))
   (equal (imp a x) (if x t a)))
  :hints (("Goal" :in-theory (enable imp))))

(defun remove-keywords (list)
  (if (consp list)
      (if (and (symbolp (car list))
               (in-pkg-of (car list) :key))
          (remove-keywords (cdr list))
        (cons (car list)
              (remove-keywords (cdr list))))
    nil))
(defun generate-cong-hyp-np (cong)
  (declare (xargs :mode :program))
  (let* ((ovar  (car cong))
         (eex   (cadr cong))
         (equiv (car eex))
         (nvar  (cadr eex))
         (exp   (caddr eex)))
    (let* ((ctx-fn        (car exp))
           (fn-witness    (safe-witness ctx-fn))
           (fix-args      (remove-keywords (cdr exp)))
           (fix-fn-unfix  (safe-symbol (list ctx-fn "_UNFIX") fn-witness))
           (fix-fn-unfix-check  (safe-symbol (list ctx-fn "_UNFIX_CHECK") fn-witness))
           (var-wrapped?  (safe-symbol (list ovar "-wrapped?")  ovar))
           (var-hyps      (safe-symbol (list ovar "-hyps")  ovar))
           (unwrapped-var (safe-symbol (list ovar "-unwrapped") ovar))
           (wrapped-var           (safe-symbol (list nvar "-wrapped")   nvar))
           (wrapped-var-hyps      (safe-symbol (list nvar "-wrapped-hyps")   nvar))
           (wrapped-var-wrapped?  (safe-symbol (list nvar "-wrapped?")  nvar))
           (unwrapped-wrapped-var nvar)
           )
      `(
        (bind-free (,fix-fn-unfix ,ovar ,@fix-args ',var-wrapped? ',unwrapped-var ',var-hyps)
                   (,var-wrapped? ,unwrapped-var ,var-hyps))

        ;; var-wrapped => (ovar == (fn .. unwrapped-var ..))

        ;; We now ask ACL2 to rewrite under the new context .. if the bound
        ;; variable was not already in such a context.

        ,(cond
          ((not (equal equiv 'equal))
                  `(,equiv ,wrapped-var (double-rewrite (if ,var-wrapped? ,ovar ,exp))))
          (t      `(,equiv ,wrapped-var (if ,var-wrapped? ,ovar ,exp))))

        (bind-free (,fix-fn-unfix ,wrapped-var ,@fix-args ',wrapped-var-wrapped? ',unwrapped-wrapped-var ',wrapped-var-hyps)
                   (,wrapped-var-wrapped? ,unwrapped-wrapped-var ,wrapped-var-hyps))

        ;; wrapped-var-wrapped? => (wrapped-var == (fn .. unwrapped-wrapped-var ..))

        ;; After rewriting in the new context, we evaluate the resulting term.
        ;; If the term is still (syntactically) wrapped in the context, we
        ;; remove the context.

        ;; Of course, we have to justify our actions when we remove the
        ;; syntactic wrapper.  To avoid re-rewriting the term, we have defined
        ;; fix-fn-unfix-check, which knows how to compare the new term with the
        ;; expected value without actually re-wrapping it in the context.

        (,fix-fn-unfix-check ,wrapped-var-wrapped? ,wrapped-var ,unwrapped-wrapped-var ,wrapped-var-hyps ,@fix-args)

        )

      )))


(defun generate-cong-hyp-p (cong)
  (declare (xargs :mode :program))
  (let* (;(ovar  (car cong))
         (eex   (cadr cong))
         (equiv (car eex))
         (nvar  (cadr eex))
         (exp   (caddr eex)))
    (let* ((ctx-fn        (car exp))
           (fn-witness    (safe-witness ctx-fn))
           (lhs           (cadr exp))
           (key-args      (cddr exp)) ; (ctx lhs :keys ..)
           (fix-fn-unfix-keyed  (safe-symbol (list ctx-fn "_UNFIX_KEYED") fn-witness))
           (fix-fn-unfix-check-keyed  (safe-symbol (list ctx-fn "_UNFIX_CHECK_KEYED") fn-witness))
           (wrapped-var           (safe-symbol (list nvar "-wrapped")   nvar))
           (wrapped-var-hyps      (safe-symbol (list nvar "-wrapped-hyps")   nvar))
           (wrapped-var-wrapped?  (safe-symbol (list nvar "-wrapped?")  nvar))
           (unwrapped-wrapped-var nvar)
           )
      `(
        ;; We now ask ACL2 to rewrite under the new context .. if the bound
        ;; variable was not already in such a context.

        (,equiv ,wrapped-var ,exp)

        (bind-free
         (,fix-fn-unfix-keyed ,wrapped-var ',wrapped-var-wrapped? ',unwrapped-wrapped-var ',wrapped-var-hyps ,lhs ,@key-args)
         (,wrapped-var-wrapped? ,unwrapped-wrapped-var ,wrapped-var-hyps))

        ;; wrapped-var-wrapped? => (wrapped-var == (fn .. unwrapped-wrapped-var ..))

        ;; After rewriting in the new context, we evaluate the resulting term.
        ;; If the term is still (syntactically) wrapped in the context, we
        ;; remove the context.

        ;; Of course, we have to justify our actions when we remove the
        ;; syntactic wrapper.  To avoid re-rewriting the term, we have defined
        ;; fix-fn-unfix-check, which knows how to compare the new term with the
        ;; expected value without actually re-wrapping it in the context.

        (,fix-fn-unfix-check-keyed ,wrapped-var ,wrapped-var-wrapped? ,unwrapped-wrapped-var ,wrapped-var-hyps ,lhs ,@key-args)

        )

      )))


(defun generate-cong-hyp (p cong)
  (declare (xargs :mode :program))
  (if p (generate-cong-hyp-p cong)
    (generate-cong-hyp-np cong)))

(defun wrapped-hyp (cong)
  (declare (xargs :mode :program))
  (let* ((eex   (cadr cong))
         (nvar  (cadr eex)))
    (let* ((wrapped-var-wrapped?  (safe-symbol (list nvar "-wrapped?")  nvar)))
      wrapped-var-wrapped?)))

(defun wrapped-hyps (congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (cons (wrapped-hyp (car congs))
            (wrapped-hyps (cdr congs)))
    nil))

(defun generate-asymmetric-hyps (congs)
  (declare (xargs :mode :program))
  `(and ,@(wrapped-hyps congs)))

(defun generate-cong-hyps (p congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (append (generate-cong-hyp p (car congs))
              (generate-cong-hyps p (cdr congs)))
    nil))

(defun generate-cong-syntax-hyp (cong)
  (let* ((ovar (car cong))
         (eex  (cadr cong))
         (nvar (cadr eex)))
    `(not (equal ,ovar ,nvar))))

(defun generate-cong-syntax-hyps-rec (congs)
  (if (consp congs)
      (cons (generate-cong-syntax-hyp (car congs))
            (generate-cong-syntax-hyps-rec (cdr congs)))
    nil))

(defun generate-cong-syntax-hyps (congs)
  `(syntaxp (or ,@(generate-cong-syntax-hyps-rec congs))))

(defun cong-equivs (congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (let ((cong (car congs)))
        (let ((eex (cadr cong)))
          (let (;(equiv (car eex))
                (term (caddr eex)))
            (let ((fix-fn (car term)))
              (cons (safe-symbol (list fix-fn "_EQUIV")
                               (safe-witness fix-fn))
                    (cong-equivs (cdr congs)))))))
    nil))

(defun replace-term (x y list)
  (declare (type t x y list))
  (if (consp list)
      (if (equal (car list) x)
          (cons y (cdr list))
        (cons (car list) (replace-term x y (cdr list))))
    nil))

(defun make-keyargs (args)
  (if (consp args)
      (cons `(,(car args) ',(car args))
            (make-keyargs (cdr args)))
    nil))

(defun bind-keyargs (args)
  (if (consp args)
      (cons (intern-in-package-of-symbol (symbol-name (car args)) :key)
            (cons (car args)
                  (bind-keyargs (cdr args))))
    nil))

(defun defequiv-fn (term lhs rhs pred context equiv chaining keywords)
  (declare (xargs :mode :program))
  (let* ((context-macro (if keywords context (safe-symbol (list context "-macro") context)))
         (context-fn    (if keywords (safe-symbol (list context "-fn") context) context))
         (context       (if keywords context-macro context-fn))
         (fn-witness   (safe-witness (if pred pred (car term))))
         (fix-fn       (or pred (safe-symbol (list (car term) "-pred") fn-witness)))
         (hyps         (safe-symbol (list fix-fn "-backchain-hyps") fn-witness))
         (args         (cons hyps (cdr term)))
         (args--       (cdr term))
         (lhs-args     (remove rhs args))
         (lhs-args--   (remove rhs args--))
         (new-rhs      (safe-symbol (list rhs "_replacement") fn-witness))
         (rhs-args--   (replace-term rhs new-rhs args--))
         (lhs-rhs--    (replace-term lhs rhs lhs-args--))
         (macroargs    (replace-term lhs 'lhs (replace-term rhs 'rhs args--)))
         (keyargs      (make-keyargs macroargs))
         (fix-fn-unfix (safe-symbol (list context "_UNFIX") fn-witness))
         (fix-fn-unfix-keyed (safe-symbol (list context "_UNFIX_KEYED") fn-witness))
         (fix-fn-unfix-check (safe-symbol (list context "_UNFIX_CHECK") fn-witness))
         (fix-fn-unfix-check-keyed (safe-symbol (list context "_UNFIX_CHECK_KEYED") fn-witness))
         (fix-fn-unfix-check-reduction-1 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_1") fn-witness))
         (fix-fn-unfix-check-reduction-2 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_2") fn-witness))
         (fix-fn-unfix-check-reduction-3 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_3") fn-witness))
         (fix-fn-context-reduction (safe-symbol (list context "_REDUCTION") fn-witness))
         (wrapped-var  (safe-symbol (list rhs "-wrapped") fn-witness))
         (wrapped-var? (safe-symbol (list rhs "-wrapped?") fn-witness))
         (fix-fn-chaining  (safe-symbol (list fix-fn "-CHAINING") fn-witness))
         )
    `(encapsulate
      ()

      (set-ignore-ok t)
      (SET-IRRELEVANT-FORMALS-OK t)

      (defun ,context-fn (,@lhs-args--)
        t)

      (defmacro ,context-macro (,lhs &key ,@(make-keyargs (remove lhs lhs-args--)))
        `(,',context-fn ,@(list ,@lhs-args--)))

      (defthm ,fix-fn-context-reduction
        (implies
         (in-conclusion-check (,context-fn ,@lhs-args--))
         (equal (,context-fn ,@lhs-args--) t)))

      (in-theory (disable (:type-prescription ,context-fn) ,context-fn (,context-fn)))

      (defund ,fix-fn (,@args)
        (if (not ,hyps) nil (not (not ,term))))

      (in-theory (disable (,fix-fn)))

      (defthm ,(safe-symbol (list fix-fn "-OPEN") fix-fn)
        (implies
         (in-conclusion-check (,fix-fn ,@args))
         (equal (,fix-fn ,@args)
                (if (not ,hyps) nil (not (not ,term)))))
        :hints (("Goal" :in-theory (enable ,fix-fn))))

      (defun ,fix-fn-unfix (term ,@lhs-args-- wrapped unwrap hyp)
        (declare (type t term))
        (and (consp term)
             (cond
              ((equal (car term) ',fix-fn)
               `((,wrapped . 't)
                 (,unwrap  . ,(ith ,(1+ (locate rhs term)) term))
                 (,hyp     . ,(ith 1 term))))
              ((equal (car term) ',context-fn)
               `((,wrapped . 'nil)
                 (,unwrap  . ,,lhs)
                 (,hyp     . 't)))
              ((equal term '(quote t))
               (cw "~%Boolean Binding reduced ~p0 to TRUE~%" ',fix-fn))
              (t
               (cw "~%Boolean Binding Failure on returned term:~%~p0~%" term)))))

      (defmacro ,fix-fn-unfix-keyed (term wrapped unwrap ,hyps ,lhs &key ,@(make-keyargs (remove lhs lhs-args--)))
        `(,',fix-fn-unfix ,term ,@(list ,@lhs-args--) ,wrapped ,unwrap ,,hyps))

      ;;
      ;; Note that this includes the "hyp" parameter in lhs-args ..
      ;;
      (defun ,fix-fn-unfix-check (,wrapped-var? ,wrapped-var ,rhs ,@lhs-args)
        (if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@args))
          (equal ,rhs ,lhs)))

      (defmacro ,fix-fn-unfix-check-keyed (,wrapped-var ,wrapped-var? ,rhs ,hyps ,lhs
                                                         &key ,@(make-keyargs (remove lhs lhs-args--)))
        `(,',fix-fn-unfix-check ,,wrapped-var? ,,wrapped-var ,,rhs ,@(list ,@lhs-args)))

      (defthm ,fix-fn-unfix-check-reduction-1
        (implies
         (in-conclusion-check (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,rhs ,@lhs-args))
         (equal (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,rhs ,@lhs-args)
                (if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@args))
                  (equal ,rhs ,lhs)))))

      (defthm ,fix-fn-unfix-check-reduction-2
        (,fix-fn-unfix-check t (,fix-fn ,@args) ,rhs ,@lhs-args))

      (defthm ,fix-fn-unfix-check-reduction-3
        (,fix-fn-unfix-check nil ,wrapped-var ,lhs ,@lhs-args))

      (in-theory (disable ,fix-fn-unfix-check))

      (defmacro ,equiv ,(if keywords `(&key (hyp 'nil) (skip 'nil) ,@keyargs) `(,@macroargs &key (hyp 'nil) (skip 'nil)))
        (let ((,lhs lhs)
              (,rhs rhs))
          (let ((hyp (if hyp `(hide ,hyp) `t)))
            `(equal (,',context-fn ,@(list ,@lhs-args--))
                    ,(if skip
                         `(skip-rewrite (,',fix-fn ,hyp ,@(list ,@args--)))
                       `(,',fix-fn ,hyp ,@(list ,@args--)))))))

      ,@(and chaining
             `(
               (defthm ,fix-fn-chaining
                 (implies
                  (and
                   (backchaining-check)
                   (bind-contextp (,rhs (equal ,new-rhs ,(if keywords
                                                             `(,context-macro ,rhs ,@(bind-keyargs (remove rhs lhs-rhs--)))
                                                           `(,context ,@lhs-rhs--))))))
                  (equal (,fix-fn ,@args)
                         (skip-rewrite (,fix-fn (hide (,fix-fn ,@args)) ,@rhs-args--))))
                 :rule-classes ((:rewrite :backchain-limit-lst 100))
                 :hints (("Goal" :expand (:free (x) (hide x)))))
               ))

      )))

(defthm equal-cons-cases
  (equal (equal (cons a b) c)
         (and (consp c)
              (equal a (car c))
              (equal b (cdr c)))))

(defun lastatom (x)
  (if (consp x) (lastatom (cdr x))
    x))

(defthm lastatom-update-nth-<
  (implies
   (< (nfix a) (len x))
   (equal (lastatom (update-nth a v x))
          (lastatom x))))

(defthm lastatom-update-nth->
  (implies
   (not (< (nfix a) (len x)))
   (equal (lastatom (update-nth a v x))
          nil)))

(defthm lastatom-update-nth
  (equal (lastatom (update-nth a v x))
         (if (< (nfix a) (len x))
             (lastatom x)
           nil)))

(defun nfix-equiv (a b)
  (equal (nfix a)
         (nfix b)))

(defthmd equal-nfix-rewrite
  (iff (equal (nfix a) b)
       (and (natp b)
            (nfix-equiv a b))))

(defun nmx-induction (n m x)
  (if (zp n) x
    (if (zp m) n
      (nmx-induction (1- n) (1- m) (cdr x)))))

(defthm update-nth-of-update-nth
  (implies
   (nfix-equiv a b)
   (equal (update-nth a v (update-nth b w x))
          (update-nth a v x)))
  :hints (("Goal" :induct (nmx-induction a b x)
           :in-theory (enable update-nth))))

(defthm update-nth-over-update-nth
  (implies
   (not (nfix-equiv a b))
   (equal (update-nth a v (update-nth b w x))
          (update-nth b w (update-nth a v x))))
  :hints (("Goal" :induct (nmx-induction a b x)
           :in-theory (enable update-nth))))

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defund clr-nth (a x)
  (update-nth a nil x))

(defthm lastatom-clr-nth
  (equal (lastatom (clr-nth a x))
         (if (< (nfix a) (len x))
             (lastatom x)
           nil))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm len-clr-nth
  (equal (len (clr-nth a x))
         (max (1+ (nfix a)) (len x)))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm clr-nth-defn
  (equal (clr-nth n x)
         (if (zp n) (cons nil (cdr x))
           (cons (car x)
                 (clr-nth (1- n) (cdr x)))))
  :hints (("Goal" :in-theory (enable clr-nth update-nth)))
  :rule-classes (:definition))

(defthm open-clr-nth
  (and
   (implies
    (not (zp n))
    (equal (clr-nth n x)
           (cons (car x)
                 (clr-nth (1- n) (cdr x)))))
   (implies
    (zp n)
    (equal (clr-nth n x)
           (cons nil (cdr x))))))

(defthm open-update-nth
  (and
   (implies
    (not (zp n))
    (equal (update-nth n v x)
           (cons (car x)
                 (update-nth (1- n) v (cdr x)))))
   (implies
    (zp n)
    (equal (update-nth n v x)
           (cons v (cdr x))))))

(defthm clr-nth-update-nth
  (equal (clr-nth a (update-nth b v x))
         (if (nfix-equiv a b) (clr-nth a x)
           (update-nth b v (clr-nth a x))))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm clr-nth-of-clr-nth
  (equal (clr-nth a (clr-nth a x))
         (clr-nth a x))
  :hints (("goal" :in-theory (enable clr-nth))))

(defthm clr-nth-over-clr-nth
  (equal (clr-nth a (clr-nth b x))
         (clr-nth b (clr-nth a x)))
  :hints (("goal" :in-theory (enable clr-nth))))

(defthm nth-clr-nth
  (equal (nth a (clr-nth b x))
         (if (nfix-equiv a b) nil
           (nth a x)))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defun equal-nth-conclusion (a x y)
  (and (equal (lastatom x) (lastatom y))
       (equal (len x) (len y))
       (equal (nth a x) (nth a y))
       (equal (clr-nth a x)
              (clr-nth a y))))

(defthm open-equal-nth-conclusion
  (equal (equal-nth-conclusion n x y)
         (if (zp n) (if (and (consp x) (consp y))
                        (and (equal (car x) (car y))
                             (equal (cdr x) (cdr y)))
                      (equal x y))
           (if (and (consp x)
                    (consp y))
               (and (equal (car x) (car y))
                    (equal-nth-conclusion (1- n) (cdr x) (cdr y)))
             (equal x y))))
  :rule-classes (:definition))

(defun equal-nth-conclusion-fn (n x y)
  (if (zp n) (if (and (consp x) (consp y))
                 (and (equal (car x) (car y))
                      (equal (cdr x) (cdr y)))
               (equal x y))
    (if (and (consp x)
             (consp y))
        (and (equal (car x) (car y))
             (equal-nth-conclusion-fn (1- n) (cdr x) (cdr y)))
      (equal x y))))

(defthmd equal-nth-conclusion-fn-to-equal-nth-conclusion
  (equal (equal-nth-conclusion n x y)
         (equal-nth-conclusion-fn n x y)))

(defthm equal-nth-conclusion-fn-to-equal
  (equal (equal-nth-conclusion-fn n x y)
         (equal x y)))

(defthmd equal-to-nth-reduction
  (equal (equal x y)
         (equal-nth-conclusion n x y))
  :hints (("Goal" :in-theory '(equal-nth-conclusion-fn-to-equal-nth-conclusion
                               equal-nth-conclusion-fn-to-equal))))

(defthm equal-update-nth-reduction
  (equal (equal (update-nth n v x) y)
         (and (< (nfix n) (len y))
              (equal v (nth n y))
              (equal (clr-nth n x)
                     (clr-nth n y))))
  :hints (("Goal" :use (:instance equal-to-nth-reduction
                                  (x (update-nth n v x))))))

(defthm update-nth-nth
  (implies
   (< (nfix n) (len x))
   (equal (update-nth n (nth n x) x) x)))

#| nil-list

(defun nil-list (n v)
  (if (zp n) (list v)
    (cons nil (nil-list (1- n) v))))

(defthm update-nth-to-append
  (implies
   (<= (len x) (nfix n))
   (equal (update-nth n v x)
          (append x (nil-list (- (nfix n) (len x)) v))))
  :hints (("Goal" :in-theory (enable append update-nth))))

(defthm nth-nil-list-nfix-equiv
  (implies
   (nfix-equiv a m)
   (equal (nth a (nil-list m v)) v))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-nil-list-not-nfix-equiv
  (implies
   (not (nfix-equiv a m))
   (equal (nth a (nil-list m v)) nil))
  :hints (("Goal" :induct (nm-induction a m)
           :in-theory (enable nth))))

(defthm nth-nil-list
  (equal (nth a (nil-list m v))
         (if (nfix-equiv a m) v
           nil))
  :hints (("Goal" :in-theory
           '(nth-nil-list-not-nfix-equiv
             nth-nil-list-nfix-equiv))))

(defthm nthcdr-nil-list
  (equal (nthcdr n (nil-list m v))
         (if (<= (nfix n) (nfix m))
             (nil-list (- (nfix m) (nfix n)) v)
           nil))
  :hints (("Goal" :induct (nm-induction n m)
           :in-theory (enable nthcdr))))

(defthm firstn-nil-list
  (implies
   (not (zp n))
   (equal (firstn n (nil-list m v))
          (if (<= (nfix n) (nfix m))
              (nil-list (1- (nfix n)) nil)
            (nil-list m v))))
  :hints (("Goal" :induct (nm-induction n m)
           :in-theory (enable firstn))))

(defthm car-nil-list-nil
  (equal (car (nil-list n nil))
         nil))

|#

#| equal append rules ..

(defthm equal-append-append-tail-equal
  (equal (equal (append x y) (append z y))
         (list::equiv x z))
  :hints (("goal" :induct (list::len-len-induction x z)
           :in-theory (enable append))))

(defthmd equal-to-equiv
  (equal (equal x y)
         (and
          (list::equiv x y)
          (equal (lastatom x) (lastatom y))))
  :hints (("goal" :induct (list::len-len-induction x y))))

(defun equal-append-append-case (x a y b)
  (and (list::equiv x (firstn (len x) a))
       (list::equiv (firstn (- (len a) (len x)) y)
                    (nthcdr (len x) a))
       (equal (nthcdr (- (len a) (len x)) y)
              b)))

(defthm equiv-append-reduction-1
  (equal (list::equiv (append x y) z)
         (and (list::equiv x (firstn (len x) z))
              (list::equiv y (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION! list::equiv)
                                  (LIST::LIST-EQUIV-HACK LIST::EQUAL-OF-FIXES)))))

(defthm equiv-append-reduction-2
  (equal (list::equiv z (append x y))
         (and (list::equiv x (firstn (len x) z))
              (list::equiv y (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION! list::equiv)
                                  (LIST::LIST-EQUIV-HACK LIST::EQUAL-OF-FIXES)))))

(defthmd equal-append-append-reduction2!
  (equal (equal (append x y) (append a b))
         (if (< (len x) (len a))
             (equal-append-append-case x a y b)
           (equal-append-append-case a x b y)))
  :hints (("goal" :in-theory '(LIST::EQUAL-APPEND-REDUCTION!))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))
          (and stable-under-simplificationp
               '(:in-theory '(LIST::EQUAL-APPEND-REDUCTION!)))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))))

|#

(in-theory (disable nfix nfix-equiv))
(in-theory (enable equal-nfix-rewrite))
(in-theory (disable nth update-nth))

(defun nfix-list (list)
  (if (consp list)
      (cons (nfix (car list))
            (nfix-list (cdr list)))
    nil))

(defun nfix-list-equiv (x y)
  (equal (nfix-list x)
         (nfix-list y)))

(defequiv nfix-list-equiv)

(defthm open-nfix-list-equiv
  (and
   (implies
    (consp x)
    (equal (nfix-list-equiv x y)
           (and (consp y)
                (equal (nfix (car x))
                       (nfix (car y)))
                (nfix-list-equiv (cdr x) (cdr y)))))
   (implies
    (not (consp x))
    (equal (nfix-list-equiv x y)
           (not (consp y))))))

(in-theory (disable nfix-list-equiv))


(defun nth* (list st)
  (if (consp list)
      (cons (nth (car list) st)
            (nth* (cdr list) st))
    nil))

(defund nth*-equiv (list st1 st2)
  (equal (nth* list st1)
         (nth* list st2)))

(defthm nth*-equiv-def
  (equal (nth*-equiv list st1 st2)
         (if (consp list)
             (and (equal (nth (car list) st1)
                         (nth (car list) st2))
                  (nth*-equiv (cdr list) st1 st2))
           t))
  :hints (("Goal" :in-theory (enable nth*-equiv)))
  :rule-classes (:definition))

(defun clr-nth* (list st)
  (if (consp list)
      (clr-nth (car list)
               (clr-nth* (cdr list) st))
    st))

(defthm open-clr-nth*
  (implies
   (consp list)
   (equal (clr-nth* list st)
          (clr-nth (car list)
                   (clr-nth* (cdr list) st)))))

(defthm clr-nth-clr-nth*
  (equal (clr-nth* list (clr-nth a st))
         (clr-nth a (clr-nth* list st)))
  :hints (("Subgoal *1/1" :cases ((nfix-equiv a (car list))))))

(defun equal-nth*-conclusion (list x y)
  (and (equal (lastatom x) (lastatom y))
       (equal (len x) (len y))
       (nth*-equiv list x y)
       (equal (clr-nth* list x)
              (clr-nth* list y))))

(defthm nth*-equiv-over-clr-nth-backchaining
  (implies
   (nth*-equiv list x y)
   (nth*-equiv list (clr-nth a x) (clr-nth a y)))
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defthm nth*-equiv-identity
  (nth*-equiv list x x)
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defun equal-nth*-induction (list x y)
  (if (consp list)
      (equal-nth*-induction (cdr list)
                            (clr-nth (car list) x)
                            (clr-nth (car list) y))
    (list x y)))

(defthmd equal-nth*-reduction
  (equal (equal x y)
         (equal-nth*-conclusion list x y))
  :hints (("Goal" :induct (equal-nth*-induction list x y)
           :in-theory (disable equal-nth*-conclusion lastatom-clr-nth len-clr-nth))
          ("Subgoal *1/2" :in-theory (enable equal-nth*-conclusion))
          ("Subgoal *1/1" :in-theory (enable equal-nth*-conclusion)
           :use ((:instance equal-to-nth-reduction
                            (n (car list)))))))


(defun copy-nth* (list st1 st2)
  (if (consp list)
      (update-nth (car list)
                  (nth (car list) st1)
                  (copy-nth* (cdr list) st1 st2))
    st2))

;;
;; Does the default ordering go the wrong way?
;;
(defthm clr-nth-thru-clr-nth*
  (equal (clr-nth ZZZZ (clr-nth* list (update-nth ZZZZ v x)))
         (clr-nth ZZZZ (clr-nth* list x))))

(defthm nth*-clr-copy-nth*
  (equal (clr-nth* list (copy-nth* list st1 st2))
         (clr-nth* list st2)))

(defund nth*-copy-equiv (list x y z)
  (equal (copy-nth* list x z)
         (copy-nth* list y z)))

(defthm nth*-copy-equiv-reduction
  (equal (nth*-copy-equiv list x y z)
         (equal-nth*-conclusion list (copy-nth* list x z) (copy-nth* list y z)))
  :hints (("Goal" :in-theory (enable nth*-copy-equiv)
           :use (:instance equal-nth*-reduction
                           (x (copy-nth* list x z))
                           (y (copy-nth* list y z))
                           (list list)))))

(defthm nth*-equiv-update-nth-chaining
  (implies
   (and
    (nth*-equiv list x y)
    (equal v (nth a y)))
   (nth*-equiv list (update-nth a v x) y))
  :hints (("goal" :induct (len list))))

(defthm nth*-equiv-copy-nth*
  (nth*-equiv list (copy-nth* list x y) x))

(defthm nth*-copy-nth*
  (equal (nth* list (copy-nth* list x y))
         (nth* list x))
  :hints (("Goal" :in-theory `(nth*-equiv)
           :use (:instance nth*-equiv-copy-nth*))))

(defthm nth*-equiv-copy-nth*-copy-nth*
  (equal (nth*-equiv list (copy-nth* list x a)
                     (copy-nth* list y b))
         (nth*-equiv list x y))
  :hints (("Goal" :in-theory (enable nth*-equiv))))

(defthm lastatom-copy-nth*
  (equal (lastatom (copy-nth* list x y))
         (if (or (not (consp list)) (< (maxval list) (len y)))
             (lastatom y)
           nil))
  :hints (("Goal" :in-theory (enable maxsize)))
  :otf-flg t)

(defthm nth*-equiv-reduction
  (equal (nth*-equiv list x y)
         (nth*-copy-equiv list x y z)))

(defun use (list st)
  (copy-nth* list st nil))

(defthm nth-use
  (implies
   (member (nfix n) (nfix-list list))
   (equal (nth n (use list x))
          (nth n x)))
  :hints (("Goal" :in-theory (enable use))))

(defthm nth*-get-copy-equivalence
  (equal (equal (nth* list x)
                (nth* list y))
         (equal (use list x)
                (use list y)))
  :hints (("goal" :in-theory '(use
                               nth*-equiv
                               nth*-copy-equiv)
           :use (:instance nth*-equiv-reduction
                           (z nil)))))

(defthm nth-copy-nth*
  (equal (nth a (copy-nth* list x y))
         (if (member (nfix a) (nfix-list list)) (nth a x)
           (nth a y))))

(defthm update-nth-nil-reduction
  (equal (update-nth a nil x)
         (clr-nth a x))
  :hints (("Goal" :in-theory (enable clr-nth))))

(defthm clr-nth-copy-nth*-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (clr-nth a (copy-nth* list x y))
          (copy-nth* list (clr-nth a x) y)))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm clr-nth-copy-nth*-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (clr-nth a (copy-nth* list x y))
          (copy-nth* list x (clr-nth a y))))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm clr-nth*-copy-nth*
  (equal (clr-nth a (copy-nth* list x y))
         (if (member (nfix a) (nfix-list list)) (copy-nth* list (clr-nth a x) y)
           (copy-nth* list x (clr-nth a y)))))

(defthm update-nth-thru-copy-nth*
  (equal (update-nth a v (copy-nth* list (update-nth a w x) y))
         (update-nth a v (copy-nth* list x y))))

(defthm copy-nth*-update-nth-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (copy-nth* list (update-nth a v x) z)
          (update-nth a v (copy-nth* list x z))))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm copy-nth*-update-nth-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (copy-nth* list (update-nth a v x) z)
          (copy-nth* list x z)))
  :hints (("Goal" :in-theory (disable EQUAL-UPDATE-NTH-REDUCTION))))

(defthm copy-nth*-update-nth
  (equal (copy-nth* list (update-nth a v x) z)
         (if (member (nfix a) (nfix-list list))
             (update-nth a v (copy-nth* list x z))
           (copy-nth* list x z)))
  :hints (("Goal" :in-theory '(copy-nth*-update-nth-member
                               copy-nth*-update-nth-non-member
                               ))))

(defthm use-update-nth-non-member
  (implies
   (not (member (nfix a) (nfix-list list)))
   (equal (use list (update-nth a v x))
          (use list x))))

(defthmd use-update-nth-member
  (implies
   (member (nfix a) (nfix-list list))
   (equal (use list (update-nth a v x))
          (update-nth a v (use list x)))))

(defthmd use-update-nth
  (equal (use list (update-nth a v x))
         (if (member (nfix a) (nfix-list list))
             (update-nth a v (use list x))
           (use list x)))
  :hints (("Goal" :in-theory '(use-update-nth-non-member
                               use-update-nth-member
                               ))))

(defthm use-use
  (equal (use list (use list x))
         (use list x)))

(defthm member-append
  (iff (member x (append y z))
       (or (member x y)
           (member x z))))

(defthm nfix-list-append
  (equal (nfix-list (append x y))
         (append (nfix-list x) (nfix-list y))))

(defthmd open-use
  (and
   (implies
    (consp list)
    (equal (use list x)
           (update-nth (car list) (nth (car list) x)
                       (use (cdr list) x))))
   (implies
    (not (consp list))
    (equal (use list x) nil)))
  :hints (("Goal" :in-theory (e/d (use) (EQUAL-UPDATE-NTH-REDUCTION)))))


(defun subset (x y)
  (if (consp x)
      (and (member (car x) y)
           (subset (cdr x) y))
    t))

(defthm nth*-use
  (implies
   (subset list listx)
   (equal (nth* list (use listx st))
          (nth* list st)))
  :hints (("Goal" :in-theory (e/d (use)
                                  (NTH*-GET-COPY-EQUIVALENCE)))))

(defthm subset-append
  (subset list (append list y)))

(defthm equal-nth*-append-reduction
  (equal (equal (nth* (append x y) a)
                (nth* (append x y) b))
         (and (equal (nth* x a)
                     (nth* x b))
              (equal (nth* y a)
                     (nth* y b))))
  :hints (("Goal" :in-theory (disable
                              NTH*-GET-COPY-EQUIVALENCE
                              ))))

(defthm clr-nth-use
  (implies
   (member (nfix a) (nfix-list list))
   (equal (clr-nth a (use list x))
          (use list (clr-nth a x))))
  :hints (("Goal" :in-theory (enable use))))

(in-theory (disable OPEN-UPDATE-NTH))

(defun o1-test (o1)
  (declare (type t o1))
  (and (consp o1)
       (o-p (car o1))
       (or (equal (cdr o1) 3)
           (equal (cdr o1) 2)
           (equal (cdr o1) 1))))

(defun o2-test (o2)
  (declare (type t o2))
  (and (consp o2)
       (o-p (car o2))
       (equal (cdr o2) 1)))

(defun oconsp (x)
  (declare (type t x))
  (and (o-p x)
       (consp x)
       (let ((o1 (car x)))
         (and (o1-test o1)
              (if (equal (cdr o1) 3)
                  (equal (cdr x) 0)
                (and (consp (cdr x))
                     (let ((o2 (cadr x)))
                       (o2-test o2))
                     (equal (cddr x) 0)))))))

(defun ocons (x y)
  (declare (type (satisfies o-p) x y))
  (if (o< x y)
      `((,(o+ y 1) . 2) (,(o+ x 1) . 1) . 0)
    (if (o< y x)
        `((,(o+ x 1) . 1) (,(o+ y 1) . 1) . 0)
      `((,(o+ x 1) . 3) . 0))))

(defun polarity (x)
  (declare (type (satisfies oconsp) x))
  (cdar x))

(defun ocar (x)
  (declare (type (satisfies oconsp) x))
  (let ((p (polarity x)))
    (cond
     ((= p 3)
      (caar x))
     ((= p 2)
      (caadr x))
     (t
      (caar x)))))

(defun ocdr (x)
  (declare (type (satisfies oconsp) x))
  (let ((p (polarity x)))
    (cond
     ((= p 3)
      (caar x))
     ((= p 2)
      (caar x))
     (t
      (caadr x)))))

(defthm ocdr-ocons
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (ocdr (ocons x y))
          (o+ y 1))))

(defthm ocar-ocons
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (ocar (ocons x y))
          (o+ x 1))))

;; We can now use the ordinals to encode structure.  The
;; rest is a simple matter of programming :)

(in-theory (disable ocons ocar ocdr oconsp))

;;

(defun len-len-induction (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (len-len-induction (cdr x) (cdr y))
    (if (consp x)
        (len-len-induction (cdr x) y)
      (if (consp y)
          (len-len-induction x (cdr y))
        (list x y)))))

(defthmd ordinal-double-containment
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (equal x y)
          (and (not (o< x y))
               (not (o< y x))))))

(defun chartoo (x)
  (declare (type character x))
  (char-code x))

(defthm op-chartoo
  (o-p (chartoo x)))

(in-theory (disable chartoo))

(defun char-listoo (x)
  (declare (type (satisfies character-listp) x))
  (if (consp x)
      (ocons (chartoo (car x))
             (char-listoo (cdr x)))
    0))

(defthm op-char-listoo
  (o-p (char-listoo x)))

(defthm equal-char-listoo-reduction
  (implies
   (and
    (character-listp x)
    (character-listp y))
   (equal (equal (char-listoo x) (char-listoo y))
          (equal x y)))
  :hints (("Goal" :induct (len-len-induction x y))
          (and stable-under-simplificationp
               '(:in-theory (e/d (ordinal-double-containment)
                                 (|0 < a  =  ~(a = 0)|))))))

(defun stringtoo (x)
  (declare (type string x))
  (char-listoo (coerce x 'list)))

(defthm op-stringtoo
  (o-p (stringtoo x)))

(defthm equal-coerce-reduction
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal (coerce x 'list) (coerce y 'list))
          (equal x y)))
  :hints (("Goal" :in-theory (disable COERCE-INVERSE-2)
           :cases ((equal x (coerce (coerce x 'list) 'string))))
          ("Subgoal 2" :in-theory (enable COERCE-INVERSE-2))
          ("Subgoal 1" :in-theory (disable COERCE-INVERSE-2)
           :cases ((equal y (coerce (coerce y 'list) 'string))))
          ("Subgoal 1.2" :in-theory (enable COERCE-INVERSE-2))))

(defthm equal-stringtoo-reduction
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal (stringtoo x) (stringtoo y))
          (equal x y))))

(in-theory (disable stringtoo))

(defun symboltoo (x)
  (declare (type symbol x))
  (ocons (stringtoo (symbol-package-name x))
         (stringtoo (symbol-name x))))

(defthm op-symboltoo
  (implies
   (symbolp x)
   (o-p (symboltoo x)))
  :hints (("Goal" :in-theory (enable symboltoo))))

(defthm equal-0+-1-reduction
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (equal (o+ x 1)
                 (o+ y 1))
          (equal x y)))
  :hints (("Goal" :in-theory (e/d (ordinal-double-containment)
                                  (|0 < a  =  ~(a = 0)|)))))

(defthmd equal-string-double-containment
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal x y)
          (and (not (string< x y))
               (not (string< y x)))))
  :hints (("Goal" :in-theory (enable string<))))

(defthmd equal-symbol-double-containment
  (implies
   (and
    (symbolp x)
    (symbolp y))
   (equal (equal x y)
          (and (not (symbol-< x y))
               (not (symbol-< y x))))))


(defthm equal-symboltoo-reduction
  (implies
   (and
    (symbolp x)
    (symbolp y))
   (equal (equal (symboltoo x) (symboltoo y))
          (equal x y)))
  :hints (("goal" :in-theory (enable
                              equal-string-double-containment
                              ))
          ("Subgoal 5" :in-theory (e/d
                                   (symbol-< equal-symbol-double-containment)
                                   (SYMBOL-<-TRICHOTOMY)))))

(in-theory (disable symboltoo))

(defun intoo (x)
  (declare (type integer x))
  (if (< x 0) (ocons 0 (- x))
    (ocons 1 x)))

(defthm equal-intoo-reduction
  (implies
   (and
    (integerp x)
    (integerp y))
   (equal (equal (intoo x) (intoo y))
          (equal x y))))

(defthm op-intoo
  (implies
   (integerp x)
   (o-p (intoo x))))

(in-theory (disable intoo))

(defun rationaltoo (x)
  (declare (type rational x))
  (let ((n (numerator x))
        (d (denominator x)))
    (ocons (intoo n)
           (intoo d))))

(defthm op-rationaltoo
  (implies
   (rationalp x)
   (o-p (rationaltoo x))))

(defthmd equal-rational-reduction
  (implies
   (and
    (syntaxp (and (symbolp x) (symbolp y)))
    (rationalp x)
    (rationalp y))
   (equal (equal x y)
          (equal (* (/ (DENOMINATOR X)) (NUMERATOR X))
                 (* (/ (DENOMINATOR y)) (NUMERATOR y))))))


(defthm equal-rationaltoo-reduction
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (equal (equal (rationaltoo x) (rationaltoo y))
          (equal x y)))
  :hints (("Goal" :in-theory (e/d (equal-rational-reduction)
                                  (EQUAL-*-/-1 RATIONAL-IMPLIES2)))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))))

(in-theory (disable rationaltoo))

(defun complextoo (x)
  (declare (type complex x))
  (let ((r (realpart x))
        (i (imagpart x)))
    (ocons (rationaltoo r)
           (rationaltoo i))))

(defthm op-complextoo
  (implies
   (complex-rationalp x)
   (o-p (complextoo x))))

(defthm equal-complextoo-reduction
  (implies
   (and
    (complex-rationalp x)
    (complex-rationalp y))
   (equal (equal (complextoo x) (complextoo y))
          (equal x y))))

(in-theory (disable complextoo))

(defun numtoo (x)
  (declare (type (satisfies acl2-numberp) x))
  (if (COMPLEX-RATIONALP x)
      (ocons 0 (complextoo x))
    (ocons 1 (rationaltoo x))))

(defthm op-numtoo
  (implies
   (acl2-numberp x)
   (o-p (numtoo x))))

(defthm equal-numtoo-reduction
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y))
   (equal (equal (numtoo x) (numtoo y))
          (equal x y))))

(in-theory (disable numtoo))

(defun atomtoo (x)
  (declare (type (satisfies atom) x))
  (cond
   ((acl2-numberp x)
    (ocons 0 (numtoo x)))
   ((symbolp x)
    (ocons 1 (symboltoo x)))
   ((characterp x)
    (ocons 2 (chartoo x)))
   ((stringp x)
    (ocons 3 (stringtoo x)))
   (t
    (ocons 4 0))))

(defun good-atom (x)
  (declare (type t x))
  (or (acl2-numberp x)
      (symbolp x)
      (characterp x)
      (stringp x)))

(defthm equal-atomtoo-reduction
  (implies
   (and
    (good-atom x)
    (good-atom y))
   (equal (equal (atomtoo x) (atomtoo y))
          (equal x y))))

(defthm op-atomtoo
  (o-p (atomtoo x)))

(in-theory (disable atomtoo))
(in-theory (disable good-atom))

(defun good-term (x)
  (declare (type t x))
  (if (consp x)
      (and (good-term (car x))
           (good-term (cdr x)))
    (good-atom x)))

(defun *too (x)
  (declare (type t x)
           (xargs :verify-guards nil))
  (if (consp x)
      (ocons 0 (ocons (*too (car x))
                      (*too (cdr x))))
    (ocons 1 (atomtoo x))))

(defthm op-*too
  (o-p (*too x)))

(defun *too-induction (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (consp x)
      (if (consp y)
          (cons (*too-induction (car x) (car y))
                (*too-induction (cdr x) (cdr y)))
        (cons (*too-induction (car x) y)
              (*too-induction (cdr x) y)))
    (if (consp y)
        (cons (*too-induction x (car y))
              (*too-induction x (cdr y)))
      (list x y))))

(defthmd equal-*too-reduction
  (implies
   (and
    (good-term x)
    (good-term y))
   (equal (equal x y)
          (equal (*too x) (*too y))))
  :hints (("Goal" :induct (*too-induction x y))))

(defun o<< (x y)
  (declare (type t x y))
  (o< (*too x) (*too y)))

(in-theory (disable *too))
(in-theory (disable good-term))

(defthmd ordinal-order-property
  (implies
   (and (good-term x)
        (good-term y))
   (equal (equal x y)
          (and (not (o<< x y))
               (not (o<< y x)))))
  :hints (("Goal" :in-theory (enable equal-*too-reduction
                                     ordinal-double-containment))))

(defthm o<<-is-well-founded
  (and (o-p (*too x))
       (implies (o<< x y)
                (o< (*too x) (*too y))))
  :rule-classes (:well-founded-relation))

(in-theory (disable o<<))

(defthm not-hide-forward
  (implies
   (not (hide x))
   (not x))
  :hints (("Goal" :expand (hide x)))
  :rule-classes (:forward-chaining))

(defthm not-rewrite-equiv-forward
  (implies
   (not (rewrite-equiv term))
   (not term))
  :rule-classes (:forward-chaining))

(defun member? (x list)
  (declare (type t x list))
  (if (consp list)
      (or (equal x (car list))
          (member? x (cdr list)))
    nil))

(defun equiv-term (equivs term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
         (and (member? (car term) equivs)
              (consp (cdr term))
              (consp (cddr term))
              (not (equal (cadr term) (caddr term)))
              term))))

;; In general, we probably want to rewrite smaller terms with larger terms.
;; For now we just rewrite variables into terms.

(defun optimize-equiv-term (term)
  (declare (type t term))
  (if (and (consp term)
           (consp (cdr term))
           (consp (cddr term))
           (symbolp (caddr term)))
      `(,(car term) ,(caddr term) ,(cadr term))
    term))

;; There may be some advantage to doing this slowly (one at a time).
;; Perhaps a hint to that effect ..

(defun rewrite-equiv-hint (once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (equiv-term equivs term)))
          (if term
              (rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if cases
        (if once nil
          `(:computed-hint-replacement ((rewrite-equiv-hint 't 'nil ',equivs clause)) :cases (,@cases)))
      (if once
          ;; When the following is tried:
          ;; `(:computed-hint-replacement  ((rewrite-equiv-hint 'nil 'nil clause)))
          ;;
          ;; ACL2 produces the following error:

          `(:computed-hint-replacement  ((rewrite-equiv-hint 'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defun step-rewrite-equiv-hint (stable once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (and stable (consp clause))
      (let ((term (car clause)))
        (let ((term (equiv-term equivs term)))
          (if term
              (rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if (and stable cases)
        (if once nil
          `(:computed-hint-replacement ((step-rewrite-equiv-hint stable-under-simplificationp
                                                            't 'nil ',equivs clause)) :cases (,@cases)))
      (if (and stable once)
          `(:computed-hint-replacement  ((step-rewrite-equiv-hint stable-under-simplificationp
                                                             'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defun equiv-var-term (equivs term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
         (and (member? (car term) equivs)
              (consp (cdr term))
              (consp (cddr term))
              (if (symbolp (cadr term))
                  (not (symbolp (caddr term)))
                (if (symbolp (caddr term))
                    (not (symbolp (cadr term)))
                  nil))
              (not (equal (cadr term) (caddr term)))
              term))))

(defun find-equiv (equivs clause)
  (declare (type t clause))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (equiv-var-term equivs term)))
          (or term (find-equiv equivs (cdr clause)))))
    nil))

#+joe
(defun slow-rewrite-equiv-hint (once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (equiv-var-term equivs term)))
          (if term
              (slow-rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (slow-rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if cases
        (if once nil
          `(:computed-hint-replacement ((slow-rewrite-equiv-hint 't 'nil ',equivs clause)) :cases (,@cases)))
      (if once
          `(:computed-hint-replacement  ((slow-rewrite-equiv-hint 'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defun slow-rewrite-equiv-hint (stbl once equivs clause)
  (declare (type t clause))
  (if stbl
      (let ((term (find-equiv equivs clause)))
        (if term
            (if once nil
              (let ((term `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))))
                `(:computed-hint-replacement
                  ((slow-rewrite-equiv-hint stable-under-simplificationp 't ',equivs clause))
                  :cases (,term))))
          (if once
              `(:computed-hint-replacement
                ((slow-rewrite-equiv-hint stable-under-simplificationp 'nil ',equivs clause)) :cases (t))
            nil)))
    nil))

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

(defun pseudo-termp-key (arg term)
  (declare (type t arg term))
  (if arg (pseudo-term-listp term)
    (pseudo-termp term)))

(defun beta-reduce-term (arg term keys vals)
  (declare (type (satisfies true-listp) keys vals))
  (declare (xargs :guard (pseudo-termp-key arg term)))
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (beta-reduce-term nil (car term) keys vals)
              (beta-reduce-term arg (cdr term) keys vals)))))
   (t
    (cond
     ((and (symbolp term) term)
      (if (member term keys)
          (cdr (assoc-eq term (pairlis$ keys vals)))
        '(quote nil)))
     ((atom term) term)
     ((eq (car term) 'quote) term)
     ((consp (car term))
      (cons (car term) (beta-reduce-term t (CDR term) keys vals)))
     ((equal (car term) 'hide)
      (list 'hide (beta-reduce-term nil (cadr term) keys vals)))
     ((equal (car term) 'unhide)
      (list 'unhide (beta-reduce-term nil (cadr term) keys vals)))
     (t
      (cons (car term) (beta-reduce-term t (cdr term) keys vals)))))))

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

(defthmd unhide-eval-key-beta-reduce-term
  (implies
   (and
    (wf-beta-term arg term)
    (equal (len keys) (len vals)))
   (equal (unhide-eval-key arg (beta-reduce-term arg term keys vals) a1)
          (unhide-eval-key arg term (pairlis$ keys
                                              (unhide-eval-key t vals a1)))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :do-not-induct t
            :induct (beta-reduce-term arg term keys vals)
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

(defthm unhide-eval-beta-reduce-term
  (implies
   (and
    (wf-beta-term nil term)
    (equal (len keys) (len vals)))
   (equal (unhide-eval (beta-reduce-term nil term keys vals) a1)
          (unhide-eval term (pairlis$ keys (unhide-eval-list vals a1)))))
  :hints (("Goal" :use (:instance unhide-eval-key-beta-reduce-term
                                  (arg nil))
           :in-theory (enable unhide-eval-key-reduction))))

(defthm unide-eval-to-beta-reduce-term
  (implies
   (and
    (lambda-expr-p term)
    (pseudo-termp term))
   (equal (unhide-eval term a1)
          (unhide-eval (beta-reduce-term nil (CAR (CDR (CDR (CAR term))))
                                         (CAR (CDR (CAR term)))
                                         (cdr term)) a1))))

(defun beta-reduce-lambda-expr (term)
  (declare (type (satisfies lambda-expr-p) term)
           (type (satisfies pseudo-termp) term)
           (xargs :guard-hints (("Goal" :in-theory (enable lambda-expr-p)))))
  (beta-reduce-term nil (CAR (CDR (CDR (CAR term))))
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

(defun beta-reduce-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (hide-p term)
      (let ((arg (cadr term)))
        (if (lambda-expr-p arg)
            `(hide ,(beta-reduce-lambda-expr arg))
          term))
    term))

(defthmd *meta*-beta-reduce-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (beta-reduce-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (hide))))


(defun unhide-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (unhide-p term)
      (let ((arg (cadr term)))
        (if (hide-p arg)
            (let ((arg (cadr arg)))
              (if (lambda-expr-p arg)
                  `(unhide (hide ,(beta-reduce-lambda-expr arg)))
                term))
          term))
    term))

;; We cannot turn this into a :meta rule because of our
;; additional evaluator constraints.
;;
;; But we can at least try it out:
;;   (unhide-hide-wrapper '(unhide (hide ((lambda (x y z) (+ x y)) (foo a) (goo b) (foo (quote 3))))))
;;     => '(+ (FOO A) (GOO B))
;;
(defthm *meta*-unhide-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (unhide-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (unhide))))

(in-theory (disable unhide))

(in-theory (disable unhide))

#|

(defund fn (a b)
  (if (consp a)
      (fn (cdr a) b)
    (list (cons a a) b)))

|#

;; Substitution from the hypothesis works with equivalences, but
;; probably would not work for (fix ..).

(defun nequiv (x y) (equal (nfix x) (nfix y)))

(defthm equal-into-equiv
  (iff (equal q (nfix x))
       (and (natp q)
        (nequiv q x))))

;; One can, however, emulate such substitution using free-variables.
;; How expensive is this?  Would this be a long-term solution for
;; this kind of problem?  Note that this solution wouldn't support
;; refinements, either.

(defthm free-variable-substitution
  (implies
   (and
    (equal (nfix x a) (nfix y a))
    (syntaxp (simpler y x)))
   (equal (nfix x a)
      (nfix y a))))

;; There may be a number of things that the poor man's version
;; of context rewriting will not do (that an integrated solution
;; might be expected to do) due to the fact that the poor man's
;; version is rewriting in a backchaining context.  One example
;; is rewriting into an "if" :

(defthm fix-case-split
  (equal (mod x n) (if (test x n) (foo x) (goo n))))

(defthm substitution-of-equals
  (implies
   (equal (z) (fix y))
   (pred (foo y))))

(defthm
  (equal (mod (foo x) n)
     (goo y)))

(defthm static-context-refinement
  (implies
   (and
    (integerp p)
    (equiv2 (mod x1 (* p 2))
        (mod x2 (* p 2))))
   (equiv1 (mod x1 p)
       (mod x2 p)))
  :rule-classes ((:context-refinement (equiv2 (mod x (* p 2)) 1)
                      (equiv1 (mod x p) 1))))

;; When rewriting within a context, certain context congruence rules may be
;; activated.  Such rules pattern match on context elements as well as on the
;; term being rewritten.  If a match is found, a new context is created and
;; used to rewrite the term indicated in the conclusion.

(defthm context-congruence
  (implies
   (and
    (not (complexp x1))  ; <- these kind of hyps can be "expensive" causing
             ; multiple rewrites of x1
    (not (complexp y))
    (equiv2 (mod x1 (* 2 n))
        (mod x2 (* 2 n))))
   (equiv1 (mod (+ x1 y) n)
       (mod (+ x2 y) n)))
  :rule-classes ((:context-congurence (equiv2 (mod x (* 2 n)) 1)
                      (equiv1 (mod (+ x1 y) n) 1 1))))

;; Simple rewrite rules are applied following a contextual rewriting of a
;; term.  Consider rewriting the form (mod term n).  We first rewrite "term"
;; in the context (equiv (mod . n) 1).  [Note that "equiv" in this context is
;; simply the weakest equiv relation that ACL2 knows about from any
;; :congruence theorems about mod].  Assuming that the rewriter returns (foo
;; x) as a result of rewriting "term" in this context, the rewriter then
;; reconstructs the term (mod (foo x) n) and searches for a rule that pattern
;; matches this new expression.  If it finds such a rule, it applies it and
;; simplifies the result.  [Note that kind of rewriting is _not_ done when
;; applying context congruence rules].

(defthm simple-rewrite
  (implies
   (hyps x)
   (equal (mod (foo x) 20)
      (hoo x))))

;; While static context refinement allows us to create a static list of
;; contexts in which a term should be rewritten, it may not be desirable (or
;; possible) to to enumerate all possible contexts that we may wish to use
;; while rewriting a term. This becomes evident when we consider the fact
;; that, for (mod x n), every multiple of "n" defines a refining context for
;; (mod x n).  While simple rewrite rules can be used to detect this case, we
;; may have an instance where we have:

;; How do we apply this rule in our current context if our current context is
;; (mod x 2)?  The solution to this is to apply dynamic context refinement
;; rules.  Dynamic context refinement rules are context refinement rules with
;; free variables.

(defthm dynamic-context-refinement
  (implies
   (and
    (integerp n1)
    (integerp n2)
    (< n1 n2)
    (equal (gcd n1 n2) n1)
    (equal (mod x1 n2)
       (mod x2 n2)))
   (equal (mod x1 n1)
      (mod x2 n1)))
  :rule-classes ((:context-refinement (equal (mod x n2) 1)
                      (equal (mod x n1) 1))))

;; In order to apply dynamic context refinement, we must somehow instantiate
;; the dynamic context refinement rules.  We do this by appealing to the
;; context rewrite.  The context instance is used to instantiate any free
;; variables appearing in an applicable dynamic-context-refinement rule.

(defthm mod-foo-20
  (implies
   (hyps x)
   (equal (mod (foo x) 20)
      (mod (hoo x) 20)))
  :rule-classes (:rewrite
         (:context (equal (mod x 20) 1))))

(defthm g-a-from-g-list
  (implies
   (and
    (hyps st1)
    (equal (g-list (foo-dia a st1) st1)
       (g-list (foo-dia a st1) st2))
    )
   (equal (g a (foo st1))
      (g a (foo st2)))))

(defthm g-list-from-g-list
  (implies
   (and
    (hyps st1)
    (equal (g-list (foo-dia* list st1) st1)
       (g-list (foo-dia* list st1) st2)))
   (equal (g-list list (foo st1))
      (g-list list (foo st2)))))



(defthm domain-context
  (implies
   (pred st)
   (equal (foo st)
      (foo (cp list st nil)))))

(defthm mod-fix-point
  (implies
   (and
    (equal x (mod a n))
    (equal y (mod b n))
    (syntaxp (and (not (equal x a))
          (not (equal y b)))))
   (equal (mod (+ a b) n)
      (mod (+ x y) n))))

(defthm domain-context
  (implies
   (and
    (pred st)
    (equiv st2
       (cp list st1)))
   (equal (foo st1)
      (foo st2))))
