
(in-package "ACL2")
(include-book "bstar")

;; This book provides a macro WITH-QUOTED-FORMS which may be
;; useful for computing complicated :USE hints.  Often we have a term
;; in which there are many nested variable bindings and we want to
;; instantiate a theorem by setting certain free variables of the
;; theorem to the bound value of some deeply-nested variable of our
;; term.  For example, say we have the term:

;; (let* ((c (foo a b))
;;        (d (bar c a))
;;        (e (baz d c b)))
;;   ...)

;; and that we want to instantiate a theorem TH with variable x bound
;; to the value of E in the above expression.  Ordinarily, we would
;; manually expand the binding of E in order to create the use hint:
;; :use ((:instance th
;;                  (x (baz (bar (foo a b) a) (foo a b) b))))
;; With more complicated sequences of bindings, this can be quite
;; tedious and error-prone.  Using our macro, one can instead write
;; the hint as a computed hint as follows:
;; (with-quoted-forms
;;  (let* ((c (foo a b))
;;         (d (bar c a))
;;         (e (baz d c b)))
;;    `(:use ((:instance th (x ,(fq e)))))))
;; Note that we simply have copied the let* bindings from above, and
;; that where we want the term of E to appear, we instead used the
;; form (fq e).  The result of evaluating this form is the desired use
;; hint from above.

;; How does this work?  First, the form is translated so as to expand
;; away any macros.  Next, it is fully beta-reduced: lambdas are
;; eliminated by replacing occurrences of variables in their bodies
;; with the corresponding bindings.  However, during this process,
;; occurrences of the function FQ (stands for "form-quote") are
;; treated differently: they are turned into quotes after their
;; arguments are beta-reduced.  Thus the occurrence of (FQ E) is
;; replaced by (QUOTE (BAZ (BAR (FOO A B) A) (FOO A B) B)) in the
;; expression above.  Finally, the resulting form is evaluated.

;; Note that the expansion of WITH-QUOTED-FORMS is a call that takes
;; STATE and produces a value-triple.  This is necessary so that it
;; can translate (macroexpand) the given term.

(defthm alistp-pairlis$
  (alistp (pairlis$ a b)))


(mutual-recursion
 (defun beta-reduce-with-quotes (x alist)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp alist))))
   (cond ((eq x nil) nil)
         ((atom x)
          (let ((look (assoc x alist)))
            (if look (cdr look) x)))
         ((eq (car x) 'quote) x)
         ((eq (car x) 'fq)
          (cons 'quote (beta-reduce-with-quotes-list (cdr x) alist)))
         ((symbolp (car x))
          (cons (car x) (beta-reduce-with-quotes-list (cdr x) alist)))
         (t (beta-reduce-with-quotes
             (caddar x)
             (pairlis$ (cadar x)
                       (beta-reduce-with-quotes-list
                        (cdr x) alist))))))
 (defun beta-reduce-with-quotes-list (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp alist))))
   (if (atom x)
       nil
     (cons (beta-reduce-with-quotes (car x) alist)
           (beta-reduce-with-quotes-list (cdr x) alist)))))

(defun fq (x) x)

(defun with-quoted-forms-fn (form state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er trans)
        (translate form '(nil) nil nil 'with-quoted-var-terms
                   (w state) state))
       (reduce (beta-reduce-with-quotes trans nil))
       ((er (cons & val))
        (simple-translate-and-eval
         reduce nil nil
         "Term for with-quoted-forms"
         'with-quoted-var-terms
         (w state) state)))
    (value val)))

(defmacro with-quoted-forms (form)
  `(with-quoted-forms-fn ',form state))



;; VAR-FQ-BINDINGS makes a list of bindings appropriate for use in a
;; substitution list for a use hint, where each variable name is bound to its
;; FQ.  For example, these two are equivalent:
;;    `(:use ((:instance foo (a ,(fq a)) (b ,(fq b)))))))
;;    `(:use ((:instance foo . ,(var-fq-bindings (a b)))))))

(defun var-fq-bindings-lst (vars)
  (if (atom vars)
      nil
    (cons ``(,',(car vars) ,(fq ,(car vars)))
          (var-fq-bindings-lst (cdr vars)))))


(defmacro var-fq-bindings (vars)
  (cons 'list (var-fq-bindings-lst vars)))
