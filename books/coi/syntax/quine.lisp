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
(include-book "syntax")

#|
((LAMBDA (X) (LIST X (LIST 'QUOTE X)))   <- program
 '(LAMBDA (X) (LIST X (LIST 'QUOTE X)))) <- data
|#

(defun quine-body-fn (name body history)
  ``(encapsulate ()
      (defmacro ,,name (name)
	(let ((history (cons (quote ,,name) (quote ,,history))))
	  (,,body (quote ,,body))))
      ))

(defmacro quine-body (name body history)
  (quine-body-fn name body history))

;; The following "quine" duplicates and augments its own macro
;; definition, creating a new macro definition (with the provided
;; name) and adding its own name to a "history" list.

(defmacro quine (name)
  (let ((history (list 'quine)))
    ((lambda (body)
       (quine-body name body history))
     `(lambda (body)
	,(quine-body-fn 'name 'body 'history)))))

#|

;; Extending an existing evaluator.
;;
;; Perhaps, rather than generating quines, we should generate the list
;; of function symbols previously employed. (nah, too simple! :)
;;
;; Do we also want to prove something about the new evaluator?
;;
;; What about rules that we might wish one day to extend?
;;

(defmacro defevalextend (&whole x ev-fn fn-lst)

  (cond
   ((not (and (symbolp ev-fn)
              (symbol-list-listp fn-lst)))
    `(er soft '(defextendeval . ,ev-fn)
	 "The form of a defevaluator event is (defevaluator evfn ~
          evfn-lst fn-args-lst), where evfn and evfn-lst are symbols ~
          and fn-args-lst is a true list of lists of symbols.  ~
          However, ~x0 does not have this form."
	 ',x))
   (t
    (syn::defevaluator-form evfn evfn-lst fn-args-lst))))


  (let ((history (list 'foo)))
    ((lambda (body)
       (foo-body name body history))
     `(lambda (body)
	,(foo-body-fn 'name 'body 'history)))))

(LAMBDA (BODY)
        (LIST 'ENCAPSULATE
              'NIL
              (LIST 'DEFMACRO
                    NAME '(NAME)
                    (LIST (LIST 'LAMBDA
                                '(HISTORY)
                                (LIST BODY (LIST 'QUOTE BODY)))
                          (LIST 'CONS
                                (LIST 'QUOTE NAME)
                                (LIST 'QUOTE HISTORY))))))

(defmacro quine (name)
  (let ((history (list 'quine)))
    (let ((name (symbol-fns::suffix name '-macro)))
      ((lambda (body)
	 (list 'encapsulate '()
	       (list 'defmacro name '(name)
		     (list
		      (list 'lambda '(history)
			    (list body (list 'quote body)))
		      (list 'cons (list 'quote name) (list 'quote history))))))
       (quote (lambda (body)
		(list 'encapsulate '()
		      (list 'defmacro name '(name)
			    (list
			     (list 'lambda '(history)
				   (list body (list 'quote body)))
			     (list 'cons (list 'quote name) (list 'quote history)))))))))))

|#