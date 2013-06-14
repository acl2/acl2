#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
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

