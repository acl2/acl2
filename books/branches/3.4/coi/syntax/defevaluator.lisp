#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defun syn::defevaluator-form (evfn evfn-lst fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses evfn fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    (symbol-name (pack2 evfn '-constraint-))
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      
      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
             (defun evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
			       :hints (("goal" :do-not '(preprocess) :in-theory (disable o< acl2-count)))
                               :mode :logic))
               (cond
                ((symbolp x) (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
	   (local (in-theory *defevaluator-form-base-theory*))
	   (local (in-theory (enable evfn evfn-lst)))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
           . defthms)))))

(defmacro syn::defevaluator (&whole x evfn evfn-lst fn-args-lst)

  (cond
   ((not (and (symbolp evfn)
              (symbolp evfn-lst)
              (symbol-list-listp fn-args-lst)))
    `(er soft '(defevaluator . ,evfn)
	       "The form of a defevaluator event is (defevaluator evfn ~
          evfn-lst fn-args-lst), where evfn and evfn-lst are symbols ~
          and fn-args-lst is a true list of lists of symbols.  ~
          However, ~x0 does not have this form."
	       ',x))
   (t
    (syn::defevaluator-form evfn evfn-lst fn-args-lst))))


(defthm o<-acl2-count-car
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cdr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAAR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caaddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDaR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-caadddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-cadaddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-caddadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDaR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-cadddar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR (car x)))
	       (ACL2-COUNT x))))

