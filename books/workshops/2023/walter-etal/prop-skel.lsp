#| Copyright © 2018 by Pete Manolios 

 Derived from an assignment from Northeastern's CS4820 course in Fall
 2018, taught by Pete Manolios.

|#

(in-package "ACL2")

#| 
 The point of the next two forms is that we can use ACL2s from within
 lisp. That will be useful to check that your code works.
|#

#|

 Here are some examples you can try to see how acl2s-query works.

 (acl2s-query '(+ 1 2))
 (acl2s-query '(thm (iff (implies p q)
                         (or (not p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. You can see the online
 documentation for the other software libraries.

|#

;;(load "interface/acl2s-interface.lisp")
(ql:quickload :trivia)
(ql:quickload :cl-ppcre)
(ql:quickload :let-plus)
(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

(proclaim '(optimize (debug 3)))

;; We import acl2s-query into our package.

(import 'acl2s-interface::acl2s-query)

;; Note that if we don't include this, it's a pain to deal with
;; symbols (note that and,or,not are all just imports of the CL
;; symbols in the ACL2/s packages)
(import 'acl2s::(implies iff => ^ v ! -> <-))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    ;; implied-by
    (<-      :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

(defun add-p-op-alias (orig-name alias-name)
  (let ((orig-entry (assoc orig-name *p-ops* :test #'equal)))
    (unless orig-entry (error "Can't find p-op with the name ~S" orig-name))
    (push (cons alias-name (cddr orig-entry)) *p-ops*)))

(add-p-op-alias 'and '^)
(add-p-op-alias 'or 'v)
(add-p-op-alias 'not '!)
(add-p-op-alias 'implies '=>)
(add-p-op-alias 'implies '->)

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defun pfun-argsp (pop args)
  (and (in pop *p-funs*)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (eql arity '-)
                  (= (len args) arity))
              (every #'p-formulap args)))))

(defun pfun-formulap (f)
  (and (consp f)
       (pfun-argsp (car f) (cdr f))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t)
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(<- (bar y) (foo x))))
(assert (p-formulap '(iff p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#


#|

 These functions return two values: the first being the propositional
 skeleton of the argument(s) and the second being a mapping from
 uninterpreted function calls to variables.

|#

;; args is a list of expressions to skeleton-ize
;; amap is the current mapping from uninterpreted function calls to variables
;; acc is the current accumulator for processed
;; abstract-termp is a predicate that should return a truthy value
;;   if the given term should be abstracted, and nil otherwise.
(defun p-skeleton-args (args amap acc abstract-termp)
  (if (endp args)
      (values (reverse acc) amap)
    (multiple-value-bind (new-arg new-amap)
        (p-skeleton- (car args) amap abstract-termp)
      (p-skeleton-args (cdr args) new-amap (cons new-arg acc) abstract-termp))))

(defun p-skeleton- (f amap abstract-termp)
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (cond ((p-funp pop)
            (multiple-value-bind (nargs namap)
              (p-skeleton-args args amap nil abstract-termp)
              (values (cons pop nargs) namap)))
           ((funcall abstract-termp f)
            (let ((geta (get-alist f amap)))
              (if geta
                  (values geta amap)
                (let ((gen (gentemp "P")))
                  (values gen (acons f gen amap))))))
           (t (values f amap))))
    (_ (error "Not a p-formula"))))

(defun p-skeleton (f &key amap (abstract-termp #'(lambda (x) (declare (ignore x)) t)))
  (p-skeleton- f amap abstract-termp))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2 formulas.

|#

(defun to-acl2-no-pskel (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2"))
    ((list (or '! 'not) x)
     `(acl2::not ,(to-acl2-no-pskel x)))
    ((list* (or 'or 'v) args)
     `(acl2::or ,@(mapcar #'to-acl2-no-pskel args)))
    ((list* (or 'and '^) args)
     `(acl2::and ,@(mapcar #'to-acl2-no-pskel args)))
    ((or (list (or 'implies '=> '->) p q)
         (list '<- q p))
     `(acl2::implies ,(to-acl2-no-pskel p) ,(to-acl2-no-pskel q)))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2-no-pskel p))
    ((list* 'iff args)
     (acl2::xxxjoin 'iff
                    (mapcar #'to-acl2-no-pskel args)))
    ((list 'if test then else)
     (to-acl2-no-pskel (list 'or (list 'and test then) (list 'and (list 'not test) else))))
    (otherwise f)))

(defun to-acl2 (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name s) "ACL2"))
      ((list (or '! 'not) x)
       `(acl2::not ,(to-acl2 x)))
      ((list* (or 'or 'v) args)
       `(acl2::or ,@(mapcar #'to-acl2 args)))
      ((list* (or 'and '^) args)
       `(acl2::and ,@(mapcar #'to-acl2 args)))
      ((or (list (or 'implies '=> '->) p q)
           (list '<- q p))
       `(acl2::implies ,(to-acl2 p) ,(to-acl2 q)))
      ((list 'iff) t)
      ((list 'iff p) (to-acl2 p))
      ((list* 'iff args)
       (acl2::xxxjoin 'iff
                      (mapcar #'to-acl2 args)))
      ((list 'if test then else)
       (to-acl2 (list 'or (list 'and test then) (list 'and (list 'not test) else))))
      (otherwise s))))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list 'not x)
     (pvars- x))
    ((list* (or 'or 'v) args)
     (reduce #'append (mapcar #'pvars- args)))
    ((list* (or 'and '^) args)
     (reduce #'append (mapcar #'pvars- args)))
    ((or (list (or 'implies '=> ->) p q)
         (list '<- q p))
     (append (pvars- p) (pvars- q)))
    ((list* 'iff args)
     (reduce #'append (mapcar #'pvars- args)))
    (otherwise nil)))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))

(defun boolean-hyps (l)
  (cons 'and
        (mapcar #'(lambda (x) `(acl2::booleanp ,x))
                (mapcar #'to-acl2 l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal-formula (f g)
  (let* ((iff `(acl2::iff ,f ,g))
	 (pvars (pvars iff))
	 (aiff (to-acl2 iff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    `(acl2::implies ,bhyps (acl2::iff ,af ,ag))))

(defun acl2s-check-equal (f g)
  (acl2s-query
   `(acl2::thm ,(acl2s-check-equal-formula f g))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (equal (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (equal (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

; This will lead to an error (so comment it out after trying it).
; In sbcl :top get you out of the debugger.
;(assert-acl2s-equal 'p 'q)

; Here is how we can use ACL2 to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))
