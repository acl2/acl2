#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "SYN")
(include-book "syntax-extensions")
(include-book "defevaluator")

(defun syn::len (n list)
  (declare (type (integer 0 *) n))
  (acl2::if (acl2::consp list)
      (acl2::if (zp n) acl2::nil
	(len (1- n) (acl2::cdr list)))
    (acl2::and (acl2::null list) (= n 0))))

(defthm open-len
  (implies
   (syntaxp (acl2::quotep n))
   (equal (len n list)
	  (acl2::if (acl2::consp list)
	      (acl2::if (zp n) acl2::nil
		(len (1- n) (acl2::cdr list)))
	    (acl2::and (acl2::null list) (= n 0))))))

(defun nth (n l)
  (declare (type (integer 0 *) n))
  (acl2::and (acl2::consp l)
	     (acl2::if (zp n)
		 (acl2::car l)
	       (nth (+ -1 n) (acl2::cdr l)))))

(defthm open-nth
  (implies
   (syntaxp (acl2::quotep n))
   (equal (nth n l)
	  (acl2::and (acl2::consp l)
		     (acl2::if (zp n)
			 (acl2::car l)
			 (nth (+ -1 n) (acl2::cdr l)))))))
	  
(defthm len-implies-true-listp
  (implies
   (len n list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defthm len-implies-acl2-len
  (implies
   (len n list)
   (equal (acl2::len list) n))
  :rule-classes (:linear :forward-chaining))

(defun syn::consp (term)
  (declare (type t term))
  (acl2::and 
   (len 3 term)
   (equal (acl2::car term) 'acl2::cons)))

(defun syn::cons (a b)
  (declare (type t a b))
  `(acl2::cons ,a ,b))

(defun syn::car (term)
  (declare (type (satisfies syn::consp) term))
  (cadr term))

(defun syn::cdr (term)
  (declare (type (satisfies syn::consp) term))
  (caddr term))

(local
 (defthm cons-reconstruction
   (implies
    (syn::consp term)
    (equal (syn::cons (syn::car term) (syn::cdr term))
	   term))))

(defun syn::quotep (term)
  (declare (type t term))
  (acl2::and (len 2 term)
	     (equal (acl2::car term) 'acl2::quote)))

(defun syn::enquote (term)
  (declare (type t term))
  `(acl2::quote ,term))

(defun syn::dequote (term)
  (declare (type (satisfies syn::quotep) term))
  (cadr term))

(local
 (defthm quote-reconstruction
   (implies
    (syn::quotep term)
    (equal (syn::enquote (syn::dequote term))
	   term))))

(defmacro syn::arg (n term)
  `(nth ,n ,term))

(defun syn::appendp (term)
  (declare (type t term))
  (acl2::and (syn::len 3 term)
	     (equal (acl2::car term) 'binary-append)))

(defun syn::append (x y)
  (declare (type t x y))
  `(acl2::binary-append ,x ,y))

(local
 (defthm append-reconstruction
   (implies
    (syn::appendp term)
    (equal (syn::append (syn::arg 1 term) (syn::arg 2 term))
	   term))))

(defun syn::ifp (term)
  (declare (type t term))
  (acl2::and (syn::len 4 term)
	     (equal (acl2::car term) 'acl2::if)))

(defun syn::if (a b c)
  (declare (type t a b c))
  `(acl2::if ,a ,b ,c))

(local
 (defthm if-reconstruction
   (implies
    (syn::ifp term)
    (equal (syn::if (syn::arg 1 term) (syn::arg 2 term) (syn::arg 3 term))
	   term))))

(defun syn::nil ()
  (declare (xargs :verify-guards t))
  `(syn::quote acl2::nil))

(defun syn::null (x)
  (declare (type t x))
  (equal x (syn::nil)))

(defun syn::true ()
  (declare (xargs :verify-guards t))
  `(syn::quote t))

;; Perhaps this should be weakened to ((cadr x) != nil) ??

(defun syn::truep (x)
  (declare (type t x))
  (acl2::and (acl2::consp x)
	     (acl2::equal (acl2::car x) 'quote)
	     (acl2::consp (acl2::cdr x))
	     (acl2::equal (acl2::cadr x) 't)))

(defun syn::conjoin (x y)
  (declare (type t x y))
  (acl2::cond
   ((acl2::not (acl2::and x y))
    acl2::nil)
   ((syn::truep y)
    x)
   ((syn::truep x)
    y)
   (acl2::t
    (syn::if x y (syn::nil)))))

(defun syn::and-fn (args)
  (declare (type t args))
  (acl2::if (acl2::consp args)
	    `(syn::conjoin ,(acl2::car args) ,(syn::and-fn (acl2::cdr args)))
	    `(syn::true)))

(defmacro syn::and (&rest args)
  (syn::and-fn args))

(defun syn::funcall (fn args term)
  (declare (type (integer 0 *) args))
  (acl2::and (syn::len (1+ args) term)
	     (equal (acl2::car term) fn)))

(defmacro syn::apply (fn &rest args)
  `(list ',fn ,@args)) 

(defevaluator eval eval-list
  (
   (acl2::equal x y)
   (acl2::consp x)
   (acl2::cons x y)
   (acl2::binary-append x y)
   (acl2::if a b c)
   ))

(defmacro extend-eval (name fns)
  `(syn::defevaluator ,name ,(symbol-fns::suffix name '-list)
     (
      (acl2::equal x y)
      (acl2::consp x)
      (acl2::cons x y)
      (acl2::binary-append x y)
      (acl2::if a b c)
      ,@fns
      )))

(defun syn::consp-rec (x)
  (declare (type t x))
  (cond
   ((syn::consp x) t)
   ((syn::appendp x)
    (or (syn::consp-rec (syn::arg 1 x))
	(syn::consp-rec (syn::arg 2 x))))
   ((syn::quotep x)
    (acl2::consp (syn::dequote x)))
   (t
    acl2::nil)))

(defthm consp-rec-implies-consp
  (implies
   (syn::consp-rec term)
   (acl2::consp (syn::eval term a))))

(defun free-var-bindings (w1 w2 term)
  (declare (type symbol w1 w2))
  (acl2::let ((list (symbol-fns::collect-variables term)))
    (symbol-fns::join-lists (symbol-fns::map-symbol-list-to-package list w1)
			    (symbol-fns::map-symbol-list-to-package list w2))))

(defmacro defevthm (ev name thm &rest key-args)
  `(defthm ,(symbol-fns::prefix ev '- name)
     ,thm
     :hints (("Goal"
              :in-theory (enable ,(symbol-fns::suffix ev '-constraint-0))
              :use (:functional-instance 
			   (:instance ,name
				      ,@(free-var-bindings name ev thm))
			   (syn::eval      ,ev)
			   (syn::eval-list ,(symbol-fns::suffix ev '-list)))))
     ,@key-args))

(defthm type-alistp-to-type-alist-entryp
  (implies
   (acl2::and
    (acl2::type-alistp term)
    (acl2::consp term))
   (acl2::type-alist-entryp (acl2::car term)))
  :rule-classes (:forward-chaining))

(defthm type-alist-entryp-implies-pseudo-termp-car
  (implies
   (acl2::type-alist-entryp entry)
   (acl2::pseudo-termp (acl2::car entry)))
  :hints (("goal" :in-theory (enable acl2::type-alist-entryp)))
  :rule-classes (:forward-chaining))

(defthm pseudo-term-listp-from-pseudo-termp
  (implies
   (acl2::and
    (acl2::pseudo-termp term)
    (not (equal (acl2::car term) 'quote)))
   (acl2::pseudo-term-listp (acl2::cdr term)))
  :hints (("goal" :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-term-listp-of-cdr
  (implies (acl2::pseudo-term-listp x)
           (acl2::pseudo-term-listp (acl2::cdr x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-of-car
  (implies (acl2::pseudo-term-listp x)
           (acl2::pseudo-termp (acl2::car x)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-termp-nth
  (implies
   (acl2::pseudo-term-listp list)
   (acl2::pseudo-termp (syn::nth n list)))
  :hints (("goal" :in-theory (enable acl2::pseudo-term-listp syn::nth))))

(defthm pseudo-termp-nth-from-pseudo-termp
  (implies
   (acl2::and
    (acl2::pseudo-termp term)
    (acl2::consp term)
    (< 0 (nfix n))
    (not (equal (acl2::car term) 'quote)))
   (acl2::pseudo-termp (syn::nth n term)))
  :hints (("goal" :expand (syn::nth n term))))

(defthm pseudo-termp-forward-to-true-listp
  (implies (acl2::and (acl2::pseudo-termp x)
		      (acl2::consp x))
           (acl2::true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-termp-of-cons-when-symbolp
 (implies (acl2::and (acl2::symbolp a)
		     (not (equal a 'quote)))
          (equal (acl2::pseudo-termp (acl2::cons a rest))
                 (acl2::pseudo-term-listp rest)))
 :hints (("Goal" :expand  (pseudo-termp (acl2::cons a rest))
          :in-theory (enable acl2::pseudo-termp))))

(defthm pseudo-term-listp-of-cons
  (equal (acl2::pseudo-term-listp (acl2::cons a rest))
         (acl2::and (acl2::pseudo-termp a)
		    (acl2::pseudo-term-listp rest)))
  :hints (("Goal" :in-theory (enable acl2::pseudo-term-listp))))

(defthm pseudo-termp-of-cadr
  (implies (acl2::and (acl2::pseudo-termp term)
		      (not (equal (acl2::car term) 'quote))
		      (acl2::consp term)
		      (acl2::consp (acl2::cdr term)))
           (acl2::pseudo-termp (acl2::cadr term)))
  :hints (("Goal" :expand  (acl2::pseudo-termp term)
           :in-theory (enable acl2::pseudo-termp))))

(defthm iff-conjoin
  (iff (syn::conjoin x y)
       (acl2::and x y))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm pseudo-termp-conjoin
  (implies
   (acl2::and
    (acl2::pseudo-termp x)
    (acl2::pseudo-termp y))
   (acl2::pseudo-termp (syn::conjoin x y))))    

(in-theory (disable syn::nth syn::open-nth))
(in-theory (disable syn::conjoin))

