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

(in-package "DEFUNG")

;; The body is decomposed into a cond expression.  The cond expression
;; makes distinctions between calls of fn

(include-book "coi/syntax/syntax" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "coi/util/skip-rewrite" :dir :system)

;; ==================================================================
;;
;; defung::true
;;
;; A wrapper to hide boolean expressions
;;
;; ==================================================================

(defun true-fn (x)
  (declare (type t x)) x)

(in-theory (disable (:type-prescription true-fn)))

(defthm quoted-true
  (implies
   (syntaxp (quotep x))
   (equal (true-fn (hide x)) x))
  :hints (("Goal" :expand (:free (x) (hide x))))
  :rule-classes (:rewrite))

(defthm true-from-x
  (implies x (true-fn (hide x)))
  :hints (("Goal" :expand (:free (x) (hide x))))
  :rule-classes (:rewrite :type-prescription))

(defthm not-true-from-not-x
  (implies (not x) (not (true-fn (hide x))))
  :hints (("Goal" :expand (:free (x) (hide x))))
  :rule-classes (:rewrite :type-prescription))

(defthm unnest-true
  (equal (true-fn (hide (true-fn (hide x))))
	 (true-fn (hide x)))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm true-id
  (equal (equal (true-fn (hide x)) x) t)
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm normalize-true
  (implies
   (and
    (bind-free (and (consp x) (equal (car x) 'hide) (acons 'arg (cadr x) nil)) (arg))
    (equal (hide arg) x)
    (equal narg (acl2::double-rewrite arg))
    (equal y  (acl2::double-rewrite (hide narg)))
    (syntaxp (not (equal x y))))
   (equal (defung::true-fn x)
	  (acl2::skip-rewrite (defung::true-fn y))))
  :hints (("Goal" :expand (:Free (x) (hide x)))))

(defthm open-true
  (equal (true-fn (hide x)) (double-rewrite x))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(in-theory (disable true-fn))

(defmacro defung::true (x)
  `(mbe :logic (defung::true-fn (hide ,x))
	:exec ,x))

(defund defung::true! (x)
  (declare (type t x))
  (if (and (consp x)
	   (or (equal (car x) 'defung::true)
	       (and (equal (car x) 'defung::true-fn)
		    (consp (cdr x))
		    (consp (cadr x))
		    (equal (caadr x) 'hide)))) x
    `(defung::true ,x)))

(defthm pseudo-termp-true!
  (implies
   (pseudo-termp x)
   (pseudo-termp (defung::true! x)))
  :hints (("Goal" :in-theory (enable defung::true!)))
  :rule-classes ((:forward-chaining :trigger-terms ((defung::true! x)))))

;; ==================================================================

(encapsulate
    ()

  (local
   (defthm acl2-count-syn-arg
     (implies
      (< (nfix i) (len term))
      (< (acl2-count (syn::arg i term))
	 (acl2-count term)))
     :hints (("Goal" :induct (syn::nth i term)
	      :in-theory (enable acl2-count syn::nth)))))

  (local
   (defthm syn-len-implication
     (implies
      (syn::len n list)
      (equal (len list) n))))

  (defthm acl2-count-syn-arg-2
    (implies
     (and
      (syn::funcall fn n term)
      (<= (nfix i) n))
     (< (acl2-count (syn::arg i term))
	(acl2-count term)))
    :rule-classes :linear)

  )

(local
(defthm pseudo-termp-arg-if-funcall
  (implies
   (and
    (syn::funcall 'if 3 term)
    (pseudo-termp term))
   (and (pseudo-termp (syn::arg 1 term))
	(pseudo-termp (syn::arg 2 term))
	(pseudo-termp (syn::arg 3 term))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable syn::funcall)))))

(in-theory (disable syn::funcall))

(defthm funcall-if-3-if
  (syn::funcall 'if 3 (syn::if test then else))
  :hints (("Goal" :in-theory (enable syn::if syn::funcall))))

(defthm args-if
  (and (equal (syn::arg 1 (syn::if test then else))
	      test)
       (equal (syn::arg 2 (syn::if test then else))
	      then)
       (equal (syn::arg 3 (syn::if test then else))
	      else))
  :hints (("Goal" :in-theory (enable syn::if syn::nth))))

(defthm pseudo-termp-if
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y)
    (pseudo-termp z))
   (pseudo-termp (syn::if x y z)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((syn::if x y z)))))

(in-theory (disable syn::if (:type-prescription syn::if)))

;; ==================================================================
;;
;; normalize-args
;;
;; normalizes the arguments to a procedure call.
;;
;; The function will pad the argument list with the value :default if
;; it must be extended while adding additional arguments to the
;; argument list as specified by each non-null entry in the sig.
;;
;; ==================================================================

(defun normalize-args (args sig)
  (declare (type (satisfies pseudo-term-listp) args sig))
  (if (endp sig) (if (consp args) (cw "** Error: normalize-args") nil)
    (let ((entry (car sig)))
      (if (null entry)
	  (if (atom args) (cons ':default (normalize-args nil (cdr sig)))
	    (cons (car args) (normalize-args (cdr args) (cdr sig))))
	(cons entry (normalize-args args (cdr sig)))))))

(defthm pseudo-term-listp-normalize-args
  (implies
   (and
    (pseudo-term-listp args)
    (pseudo-term-listp sig))
   (pseudo-term-listp (normalize-args args sig))))

(defthm len-normalize-args
  (equal (len (normalize-args args sig))
	 (len sig)))

;; ==================================================================
;;
;; remap-fn
;;
;; renaming procedure for
;;
;; ==================================================================

(defun not-quote-symbolp (fn)
  (declare (type t fn))
  (and (symbolp fn)
       (not (equal fn 'quote))))

(defthm implies-not-quote-symbolp
  (implies
   (and
    (symbolp fn)
    (not (equal fn 'quote)))
   (not-quote-symbolp fn))
  :rule-classes (:forward-chaining))

(defthm not-quote-symbolp-implication
  (implies
   (not-quote-symbolp fn)
   (and (symbolp fn)
	(not (equal fn 'quote))))
  :rule-classes (:forward-chaining))

(defun pseudo-fn-map (alist)
  (declare (type t alist))
  (if (consp alist)
      (and
       (let ((entry (car alist)))
	 (and (consp entry)
	      (not-quote-symbolp (car entry))
	      (let ((term (cdr entry)))
		(and (consp term)
		     (not-quote-symbolp (car term))
		     (pseudo-term-listp (cdr term))))))
       (pseudo-fn-map (cdr alist)))
    (null alist)))

(defthm pseudo-fn-map-implies-alistp
  (implies
   (pseudo-fn-map alist)
   (alistp alist))
  :rule-classes (:forward-chaining))

(defthm symbol-listp-implies-eqlable-listp
  (implies
   (symbol-listp x)
   (eqlable-listp x))
  :rule-classes (:forward-chaining))

(defun fn-map-keys (alist)
  (declare (type (satisfies pseudo-fn-map) alist))
  (if (endp alist) nil
    (cons (caar alist) (fn-map-keys (cdr alist)))))

(defthm symbol-listp-fn-map-keys
  (implies
   (pseudo-fn-map alist)
   (symbol-listp (fn-map-keys alist)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((fn-map-keys alist)))))

(defund map-fn-sig (f1 f2 sig)
  (declare (type (satisfies not-quote-symbolp) f1 f2)
	   (type (satisfies pseudo-term-listp) sig))
  (acons f1 (cons f2 sig) nil))

(defthm pseudo-fn-map-map-fn-sig
  (implies
   (and
    (not-quote-symbolp f1)
    (not-quote-symbolp f2)
    (pseudo-term-listp sig))
   (pseudo-fn-map (map-fn-sig f1 f2 sig)))
  :hints (("Goal" :in-theory (enable map-fn-sig)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((map-fn-sig f1 f2 sig)))))

(defund remap-fn (fn args alist)
  (declare (type (satisfies not-quote-symbolp) fn)
	   (type (satisfies pseudo-term-listp) args)
	   (type (satisfies pseudo-fn-map) alist))
  (let ((hit (assoc fn alist)))
    (if (not hit) (mv nil (cons fn args))
      (let ((term (cdr hit)))
	(let ((fn  (car term))
	      (sig (cdr term)))
	  (mv t (cons fn (normalize-args args sig))))))))

(defthm pseudo-termp-remap-fn
  (implies
   (and
    (pseudo-fn-map alist)
    (pseudo-term-listp args)
    (not-quote-symbolp fn))
   (pseudo-termp (val 1 (remap-fn fn args alist))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((remap-fn fn args alist))))
  :hints (("Goal" :in-theory (enable remap-fn))))

(defund remap-fn-hit (fn alist)
  (declare (type (satisfies not-quote-symbolp) fn)
	   (type (satisfies pseudo-fn-map) alist))
  (let ((hit (assoc fn alist)))
    (if (not hit) (mv nil fn nil)
      (let ((term (cdr hit)))
	(let ((fn  (car term))
	      (sig (cdr term)))
	  (mv t fn sig))))))

(defthm pseudo-termp-remap-fn-hit
  (implies
   (and
    (pseudo-fn-map alist)
    (not-quote-symbolp fn))
   (and (not-quote-symbolp (val 1 (remap-fn-hit fn alist)))
	(pseudo-term-listp (val 2 (remap-fn-hit fn alist)))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((remap-fn-hit fn alist))))
  :hints (("Goal" :in-theory (enable remap-fn-hit))))

;; ==================================================================
;;
;; opt-if
;;
;; optimizing if constructor
;;
;; ==================================================================

(defund unnot-test (test then else)
  (declare (type (satisfies pseudo-termp) test then else))
  (if (syn::funcall 'not 1 test)
      (syn::if (syn::arg 1 test) else then)
    (syn::if test then else)))

(defthm psueod-termp-unnot-test
  (implies
   (and
    (pseudo-termp test)
    (pseudo-termp then)
    (pseudo-termp else))
   (pseudo-termp (unnot-test test then else)))
  :hints (("Goal" :in-theory (enable syn::funcall unnot-test))))

(defun iff-fix-rec (iff negate ctx term)
  (declare (type (satisfies true-listp) ctx)
	   (type (satisfies pseudo-termp) term)
	   (xargs :verify-guards nil))
  (cond
   ((and iff (member-equal term ctx)) (if negate *nil* *t*))
   ((and iff (member-equal `(not ,term) ctx)) (if negate *t* *nil*))
   ((syn::funcall 'if 3 term)
    (let ((test (syn::arg 1 term))
	  (then (syn::arg 2 term))
	  (else (syn::arg 3 term)))
      (let ((then (iff-fix-rec iff negate (cons test ctx) then))
	    (else (iff-fix-rec iff negate (cons `(not ,test) ctx) else)))
	(if (equal then else) then
	  (if (and iff (equal then *t*) (equal else *nil*))
	      (iff-fix-rec t nil ctx test)
	    (if (and iff (equal then *nil*) (equal else *t*))
		(iff-fix-rec t t ctx test)
	      (let ((test (iff-fix-rec t nil ctx test)))
		(if (equal test *t*) then
		  (if (equal test *nil*) else
		    (unnot-test test then else))))))))))
   ((syn::funcall 'not 1 term)
    (iff-fix-rec t (not negate) ctx (syn::arg 1 term)))
   (t
    (if negate `(not ,term) term))))

(defthm pseudo-termp-iff-fix-rec
  (implies
   (pseudo-termp term)
   (pseudo-termp (iff-fix-rec iff negate ctx term)))
  :hints (("Goal" :in-theory (enable syn::funcall)
	   :expand (:free (n x) (syn::nth n x)))))

(verify-guards iff-fix-rec
	       :hints (("Goal" :in-theory (enable syn::funcall)
			:expand (:free (n x) (syn::nth n x)))))


(defmacro iff-fix (iff negate term)
  `(iff-fix-rec ,iff ,negate nil ,term))

(defun iff-fix-list (iff negate list)
  (declare (type (satisfies pseudo-term-listp) list))
  (if (endp list) nil
    (cons (iff-fix iff negate (car list))
	  (iff-fix-list iff negate (cdr list)))))

(defthm pseudo-term-listp-iff-fix-list
  (implies
   (pseudo-term-listp list)
   (pseudo-term-listp (iff-fix-list iff negate list)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((iff-fix-list iff negate list)))))

(defun opt-if (iff test then else)
  (declare (type (satisfies pseudo-termp) test then else))
  (iff-fix iff nil `(if ,test ,then ,else)))

(defthm pseudo-termp-opt-if
  (implies
   (and
    (pseudo-termp test)
    (pseudo-termp then)
    (pseudo-termp else))
   (pseudo-termp (opt-if iff test then else))))

(in-theory (disable opt-if))

(defund top-if (def test then else)
  (declare (type (satisfies pseudo-termp) def test then else))
  (if (equal then def) else
    (if (equal else def) then
      (opt-if nil (defung::true! test) then else))))

(defthm pseudo-termp-top-if
  (implies
   (and
    (pseudo-termp def)
    (pseudo-termp test)
    (pseudo-termp then)
    (pseudo-termp else))
   (pseudo-termp (top-if def test then else)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((top-if def test then else))))
  :hints (("Goal" :in-theory (enable top-if))))

(defthm alistp-implies-true-listp
  (implies
   (alistp x)
   (true-listp x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable (:rewrite alistp-implies-true-listp)))

;; ==================================================================
;;
;; lambda-function-p
;;
;; ==================================================================

(encapsulate

    ()

  (defund weak-lambda-function-p (x)
    (declare (type t x))
    (and (consp x)
	 (consp (cdr x))
	 (consp (cddr x))
	 (null (cdddr x))))

  (local (in-theory (enable weak-lambda-function-p)))

  (defund lambda-function-p (x)
    (declare (type t x))
    (and (true-listp x)
	 (equal (length x) 3)
	 (eq (car x) 'acl2::lambda)
	 (symbol-listp (cadr x))
	 (pseudo-termp (caddr x))))

  (local (in-theory (enable lambda-function-p)))

  (local
   (defthm sum-quoted-constants
     (implies
      (and
       (syntaxp (and (quotep x) (quotep y)))
       (equal q (+ x y)))
      (equal (+ x y z)
	     (+ q z)))))

  (local
   (defthm equal-sum-constant-reduction
     (implies
      (and
       (syntaxp (and (quotep c) (quotep q)))
       (acl2-numberp q)
       (acl2-numberp v)
       (equal z (- q c)))
      (equal (equal (+ c v) q)
	     (equal v z)))))

  (local
   (defthm equal-len-0-reduction
     (equal (equal (len x) 0)
	    (not (consp x)))))

  (defthm lambda-function-p-implies-weak-lambda-function-p
    (implies
     (lambda-function-p x)
     (weak-lambda-function-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm not-consp-not-lambda-function-p
    (implies
     (not (consp x))
     (not (lambda-function-p x))))

  (defthm not-consp-not-weak-lambda-function-p
    (implies
     (not (consp x))
     (not (weak-lambda-function-p x))))

  (defund lambda-function-formals (x)
    (declare (type (satisfies lambda-function-p) x))
    (cadr x))

  (local (in-theory (enable lambda-function-formals)))

  (defthm symbol-listp-lambda-function-formals
    (implies
     (lambda-function-p x)
     (symbol-listp (lambda-function-formals x)))
    :rule-classes (:rewrite
		   (:forward-chaining :trigger-terms ((lambda-function-formals x)))))

  (defund lambda-function-body (x)
    (declare (type (satisfies lambda-function-p) x))
    (caddr x))

  (local (in-theory (enable lambda-function-body)))

  (defthm pseudo-termp-lambda-function-formals
    (implies
     (lambda-function-p x)
     (pseudo-termp (lambda-function-body x)))
    :rule-classes (:rewrite
		   (:forward-chaining :trigger-terms ((lambda-function-body x)))))

  (defthm lambda-function-body-decreases
    (implies
     (weak-lambda-function-p x)
     (< (acl2-count (lambda-function-body x))
	(acl2-count x)))
    :rule-classes (:linear))

  (defthm lambda-function-formals-decreases
    (implies
     (weak-lambda-function-p x)
     (< (acl2-count (lambda-function-formals x))
	(acl2-count x)))
    :rule-classes (:linear))

  (defund lambda-function (formals body)
    (declare (type (satisfies symbol-listp) formals)
	     (type (satisfies pseudo-termp) body))
    `(lambda ,formals ,body))

  (in-theory (disable (:type-prescription lambda-function)))

  (local (in-theory (enable lambda-function)))

  (defthm lambda-function-is-not-quote
    (not (equal (lambda-function formals body) 'quote)))

  (defthm lambda-function-is-not-symbolp
    (not (symbolp (lambda-function formals body))))

  (defthm lambda-function-p-lambda-function
    (implies
     (and
      (symbol-listp formals)
      (pseudo-termp body))
     (lambda-function-p (lambda-function formals body)))
    :rule-classes (:rewrite
		   (:forward-chaining :trigger-terms ((lambda-function formals body)))))

  (defthm lambda-function-accessors
    (and
     (equal (lambda-function-formals (lambda-function formals body))
	    formals)
     (equal (lambda-function-body (lambda-function formals body))
	    body)))

  (defthm open-pseudo-termp
    (and
     (implies
      (not (consp term))
      (equal (pseudo-termp term)
	     (symbolp term)))
     (implies
      (symbolp term)
      (pseudo-termp term))
     (implies
      (consp term)
      (equal (pseudo-termp term)
	     (cond
	      ((equal (car term) 'quote) (and (consp (cdr term)) (null (cddr term))))
	      ((symbolp (car term)) (pseudo-term-listp (cdr term)))
	      (t (and (lambda-function-p (car term))
		      (equal (len (lambda-function-formals (car term)))
			     (len (cdr term)))
		      (pseudo-term-listp (cdr term)))))))))

  )

(local (in-theory (disable pseudo-termp)))

(in-theory (disable open-pseudo-termp))
(local (in-theory (enable open-pseudo-termp)))

(defund lambda-application (formals body args)
  (declare (xargs :guard (equal (len formals) (len args)))
	   (type (satisfies symbol-listp) formals)
	   (type (satisfies pseudo-termp) body))
  (if (quotep body) body
    (cons (lambda-function formals body) args)))

(defthm pseudo-termp-lambda-application
  (implies
   (and
    (symbol-listp formals)
    (pseudo-termp body)
    (pseudo-term-listp args)
    (equal (len formals) (len args)))
   (pseudo-termp (lambda-application formals body args)))
  :hints (("Goal" :in-theory (enable LAMBDA-FUNCTION-FORMALS
				     LENGTH LAMBDA-FUNCTION-P
				     OPEN-PSEUDO-TERMP
				     lambda-function
				     lambda-application))))

(defun not-quote-fn-p (fn)
  (declare (type t fn))
  (or (lambda-function-p fn)
      (not-quote-symbolp fn)))

;; ==================================================================
;;
;; wrap-ifs
;;
;; Wrap the condition of every 'if' with 'defung::true' to prevent ACL2
;; from doing annoying things with, for example, equality that I
;; cannot control.  We do this to the raw translated function so it
;; permanantly changes the function definition.  Such is life in
;; user land.
;;
;; ==================================================================

(mutual-recursion

 (defun wrap-ifs-args (args)
   (if (endp args) nil
     (cons (wrap-ifs (car args))
	   (wrap-ifs-args (cdr args)))))

 (defun wrap-ifs (term)
   (cond
    ((atom term) term)
    ((equal (car term) 'quote) term)
    (t (let ((args (wrap-ifs-args (cdr term))))
	 (cond
	  ((consp (car term))
	   ;;((lambda (x y) body) args)
	   `((lambda ,(cadr (car term)) ,(wrap-ifs (caddr (car term)))) ,@args))
	  ((equal (car term) 'if)
	   `(if ,(defung::true! (car args)) ,@(cdr args)))
	  (t
	   (cons (car term) args)))))))

 )

;; ==================================================================
;;
;; hide-ifs
;;
;; replace 'if' with 'if-macro' if the condition does not impact
;; the recursive nature of the expression.
;;
;;
;; ==================================================================

(defun if-fn (x y z)
  (declare (type t x y z))
  (if x y z))

(defmacro if-macro (x y z)
  `(mbe :logic (if-fn ,x ,y ,z)
	:exec  (if ,x ,y ,z)))

(defmacro hide-ifs-term (fset term)
  `(hide-ifs-key :term ,fset ,term))

(defmacro hide-ifs-args (fset args)
  `(hide-ifs-key :args ,fset ,args))

(defun hide-ifs-key-guard (key fset x)
  (declare (type t key fset x))
  (let ((term x)
	(args x))
    (and (symbol-listp fset)
	 (cond
	  ((equal key :args)
	   (pseudo-term-listp args))
	  (t
	   (pseudo-termp term))))))

(defun hide-ifs-key (key fset term)
  (declare (xargs :guard (hide-ifs-key-guard key fset term)
		  :verify-guards nil))
  (cond
   ((equal key :args)
    (let ((args term))
      (if (not (consp args)) (mv nil nil)
	(met ((ahit nargs) (hide-ifs-args fset (cdr args)))
	  (met ((bhit term) (hide-ifs-term fset (car args)))
	    (mv (or ahit bhit) (cons term nargs)))))))
   ((atom term)
    (mv nil term))
   ((quotep term)
    (mv nil term))
   ((syn::funcall 'if 3 term)
    (met ((testhit test) (hide-ifs-term fset (syn::nth 1 term)))
      (met ((thenhit then) (hide-ifs-term fset (syn::nth 2 term)))
	(met ((elsehit else) (hide-ifs-term fset (syn::nth 3 term)))
	  (if (or thenhit elsehit) (mv t `(if ,test ,then ,else))
	    (mv testhit `(if-macro ,test ,then ,else)))))))
   ((lambda-function-p (car term))
    (let ((args    (cdr term))
	  (body    (lambda-function-body (car term)))
	  (formals (lambda-function-formals (car term))))
      (met ((ahit args) (hide-ifs-args fset args))
	(met ((bhit body) (hide-ifs-term fset body))
	  (mv (or bhit ahit) (lambda-application formals body args))))))
   (t
    (met ((ahit args) (hide-ifs-args fset (cdr term)))
      (let ((fhit (member (car term) fset)))
	(mv (or ahit fhit) `(,(car term) ,@args)))))))

(defun hide-ifs-key-postcondition (key val)
  (declare (type t key val))
  (cond
   ((equal key :args)
    (pseudo-term-listp val))
   (t (pseudo-termp val))))

(encapsulate
 ()

 (local
  (defthm open-hide-ifs-args
    (implies
     (consp term)
     (equal (hide-ifs-key :args fset term)
	    (let ((args term))
	      (if (not (consp args)) (mv nil nil)
		(met ((ahit nargs) (hide-ifs-args fset (cdr args)))
		  (met ((bhit term) (hide-ifs-term fset (car args)))
		    (mv (or ahit bhit) (cons term nargs))))))))))

 (defthm len-hide-ifs-key
   (equal (len (val 1 (hide-ifs-key :args fset args)))
	  (len args))
   :hints (("Goal'" :induct (len args))))

 )

(defthmd hide-ifs-key-postcondition-proof
  (implies
   (hide-ifs-key-guard key fset x)
   (hide-ifs-key-postcondition key (val 1 (hide-ifs-key key fset x))))
  :hints (("Goal" :in-theory (e/d (syn::funcall) nil))))


(defthm pseudo-term-listp-hide-ifs-args
  (implies
   (and
    (symbol-listp fset)
    (pseudo-term-listp args))
   (pseudo-term-listp (val 1 (hide-ifs-args fset args))))
  :hints (("Goal" :use (:instance hide-ifs-key-postcondition-proof
				  (x args)
				  (key :args))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((hide-ifs-term fset term)))))

(defthm pseudo-termp-hide-ifs-term
  (implies
   (and
    (symbol-listp fset)
    (pseudo-termp term))
   (pseudo-termp (val 1 (hide-ifs-term fset term))))
  :hints (("Goal" :use (:instance hide-ifs-key-postcondition-proof
				  (x term)
				  (key :term))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((hide-ifs-term fset term)))))

(defthm pseudo-term-listp-implies-true-listp
  (implies
   (pseudo-term-listp x)
   (true-listp x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable (:rewrite pseudo-term-listp-implies-true-listp)))


(verify-guards hide-ifs-key
	       :hints (("Goal" :in-theory (enable syn::funcall
						  pseudo-term-listp-implies-true-listp
						  alistp-implies-true-listp
						  )
			:expand (:free (n x) (syn::nth n x)))))

(defun hide-ifs (fset term)
  (declare (type (satisfies symbol-listp) fset)
	   (type (satisfies pseudo-termp) term))
  (met ((hit term) (hide-ifs-term fset term))
    (declare (ignore hit))
    term))

;; ==================================================================
;;
;; fset-exists
;;
;; Detect if an expression calls any member of fset
;;
;; ==================================================================

(defmacro fset-exists-term (fset term)
  `(fset-exists-key :term ,fset ,term))

(defmacro fset-exists-args (fset args)
  `(fset-exists-key :args ,fset ,args))

(defun fset-exists-guard (key fset term)
  (declare (type t key term))
  (and (symbol-listp fset)
       (if (equal key :args)
	   (pseudo-term-listp term)
	 (pseudo-termp term))))

(defun fset-exists-key (key fset term)
  (declare (xargs :guard (fset-exists-guard key fset term)))
  (cond
   ((equal key :args)
    (let ((args term))
      (if (not (consp args)) nil
	(or (fset-exists-term fset (car args))
	    (fset-exists-args fset (cdr args))))))
   ((atom term) nil)
   ((quotep term) nil)
   ((lambda-function-p (car term))
    (let ((args    (cdr term))
	  (body    (lambda-function-body (car term))))
      (or (fset-exists-args fset args)
	  (fset-exists-term fset body))))
   (t
    (let ((hit (member (car term) fset)))
      (or hit (fset-exists-args fset (cdr term)))))))

;; ==================================================================
;;
;; normalize-ite
;;
;; remove any if expressions appearing in the test position of an if
;; expression.
;;
;; The primary transformation is:
;;
;; (if (if a b c) d e) ->
;;
;;   (if a (if b d e) (if c d e))
;;
;; ==================================================================

(defun normalized-ite (test)
  (declare (type t test) (xargs :measure (acl2-count test)))
  (cond
   ((syn::funcall 'if 3 test)
    (let ((xtest (syn::nth 1 test))
	  (xthen (syn::nth 2 test))
	  (xelse (syn::nth 3 test)))
      (and (not (syn::funcall 'if 3 xtest))
	   (not (syn::funcall 'not 1 xtest))
	   (normalized-ite xthen)
	   (normalized-ite xelse))))
   ((syn::funcall 'not 1 test)
    (let ((arg (syn::nth 1 test)))
      (and (not (syn::funcall 'if 3 arg))
	   (not (syn::funcall 'not 1 arg)))))
   (t t)))

(defthm normalized-unnot-test
  (implies
   (and
    (normalized-ite test)
    (not (syn::funcall 'if 3 test))
    (normalized-ite then)
    (normalized-ite else))
   (normalized-ite (unnot-test test then else)))
  :hints (("Goal" :in-theory (enable unnot-test))))

(defthmd funcall-not
  (and
   (not (syn::funcall 'if 3 (list 'not test)))
   (syn::funcall 'not 1 (list 'not test))
   (syn::funcall 'if 3 (syn::if x y z))
   (equal (syn::nth 1 (syn::if x y z))
	  x)
   (equal (syn::nth 2 (syn::if x y z))
	  y)
   (equal (syn::nth 3 (syn::if x y z))
	  z)
   (equal (syn::nth 1 (list 'not test))
	  test))
  :hints (("Goal" :in-theory (enable syn::if syn::nth syn::funcall))))

(defthm normalized-ite-iff-fix-rec
  (implies
   (normalized-ite test)
   (normalized-ite (iff-fix-rec iff negate ctx test)))
  :hints (("Goal" :in-theory (enable funcall-not)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((iff-fix-rec iff negate ctx test)))))

(defun normalize-ite (negate test then else)
  (declare (type (satisfies pseudo-termp) test then else)
	   (type (satisfies normalized-ite) then else)
	   (xargs :measure (acl2-count test)
		  :verify-guards nil))
  (cond
   ((syn::funcall 'if 3 test)
    (let ((xtest (syn::nth 1 test))
	  (xthen (syn::nth 2 test))
	  (xelse (syn::nth 3 test)))
      (let ((then (normalize-ite negate xthen then else))
	    (else (normalize-ite negate xelse then else)))
	(normalize-ite negate xtest then else))))
   ((syn::funcall 'not 1 test)
    (let ((arg (syn::nth 1 test)))
      (normalize-ite (not negate) arg then else)))
   (t
    (if negate
	(syn::if test else then)
      (syn::if test then else)))))


(defthm pseudo-termp-normalize-ite
  (implies
   (and
    (pseudo-termp test)
    (pseudo-termp then)
    (pseudo-termp else))
   (pseudo-termp (normalize-ite negate test then else)))
  :hints (("Goal" :in-theory (enable syn::funcall))))

;; Yay!
(defthm normalized-ite-normalize-ite
  (implies
   (and
    (normalized-ite then)
    (normalized-ite else))
   (normalized-ite (normalize-ite negate test then else))))

(verify-guards normalize-ite
	       :hints (("Goal" :in-theory (enable syn::funcall))))

(defthm len-revappend
  (equal (len (revappend x y))
	 (+ (len x) (len y))))

(defthm pseudo-term-listp-revappend
  (implies
   (and
    (pseudo-term-listp x)
    (pseudo-term-listp y))
   (pseudo-term-listp (revappend x y)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((revappend x y)))))

(defun unspecial-function (x)
  (declare (type t x))
  (or (and (symbolp x)
	   (not (equal x 'not))
	   (not (equal x 'quote))
	   (not (equal x 'if)))
      (lambda-function-p x)))

(defun len-fn-args (fn n)
  (declare (type t fn n))
  (if (lambda-function-p fn)
      (equal (len (lambda-function-formals fn)) n)
    t))

;; ==================================================================
;;
;; merge-ite
;;
;; applies a function to a list of arguments, each of which may be a
;; conditional expression.  The result is a single conditional
;; expression whose leaves are function applications to the
;; appropriate arguments from the original argument list.
;;
;; ==================================================================

(defun merge-ite-rec (x args arg fn)
  (declare (xargs :verify-guards nil
		  :guard (len-fn-args fn (+ 1 (len args) (len arg)))
		  :measure (llist (len args) (acl2-count x))
		  :WELL-FOUNDED-RELATION l<)
	   (type (satisfies pseudo-term-listp) args arg)
	   (type (satisfies pseudo-termp) x)
	   (type (satisfies unspecial-function) fn))
  (cond
   ((syn::funcall 'if 3 x)
    (let ((test (syn::nth 1 x))
	  (then (syn::nth 2 x))
	  (else (syn::nth 3 x)))
      (let ((then (merge-ite-rec then args arg fn))
	    (else (merge-ite-rec else args arg fn)))
	(normalize-ite nil test then else))))
   ((consp args)
    (merge-ite-rec (car args) (cdr args) (cons x arg) fn))
   (t (iff-fix nil nil (cons fn (revappend arg (list x)))))))

(defthm pseudo-termp-merge-ite-rec
  (implies
   (and
    (pseudo-term-listp args)
    (pseudo-term-listp arg)
    (unspecial-function fn)
    (len-fn-args fn (+ 1 (len args) (len arg)))
    (pseudo-termp x))
   (pseudo-termp (merge-ite-rec x args arg fn)))
  :hints (("Goal" :induct (merge-ite-rec x args arg fn)
	   :in-theory (enable syn::funcall))))

(defthm normalized-ite-merge-ite-rec
  (implies
   (unspecial-function fn)
   (normalized-ite (merge-ite-rec x args arg fn)))
  :hints (("Goal" :in-theory (enable funcall-not
				     syn::funcall))))

(verify-guards merge-ite-rec
	       :hints (("Goal" :in-theory (enable syn::funcall))))

(defund xmerge-ite (fn args)
  (declare (xargs :guard (len-fn-args fn (len args)))
	   (type (satisfies unspecial-function) fn)
	   (type (satisfies pseudo-term-listp) args))
  (if (consp args)
      (merge-ite-rec (car args) (cdr args) nil fn)
    `(,fn)))

(defthm pseudo-termp-xmerge-ite
  (implies
   (and
    (pseudo-term-listp args)
    (unspecial-function fn)
    (len-fn-args fn (len args)))
   (pseudo-termp (xmerge-ite fn args)))
  :hints (("Goal" :in-theory (enable xmerge-ite))))

(defthm normalized-ite-xmerge-ite
  (implies
   (unspecial-function fn)
   (normalized-ite (xmerge-ite fn args)))
  :hints (("Goal" :in-theory (enable xmerge-ite syn::funcall))))

;; ==================================================================
;;
;; lift-conditions-over-lambda-application
;;
;; ==================================================================

(defun lift-conditions-over-lambda-application (formals body args)
  (declare (type (satisfies pseudo-termp) body)
	   (type (satisfies symbol-listp) formals)
	   (type (satisfies pseudo-term-listp) args)
	   (xargs :guard (equal (len formals) (len args))
		  :verify-guards nil))
  (if (syn::funcall 'if 3 body)
      (let ((test (syn::nth 1 body))
	    (then (syn::nth 2 body))
	    (else (syn::nth 3 body)))
	(let ((test (lift-conditions-over-lambda-application formals test args))
	      (then (lift-conditions-over-lambda-application formals then args))
	      (else (lift-conditions-over-lambda-application formals else args)))
	  ;; I'm not sure I need to do this ..
	  (normalize-ite nil test then else)))
    (xmerge-ite (lambda-function formals body) args)))

(defthm pseudo-termp-lift-conditions-over-lambda-application
  (implies
   (and
    (pseudo-termp body)
    (symbol-listp formals)
    (pseudo-term-listp args)
    (equal (len formals) (len args)))
   (pseudo-termp (lift-conditions-over-lambda-application formals body args)))
  :hints (("Goal" :in-theory (enable syn::funcall))))

(defthm normalized-ite-lift-conditions-over-lambda-application
  (implies
   (and
    (pseudo-termp body)
    (symbol-listp formals))
   (normalized-ite (lift-conditions-over-lambda-application formals body args)))
  :hints (("Goal" :in-theory (enable syn::funcall))))

(verify-guards lift-conditions-over-lambda-application
	       :hints (("Goal" :in-theory (enable syn::funcall))))

;; ==================================================================
;;
;; lift-ifs
;;
;; lift 'if' expressions to the top level while doing "minimal" damage
;; to the term.  The final result is a normalized ite expression whose
;; leaves are unconditional expressions.
;;
;; Note that for our purposes the term fed into this function has
;; had any irrelevant 'if' expressions "hidden" via renaming.
;;
;; ==================================================================

(defmacro lift-ifs-term (term)
  `(lift-ifs-key :term ,term))

(defmacro lift-ifs-args (args)
  `(lift-ifs-key :args ,args))

(defun lift-ifs-key-guard (key x)
  (declare (type t key x))
  (let ((term x)
	(args x))
    (cond
     ((equal key :args)
      (pseudo-term-listp args))
     (t
      (pseudo-termp term)))))

(defun lift-ifs-key (key term)
  (declare (xargs :guard (lift-ifs-key-guard key term)
		  :verify-guards nil))
  (cond
   ((equal key :args)
    (let ((args term))
      (if (not (consp args)) nil
	(cons (lift-ifs-term (car args))
	      (lift-ifs-args (cdr args))))))
   ((atom term) term)
   ((quotep term) term)
   ((equal (car term) 'if)
    (if (syn::funcall 'if 3 term)
	(let ((test (lift-ifs-term (syn::nth 1 term)))
	      (then (lift-ifs-term (syn::nth 2 term)))
	      (else (lift-ifs-term (syn::nth 3 term)))
	      )
	  (normalize-ite nil test then else))
      *nil*))
   ((equal (car term) 'not)
    (if (syn::funcall 'not 1 term)
	(let ((arg (lift-ifs-term (syn::nth 1 term))))
	  (iff-fix t t arg))
      *nil*))
   ((lambda-function-p (car term))
    (let ((args    (cdr term))
	  (body    (lambda-function-body (car term)))
	  (formals (lambda-function-formals (car term))))
      (let ((args (lift-ifs-args args))
	    (body (lift-ifs-term body)))
	(lift-conditions-over-lambda-application formals body args))))
   (t
    (let ((args (lift-ifs-args (cdr term))))
      (xmerge-ite (car term) args)))))

(defun lift-ifs-key-postcondition (key val)
  (declare (type t key val))
  (cond
   ((equal key :args)
    (pseudo-term-listp val))
   (t (pseudo-termp val))))

(encapsulate
 ()

 (local
  (defthm open-lift-ifs-args
    (implies
     (consp term)
     (equal (lift-ifs-key :args term)
	    (let ((args term))
	      (if (not (consp args)) nil
		(cons (lift-ifs-term (car args))
		      (lift-ifs-args (cdr args)))))))))

 (defthm len-lift-ifs-args
   (equal (len (lift-ifs-key :args args))
	  (len args))
   :hints (("Goal'" :induct (len args))))

 )

(defthmd lift-ifs-key-postcondition-proof
  (implies
   (lift-ifs-key-guard key x)
   (lift-ifs-key-postcondition key (lift-ifs-key key x)))
  :hints (("Goal" :in-theory (e/d (syn::funcall) nil))))

(defthm pseudo-term-listp-lift-ifs-args
  (implies
   (pseudo-term-listp args)
   (pseudo-term-listp (lift-ifs-args args)))
  :hints (("Goal" :use (:instance lift-ifs-key-postcondition-proof
				  (x args)
				  (key :args))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((lift-ifs-term  term)))))

(defthm pseudo-termp-lift-ifs-term
  (implies
   (pseudo-termp term)
   (pseudo-termp (lift-ifs-term term)))
  :hints (("Goal" :use (:instance lift-ifs-key-postcondition-proof
				  (x term)
				  (key :term))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((lift-ifs-term term)))))

(defun alt-lift-ifs-key-postcondition (key val)
  (declare (type t key val))
  (cond
   ((equal key :args) t)
   (t (normalized-ite val))))

(defthmd lift-ifs-key-alt-postcondition-proof
  (implies
   (lift-ifs-key-guard key x)
   (alt-lift-ifs-key-postcondition key (lift-ifs-key key x)))
  :hints (("Goal" :in-theory (e/d (syn::funcall) nil))))

(defthm normalized-ite-lift-ifs-term
  (implies
   (pseudo-termp term)
   (normalized-ite (lift-ifs-term term)))
  :hints (("Goal" :use (:instance lift-ifs-key-alt-postcondition-proof
				  (x term)
				  (key :term))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((lift-ifs-term term)))))

(verify-guards lift-ifs-key
	       :hints (("Goal" :in-theory (enable syn::funcall
						  pseudo-term-listp-implies-true-listp
						  alistp-implies-true-listp
						  ))))
(defun lift-ifs (term)
  (declare (type (satisfies pseudo-termp) term))
  (lift-ifs-term term))

;; ==================================================================
;;
;; xtract-base
;;
;; Partitions the function into test/base/rec.
;; We assume that ifs have already been lifted.
;;
;; ==================================================================
;;
;; (if test (if thentest thenbase thenrec) (if elsetest elsebase elserec))
;; (if (or (and test thentest) (and (not test) elsetest)) (if test thenbase elsebase) (if test thenrec elserec))
;;
(defun xtract-base (fset term)
  (declare (type (satisfies symbol-listp) fset)
	   (type (satisfies pseudo-termp) term)
	   (xargs :verify-guards nil))
  (if (syn::funcall 'if 3 term)
      (let ((test (syn::nth 1 term)))
	(if (fset-exists-term fset test) (mv *nil* :default term)
	  (met ((thentest thenbase thenrec) (xtract-base fset (syn::nth 2 term)))
	    (met ((elsetest elsebase elserec) (xtract-base fset (syn::nth 3 term)))
	      ;; thentest = *t*
	      ;; elsetest = *nil*
	      ;; Can we prove that iff-fix preserves normalized-ite
	      ;;
	      (let ((test (iff-fix t nil (normalize-ite nil (normalize-ite nil test thentest *nil*) *t*
							(normalize-ite nil test *nil* elsetest))))
		    (base (top-if :default test thenbase elsebase))
		    (rec  (top-if :default test thenrec elserec)))
		(mv test base rec))))))
    (if (fset-exists-term fset term) (mv *nil* :default term)
      (mv *t* term :default))))

(defthm pseudo-termp-xtract-base
  (implies
   (pseudo-termp term)
   (and (pseudo-termp (val 0 (xtract-base fset term)))
	(pseudo-termp (val 1 (xtract-base fset term)))
	(pseudo-termp (val 2 (xtract-base fset term)))))
  :hints (("Goal" :in-theory (enable syn::funcall)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((xtract-base fset term)))))

(defthm normalized-ite-xtract-base
  (implies
   (and
    (pseudo-termp term)
    (symbol-listp fset))
   (normalized-ite (val 0 (xtract-base fset term))))
  :hints (("Goal" :in-theory (enable syn::funcall)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((xtract-base fset term)))))

(verify-guards xtract-base
	       :hints (("Goal" :in-theory (enable syn::funcall))))

;; ==================================================================
;;
;; split-body
;;
;; This function is used to partition the function body (expressed
;; as a pseudo-termp) into a "done" test, a base case, and a recursive
;; case (as pseudo-termps)
;;
;; ==================================================================

(defund split-term-on-fset (fset term)
  (declare (type (satisfies symbol-listp) fset)
	   (type (satisfies pseudo-termp) term))
  (let ((term (hide-ifs fset term)))
    (let ((term (lift-ifs term)))
      (xtract-base fset term))))

(defthm pseudo-termp-split-term-on-fset
  (implies
   (and
    (symbol-listp fset)
    (pseudo-termp term))
   (and (pseudo-termp (val 0 (split-term-on-fset fset term)))
	(pseudo-termp (val 1 (split-term-on-fset fset term)))
	(pseudo-termp (val 2 (split-term-on-fset fset term)))))
  :hints (("Goal" :in-theory (enable split-term-on-fset)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((split-term-on-fset fset term)))))


;; ==================================================================
;;
;; search-and-replace
;;
;; Transform a function call by replacing the function name and
;; adding some number of arguments.
;;
;; The macros add-depth and rename-fn are based on this function.
;;
;; ==================================================================

(defmacro search-and-replace (fmap term)
  `(search-and-replace-key :term ,fmap ,term))

(defmacro search-and-replace-args (fmap args)
  `(search-and-replace-key :args ,fmap ,args))

(defun search-and-replace-key-guards (key fmap x)
  (declare (type t key x))
  (and (pseudo-fn-map fmap)
       (let ((args x)
	     (term x))
	 (if (equal key :term)
	     (pseudo-termp term)
	   (pseudo-term-listp args)))))

(defthm pseudo-term-listp-append
  (implies
   (pseudo-term-listp x)
   (equal (pseudo-term-listp (append x y))
	  (pseudo-term-listp y))))

(defun search-and-replace-key (key fmap x)
  (declare (xargs :guard (search-and-replace-key-guards key fmap x)
		  :verify-guards nil))
  (let ((args x)
	(term x))
    (if (equal key :term)
	(cond
	 ((atom term) term)
	 ((equal (car term) 'quote) term)
	 ((weak-lambda-function-p (car term))
	  (lambda-application (lambda-function-formals (car term))
			      (search-and-replace fmap (lambda-function-body (car term)))
			      (search-and-replace-args fmap (cdr term))))
	 (t
	  (let ((args (search-and-replace-args fmap (cdr term))))
	    (met ((hit fapp) (remap-fn (car term) args fmap))
	      (declare (ignore hit))
	      fapp))))

      (if (endp args) nil
	(cons (search-and-replace fmap (car args))
	      (search-and-replace-args fmap (cdr args)))))))

(defun search-and-replace-key-postcondition (key val)
  (declare (type t key val))
  (if (equal key :term)
      (pseudo-termp val)
    (pseudo-term-listp val)))

(defthm len-search-and-replace-args
  (equal (len (search-and-replace-args fmap args))
	 (len args))
  :hints (("Goal" :induct (len args))))

(defthmd search-and-replace-key-postcondition-proof
  (implies
   (search-and-replace-key-guards key fmap x)
   (search-and-replace-key-postcondition key (search-and-replace-key key fmap x))))

(defthm pseudo-termp-search-and-replace
  (implies
   (and
    (pseudo-termp term)
    (pseudo-term-listp d)
    (pseudo-fn-map fmap))
   (pseudo-termp (search-and-replace fmap term)))
  :hints (("Goal" :use (:instance search-and-replace-key-postcondition-proof
				  (x term)
				  (key :term))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((search-and-replace-key :term fmap term)))))

(defthm pseudo-termp-listp-search-and-replace-args
  (implies
   (and
    (pseudo-term-listp term)
    (pseudo-term-listp d)
    (pseudo-fn-map fmap))
   (pseudo-term-listp (search-and-replace-key :args fmap term)))
  :hints (("Goal" :use (:instance search-and-replace-key-postcondition-proof
				  (x term)
				  (key :term))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((search-and-replace-key :args fmap term)))))

(defmacro add-depth (fmap term)
  `(search-and-replace ,fmap ,term))

(defmacro rename-fn (fmap term)
  `(search-and-replace ,fmap ,term))

(defmacro rename-fn-args (fmap term)
  `(search-and-replace-args ,fmap ,term))

(verify-guards search-and-replace-key)

;; ==================================================================
;;
;; aggregate
;;
;; Generate functions that aggregate lists of values
;;
;; ==================================================================

(defun remove-default (def list)
  (declare (type (satisfies pseudo-term-listp) list))
  (if (endp list) nil
    (if (equal (car list) def)
	(remove-default def (cdr list))
      (cons (car list) (remove-default def (cdr list))))))

(defthm pseudo-term-listp-remove-default
  (implies
   (pseudo-term-listp list)
   (pseudo-term-listp (remove-default def list)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((remove-default def list)))))

(defthm pseudo-term-listp-remove-duplicates-equal
  (implies
   (pseudo-term-listp list)
   (pseudo-term-listp (remove-duplicates-equal list)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((remove-duplicates-equal list)))))

(defund aggregate (ag def list)
  (declare (type (satisfies not-quote-symbolp) ag)
	   (type (satisfies pseudo-termp) def)
	   (type (satisfies pseudo-term-listp) list))
  (let ((list (remove-default def list)))
    (let ((list (remove-duplicates-equal list)))
      (if (null list) def
	(if (equal (len list) 1) (car list)
	  (cons ag list))))))

(defthm pseudo-termp-aggregate
  (implies
   (and
    (not-quote-symbolp ag)
    (pseudo-termp def)
    (pseudo-term-listp args))
   (pseudo-termp (aggregate ag def args)))
  :hints (("Goal" :in-theory (enable aggregate)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((aggregate ag def args)))))

;; ==================================================================
;;
;; map-lambda-over-list
;;
;; For each member of the list introduce a lambda abstraction and
;; apply it to some number of arguments.
;;
;; ==================================================================

(defun map-lambda-over-list (formals list args)
  (declare (xargs :guard (equal (len formals) (len args)))
	   (type (satisfies symbol-listp) formals)
	   (type (satisfies pseudo-term-listp) list args))
  (if (endp list) nil
    (let ((body (car list)))
      (if (quotep body) (cons body (map-lambda-over-list formals (cdr list) args))
	(cons (lambda-application formals body args)
	      (map-lambda-over-list formals (cdr list) args))))))

(defthm pseudo-term-listp-map-lambda-over-list
  (implies
   (and
    (symbol-listp formals)
    (pseudo-term-listp list)
    (pseudo-term-listp args)
    (equal (len formals) (len args)))
   (pseudo-term-listp (map-lambda-over-list formals list args)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((map-lambda-over-list formals list args)))))

;; ==================================================================
;;
;; aux-functions
;;
;; Useful for generating auxiliary functions such as the measure
;; function and the domain predicate.  The function should really be
;; applied only to the leaves of normal terms (terms w/out if's)
;;
;; ==================================================================

(defmacro aux-function (fmap ag def term)
  `(aux-function-key :term ,fmap ,ag ,def ,term))

(defmacro aux-function-args (fmap ag def args)
  `(aux-function-key :args ,fmap ,ag ,def ,args))

(defun aux-function-key-guard (key fmap ag def x)
  (declare (type t key))
  (let ((args x)
	(term x))
    (and (pseudo-fn-map fmap)
	 (not-quote-symbolp ag)
	 (pseudo-termp def)
	 (if (equal key :term)
	     (pseudo-termp term)
	   (pseudo-term-listp args)))))

(defun aux-function-key (key fmap ag def x)
  (declare (xargs :guard (aux-function-key-guard key fmap ag def x)
		  :verify-guards nil))
  (let ((args x)
	(term x))
    (if (equal key :term)
	(cond
	 ((atom term) nil)
	 ((equal (car term) 'quote) nil)
	 ((weak-lambda-function-p (car term))
	  (append
	   (aux-function-args fmap ag def (cdr term))
	   (map-lambda-over-list (lambda-function-formals (car term))
				 (aux-function fmap ag def (lambda-function-body (car term)))
				 (cdr term))))
	 ((syn::funcall 'if 3 term)
	  (let ((testlist (aux-function fmap ag def (syn::arg 1 term)))
		(thenlist (aux-function fmap ag def (syn::arg 2 term)))
		(elselist (aux-function fmap ag def (syn::arg 3 term))))
	    (append testlist
		    ;;
		    ;; It would be nice to use "top-if" here ..  but
		    ;; we can only do that if we know that we have
		    ;; already covered the base case.
		    ;;
	      (list (top-if nil (syn::arg 1 term)
			    (aggregate ag def thenlist)
			    (aggregate ag def elselist))))))
	 (t
	  (met ((hit aux) (remap-fn (car term) (cdr term) fmap))
	    (if hit
		(append (aux-function-args fmap ag def (cdr term)) (list aux))
	      (aux-function-args fmap ag def (cdr term))))))

      (if (endp args) nil
	(append (aux-function fmap ag def (car args))
		(aux-function-args fmap ag def (cdr args)))))))

(defthmd pseudo-term-listp-aux-function-key
  (implies
   (aux-function-key-guard key fmap ag def x)
   (pseudo-term-listp (aux-function-key key fmap ag def x))))

(defthm pseudo-term-listp-aux-function
  (implies
   (and
    (pseudo-fn-map fmap)
    (not-quote-symbolp ag)
    (pseudo-termp def)
    (pseudo-termp term))
   (pseudo-term-listp (aux-function fmap ag def term)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp-aux-function-key)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((aux-function-key :term fmap ag def term)))))

(verify-guards aux-function-key
 :hints (("Goal" :in-theory (enable syn::funcall
				    pseudo-term-listp-aux-function-key
				    pseudo-term-listp-implies-true-listp
				    )
	  :expand (:free (n x) (syn::nth n x)))))

;; ==================================================================
;;
;; aux-if
;;
;; Useful for generating auxiliary functions such as the measure
;; function and the domain predicate.  This function should be
;; applied only to normalized terms.
;;
;; ==================================================================

(defun aux-if (fmap ag def inc acc term)
  (declare (type (satisfies pseudo-fn-map) fmap)
	   (type (satisfies not-quote-symbolp) ag inc)
	   (type (satisfies pseudo-termp) def)
	   (type (satisfies pseudo-termp) term)
	   (type (satisfies pseudo-term-listp) acc)
	   (xargs :verify-guards nil))
  (if (syn::funcall 'if 3 term)
      (let ((test (syn::arg 1 term))
	    (then (syn::arg 2 term))
	    (else (syn::arg 3 term)))
	(let* ((auxtest (aux-function fmap ag def test))
	       (then    (aux-if fmap ag def inc (append auxtest acc) then))
	       (else    (aux-if fmap ag def inc (append auxtest acc) else)))
	  (syn::if (defung::true! test) then else)))
    (let ((auxterm (aux-function fmap ag def term)))
      (if inc
	  `(,inc ,(aggregate ag def (revappend acc auxterm)))
	(aggregate ag def (revappend acc auxterm))))))

(defthm pseudo-termp-aux-if
  (implies
   (and
    (pseudo-termp def)
    (pseudo-fn-map fmap)
    (not-quote-symbolp ag)
    (not-quote-symbolp inc)
    (pseudo-termp term)
    (pseudo-term-listp acc))
   (pseudo-termp (aux-if fmap ag def inc acc term)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((aux-if fmap ag def inc acc term)))))

(verify-guards
 aux-if
 :hints (("Goal" :in-theory (enable pseudo-term-listp-implies-true-listp))))

;; ==================================================================
;;
;; ==================================================================
