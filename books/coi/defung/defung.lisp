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

(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/gensym/gensym" :dir :system)
(include-book "coi/generalize/generalize" :dir :system)
(INCLUDE-BOOK "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "coi/util/table" :dir :system)
(include-book "map-ec-call")
(include-book "tools/flag" :dir :system)
;;
;; move to util ?
;;

(defthmd natp-fc
  (implies
   (natp x)
   (and (integerp x)
        (<= 0 x)))
  :rule-classes (:forward-chaining))

(defthmd posp-fc
  (implies
   (posp x)
   (and (integerp x)
        (< 0 x)))
  :rule-classes (:forward-chaining))

(DEFTHMd <-+-NEGATIVE-0-1
  (EQUAL (< (+ (- Y) X) 0)
         (< X Y)))

(defund ec-call-omit ()
  (declare (xargs :verify-guards t))
  `(if-macro))

(def::und gensym+ (var avoid)
  (declare (xargs :signature ((t symbol-listp) symbolp symbol-listp)))
  (let ((res (gensym::gensym var avoid)))
    (mv res (cons res avoid))))

(def::signature revappend (symbol-listp symbol-listp)
  symbol-listp
  :hints (("Goal" :in-theory (enable revappend))))

(def::und gensym+sig (var stobj-out res avoid)
  (declare (xargs :signature ((symbolp symbol-listp symbol-listp symbol-listp) 
                              symbol-listp symbol-listp)))
  (if (endp stobj-out) (mv (revappend res nil) avoid)
    (let ((entry (car stobj-out)))
      (if entry (gensym+sig var (cdr stobj-out) (cons entry res) avoid)
        (met ((entry avoid) (gensym+ var avoid))
          (gensym+sig var (cdr stobj-out) (cons entry res) avoid))))))

(defun add-to-implication (xhyps stmt)
  (declare (type (satisfies true-listp) xhyps))
  (if (null xhyps) stmt
    (if (and (consp stmt)
	     (equal (car stmt) 'implies)
	     (consp (cdr stmt))
	     (consp (cddr stmt)))
	(let ((hyps (cadr stmt))
	      (body (caddr stmt)))
	  (if (and (consp hyps)
		   (equal (car hyps) 'and)
		   (true-listp (cdr hyps)))
	      `(implies (and ,@xhyps ,@(cdr hyps)) ,body)
	    `(implies (and ,@xhyps ,hyps) ,body)))
      `(implies (and ,@xhyps) ,stmt))))

(def::un add-to-implication-list (xhyps list)
  (declare (xargs :signature ((true-listp t) true-listp)))
  (if (atom list) nil
    (cons (add-to-implication xhyps (car list))
	  (add-to-implication-list xhyps (cdr list)))))

(defund defun::function-declaration-to-type-thm-hyps (name args hyps decl sig-hints)
  (declare (type symbol name)
	   (type (satisfies defun::function-declaration-p) decl)
	   (type (satisfies true-listp) args hyps))
  (let ((fapp `(,name ,@args)))
    (let ((argsymbol (defun::merge-type-decl-fn-names (defun::function-declaration-args decl))))
      (let ((valsymbol (defun::merge-type-decl-fn-names (defun::function-declaration-vals decl))))
	(let ((thmname (symbol-fns::join-symbols name argsymbol 'implies- valsymbol name)))
	  (let ((type-statement (defun::function-declaration-to-type-statement name args decl)))
	    (and type-statement
		 `((defthm ,thmname
		     ,@(add-to-implication-list hyps type-statement)
		     ,@(and sig-hints `(:hints ,sig-hints))
		     :rule-classes (:rewrite
				    (:forward-chaining
				     :trigger-terms (,fapp))))))))))))

(include-book "split")
(include-book "phony-induction")

(local (in-theory (enable open-pseudo-termp)))
(local (in-theory (disable pseudo-termp)))

(make-event
 `(defmacro big-depth-value ()
    ,(acl2::fixnum-bound)))

(defun big-depth-fn ()
  (declare (xargs :guard t))
  (big-depth-value))

(defmacro big-depth ()
  `(mbe :logic (big-depth-fn)
	:exec  (big-depth-value)))

(defthm unsigned-byte-p-29-big-depth-fn
  (acl2::unsigned-byte-p 29 (big-depth-fn))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((big-depth-fn)))))

(defthm big-depth-fn-is-big-depth-value
  (iff (equal (big-depth-fn) (big-depth-value)) t))

(defun big-depth-generalization ()
  (declare (xargs :guard t))
  (big-depth-fn))

(defthm generalize-big-depth-fn
  (equal (big-depth-fn) (gensym::generalize (big-depth-generalization)))
  :hints (("Goal" :in-theory (enable gensym::generalize))))

(in-theory (disable big-depth-generalization (big-depth-generalization)))

(acl2::add-generalization-pattern (big-depth-generalization))

(in-theory (disable big-depth-fn (big-depth-fn)))

;; It would be nice if this could be made to work somehow
;; with machine dependent fixnums ..

(defmacro 1-<29> (d)
  `(mbe :logic (1- ,d)
	:exec (the (unsigned-byte 29) (- (the (unsigned-byte 29) ,d) (the (unsigned-byte 29) 1)))))

(defmacro zp<29> (n)
  `(mbe :logic (zp ,n)
	:exec  (= ,n 0)))

(local (in-theory (disable zp acl2::zp-open nfix)))

(defun max*-rec (x list)
  (if (consp list)
      `(max ,x ,(max*-rec (car list) (cdr list)))
    x))

(defmacro max* (&rest args)
  (if (consp args)
      (max*-rec (car args) (cdr args))
    0))

(defun equal-fn (x y)
  (equal x y))

(defthm equal-fn-false
  (implies
   (not (equal x y))
   (not (equal-fn x y))))

(defthm equal-fn-true
  (implies
   (equal x y)
   (equal-fn x y)))

(in-theory (disable (:type-prescription equal-fn)))

(defthm combine-and-evaluate-constants
  (implies
   (and
    (syntaxp (and (quotep a) (quotep b)))
    (equal r (+ a b)))
   (equal (+ a (+ b x))
	  (+ r x))))

(defthm boolean-equal-reduction
  (implies
   (booleanp b1)
   (equal (equal b1 b2)
          (and (booleanp b2)
               (implies b1 b2)
               (implies b2 b1)))))

(defthmd natp-equal-reduction
  (implies
   (and
    (natp x)
    (natp y))
   (equal (equal x y)
          (and (not (< x y))
               (not (< y x))))))

(defund nat<=nat-induction (x y)
  (if (zp x) t
    (and (not (zp y))
         (nat<=nat-induction (1- x) (1- y)))))

(defthm natp-max
  (implies
   (and
    (natp x)
    (natp y))
   (natp (max x y)))
  :rule-classes (:type-prescription))

(defthm natp-fix
  (implies
   (natp x)
   (equal (fix x) x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm not-zp-inc
  (implies
   (natp n)
   (not (zp (+ 1 n))))
  :hints (("Goal" :in-theory (enable zp))))

(defthm if-fn-true
  (implies
   test
   (equal (if-fn test then else)
	  then))
  :hints (("Goal" :in-theory (enable if-fn))))

(defthm if-fn-false
  (implies
   (not test)
   (equal (if-fn test then else)
	  else))
  :hints (("Goal" :in-theory (enable if-fn))))

(defthm if-fn-id
  (equal (if-fn test x x) x)
  :hints (("Goal" :in-theory (enable if-fn))))

(defthmd unhide
  (equal (hide x) x)
  :hints (("Goal" :expand (:Free (x) (hide x)))))

;; (defthmd zp-from-not-posp-natp
;;   (implies
;;    (and
;;     (not (posp d))
;;     (natp d))
;;    (zp d))
;;   :rule-classes (:Forward-chaining))

;; (defthmd not-posp-not-zp-lt
;;   (implies
;;    (and
;;     (not (posp d2))
;;     (natp d2)
;;     (not (zp d1)))
;;    (< d2 d1))
;;   :rule-classes ((:Forward-chaining :trigger-terms ((< d2 d1)))))

;; (defthmd zp-not-zp-lt
;;   (implies
;;    (and
;;     (zp d2)
;;     (natp d2)
;;     (not (zp d1)))
;;    (< d2 d1))
;;   :rule-classes ((:Forward-chaining :trigger-terms ((< d2 d1)))))

;; (defthm not-zp-implies-natp-and-below
;;   (implies
;;    (not (zp n))
;;    (and (<= (1- n) n)
;; 	(natp (1- n))
;; 	(natp n)))
;;   :rule-classes ((:Forward-chaining :trigger-terms ((binary-+ -1 n)))))

;; (defthm <-implies-<=-1-
;;   (implies
;;    (and
;;     (< d2 d1)
;;     (natp d2)
;;     (natp d1))
;;    (<= d2 (1- d1)))
;;   :rule-classes (:forward-chaining))

;; (defthm not-natp-implies-zp
;;   (implies
;;    (not (natp x))
;;    (zp x))
;;   :rule-classes (:forward-chaining))

;; (defthm natp-plus
;;   (implies
;;    (and
;;     (natp x)
;;     (natp y))
;;    (natp (+ x y)))
;;   :rule-classes (:type-prescription
;; 		 (:forward-chaining :trigger-terms ((binary-+ x y)))))

;; (defthm natp-implication
;;   (implies
;;    (natp x)
;;    (<= 0 x))
;;   :rule-classes (:forward-chaining))

(defun appears-lt-measure (measure clause)
  (let ((conc (car (last clause))))
    (and (consp conc)
	 (equal (car conc) 'not)
	 (let ((term (nth 1 conc)))
	   (and (equal (nth 0 term) '<)
		(let ((arg1 (nth 1 term)))
		  (and (equal (car arg1) measure)
		       (symbol-listp (cdr arg1))
		       arg1)))))))

(defun appears-measure-lt (measure clause)
  (let ((conc (car (last clause))))
    (and (consp conc)
	 (equal (car conc) 'not)
	 (let ((term (nth 1 conc)))
	   (and (equal (nth 0 term) '<)
		(let ((arg2 (nth 2 term)))
		  (and (equal (nth 0 arg2) measure)
		       (symbol-listp (cdr arg2))
		       arg2)))))))

(defun appears-negated (fn clause)
  (if (endp clause) nil
    (let ((entry (car clause)))
      (if (and (consp entry) (consp (cdr entry)) (equal (car entry) fn) (symbol-listp (cddr entry))) entry
	(appears-negated fn (cdr clause))))))

(defun quadrant (measure domain id clause)
  (let ((id (acl2::string-for-tilde-@-clause-id-phrase id)))
    (let ((negated (appears-negated domain clause))
	  (ltm     (appears-lt-measure measure clause))
	  (mlt     (appears-measure-lt measure clause)))
      (or (and negated (cw "In ~p0 ~p1 appears negated~%" id negated))
	  (and ltm     (cw "In ~p0 appears as (<= x ~p1)~%" id ltm))
	  (and mlt     (cw "In ~p0 appears as (<= ~p1 x)~%"  id mlt))))))

(deftheory defung-theory
  (remove-equal '(:definition mv-nth)
  (append '(;;unhide
            acl2::mv-nth-to-val
            acl2::val-of-cons
	    quoted-true
	    unnest-true
	    normalize-true
	    true-from-x
	    not-true-from-not-x
	    true-id
	    acl2::*meta*-beta-reduce-hide
	    acl2::unhide-hide
	    return-last ; originally must-be-equal
	    the-check ;;the-error
	    if-fn-true
	    if-fn-false
	    if-fn-id
	    equal-fn-false
	    equal-fn-true
	    not-zp-inc
	    natp-fix
	    natp-max
	    len
	    car-cons
	    cdr-cons
	    acl2::d<  ;; ??
	    l<
	    acl2::lexp
	    nfix
	    not
	    fix
	    max
	    synp
	    BOOLEANP-COMPOUND-RECOGNIZER
	    ;; zp-from-not-posp-natp
	    ;; not-posp-not-zp-lt
	    ;; zp-not-zp-lt
	    ;; not-zp-implies-natp-and-below
	    ;; <-implies-<=-1-
	    ;; not-natp-implies-zp
	    ;; (natp) (zp)
	    ;; natp-plus
	    ;; natp-implication
	    acl2::NATP-COMPOUND-RECOGNIZER
	    acl2::POSP-COMPOUND-RECOGNIZER
	    acl2::ZP-COMPOUND-RECOGNIZER
	    acl2::O-FINP-CR
	    acl2-count
	    acl2::UNICITY-OF-0
	    ;;CANCEL_PLUS-LESSP-CORRECT
	    acl2::O-FINP-<
	    acl2::O-P-DEF-O-FINP-1
            ;; we may need a version of these ..
	    ;;acl2::<-+-NEGATIVE-0-1
	    ;;acl2::NATP-FC-1
	    ;;acl2::NATP-FC-2
	    ;;acl2::POSP-FC-1
	    ;;acl2::POSP-FC-2
	    ;;acl2::NATP-POSP--1
            ;; here they are ..
            <-+-NEGATIVE-0-1
            posp-fc
            natp-fc
	    acl2::INTEGER-ABS
	    combine-and-evaluate-constants
	    boolean-equal-reduction)
	  (theory 'minimal-theory))))

;;===========================================================================

(defmacro def::stub (fn args body)
  `(defun ,fn ,args
     (declare (ignore ,@args))
     ,body))

;;(let ((d `(1-<29> ,d)))

(defun nullify-list (list)
  (declare (type t list))
  (if (consp list) (cons nil (nullify-list (cdr list)))
    nil))

(defthm pseudo-term-listp-nullify-list
  (pseudo-term-listp (nullify-list list)))

(defmacro map-fns (f1 f2 args)
  `(map-fn-sig ,f1 ,f2 (nullify-list ,args)))

(defund mk-ibody (fn1 fn2 d args body)
  (declare (type (satisfies not-quote-symbolp) fn1 fn2)
	   (type (satisfies pseudo-termp) d body))
  (add-depth (map-fn-sig fn1 fn2 (cons d (nullify-list args))) body))

(defthm pseudo-termp-mk-ibody
  (implies
   (and
    (not-quote-symbolp fn1)
    (not-quote-symbolp fn2)
    (pseudo-termp d)
    (pseudo-termp body))
   (pseudo-termp (mk-ibody fn1 fn2 d args body)))
  :hints (("Goal" :in-theory (enable mk-ibody))))

(defund mk-idom-body (fn aux args body)
  (declare (type (satisfies not-quote-symbolp) fn aux)
	   (type (satisfies pseudo-termp) body))
  (let ((list (aux-function (map-fns fn aux args) 'and *t* body)))
    (aggregate 'and *t* list)))

(defthm pseudo-termp-mk-idom-body
  (implies
   (and
    (not-quote-symbolp fn)
    (not-quote-symbolp aux)
    (pseudo-termp body))
   (pseudo-termp (mk-idom-body fn aux args body)))
  :hints (("Goal" :in-theory (enable mk-idom-body))))

(defund mk-measure-body (fn aux args body)
  (declare (type (satisfies not-quote-symbolp) fn aux)
	   (type (satisfies pseudo-termp) body))
  (aux-if (map-fns fn aux args) 'max* '(quote 0) '1+ nil body))

(defthm pseudo-termp-mk-measure-body
  (implies
   (and
    (not-quote-symbolp fn)
    (not-quote-symbolp aux)
    (pseudo-termp body))
   (pseudo-termp (mk-measure-body fn aux args body)))
  :hints (("Goal" :in-theory (enable mk-measure-body))))

(defund mk-domain-body (fn aux args body)
  (declare (type (satisfies not-quote-symbolp) fn aux)
	   (type (satisfies pseudo-termp) body))
  (let ((list (aux-function (map-fns fn aux args) 'and *t* body)))
    (aggregate 'and *t* list)))

(defthm pseudo-termp-mk-domain-body
  (implies
   (and
    (not-quote-symbolp fn)
    (not-quote-symbolp aux)
    (pseudo-termp body))
   (pseudo-termp (mk-domain-body fn aux args body)))
  :hints (("Goal" :in-theory (enable mk-domain-body))))

(defund mk-alt-body (fn aux args body)
  (declare (type (satisfies not-quote-symbolp) fn aux)
	   (type (satisfies pseudo-termp) body))
  (aux-if (map-fns fn aux args) 'list *t* 'identity nil body))

(defthm pseudo-termp-mk-alt-body
  (implies
   (and
    (not-quote-symbolp fn)
    (not-quote-symbolp aux)
    (pseudo-termp body))
   (pseudo-termp (mk-alt-body fn aux args body)))
  :hints (("Goal" :in-theory (enable mk-alt-body)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((mk-alt-body fn aux args body)))))

(defun bind-args-self (args)
  (declare (type t args))
  (if (atom args) nil
    (cons (list (car args) (car args))
	  (bind-args-self (cdr args)))))

;;---------------------------------------------------------------------------
;; Define the indexed functions
;;---------------------------------------------------------------------------

(defun indexed-defns (fn ifn idom index ftest fdefault fbase d args arg-type-info test default base body ec-call)
  (declare (type (satisfies not-quote-symbolp) fn ifn idom index ftest fbase)
	   (type symbol d)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies true-listp) arg-type-info)
	   (type (satisfies pseudo-termp) test base body default)
	   (type (satisfies symbol-listp) ec-call)
	   )

  (let* ((default-value  default)
	 (ibody          (mk-ibody fn ifn `(1- ,d) args body))
	 (idom-body      (mk-idom-body ifn idom (cons d args) ibody))
	 ;;(default-call  `(,fdefault ,@args))
	 (fbase-call    `(,fbase ,@args))
	 (test-call `(,ftest ,@args))
	 )
    `(

      (defun-nx ,fbase ,args
	,@arg-type-info
	(declare (ignorable ,@args))
	,base)

      (in-theory (disable (,fbase)))
      (local (in-theory (disable ,fbase)))

      (defun-nx ,fdefault ,args
	,@arg-type-info
	(declare (ignorable ,@args))
	,(if ec-call (map-ec-call-term default-value ec-call) default-value))

      (in-theory (disable (,fdefault)))
      (local (in-theory (disable ,fdefault)))

      (defun-nx ,ftest ,args
	,@arg-type-info
	(declare (xargs :normalize nil))
	(declare (ignorable ,@args))
	,(normalize-ite nil test *t* *nil*))

      (in-theory (disable (,ftest)))
      (local (in-theory (disable ,ftest)))

      (defun-nx ,ifn (,d ,@args)
	(if (or (zp ,d) ,test-call)
	    (if ,test-call ,fbase-call nil) ;; ,default-call)
	  ,ibody))

      (in-theory (disable ,ifn (:type-prescription ,ifn)))

      (defun-nx ,idom (,d ,@args)
	(if (zp ,d) ,test-call
	  (if ,test-call t
	    ,idom-body)))

      (in-theory (disable ,idom))

      ;; There are some nice things that we know about the base
      ;; functions which might make some of these proofs more robust
      ;; (?)

      (defchoose ,index (,d) ,args (,idom ,d ,@args))

     )
    )
  )

;;---------------------------------------------------------------------------
;; Prove the indexed domain properties
;;---------------------------------------------------------------------------

(defun indexed-domain-lemmas (ifn idom index d d1 d2 args
                              ftest index-thm mono-determ mono mono-contra idom-lower-bound)
  (declare (type (satisfies symbol-listp) args)
	   (ignorable ftest))
 `(

   (defthmd ,index-thm
     (implies
      (,idom ,d ,@args)
      (,idom (,index ,@args) ,@args))
     :rule-classes (:forward-chaining)
     :hints (("Goal" :use ,index)))

   (defthmd ,mono-determ
     (implies
      (and
       (natp ,d1)
       (natp ,d2)
       (<= ,d1 ,d2)
       (,idom ,d1 ,@args))
      (and (,idom ,d2 ,@args)
           (equal (,ifn ,d1 ,@args)
                  (,ifn ,d2 ,@args))))
     :hints (("Goal" :in-theory (enable ,idom ,ifn nat<=nat-induction)
	      :restrict ((,idom ,(bind-args-self args))
			 (,ifn  ,(bind-args-self args)))
	      ;; :expand ((,idom ,d1 ,@args)
	      ;; 	       (,idom ,d2 ,@args)
	      ;; 	       (,ifn  ,d1 ,@args)
	      ;; 	       (,ifn  ,d2 ,@args))
	      :induct (list (nat<=nat-induction ,d1 ,d2)
			    (,idom ,d1 ,@args)))
	     (and stable-under-simplificationp
		  '(:expand ((,idom ,d1 ,@args)
			     (,idom ,d2 ,@args))))
	     (and stable-under-simplificationp
		  '(:in-theory (enable open-true)
		    :expand ((,ifn  ,d1 ,@args)
			     (,ifn  ,d2 ,@args)
			     (,idom ,d1 ,@args)
			     (,idom ,d2 ,@args))))))

   (defthmd ,mono
     (implies
      (and
       (,idom ,d1 ,@args)
       (<= ,d1 ,d2)
       (natp ,d1)
       (natp ,d2))
      (,idom ,d2 ,@args))
     :rule-classes (:rewrite :forward-chaining)
     :hints (("Goal" :in-theory (enable ,mono-determ))))

   (defthmd ,mono-contra
     (implies
      (and
       (,idom ,d1 ,@args)
       (not (,idom ,d2 ,@args))
       (natp ,d1)
       (natp ,d2))
      (< ,d2 ,d1))
     :rule-classes (:forward-chaining)
     :hints (("Goal" :use ,mono)))

   (defthmd ,idom-lower-bound
     (implies
      (and
       (,idom ,d1 ,@args)
       (,idom ,d2 ,@args)
       (not (,idom (1- ,d1) ,@args))
       (not (zp ,d1))
       (natp ,d2))
      (<= ,d1 ,d2))
     :hints (("Goal" :in-theory (enable ,mono ,mono-contra)))
     :rule-classes (:forward-chaining))

   ))

;;---------------------------------------------------------------------------
;; Define and characterize the min-index
;;---------------------------------------------------------------------------

(defun min-index (idom d d1 d2 args idom-lower-bound mono mono-contra
                  ifn-min-index natp-min-index idom-min-index
                  min-index-bound min-index-smallest)
  `(

    (defun-nx ,ifn-min-index (,d ,@args)
      (if (zp ,d) 0
       (if (not (,idom ,d ,@args)) 0
         (if (not (,idom (1- ,d) ,@args)) ,d
	   (,ifn-min-index (1- ,d) ,@args)))))

    (in-theory (disable ,ifn-min-index))

    (defthm ,natp-min-index
      (natp (,ifn-min-index ,d ,@args))
      :hints (("Goal" :in-theory (enable ,ifn-min-index)))
      :rule-classes (:type-prescription))

    (defthmd ,idom-min-index
      (implies
       (,idom ,d ,@args)
       (,idom (,ifn-min-index ,d ,@args) ,@args))
      :hints (("Goal" :in-theory (enable ,ifn-min-index
					 ,mono ,mono-contra
					 )
	       :induct (,ifn-min-index ,d ,@args))
	      (and stable-under-simplificationp
		   '(:expand (:Free (,d) (,idom ,d ,@args)))))
      :rule-classes (:rewrite :forward-chaining))

    (defthmd ,min-index-bound
      (implies
       (natp ,d)
       (<= (,ifn-min-index ,d ,@args) ,d))
      :hints (("Goal" :induct (,ifn-min-index ,d ,@args)
	       :in-theory (enable ,ifn-min-index
				  ,idom-min-index
				  ,mono
				  ,mono-contra
				  )))
      :rule-classes (:linear
		     (:forward-chaining
		      :trigger-terms ((,ifn-min-index ,d ,@args)))))

    (defthmd ,min-index-smallest
      (implies
       (and
	(,idom ,d1 ,@args)
	(,idom ,d2 ,@args)
	(natp ,d1)
	(natp ,d2))
       (<= (,ifn-min-index ,d1 ,@args) ,d2))
      :rule-classes (:rewrite :linear :forward-chaining)
      :hints (("Goal" :in-theory (enable ,idom-lower-bound
					 ,ifn-min-index
					 ,min-index-bound
					 ,mono
					 ,mono-contra)
	       :induct (,ifn-min-index ,d1 ,@args))))
    )
  )

;;---------------------------------------------------------------------------
;; Introduce the measure function
;;---------------------------------------------------------------------------

;; We cannot use the variable "state" in certain places ..
;; in particular, we cannot use it in a (syntaxp ..) context.
(defun rename-state-args (args)
  (declare (type t args))
  (if (not (consp args)) args
    (let ((entry (car args)))
      (if (consp entry)
          (let ((fn (car entry)))
            (if (consp fn)
                (if (and (equal (car fn) 'acl2::lambda)
                         (consp (cdr fn)))
                    (cons (cons (cons (car fn) (cons (rename-state-args (cadr fn))
                                                     (rename-state-args (cddr fn))))
                                (rename-state-args (cdr entry)))
                          (rename-state-args (cdr args)))
                  (cons (cons (rename-state-args fn) (rename-state-args (cdr entry)))
                        (rename-state-args (cdr args))))
              (cons (cons fn (rename-state-args (cdr entry)))
                    (rename-state-args (cdr args)))))
        (if (equal entry 'acl2::state)
            (cons (symbol-fns::suffix entry '-var)
                  (rename-state-args (cdr args)))
          (cons entry (rename-state-args (cdr args))))))))

(defun rename-state (term)
  (declare (type t term))
  (if (consp term)
      (cons (car term) (rename-state-args (cdr term)))
    term))

(defun mk-measure (measure measure-type test ifn-min-index index ifn idom args d d1 d2
		   idom-min-index min-index-bound min-index-smallest mono mono-contra
                   index-thm measure-property measure-smallest
                   replace-index-by-measure replace-index-by-measure-2
		   replace-domain-index-by-measure
		   mono-determ)
  (declare (ignorable test min-index-bound))
  `(

    (defun-nx ,measure ,args 
      (,ifn-min-index (,index ,@args) ,@args))

    (in-theory (disable ,measure (,measure)))

    (defthm ,measure-type
      (natp (,measure ,@args))
      :hints (("Goal" :in-theory (enable ,measure)))
      :rule-classes (:type-prescription :rewrite (:forward-chaining :trigger-terms ((,measure ,@args)))))

    (defthmd ,measure-property
      (implies
       (,idom ,d ,@args)
       (,idom (,measure ,@args) ,@args))
      :hints (("Goal" :in-theory (enable ,measure
					 ,idom-min-index
					 ,index-thm
					 )))
      :rule-classes (:forward-chaining))

    (defthmd ,measure-smallest
      (implies
       (and
	(,idom ,d ,@args)
	(natp ,d))
       (<= (,measure ,@args) ,d))
      :rule-classes (:rewrite :linear :forward-chaining)
      :hints (("Goal" :do-not-induct t
	       :cases ((natp (,index ,@args)))
	       :in-theory (enable ,measure
				  ,index-thm
				  ,min-index-smallest
				  ;;,idom-min-index
				  ,ifn-min-index
				  ;;,min-index-bound
				  ;;,mono
				  ))))

    (in-theory (disable ,measure))

    ,(rename-state 
      `(defthmd ,replace-index-by-measure
         (implies
          (and
           (syntaxp (not (or (equal ,d '(quote 0))
                             (and (eq (car ,d) ',measure)
                                  (equal (cdr ,d) (list ,@args))))))
           (,idom ,d ,@args)
           (equal ,d1 (,measure ,@args))
           (syntaxp (equal ,d1 (cons ',measure (list ,@args)))))
          (equal (,ifn ,d ,@args)
                 (,ifn (,measure ,@args) ,@args)))
         :hints (("Goal" :do-not-induct t
                  :in-theory (enable ,idom ,ifn
                                     ,measure-property ,measure-smallest)
                  :restrict ((,idom ,(bind-args-self args))
                             (,ifn  ,(bind-args-self args)))
                  :use (:instance ,mono-determ
                                  ,@(bind-args-self args)
                                  (,d1 (,measure ,@args))
                                  (,d2 ,d))))))
    
    ,(rename-state 
      `(defthmd ,replace-index-by-measure-2
         (implies
          (and
           (syntaxp (not (or (equal ,d '(quote 0))
                             (and (eq (car ,d) ',measure)
                                  (equal (cdr ,d) (list ,@args))))))
           (equal ,d1 (,measure ,@args))
           (syntaxp (equal ,d1 (cons ',measure (list ,@args))))
           (,idom (,measure ,@args) ,@args)
           (natp ,d)
           (<= (,measure ,@args) ,d))
          (equal (,ifn ,d ,@args)
                 (,ifn (,measure ,@args) ,@args)))
         :hints (("Goal" :do-not-induct t
                  :use (:instance ,mono-determ
                                  ,@(bind-args-self args)
                                  (,d1 (,measure ,@args))
                                  (,d2 ,d))))))

    ,(rename-state 
      `(defthmd ,replace-domain-index-by-measure
         (implies
          (and
           (<= (,measure ,@args) ,d)
           (natp ,d)
           (syntaxp (not (or (equal ,d '(quote 0))
                             (and (eq (car ,d) ',measure)
                                  (equal (cdr ,d) (list ,@args)))))))
          (equal (,idom ,d ,@args)
                 (,idom (,measure ,@args) ,@args)))
         :hints (("Goal" :in-theory (enable ,mono ,mono-contra ,measure-property)))))

    )
  )

;;---------------------------------------------------------------------------
;; Introduce the "real" definition
;;---------------------------------------------------------------------------

;; By default, use the variables that are part of the test for the
;; base condition.

(defun replace-each (args v)
  (declare (type t args))
  (if (atom args) nil
    (cons v (replace-each (cdr args) v))))

(defthm pseudo-term-listp-replace-each
  (implies
   (pseudo-termp v)
   (pseudo-term-listp (replace-each args v))))

(defund default-calist (fn args)
  (declare (type (satisfies not-quote-symbolp) fn))
  (list (cons fn (replace-each args t))))

(defthm pseudo-term-listp-default-calist
  (implies
   (not-quote-symbolp fn)
   (pseudo-term-listp (default-calist fn args)))
  :hints (("Goal" :in-theory (enable default-calist))))

(defun fn-openers (fn fn-definition fn-domain xargs args ftest base xbody)
  (declare (type (satisfies true-listp) xargs args)
	   (type symbol fn))
  (let* ((open-fn (symbol-fns::prefix 'open- fn))
	 (open-fn-base      (symbol-fns::suffix open-fn '-base))
	 (open-fn-induction (symbol-fns::suffix open-fn '-induction)))

    `(

      (defthm ,open-fn-base
	(implies
	 (and
	  (,ftest ,@args)
	  (,fn-domain ,@args))
	 (equal (,fn ,@xargs) ,base))
	:hints (("Goal" :expand (:with ,fn-definition (,fn ,@xargs)))))

      (local (in-theory (disable ,open-fn-base)))

      ,(rename-state 
        `(defthm ,open-fn-induction
           (implies
            (and
             (syntaxp (symbol-listp (list ,@xargs)))
             (,fn-domain ,@args)
             (not (,ftest ,@args)))
            (equal (,fn ,@xargs) ,xbody))
           :hints (("Goal" :expand (:with ,fn-definition (,fn ,@xargs))))))

      (local (in-theory (disable ,open-fn-induction)))

    )))

(defun real-defs (ifn fn fn0 fn0-domain depth args ftest fdefault fbase body
                  idom measure index d mono mono-contra
                  ifn-min-index idom-min-index
                  min-index-bound min-index-smallest
                  base-implies-zero-measure fn0-measure-definition
                  fn0-domain-definition open-fn0-domain fn0-definition induction-fn0
		  fn0-induction-rule fn0-domain-true
                  induction-is-domain measure-property measure-smallest
                  replace-index-by-measure replace-index-by-measure-2
		  replace-domain-index-by-measure)

  (declare (type (satisfies not-quote-symbolp) ifn fn fn0 measure fn0-domain induction-fn0)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies pseudo-termp) body)
	   (ignore fdefault replace-domain-index-by-measure))

  (let* ((fn0-body        (rename-fn (map-fns fn fn0 args) body))
	 (measure-xbody   (mk-measure-body fn0 measure args fn0-body))
	 (measure-body   `(if (,ftest ,@args) 0 ,measure-xbody))
	 (measure-body-fn (symbol-fns::suffix measure '-body))
	 (domain-xbody    (mk-domain-body  fn0 fn0-domain  args fn0-body))
	 (domain-body    `(if (,ftest ,@args) t ,domain-xbody))
	 (ind-body        (mk-domain-body  fn0 induction-fn0 args fn0-body))
	 (ind-body       `(if (,ftest ,@args) t ,ind-body))
	 (fn0-body      `(if (,ftest ,@args) (,fbase ,@args) ,fn0-body))
	 (calist          (default-calist fn args)))

    `(

      ;; ==================================================================
      ;; Define the function and domain.
      ;; ==================================================================

      (defun-nx ,fn0 ,args (,ifn (,measure ,@args) ,@args))
      (defun-nx ,fn0-domain ,args (,idom (,measure ,@args) ,@args))

      (in-theory (disable ,fn0 (,fn0) ,fn0-domain (,fn0-domain)))

      (defthmd ,base-implies-zero-measure
	(implies
	 (not (,fn0-domain ,@args))
	 (equal (,measure ,@args) 0))
	:hints (("Goal" :in-theory (enable
				    ,fn0-domain
				    ;;,fdom
				    ,measure
				    ,idom-min-index
				    ,mono
				    ,mono-contra
				    )
		 :expand (,ifn-min-index (,index ,@args) ,@args))))

      (in-theory (disable ,idom-min-index ,min-index-bound ,min-index-smallest))

      ;; ==================================================================
      ;; The important theorems about the "top level" functions.
      ;; ==================================================================

      (defun-nx ,measure-body-fn (,@args)
	,measure-body)

      (in-theory (disable (,measure-body-fn)))

      (defthmd ,fn0-measure-definition
	(equal (,measure ,@args)
	       (if (not (,fn0-domain ,@args)) 0 ,measure-body))
	:rule-classes ((:definition
			:install-body t
			:controller-alist ,(rename-fn-args (map-fns fn measure args) calist)))
	:hints (("Goal" :cases ((,fn0-domain ,@args)))
		("Subgoal 2" :in-theory (enable ,base-implies-zero-measure))
		("Subgoal 1" :cases ((,idom (,measure-body-fn ,@args) ,@args))
		 :in-theory (enable natp-equal-reduction
				    ,fn0-domain
				    ,mono
				    ,mono-contra
				    ,fn0
				    ,measure-smallest
				    ,replace-index-by-measure
				    ,replace-index-by-measure-2
				    ,measure-property))
		(and stable-under-simplificationp
		     '(:expand (,idom (,measure ,@args) ,@args)
			       :in-theory (enable ,idom
						  ,mono
						  ,mono-contra
						  ,fn0
						  ,measure-smallest
						  ,replace-index-by-measure
						  ,replace-index-by-measure-2
						  ,measure-property)))
		))

      (in-theory (disable (:definition ,measure)))

      ;; Is there an analogous rule to replace-index-by-measure for domains?

      (defthmd ,fn0-domain-definition
	(equal (,fn0-domain ,@args) ,domain-body)
	:rule-classes ((:definition
			:install-body t
			:controller-alist ,(rename-fn-args (map-fns fn fn0-domain args) calist)))
	:hints ((and stable-under-simplificationp
		     '(:restrict ((,ifn  ,(bind-args-self args))
				  (,idom ,(bind-args-self args)))
		       :in-theory (enable ,fn0
					  ,idom
					  ;;,fdom
					  ,fn0-domain
					  ,base-implies-zero-measure
					  ,replace-index-by-measure
					  ,replace-index-by-measure-2
					  ,measure-property
					  ,measure-smallest
					  ,mono
					  ,mono-contra
					  )))
		(and stable-under-simplificationp
		     '(:expand (,idom (,measure ,@args) ,@args)
			       :use ((:instance ,measure-property
						(,d (,measure-body-fn ,@args))))))))

      ;;(in-theory (disable (:definition ,fdom)))
      (in-theory (disable (:definition ,fn0-domain)))

      (defthm ,fn0-definition
	(equal (,fn0 ,@args)
	       (if (not (,fn0-domain ,@args)) nil ;; (,fdefault ,@args) 
                 ,fn0-body))
	:rule-classes ((:definition
			:install-body t
			:controller-alist ,(rename-fn-args (map-fns fn fn0 args) calist)))
	:hints ((and stable-under-simplificationp
		     '(:do-not '(preprocess)
		       :expand ((:free (,depth) (,ifn ,depth ,@args)))
		       :in-theory (e/d (,ifn
					,fn0
					,fn0-domain-definition
					,fn0-measure-definition) (max))
		       :restrict ((,ifn ,(bind-args-self args))
				  (,fn0-domain-definition  ,(bind-args-self args))
				  (,fn0-measure-definition ,(bind-args-self args)))))
		(and stable-under-simplificationp
		     '(:expand ((:free ,args (,ifn 0 ,@args))
				(:free (,depth) (,idom ,depth ,@args)))
		       :in-theory (enable ,ifn
					  ,replace-index-by-measure
					  ,replace-index-by-measure-2
					  ,mono ,mono-contra
					  ,fn0-domain)))
		(and stable-under-simplificationp
		     '(:in-theory (enable open-true
					  ,ifn
					  ,replace-index-by-measure
					  ,replace-index-by-measure-2
					  ,mono ,mono-contra
					  ,fn0-domain)))))

      (in-theory (disable (:definition ,fn0)))

      (defun-nx ,induction-fn0 ,args
	(declare (xargs :measure (,measure ,@args)
			;;
			;; I would think that I would not need this?
			;; The fact that I need this, along with the
			;; fact that the "alt" proof is failing, may
			;; suggest that perhaps there is a mistake in
			;; one or more of my analysis procedures.
			;;
			:ruler-extenders :all
			;;
			:hints (("Goal" :in-theory (enable ,ftest)
				 :do-not '(preprocess))
				(and stable-under-simplificationp
				     '(:in-theory (e/d (,ftest) (max))
				       :expand (:with ,fn0-measure-definition (,measure ,@args))))
				(and stable-under-simplificationp
				     '(:in-theory (enable ,ftest))))))
	(if (not (,fn0-domain ,@args)) nil ,ind-body))

      (defthm ,induction-is-domain
	(equal (,induction-fn0 ,@args) (,fn0-domain ,@args))
	:hints (("Goal" :do-not '(preprocess)
		 :induct (,induction-fn0 ,@args))
		(and stable-under-simplificationp
		     '(:expand (:with ,fn0-domain-definition (,fn0-domain ,@args))))))

      (in-theory (disable (:definition ,induction-fn0) (,induction-fn0)))

      (defthm ,fn0-induction-rule t
	:rule-classes ((:induction :corollary t
				   :pattern (,fn0 ,@args)
				   :scheme (,induction-fn0 ,@args))))


      ,(rename-state 
        `(defthm ,open-fn0-domain
           (implies
            (and
             (syntaxp (symbol-listp (list ,@args)))
             (not (,ftest ,@args)))
            (equal (,fn0-domain ,@args) ,domain-xbody))
           :hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args))))))

      (defthm ,fn0-domain-true
	(implies
	 (,ftest ,@args)
	 (,fn0-domain ,@args))
	:hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args)))))

      (local (in-theory (disable ,open-fn0-domain)))

      ,@(fn-openers fn0 fn0-definition fn0-domain args args ftest `(,fbase ,@args) fn0-body)

      ,@(fn-openers measure fn0-measure-definition fn0-domain args args ftest '0 measure-xbody)

      )))

;;---------------------------------------------------------------------------
;; Introduce the executable definition
;;---------------------------------------------------------------------------

(defun id-fn ()
  `(lambda (x) x))

(defun if-to-opener (base n fn args defn acc term)
  (if (syn::funcall 'if 3 term)
      (let ((test (syn::arg 1 term))
	    (then (syn::arg 2 term))
	    (else (syn::arg 3 term)))
	(append (if-to-opener base     (* 2 n)  fn args defn (cons        test  acc) then)
		(if-to-opener base (1+ (* 2 n)) fn args defn (cons `(not ,test) acc) else)))
    (let ((branch `(defthm ,(symbol-fns::suffix base '- n)
		     (implies (and ,@(revappend acc nil)) (equal (,fn ,@args) ,term))
		     :hints (("Goal" :expand (:with ,defn (,fn ,@args)))))))
      (let ((disable `(local (in-theory (disable ,(symbol-fns::suffix base '- n))))))
	(list branch disable)))))

;; (defun fn-mbe (fn
;; 	       fn-mbe fn-mbe-definition fn0 fn0-definition
;; 	       fn-mbe-domain fn-mbe-domain-definition fn0-domain fn0-domain-definition
;; 	       fn-mbe-measure fn-mbe-measure-definition fn0-measure fn0-measure-definition
;; 	       fn-mbe-induction fn-mbe-induction-rule fn-mbe-induction-is-fn-mbe-domain
;; 	       fn0-to-fn-mbe open-fn-mbe-domain
;; 	       args arg-type-info ftest fbase fdefault tbody xbody ec-call
;; 	       )
;;   (let* ((omit                    `(,fn-mbe ,fn-mbe-domain ,@ec-call ,@(ec-call-omit)))
;; 	 (fn-mbe-exec-body        (rename-fn (map-fns fn fn-mbe args) tbody))
;; 	 (fn-mbe-exec-body-ec     (if ec-call (map-ec-call-term fn-mbe-exec-body omit)
;; 				    fn-mbe-exec-body))
;; 	 (fn-mbe-xbody            (rename-fn (map-fns fn fn-mbe args) xbody))
;; 	 (fn-mbe-tbody            `(if (,ftest ,@args) (,fbase ,@args) ,fn-mbe-xbody))
;; 	 (fn-mbe-domain-exec-body (mk-domain-body fn-mbe fn-mbe-domain args fn-mbe-exec-body))
;; 	 (fn-mbe-domain-exec-body-ec (if ec-call (map-ec-call-term fn-mbe-domain-exec-body omit)
;; 				       fn-mbe-domain-exec-body))
;; 	 (fn-mbe-domain-xbody     (mk-domain-body fn-mbe fn-mbe-domain args fn-mbe-xbody))
;; 	 (fn-mbe-domain-tbody     `(if (,ftest ,@args) t ,fn-mbe-domain-xbody))
;; 	 (fn-mbe-induction-xbody  (mk-domain-body fn-mbe fn-mbe-induction args fn-mbe-xbody))
;; 	 (fn-mbe-induction-tbody  `(if (,ftest ,@args) t ,fn-mbe-induction-xbody))
;; 	 (fn-mbe-measure-xbody    (mk-measure-body fn-mbe fn-mbe-measure args fn-mbe-xbody))
;; 	 (fn-mbe-measure-tbody    `(if (,ftest ,@args) 0 ,fn-mbe-measure-xbody))
;; 	 )

;;     `(
;;       (set-bogus-mutual-recursion-ok t)

;;       (mutual-recursion

;;        (defun ,fn-mbe ,args
;; 	 ,@arg-type-info
;; 	 (declare (xargs ;;:hints (("Goal" :expand (:with ,fn0-measure-definition (,fn0-measure ,@args))))
;; 			 :guard (,fn-mbe-domain ,@args)
;; 			 ;;:measure (,fn-measure ,@args)
;; 			 ))
;; 	 (mbe :logic (,fn0 ,@args)  :exec ,fn-mbe-exec-body-ec))

;;        (defun ,fn-mbe-domain ,args
;; 	 ,@arg-type-info
;; 	 (declare (xargs ;;:measure (,fn-measure ,@args)))
;; 		   ))
;; 	 (mbe :logic (,fn0-domain ,@args) :exec ,fn-mbe-domain-exec-body-ec))

;;        )

;;       (in-theory (disable (,fn-mbe) (,fn-mbe-domain)))

;;       (defthm ,fn0-to-fn-mbe
;; 	(and (equal (,fn0 ,@args) (,fn-mbe ,@args))
;; 	     (equal (,fn0-domain ,@args) (,fn-mbe-domain ,@args))))

;;       (local (in-theory (disable ,fn0-to-fn-mbe)))

;;       (defun ,fn-mbe-measure ,args
;; 	(,fn0-measure ,@args))

;;       (in-theory (disable (,fn-mbe-measure)))

;;       (defthm ,fn-mbe-definition
;; 	(equal (,fn-mbe ,@args)
;; 	       (if (,fn-mbe-domain ,@args)
;; 		   ,fn-mbe-tbody
;; 		 (,fdefault ,@args)))
;; 	:hints (("Goal" :expand (:with ,fn0-definition (,fn0 ,@args))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-mbe args))))

;;       (local (in-theory (disable ,fn-mbe-definition)))

;;       (defthm ,fn-mbe-domain-definition
;; 	(equal (,fn-mbe-domain ,@args)
;; 	       ,fn-mbe-domain-tbody)
;; 	:hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-mbe-domain args))))

;;       (local (in-theory (disable ,fn-mbe-domain-definition)))

;;       (defthm ,fn-mbe-measure-definition
;; 	(equal (,fn-mbe-measure ,@args)
;; 	       (if (,fn-mbe-domain ,@args)
;; 		   ,fn-mbe-measure-tbody
;; 		 0))
;; 	:hints (("Goal" :expand (:with ,fn0-measure-definition (,fn0-measure ,@args))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-mbe-measure args))))

;;       (local (in-theory (disable ,fn-mbe-measure-definition)))

;;       (in-theory (disable ,fn-mbe ,fn-mbe-domain ,fn-mbe-measure))

;;       (theory-invariant (incompatible (:definition ,fn-mbe)        (:rewrite ,fn0-to-fn-mbe)))
;;       (theory-invariant (incompatible (:definition ,fn-mbe-domain) (:rewrite ,fn0-to-fn-mbe)))

;;       (defun ,fn-mbe-induction ,args
;; 	(declare (xargs :measure (,fn-mbe-measure ,@args)
;; 			:hints (("Goal" :expand (:with ,fn-mbe-measure-definition
;; 						       (,fn-mbe-measure ,@args))))))
;; 	(if (,fn-mbe-domain ,@args)
;; 	    ,fn-mbe-induction-tbody
;; 	  nil))

;;      (defthm ,fn-mbe-induction-rule t
;;        :rule-classes ((:induction :corollary t
;; 				  :pattern (,fn-mbe ,@args)
;; 				  :scheme (,fn-mbe-induction ,@args))))

;;      (in-theory (disable (:definition ,fn-mbe-induction) (,fn-mbe-induction)))

;;      (defthm ,fn-mbe-induction-is-fn-mbe-domain
;;        (equal (,fn-mbe-induction ,@args) (,fn-mbe-domain ,@args))
;;        :hints (("goal" :induct (,fn-mbe-induction ,@args)
;; 		:expand ((:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))
;; 			 (,fn-mbe-induction ,@args)))))

;;      ,(rename-state 
;;        `(defthm ,open-fn-mbe-domain
;;           (implies
;;            (and
;;             (syntaxp (symbol-listp (list ,@args)))
;;             (not (,ftest ,@args)))
;;            (equal (,fn-mbe-domain ,@args)
;;                   ,fn-mbe-domain-xbody))
;;           :hints (("Goal" :expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))))))

;;      (local (in-theory (disable ,open-fn-mbe-domain)))

;;      ,@(fn-openers fn-mbe fn-mbe-definition fn-mbe-domain args args ftest `(,fbase ,@args) fn-mbe-xbody)

;;      ,@(fn-openers fn-mbe-measure fn-mbe-measure-definition fn-mbe-domain args args ftest '0 fn-mbe-measure-xbody)

;;      )))

;; (defun fn-comp (fn
;; 	       fn-comp fn-mbe-domain fn-mbe fn-measure fn-mbe-definition  fn-mbe-measure-definition fn-mbe-domain-definition
;; 	       fn-comp-induction fn-comp-induction-rule
;; 	       fn-comp-to-fn-mbe fn-comp-definition
;; 	       args depth arg-type-info ftest fbase fdefault default-expr tbody xbody
;; 	       )
;;   (declare (ignorable fdefault))
;;   (let* ((fn-comp-xbody          (mk-ibody fn fn-comp `(1-<29> ,depth) args xbody))
;; 	 (fn-comp-exec-body      (mk-ibody fn fn-comp `(1-<29> ,depth) args tbody))
;; 	 (fn-comp-induction-body (mk-alt-body fn-comp fn-comp-induction (cons depth args) fn-comp-xbody))
;; 	 )

;;     `(

;;       (defun ,fn-comp (,depth ,@args)
;; 	,@arg-type-info
;; 	(declare (type (unsigned-byte 29) ,depth))
;; 	(cond
;; 	 ((zp<29> ,depth) (if (,fn-mbe-domain ,@args)
;; 			      (,fn-mbe ,@args)
;; 			    ,default-expr))
;; 	 (t (mbe :logic (if (,ftest ,@args) (,fbase ,@args)
;; 			  ,fn-comp-xbody)
;; 		 :exec ,fn-comp-exec-body))))

;;       (in-theory (disable (,fn-comp)))

;;       ;; An all-in-one induction strategy for fn-comp
;;       (defun ,fn-comp-induction (,depth ,@args)
;; 	(declare (xargs :measure (llist (nfix ,depth) (,fn-measure ,@args))
;; 			:well-founded-relation l<
;; 			:hints (("Goal" :expand (:with ,fn-mbe-measure-definition (,fn-measure ,@args)))
;; 				(and stable-under-simplificationp
;; 				     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))))
;; 	(cond
;; 	 ((and (zp ,depth) (not (,fn-mbe-domain ,@args))) nil)
;; 	 ((,ftest ,@args) t)
;; 	 (t ,fn-comp-induction-body)))

;;       (defthm ,fn-comp-induction-rule t
;; 	:rule-classes ((:induction :corollary t
;; 				   :pattern (,fn-comp ,depth ,@args)
;; 				   :scheme (,fn-comp-induction ,depth ,@args))))

;;       (in-theory (disable (:induction ,fn-comp)))

;;       (defthmd ,fn-comp-to-fn-mbe
;; 	(implies
;; 	 (,fn-mbe-domain ,@args)
;; 	 (equal (,fn-comp ,depth ,@args)
;; 		(,fn-mbe ,@args)))
;; 	:hints (("Goal" :induct (,fn-comp ,depth ,@args)
;; 		 :expand (:with ,fn-mbe-definition (,fn-mbe ,@args)))
;; 		(and stable-under-simplificationp
;; 		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))))))

;;       ;; A definition rule for fn-comp that better matches the induction
;;       (defthm ,fn-comp-definition
;; 	(equal (,fn-comp ,depth ,@args)
;; 	       (cond
;; 		((and (zp ,depth) (not (,fn-mbe-domain ,@args))) (,fdefault ,@args))
;; 		((,ftest ,@args) (,fbase ,@args))
;; 		(t ,fn-comp-xbody)))
;; 	:hints (("Goal" :in-theory (enable ,fdefault)
;; 		 :expand ((:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))
;; 			  (:with ,fn-mbe-definition (,fn-mbe ,@args)))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-comp (cons depth args)))))

;;       (local (in-theory (disable ,fn-comp-definition)))
;;       (in-theory (disable ,fn-comp))

;;       )))

;; (defun fn-exec (fn
;; 		fn-exec fn-exec-definition fn-comp fn-comp-to-fn-mbe fn-mbe fn-mbe-definition
;; 		fn-exec-domain fn-exec-domain-definition fn-mbe-domain fn-mbe-domain-definition
;; 		fn-exec-measure fn-exec-measure-definition fn-mbe-measure fn-mbe-measure-definition
;; 		fn-exec-induction fn-exec-induction-rule fn-exec-induction-is-fn-exec-domain
;; 		use-total-induction open-fn-exec-domain
;; 		args arg-type-info ftest fbase fdefault tbody xbody
;; 		)
;;   (declare (ignorable fdefault tbody))
;;   (let* ((fn-exec-xbody            (rename-fn (map-fns fn fn-exec args) xbody))
;; 	 (fn-exec-tbody            `(if (,ftest ,@args) (,fbase ,@args) ,fn-exec-xbody))
;; 	 (fn-exec-domain-xbody     (mk-domain-body fn-exec fn-exec-domain args fn-exec-xbody))
;; 	 (fn-exec-domain-tbody     `(if (,ftest ,@args) t ,fn-exec-domain-xbody))
;; 	 (fn-exec-induction-xbody  (mk-domain-body fn-exec fn-exec-induction args fn-exec-xbody))
;; 	 (fn-exec-induction-tbody  `(if (,ftest ,@args) t ,fn-exec-induction-xbody))
;; 	 (fn-exec-measure-xbody    (mk-measure-body fn-exec fn-exec-measure args fn-exec-xbody))
;; 	 (fn-exec-measure-tbody    `(if (,ftest ,@args) 0 ,fn-exec-measure-xbody))
;; 	 )

;;     `(

;;       (defun ,fn-exec ,args
;; 	,@arg-type-info
;; 	(,fn-comp (big-depth-value) ,@args))

;;       (in-theory (disable (,fn-exec)))

;;       ,(rename-state 
;;         `(defthmd ,use-total-induction
;;            (implies
;;             (and
;;              (syntaxp (symbol-listp (list ,@args)))
;;              (syntaxp (not (cw "~% ** Note: ~p0 usually requires :otf-flg t **~%" ',use-total-induction))))
;;             (equal (,fn-exec ,@args)
;;                    (,fn-comp (big-depth-fn) ,@args)))
;;            :hints (("Goal" :in-theory (append '(,fn-exec big-depth-fn) (theory 'defung-theory))))))

;;       (defun ,fn-exec-domain (,@args)
;; 	,@arg-type-info
;; 	(,fn-mbe-domain ,@args))

;;       (in-theory (disable (,fn-exec-domain)))

;;       (defun ,fn-exec-measure (,@args)
;; 	(,fn-mbe-measure ,@args))

;;       (in-theory (disable (,fn-exec-measure)))

;;       (defthm ,fn-exec-definition
;; 	(equal (,fn-exec ,@args)
;; 	       (if (,fn-exec-domain ,@args)
;; 		   ,fn-exec-tbody
;; 		 (,fn-comp (big-depth-value) ,@args)))
;; 	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
;; 		 :expand (:with ,fn-mbe-definition (,fn-mbe ,@args)))
;; 		(and stable-under-simplificationp
;; 		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-exec args))))

;;       (local (in-theory (disable ,fn-exec-definition)))

;;       (defthm ,fn-exec-domain-definition
;; 	(equal (,fn-exec-domain ,@args)
;; 	       ,fn-exec-domain-tbody)
;; 	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
;; 		 :expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-exec-domain args))))

;;       (local (in-theory (disable ,fn-exec-domain-definition)))

;;       (defthm ,fn-exec-measure-definition
;; 	(equal (,fn-exec-measure ,@args)
;; 	       (if (,fn-exec-domain ,@args)
;; 		   ,fn-exec-measure-tbody
;; 		 0))
;; 	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
;; 		 :expand (:with ,fn-mbe-measure-definition (,fn-mbe-measure ,@args)))
;; 		(and stable-under-simplificationp
;; 		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))
;; 	:rule-classes ((:definition
;; 			:install-body t
;; 			:controller-alist ,(default-calist fn-exec-measure args))))

;;       (local (in-theory (disable ,fn-exec-measure-definition)))

;;       (in-theory (disable ,fn-exec ,fn-exec-domain ,fn-exec-measure))

;;       (defun ,fn-exec-induction ,args
;; 	(declare (xargs :measure (,fn-exec-measure ,@args)
;; 			:hints (("Goal" :expand (:with ,fn-exec-measure-definition
;; 						       (,fn-exec-measure ,@args))))))
;; 	(if (,fn-exec-domain ,@args)
;; 	    ,fn-exec-induction-tbody
;; 	  nil))

;;      (defthm ,fn-exec-induction-rule t
;;        :rule-classes ((:induction :corollary t
;; 				  :pattern (,fn-exec ,@args)
;; 				  :scheme (,fn-exec-induction ,@args))))

;;      (in-theory (disable (:definition ,fn-exec-induction) (,fn-exec-induction)))

;;      (defthm ,fn-exec-induction-is-fn-exec-domain
;;        (equal (,fn-exec-induction ,@args) (,fn-exec-domain ,@args))
;;        :hints (("goal" :induct (,fn-exec-induction ,@args)
;; 		:expand ((:with ,fn-exec-domain-definition (,fn-exec-domain ,@args))
;; 			 (,fn-exec-induction ,@args)))))
     
;;      ,(rename-state 
;;        `(defthm ,open-fn-exec-domain
;;           (implies
;;            (and
;;             (syntaxp (symbol-listp (list ,@args)))
;;             (not (,ftest ,@args)))
;;            (equal (,fn-exec-domain ,@args)
;;                   ,fn-exec-domain-xbody))
;;           :hints (("Goal" :expand (:with ,fn-exec-domain-definition (,fn-exec-domain ,@args))))))

;;      (local (in-theory (disable ,open-fn-exec-domain)))


;;      ,@(fn-openers fn-exec fn-exec-definition fn-exec-domain args args ftest `(,fbase ,@args) fn-exec-xbody)

;;      ,@(fn-openers fn-exec-measure fn-exec-measure-definition fn-exec-domain args args ftest '0 fn-exec-measure-xbody)

;;      )))

(defmacro mk-acl2-symb (&rest strlist)
    `(intern (concatenate 'string ,@strlist) "ACL2"))

(defmacro strcatl (&rest strlist) `(concatenate 'string ,@strlist))

(mutual-recursion

 (defun symbols-of-args (args res)
   (if (endp args) res
     (let ((res (symbols-of (car args) res)))
       (symbols-of-args (cdr args) res))))

 (defun symbols-of (term res)
   (if (symbolp term) (cons term res)
     (if (atom term) res
       (if (equal (car term) 'quote) res
	 (let ((res (symbols-of-args (cdr term) res)))
	   (if (atom (car term)) res
	     (symbols-of (caddr (car term)) res)))))))

)

(defun bind-args (args)
  (if (endp args) *nil*
    `(cons (cons (quote ,(car args))
		 (cons ,(car args) (quote nil)))
	   ,(bind-args (cdr args)))))

(defun add-arg-type (type typespec)
  (list* (car typespec)
	 (cadr typespec)
	 (cons type (caddr typespec))
	 (cdddr typespec)))

;;
;; mk-monadic
;;

(defun wf-fapp (x)
  (declare (type t x))
  (and (pseudo-termp x)
       (consp x)
       (not (equal (car x) 'quote))))

(defun binding-listp (x)
  (declare (type t x))
  (if (atom x) (null x)
    (let ((entry (car x)))
      (and (consp entry)
	   (symbol-listp (car entry))
	   (wf-fapp (cdr entry))
	   (binding-listp (cdr x))))))

(defthm symbol-listp-implies-true-listp
  (implies
   (symbol-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

(defthm binding-listp-is-alistp
  (implies
   (binding-listp x)
   (alistp x))
  :rule-classes (:forward-chaining))

(def::signature revappend (binding-listp binding-listp) binding-listp)
(def::signature nth (t pseudo-term-listp) pseudo-termp)

(local (in-theory (disable nth)))

(local (in-theory (disable acl2-count)))

(defthm len-revappend
  (equal (len (revappend x y))
	 (+ (len x) (len y))))

(defthm pseudo-term-listp-pseudo-term-args
  (implies
   (and
    (pseudo-termp x)
    (not (equal (car x) 'quote))
    (consp x))
   (pseudo-term-listp (cdr x)))
  :rule-classes (:forward-chaining))

(defun lambda-map (x)
  (declare (type t x))
  (if (atom x) (null x)
    (let ((entry (car x)))
      (and (consp entry)
	   (symbolp (car entry))
	   (defung::lambda-function-p (cdr entry))
	   (lambda-map (cdr x))))))

(defthm lambda-function-p-implications
  (implies
   (lambda-function-p x)
   (AND (TRUE-LISTP X)
	(EQUAL (LEN X) 3)
	(EQ (CAR X) 'LAMBDA)
	(not (equal x 'quote))
	(SYMBOL-LISTP (CADR X))
	(PSEUDO-TERMP (CADDR X))))
  :hints (("Goal" :in-theory (enable lambda-function-p)))
  :rule-classes (:forward-chaining))

(defthm lambda-map-is-eqlable-alistp
  (implies
   (lambda-map x)
   (and (eqlable-alistp x)
	(symbol-alistp x)))
  :rule-classes (:forward-chaining))

(defthm lambda-function-p-cdr-assoc-lambda-map
  (implies
   (and
    (lambda-map alist)
    (assoc-equal key alist))
   (lambda-function-p (cdr (assoc-equal key alist))))
  :rule-classes ((:forward-chaining :trigger-terms ((assoc-equal key alist)))))

(defun weak-lambda-application-p (term)
  (declare (type t term))
  (and (consp term)
       (let ((fn (car term)))
         (and (consp fn)
              (equal (car fn) 'acl2::lambda)
              (consp (cdr fn))
              (consp (cddr fn))))))

(def::und lambda-application-formals (term)
  (declare (xargs :signature ((weak-lambda-application-p) t)))
  (cadar term))

(defun lambda-application-p (term)
  (and (pseudo-termp term)
       (weak-lambda-application-p term)))

(defthm lambda-application-p-implies
  (implies
   (lambda-application-p term)
   (and (pseudo-termp term)
        (weak-lambda-application-p term)))
  :rule-classes (:forward-chaining))

(defthm implies-lambda-application-p
  (implies
   (and (pseudo-termp term)
        (weak-lambda-application-p term))
   (lambda-application-p term))
  :rule-classes (:type-prescription :rewrite))

(def::signature lambda-application-formals (lambda-application-p)
  symbol-listp
  :hints (("Goal" :in-theory (enable lambda-application-formals))))

(def::und lambda-application-body (term)
  (declare (xargs :signature ((weak-lambda-application-p) t)))
  (caddar term))

(def::signature lambda-application-body (lambda-application-p)
  pseudo-termp
  :hints (("Goal" :in-theory (enable lambda-application-body))))
  
(def::und lambda-application-actuals (term)
  (declare (xargs :signature ((weak-lambda-application-p) t)))
  (cdr term))

(def::signature lambda-application-actuals (lambda-application-p)
  pseudo-term-listp
  :hints (("Goal" :in-theory (enable lambda-application-actuals))))

(defthm len-lambda-application-formals
  (implies
   (and
    (pseudo-termp term)
    (weak-lambda-application-p term))
   (equal (len (lambda-application-formals term))
          (len (lambda-application-actuals term))))
  :hints (("Goal" :in-theory (enable lambda-function-p
                                     lambda-function-formals
                                     lambda-application-formals
                                     lambda-application-actuals))))

(defthm lambda-application-body-decreasing
  (implies
   (weak-lambda-application-p term)
   (< (acl2-count (lambda-application-body term))
      (acl2-count term)))
  :hints (("Goal" :in-theory (enable lambda-application-body)))
  :rule-classes (:linear))

(defthm lambda-application-actuals-decreasing
  (implies
   (weak-lambda-application-p term)
   (< (acl2-count (lambda-application-actuals term))
      (acl2-count term)))
  :hints (("Goal" :in-theory (enable lambda-application-actuals)))
  :rule-classes (:linear))

(defun symbol-map (x)
  (declare (type t x))
  (if (atom x) (null x)
    (let ((entry (car x)))
      (and (consp entry)
	   (symbolp (car entry))
	   (defung::not-quote-symbolp (cdr entry))
	   (symbol-map (cdr x))))))

(defthm symbol-map-is-eqlable-alistp
  (implies
   (symbol-map x)
   (and (eqlable-alistp x)
	(symbol-alistp x)))
  :rule-classes (:forward-chaining))

(defthm eqlable-alistp-implies-alistp
  (implies
   (eqlable-alistp x)
   (alistp x))
  :rule-classes (:forward-chaining))

(defthm symbolp-cdr-assoc-symbol-map
  (implies
   (symbol-map alist)
   (and (symbolp (cdr (assoc-equal key alist)))
	(not (equal (cdr (assoc-equal key alist)) 'quote))))
  :rule-classes ((:forward-chaining :trigger-terms ((assoc-equal key alist)))))

;; We should probably do this in two passes.
;; .. but we don't.

;; So here is where we introduce the single threaded bindings for "dom" ..
;; which means every term is returning stobj-out which means we need
;; to bind all of the stobj-out stuff ..

(defun construct-a-binding (vars fapp dom default funmap defmap term)
;;  (declare (xargs :signature ((symbol-listp wf-fapp symbolp symbolp symbol-map lambda-map pseudo-termp) pseudo-termp)
;;		     :signature-hints (("Goal" :in-theory (enable lambda-function-formals lambda-function-p)))))
  (declare (ignorable default defmap))
  (if (and (symbolp (car fapp))
	   (not (equal (car fapp) 'if)))
      (let ((fx (assoc-eq (car fapp) funmap)))
        ;; (dx (assoc-eq (car fapp) defmap)))
	(if fx ;; (and fx dx (equal (len (cadr (cdr dx))) (len (cdr fapp))))
	    `(mv-let (,dom ,@vars) (,(cdr fx) ,dom ,@(cdr fapp))
		     ,term)
          ;; Do we ever do this??
	  `(mv-let (,dom ,@vars) ,fapp ,term)))
    `(mv-let (,dom ,@vars) ,fapp ,term)))

(defun mv-dom (dom term)
  (cond
   ((atom term)               `(mv ,dom ,term))
   ((equal (car term) 'quote) `(mv ,dom ,term))
   ((equal (car term) 'mv)    `(mv ,dom ,@(cdr term)))
   ((equal (car term) 'mv-let)
    (let ((formals (cadr term))
          (arg     (caddr term))
          (body    (cadddr term)))
      `(mv-let ,formals ,arg ,(mv-dom dom body))))
   ((weak-lambda-application-p term)
    (let ((formals (lambda-application-formals term))
          (body    (lambda-application-body    term)))
      `((lambda ,formals ,(mv-dom dom body)) ,@(cdr term))))
   ;; What if it is a recursive call?  Then we should
   ;; not add the (mv dom ..) wrapper.
   (t
    `(mv ,dom ,term))))

;; We call this when 'term' is known to return (mv dom ..)
(defun construct-bindings-mv-dom (blist dom default funmap defmap term)
  ;; (declare (xargs :signature ((binding-listp symbolp symbolp symbol-map lambda-map pseudo-termp) pseudo-termp)
  ;;       	  :signature-hints (("Goal" :in-theory (disable open-pseudo-termp)))
  ;;       	  :guard-hints (("Goal" :in-theory (disable open-pseudo-termp)))))
  (if (endp blist) term
    (let ((term (construct-a-binding (caar blist) (cdar blist) dom default funmap defmap term)))
      (construct-bindings-mv-dom (cdr blist) dom default funmap defmap term))))

;; We call then when we need to make 'term' return (mv dom ..)
(defund construct-bindings-force-mv (blist dom default funmap defmap term)
  (declare (type t blist))
  ;;  (declare (xargs :signature ((binding-listp symbolp symbolp symbol-map lambda-map pseudo-termp) pseudo-termp)))
  ;; The default return term is wrong .. we need to add dom to the
  ;; return signature.  How do we do that?  Could we somehow
  ;; know that the innermost return is an (mv) ?
  (let ((term (ec-call (mv-dom dom term))))
    (ec-call (construct-bindings-mv-dom blist dom default funmap defmap term))))

;; ------------------------------------------------------------------

;; stobj/mv support ..

;; (mv x y z)
;; (mv-let (x y z) arg body)

;; If "hit" is true, the expression is returning 'dom' in the first
;; argument.

;; When we bind 'value' we actually need to bind all of the return
;; values, including any stobjs, by name.  The binding arguments can
;; be passed in to monadic-surgery.

;; I don't think we need the (if dom (mv t value) (mv nil default))
;; I think (mv dom value) is sufficient.

;; ------------------------------------------------------------------

;; (mv-let (x y z) arg body)

(MUTUAL-RECURSION
 (DEFUN MV-TERMP (X)
   (DECLARE (type t x))
   (COND ((ATOM X) (SYMBOLP X))
         ((EQ (CAR X) 'QUOTE)
          (AND (CONSP (CDR X))
               (NULL (CDR (CDR X)))))
         ((eq (car x) 'mv-let)
          (and (consp (cdr x))
               (symbol-listp (cadr x))
               (consp (cddr x))
               (mv-termp (caddr x))
               (consp (cdddr x))
               (mv-termp (cadddr x))))
         ((NOT (TRUE-LISTP X)) NIL)
         ((NOT (MV-TERM-LISTP (CDR X))) NIL)
         (T (OR (SYMBOLP (CAR X))
                (AND (TRUE-LISTP (CAR X))
                     (EQUAL (LENGTH (CAR X)) 3)
                     (EQ (CAR (CAR X)) 'LAMBDA)
                     (SYMBOL-LISTP (CADR (CAR X)))
                     (MV-TERMP (CADDR (CAR X)))
                     (EQUAL (LENGTH (CADR (CAR X)))
                            (LENGTH (CDR X))))))))
 (DEFUN MV-TERM-LISTP (LST)
   (DECLARE (type t lst))
   (COND ((ATOM LST) (EQUAL LST NIL))
         (T (AND (MV-TERMP (CAR LST))
                 (MV-TERM-LISTP (CDR LST))))))
 )

;; The only reason we generate bindings is to allow us to thread
;; stuff 

(defun mv? (values)
  (declare (type t values))
  (if (not (consp values)) nil
    (if (null (cdr values)) (car values)
      (cons 'mv values))))

(mutual-recursion

 (defun monadic-surgery-args-list (stobj-out fmap dom default defmap list blist vars res hit)
   (declare (xargs :measure (acl2-count list)
                   :verify-guards nil)
	    (type (satisfies symbol-map) fmap)
	    (type (satisfies symbolp) dom)
	    (type (satisfies symbolp) default)
	    (type (satisfies lambda-map) defmap)
	    ;;(type (satisfies pseudo-term-listp) list)
	    ;;(type (satisfies binding-listp) blist)
	    ;;(type (satisfies symbol-listp) vars)
	    (type (satisfies true-listp) res)
            )
   (if (not (consp list)) (mv (revappend res nil) blist vars hit)
     (met ((term blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap (car list) blist vars hit))
       (monadic-surgery-args-list stobj-out fmap dom default defmap (cdr list) blist vars (cons term res) hit))))

 (defun monadic-surgery-expr (stobj-out fmap dom default defmap term blist vars hit)
   (declare (xargs :measure (acl2-count term)
                   :verify-guards nil)
	    (type (satisfies symbol-map) fmap)
	    (type (satisfies symbolp) dom)
	    (type (satisfies symbolp) default)
	    (type (satisfies lambda-map) defmap)
	    ;;(type (satisfies pseudo-termp) term)
	    ;;(type (satisfies binding-listp) blist)
	    ;;(type (satisfies symbol-listp) vars)
            )
   (cond
    ((atom term) (mv term blist vars hit))
    ((equal (car term) 'quote) (mv term blist vars hit))
    ;; Do we need to do anything special for "mv" terms?
    ;;   I suspect we do ..
    ((equal (car term) 'if)
     (let ((args (cdr term)))
       (let ((test (nth 0 args))
	     (then (nth 1 args))
	     (else (nth 2 args)))
	 (met ((test blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap test blist vars hit))
	   (met ((then then-blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap then nil vars hit))
	     (met ((else else-blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap else nil vars hit))
	       (if (or then-blist else-blist)
		   (met ((fvar vars) (gensym+sig 'var stobj-out nil vars))
		     (mv (mv? fvar) (acons fvar `(if ,test ,(construct-bindings-force-mv then-blist dom default fmap defmap then)
                                                   ,(construct-bindings-force-mv else-blist dom default fmap defmap else)) blist) vars hit))
		 (mv `(if ,test ,then ,else) blist vars hit))))))))
    ((equal (car term) 'mv-let)
     (let ((formals (cadr term))
           (arg     (caddr term))
           (body    (cadddr term)))
       (met ((arg blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap arg nil vars nil))
         (met ((body bblist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap body nil vars hit))
           (if (not bblist) (mv `(mv-let ,formals ,arg ,body) blist vars hit)
             (met ((fvar vars) (gensym+sig 'var stobj-out nil vars))
               (let ((body (construct-bindings-force-mv bblist dom default fmap defmap body)))
                 (mv (mv? fvar) (acons fvar `(mv-let ,formals ,arg ,body) blist) vars hit))))))))
    (t
     (met ((args blist vars hit) (monadic-surgery-args-list stobj-out fmap dom default defmap (cdr term) blist vars nil hit))
       (let ((fn (car term)))
         (cond
          ((consp fn)
           (let ((formals (cadr fn))
                 (body    (caddr fn)))
             (met ((body bblist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap body nil vars hit))
               (if (not bblist) (mv `((lambda ,formals ,body) ,@args) blist vars hit)
                 (met ((fvar vars) (gensym+sig 'var stobj-out nil vars))
                   (let ((body (construct-bindings-force-mv bblist dom default fmap defmap body)))
                     (mv (mv? fvar) (acons fvar `((lambda ,formals ,body) ,@args) blist) vars hit)))))))
          ((assoc fn fmap)
           (met ((fvar vars) (gensym+sig 'var stobj-out nil vars))
             (mv (mv? fvar) (acons fvar `(,fn ,@args) blist) vars t)))
          (t 
           (mv (cons fn args) blist vars hit)))))))
   )
 )

;; (acl2::make-flag
;;  monadic-surgery-clique
;;  monadic-surgery-expr
;;  )

;; (encapsulate

;;     ()

;;   (local (in-theory (disable open-pseudo-termp)))
;;   (local (in-theory (enable pseudo-termp)))

;; (defthm-monadic-surgery-clique

;;   (defthm monadic-surgery-args-list-type
;;     (implies
;;      (and (symbol-map fmap)
;; 	  (symbolp dom)
;; 	  (symbolp default)
;; 	  (lambda-map defmap)
;; 	  (pseudo-term-listp list)
;; 	  (binding-listp blist)
;; 	  (symbol-listp vars)
;; 	  (pseudo-term-listp res))
;;      (and
;;       (true-listp (monadic-surgery-args-list fmap dom default defmap list blist vars res hit))
;;       (and
;;        (pseudo-term-listp (val '0
;; 			       (monadic-surgery-args-list fmap dom default defmap list blist vars res hit)))
;;        (equal (len (val '0
;; 			(monadic-surgery-args-list fmap dom default defmap list blist vars res hit)))
;; 	      (+ (len res) (len list))))
;;       (binding-listp (val '1
;; 			  (monadic-surgery-args-list fmap dom default defmap list blist vars res hit)))
;;       (symbol-listp (val '2
;; 			 (monadic-surgery-args-list fmap dom default defmap list blist vars res hit)))))
;;     :flag monadic-surgery-args-list
;;     :rule-classes
;;     (:rewrite
;;      (:forward-chaining
;;       :trigger-terms ((monadic-surgery-args-list fmap dom default defmap list blist vars res hit)))))

;;   (defthm monadic-surgery-expr-type
;;     (implies (and (symbol-map fmap)
;; 		  (symbolp dom)
;; 		  (symbolp default)
;; 		  (lambda-map defmap)
;; 		  (pseudo-termp term)
;; 		  (binding-listp blist)
;; 		  (symbol-listp vars))
;; 	     (and (true-listp (monadic-surgery-expr fmap dom default defmap term blist vars hit))
;; 		  (pseudo-termp (val '0
;; 				     (monadic-surgery-expr fmap dom default defmap term blist vars hit)))
;; 		  (binding-listp (val '1
;; 				      (monadic-surgery-expr fmap dom default defmap term blist vars hit)))
;; 		  (symbol-listp (val '2
;; 				     (monadic-surgery-expr fmap dom default defmap term blist vars hit)))))
;;     :flag monadic-surgery-expr
;;     :rule-classes
;;     (:rewrite (:forward-chaining
;; 	       :trigger-terms ((monadic-surgery-expr fmap dom default defmap term blist vars hit)))))
;;   )

;; (verify-guards monadic-surgery-expr)

;; So .. monadic-surgery-fn always returns an (mv dom .. ) term.


(defun monadic-surgery-fn (stobj-out fmap dom default defmap term vars)
  ;; :signature ((symbol-map symbolp symbolp lambda-map pseudo-termp symbol-listp) pseudo-termp)))
  (cond
   ((atom term) `(if ,dom (mv t ,term) (non-exec (mv nil nil))))
   ((equal (car term) 'quote) 
    `(if ,dom (mv t ,term) (non-exec (mv nil nil))))
   ((equal (car term) 'mv)
    (met ((args blist vars hit) (monadic-surgery-args-list stobj-out fmap dom default defmap (cdr term) nil vars nil nil))
      (declare (ignore vars hit))
      (let ((term `(if ,dom (mv t ,@args) (non-exec (mv nil nil)))))
        (construct-bindings-mv-dom blist dom default fmap defmap term))))
   ((equal (car term) 'if)
    (let ((args (cdr term)))
      (let ((test (nth 0 args))
	    (then (nth 1 args))
	    (else (nth 2 args)))
	(met ((test blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap test nil vars nil))
          (declare (ignore hit))
	  (let ((then (monadic-surgery-fn stobj-out fmap dom default defmap then vars))
		(else (monadic-surgery-fn stobj-out fmap dom default defmap else vars)))
	    (let ((term `(if ,test ,then ,else)))
	      (let ((term (construct-bindings-mv-dom blist dom default fmap defmap term)))
		term)))))))
   ;;
   ;; (mv-let (x y z) arg body)
   ;; (mv a b c)
   ;;
   ;; ((equal (car term) 'acl2::mv-let) ..)
   ((equal (car term) 'mv-let)
    (let ((formals (cadr term))
          (arg     (caddr term))
          (body    (cadddr term)))
      (met ((arg blist vars hit) (monadic-surgery-expr stobj-out fmap dom default defmap arg nil vars nil))
        (declare (ignore hit))
        (let ((body (monadic-surgery-fn stobj-out fmap dom default defmap body vars)))
          (construct-bindings-mv-dom blist dom default fmap defmap `(mv-let ,formals ,arg ,body))))))
   (t
    (met ((args blist vars hit) (monadic-surgery-args-list stobj-out fmap dom default defmap (cdr term) nil vars nil nil))
      (declare (ignore hit))
      (let ((term (cond
		   ((consp (car term))
		    (let ((formals (cadr (car term)))
			  (body    (caddr (car term))))
		      (let ((body (monadic-surgery-fn stobj-out fmap dom default defmap body vars)))
			(construct-bindings-mv-dom blist dom default fmap defmap `((lambda ,formals ,body) ,@args)))))
		   ((assoc-eq (car term) fmap)
		    (construct-bindings-mv-dom blist dom default fmap defmap `(,(cdr (assoc-eq (car term) fmap)) ,dom ,@args)))
		   (t 
                    (let ((body `(if ,dom (mv t ,(cons (car term) args)) (non-exec (mv nil nil)))))
                      (construct-bindings-mv-dom blist dom default fmap defmap body))))))
	term)))
   
   ))

;; The default value represents a substantial computational challenge.
;;
;; There are really three cases:
;;
;; 1. Constant value
;; 2. Computed value, constant type.
;; 3. Computed value, dependent type.
;;
;; To do 3 correctly,

;; A lambda expression binding the symbol 'mv
;; whose body is a lambda expression binding
;; some number of symbols, each of which is
;; bound to (mv-nth i mv)

(defun weak-hide-termp (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'acl2::hide)
       (consp (cdr term))))

(defun hide-termp (term)
  (and (pseudo-termp term)
       (weak-hide-termp term)))

(def::und hide-body (term)
  (declare (xargs :signature ((weak-hide-termp) t)))
  (cadr term))

(defun mv-nth-termp! (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'acl2::mv-nth)
       (consp (cdr term))
       (consp (cddr term))))

(defun mv-nth-termp (term)
  (declare (type t term))
  (or (mv-nth-termp! term)
      (and (weak-hide-termp term)
           (mv-nth-termp! (hide-body term)))))

(defun mv-nth-listp (list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (mv-nth-termp (car list))
         (mv-nth-listp (cdr list)))))

(defun mv-bindingp (term)
  (declare (type t term))
  (and (weak-lambda-application-p term)
       (equal (lambda-application-formals term) '(acl2::mv))
       (consp (lambda-application-actuals term))
       (let ((body (lambda-application-body term)))
         (and (weak-lambda-application-p body)
              (mv-nth-listp (lambda-application-actuals body))))))

(defthm mv-binding-implication
  (implies
   (mv-bindingp term)
   (and (weak-lambda-application-p term)
        (weak-lambda-application-p (lambda-application-body term))))
  :rule-classes (:forward-chaining))

(in-theory (disable mv-nth-termp weak-lambda-application-p))

;; (def::und reconstruct-mv-let (term)
;;   (declare (xargs :signature ((mv-bindingp) t)))
;;   (let ((body (lambda-application-body term)))
;;     (let ((formals (lambda-application-formals body))
;;           (actuals (reconstruct-mv-args (lambda-application-actuals term))))
;;       (let ((actual (reconstruct-mv (car actuals))))
;;         `(acl2::mv-let ,formals ,actual
;;                        ,(lambda-application-body body))))))
  
(def::und extract-cars (term)
  (declare (xargs :signature ((mv-termp) mv-term-listp)))
  (if (and (consp term)
           (equal (car term) 'acl2::cons)
           (consp (cdr term))
           (consp (cddr term)))
      (cons (cadr term) (extract-cars (caddr term)))
    nil))

;; Yeah .. but it probably isn't worth type checking just yet.
;; Let's get it working first.

(defun reconstruct-mv (term)
  (cond
   ((atom term) term)
   ((equal (car term) 'acl2::quote) 
    term)
   ((equal (car term) 'acl2::cons)
    `(mv ,@(extract-cars term)))
   ((equal (car term) 'acl2::mv-let)
    (let ((formals (cadr term))
          (body    (caddr term))
          (actual  (cadddr term)))
      `(mv-let ,formals ,body ,(reconstruct-mv actual))))
   ((equal (car term) 'acl2::if)
    `(if ,(nth 1 term)
         ,(reconstruct-mv (caddr term))
       ,(reconstruct-mv (cadddr term))))
   ((weak-lambda-application-p term)
    `((lambda ,(lambda-application-formals term) 
        ,(reconstruct-mv (lambda-application-body term)))
      ,@(lambda-application-actuals term)))
   (t
    term)))

(mutual-recursion

 (defun reconstruct-mv-let (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term) term)
    ((equal (car term) 'acl2::quote)
     term)
    ((mv-bindingp term)
     (let ((body (lambda-application-body term)))
       (let ((formals (lambda-application-formals body))
             (actuals (reconstruct-mv-let-args (lambda-application-actuals term))))
         (let ((actual (reconstruct-mv (car actuals))))
           `(acl2::mv-let ,formals ,actual
                          ,(lambda-application-body body))))))
    ((weak-lambda-application-p term)
     `((lambda ,(lambda-application-formals term) 
         ,(reconstruct-mv-let (lambda-application-body term)))
       ,@(reconstruct-mv-let-args (lambda-application-actuals term))))
    (t
     (cons (car term) (reconstruct-mv-let-args (cdr term))))))
 
 (defun reconstruct-mv-let-args (args)
   (declare (xargs :measure (acl2-count args)))
   (if (not (consp args)) nil
     (cons (reconstruct-mv-let (car args))
           (reconstruct-mv-let-args (cdr args)))))

 )

(defun drop-equal-formal-actual-pairs (formals actuals formalres actualres)
  (if (endp formals) (mv (revappend formalres nil) (revappend actualres nil))
    (if (equal (car formals) (car actuals))
        (drop-equal-formal-actual-pairs (cdr formals) (cdr actuals) formalres actualres)
      (drop-equal-formal-actual-pairs (cdr formals) 
                                      (cdr actuals) 
                                      (cons (car formals) formalres) 
                                      (cons (car actuals) actualres)))))

(mutual-recursion

 (defun remove-redundant-bindings-args (args)
   (if (endp args) nil
     (cons (remove-redundant-bindings (car args))
           (remove-redundant-bindings-args (cdr args)))))
 
 (defun remove-redundant-bindings (term)
   (cond
    ((atom term) term)
    ((equal (car term) 'quote) term)
    ((equal (car term) 'mv-let)
     (let ((formals (cadr term))
           (arg     (remove-redundant-bindings (caddr term)))
           (body    (remove-redundant-bindings (cadddr term))))
       `(mv-let ,formals ,arg ,body)))
    ((weak-lambda-application-p term)
     (let ((formals (lambda-application-formals term))
           (actuals (cdr term))
           (body    (lambda-application-body term)))
       (let ((actuals (remove-redundant-bindings-args actuals))
             (body    (remove-redundant-bindings body)))
         (met ((formals actuals) (drop-equal-formal-actual-pairs formals actuals nil nil))
           `((lambda ,formals ,body) ,@actuals)))))
    (t
     (cons (car term) (remove-redundant-bindings-args (cdr term))))))
 
 )

;; We need to push stobj-out a bit farther .. using it to bind 'val' 
(defun monadic-surgery (stobj-out fmap dom default defmap term vars)
  (let ((term (if (< (len stobj-out) 2) term (reconstruct-mv term))))
    (let ((term (reconstruct-mv-let term)))
      (let ((term (remove-redundant-bindings term)))
        (monadic-surgery-fn stobj-out fmap dom default defmap term vars)))))

(defun stobjs-in-list (formals wrld)
  (declare (xargs :mode :program))
  (if (endp formals) nil
    (cons (and (acl2::stobjp (car formals) nil wrld) (car formals))
          (stobjs-in-list (cdr formals) wrld))))

(defun tt-fn (fn args body wrld)
  (declare (xargs :mode :program))
  (let ((fn-args-list (list (cons fn args)
                            `(done state)
                            `(next state)
                            )))
    (met ((err tbody sig) (acl2::pseudo-translate-defun fn (stobjs-in-list args wrld) body fn-args-list wrld))
      (declare (ignore err))
      (let ((term (monadic-surgery sig (acons fn (symbol-fns::suffix fn '-mon) nil) 'dom 'default nil tbody (symbols-of tbody nil))))
        (acl2::untranslate1 term nil nil nil wrld)))))

(defmacro tt (fn args body)
  `(tt-fn ',fn ',args ',body (w state)))

#+joe
(trace$ (acl2::pseudo-translate :entry `(acl2::pseudo-translate ,acl2::form)))

#+joe
(trace$ (monadic-surgery-args-list :entry `(monadic-surgery-args-list ,fmap ,list)))

#+joe
(trace$ (monadic-surgery-expr :entry `(monadic-surgery-expr ,fmap ,term)))

#+joe
(trace$ (monadic-surgery-fn :entry `(monadic-surgery-fn ,fmap ,term)))

#+joe
(trace$ (reconstruct-mv-let :entry `(reconstruct-mv-let ,term)))

#+joe
(trace$ construct-a-binding)

;; The last two met bindings are reversed ..
#+joe
(tt zed (n state)
    (if (done state) (mv n state)
      (if (< n 0) (zed 1 state)
        (let ((n (met ((x y) (mv (+ n 1) (+ 2 n)))
                   (+ x y))))
          (let ((state (next state)))
            (met ((n state) (zed (+ n 1) state))
              (zed (+ n 2) state)))))))

#+joe
(tt ack (x y)
    (if (<= x 0) (1+ y)
      (if (<= y 0) (ack (1- x) 1)
        (ack (1- x) (ack x (1- y))))))

#+joe
(monadic-surgery (acons 'ack 'xack nil) 'dom 'default 'ack-default
		 '(if (defung::true (= x '0)) (1+ y)
		    (if (defung::true (= y '0)) (ack (1- x) '1)
		      (ack (1- x) (ack x (1- y))))) '(x y))

#|
;; (mv-let (x y z) a
;;   (+ x y z))

;; (mv-let (mv y z) a
;;         (+ mv y z))

;; (defun example ()
;;   '((LAMBDA (MV) ((LAMBDA (X Y Z)
;;                           (BINARY-+ X (BINARY-+ Y Z)))
;;                   (MV-NTH '0 MV)
;;                   (MV-NTH '1 MV)
;;                   (MV-NTH '2 MV)))
;;     A))

;; (mv-bindingp (example))

;; (lambda-application-body (example))
;; (lambda-application-actuals (example)) => (A)
;; (lambda-application-body (lambda-application-body (example))) => (BINARY-+ X (BINARY-+ Y Z))
;; ;; Worthless ..
;; (lambda-application-actuals (lambda-application-body (example))) -> mv-nth list
;; (lambda-application-formals (lambda-application-body (example))) -> (x y z)

;; (mv-let (x y z) a
;;         (declare (ignorable y))
;;         (+ x z))

|#

(def::und alt-args (args avoid)
  (declare (xargs :signature ((symbol-listp symbol-listp) symbol-listp)))
  (if (endp args) nil
    (cons (gensym::gensym (symbol-fns::join-symbols 'defung::|| 'alt- (car args)) avoid)
          (alt-args (cdr args) avoid))))

(defun add-guard-conditions (cond list)
  (if (endp list) nil
    (let ((guard (car list)))
      (let ((guard `(if ,cond ,guard t)))
        (cons guard (add-guard-conditions cond (cdr list)))))))

(defun add-guard-declarations (guards decls)
  (if (endp guards) decls
    (cons `(declare (xargs :guard ,(car guards)))
          (add-guard-declarations (cdr guards) decls))))

(defun conditional-guards (cond decls)
  (met ((guards decls) (defun::extract-xarg-key-from-decls :guard decls))
    (let ((guards (add-guard-conditions cond guards)))
      (add-guard-declarations guards decls))))

(defun mk-monadic (fnx fn fn-definition fn0 fn0-definition
		  fn-domain fn-domain-definition fn0-domain fn0-domain-definition
		  fn-measure fn-measure-type fn-measure-definition fn0-measure fn0-measure-definition
		  fn-induction fn-induction-rule fn-induction-is-fn-domain
		  open-fn-domain fn-domain-true
		  vars args arg-type-info ftest fbase default-value stobj-out tbody xbody ec-call
                  copy-args
		  )
  (declare (ignore fn0-definition))
  (let* ((omit               `(,fnx ,@ec-call ,@(ec-call-omit)))
	 (dom                 (gensym::gensym 'dom vars))
	 (vars                (cons dom vars))
	 (default             (gensym::gensym 'default vars))
	 (vars                (cons default vars))
         (alt-args            (alt-args args vars))
         (vars                (append alt-args vars))
	 #+joe
	 (default-guard       (and (consp default-type)
				   `((declare (xargs :guard
						     ,(if (consp (cdr default-type))
							  (defun::vals-to-thms-rec 0 default-type default)
							`(and ,@(defun::translate-declaration-to-guard-list (car default-type) default))))))))
	 (fnx-tbody           (if ec-call (map-ec-call-term tbody omit) tbody))
	 (defmap              (acons fn `(lambda ,args ,(if ec-call (map-ec-call-term default-value omit) default-value)) nil))
	 (fnx-tbody           (monadic-surgery stobj-out (acons fn fnx nil) dom default defmap fnx-tbody vars))
	 (fnx-tbody           (strip-bad-ec-calls fnx-tbody))
	 (fn-xbody            xbody)
	 (fn-tbody            `(if (,ftest ,@args) (,fbase ,@args) ,fn-xbody))
	 (fn-domain-xbody     (mk-domain-body fn fn-domain args fn-xbody))
	 (fn-domain-tbody     `(if (,ftest ,@args) t ,fn-domain-xbody))
	 (fn-induction-xbody  (mk-domain-body fn fn-induction args fn-xbody))
	 (fn-induction-tbody  `(if (,ftest ,@args) t ,fn-induction-xbody))
	 (fn-measure-xbody    (mk-measure-body fn fn-measure args fn-xbody))
	 (fn-measure-tbody    `(if (,ftest ,@args) 0 ,fn-measure-xbody))
	 )
    (met ((fvar vars) (gensym+sig 'var stobj-out nil nil))
      (declare (ignore vars))
      `(
        
        ;; Technically I think the guard needs to be weakened such that
        ;; it applies only for a "true" dom argument: (implies dom guard)
        ;; This obviates the need for a fancy guard on the default
        ;; value.
        
        ;; What is the point of the "dom" argument?  Oh .. we thread it
        ;; through recursive calls.  The alternative is we need to save
        ;; them off somewhere and then "and" them all together.
        
        (defun ,fnx (,dom ,@args)
          ,@(conditional-guards dom arg-type-info)
          (declare (type (satisfies booleanp) ,dom))
          (declare (xargs :verify-guards nil))
          (mbe :logic (non-exec (let ((dom (and dom (,fn0-domain ,@args))))
                                  (if dom (met (,fvar (,fn0 ,@args))
                                            (mv t ,@fvar))
                                    (mv nil nil))))
               :exec (if (not ,dom) (non-exec (mv nil nil))
                       ,fnx-tbody)))
        
        (in-theory (disable (,fnx)))

        (defun-nx ,fn-domain ,args
          ;;,@arg-type-info
          (non-exec (met ((dom ,@fvar) (,fnx t ,@args))
                      (declare (ignore ,@fvar))
                      dom)))
        
        (in-theory (disable (,fn-domain)))
        ;; (booleanp (,fn-domain ,@args))
        
        (defun ,fn ,args
          ,@arg-type-info
          (met (,alt-args (,copy-args ,@args))
            (met ((dom ,@fvar) ,(if ec-call (map-ec-call-term `(,fnx t ,@args) omit)
                                  `(,fnx t ,@args)))
              (if (not dom) (non-exec 
                             (met (,args ,(mv? alt-args))
                               ,(if ec-call (map-ec-call-term default-value omit) default-value)))
                ,(mv? fvar)))))
        
        (defun ,fn-measure ,args
          (,fn0-measure ,@args))
        
        (defthm ,fn-measure-type
          (natp (,fn-measure ,@args))
          :rule-classes ((:forward-chaining :trigger-terms ((,fn-measure ,@args)))
                         :type-prescription
                         :rewrite))
        
        (encapsulate
            ()
          
          (defthm ,fn-definition
            (equal (,fn ,@args)
                   (if (not (,fn-domain ,@args)) 
                       (met (,alt-args (,copy-args ,@args))
                         (met (,args ,(mv? alt-args))
                           ,default-value))
                     ,fn-tbody))
            :rule-classes ((:definition :install-body t :controller-alist ,(default-calist fn args)))
            :hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args)))
                    (and acl2::stable-under-simplificationp
                         '(:in-theory (enable ,fbase)))))
          
          (local (in-theory (disable ,fn-definition)))
          
          (defthm ,fn-domain-definition
            (equal (,fn-domain ,@args)
                   ,fn-domain-tbody)
            :rule-classes ((:definition :install-body t :controller-alist ,(default-calist fn-domain args)))
            :hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args)))))
          
          (local (in-theory (disable ,fn-domain-definition)))
          
          (defthm ,fn-measure-definition
            (equal (,fn-measure ,@args)
                   (if (not (,fn-domain ,@args)) 0
                     ,fn-measure-tbody))
            :rule-classes ((:definition :install-body t :controller-alist ,(default-calist fn-measure args)))
            :hints (("Goal" :expand ((:with ,fn0-domain-definition (,fn0-domain ,@args))
                                     (:with ,fn0-measure-definition (,fn0-measure ,@args))))))
          
          (in-theory (disable (:definition ,fn)
                              (:definition ,fn-domain)
                              (:definition ,fn-measure)))
          
          )
        
        (encapsulate
            ()
          
          (local (in-theory (disable ,fn-definition)))
          
          (defun-nx ,fn-induction ,args
            (declare (xargs :measure (,fn-measure ,@args)
                            :hints ((and stable-under-simplificationp
                                         '(:expand (,fn-measure ,@args))))))
            (if (not (,fn-domain ,@args)) nil
              ,fn-induction-tbody))
          
          (defthm ,fn-induction-is-fn-domain
            (equal (,fn-induction ,@args)
                   (,fn-domain ,@args))
            :hints (("Goal" :induct (,fn-induction ,@args))))
          
          (defthm ,fn-induction-rule t
            :rule-classes ((:induction :corollary t
                                       :pattern (,fn ,@args)
                                       :scheme (,fn-induction ,@args))))
          
          ,(rename-state
            `(defthm ,open-fn-domain
               (implies
                (and
                 (syntaxp (symbol-listp (list ,@args)))
                 (not (,ftest ,@args)))
                (equal (,fn-domain ,@args) ,fn-domain-xbody))
               :hints (("Goal" :expand (:with ,fn-domain-definition (,fn-domain ,@args))))))
          
          (defthm ,fn-domain-true
            (implies
             (,ftest ,@args)
             (,fn-domain ,@args))
            :hints (("Goal" :expand (:with ,fn-domain-definition (,fn-domain ,@args)))))
          
          )
        
        (local (in-theory (disable ,open-fn-domain)))
        
        ,@(fn-openers fn fn-definition fn-domain args args ftest `(,fbase ,@args) fn-xbody)
        
        ,@(fn-openers fn-measure fn-measure-definition fn-domain args args ftest '0 fn-measure-xbody)
        
        ))))

(defun defunger (fn args doc decls body tbody stobj-out)
  (declare (type (satisfies not-quote-symbolp) fn)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies pseudo-termp) tbody)
           (type (satisfies true-listp) stobj-out)
	   (ignore doc body)
	   (xargs :verify-guards nil))
  ;;
  ;; fn    : the function name desired by user
  ;; body  : the original body of the function as provided by the user
  ;; tbody : the macro expanded version of the body (pseudo-termp)
  ;;
  ;;(met ((stest sbase cbody) (split-term-on-fn fn tbody))
  ;;  (let ((stest (cond-to-pseudo-termp t   stest))
  ;;	    (sbase (cond-to-pseudo-termp nil sbase))
  ;;	    (sbody (cond-to-pseudo-termp nil cbody)))

  (met ((stest sbase sbody) (split-term-on-fset (list fn) tbody))
    ;;(let ((cbodyp (normalized-if-to-parallel-cond sbody)))
    (met ((typespec signature fty-sig sig-hints decls) (defun::extract-function-declaration decls))
      (declare (ignore fty-sig))
      (met ((default-value decls) (defun::extract-xarg-key-from-decls :default-value decls))
      ;;(met ((default-type decls) (defun::extract-xarg-key-from-decls :default-type decls))
      (met ((nx decls) (defun::extract-xarg-key-from-decls :non-executable decls))
      (met ((no-ec-call decls) (defun::extract-xarg-key-from-decls :no-ec-call decls))
      (met ((copy-args  decls) (defun::extract-xarg-key-from-decls :copy-args  decls))

	(let*
	    (
	     (typespec        (or typespec signature))
             (copy-args       (or (car copy-args) `(lambda ,args ,(mv? args))))

	     (default-value  (and (consp default-value)
				  (let ((expr (car default-value)))
				    (if (not expr) *nil* expr))))

	     (default-value   (or default-value sbase))

	     ;; The default type could also be provided via the signature.
	     #+joe
	     (default-type    (or (and (consp default-type) default-type)
				  (and signature (defun::function-declaration-vals typespec))))

	     (verify-guards   (defun::get-xarg-keys-from-decls :verify-guards decls))
	     (xarg-guards     (defun::get-xarg-keys-from-decls :guard decls))
	     (guard-hints     (defun::get-xarg-keys-from-decls :guard-hints decls))
	     (type-decls      (defun::get-type-declarations-from-decls decls))

	     (nx              (and (consp nx) (car nx)))

	     (typeinfo        (or signature verify-guards xarg-guards type-decls))

	     (ec-call         (and (not nx) (not typeinfo)
				   (append `(and defung::true acl2::mv acl2::mv-let)
					   (and (consp no-ec-call) (car no-ec-call)))))

	     (verify-guards   (and (not nx) (not (defun::contains-nil verify-guards))))

	     (body-symbols (symbols-of tbody nil))
	     (depth (gensym::gensym 'd body-symbols))
	     (vars (cons depth body-symbols))
	     (d1 (gensym::gensym 'd1 vars))
	     (d2 (gensym::gensym 'd2 (cons d1 vars)))

	     (fname  fn)

	     (fbase    (symbol-fns::suffix fname "-base"))
	     (ftest    (symbol-fns::suffix fname "-test"))
	     (fdefault (symbol-fns::suffix fname "-DEFAULT"))

	     ;; Indexed Functions

	     (iname      (symbol-fns::prefix "i" fname))
	     (ifn        (symbol-fns::suffix iname))
	     (idom       (symbol-fns::suffix iname "-DOMAIN"))
	     (indexx     (symbol-fns::suffix iname '-index))
	     (arb-index  (symbol-fns::prefix "ARB-" indexx))

	     (arb-index-thm      (symbol-fns::suffix arb-index "-THM"))
	     (mono-determ        (symbol-fns::suffix iname "-MONO-DETERM"))
	     (mono               (symbol-fns::suffix iname "-DOMAIN-MONOTONE"))
	     (mono-contra        (symbol-fns::suffix mono  "-CONTRAPOSITIVE"))
	     (idom-lower-bound   (symbol-fns::suffix iname "-DOMAIN-LOWER-BOUND"))
	     (ifn-min-index      (symbol-fns::suffix iname "-MIN-INDEX"))
	     (natp-min-index     (symbol-fns::prefix "NATP-" ifn-min-index))
	     (idom-min-index     (symbol-fns::suffix iname "-DOMAIN-MIN-INDEX"))
	     (min-index-bound    (symbol-fns::suffix iname "-MIN-INDEX-BOUND"))
	     (min-index-smallest (symbol-fns::suffix iname "-MIN-INDEX-SMALLEST"))

	     ;; FN0 (in terms of indexed function)

	     (f0name               (if nx fname (symbol-fns::suffix fname "-0")))
	     (fn0-measure          (symbol-fns::suffix f0name "-MEASURE"))
	     (fn0-measure-type     (symbol-fns::suffix fn0-measure '-type))
	     (fn0-measure-property (symbol-fns::suffix fn0-measure "-PROPERTY"))
	     (fn0-measure-smallest (symbol-fns::suffix fn0-measure "-SMALLEST"))
	     (replace-index-by-fn0-measure    (symbol-fns::prefix "REPLACE-" arb-index "-BY-" fn0-measure))
	     (replace-index-by-fn0-measure-2  (symbol-fns::suffix replace-index-by-fn0-measure "-2"))
	     (replace-domain-index-by-fn0-measure
	                           (symbol-fns::prefix "REPLACE-" iname "-DOMAIN-INDEX-BY-" fn0-measure))
	     (fn0            f0name)
	     (fn0-definition (symbol-fns::suffix f0name "-DEFINITION"))
	     (fn0-measure-definition (symbol-fns::suffix fn0-measure "-DEFINITION"))
	     (fn0-domain     (symbol-fns::suffix fn0 "-DOMAIN"))
	     (open-fn0-domain (symbol-fns::prefix 'open- fn0-domain))
	     (fn0-domain-true (symbol-fns::suffix fn0-domain '-true))
	     (fn0-domain-definition  (symbol-fns::suffix fn0 "-DOMAIN-DEFINITION"))
	     (not-fn0-domain (symbol-fns::prefix 'not- fn0-domain))
	     (not-fn0-domain-implies-zero-fn0-measure (symbol-fns::suffix not-fn0-domain '-implies-zero- fn0-measure))
	     (fn0-induction (symbol-fns::suffix f0name "-INDUCTION"))
	     (fn0-induction-rule (symbol-fns::suffix f0name "-INDUCTION-RULE"))
	     (fn0-induction-is-fn0-domain (symbol-fns::suffix f0name "-INDUCTION-IS-" f0name "-DOMAIN"))

	     (fn-monadic            (symbol-fns::suffix fname "-MONADIC"))
	     (fn-definition         (symbol-fns::suffix fn '-definition))
	     (fn-domain             (symbol-fns::suffix fn '-domain))
	     (open-fn-domain        (symbol-fns::prefix 'open- fn-domain))
	     (fn-domain-true        (symbol-fns::suffix fn-domain '-true))
	     (fn-domain-definition  (symbol-fns::suffix fn-domain '-definition))

	     (fn-measure            (symbol-fns::suffix fn '-measure))
	     (fn-measure-type       (symbol-fns::suffix fn-measure '-type))
	     (fn-measure-definition (symbol-fns::suffix fn-measure '-definition))
	     (fn-induction          (symbol-fns::suffix fn '-induction))
	     (fn-induction-rule     (symbol-fns::suffix fn-induction '-rule))
	     (fn-induction-is-fn-domain
	      (symbol-fns::suffix fn-induction '-is- fn-domain))

	     (decls           (if signature
				  (cons `(declare
					  (xargs :guard
						 ,(defun::function-declaration-to-guard args signature))) decls)
				decls))
	     (inhibited-decls (cons `(declare (xargs :verify-guards nil)) decls))
	     (arg-type-info   inhibited-decls)

	     (fn0-typethm      (and typespec
				    (defun::function-declaration-to-type-thm-hyps fn0 args
				      (list `(,fn0-domain ,@args))
				      typespec
				      (or sig-hints
					  `(("Goal" :in-theory (disable open-true (,fn0) (,fn0-domain))
					     :do-not-induct t
					     :induct (,fn0 ,@args))
					    (and stable-under-simplificationp
						 '(:in-theory (current-theory :here))))))))

	     (fn-typethm      (and (not nx)
				   typespec
				   (defun::function-declaration-to-type-thm-hyps fn args
				     nil
				     typespec
				     (or sig-hints
					 `(("Goal" :in-theory (disable open-true (,fn) (,fn-domain))
					    :do-not-induct t
					    :induct (,fn ,@args))
					   (and stable-under-simplificationp
						'(:in-theory (current-theory :here))))))))

	     (fn-verifystmt   (and (not nx)
				   verify-guards
				   `((verify-guards
				      ,fn-monadic
				      ,@(if guard-hints `(:hints ,@guard-hints)
					  `(:hints (("Goal" :in-theory (disable open-true
										,fn-definition
										,fn0-definition
										,fn-domain
										,fn0-domain)
						     :expand (,fn0-domain ,@args)
						     :do-not-induct t)
						    (and stable-under-simplificationp
							 '(:in-theory (current-theory :here)))))))
				     (verify-guards ,fn-domain)
				     (verify-guards ,fn))))


	     )

	  `(encapsulate ()

	     (encapsulate
		 ()

	       (set-ignore-ok t)

	       (local (in-theory (theory 'defung-theory)))

	       ,@(indexed-defns fn ifn idom arb-index ftest fdefault fbase depth args arg-type-info
				stest default-value sbase sbody ec-call)

	       ,@(indexed-domain-lemmas
		  ifn idom arb-index depth d1 d2 args
		  ftest arb-index-thm mono-determ mono mono-contra idom-lower-bound)

	       ,@(min-index
		  idom depth d1 d2 args idom-lower-bound mono mono-contra
		  ifn-min-index natp-min-index idom-min-index
		  min-index-bound min-index-smallest)

	       ,@(mk-measure
		  fn0-measure fn0-measure-type ftest ifn-min-index arb-index ifn idom args depth d1 d2
		  idom-min-index min-index-bound min-index-smallest mono mono-contra
		  arb-index-thm fn0-measure-property fn0-measure-smallest
		  replace-index-by-fn0-measure replace-index-by-fn0-measure-2
		  replace-domain-index-by-fn0-measure
		  mono-determ)

	       ,@(real-defs
		  ifn fn fn0 fn0-domain depth args ftest fdefault fbase sbody
		  idom fn0-measure arb-index depth mono mono-contra
		  ifn-min-index idom-min-index
		  min-index-bound min-index-smallest
		  not-fn0-domain-implies-zero-fn0-measure fn0-measure-definition
		  fn0-domain-definition open-fn0-domain fn0-definition fn0-induction
		  fn0-induction-rule fn0-domain-true
		  fn0-induction-is-fn0-domain fn0-measure-property fn0-measure-smallest
		  replace-index-by-fn0-measure replace-index-by-fn0-measure-2
		  replace-domain-index-by-fn0-measure)

	       ,@(and (not nx)
		      (mk-monadic
		       fn-monadic fn fn-definition fn0 fn0-definition
		       fn-domain fn-domain-definition fn0-domain fn0-domain-definition
		       fn-measure fn-measure-type fn-measure-definition fn0-measure fn0-measure-definition
		       fn-induction fn-induction-rule fn-induction-is-fn-domain
		       open-fn-domain fn-domain-true
		       vars args arg-type-info ftest fbase default-value stobj-out tbody sbody ec-call
                       copy-args
		       ))

	       )

	     ,@fn0-typethm
	     ,@fn-typethm
	     ,@fn-verifystmt

	     )

	  ))))))))

(set-state-ok t)

;; stobjs can be listed as atoms or lists .. we want a list.
(defun smash-list-elements (list)
  (if (endp list) nil
    (let ((entry (car list)))
      (if (atom entry)
          (cons entry (smash-list-elements (cdr list)))
        (append entry (smash-list-elements (cdr list)))))))

(defun translate-extract (fn args body state)
  (declare (xargs :mode :program))
  (met ((doc decls body) (defun::decompose-defun-body body))
    (let ((stobj-list (cons 'acl2::state (smash-list-elements (defun::get-xarg-keys-from-decls :stobjs decls)))))
      (met ((err tbody signature) (acl2::pseudo-translate-defun fn stobj-list body (list (cons fn args)) (w state)))
      ;; equality substitutions kill us
      ;; - Added a "true-fn" patch (wrap-ifs) to avoid this
      (let ((tbody (wrap-ifs tbody)))
        (let ((event1 (defunger fn args doc decls body tbody signature))
              (event2 `(table::set ',(symbol-fns::suffix fn '-defung-body) ',tbody)))
          (let ((form `(encapsulate
                           ()
                         (set-verify-guards-eagerness 1)
                         ,event1
                         ,event2
                         )))
            (mv err form state))))))))

(defmacro def::ung (fn args &rest body)
  `(make-event (translate-extract ',fn ',args ',body state)))


;;
;; Support for proving the totality of a domain.
;;

(defun total-event-fn (fn args decls cond tbody)
  (met ((stest sbase sbody) (split-term-on-fset (list fn) tbody))
    (declare (ignore stest sbase))
    (met ((tname decls) (defun::extract-xarg-key-from-decls :totality-theorem decls))
      (let* ((ftest              (symbol-fns::suffix fn "-test"))
	     (fn-domain          (symbol-fns::suffix fn '-domain))
	     (fn-domain-is-total (symbol-fns::suffix fn-domain '-is-total))
	     (totality-theorem   (if (consp tname) (car tname) fn-domain-is-total))
	     (fn-total-induction (symbol-fns::suffix totality-theorem '-induction))
	     (fn-total-induction-body         (mk-domain-body fn fn-total-induction args sbody))
	     (fn-total-induction-is-fn-domain (symbol-fns::suffix fn-total-induction '-is- fn-domain))
	     )

	`(encapsulate ()
	   (local
	    (encapsulate
		()

	      (set-ignore-ok t)

	      (defun ,fn-total-induction ,args
		,@decls
		(if ,cond
		    (if (,ftest ,@args) t
		      ,fn-total-induction-body)
		  nil))

	      (defthm ,fn-total-induction-is-fn-domain
		(implies
		 ,cond
		 (equal (,fn-total-induction ,@args)
			(,fn-domain ,@args)))
		:hints (("Goal" :do-not-induct t
                         :induct (,fn-total-induction ,@args))))

	      ))

	   (defthm ,totality-theorem
	     (implies ,cond
		      (,fn-domain ,@args))
	     :hints (("Goal" :do-not-induct t
                      :induct (,fn-total-induction ,@args))))

	   )))))

(defun total-event (fn args body state)
  (declare (xargs :mode :program))
  (met ((doc decls cond) (defun::decompose-defun-body body))
    (declare (ignore doc))
    (let ((world (w state)))
      (let ((tbody (table::get (symbol-fns::suffix fn '-defung-body))))
	(let ((event (total-event-fn fn args decls cond tbody)))
	  (mv nil event state))))))

(defmacro def::total (fn args &rest body)
  `(make-event (total-event ',fn ',args ',body state)))

(local
(encapsulate
    ()

  (defthm true-listp-cdr
    (implies
     (true-listp x)
     (true-listp (cdr x)))
    :rule-classes (:type-prescription :rewrite))

  (def::ung rev3 (x)
    (declare (xargs :signature ((true-listp) true-listp)
		    :default-value x))
    (cond
     ((endp x) nil)
     ((endp (cdr x)) (list (car x)))
     (t
      ;; a.b*.c
      (let* ((b.c       (cdr x))
	     (c.rev-b   (rev3 b.c))
	     (rev-b     (cdr c.rev-b))
	     (b         (rev3 rev-b))
	     (a         (car x))
	     (a.b       (cons a b))
	     (rev-b.a   (rev3 a.b))
	     (c         (car c.rev-b))
	     (c.rev-b.a (cons c rev-b.a)))
	c.rev-b.a))))

  (defthm len-rev3
    (equal (len (rev3 x))
	   (len x)))

  (defthm consp-rev3
    (equal (consp (rev3 x))
	   (consp x)))

  ;; Here we prove that (rev3-domain x) is true whenever
  ;; (true-listp x) is true.
  (def::total rev3 (x)
    (declare (xargs :measure (len x)
		    :totality-theorem true-listp-rev3-totality))
    (true-listp x))

  ;; Now we prove that is it always total.
  (def::total rev3 (x)
    (declare (xargs :measure (len x)))
    t)

))
