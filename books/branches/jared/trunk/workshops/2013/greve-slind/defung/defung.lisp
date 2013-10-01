(in-package "DEFUNG")

(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/gensym/gensym" :dir :system)
(include-book "coi/generalize/generalize" :dir :system)
(INCLUDE-BOOK "ordinals/lexicographic-ordering" :dir :system)
(include-book "coi/util/table" :dir :system)
(include-book "map-ec-call")
;;
;; move to util ?
;;

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

(deftheory defung-theory
  (append '(unhide
	    return-last ; originally must-be-equal
	    the-check
	    true-fn-from-x
	    not-true-fn-from-not-x
	    true-fn-id
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
	    acl2::natp-listp
	    nfix
	    not
	    fix
	    max
	    synp
	    BOOLEANP-COMPOUND-RECOGNIZER
	    acl2::NATP-COMPOUND-RECOGNIZER
	    acl2::POSP-COMPOUND-RECOGNIZER	
	    acl2::ZP-COMPOUND-RECOGNIZER 
	    acl2::O-FINP-CR
	    acl2-count
	    acl2::UNICITY-OF-0
	    ;;CANCEL_PLUS-LESSP-CORRECT
	    acl2::O-FINP-<
	    acl2::O-P-DEF-O-FINP-1
	    acl2::<-+-NEGATIVE-0-1
	    acl2::INTEGER-ABS
	    acl2::NATP-FC-1
	    acl2::NATP-FC-2
	    acl2::POSP-FC-1
	    acl2::POSP-FC-2
	    acl2::NATP-POSP--1
	    combine-and-evaluate-constants
	    boolean-equal-reduction)
	  (theory 'minimal-theory)))

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

(defun indexed-defns (fn ifn idom index ftest fdefault fbase d args arg-type-info test default base body)
  (declare (type (satisfies not-quote-symbolp) fn ifn idom index ftest fbase)
	   (type symbol d)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies true-listp) arg-type-info)
	   (type (satisfies pseudo-termp) test base body)
	   )
  
  (let* ((default-value  default)
	 (ibody          (mk-ibody fn ifn `(1- ,d) args body))
	 (idom-body      (mk-idom-body ifn idom (cons d args) ibody))
	 (default-call  `(,fdefault ,@args))
	 (fbase-call    `(,fbase ,@args))
	 (test-call `(,ftest ,@args))
	 )
    `(
      
      (defun ,fbase ,args 
	,@arg-type-info
	(declare (ignorable ,@args))
	,base)

      (local (in-theory (disable ,fbase)))

      (defun ,fdefault ,args 
	,@arg-type-info
	(declare (ignorable ,@args))
	,default-value)

      (local (in-theory (disable ,fdefault)))

      (defun ,ftest ,args
	,@arg-type-info
	(declare (ignorable ,@args))
	,(normalize-ite nil test *t* *nil*))

      (local (in-theory (disable ,ftest)))

      (defund ,ifn (,d ,@args)
	(if (or (zp ,d) ,test-call) 
	    (if ,test-call ,fbase-call ,default-call)
	  ,ibody))
      
      (in-theory (disable (:type-prescription ,ifn)))

      (defund ,idom (,d ,@args) 
	(if (zp ,d) ,test-call
	  (if ,test-call t 
	    ,idom-body)))
      
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
                              ftest index-thm mono-determ mono idom-lower-bound)
  (declare (type (satisfies symbol-listp) args))
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
     :hints (("Goal" :in-theory (enable ,idom ,ifn ,ftest nat<=nat-induction)
	      :restrict ((,idom ,(bind-args-self args))
			 (,ifn  ,(bind-args-self args)))
	      :induct (list (nat<=nat-induction ,d1 ,d2)
			    (,idom ,d1 ,@args)))
	     (and stable-under-simplificationp
		  '(:expand ((,idom ,d1 ,@args)
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

   (defthmd ,idom-lower-bound
     (implies
      (and
       (,idom ,d1 ,@args)
       (,idom ,d2 ,@args)
       (not (,idom (1- ,d1) ,@args))
       (not (zp ,d1))
       (natp ,d2))
      (<= ,d1 ,d2))
     :hints (("Goal" :in-theory (enable ,mono)))
     :rule-classes (:forward-chaining))

   ))

;;---------------------------------------------------------------------------
;; Define and characterize the min-index
;;---------------------------------------------------------------------------

(defun min-index (idom d d1 d2 args idom-lower-bound mono
                  ifn-min-index natp-min-index idom-min-index
                  min-index-bound min-index-smallest)
  `(

    (defund ,ifn-min-index (,d ,@args)
      (if (zp ,d) 0
       (if (not (,idom ,d ,@args)) 0
         (if (not (,idom (1- ,d) ,@args)) ,d
	   (,ifn-min-index (1- ,d) ,@args)))))
    
    (defthm ,natp-min-index
      (natp (,ifn-min-index ,d ,@args))
      :hints (("Goal" :in-theory (enable ,ifn-min-index)))
      :rule-classes (:type-prescription))
    
    (defthmd ,idom-min-index
      (implies
       (,idom ,d ,@args)
       (,idom (,ifn-min-index ,d ,@args) ,@args))
      :hints (("Goal" :in-theory (enable ,ifn-min-index
					 ,mono
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
					 ,mono)
	       :induct (,ifn-min-index ,d1 ,@args))))
    )
  )

;;---------------------------------------------------------------------------
;; Introduce the measure function
;;---------------------------------------------------------------------------

(defun mk-measure (measure test ifn-min-index index ifn idom args d d1 d2
		   idom-min-index min-index-bound min-index-smallest mono
                   index-thm measure-property measure-smallest
                   replace-index-by-measure 
		   replace-domain-index-by-measure
		   mono-determ)
  (declare (ignorable test min-index-bound))
  `(

    (defund ,measure ,args (,ifn-min-index (,index ,@args) ,@args))
    
    (in-theory (disable (,measure)))

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
    
    (defthmd ,replace-index-by-measure
      (implies
       (and
	(,idom ,d ,@args)
	(syntaxp (not (or (equal ,d '(quote 0))
			  (and (eq (car ,d) ',measure)
			       (equal (cdr ,d) (list ,@args)))))))
       (equal (,ifn ,d ,@args)
	      (,ifn (,measure ,@args) ,@args)))
      :hints (("Goal" :do-not-induct t
	       :in-theory (enable ,idom ,ifn
				  ,measure-property ,measure-smallest)
	       :restrict ((,idom ,(bind-args-self args))
			  (,ifn  ,(bind-args-self args)))
	       :use (:instance ,mono-determ
			       (,d1 (,measure ,@args))
			       (,d2 ,d)))))

    (defthmd ,replace-domain-index-by-measure
      (implies
       (and
	(<= (,measure ,@args) ,d)
	(natp ,d)
	(syntaxp (not (or (equal ,d '(quote 0))
			  (and (eq (car ,d) ',measure)
			       (equal (cdr ,d) (list ,@args)))))))
       (equal (,idom ,d ,@args)
	      (,idom (,measure ,@args) ,@args)))
      :hints (("Goal" :in-theory (enable ,mono ,measure-property))))

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
	  (syntaxp (symbol-listp (list ,@xargs)))
	  (,fn-domain ,@args)
	  (,ftest ,@args))
	 (equal (,fn ,@xargs) ,base))
	:hints (("Goal" :expand (:with ,fn-definition (,fn ,@xargs)))))
      
      (local (in-theory (disable ,open-fn-base)))

      (defthm ,open-fn-induction
	(implies
	 (and
	  (syntaxp (symbol-listp (list ,@xargs)))
	  (,fn-domain ,@args)
	  (not (,ftest ,@args)))
	 (equal (,fn ,@xargs) ,xbody))
	:hints (("Goal" :expand (:with ,fn-definition (,fn ,@xargs)))))
      
      (local (in-theory (disable ,open-fn-induction)))
      
    )))

(defun real-defs (ifn fn fn0 fn0-domain depth args ftest fdefault fbase body
                  idom measure index d mono
                  ifn-min-index idom-min-index 
                  min-index-bound min-index-smallest
                  base-implies-zero-measure fn0-measure-definition
                  fn0-domain-definition open-fn0-domain fn0-definition induction-fn0
		  fn0-induction-rule 
                  induction-is-domain measure-property measure-smallest
                  replace-index-by-measure replace-domain-index-by-measure)

  (declare (type (satisfies not-quote-symbolp) ifn fn fn0 measure fn0-domain induction-fn0)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies pseudo-termp) body)
	   (ignore replace-domain-index-by-measure))
  
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
      
      (defund ,fn0 ,args (,ifn (,measure ,@args) ,@args))
      (defund ,fn0-domain ,args (,idom (,measure ,@args) ,@args))
      
      (in-theory (disable (,fn0) (,fn0-domain)))

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
				    )
		 :expand (,ifn-min-index (,index ,@args) ,@args))))
      
      (in-theory (disable ,idom-min-index ,min-index-bound ,min-index-smallest))
      
      ;; ==================================================================
      ;; The important theorems about the "top level" functions.
      ;; ==================================================================
      
      (defun ,measure-body-fn (,@args)
	,measure-body)

      (in-theory (disable (,measure-body-fn)))

      (defthmd ,fn0-measure-definition
	(equal (,measure ,@args)
	       (if (not (,fn0-domain ,@args)) 0 ,measure-body))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(rename-fn-args (map-fns fn measure args) calist)))
	:hints ((and stable-under-simplificationp
		     '(:in-theory (enable ,base-implies-zero-measure
					  )))
		(and stable-under-simplificationp
		     '(:expand (:free ,args (,ifn 0 ,@args))
		       :restrict ((,ifn  ,(bind-args-self args))
				  (,idom ,(bind-args-self args)))
		       :in-theory (enable natp-equal-reduction
					  ,ifn
					  ,fn0
					  ,idom
					  ;;,fdom
					  ,fn0-domain
					  ,measure-property
					  ,measure-smallest
					  ,mono
					  ,replace-index-by-measure
					   )))
		(and stable-under-simplificationp
		     '(:expand (,idom (,measure ,@args) ,@args)
			       :use ((:instance ,measure-property 
						(,d (,measure-body-fn ,@args))))))))
      
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
					  ,measure-property
					  ,measure-smallest
					  ,mono
					  )))
		(and stable-under-simplificationp
		     '(:expand (,idom (,measure ,@args) ,@args)
			       :use ((:instance ,measure-property 
						(,d (,measure-body-fn ,@args))))))))
      
      ;;(in-theory (disable (:definition ,fdom)))
      (in-theory (disable (:definition ,fn0-domain)))
      
      (defthm ,fn0-definition
	(equal (,fn0 ,@args)
	       (if (not (,fn0-domain ,@args)) (,fdefault ,@args) ,fn0-body))
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
					  ,mono
					  ;;,fdom
					  ,fn0-domain)))))
      
      (in-theory (disable (:definition ,fn0)))
      
      (defun ,induction-fn0 ,args
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

      
      (defthm ,open-fn0-domain
	(implies
	 (and
	  (syntaxp (symbol-listp (list ,@args)))
	  (not (,ftest ,@args)))
	 (equal (,fn0-domain ,@args) ,domain-xbody))
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

(defun fn-mbe (fn
	       fn-mbe fn-mbe-definition fn0 fn0-definition
	       fn-mbe-domain fn-mbe-domain-definition fn0-domain fn0-domain-definition
	       fn-mbe-measure fn-mbe-measure-definition fn0-measure fn0-measure-definition
	       fn-mbe-induction fn-mbe-induction-rule fn-mbe-induction-is-fn-mbe-domain
	       fn0-to-fn-mbe open-fn-mbe-domain
	       args arg-type-info ftest fbase fdefault tbody xbody ec-call
	       )
  (let* ((omit                    `(,fn-mbe ,fn-mbe-domain ,@ec-call))
	 (fn-mbe-exec-body        (rename-fn (map-fns fn fn-mbe args) tbody))
	 (fn-mbe-exec-body-ec     (if ec-call (map-ec-call-term fn-mbe-exec-body omit)
				    fn-mbe-exec-body))
	 (fn-mbe-xbody            (rename-fn (map-fns fn fn-mbe args) xbody))
	 (fn-mbe-tbody            `(if (,ftest ,@args) (,fbase ,@args) ,fn-mbe-xbody))
	 (fn-mbe-domain-exec-body (mk-domain-body fn-mbe fn-mbe-domain args fn-mbe-exec-body))
	 (fn-mbe-domain-exec-body-ec (if ec-call (map-ec-call-term fn-mbe-domain-exec-body omit)
				       fn-mbe-domain-exec-body))
	 (fn-mbe-domain-xbody     (mk-domain-body fn-mbe fn-mbe-domain args fn-mbe-xbody))
	 (fn-mbe-domain-tbody     `(if (,ftest ,@args) t ,fn-mbe-domain-xbody))
	 (fn-mbe-induction-xbody  (mk-domain-body fn-mbe fn-mbe-induction args fn-mbe-xbody))
	 (fn-mbe-induction-tbody  `(if (,ftest ,@args) t ,fn-mbe-induction-xbody))
	 (fn-mbe-measure-xbody    (mk-measure-body fn-mbe fn-mbe-measure args fn-mbe-xbody))
	 (fn-mbe-measure-tbody    `(if (,ftest ,@args) 0 ,fn-mbe-measure-xbody))
	 )
    
    `(
      (set-bogus-mutual-recursion-ok t)
      
      (mutual-recursion
       
       (defun ,fn-mbe ,args
	 ,@arg-type-info
	 (declare (xargs ;;:hints (("Goal" :expand (:with ,fn0-measure-definition (,fn0-measure ,@args))))
			 :guard (,fn-mbe-domain ,@args)
			 ;;:measure (,fn-measure ,@args)
			 ))
	 (mbe :logic (,fn0 ,@args)  :exec ,fn-mbe-exec-body-ec))
       
       (defun ,fn-mbe-domain ,args
	 ,@arg-type-info
	 (declare (xargs ;;:measure (,fn-measure ,@args)))
		   ))
	 (mbe :logic (,fn0-domain ,@args) :exec ,fn-mbe-domain-exec-body-ec))
       
       )
      
      (in-theory (disable (,fn-mbe) (,fn-mbe-domain)))

      (defthm ,fn0-to-fn-mbe
	(and (equal (,fn0 ,@args) (,fn-mbe ,@args))
	     (equal (,fn0-domain ,@args) (,fn-mbe-domain ,@args))))
      
      (local (in-theory (disable ,fn0-to-fn-mbe)))

      (defun ,fn-mbe-measure ,args
	(,fn0-measure ,@args))

      (in-theory (disable (,fn-mbe-measure)))

      (defthm ,fn-mbe-definition
	(equal (,fn-mbe ,@args) 
	       (if (,fn-mbe-domain ,@args)
		   ,fn-mbe-tbody
		 (,fdefault ,@args)))
	:hints (("Goal" :expand (:with ,fn0-definition (,fn0 ,@args))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-mbe args))))

      (local (in-theory (disable ,fn-mbe-definition)))
      
      (defthm ,fn-mbe-domain-definition
	(equal (,fn-mbe-domain ,@args)
	       ,fn-mbe-domain-tbody)
	:hints (("Goal" :expand (:with ,fn0-domain-definition (,fn0-domain ,@args))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-mbe-domain args))))
      
      (local (in-theory (disable ,fn-mbe-domain-definition)))

      (defthm ,fn-mbe-measure-definition
	(equal (,fn-mbe-measure ,@args)
	       (if (,fn-mbe-domain ,@args)
		   ,fn-mbe-measure-tbody
		 0))
	:hints (("Goal" :expand (:with ,fn0-measure-definition (,fn0-measure ,@args))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-mbe-measure args))))
      
      (local (in-theory (disable ,fn-mbe-measure-definition)))

      (in-theory (disable ,fn-mbe ,fn-mbe-domain ,fn-mbe-measure))

      (theory-invariant (incompatible (:definition ,fn-mbe)        (:rewrite ,fn0-to-fn-mbe)))
      (theory-invariant (incompatible (:definition ,fn-mbe-domain) (:rewrite ,fn0-to-fn-mbe)))

      (defun ,fn-mbe-induction ,args
	(declare (xargs :measure (,fn-mbe-measure ,@args)
			:hints (("Goal" :expand (:with ,fn-mbe-measure-definition
						       (,fn-mbe-measure ,@args))))))
	(if (,fn-mbe-domain ,@args)
	    ,fn-mbe-induction-tbody
	  nil))
      
     (defthm ,fn-mbe-induction-rule t
       :rule-classes ((:induction :corollary t
				  :pattern (,fn-mbe ,@args)
				  :scheme (,fn-mbe-induction ,@args))))
     
     (in-theory (disable (:definition ,fn-mbe-induction) (,fn-mbe-induction)))
     
     (defthm ,fn-mbe-induction-is-fn-mbe-domain
       (equal (,fn-mbe-induction ,@args) (,fn-mbe-domain ,@args))
       :hints (("goal" :induct (,fn-mbe-induction ,@args)
		:expand ((:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))
			 (,fn-mbe-induction ,@args)))))
     
     (defthm ,open-fn-mbe-domain
       (implies
	(and
	 (syntaxp (symbol-listp (list ,@args)))
	 (not (,ftest ,@args)))
	(equal (,fn-mbe-domain ,@args)
	       ,fn-mbe-domain-xbody))
       :hints (("Goal" :expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))
     
     (local (in-theory (disable ,open-fn-mbe-domain)))
	
     ,@(fn-openers fn-mbe fn-mbe-definition fn-mbe-domain args args ftest `(,fbase ,@args) fn-mbe-xbody)
     
     ,@(fn-openers fn-mbe-measure fn-mbe-measure-definition fn-mbe-domain args args ftest '0 fn-mbe-measure-xbody)

     )))

(defun fn-comp (fn 
	       fn-comp fn-mbe-domain fn-mbe fn-measure fn-mbe-definition  fn-mbe-measure-definition fn-mbe-domain-definition
	       fn-comp-induction fn-comp-induction-rule
	       fn-comp-to-fn-mbe fn-comp-definition
	       args depth arg-type-info ftest fbase fdefault default-expr tbody xbody
	       )
  (declare (ignorable fdefault))
  (let* ((fn-comp-xbody          (mk-ibody fn fn-comp `(1-<29> ,depth) args xbody))
	 (fn-comp-exec-body      (mk-ibody fn fn-comp `(1-<29> ,depth) args tbody))
	 (fn-comp-induction-body (mk-alt-body fn-comp fn-comp-induction (cons depth args) fn-comp-xbody))
	 )
    
    `(
      
      (defun ,fn-comp (,depth ,@args)
	,@arg-type-info
	(declare (type (unsigned-byte 29) ,depth))
	(cond
	 ((zp<29> ,depth) (if (,fn-mbe-domain ,@args) 
			      (,fn-mbe ,@args) 
			    ,default-expr))
	 (t (mbe :logic (if (,ftest ,@args) (,fbase ,@args)
			  ,fn-comp-xbody)
		 :exec ,fn-comp-exec-body))))

      (in-theory (disable (,fn-comp)))

      ;; An all-in-one induction strategy for fn-comp
      (defun ,fn-comp-induction (,depth ,@args)
	(declare (xargs :measure (llist (nfix ,depth) (,fn-measure ,@args))
			:well-founded-relation l<
			:hints (("Goal" :expand (:with ,fn-mbe-measure-definition (,fn-measure ,@args)))
				(and stable-under-simplificationp
				     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))))
	(cond
	 ((and (zp ,depth) (not (,fn-mbe-domain ,@args))) nil)
	 ((,ftest ,@args) t)
	 (t ,fn-comp-induction-body)))
      
      (defthm ,fn-comp-induction-rule t
	:rule-classes ((:induction :corollary t
				   :pattern (,fn-comp ,depth ,@args)
				   :scheme (,fn-comp-induction ,depth ,@args))))
      
      (in-theory (disable (:induction ,fn-comp)))
      
      (defthmd ,fn-comp-to-fn-mbe
	(implies
	 (,fn-mbe-domain ,@args)
	 (equal (,fn-comp ,depth ,@args)
		(,fn-mbe ,@args)))
	:hints (("Goal" :induct (,fn-comp ,depth ,@args)
		 :expand (:with ,fn-mbe-definition (,fn-mbe ,@args)))
		(and stable-under-simplificationp
		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))))))
      
      ;; A definition rule for fn-comp that better matches the induction
      (defthm ,fn-comp-definition
	(equal (,fn-comp ,depth ,@args)
	       (cond
		((and (zp ,depth) (not (,fn-mbe-domain ,@args))) (,fdefault ,@args))
		((,ftest ,@args) (,fbase ,@args))
		(t ,fn-comp-xbody)))
	:hints (("Goal" :in-theory (enable ,fdefault)
		 :expand ((:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))
			  (:with ,fn-mbe-definition (,fn-mbe ,@args)))))
	:rule-classes ((:definition
			:install-body t
			:controller-alist ,(default-calist fn-comp (cons depth args)))))
      
      (local (in-theory (disable ,fn-comp-definition)))
      (in-theory (disable ,fn-comp))
      
      )))
      
(defun fn-exec (fn 
		fn-exec fn-exec-definition fn-comp fn-comp-to-fn-mbe fn-mbe fn-mbe-definition
		fn-exec-domain fn-exec-domain-definition fn-mbe-domain fn-mbe-domain-definition
		fn-exec-measure fn-exec-measure-definition fn-mbe-measure fn-mbe-measure-definition
		fn-exec-induction fn-exec-induction-rule fn-exec-induction-is-fn-exec-domain
		use-total-induction open-fn-exec-domain
		args arg-type-info ftest fbase fdefault tbody xbody
		)
  (declare (ignorable fdefault tbody))
  (let* ((fn-exec-xbody            (rename-fn (map-fns fn fn-exec args) xbody))
	 (fn-exec-tbody            `(if (,ftest ,@args) (,fbase ,@args) ,fn-exec-xbody))
	 (fn-exec-domain-xbody     (mk-domain-body fn-exec fn-exec-domain args fn-exec-xbody))
	 (fn-exec-domain-tbody     `(if (,ftest ,@args) t ,fn-exec-domain-xbody))
	 (fn-exec-induction-xbody  (mk-domain-body fn-exec fn-exec-induction args fn-exec-xbody))
	 (fn-exec-induction-tbody  `(if (,ftest ,@args) t ,fn-exec-induction-xbody))
	 (fn-exec-measure-xbody    (mk-measure-body fn-exec fn-exec-measure args fn-exec-xbody))
	 (fn-exec-measure-tbody    `(if (,ftest ,@args) 0 ,fn-exec-measure-xbody))
	 )
    
    `(

      (defun ,fn-exec ,args
	,@arg-type-info
	(,fn-comp (big-depth-value) ,@args))
      
      (in-theory (disable (,fn-exec)))
      
      (defthmd ,use-total-induction
	(implies
	 (and
	  (syntaxp (symbol-listp (list ,@args)))
	  (syntaxp (not (cw "~% ** Note: ~p0 usually requires :otf-flg t **~%" ',use-total-induction))))
	 (equal (,fn-exec ,@args)
		(,fn-comp (big-depth-fn) ,@args)))
	:hints (("Goal" :in-theory (append '(,fn-exec big-depth-fn) (theory 'defung-theory)))))
      
      (defun ,fn-exec-domain (,@args)
	,@arg-type-info
	(,fn-mbe-domain ,@args))
      
      (in-theory (disable (,fn-exec-domain)))

      (defun ,fn-exec-measure (,@args)
	(,fn-mbe-measure ,@args))

      (in-theory (disable (,fn-exec-measure)))

      (defthm ,fn-exec-definition
	(equal (,fn-exec ,@args) 
	       (if (,fn-exec-domain ,@args)
		   ,fn-exec-tbody
		 (,fn-comp (big-depth-value) ,@args)))
	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
		 :expand (:with ,fn-mbe-definition (,fn-mbe ,@args)))
		(and stable-under-simplificationp
		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-exec args))))
      
      (local (in-theory (disable ,fn-exec-definition)))

      (defthm ,fn-exec-domain-definition
	(equal (,fn-exec-domain ,@args)
	       ,fn-exec-domain-tbody)
	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
		 :expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-exec-domain args))))
      
      (local (in-theory (disable ,fn-exec-domain-definition)))

      (defthm ,fn-exec-measure-definition
	(equal (,fn-exec-measure ,@args)
	       (if (,fn-exec-domain ,@args)
		   ,fn-exec-measure-tbody
		 0))
	:hints (("Goal" :in-theory (enable ,fn-comp-to-fn-mbe)
		 :expand (:with ,fn-mbe-measure-definition (,fn-mbe-measure ,@args)))
		(and stable-under-simplificationp
		     '(:expand (:with ,fn-mbe-domain-definition (,fn-mbe-domain ,@args)))))
	:rule-classes ((:definition 
			:install-body t
			:controller-alist ,(default-calist fn-exec-measure args))))
      
      (local (in-theory (disable ,fn-exec-measure-definition)))

      (in-theory (disable ,fn-exec ,fn-exec-domain ,fn-exec-measure))

      (defun ,fn-exec-induction ,args
	(declare (xargs :measure (,fn-exec-measure ,@args)
			:hints (("Goal" :expand (:with ,fn-exec-measure-definition
						       (,fn-exec-measure ,@args))))))
	(if (,fn-exec-domain ,@args)
	    ,fn-exec-induction-tbody
	  nil))
      
     (defthm ,fn-exec-induction-rule t
       :rule-classes ((:induction :corollary t
				  :pattern (,fn-exec ,@args)
				  :scheme (,fn-exec-induction ,@args))))
     
     (in-theory (disable (:definition ,fn-exec-induction) (,fn-exec-induction)))
     
     (defthm ,fn-exec-induction-is-fn-exec-domain
       (equal (,fn-exec-induction ,@args) (,fn-exec-domain ,@args))
       :hints (("goal" :induct (,fn-exec-induction ,@args)
		:expand ((:with ,fn-exec-domain-definition (,fn-exec-domain ,@args))
			 (,fn-exec-induction ,@args)))))
     
     (defthm ,open-fn-exec-domain
       (implies
	(and
	 (syntaxp (symbol-listp (list ,@args)))
	 (not (,ftest ,@args)))
	(equal (,fn-exec-domain ,@args)
	       ,fn-exec-domain-xbody))
       :hints (("Goal" :expand (:with ,fn-exec-domain-definition (,fn-exec-domain ,@args)))))
     
     (local (in-theory (disable ,open-fn-exec-domain)))
	

     ,@(fn-openers fn-exec fn-exec-definition fn-exec-domain args args ftest `(,fbase ,@args) fn-exec-xbody)
     
     ,@(fn-openers fn-exec-measure fn-exec-measure-definition fn-exec-domain args args ftest '0 fn-exec-measure-xbody)

     )))

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

(defun defunger (fn args doc decls body tbody)
  (declare (type (satisfies not-quote-symbolp) fn)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies pseudo-termp) tbody)
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

      (met ((typespec signature sig-hints decls) (defun::extract-function-declaration decls))
      (met ((default-value decls) (defun::extract-xarg-key-from-decls :default-value decls))
      (met ((nx decls) (defun::extract-xarg-key-from-decls :non-executable decls))
      (met ((no-ec-call decls) (defun::extract-xarg-key-from-decls :no-ec-call decls))
      (met ((indexed-execution decls)  (defun::extract-xarg-key-from-decls :indexed-execution decls))
      (met ((wrapper-macro decls) (defun::extract-xarg-key-from-decls :wrapper-macro decls))
	
	
	(let* 
	    (
	     (default-value  (and (consp default-value)
				  (let ((expr (car default-value)))
				    (if (not expr) *nil* expr))))
	     (default-value   (or default-value sbase))
	     (verify-guards   (defun::get-xarg-keys-from-decls :verify-guards decls))
	     (xarg-guards     (defun::get-xarg-keys-from-decls :guard decls))
	     (guard-hints     (defun::get-xarg-keys-from-decls :guard-hints decls))
	     (type-decls      (defun::get-type-declarations-from-decls decls))

	     (nx              (and (consp nx) (car nx)))

	     (typeinfo        (or signature verify-guards xarg-guards type-decls))

	     (verify-guards   (and (not nx) (not (defun::contains-nil verify-guards))))
	     
	     (ec-call         (and (not nx) (not typeinfo)
				   (append `(and defung::true) (and (consp no-ec-call) (car no-ec-call)))))
	     
	     (indexed-execution (and (not nx) (if (and (consp indexed-execution) (not (car indexed-execution))) nil
						typeinfo)))
				  
	     (wrapper-macro     (and (not nx) (not indexed-execution) (consp wrapper-macro) (car wrapper-macro)))
	     

	     (body-symbols (symbols-of tbody nil))
	     (depth (gensym::gensym 'd body-symbols))
	     (vars (cons depth body-symbols))
	     (d1 (gensym::gensym 'd1 vars))
	     (d2 (gensym::gensym 'd2 (cons d1 vars)))

	     (fname  fn)

	     (fbase    (symbol-fns::suffix fname "-base"))
	     (ftest    (symbol-fns::suffix fname "-test"))
	     (fdefault (symbol-fns::suffix fname "-default"))

	     ;; Indexed Functions

	     (iname      (symbol-fns::prefix "i" fname))
	     (ifn        (symbol-fns::suffix iname))
	     (idom       (symbol-fns::suffix iname "-DOMAIN"))
	     (indexx     (symbol-fns::suffix iname '-index))
	     (arb-index  (symbol-fns::prefix "ARB-" indexx))

	     (arb-index-thm      (symbol-fns::suffix arb-index "-THM"))
	     (mono-determ        (symbol-fns::suffix iname "-MONO-DETERM"))
	     (mono               (symbol-fns::suffix iname "-DOMAIN-MONOTONE"))
	     (idom-lower-bound   (symbol-fns::suffix iname "-DOMAIN-LOWER-BOUND"))
	     (ifn-min-index      (symbol-fns::suffix iname "-MIN-INDEX"))
	     (natp-min-index     (symbol-fns::prefix "NATP-" ifn-min-index))
	     (idom-min-index     (symbol-fns::suffix iname "-DOMAIN-MIN-INDEX"))
	     (min-index-bound    (symbol-fns::suffix iname "-MIN-INDEX-BOUND"))
	     (min-index-smallest (symbol-fns::suffix iname "-MIN-INDEX-SMALLEST"))

	     ;; FN0 (in terms of indexed function)

	     (f0name               (if nx fname (symbol-fns::suffix fname "-0")))
	     (fn0-measure          (symbol-fns::suffix f0name "-MEASURE"))
	     (fn0-measure-property (symbol-fns::suffix fn0-measure "-PROPERTY"))
	     (fn0-measure-smallest (symbol-fns::suffix fn0-measure "-SMALLEST"))
	     (replace-index-by-fn0-measure        (symbol-fns::prefix "REPLACE-" arb-index "-BY-" fn0-measure))
	     (replace-domain-index-by-fn0-measure (symbol-fns::prefix "REPLACE-" iname "-DOMAIN-INDEX-BY-" fn0-measure))

	     (fn0            f0name)
	     (fn0-definition (symbol-fns::suffix f0name "-DEFINITION"))
	     (fn0-measure-definition (symbol-fns::suffix fn0-measure "-DEFINITION"))
	     (fn0-domain     (symbol-fns::suffix fn0 "-DOMAIN"))
	     (open-fn0-domain (symbol-fns::prefix 'open- fn0-domain))
	     (fn0-domain-definition  (symbol-fns::suffix fn0 "-DOMAIN-DEFINITION"))
	     (not-fn0-domain (symbol-fns::prefix 'not- fn0-domain))
	     (not-fn0-domain-implies-zero-fn0-measure (symbol-fns::suffix not-fn0-domain '-implies-zero- fn0-measure))
	     (fn0-induction (symbol-fns::suffix f0name "-INDUCTION"))
	     (fn0-induction-rule (symbol-fns::suffix f0name "-INDUCTION-RULE"))
	     (fn0-induction-is-fn0-domain (symbol-fns::suffix f0name "-INDUCTION-IS-" f0name "-DOMAIN"))
	     
	     ;; fn-mbe (mutual recursion) definitions
	     
	     (fn-mbe                      (if indexed-execution (symbol-fns::suffix fname "-MBE") fname))
	     (fn-mbe-domain               (symbol-fns::suffix fn-mbe "-DOMAIN"))
	     (open-fn-mbe-domain          (symbol-fns::prefix 'open- fn-mbe-domain))
	     (fn-mbe-definition           (symbol-fns::suffix fn-mbe "-DEFINITION"))
	     (fn-mbe-domain-definition    (symbol-fns::suffix fn-mbe-domain "-DEFINITION"))
	     (fn-mbe-measure              (symbol-fns::suffix fn-mbe "-MEASURE"))
	     (fn-mbe-measure-definition   (symbol-fns::suffix fn-mbe-measure "-DEFINITION"))
	     (fn-mbe-induction                  (symbol-fns::suffix fn-mbe "-INDUCTION"))
	     (fn-mbe-induction-rule             (symbol-fns::suffix fn-mbe-induction "-RULE"))
	     (fn-mbe-induction-is-fn-mbe-domain (symbol-fns::suffix fn-mbe-induction '-is- fn-mbe-domain))
	     
	     (fn0-to-fn-mbe               (symbol-fns::suffix fn0 '-to- fn-mbe))

	     ;; fn-comp (Iterative computation) definitions
	     
	     (fn-comp                (symbol-fns::suffix fname "-COMPUTE"))
	     (fn-comp-definition     (symbol-fns::suffix fn-comp '-definition))
	     (fn-comp-induction      (symbol-fns::suffix fn-comp '-induction))
	     (fn-comp-induction-rule (symbol-fns::suffix fn-comp-induction '-rule))

	     (fn-comp-to-fn-mbe      (symbol-fns::suffix fn-comp '-to- fn-mbe))

	     ;; fn-exec (top level executable) definitions

	     (fn-exec                    fn)
	     (fn-exec-definition         (symbol-fns::suffix fn-exec '-definition))
	     (fn-exec-domain             (symbol-fns::suffix fn-exec '-domain))
	     (open-fn-exec-domain        (symbol-fns::prefix 'open- fn-exec-domain))
	     (fn-exec-domain-definition  (symbol-fns::suffix fn-exec-domain '-definition))

	     (fn-exec-measure            (symbol-fns::suffix fn-exec '-measure))
	     (fn-exec-measure-definition (symbol-fns::suffix fn-exec-measure '-definition))
	     (fn-exec-induction          (symbol-fns::suffix fn-exec '-induction))
	     (fn-exec-induction-rule     (symbol-fns::suffix fn-exec-induction '-rule))
	     (fn-exec-induction-is-fn-exec-domain
	      (symbol-fns::suffix fn-exec-induction '-is- fn-exec-domain))

	     (fn-total-induction      (symbol-fns::suffix fn '-total-induction))
	     (use-total-induction     (symbol-fns::prefix 'use- fn-total-induction))
	     
	     (decls           (if signature 
				  (cons `(declare 
					  (xargs :guard 
						 ,(defun::function-declaration-to-guard args signature))) decls)
				decls))
	     (typespec        (or typespec signature))
	     (inhibited-decls (cons `(declare (xargs :verify-guards nil)) decls))
	     (arg-type-info   inhibited-decls)
	     
	     (fn0-typethm      (and typespec
				    (defun::function-declaration-to-type-thm-hyps fn0 args
				      nil
				      typespec 
				      (or sig-hints
					  `(("Goal" ,@(and (not nx) `(:in-theory (disable true-fn ,fn0-to-fn-mbe)))
					     :do-not-induct t :induct (,fn0 ,@args))
					    (and stable-under-simplificationp
						 '(:in-theory (current-theory :here))))))))
	     
	     (fn-mbe-typethm  (and (not nx)
				   typespec
				   (defun::function-declaration-to-type-thm-hyps fn-mbe args 
				     (list `(,fn-mbe-domain ,@args))
				     typespec 
				     (or sig-hints
					 `(("Goal" :do-not-induct t :induct (,fn-mbe ,@args)
					    :in-theory (disable true-fn))
					   (and stable-under-simplificationp
						'(:in-theory (current-theory :here))))))))
	     
	     (fn-comp-typethm  (and indexed-execution
				    typespec
				    (defun::function-declaration-to-type-thm fn-comp 
				      (cons depth args) (add-arg-type t typespec) 
				      (or sig-hints
					  `(("Goal" :do-not-induct t :induct (,fn-comp ,depth ,@args)
					     :in-theory (disable true-fn))
					    (and stable-under-simplificationp
						 '(:in-theory (current-theory :here))))))))
	     
	     (fn-exec-typethm  (and indexed-execution
				    typespec
				    (defun::function-declaration-to-type-thm fn-exec args typespec 
				      `(("Goal" :in-theory (enable ,fn-exec))))))
	     
	     (fn-mbe-verifystmt  (and (not nx) 
				      verify-guards
				      `((verify-guards 
					 ,fn-mbe
					 ,@(or (and guard-hints `(:hints ,@guard-hints))
					       `(:hints (("Goal" :in-theory (disable true-fn))
							 (and stable-under-simplificationp
							      '(:in-theory (current-theory :here)))))))
					(in-theory (enable (,fn-mbe) (,fn-mbe-domain) (,fn-mbe-measure))))))
	     
	     (fn-comp-verifystmt (and indexed-execution
				      verify-guards 
				      `((verify-guards
					 ,fn-comp
					 ,@(or (and guard-hints `(:hints ,@guard-hints))
					       `(:hints (("Goal" :in-theory (disable true-fn))
							 (and stable-under-simplificationp
							      '(:in-theory (enable true-fn ,fn-comp-to-fn-mbe)))))))
					(in-theory (enable (,fn-comp))))))
	     
	     (fn-exec-verifystmt   (and indexed-execution
					verify-guards 
					`((verify-guards 
					   ,fn-exec
					   ,@(and guard-hints `(:hints ,@guard-hints)))
					  (in-theory (enable (,fn-exec) (,fn-exec-domain) (,fn-exec-measure))))))
	     
	     )

	  `(encapsulate ()
	     
	     (encapsulate
		 ()
	       
	       (set-ignore-ok t)

	       (local (in-theory (theory 'defung-theory)))
	       
	       (local (in-theory (disable true-fn)))

	       ,@(indexed-defns fn ifn idom arb-index ftest fdefault fbase depth args arg-type-info 
				stest default-value sbase sbody)
	       
	       ,@(indexed-domain-lemmas 
		  ifn idom arb-index depth d1 d2 args
		  ftest arb-index-thm mono-determ mono idom-lower-bound)
	       
	       ,@(min-index 
		  idom depth d1 d2 args idom-lower-bound mono
		  ifn-min-index natp-min-index idom-min-index
		  min-index-bound min-index-smallest)
	       
	       ,@(mk-measure 
		  fn0-measure ftest ifn-min-index arb-index ifn idom args depth d1 d2 
		  idom-min-index min-index-bound min-index-smallest mono
		  arb-index-thm fn0-measure-property fn0-measure-smallest
		  replace-index-by-fn0-measure 
		  replace-domain-index-by-fn0-measure 
		  mono-determ)
	       
	       ,@(real-defs 
		  ifn fn fn0 fn0-domain depth args ftest fdefault fbase sbody 
		  idom fn0-measure arb-index depth mono
		  ifn-min-index idom-min-index 
		  min-index-bound min-index-smallest
		  not-fn0-domain-implies-zero-fn0-measure fn0-measure-definition
		  fn0-domain-definition open-fn0-domain fn0-definition fn0-induction
		  fn0-induction-rule
		  fn0-induction-is-fn0-domain fn0-measure-property fn0-measure-smallest
		  replace-index-by-fn0-measure replace-domain-index-by-fn0-measure)
	       
	       ,@(and (not nx)
		      (fn-mbe fn 
			      fn-mbe fn-mbe-definition fn0 fn0-definition
			      fn-mbe-domain fn-mbe-domain-definition fn0-domain fn0-domain-definition
			      fn-mbe-measure fn-mbe-measure-definition fn0-measure fn0-measure-definition
			      fn-mbe-induction fn-mbe-induction-rule fn-mbe-induction-is-fn-mbe-domain
			      fn0-to-fn-mbe open-fn-mbe-domain
			      args arg-type-info ftest fbase fdefault tbody sbody ec-call)
		      )
	       
	       ,@(and indexed-execution
		      `(
			,@(fn-comp fn
				   fn-comp fn-mbe-domain fn-mbe fn-mbe-measure fn-mbe-definition fn-mbe-measure-definition fn-mbe-domain-definition
				   fn-comp-induction fn-comp-induction-rule
				   fn-comp-to-fn-mbe fn-comp-definition
				   args depth arg-type-info ftest fbase fdefault default-value tbody sbody
				   )
			
			,@(fn-exec fn
				   fn-exec fn-exec-definition fn-comp fn-comp-to-fn-mbe fn-mbe fn-mbe-definition
				   fn-exec-domain fn-exec-domain-definition fn-mbe-domain fn-mbe-domain-definition
				   fn-exec-measure fn-exec-measure-definition fn-mbe-measure fn-mbe-measure-definition 
				   fn-exec-induction fn-exec-induction-rule fn-exec-induction-is-fn-exec-domain
				   use-total-induction open-fn-exec-domain
				   args arg-type-info ftest fbase fdefault tbody sbody
				   )
			
			))

	       )
	     
	     ,@fn0-typethm

	     (local (in-theory (disable generalize-big-depth-fn)))
	     
	     ,@fn-mbe-typethm
	     ,@fn-comp-typethm
	     ,@fn-exec-typethm
	     ,@fn-mbe-verifystmt
	     ,@fn-comp-verifystmt
	     ,@fn-exec-verifystmt
	     
	     ,@(and wrapper-macro
		    (let ((bind-args (bind-args args)))
		      `((defmacro ,wrapper-macro ,args
			  `(let ,,bind-args
			     (if (,',(symbol-fns::suffix fname '-domain) ,',args)
				 (,',fname ,',args)
			       ,',default-value))))))
		    
	     )
	  
	  )))))))))
  
(set-state-ok t)

(defun translate-extract (fn args body state)
  (declare (xargs :mode :program))
  (met ((doc decls body) (defun::decompose-defun-body body))
    (met ((err tbody) (acl2::pseudo-translate body (list (cons fn args)) (w state)))
      ;; equality substitutions kill us 
      ;; - Added a "true-fn" patch (wrap-ifs) to avoid this
      (let ((tbody (wrap-ifs tbody)))
	(let ((event1 (defunger fn args doc decls body tbody))
	      (event2 `(table::set ',(symbol-fns::suffix fn '-defung-body) ',tbody)))
	  (let ((form `(encapsulate
			   ()
			 ,event1
			 ,event2
			 )))
	    (mv err form state)))))))

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
		:hints (("Goal" :induct (,fn-total-induction ,@args))))
	      
	      ))
	   
	   (defthm ,totality-theorem
	     (implies ,cond
		      (,fn-domain ,@args))
	     :hints (("Goal" :induct (,fn-total-induction ,@args))))
	   
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
	   (len x))
    :otf-flg t
    :hints (("Goal" :in-theory (enable use-rev3-total-induction))))
  
  (defthm consp-rev3
    (equal (consp (rev3 x))
	   (consp x))
    :otf-flg t
    :hints (("Goal" :in-theory (enable use-rev3-total-induction))))
  
  
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