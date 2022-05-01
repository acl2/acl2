; asymptotic-analysis-support.lsp                     William D. Young

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
; (include-book "arithmetic/top-with-meta" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(in-theory (disable simplify-products-gather-exponents-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                      ASYMPTOTIC COMPLEXITY                       ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is an attempt to model simple asymptotic analysis using the 
;; simple while language as the programming language. 

; (defun apt () (accumulated-persistence t))
; (defun apn () (accumulated-persistence nil))
; (defun sap () (show-accumulated-persistence))
; 
; (define-pc-macro ls ()
;   (mv nil 's-prop state))
; 
; (define-pc-macro sp ()
;   (mv nil 's-prop state))
; 
; (define-pc-macro sr1 ()
;   (mv nil '(show-rewrites 1) state))
; 
; (define-pc-macro sr2 ()
;   (mv nil '(show-rewrites 2) state))
; 
; (define-pc-macro sr3 ()
;   (mv nil '(show-rewrites 3) state))
; 
; (define-pc-macro sr4 ()
;   (mv nil '(show-rewrites 4) state))
; 
; (define-pc-macro sr5 ()
;   (mv nil '(show-rewrites 5) state))
; 
; (define-pc-macro sr6 ()
;   (mv nil '(show-rewrites 6) state))
; 
; (define-pc-macro sr7 ()
;   (mv nil '(show-rewrites 7) state))
; 
; (define-pc-macro sr8 ()
;   (mv nil '(show-rewrites 8) state))
; 
; (define-pc-macro promtoe ()
;   (mv nil 'promote state))
; 
; (define-pc-macro push ()
;   (mv nil '(= & t t) state))
; 
; (define-pc-macro 1p ()
;   (mv nil '(do-all 1 p) state))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                          PRELIMINARIES                           ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (defun here () t)

;; SOME ELEMENTARY LEMMAS

(defthm member-equal-append
  (iff (member-equal x (append y z))
       (or (member-equal x y)
	   (member-equal x z))))

(defthm member-equal-cons
  (iff (member-equal x (cons y z))
       (or (equal x y)
	   (member-equal x z))))

(defthm has-member-non-empty
  (implies (member-equal x lst)
	   (and (equal (< 0 (len lst)) t)
		(equal (< (1- (len lst)) 0) nil))))

(defthm non-empty-len
  (implies (and (true-listp lst)
		lst)
	   (and (equal (< (1- (len lst)) 0) nil)
		(equal (< 0 (len lst)) t))))

(defthm put-assoc-equal-twice
  (equal (put-assoc-equal key val1 (put-assoc-equal key val2 vars))
	 (put-assoc-equal key val1 vars)))

(defthm assoc-equal-put-assoc-equal1
  (implies (not (equal key1 key2))
	   (equal (assoc-equal key1 (put-assoc-equal key2 val alist))
		  (assoc-equal key1 alist))))

(defthm assoc-equal-put-assoc-equal2
  (equal (cdr (assoc-equal key (put-assoc-equal key val alist)))
	 val))

(defthmd not-member-null-nthcdr
  (implies (and (<= (len lst) n)
		(integerp n))
	   (not (member-equal x (nthcdr n lst)))))

(defthm not-member-empty-list
  (implies (equal (len lst) 0)
	   (not (member-equal x lst))))

(defthm member-nthcdr-cdr
  (implies (member-equal x (nthcdr i (cdr lst)))
	   (member-equal x (nthcdr i lst))))

(defthm member-nthcdr-kludge
  (implies (and (not (equal (nth i lst) x))
		(not (member-equal x (nthcdr i (cdr lst)))))
	   (not (member-equal x (nthcdr i lst))))
  :hints (("Goal" :in-theory (enable  not-member-null-nthcdr))))

(defthm nth-nthcdr-kludge
  (implies (and (equal (1+ i) (len lst))
		(not (equal (nth i lst) x)))
	   (not (member-equal x (nthcdr i lst)))))

(defthm member-equal-nthcdr
  (implies (and (equal (nth i lst) x)
		x)
	   (member-equal x (nthcdr i lst))))

(defthm nthcdr-bound
  (implies (and (integerp low)
		(true-listp lst)
		(not (< low (len lst))))
	   (equal (nthcdr low lst)
		  nil)))

;; DEFINEDP

(defun definedp (name alist)
  (if (endp alist)
      nil
    (or (equal name (caar alist))
	(definedp name (cdr alist)))))

(defthm definedp-put-assoc-equal
  (definedp key (put-assoc-equal key val vars)))

(defthm definedp-key
  (implies (not (equal key1 key2))
	   (equal (definedp key1 (put-assoc key2 val vars))
		  (definedp key1 vars))))

(defthm assoc-equal-preserves-definep
  (implies (definedp v alist)
	   (definedp v (put-assoc x val alist))))

(defthmd less-equal-transitive
  (implies (and (<= x y)
		(<= y z))
	   (<= x z)))

;; FLR

;; This keeps floor from being rewritten into some horrible
;; expression.   Otherwise flr and floor are identical.

(defund flr (x y)
  (floor x y))

(defthm flr-half-lemma
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z)
		(< x z)
		(< y z))
	   (< (flr (+ x y) 2) z))
  :hints (("Goal" :in-theory (enable flr)))
  :rule-classes (:rewrite :linear))

(defthm flr-posp
  (implies (and (<= 0 x)
	        (<= x y)
		)
	   (not (< (flr (+ x y) 2) 0)))
  :hints (("Goal" :in-theory (enable flr)))
  :rule-classes (:rewrite :linear))

(defthm flr-lessp
  (implies (and (natp x)
		(natp y)
		(< x y))
	   (< (flr (+ x y) 2) y))
  :hints (("Goal" :in-theory (enable flr)))
  :rule-classes (:rewrite :linear))

(defthm flr-less-equal
  (implies (and (natp x)
		(natp y)
		(<= x y))
	   (<= (flr (+ x y) 2) y))
  :hints (("Goal" :in-theory (enable flr)))
  :rule-classes (:rewrite :linear))

;; STORE and LOOKUP

(defun lookup (v alist)
  (cdr (assoc-equal v alist)))

(defun store (v val alist)
  (put-assoc-equal v val alist))

(defthm lookup-store
  (equal (lookup key1 (store key2 val alist))
	 (if (equal key1 key2)
	     val
	   (lookup key1 alist))))

(defthm store-store
  (equal (store i x (store i y vars))
	 (store i x vars)))

(defthm store-store2
  (implies (not (equal key1 key2))
	   (equal (store key1 val1 (store key2 val2 (store key1 val3 vars)))
		  (store key2 val2 (store key1 val1 vars))))
  :hints (("Goal" :in-theory (enable store))))

(defthmd re-order-store
  (implies (and (syntaxp (lexorder key1 key2))
		(not (equal key1 key2))
		(or (definedp key1 vars)
		    (definedp key2 vars)))
	   (equal (store key2 val2 (store key1 val1 vars))
		  (store key1 val1 (store key2 val2 vars))))
  :hints (("Goal" :in-theory (enable store))))

(defthm store-store3
  (implies (and (not (equal key1 key2))
		(not (equal key2 key3))
		(not (equal key1 key3)))
	   (equal (store key1 val1 (store key2 val2 (store key3 val3 (store key1 val4 vars))))
		  (store key2 val2 (store key3 val3 (store key1 val1 vars)))))
  :hints (("goal" :instructions (:promote (:dv 1) (:rewrite re-order-store)
					  (:dv 3) (:rewrite store-store2)
					  :top :s :bash))))

(defthm store-preserves-definep
  (implies (definedp v alist)
	   (definedp v (store x val alist))))

(defthm lookup-definedp
  (implies (lookup v vars)
	   (definedp v vars)))

(defthm lookup-numberp-definedp
  (implies (acl2-numberp (lookup v vars))
	   (definedp v vars)))
;  :hints (("Goal" :in-theory (enable lookup))))

(defthm non-zero-len-definedp
  (implies (< 0 (len (lookup x vars)))
	   (definedp x vars)))

(defthm store-defines
  (definedp key (store key val alist)))

(defthm lookup-store-unchanged
  (implies (and (equal (lookup i vars) x)
		x)
	   (equal (store i x vars)
		  vars)))

(in-theory (disable lookup store))


;; NUMBER-LISTP

(defun number-listp (lst)
  (if (endp lst)
      (equal lst nil)
    (and (acl2-numberp (car lst))
	 (number-listp (cdr lst)))))

(defthm nth-in-number-listp
  (implies (and (natp i)
		(< i (len lst))
		(number-listp lst))
	   (acl2-numberp (nth i lst))))

(defthm number-listp-true-listp
  (implies (number-listp lst)
	   (true-listp lst)))

;; LENP

(defun lenp (x n)
  (and (true-listp x)
       (equal (len x) n)))

(defthm len-lessp-not-zp
  (implies (and (< (len lst) count)
		(integerp count))
	   (not (zp count))))

(in-theory (disable lenp))

;; VARIABLES and LITERALS

;; The names opr, arg1, arg2, arg3 etc are used in the arithmetic library.
;; I could use operator, param1, ... instead.

(defmacro operator (x) `(car ,x))
(defmacro paramlist (x) `(cdr ,x))
(defmacro param1 (x) `(cadr ,x))
(defmacro param2 (x) `(caddr ,x))
(defmacro param3 (x) `(cadddr ,x))

;; For this time around, let's assume that the only values in the var-alist
;; are numbers and symbols, or lists of those. 

;; >> Note that for a literal int, we need (lit . n) rather than (lit n). 
;;    Otherwise, we probably can't have a list of just n.

(defun literalp (x)
  (or (acl2-numberp x)
      (and (symbolp x)
	   (not (null x)))))

(defun literal-listp (lst)
  (if (endp lst)
      (equal lst nil)
    (and (literalp (car lst))
	 (literal-listp (cdr lst)))))

(defthm literal-listp-true-listp
  (implies (literal-listp lst)
	   (true-listp lst)))

(defun var-namep (x)
  (and (symbolp x)
       (not (null x))
       ;; I added this because 'result is used
       ;; in the var-alist for special purposes.
       (not (equal x 'result))))

(defun varp (x)
  ;; This defines the syntax of a variable, 
  ;; but not whether it's defined. 
  (and (lenp x 2)
       (equal (operator x) 'var)
       (var-namep (param1 x))))
  
; (defun list-varp (lst vars)
;   (let ((lstval (lookup (param1 lst) vars)))
;     (and (varp lst)
; 	 (true-listp lstval)
; 	 lstval)))

(defun definedp-varp (x vars)
  ;; x has form (var v), v is defined in vars,
  ;; and the value is not null.
  (let ((val (lookup (param1 x) vars)))
    (and (varp x) 
	 val)))

;; VALUE

(defthm varp-not-result
  (implies (varp x)
	   (not (equal (param1 x) 'result))))

(defun valuep (x)
  (or (literalp x)
      (literal-listp x)))

;; VAR-ALISTP

(defun var-alist-pairp (x)
  ;; Recognizes a pair of form (var . value).
  ;; Even though a var has form (var x), we only 
  ;; include the x as a key. 
  (and (consp x)
       (var-namep (car x))
       (valuep (cdr x))
       ))

(defun var-alistp (alist)
  ;; Recognizes a true-list of pairs where each 
  ;; pair is a cons with a var-namep as key, and
  ;; each values is either a constant or a list of 
  ;; constants. 
  (if (endp alist)
      (equal alist nil)
    (and (var-alist-pairp (car alist))
	 (var-alistp (cdr alist)))))

(defthm var-alistp-var-valuep
  (implies (and (var-alistp vars)
		(definedp v vars))
	   (valuep (lookup v vars)))
  :hints (("Goal" :in-theory (enable lookup))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                      EXPRESSION EVALUATION                       ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We define a simple expression language that has (at this point)
;; only integer and Boolean expressions. 

;; This recognizer is never used.  I build all of the tests into
;; the evaluation function.  If any syntactic check ever fails, then
;; the evaluation fails and returns an error.  

(defund exprp (x vars)
  ;; x is an expression and vars a variable-alist.
  (if (atom x)
      nil
    (case (operator x)
	  ;; A variable has form (var v)
	  (var (and (varp x)
		    (definedp (param1 x) vars)))
	  ;; A literal has form (lit . x), where x is
	  ;; a constant number or symbol, or a list of such.
	  (lit (valuep (cdr x)))
	  ;; The following are all expressions involving 
	  ;; operations. 
	  (== (and (lenp x 3)
		   (exprp (param1 x) vars)
		   (exprp (param2 x) vars)))
	  (+ (and (lenp x 3)
		  (exprp (param1 x) vars)
		  (exprp (param2 x) vars)))
	  (- (and (lenp x 3)
		  (exprp (param1 x) vars)
		  (exprp (param2 x) vars)))
	  (* (and (lenp x 3)
		  (exprp (param1 x) vars)
		  (exprp (param2 x) vars)))
	  (< (and (lenp x 3)
		  (exprp (param1 x) vars)
		  (exprp (param2 x) vars)))
	  (<= (and (lenp x 3)
		   (exprp (param1 x) vars)
		   (exprp (param2 x) vars)))
	  (> (and (lenp x 3)
		  (exprp (param1 x) vars)
		  (exprp (param2 x) vars)))
	  (>= (and (lenp x 3)
		   (exprp (param1 x) vars)
		   (exprp (param2 x) vars)))
	  ;; flr function
	  (// (and (lenp x 3)
		   (exprp (param1 x) vars)
		   (exprp (param1 x) vars)))
	  ;; len function for a list
	  (len (and (lenp x 3)
		    (exprp (param1 x) vars)))
	  ;; indexing into a list: (int i l) is l[i]
	  (ind (and (lenp x 3)
		    (exprp (param1 x) vars)
		    (exprp (param2 x) vars)))
	  (otherwise nil))))

;; Now returns a triple (mv status value steps).  If the status is T
;;    then the value can be trusted.  If the status is nil, then some
;;    error occurred in the evaluation.

(defmacro exeval-status (triple)
  `(mv-nth 0 ,triple))

(defmacro exeval-value (triple)
  `(mv-nth 1 ,triple))

(defmacro exeval-value (triple)
  `(mv-nth 1 ,triple))

(defmacro exeval-steps (triple)
  `(mv-nth 2 ,triple))

(defun exeval-error ()
  (mv nil nil 0))

;; All syntactic/semantic tests are built into the evaluation
;; function.  If any check ever fails, then the evaluation fails and
;; returns an error.  Evaluation is strict, in that any error stops
;; evaluation and percolates up to the top.

(defun exeval (x status vars)
  ;; This returns a triple (status value steps), where status is a
  ;; boolean indicating whether evaluation returned an error. Steps is
  ;; the number of steps required to evaluate the expression.  This is
  ;; strict in the error evaluation.  If an error occurs during the
  ;; evaluation, we don't care about the value or steps.
  (if (not status)
      (exeval-error)
    (if (atom x)
	(exeval-error)
      (case (operator x)
	    ;; Variables
	    (var (if (definedp (param1 x) vars)
		     (mv t (lookup (param1 x) vars) 1)
		   (exeval-error)))
	    ;; Literals
	    (lit (if (valuep (cdr x))
		     (mv t (cdr x) 1)
		   (exeval-error)))
	    ;; Equality
	    (== (mv-let (stat1 val1 steps1)
			(exeval (param1 x) status vars)
			(mv-let (stat2 val2 steps2)
				(exeval (param2 x) status vars)
				(if (and stat1 stat2)
				    (mv t (equal val1 val2) (+ 1 steps1 steps2))
				  (exeval-error)))))
	    ;; Addition
	    (+ (mv-let (stat1 val1 steps1)
		       (exeval (param1 x) status vars)
		       (mv-let (stat2 val2 steps2)
			       (exeval (param2 x) status vars)
			       (if (and stat1 stat2
					(acl2-numberp val1)
					(acl2-numberp val2))
				   (mv t (+ val1 val2) (+ 1 steps1 steps2))
				 (exeval-error)))))
	    ;; Subtraction
	    (- (mv-let (stat1 val1 steps1)
		       (exeval (param1 x) status vars)
		       (mv-let (stat2 val2 steps2)
			       (exeval (param2 x) status vars)
			       (if (and stat1 stat2
					(acl2-numberp val1)
					(acl2-numberp val2))
				   (mv t (- val1 val2) (+ 1 steps1 steps2))
				 (exeval-error)))))
	    ;; Multiplication
	    (* (mv-let (stat1 val1 steps1)
		       (exeval (param1 x) status vars)
		       (mv-let (stat2 val2 steps2)
			       (exeval (param2 x) status vars)
			       (if (and stat1 stat2
					(acl2-numberp val1)
					(acl2-numberp val2))
				   (mv t (* val1 val2) (+ 1 steps1 steps2))
				 (exeval-error)))))
	    ;; Integer division (flr)
	    ;; We're only going to allow integer division (// n d), where
	    ;; n is a natural and d is a positive natural
	    (// (mv-let (stat1 val1 steps1)
			(exeval (param1 x) status vars)
			(mv-let (stat2 val2 steps2)
				(exeval (param2 x) status vars)
				(if (and stat1 stat2
					 (natp val1)
					 (posp val2))
				    (mv t (flr val1 val2) (+ 1 steps1 steps2))
				  (exeval-error)))))
	    ;; Less than
	    (< (mv-let (stat1 val1 steps1)
		       (exeval (param1 x) status vars)
		       (mv-let (stat2 val2 steps2)
			       (exeval (param2 x) status vars)
			       (if (and stat1 stat2
					(acl2-numberp val1)
					(acl2-numberp val2))
				   (mv t (< val1 val2) (+ 1 steps1 steps2))
				 (exeval-error)))))
	    ;; Less than or equal
	    (<= (mv-let (stat1 val1 steps1)
			(exeval (param1 x) status vars)
			(mv-let (stat2 val2 steps2)
				(exeval (param2 x) status vars)
				(if (and stat1 stat2
					 (acl2-numberp val1)
					 (acl2-numberp val2))
				    (mv t (<= val1 val2) (+ 1 steps1 steps2))
				  (exeval-error)))))
	    ;; Greater than
	    (> (mv-let (stat1 val1 steps1)
		       (exeval (param1 x) status vars)
		       (mv-let (stat2 val2 steps2)
			       (exeval (param2 x) status vars)
			       (if (and stat1 stat2
					(acl2-numberp val1)
					(acl2-numberp val2))
				   (mv t (> val1 val2) (+ 1 steps1 steps2))
				 (exeval-error)))))
	    ;; Greater than or equal
	    (>= (mv-let (stat1 val1 steps1)
			(exeval (param1 x) status vars)
			(mv-let (stat2 val2 steps2)
				(exeval (param2 x) status vars)
				(if (and stat1 stat2
					 (acl2-numberp val1)
					 (acl2-numberp val2))
				    (mv t (>= val1 val2) (+ 1 steps1 steps2))
				  (exeval-error)))))
	    ;; Length of a list
	    (len (mv-let (stat val steps)
			 (exeval (param1 x) status vars)
			 (if (and stat
				  (listp val))
			     (mv t (len val) (1+ steps))
			   (exeval-error))))
	    ;; Index into a list (ind i lst)
	    (ind (mv-let (stat1 val1 steps1)
			 (exeval (param1 x) status vars)
			 (mv-let (stat2 val2 steps2)
				 (exeval (param2 x) status vars)
				 (if (and stat1 stat2
					  (natp val1)
					  (listp val2)
					  (< val1 (len val2)))
				     (mv t (nth val1 val2) (+ 1 steps1 steps2))
				   (exeval-error)))))
	    (otherwise (exeval-error))))))

(defthm varp-exeval-expander
  (implies (and (varp x)
		status)
	   (equal (exeval x status alist)
		  (if (definedp (param1 x) alist)
		      (mv t (lookup (param1 x) alist) 1)
		    (exeval-error)))))

(defthm valuep-list-literal-listp
  (implies (and (valuep lst)
		(< 0 (len lst)))
	   (literal-listp lst)))
		
(defthm ind-literal-listp-literalp
  (implies (and (natp i)
		(literal-listp lst)
		(< i (len lst)))
	   (literalp (nth i lst))))

(defthm literalp-valuep
  (implies (literalp x)
	   (valuep x)))

(in-theory (disable valuep))

(defthm exeval-equality-expander
  (implies status
	   (equal (exeval (list '== x y) status vars)
		  (if (exeval-status (exeval x status vars))
		      (if (exeval-status (exeval y status vars))
			  (mv t
			      (equal (exeval-value (exeval x status vars))
				     (exeval-value (exeval y status vars)))
			      (+ 1
				 (exeval-steps (exeval x status vars))
				 (exeval-steps (exeval y status vars))))
			(exeval-error))
		    (exeval-error)))))

(defthm exeval-ind-expander
  (implies status
	   (equal (exeval (list 'ind i lst) status vars)
		  (if (and (exeval-status (exeval i status vars))
			   (exeval-status (exeval lst status vars))
			   (natp (exeval-value (exeval i status vars)))
			   (< (exeval-value (exeval i status vars))
			      (len (exeval-value (exeval lst status vars)))))
		      (mv t
			  (nth (exeval-value (exeval i status vars))
			       (exeval-value (exeval lst status vars)))
			  (+ 1
			     (exeval-steps (exeval i status vars))
			     (exeval-steps (exeval lst status vars))))
		    (exeval-error)))))

(defthm exeval-<-expander
  (implies status
	   (equal (exeval (list '< x y) status vars)
		  (if (and (exeval-status (exeval x status vars))
		           (exeval-status (exeval y status vars))
			   (acl2-numberp (exeval-value (exeval x status vars)))
			   (acl2-numberp (exeval-value (exeval y status vars))))
		      (mv t (< (mv-nth 1 (exeval x status vars))
			       (mv-nth 1 (exeval y status vars)))
			  (+ 1
			     (exeval-steps (exeval x status vars))
			     (exeval-steps (exeval y status vars))))
		  (exeval-error)))))

(defthm exeval-<=-expander
  (implies status
	   (equal (exeval (list '<= x y) status vars)
		  (if (and (exeval-status (exeval x status vars))
		           (exeval-status (exeval y status vars))
			   (acl2-numberp (exeval-value (exeval x status vars)))
			   (acl2-numberp (exeval-value (exeval y status vars))))
		      (mv t (<= (mv-nth 1 (exeval x status vars))
			       (mv-nth 1 (exeval y status vars)))
			  (+ 1
			     (exeval-steps (exeval x status vars))
			     (exeval-steps (exeval y status vars))))
		  (exeval-error))))
  :hints (("Goal" :in-theory (enable exeval))))

(defthm exeval-len-expander
  (implies status
	   (equal (exeval (list 'len lst) status vars)
		  (if (and (exeval-status (exeval lst status vars))
			   (listp (exeval-value (exeval lst status vars))))
		      (mv t
			  (len (exeval-value (exeval lst status vars)))
			  (1+ (exeval-steps (exeval lst status vars))))
		    (exeval-error)))))
			   
(defthm exeval-lit-expander
  (implies (valuep x)
	   (equal (exeval (cons 'lit x) t vars)
		  (mv t x 1))))
;  :hints (("Goal" :in-theory (enable exeval))))

(defthm exeval-arithmetic-op-expander
  (implies status
	   (and (equal (exeval (list '+ x y) status vars)
		       (if (and (exeval-status (exeval x status vars))
				(exeval-status (exeval y status vars))
				(acl2-numberp (exeval-value (exeval x status vars)))
				(acl2-numberp (exeval-value (exeval y status vars))))
			   (mv t (+ (mv-nth 1 (exeval x status vars))
				    (mv-nth 1 (exeval y status vars)))
			       (+ 1
				  (exeval-steps (exeval x status vars))
				  (exeval-steps (exeval y status vars))))
			 (exeval-error)))
		(equal (exeval (list '- x y) status vars)
		       (if (and (exeval-status (exeval x status vars))
				(exeval-status (exeval y status vars))
				(acl2-numberp (exeval-value (exeval x status vars)))
				(acl2-numberp (exeval-value (exeval y status vars))))
			   (mv t (- (mv-nth 1 (exeval x status vars))
				    (mv-nth 1 (exeval y status vars)))
			       (+ 1
				  (exeval-steps (exeval x status vars))
				  (exeval-steps (exeval y status vars))))
			 (exeval-error)))
		(equal (exeval (list '* x y) status vars)
		       (if (and (exeval-status (exeval x status vars))
				(exeval-status (exeval y status vars))
				(acl2-numberp (exeval-value (exeval x status vars)))
				(acl2-numberp (exeval-value (exeval y status vars))))
			   (mv t (* (mv-nth 1 (exeval x status vars))
				    (mv-nth 1 (exeval y status vars)))
			       (+ 1
				  (exeval-steps (exeval x status vars))
				  (exeval-steps (exeval y status vars))))
			 (exeval-error)))))
  :hints (("Goal" :in-theory (enable exeval))))

(defthm exeval-//-expander
  (implies status
	   (equal (exeval (list '// x y) status vars)
		  (if (and (exeval-status (exeval x status vars))
			   (exeval-status (exeval y status vars))
			   (natp (exeval-value (exeval x status vars)))
			   (posp (exeval-value (exeval y status vars))))
		      (mv t
			  (flr (exeval-value (exeval x status vars))
				 (exeval-value (exeval y status vars)))
			  (+ 1 (exeval-steps (exeval x status vars))
			     (exeval-steps (exeval y status vars))))
		    (exeval-error))))
  :hints (("Goal" :in-theory (enable exeval))))

(defthm exeval-steps-natp
  (natp (exeval-steps (exeval exp status vars)))
  :rule-classes :type-prescription)

(defthm exeval-steps-natp-corollary1
  (and (acl2-numberp (exeval-steps (exeval exp status vars)))
       (integerp (exeval-steps (exeval exp status vars))))
  :hints (("Goal" :use (:instance exeval-steps-natp)))
  :rule-classes (:rewrite :type-prescription ))

(defthm exeval-steps-natp-corollary2
  (<= 0 (exeval-steps (exeval exp status vars)))
  :hints (("Goal" :use (:instance exeval-steps-natp)))
  :rule-classes :linear )

(in-theory (disable exeval))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                       STATEMENT LANGUAGE                         ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The statement language consists of the following:
;;     (skip)                             - no-op
;;     (assign var expr)                  - var = expr
;;     (return val)                       - return val
;;     (if-else test stmt1 stmt2)         - if test then stmt1 else stmt2
;;     (while test stmt)                  - while test: stmt
;;     (seq stmt1 stmt2)                  - stmt1 ; stmt2

;;
;; Statements are evaluated within the context of a state that contains
;; a variable alist and a status (T or nil). 

(defun okp (status)
  (equal status 'ok))

(defun timedoutp (status)
  (equal status 'timed-out))

(defun returnedp (status)
  (equal status 'returned))

;; The run function returns a triple: (status vars steps).

(defmacro run-status (triple)
  `(mv-nth 0 ,triple))

(defmacro run-vars (triple)
  `(mv-nth 1 ,triple))

(defmacro run-steps (triple)
  `(mv-nth 2 ,triple))

;; >>> If there's an error, we don't really care about steps.  Not sure if this is 
;;     the right choice. 

(defun run-error (vars)
  (mv 'error vars 0))

;; Each of the run functions is passed a steps parameter, which is the number of 
;; steps prior to the execution. 

(defun run-skip (stmt vars steps)
  ;; statement has form (skip)
  (declare (ignore stmt))
  (mv 'ok vars steps))

;; Not clear whether steps for an assignment should be (steps lhs) + 1
;; or + 2.  Perhaps one for the variable on the lhs and one for the
;; assignment.  I don't think it really matters much.  I'm going with +1 
;; for this first version.

(defun run-assignment (stmt vars steps)
  ;; statement has form (assign var expr)
  ;; Notice that this only allows the lhs to be a variable.
  (mv-let (eval-stat val eval-steps)
	  (exeval (param2 stmt) t vars)
	  (if (and (varp (param1 stmt))
		   eval-stat)
	      (mv 'ok (store (cadr (cadr stmt)) val vars) (+ 1 eval-steps steps))
	    (run-error vars))))

;; Return uses variable 'result to store the value.
;; Probably need to declare this special in some way. 

(defun run-return (stmt vars steps)
  ;; statement has form (return val)
  (mv-let (eval-stat val eval-steps)
	  (exeval (param1 stmt) t vars)
	  (if eval-stat
	      (mv 'returned (store 'result val vars) (+ 1 eval-steps steps))
	    (run-error vars))))

(defun run (stmt status vars steps count)
  ;; This is the interpreter for our simple language.  It returns a triple 
  ;; (mv status var-alist steps).  The steps parameter is the cumulative count 
  ;; of steps before this execution.
  (declare (xargs :measure (two-nats-measure count (acl2-count stmt))))
  (if (not (okp status))
      (mv status vars steps)
    (if (zp count)
	(mv 'timed-out vars steps)
      (case (operator stmt)
	    (skip     (run-skip stmt vars steps))
	    (assign   (run-assignment stmt vars steps))
	    (return   (run-return stmt vars steps))
	    (seq      (mv-let (new-stat new-vars steps1)
			      (run (param1 stmt) status vars steps count)
			      ;; Note that steps1 should already include steps.
			      (run (param2 stmt) new-stat new-vars steps1 count)))
	    (if-else  (mv-let (eval-stat eval-val eval-steps)
			      (exeval (param1 stmt) t vars)
			      (if (not eval-stat)
				  (run-error vars)
				(if eval-val
				    (run (param2 stmt) status vars (+ 1 steps eval-steps) count)
				  (run (param3 stmt) status vars (+ 1 steps eval-steps) count)))))
	    (while   (mv-let (test-stat test-val test-steps)
			     (exeval (param1 stmt) t vars)
			     (if (not test-stat)
				 (run-error vars)
			       (if test-val
				   (mv-let (body-stat body-vars body-steps)
					   (run (param2 stmt) status vars (+ 1 steps test-steps) count)
					   (run stmt body-stat body-vars body-steps (1- count)))
				 (mv 'ok vars (+ 1 test-steps steps))))))
	    (otherwise (run-error vars))))))

(defthm not-timed-outp-not-zp-count
  (implies (and (not (timedoutp (run-status (run stmt status vars steps count))))
		(okp status))
	   (not (zp count))))

; (defthm run-preserves-var-sublistp
;   (var-sublistp vars (run-vars (run stmt status vars steps count))))

; (defthm run-preserves-exprp
;   (implies (exprp exp vars)
; 	   (exprp exp (run-vars (run stmt status vars steps count)))))

(defthmd run-splitter
  ;; This is a very specialized rule, so keep it disabled
  (equal (equal (run stmt stat vars steps count)
		(list (car (run stmt stat vars steps count))
		      (mv-nth 1 (run stmt stat vars steps count))
		      (mv-nth 2 (run stmt stat vars steps count))))
	 t))

(defthm run-return-expander
  (equal (run (list 'return x) stat vars steps count)
	 (if (not (okp stat))
	     (mv stat vars steps)
	   (if (zp count)
	       (mv 'timed-out vars steps)
	     (if (exeval-status (exeval x t vars))
		 (mv 'returned
		     (store 'result
			    (exeval-value (exeval x t vars))
			    vars)
		     (+ 1 steps (exeval-steps (exeval x t vars))))
	       (run-error vars))))))

(defthm run-assign-expander
  (equal (run (list 'assign i val) stat vars steps count)
	 (if (not (okp stat))
	     (mv stat vars steps)
	   (if (zp count)
	       (mv 'timed-out vars steps)
	     (if (or (not (exeval-status (exeval val t vars)))
		     (not (varp i)))
		 (run-error vars)
	       (mv 'ok
		   (store (param1 i)
			  (exeval-value (exeval val t vars))
			  vars)
		   (+ 1 (exeval-steps (exeval val t vars)) steps)))))))

(defthm run-seq-expander
  (equal (run (list 'seq stmt1 stmt2) stat vars steps count)
	 (if (not (okp stat))
	     (mv stat vars steps)
	   (if (zp count)
	       (mv 'timed-out vars steps)
	     (run stmt2
		  (run-status (run stmt1 'ok vars steps count))
		  (run-vars   (run stmt1 'ok vars steps count))
		  (run-steps  (run stmt1 'ok vars steps count))
		  count)))))

(defthm run-if-else-expander
  (equal (run (cons 'if-else (list test tbranch fbranch)) stat vars steps count)
	 (if (not (okp stat))
	     (mv stat vars steps)
	   (if (zp count)
	       (mv 'timed-out vars steps)
	     (mv-let (test-stat test-val test-steps)
		     (exeval test t vars)
		     (if (not test-stat)
			 (run-error vars)
		       (if test-val
			   (run tbranch stat vars (+ 1 steps test-steps) count)
			 (run fbranch stat vars (+ 1 steps test-steps) count))))))))

(defthmd run-while-expander
    (equal (run (list 'while test body) stat vars steps count)
	   (if (not (okp stat))
	       (mv stat vars steps)
	     (if (zp count)
		 (mv 'timed-out vars steps)
	       (mv-let (test-stat test-val test-steps)
		       (exeval test t vars)
		       (if (not test-stat)
			   (run-error vars)
			 (if test-val
			     (mv-let (body-stat body-vars body-steps)
				     (run body stat vars (+ 1 steps test-steps) count)
				     (run (list 'while test body) body-stat body-vars body-steps (1- count)))
			   (mv stat vars (+ 1 test-steps steps)))))))))


(defthm assign-preserves-other-vars
  (implies (and (okp stat)
		(varp i)
		(varp j)
		(not (equal (param1 i) (param1 j))))
	   (let* ((st (run (list 'assign i val) stat vars steps count))
		  (vars2 (mv-nth 1 st)))
	     (equal (lookup j vars2)
		    (lookup j vars)))))

;; These functions allow using the syntax: (seqn x y z ...) 
;; instead of a bunch of nested seqs.

(defun seqn-fn (args)
  (declare (xargs :guard (true-listp args)))
  (if (endp args)
      '(skip)
    (if (endp (rest args))
        (first args)
      (xxxjoin 'seq args))))

(defun expand-seqn (x)
; Returns nil for other than (seqn ...).
  (declare (xargs :guard t))
  (and (true-listp x)
       (eq (car x) 'seqn)
       (seqn-fn (cdr x))))

