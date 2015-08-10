(in-package "ACL2")

;;(xxinclude-book "top" :dir :bags)
(include-book "nary")

(local (include-book "ihs/ihs-definitions" :dir :system))

(defmacro ac (&optional (v 't))
  `(accumulated-persistence ,v))

(defmacro sac ()
  `(show-accumulated-persistence))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Some modular arithmetic examples
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defmacro local-hide (&rest args)
  `(local
    (encapsulate
	()
      (local
       (encapsulate
	   ()
	 ,@args)))))


(local-hide

 (defcontext (mod a n) 1)

 (encapsulate
     ()

   (local
    (encapsulate
	()

      (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

      (defun mag (x)
	(declare (xargs :measure (abs (ifix x))))
	(if (integerp x)
	    (if (zp x) 0
	      (if (< x 0) (mag (1+ x))
		(mag (1- x))))
	  x))

     (defthmd push-mod-+-1
       (implies
	(and
	 (syntaxp (symbolp x))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (+ x y) n)
	       (mod (+ (mod x n) y) n))))

     (defthmd push-mod-+-2
       (implies
	(and
	 (syntaxp (symbolp x))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (+ y x) n)
	       (mod (+ y (mod x n)) n))))

     (defthmd push-mod-*-1
       (implies
	(and
	 (syntaxp (symbolp x))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (* x y) n)
	       (mod (* (mod x n) y) n)))
       :hints (("Goal" :induct (mag x))))

     (defthmd push-mod-*-2
       (implies
	(and
	 (syntaxp (symbolp x))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (* y x) n)
	       (mod (* y (mod x n)) n)))
       :hints (("Goal" :induct (mag x))))

     (defthmd push-mod-*
       (implies
	(and
	 (syntaxp (and (symbolp x)
		       (symbolp y)))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (* y x) n)
	       (mod (* (mod y n) (mod x n)) n)))
       :hints (("Goal" :in-theory '(integerp-mod
				    push-mod-*-1
				    push-mod-*-2))))

     (defthmd push-mod-+
       (implies
	(and
	 (syntaxp (and (symbolp x)
		       (symbolp y)))
	 (integerp n)
	 (not (equal n 0))
	 (integerp x)
	 (integerp y))
	(equal (mod (+ y x) n)
	       (mod (+ (mod y n) (mod x n)) n)))
       :hints (("Goal" :in-theory '(integerp-mod
				    push-mod-+-1
				    push-mod-+-2))))

     (defthm mod-mod
       (implies
	(and
	 (integerp x)
	 (integerp n)
	 (not (equal n 0)))
	(equal (mod (mod x n) n)
	       (mod x n))))

     (defthm integerp-mod+
       (implies
	(and
	 (integerp x)
	 (integerp n))
	(integerp (mod x n))))

     ))

  (defthm mod-mod
    (implies
     (and
      (integerp x)
      (integerp n)
      (not (equal n 0)))
     (equal (mod (mod x n) n)
	    (mod x n))))

;;   (defthm integerp-mod+
;;     (implies
;;      (and
;;       (integerp x)
;;       (integerp n))
;;      (integerp (mod x n))))

;;   (defthm mod-mod
;;     (implies
;;      (and
;;       (integerp x)
;;       (integerp n)
;;       (not (equal n 0)))
;;      (equal (mod (mod x n) n)
;; 	    (mod x n))))

  (defcong+ mod-+-cong

    (mod (+ a b) n)

    :hyps (and (integerp n)
	       (not (equal n 0))
	       (integerp a)
	       (integerp b))

    :cong ((a (equal x (mod a n)))
	   (b (equal y (mod b n))))

    :check (and (integerp x)
		(integerp y))

    :hints (("Goal" :in-theory (e/d (push-mod-+)
				    (mod)))))

  (defcong+ mod-*-cong

    (mod (* a b) n)

    :hyps (and (integerp n)
	       (not (equal n 0))
	       (integerp a)
	       (integerp b))

    :cong ((a (equal x (mod a n)))
	   (b (equal y (mod b n))))

    :check (and (integerp x)
		(integerp y))

    :hints (("Goal" :in-theory (e/d (push-mod-*)
				    (mod)))))

  )

;; (defthm COMMUTATIVITY-2-OF-+
;;   (equal (+ x (+ y z))
;; 	 (+ y (+ x z))))

;; (defthm integerp-*
;;   (implies
;;    (and (integerp x) (integerp y))
;;    (integerp (* x y))))

;; (in-theory (disable mod))

(local-hide

 (local (INCLUDE-BOOK "arithmetic-3/floor-mod/floor-mod" :dir :system))

 (defun integerp-guard-fn (args)
   (if (endp (cdr args))
       (cons (cons 'integerp (cons (car args) 'nil))
	     'nil)
     (cons (cons 'integerp (cons (car args) 'nil))
	   (integerp-guard-fn (cdr args)))))

 (defmacro integerp-guard (&rest args)
   (if (endp (cdr args))
       (cons 'integerp (cons (car args) 'nil))
     (cons 'and (integerp-guard-fn args))))

 (defthm multiply-test
   (implies
    (and
     (integerp n)
     (not (equal n 0))
     (integerp-guard a b c d e))
    (equal (mod (+ (* (mod a n) (mod b n))
		   (mod (+ c (mod d n)) n)
		   (mod e n)) n)
	   (mod (+ (* a b) c d e) n))))

 (defthm test1
   (implies
    (and
     (integerp-guard a b c n)
     (not (equal n 0)))
    (equal (mod (+ a (mod (+ b (mod c n)) n)) n)
	   (mod (+ a b c) n)))
   :rule-classes nil)

 ;;
 ;; Example from the paper "Parameterized Congruences in ACL2"
 ;;

 (defund foo1 (x) x)

 (defthm foo1-prop
   (equal (mod (foo1 x) n) (mod x n))
   :hints (("Goal" :in-theory (enable foo1))))

 (defund foo2 (x) x)

 (defcong+ foo2-prop
   (mod (foo2 x) n)
   :cong ((x (equal a (mod x n))))
   :hyps (and (integerp x)
	      (integerp n)
	      (not (equal n 0)))
   :check (integerp a)
   :hints (("Goal" :in-theory (enable foo2))))

 (defthm test-foo
   (implies
    (and
     (integerp-guard a b c d e n)
     (not (equal n 0)))
    (equal (mod (+ a (mod b n) (foo1 c) (foo2 (+ (mod d n) (mod e n)))) n)
	   (mod (+ a b c (foo2 (+ d e))) n)))
   :rule-classes nil)

 ;;
 ;; Accumulated Persistence results showing quadratic behavior ..
 ;;

 (defthm test2
   (implies
    (integerp-guard a b c d e f g h)
    (equal (mod (+ a b c d e f g (mod h 100)) 5)
	   (mod (+ a b c d e f g h) 5)))
   :rule-classes nil)

#|
:brr t

Accumulated Persistence
   :frames   :tries    :ratio  rune
      1393       21 (   66.33) (:REWRITE MOD-+-CONG)

:brr nil

Accumulated Persistence
   :frames   :tries    :ratio  rune
      3878       42 (   92.33) (:REWRITE MOD-+-CONG)

|#

 (defthm test3
   (implies
    (integerp-guard a b c d e f g h i)
    (equal (mod (+ a b c d e f g h (mod i 100)) 5)
	   (mod (+ a b c d e f g h i) 5)))
   :rule-classes nil)

#|
:brr t

Accumulated Persistence
   :frames   :tries    :ratio  rune
      1784       24 (   74.33) (:REWRITE MOD-+-CONG)

:brr nil

Accumulated Persistence
   :frames   :tries    :ratio  rune
      5340       52 (  102.69) (:REWRITE MOD-+-CONG)
|#

 (defthm test4
   (implies
    (integerp-guard a b c d e f g h i j)
    (equal (mod (+ a b c d e f g h i (mod j 100)) 5)
	   (mod (+ a b c d e f g h i j) 5)))
   :rule-classes nil)

#|
:brr t

Accumulated Persistence
   :frames   :tries    :ratio  rune
      2223       27 (   82.33) (:REWRITE MOD-+-CONG)

:brr nil

Accumulated Persistence
   :frames   :tries    :ratio  rune
      7119       63 (  113.00) (:REWRITE MOD-+-CONG)
|#

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Another example, adding a second congruence rule.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

 (defun foo (a)
   (mod a 2))

 (defthm integerp-foo
   (implies
    (integerp x)
    (integerp (foo x))))

 (defthm mod-foo
   (implies
    (integerp a)
    (equal (mod (foo a) 2)
	   (mod a 2))))

 (defcong+ foo-cong

   (foo a)

   :hyps (integerp a)
   :cong ((a (equal x (mod a 2))))
   :check (integerp x)
   )

 (in-theory (disable foo))

 (defthm integerp-+
   (implies
    (and (integerp x) (integerp y))
    (integerp (+ x y))))

 (defthm foo-reduction
   (implies
    (integerp-guard x b c d)
    (equal (foo (+ x (foo (+ b (mod c 20))) (mod d 10)))
	   (foo (+ x b c d))))
   :hints (("goal" :in-theory (enable integerp-+))))

 )

(in-theory (disable mod))

(local-hide

(defcontext (loghead n x) 2)

(defcong+ loghead-+-cong

  (loghead n (+ a b))

  :hyps (and (integerp a)
	     (integerp b))

  :cong ((a (equal x (loghead n a)))
	 (b (equal y (loghead n b))))

  :check (and (integerp x)
	      (integerp y))

  :hints (("Goal" :in-theory (enable loghead))))

(defcong+ loghead-*-cong

  (loghead n (* a b))

  :hyps (and (integerp a)
	     (integerp b))

  :cong ((a (equal x (loghead n a)))
	 (b (equal y (loghead n b))))

  :check (and (integerp x)
	      (integerp y))

  :hints (("Goal" :in-theory (enable loghead))))

(defthm plus-fold-constants
  (implies
   (syntaxp (quotep c))
   (equal (+ a (+ (* c a) b))
	  (+ (* (+ c 1) a) b))))

(local (include-book "ihs/ihs-lemmas" :dir :system))

(in-theory (disable loghead))

;;; Commented out 11/28/2014 by Matt K., because the enclosing local-hide is no
;;; longer redundant, since as of late today, ACL2 no longer stores encapsulate
;;; events in the world whose sub-events are all local for encapsulates that
;;; are also "trivial" (have empty signatures).  This theorem failed previously
;;; when it was actually attempted; I'll leave it to someone else to fix, if
;;; someone wants to do that (as my simple attempts didn't work).

; (defthm loghead-theorem
;   (implies (and (integerp x) (integerp f))
;            (equal (loghead 32 (+ (* 4294967295 (loghead 32 (* x f)))
;                                  (* x f)
;                                  (* x (loghead 32 (* x f)))))
;                   (loghead 32 (* x x f)))))

(defcong+ loghead-mod-refinement
  (loghead n x)
  :cong ((x (equal a (mod x (expt 2 n)))))
  :hyps  (integerp x)
  :check (integerp a)
  :hints (("Goal" :in-theory (enable loghead))))

;;
;; Works much better if we disable LOGHEAD-UPPER-BOUND and MOD-X-Y-=-X+Y
;;

(defthm loghead-mod-theorem
  (implies (and (integerp x) (integerp f))
	   (equal (loghead 32 (+ (* 4294967295 (loghead 32 (* x f)))
				 (* (mod x (expt 2 32)) f)
				 (* x (loghead 32 (* x f)))))
		  (loghead 32 (* x x f)))))

)

(in-theory (disable mod))

(defun loghead-equivp (x y n)
  (equal (loghead n x)
	 (loghead n y)))

(defequiv+ (loghead-equivp x y n)
  :lhs x
  :rhs y
  :equiv   loghead-equiv
  :context loghead-ctx
  :keywords t
  )

(defthm loghead-cong
  (implies
   (bind-contextp (x (equal a (loghead-ctx x :n n))))
   (equal (loghead n x)
	  (loghead n a))))

(encapsulate
    ()
  (local
   (include-book "ihs/ihs-lemmas" :dir :system))

  (defthm loghead-elimination
    (implies
     (and
      (integerp n)
      (<= 0 n))
     (loghead-equiv :lhs (loghead n x)
		    :rhs x
		    :n n))
    :hints (("Goal" :in-theory (disable loghead loghead-loghead))))

  )

(defthm loghead-+-cong
  (implies
   (and
    (integerp x)
    (integerp y)
    (bind-contextp ((x (equal a (loghead-ctx x :n n)))
		    (y (equal b (loghead-ctx y :n n)))))
    (integerp a)
    (integerp b))
   (loghead-equiv :lhs (+ x y)
		  :rhs (skip-rewrite (+ a b)))))

)

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; An example of def/use analysis on stobjs
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(encapsulate
    ()

  (local (include-book "nth-rules"))

  (local
   (encapsulate
       ()

     (defcontext (use list x) 2)

     (defcong+ *nary*-use-update-nth
       (use list (update-nth a v x))
       :cong ((x (equal z (use list x))))
       :hyps (member (nfix a) (nfix-list list))
       :hints (("Goal" :in-theory `(unide-hide use-use use_unfix_check use-update-nth-member)))
       )

     (in-theory (disable (use) use))

     (defthm use-to-nth-in-conclusion
       (implies
	(in-conclusion-check (equal (use list x)
				    (use list y)))
	(equal (equal (use list x)
		      (use list y))
	       (equal (nth* list x)
		      (nth* list y))))
       :hints (("Goal" :in-theory (enable NTH*-GET-COPY-EQUIVALENCE))))


     (in-theory (disable NTH*-GET-COPY-EQUIVALENCE))

     (defstobj st
       (r1 :type integer :initially 0)
       (r2 :type integer :initially 0)
       (r3 :type integer :initially 0)
       (r4 :type integer :initially 0)
       )

     (defun foo-st (st)
       (declare (xargs :stobjs (st)))
       (let ((st (update-r1 (1+ (r1 st)) st)))
	 st))

     (defun foo-use ()
       (list *r1*))

     (defun foo-def ()
       (list *r1*))

     (defthm nth-foo-st
       (implies
	(not (member (nfix a) (foo-def)))
	(equal (nth a (foo-st st))
	       (nth a st))))

     (defcong+ *nary*-nth-foo-st-use
       (nth a (foo-st st))
       :cong ((st (equal z (use (foo-use) st))))
       :hyps (member (nfix a) (foo-def))
       :hints (("Goal" :in-theory (enable member))))

     (defcong+ *nary*-use-foo-st-use
       (use list (foo-st st))
       :cong ((st (equal z (use (append list (foo-use)) st))))
       :hints (("goal" :in-theory (e/d (use-update-nth)
				       (CLR-NTH-DEFN open-clr-nth)))))

     (in-theory (disable foo-st))

     (defthm nth-foo-st-test
       (equal (nth *r1* (foo-st st))
	      (nth *r1* (foo-st (update-nth 3 v st)))))

     (defthm use-foo-st-test
       (implies
	(not (member 3 (nfix-list list)))
	(equal (use list (foo-st st))
	       (use list (foo-st (update-nth 3 v st))))))

     )))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; An example of generalized (Boolean) congruences replacing linear
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(encapsulate
    ()

  (local
   (encapsulate
       ()

     ;; In this context we will tend to rewrite terms that are smaller
     ;; into terms that are larger.
     ;;
     (defequiv+ (<= x y)
       :equiv   <=equiv
       :context <=ctx
       )

     (defcongp+ <=-+-cong
       (+ x y)
       :equiv <=equiv
       :hyps (and (integerp x)
		  (integerp y))
       :cong ((x (equal a (<=ctx x)))
	      (y (equal b (<=ctx y)))))

     (defthm maxv-bounds-v
       (implies
	(and
	 (bind-contextp (v (equal maxv (<=ctx v))))
	 (<= maxv z))
	(<= v z)))

     (defun foo (x)
       (if (< (ifix x) 100) x 0))

     (defthm <=-foo-100-driver
       (implies
	(integerp x)
	(<=equiv (foo x) 100)))

     (in-theory (disable foo))

     (defthm <=-foo-sum-300
       (implies
	(and
	 (integerp x)
	 (integerp y)
	 (integerp z))
	(<= (+ (foo x) (foo y) (foo z)) 300)))

     )))

#+bags
(encapsulate
    ()

  (local
   (encapsulate
       ()

     (xxinclude-book "top" :dir :bags)

     (defequiv+ (bag::memberp x y)
       :pred    memberp-pred
       :equiv   memberp-equiv
       :context memberp-subbag
       :chaining nil
       )

     (defequiv+ (bag::subbagp x y)
       :pred    subbagp-pred
       :equiv   subbagp-equiv
       :context subbagp-ctx
       )

     (defstub xterm () nil)

     (defun xlist ()
       (list (xterm)))

     (in-theory (disable (xlist)))

     (defthm xterm-becomes-xlist
       (memberp-equiv (xterm) (xlist)))

     (defun x2list ()
       (list (xterm) :2))

     (in-theory (disable (x2list)))

     (defthm xlist-becomes-x2list
       (subbagp-equiv (xlist) (x2list)))

     (in-theory (disable xlist))
     (in-theory (disable x2list))

     (defun fido (x) x)

     (defcongp+ subbagp-equiv-cons-1
       (cons x y)
       :rhs (append z y)
       :cong ((x (equal z (memberp-subbag (fido x)))))
       :equiv subbagp-equiv
       :hints (("goal" :in-theory (e/d (BAG::SUBBAGP-APPEND-2
					BAG::REMOVE-1-OF-APPEND-WHEN-MEMBERP)
				       (BAG::APPEND-REMOVE-1-REDUCTION))))
       )

     (defcongp+ subbagp-equiv-cons-2
       (cons x y)
       :cong ((y (equal z (subbagp-ctx (fido y)))))
       :equiv subbagp-equiv
       )

     (defcongp+ subbagp-equiv-append-1
       (append x y)
       :cong ((x (equal z (subbagp-ctx (fido x)))))
       :equiv subbagp-equiv
       :hints (("goal" :in-theory (enable BAG::SUBBAGP-APPEND-APPEND)))
       )

     (defcongp+ subbagp-equiv-append-2
       (append x y)
       :cong ((y (equal z (subbagp-ctx (fido y)))))
       :equiv subbagp-equiv
       )

     (defund subfn (x y)
       (bag::subbagp y x))

     (defcongp+ subfn-expansion
       (subfn x y)
       :cong ((y (equal z (subbagp-ctx (fido y)))))
       :equiv =>
       :hints (("Goal" :expand (:free (x) (hide x))
		:in-theory (enable subfn)))
       )

     (defthm bag-test
       (implies
	(subfn x (CONS :A (APPEND (X2LIST) (X2LIST) (X2LIST))))
	(subfn x (cons :a
		       (cons (xterm)
			     (append (xlist)
				     (x2list)))))))
     )))
