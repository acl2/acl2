#|

This is in an ACL2 "book".  It implementes the basic definitions and theorems
needed to reason about powerlists.  This book, as well as others working with
powerlists, is described in the paper "Defthms About Zip and Tie", UTCS tech
report TR97-02.

Powerlists are objects much like lists with the following basic differences:

    * There is no such thing as a singleton powerlist (i.e., a powerlist of
      length 1).  To represent the singleton <x>, we simply use x.

    * The basic constructors/destructors for powerlists are tie & zip.  Tie
      behaves like "list append", and zip behaves like a shuffle.  For example,

	(tie '<a1 a2 a3 a4> '<b1 b2 b3 b4>) = '<a1 a2 a3 a4 b1 b2 b3 b4>

	(zip '<a1 a2 a3 a4> '<b1 b2 b3 b4>) = '<a1 b1 a2 b2 a3 b3 a4 b4>

      It is expected that these operators are applied to powerlists of the same
      length, so that powerlists are usually of length 2^n.  Of course, our
      definitions are more general (ACL2 being a complete logic).

We implement powerlists as cons-trees.  We bias the implementation in favor of
tie, so that the tie of two powerlists is simply their cons.  With the expected
usage (i.e., tie/zip applied to lists of equal length), this will result in
perfectly balanced cons trees.

To certify this book, first define the POWERLISTS package, then execute an
appropriate certify-book command.  Something like the following will work:

    (ld ;; newline to fool dependency scanner
      "defpkg.lisp")
    (certify-book "algebra" 4)

|#

(in-package "POWERLISTS")

(set-verify-guards-eagerness 2)


(include-book "data-structures/structures" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(verify-guards u::import-as-macros-fn)	; Sigh.....

;;; We start out with the basic definitions of tie & zip.  We also need the
;;; inverse functions, so that we can define recursive functions of powerlists

;(defstructure::defstructure powerlist car cdr (:options :guards))

(encapsulate
 ((powerlist (car cdr) t)
  (powerlist-p (powerlist) t)
  (powerlist-car (powerlist) t)
  (powerlist-cdr (powerlist) t))

 (local
  (in-theory (theory 'defstructure::minimal-theory-for-defstructure)))

 (local
  (defun powerlist (car cdr)
    (declare (xargs :guard t))
    (cons 'powerlist (cons car (cons cdr nil)))))

 (defthm defs-acl2-count-powerlist
   (equal (acl2-count (powerlist car cdr))
	  (+ 3 (acl2-count car) (acl2-count cdr))))

 (local
  (defun powerlist-p (powerlist)
    (declare (xargs :guard t))
    (and (consp powerlist) (consp (cdr powerlist))
	 (consp (cdr (cdr powerlist)))
	 (null (cdr (cdr (cdr powerlist))))
	 (eq (car powerlist) 'powerlist))))

 (defthm defs-powerlist-p-powerlist
   (equal (powerlist-p (powerlist car cdr)) t)
   :rule-classes ((:rewrite)
		  (:built-in-clause :corollary
				    (powerlist-p (powerlist car cdr)))))

 (local
  (defun powerlist-car (powerlist)
    (declare (xargs :guard (powerlist-p powerlist)))
    (car (cdr powerlist))))

 (local
  (defun powerlist-cdr (powerlist)
    (declare (xargs :guard (powerlist-p powerlist)))
    (car (cdr (cdr powerlist)))))

 (defthm untie-reduces-count
   (implies (powerlist-p x)
	    (and (< (acl2-count (powerlist-car x))
		    (acl2-count x))
		 (< (acl2-count (powerlist-cdr x))
		    (acl2-count x))))
   :rule-classes (:rewrite :linear))

 (defthm defs-read-powerlist
   (and (equal (powerlist-car (powerlist car cdr))
	       car)
	(equal (powerlist-cdr (powerlist car cdr))
	       cdr)))

 (defthm defs-powerlist-lift-if
   (and (equal (powerlist-car
		(if powerlist-test powerlist-left
		  powerlist-right))
	       (if powerlist-test
		   (powerlist-car powerlist-left)
		 (powerlist-car powerlist-right)))
	(equal (powerlist-cdr
		(if powerlist-test powerlist-left
		  powerlist-right))
	       (if powerlist-test
		   (powerlist-cdr powerlist-left)
		 (powerlist-cdr powerlist-right)))))

 (defthm defs-eliminate-powerlist
   (implies (powerlist-p powerlist)
	    (equal (powerlist (powerlist-car powerlist)
			      (powerlist-cdr powerlist))
		   powerlist))
   :rule-classes (:rewrite :elim))

 (defthm nesting-powerlists
   (equal (powerlist-p (list 'nest x)) nil))

 (local
  (defthm expand-booleanp
    (equal (booleanp x)
	   (or (equal x t) (equal x nil)))
    :hints (("Goal" :expand ((booleanp x))))))

 (defthm powerlist-non-boolean
   (implies (powerlist-p x)
	    (not (booleanp x))))

 (defthm boolean-non-powerlist
   (implies (booleanp x)
	    (not (powerlist-p x))))

 (defthm powerlist-non-numeric
   (implies (powerlist-p x)
	    (not (acl2-numberp x))))

 (defthm numeric-non-powerlist
   (implies (acl2-numberp x)
	    (not (powerlist-p x))))
 )

(deftheory defs-powerlist-lemma-theory
  '(defs-acl2-count-powerlist defs-eliminate-powerlist
     defs-powerlist-lift-if defs-powerlist-p-powerlist
     defs-read-powerlist))

(defmacro p-tie (x y)
  `(powerlist ,x ,y))

(defmacro p-untie-l (x)
  `(powerlist-car ,x))

(defmacro p-untie-r (x)
  `(powerlist-cdr ,x))

(defthm untie-reduces-count-fast
  (implies (powerlist-p x)
	   (and (e0-ord-< (acl2-count (p-untie-l x))
			  (acl2-count x))
		(e0-ord-< (acl2-count (p-untie-r x))
			  (acl2-count x))))
  :rule-classes :built-in-clause)

(defun p-zip (x y)
  "Zip two powerlists"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (p-zip (p-untie-l x) (p-untie-l y))
	     (p-zip (p-untie-r x) (p-untie-r y)))
    (p-tie x y)))

(defthm powerlist-zip
  (powerlist-p (p-zip x y))
  :rule-classes (:rewrite :type-prescription))

(defun p-unzip-l (x)
  "Get the left part of a zipped powerlist"
  (declare (xargs :guard (powerlist-p x)))
  (if (powerlist-p x)
      (if (powerlist-p (p-untie-l x))
	  (if (powerlist-p (p-untie-r x))
	      (p-tie (p-unzip-l (p-untie-l x))
		     (p-unzip-l (p-untie-r x)))
	    (p-untie-l x))
	(p-untie-l x))
    x))

(defun p-unzip-r (x)
  "Get the right part of a zipped powerlist"
  (declare (xargs :guard (powerlist-p x)))
  (if (powerlist-p x)
      (if (powerlist-p (p-untie-l x))
	  (if (powerlist-p (p-untie-r x))
	      (p-tie (p-unzip-r (p-untie-l x))
		     (p-unzip-r (p-untie-r x)))
	    (p-untie-r x))
	(p-untie-r x))
    nil))

;;; The following theorem justifies recursion on powerlists using unzip.  As
;;; with untie, we make the rewrite rulea built-in so that such recursions are
;;; automatically accepted by ACL2.

(defthm unzip-reduces-count
  (implies (powerlist-p x)
	   (and (< (acl2-count (p-unzip-l x)) (acl2-count x))
		(< (acl2-count (p-unzip-r x)) (acl2-count x))))
  :rule-classes (:rewrite :linear))

(defthm unzip-reduces-count-fast
  (implies (powerlist-p x)
	   (and (e0-ord-< (acl2-count (p-unzip-l x))
			  (acl2-count x))
		(e0-ord-< (acl2-count (p-unzip-r x))
			  (acl2-count x))))
  :rule-classes :built-in-clause)

;;; Following are the fundamental theorems about zip and unzip.  We do not have
;;; to do equivalent theorems for tie/untie, since tie/untie is implemented as
;;; cons and car/cdr so that the similar theorems are "built-in" to ACL2.

;;; We cooked the definitions of zip/unzip to make the following three theorems
;;; true.

(defthm zip-unzip
  (implies (powerlist-p x)
	   (equal (p-zip (p-unzip-l x)
			 (p-unzip-r x))
		  x))
  :rule-classes (:rewrite :elim))

(defthm unzip-l-zip
  (equal (p-unzip-l (p-zip x y)) x))

(defthm unzip-r-zip
      (equal (p-unzip-r (p-zip x y)) y))

;;; The following type-predicate is one of the most fundamental properties on
;;; powerlists.  We say two powerlists are similar if they have the same
;;; cons-tree structure.  Many theorems require that two powerlists be
;;; similar. This is so that when traversing one of the trees, we're guaranteed
;;; to have a corresponding branch on the other tree.

(defun p-similar-p (x y)
  "Powerlists are similar if they have the same tree structure"
  (if (powerlist-p x)
      (and (powerlist-p y)
	   (p-similar-p (p-untie-l x) (p-untie-l y))
	   (p-similar-p (p-untie-r x) (p-untie-r y)))
    (not (powerlist-p y))))


(in-theory (disable (p-similar-p)))

(defthm similar-non-powerlists
  (implies (and (not (powerlist-p x))
		(p-similar-p x y))
	   (not (powerlist-p y)))
  :rule-classes (:rewrite :forward-chaining))

;;; A trivial, yet useful result.  Similar is an equivalence relation on the
;;; powerlists.

(defequiv p-similar-p :otf-flg t)

;;; A common proof obligation is that if two powerlists are similar, then their
;;; untie's or unzip's are similar.  We encounter this often when proving
;;; theorems with 'similar' in the hypothesis.  We declare these rules to be
;;; forward-chained so that whenever we detect that two powerlists are similar,
;;; we can automatically deduce that about their tie/unzip and speed up the
;;; inductive step.  We do not know yet whether we're getting much mileage out
;;; of this rule-type, though we notice that several proofs do use the
;;; forward-chaining version of the generated rules.

(defthm unzip-l-similar
  (implies (and (p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (acl2::term-order x y))))
	   (p-similar-p (p-unzip-l x) (p-unzip-l y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm unzip-r-similar
  (implies (and (p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (acl2::term-order x y))))
	   (p-similar-p (p-unzip-r x) (p-unzip-r y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm untie-l-similar
  (implies (and (powerlist-p x)
		(p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (acl2::term-order x y))))
	   (p-similar-p (p-untie-l x) (p-untie-l y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm untie-r-similar
  (implies (and (powerlist-p x)
		(p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (acl2::term-order x y))))
	   (p-similar-p (p-untie-r x) (p-untie-r y)))
  :rule-classes (:rewrite :forward-chaining))

;;; This is a silly theorem, stating that if two trees are similar, then either
;;; they're both trees or neither is a tree.  Duh.  However, we found some
;;; proofs that got stuck on just this point, so we add it as a rewrite
;;; rule. Maybe this should be forward-chained as well?

(defthm similar-powerlist
  (implies (and (p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (acl2::term-order x y))))
	   (iff (powerlist-p x) (powerlist-p y))))

;;; Next, we consider what happens to the structure of a zip when we replace
;;; one of its arguments with a similar one.  The answer, of course, is that
;;; the structure doesn't change.  In ACL2-speak, this is a congruence.  If x1
;;; and x2 are similar, then so are (zip x1 y) and (zip x2 y) and similarly if
;;; y is replaced instead of x.  We do not need to write the corresponding
;;; theorems for tie, since the result follows from the transitivity of similar
;;; and the definition of similar (which says trees are similar if their unties
;;; are similar.

(defcong p-similar-p p-similar-p (p-zip x y) 1)
(defcong p-similar-p p-similar-p (p-zip x y) 2)

;;; Another important property of powerlists is 'regular'.  A powerlist is
;;; regular if and only if its underlying cons tree is a complete binary
;;; tree. The reason this property is so important is that a regular tree has
;;; similar unties and unzips, so it is possible to swap these around in a
;;; recursive definition.  For example, one could recurse on the unzips of a
;;; powerlists and then join the results using tie.

(defun p-regular-p (x)
  "Regular powerlists are complete binary trees"
  (if (powerlist-p x)
      (and (p-similar-p (p-untie-l x) (p-untie-r x))
	   (p-regular-p (p-untie-l x))
	   (p-regular-p (p-untie-r x)))
    t))

(in-theory (disable (p-regular-p)))

;;; First, we prove the following results, which allow us to preserve the
;;; regular property across recursions using unzip on powerlists. Incidentally,
;;; a similar theorem involving zip is not true.  Just because two powerlists
;;; are regular does not mean their zip is regular (they could be of different
;;; heights).

(defthm unzip-regular
  (implies (p-regular-p x)
	   (and (p-regular-p (p-unzip-l x))
		(p-regular-p (p-unzip-r x))))
  :hints (("Goal" :in-theory (disable zip-unzip)))
  :rule-classes (:rewrite :forward-chaining)
  :otf-flg t)

;;; Next, we prove the fundamental properties of regular powerlists.  We start
;;; out with the crucial property that if a powerlist is regular, then all the
;;; possible combinations of unzips and unties are regular.  Then, we show that
;;; a powerlist similar to a regular powerlist, then it too is regular.  This
;;; is tremendously useful, since it avoids having to add "(regular y)" as a
;;; hypothesis in many theorems.  That's because often we already need x to be
;;; regular, and we also need x and y to be similar, then we can say something
;;; about a combination of x and y.

(defthm regular-similar-unzip-untie
  (implies (and (powerlist-p x)
		(p-regular-p x))
	   (and (p-similar-p (p-unzip-l x)
			     (p-unzip-r x))
		(p-similar-p (p-unzip-l x)
			     (p-untie-l x))
		(p-similar-p (p-unzip-r x)
			     (p-untie-r x))))
  :rule-classes (:rewrite :forward-chaining))

(defthm regular-similar-swap-unzip
  (implies (and (p-regular-p x)
		(p-similar-p x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context
                ;; (avoids stack overflow in merge-similar-zip, book
                ;; batcher-sort):
                (syntaxp (not (acl2::term-order x y))))
	   (and (p-similar-p (p-unzip-l x) (p-unzip-r y))
		(p-similar-p (p-unzip-r x) (p-unzip-l y))))
  :rule-classes (:rewrite :forward-chaining))

(defthm similar-regular
  (implies (and (p-regular-p x)
		(p-similar-p x y)
                ;; Unlike the other chnages for mod to ACL2 v2-8 that does
                ;; better matching for calls of equivalence relations against
                ;; the current context, this case is different because the free
                ;; variable (x) is bound first.  So, there is no free variable
                ;; here, and hence the restriction to term-order doesn't really
                ;; help anyhow, since the full rewriter is called on
                ;; (p-similar-p x y) rather than just a matcher on type-alists
                ;; [which we had been trying to restrict using term-order to
                ;; the pre-v2-8 behavior, now that v2-8 does better matching].
                )
	   (p-regular-p y))
  :rule-classes (:rewrite :forward-chaining))

;;; The following beautiful result states that zips/ties of regular and similar
;;; powerlists, keep the same structure.

(defthm regular-similar-tie-zip
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (p-similar-p (p-zip x y)
			(p-tie x y))))

;;; Finally, we can prove a basic theorem about constructing regular powerlists
;;; using zip.  The only requirement is that the two lists be regular and
;;; similar to each other (and we can omit the requirement that one of the
;;; lists be regular due to the theorem similar-regular).  Note how this
;;; mirrors the definition of regular, which uses tie instead of zip.  In light
;;; of the previous theorem, this result is trivial.

(defthm zip-regular
  (implies (and (p-regular-p x)
		(p-similar-p x y))
	   (p-regular-p (p-zip x y))))

;;; In the spirit of code reuse (proof reuse?) we now prove a slew of theorems
;;; about applying functions to the elements of powerlists.  What we're after
;;; are theorems like "if you construct a new powerlists by applying a function
;;; to each member of another powerlists, then it doesn't matter if you use tie
;;; or zip to do it".  Also, if we're walking down two lists and applying a
;;; function to corresponding elements, then it's interesting to see what
;;; properties of the function carry over to the function on powerlists.

(encapsulate
 ((type-fn (x) t)			; A type restriction function on the members
  (equiv (x y) t)			; An equivalence class
  (fn1 (x) t)				; Arbitrary unary function on powerlist members
  (fn1-num (x) t)			; Numeric unary function on powerlist members
  (fn2       (x y) t)			; Arbitrary binary function on members
  (fn2-comm  (x y) t)			; Commutative binary function on members
  (fn2-assoc (x y) t)			; Transitive binary function on members
  (fn2-accum (x y) t))			; "Accumulator" binary function (comm/assoc)

 (local (defun type-fn   (x)   (equal x x)))
 (local (defun equiv     (x y) (equal x y)))
 (local (defun fn1       (x)   (fix x)))
 (local (defun fn1-num   (x)   (fix x)))
 (local (defun fn2       (x y) (+ (fix x) (fix y))))
 (local (defun fn2-comm  (x y) (+ (fix x) (fix y))))
 (local (defun fn2-assoc (x y) (+ (fix x) (fix y))))
 (local (defun fn2-accum (x y) (+ (fix x) (fix y))))

 ;;
 ;; We assume our type function is boolean, and our equivalence class is
 ;;
 (defthm type-fn-boolean
   (booleanp (type-fn x))
   :rule-classes (:type-prescription))
 (defequiv equiv)

 ;;
 ;; An important restriction.  The functions that operate on scalars should
 ;; return scalar values.  Otherwise, it would be possible for them to return
 ;; powerlists, and then we wouldn't know the structure of the resulting list.
 ;;
 (defthm fn1-scalar
   (implies (not (powerlist-p x))
	    (not (powerlist-p (fn1 x)))))

 (defthm fn1-num-scalar
   (implies (not (powerlist-p x))
	    (not (powerlist-p (fn1-num x)))))

 (defthm fn1-num-numeric
   (acl2-numberp (fn1-num x))
   :rule-classes (:type-prescription))

 (defthm fn2-scalar
   (implies (or (not (powerlist-p x))
		(not (powerlist-p y)))
	    (not (powerlist-p (fn2 x y)))))

 (defthm fn2-comm-scalar
   (implies (or (not (powerlist-p x))
		(not (powerlist-p y)))
	    (not (powerlist-p (fn2-comm x y)))))

 (defthm fn2-assoc-scalar
   (implies (or (not (powerlist-p x))
		(not (powerlist-p y)))
	    (not (powerlist-p (fn2-assoc x y)))))

 ;;
 ;; And of course, fn2-comm and fn2-assoc are commutative and associative as
 ;; advertised
 ;;
 (defthm fn2-commutative
   (equal (fn2-comm x y) (fn2-comm y x)))

 (defthm fn2-associative
   (equal (fn2-assoc (fn2-assoc x y) z)
	  (fn2-assoc x (fn2-assoc y z))))

 ;;
 ;; In a similar vein, our accumulator function does serve as a valid
 ;; accumulator -- i.e., it is associative and commutative
 ;;
 (defthm fn2-accum-commutative
   (equiv (fn2-accum x y) (fn2-accum y x)))

 (defthm fn2-accum-associative
   (equiv (fn2-accum (fn2-accum x y) z)
	  (fn2-accum x (fn2-accum y z))))

 (defcong equiv equiv (fn2-accum x y) 1)
 (defcong equiv equiv (fn2-accum x y) 2)
 )

;;; We start out with properties of applying the unary function to the members
;;; of a powerlist.  We can do this recursing on either unzip or untie.

(defun a-zip-fn1 (x)
  "Apply fn1 to x recursing with unzip"
  (if (powerlist-p x)
      (p-zip (a-zip-fn1 (p-unzip-l x)) (a-zip-fn1 (p-unzip-r x)))
    (fn1 x)))

(defun b-tie-fn1 (x)
  "Apply fn1 to x recursing with untie"
  (if (powerlist-p x)
      (p-tie (b-tie-fn1 (p-untie-l x)) (b-tie-fn1 (p-untie-r x)))
    (fn1 x)))

;;; Whether we use untie or unzip as our recursion scheme, we should end up
;;; with the same answer.

(defthm b-tie-fn1-same-as-a-zip-fn1
  (equal (b-tie-fn1 x)
	 (a-zip-fn1 x)))

;;; Moreover, the resulting powerlist has the same structure as the original
;;; list.  Of course, this assumes the unary function does not convert a scalar
;;; object into a powerlist!

(defthm a-zip-fn1-similar
  (p-similar-p (a-zip-fn1 x) x))

(defthm b-tie-fn1-similar
  (p-similar-p (b-tie-fn1 x) x))

;;; A simple consequence of the above is that the resulting powerlist is
;;; regular if the original list is regular

(defthm a-zip-fn1-regular
  (equal (p-regular-p (a-zip-fn1 x))
	 (p-regular-p x))
  :hints (("Goal"
	   :use ((:instance a-zip-fn1-similar)
		 (:instance similar-regular
			    (x (a-zip-fn1 x))
			    (y x))
		 (:instance similar-regular
			    (x x)
			    (y (a-zip-fn1 x)))))))

(defthm b-tie-fn1-regular
  (equal (p-regular-p (b-tie-fn1 x))
	 (p-regular-p x)))

;;; Now, we consider what happens when we apply a binary function pairwise to
;;; two powerlists.  As before, we can recurse using either unzip or untie.

(defun a-zip-fn2 (x y)
  "Apply fn2 to x and y recursing with unzip"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-zip (a-zip-fn2 (p-unzip-l x) (p-unzip-l y))
	     (a-zip-fn2 (p-unzip-r x) (p-unzip-r y)))
    (fn2 x y)))

(defun b-tie-fn2 (x y)
  "Apply fn2 to x and y recursing with untie"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (b-tie-fn2 (p-untie-l x) (p-untie-l y))
	     (b-tie-fn2 (p-untie-r x) (p-untie-r y)))
    (fn2 x y)))

;;; When dealing with similar powerlists, we get the same results if we recurse
;;; using unzip or untie.  This theorem does not remain true if we get rid of
;;; the similarity requirement.  This is because the "left-over" pieces when we
;;; reach a leaf on one of the trees will be different if we're unzipping or
;;; untieing.

(defthm b-tie-fn2-same-as-a-zip-fn2
  (implies (p-similar-p x y)
	   (equal (a-zip-fn2 x y)
		  (b-tie-fn2 x y)))
  :hints (("Goal" :in-theory (disable zip-unzip))))

;;; As in the unary case, the result of applying a binary function pairwise to
;;; two powerlists is similar.  However, we require the original lists to be
;;; similar, since our definitions stop the recursion as soon as one list
;;; bottoms out.

(defthm a-zip-fn2-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (a-zip-fn2 x y) x)))

(defthm b-tie-fn2-similar-1
  (implies (p-similar-p x y)
	   (p-similar-p (b-tie-fn2 x y) x))
  :hints (("Goal"
	   :use ((:instance b-tie-fn2-same-as-a-zip-fn2)
		 (:instance a-zip-fn2-similar-1))
	   :in-theory (disable b-tie-fn2-same-as-a-zip-fn2
			       a-zip-fn2-similar-1))))

(defthm a-zip-fn2-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (a-zip-fn2 x y) y)))

(defthm b-tie-fn2-similar-2
  (implies (p-similar-p x y)
	   (p-similar-p (b-tie-fn2 x y) y)))

;;; We can also prove that if a powerlist is replaced with a similar powerlist
;;; in one of these operations, the result will retain the same shape.

(defcong p-similar-p p-similar-p (b-tie-fn2 x y) 1)
(defcong p-similar-p p-similar-p (b-tie-fn2 x y) 2)
(defcong p-similar-p p-similar-p (a-zip-fn2 x y) 1)
(defcong p-similar-p p-similar-p (a-zip-fn2 x y) 2)

;;; Finally, we find that if we apply our operator to two similar and regular
;;; powerlists, then the result is regular.  This is just a corollary of the
;;; theorems above.

(defthm b-tie-fn2-regular
  (implies (p-similar-p x y)
	   (equal (p-regular-p (b-tie-fn2 x y))
		  (and (p-regular-p x)
		       (p-regular-p y))))
  :hints (("Subgoal *1/4''"
	   :use (:instance similar-regular
			   (x (powerlist-car x))
			   (y (powerlist-cdr x)))
	   :in-theory (disable similar-regular))))

(defthm a-zip-fn2-regular
  (implies (p-similar-p x y)
	   (equal (p-regular-p (a-zip-fn2 x y))
		  (and (p-regular-p x)
		       (p-regular-p y)))))

;;; Now, we define the functions derived to apply our commutative function to
;;; the powerlist elements.  We can prove that the resulting functions on
;;; powerlists are also commutative.

(defun a-zip-fn2-comm (x y)
  "Apply fn2-comm to x and y recursing with unzip"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-zip (a-zip-fn2-comm (p-unzip-l x) (p-unzip-l y))
	     (a-zip-fn2-comm (p-unzip-r x) (p-unzip-r y)))
    (fn2-comm x y)))

(defun b-tie-fn2-comm (x y)
  "Apply fn2-comm to x and y recursing with untie"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (b-tie-fn2-comm (p-untie-l x) (p-untie-l y))
	     (b-tie-fn2-comm (p-untie-r x) (p-untie-r y)))
    (fn2-comm x y)))

(defthm a-zip-fn2-comm-commutes
  (equal (a-zip-fn2-comm x y)
	 (a-zip-fn2-comm y x)))

(defthm b-tie-fn2-comm-commutes
  (equal (b-tie-fn2-comm x y)
	 (b-tie-fn2-comm y x)))

;;; Now we do the same for our transitive function.  Again, we find that the
;;; resulting functions on powerlists are transitive, but only for similar
;;; lists.

(defun a-zip-fn2-assoc (x y)
  "Apply fn2-assoc to x and y recursing with unzip"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-zip (a-zip-fn2-assoc (p-unzip-l x) (p-unzip-l y))
	     (a-zip-fn2-assoc (p-unzip-r x) (p-unzip-r y)))
    (fn2-assoc x y)))

(defun b-tie-fn2-assoc (x y)
  "Apply fn2-assoc to x and y recursing with untie"
  (if (and (powerlist-p x) (powerlist-p y))
      (p-tie (b-tie-fn2-assoc (p-untie-l x) (p-untie-l y))
	     (b-tie-fn2-assoc (p-untie-r x) (p-untie-r y)))
    (fn2-assoc x y)))

(defthm a-zip-fn2-assoc-transitive
  (implies (and (p-similar-p x y)
		(p-similar-p y z))
	   (equal (a-zip-fn2-assoc (a-zip-fn2-assoc x y) z)
		  (a-zip-fn2-assoc x (a-zip-fn2-assoc y z)))))

(defthm b-tie-fn2-assoc-transitive
  (implies (and (p-similar-p x y)
		(p-similar-p y z))
	   (equal (b-tie-fn2-assoc (b-tie-fn2-assoc x y) z)
		  (b-tie-fn2-assoc x (b-tie-fn2-assoc y z)))))

;;; Next we define an accumulator or aggregator function over powerlists.  For
;;; example, given a powerlist of integers, we can find its sum, number of
;;; elements, etc.  What we can't do is find its "difference", since that's not
;;; a well-defined term.  The reason is that the binary minus operator is not
;;; commutative or associative, so the "difference" of a powerlist will differ
;;; on how we decide to traverse it.  We generalize the notion by allowing the
;;; values aggregated to be computed by a scalar function of the leaves -- this
;;; is especially useful for testing functions, which test to see if the leaves
;;; meet a certain property (e.g., a type-checking function)

(defun a-zip-fn2-accum-fn1 (x)
  "Run fn-accum over fn1 of all elements of a powerlist, recursing with unzip"
  (if (powerlist-p x)
      (fn2-accum (a-zip-fn2-accum-fn1 (p-unzip-l x))
		 (a-zip-fn2-accum-fn1 (p-unzip-r x)))
    (fn1 x)))

(defun b-tie-fn2-accum-fn1 (x)
  "Run fn-accum over fn1 of all elements of a powerlist, recursing with untie"
  (if (powerlist-p x)
      (fn2-accum (b-tie-fn2-accum-fn1 (p-untie-l x))
		 (b-tie-fn2-accum-fn1 (p-untie-r x)))
    (fn1 x)))

;;; To prove that the two accumulators above are equivalent, we start out by
;;; showing what happens when you zip two lists that satisfy the condition
;;; testing with zips.  That, of course, is trivial from the definition.  Then,
;;; we see what happens to the zip when you test the condition using the untie
;;; recursion.  That's not so trivial.  But, we need these results in the
;;; inductive proof that the two functions are equivalent.

(defun untie-on-x-and-y (x y)
  "Walk down both x and y looking at corresponding unties"
  (declare (xargs :guard (p-similar-p x y)))
  (if (powerlist-p x)
      (list (untie-on-x-and-y (p-untie-l x) (p-untie-l y))
	    (untie-on-x-and-y (p-untie-r x) (p-untie-r y)))
    (list x y)))
(defthm zip-a-zip-fn2-accum-fn1
  (equiv (a-zip-fn2-accum-fn1 (p-zip x y))
	 (fn2-accum (a-zip-fn2-accum-fn1 x)
		    (a-zip-fn2-accum-fn1 y))))

;;; ACL2 doesn't really like reasoning about the equiv/fn2-accum,
;;; because the associative and commutative rules aren't strong enough
;;; to canonicize an arbitrary nest of fn2-accums.  There's an old
;;; trick, back from the nqthm days of proving the rewrite rule
;;; (+ i (+ j k)) -> (+ j (+ i k)) which solves the problem.

(defthm fnt-accum-assoc-trick
  (equiv (fn2-accum y (fn2-accum x z))
	 (fn2-accum x (fn2-accum y z)))
  :hints (("Goal"
	   :use ((:instance fn2-accum-associative (x y) (y x) (z z))
		 (:instance fn2-accum-associative (x x) (y y) (z z))
		 (:instance fn2-accum-commutative))
	   :in-theory (disable fn2-accum-associative fn2-accum-commutative))))

(defthm zip-b-tie-fn2-accum-fn1
  (equiv (b-tie-fn2-accum-fn1 (p-zip x y))
	 (fn2-accum (b-tie-fn2-accum-fn1 x)
		    (b-tie-fn2-accum-fn1 y)))
  :hints (("Goal"
	   :induct (untie-on-x-and-y x y))))

(defthm a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
  (equiv (b-tie-fn2-accum-fn1 x)
	 (a-zip-fn2-accum-fn1 x))
  :rule-classes nil)

(defthm tie-b-tie-fn2-accum-fn1
  (equiv (b-tie-fn2-accum-fn1 (p-tie x y))
	 (fn2-accum (b-tie-fn2-accum-fn1 x)
		    (b-tie-fn2-accum-fn1 y))))

(defthm tie-a-zip-fn2-accum-fn1
  (equiv (a-zip-fn2-accum-fn1 (p-tie x y))
	 (fn2-accum (a-zip-fn2-accum-fn1 x)
		    (a-zip-fn2-accum-fn1 y)))
  :hints (("Goal"
	   :use ((:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x (p-tie x y)))
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x y))
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1)
		 (:instance tie-b-tie-fn2-accum-fn1)))))

;;; Now, we can prove some common properties useful when using induction.

(defthm unzip-a-zip-fn2-accum-fn1
  (implies (powerlist-p x)
	   (equiv (fn2-accum (a-zip-fn2-accum-fn1 (p-unzip-l x))
			     (a-zip-fn2-accum-fn1 (p-unzip-r x)))
		  (a-zip-fn2-accum-fn1 x)))
  :rule-classes nil)

(defthm unzip-b-tie-fn2-accum-fn1
  (implies (powerlist-p x)
	   (equiv (fn2-accum
		   (b-tie-fn2-accum-fn1 (p-unzip-l x))
		   (b-tie-fn2-accum-fn1 (p-unzip-r x)))
		  (b-tie-fn2-accum-fn1 x)))
  :hints (("Goal"
	   :use ((:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1)
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x (p-unzip-l x)))
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x (p-unzip-r x)))
		 (:instance unzip-a-zip-fn2-accum-fn1))))
  :rule-classes nil)

(defthm untie-b-tie-fn2-accum-fn1
  (implies (powerlist-p x)
	   (equiv (fn2-accum (b-tie-fn2-accum-fn1 (p-untie-l x))
			     (b-tie-fn2-accum-fn1 (p-untie-r x)))
		  (b-tie-fn2-accum-fn1 x)))
  :rule-classes nil)

(defthm untie-a-zip-fn2-accum-fn1
  (implies (powerlist-p x)
	   (equiv (fn2-accum (a-zip-fn2-accum-fn1 (p-untie-l x))
			     (a-zip-fn2-accum-fn1 (p-untie-r x)))
		  (a-zip-fn2-accum-fn1 x)))
  :hints (("Goal"
	   :use ((:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1)
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x (p-untie-l x)))
		 (:instance a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
			    (x (p-untie-r x)))
		 (:instance untie-b-tie-fn2-accum-fn1))))
  :rule-classes nil)

;;; The above accumulators are really nice.  Perhaps the most common are going
;;; to be based on '+' and 'and', with equivalence relations 'equal' and 'iff'
;;; respectively.  To save time later, we go ahead and specialize the main
;;; results for these two cases here.

;;; We start with the '+' case....

(defun a-zip-plus-fn1 (x)
  "Add the fn1 of all elements of a powerlist, recursing with unzip"
  (if (powerlist-p x)
      (+ (a-zip-plus-fn1 (p-unzip-l x))
	 (a-zip-plus-fn1 (p-unzip-r x)))
    (fn1-num x)))

(defun b-tie-plus-fn1 (x)
  "Add the fn1 of all elements of a powerlist, recursing with untie"
  (if (powerlist-p x)
      (+ (b-tie-plus-fn1 (p-untie-l x))
	 (b-tie-plus-fn1 (p-untie-r x)))
    (fn1-num x)))

(defthm a-zip-plus-fn1-same-as-b-tie-plus-fn1
  (equal (b-tie-plus-fn1 x)
	 (a-zip-plus-fn1 x))
  :hints (("Goal"
	   :by (:functional-instance
		a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
		(a-zip-fn2-accum-fn1 a-zip-plus-fn1)
		(b-tie-fn2-accum-fn1 b-tie-plus-fn1)
		(equiv equal)
		(fn2-accum binary-+))))
  :rule-classes nil)

(defthm zip-a-zip-plus-fn1
  (equal (a-zip-plus-fn1 (p-zip x y))
	 (+ (a-zip-plus-fn1 x)
	    (a-zip-plus-fn1 y)))
  :hints (("Goal"
	   :by (:functional-instance zip-a-zip-fn2-accum-fn1
				     (a-zip-fn2-accum-fn1 a-zip-plus-fn1)
				     (equiv equal)
				     (fn2-accum binary-+)))))

(defthm zip-b-tie-plus-fn1
  (equal (b-tie-plus-fn1 (p-zip x y))
	 (+ (b-tie-plus-fn1 x)
	    (b-tie-plus-fn1 y)))
  :hints (("Goal"
	   :by (:functional-instance zip-b-tie-fn2-accum-fn1
				     (b-tie-fn2-accum-fn1 b-tie-plus-fn1)
				     (equiv equal)
				     (fn2-accum binary-+)))))

(defthm tie-a-zip-plus-fn1
  (equal (a-zip-plus-fn1 (p-tie x y))
	 (+ (a-zip-plus-fn1 x)
	    (a-zip-plus-fn1 y)))
  :hints (("Goal"
	   :by (:functional-instance tie-a-zip-fn2-accum-fn1
				     (a-zip-fn2-accum-fn1 a-zip-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+)))))

(defthm tie-b-tie-plus-fn1
  (equal (b-tie-plus-fn1 (p-tie x y))
	 (+ (b-tie-plus-fn1 x)
	    (b-tie-plus-fn1 y)))
  :hints (("Goal"
	   :by (:functional-instance tie-b-tie-fn2-accum-fn1
				     (b-tie-fn2-accum-fn1 b-tie-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+)))))

(defthm unzip-a-zip-plus-fn1
  (implies (powerlist-p x)
	   (equal (a-zip-plus-fn1 x)
		  (+ (a-zip-plus-fn1 (p-unzip-l x))
		     (a-zip-plus-fn1 (p-unzip-r x)))))
  :hints (("Goal"
	   :by (:functional-instance unzip-a-zip-fn2-accum-fn1
				     (a-zip-fn2-accum-fn1 a-zip-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+))))
  :rule-classes nil)

(defthm unzip-b-tie-plus-fn1
  (implies (powerlist-p x)
	   (equal (b-tie-plus-fn1 x)
		  (+ (b-tie-plus-fn1 (p-unzip-l x))
		     (b-tie-plus-fn1 (p-unzip-r x)))))
  :hints (("Goal"
	   :by (:functional-instance unzip-b-tie-fn2-accum-fn1
				     (b-tie-fn2-accum-fn1 b-tie-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+))))
  :rule-classes nil)

(defthm untie-b-tie-plus-fn1
  (implies (powerlist-p x)
	   (equal (b-tie-plus-fn1 x)
		  (+ (b-tie-plus-fn1 (p-untie-l x))
		     (b-tie-plus-fn1 (p-untie-r x)))))
  :hints (("Goal"
	   :by (:functional-instance untie-b-tie-fn2-accum-fn1
				     (b-tie-fn2-accum-fn1 b-tie-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+))))
  :rule-classes nil)

(defthm untie-a-zip-plus-fn1
  (implies (powerlist-p x)
	   (equal (a-zip-plus-fn1 x)
		  (+ (a-zip-plus-fn1 (p-untie-l x))
		     (a-zip-plus-fn1 (p-untie-r x)))))
  :hints (("Goal"
	   :by (:functional-instance untie-a-zip-fn2-accum-fn1
				     (a-zip-fn2-accum-fn1 a-zip-plus-fn1)
				     (equiv equal)
				     (fn1 fn1-num)
				     (fn2-accum binary-+))))
  :rule-classes nil)

;;; Great!  Now, we do with the 'and' case....

(defun a-zip-and-fn1 (x)
  "Add the fn1 of all elements of a powerlist, recursing with unzip"
  (if (powerlist-p x)
      (and (a-zip-and-fn1 (p-unzip-l x))
	   (a-zip-and-fn1 (p-unzip-r x)))
    (fn1 x)))

(defun b-tie-and-fn1 (x)
  "Add the fn1 of all elements of a powerlist, recursing with untie"
  (if (powerlist-p x)
      (and (b-tie-and-fn1 (p-untie-l x))
	   (b-tie-and-fn1 (p-untie-r x)))
    (fn1 x)))

(local
 (defun my-and (x y)
   (and x y)))

(defthm a-zip-and-fn1-same-as-b-tie-and-fn1
  (iff (b-tie-and-fn1 x)
       (a-zip-and-fn1 x))
  :hints (("Goal"
	   :by (:functional-instance
		a-zip-fn2-accum-fn1-same-as-b-tie-fn2-accum-fn1
		(a-zip-fn2-accum-fn1 a-zip-and-fn1)
		(b-tie-fn2-accum-fn1 b-tie-and-fn1)
		(equiv iff)
		(fn2-accum my-and))))
  :rule-classes nil)

(defthm zip-a-zip-and-fn1
  (iff (a-zip-and-fn1 (p-zip x y))
       (and (a-zip-and-fn1 x)
	    (a-zip-and-fn1 y)))
  :hints (("Goal"
	   :use (:functional-instance zip-a-zip-fn2-accum-fn1
				      (a-zip-fn2-accum-fn1 a-zip-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and)))))

(defthm zip-b-tie-and-fn1
  (iff (b-tie-and-fn1 (p-zip x y))
       (and (b-tie-and-fn1 x)
	    (b-tie-and-fn1 y)))
  :hints (("Goal"
	   :use (:functional-instance zip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 b-tie-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and)))))

(defthm tie-a-zip-and-fn1
  (iff (a-zip-and-fn1 (p-tie x y))
       (and (a-zip-and-fn1 x)
	    (a-zip-and-fn1 y)))
  :hints (("Goal"
	   :use (:functional-instance tie-a-zip-fn2-accum-fn1
				      (a-zip-fn2-accum-fn1 a-zip-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and)))))

(defthm tie-b-tie-and-fn1
  (iff (b-tie-and-fn1 (p-tie x y))
       (and (b-tie-and-fn1 x)
	    (b-tie-and-fn1 y)))
  :hints (("Goal"
	   :use (:functional-instance tie-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 b-tie-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and)))))

(defthm unzip-a-zip-and-fn1
  (implies (powerlist-p x)
	   (iff (a-zip-and-fn1 x)
		(and (a-zip-and-fn1 (p-unzip-l x))
		     (a-zip-and-fn1 (p-unzip-r x)))))
  :hints (("Goal"
	   :use (:functional-instance unzip-a-zip-fn2-accum-fn1
				      (a-zip-fn2-accum-fn1 a-zip-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and))))
  :rule-classes nil)

(defthm unzip-b-tie-and-fn1
  (implies (powerlist-p x)
	   (iff (b-tie-and-fn1 x)
		(and (b-tie-and-fn1 (p-unzip-l x))
		     (b-tie-and-fn1 (p-unzip-r x)))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 b-tie-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and))))
  :rule-classes nil)

(defthm untie-b-tie-and-fn1
  (implies (powerlist-p x)
	   (iff (b-tie-and-fn1 x)
		(and (b-tie-and-fn1 (p-untie-l x))
		     (b-tie-and-fn1 (p-untie-r x)))))
  :hints (("Goal"
	   :use (:functional-instance untie-b-tie-fn2-accum-fn1
				      (b-tie-fn2-accum-fn1 b-tie-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and))))
  :rule-classes nil)

(defthm untie-a-zip-and-fn1
  (implies (powerlist-p x)
	   (iff (a-zip-and-fn1 x)
		(and (a-zip-and-fn1 (p-untie-l x))
		     (a-zip-and-fn1 (p-untie-r x)))))
  :hints (("Goal"
	   :use (:functional-instance untie-a-zip-fn2-accum-fn1
				      (a-zip-fn2-accum-fn1 a-zip-and-fn1)
				      (equiv iff)
				      (fn2-accum my-and))))
  :rule-classes nil)

;;; Now we use our type function and extend that to powerlists.  That is, we're
;;; interested in powerlists made up of elements that satisfy type-fn.  We can
;;; do this by recursing on either unzip or untie, and the result should be the
;;; same.  We'll make use of the "and" accumulator above.

(defun a-zip-list-of-type-fn (x)
  "Check that a powerlist has only type-fn elements, recursing with unzip"
  (if (powerlist-p x)
      (and (a-zip-list-of-type-fn (p-unzip-l x))
	   (a-zip-list-of-type-fn (p-unzip-r x)))
    (type-fn x)))

(defun b-tie-list-of-type-fn (x)
  "Check that a powerlist has only type-fn elements, recursing with untie"
  (if (powerlist-p x)
      (and (b-tie-list-of-type-fn (p-untie-l x))
	   (b-tie-list-of-type-fn (p-untie-r x)))
    (type-fn x)))

(defthm a-zip-type-same-as-b-tie-type
  (equal (b-tie-list-of-type-fn x)
	 (a-zip-list-of-type-fn x))
  :hints (("Goal"
	   :use (:functional-instance a-zip-and-fn1-same-as-b-tie-and-fn1
				      (a-zip-and-fn1 a-zip-list-of-type-fn)
				      (b-tie-and-fn1 b-tie-list-of-type-fn)
				      (fn1 type-fn))))
  :rule-classes nil)

(defthm zip-a-zip-list-of-type-fn
  (equal (a-zip-list-of-type-fn (p-zip x y))
	 (and (a-zip-list-of-type-fn x)
	      (a-zip-list-of-type-fn y)))
  :hints (("Goal"
	   :in-theory (disable zip-a-zip-and-fn1)
	   :use (:functional-instance zip-a-zip-and-fn1
				      (a-zip-and-fn1 a-zip-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm zip-b-tie-list-of-type-fn
  (equal (b-tie-list-of-type-fn (p-zip x y))
	 (and (b-tie-list-of-type-fn x)
	      (b-tie-list-of-type-fn y)))
  :hints (("Goal"
	   :use (:functional-instance zip-b-tie-and-fn1
				      (b-tie-and-fn1 b-tie-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm tie-a-zip-list-of-type-fn
  (equal (a-zip-list-of-type-fn (p-tie x y))
	 (and (a-zip-list-of-type-fn x)
	      (a-zip-list-of-type-fn y)))
  :hints (("Goal"
	   :use (:functional-instance tie-a-zip-and-fn1
				      (a-zip-and-fn1 a-zip-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm tie-b-tie-list-of-type-fn
  (equal (b-tie-list-of-type-fn (p-tie x y))
	 (and (b-tie-list-of-type-fn x)
	      (b-tie-list-of-type-fn y)))
  :hints (("Goal"
	   :use (:functional-instance tie-b-tie-and-fn1
				      (b-tie-and-fn1 b-tie-list-of-type-fn)
				      (fn1 type-fn)))))

;;; Now, we can prove the "inductive proof obligation" lemmas about the types
;;; of powerlists derived by unzipping/untieing a powerlist whose elements are
;;; all of type type-fn.

(defthm unzip-a-zip-list-of-type-fn
  (implies (powerlist-p x)
	   (equal (a-zip-list-of-type-fn x)
		  (and (a-zip-list-of-type-fn (p-unzip-l x))
		       (a-zip-list-of-type-fn (p-unzip-r x)))))
  :hints (("Goal"
	   :use (:functional-instance unzip-a-zip-and-fn1
				      (a-zip-and-fn1 a-zip-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm unzip-b-tie-list-of-type-fn
  (implies (powerlist-p x)
	   (equal (b-tie-list-of-type-fn x)
		  (and (b-tie-list-of-type-fn (p-unzip-l x))
		       (b-tie-list-of-type-fn (p-unzip-r x)))))
  :hints (("Goal"
	   :use (:functional-instance unzip-b-tie-and-fn1
				      (b-tie-and-fn1 b-tie-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm untie-a-zip-list-of-type-fn
  (implies (powerlist-p x)
	   (equal (a-zip-list-of-type-fn x)
		  (and (a-zip-list-of-type-fn (p-untie-l x))
		       (a-zip-list-of-type-fn (p-untie-r x)))))
  :hints (("Goal"
	   :use (:functional-instance untie-a-zip-and-fn1
				      (a-zip-and-fn1 a-zip-list-of-type-fn)
				      (fn1 type-fn)))))

(defthm untie-b-tie-list-of-type-fn
  (implies (powerlist-p x)
	   (equal (b-tie-list-of-type-fn x)
		  (and (b-tie-list-of-type-fn (p-untie-l x))
		       (b-tie-list-of-type-fn (p-untie-r x)))))
  :hints (("Goal"
	   :use (:functional-instance untie-b-tie-and-fn1
				      (b-tie-and-fn1 b-tie-list-of-type-fn)
				      (fn1 type-fn)))
	  ("Goal'" ; modified for v2-7 because more constraint proofs are bypassed
	   :in-theory (disable b-tie-list-of-type-fn))))

;;; Now, we undertake the task of defining typical induction strategies.  This
;;; is so that all the books using powerlists don't have to define their own
;;; versions of these common inductions that ACL2 doesn't seem to discover for
;;; itself.

(defun unzip-on-x-and-y (x y)
  "Walk down both x and y looking at corresponding unzips"
  (declare (xargs :guard (p-similar-p x y)))
  (if (powerlist-p x)
      (list (unzip-on-x-and-y (p-unzip-l x) (p-unzip-l y))
	    (unzip-on-x-and-y (p-unzip-r x) (p-unzip-r y)))
    (list x y)))
(defun unzip-swap-on-x-and-y (x y)
  "Walk down x and y looking at opposite unzips"
  (declare (xargs :guard (and (p-regular-p x) (p-similar-p x y))))
  (if (powerlist-p x)
      (list (unzip-swap-on-x-and-y (p-unzip-l x) (p-unzip-r y))
	    (unzip-swap-on-x-and-y (p-unzip-r x) (p-unzip-l y)))
    (list x y)))
(defun unzip-on-x1-x2-y1-and-y2 (x1 x2 y1 y2)
  "Walk down x1,y1 and x2,y2 looking at corresponding unzips"
  (declare (xargs :guard (and (p-similar-p x1 x2)
			      (p-similar-p x1 y1)
			      (p-similar-p x1 y2))))
  (if (powerlist-p x1)
      (list (unzip-on-x1-x2-y1-and-y2 (p-unzip-l x1) (p-unzip-l x2)
				      (p-unzip-l y1) (p-unzip-l y2))
	    (unzip-on-x1-x2-y1-and-y2 (p-unzip-r x1) (p-unzip-r x2)
				      (p-unzip-r y1) (p-unzip-r y2)))
    (list x1 x2 y1 y2)))
(defun unzip-swap-on-x1-x2-y1-and-y2 (x1 x2 y1 y2)
  "Walk down x1,y1 and x2,y2 looking at opposite unzips"
  (declare (xargs :guard (and (p-regular-p x1)
			      (p-similar-p x1 x2)
			      (p-similar-p x1 y1)
			      (p-similar-p x1 y2))))
  (if (powerlist-p x1)
      (list (unzip-swap-on-x1-x2-y1-and-y2 (p-unzip-l x1) (p-unzip-l x2)
					   (p-unzip-r y1) (p-unzip-r y2))
	    (unzip-swap-on-x1-x2-y1-and-y2 (p-unzip-r x1) (p-unzip-r x2)
					   (p-unzip-l y1) (p-unzip-l y2)))

    (list x1 x2 y1 y2)))

