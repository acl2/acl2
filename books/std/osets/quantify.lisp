; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>


; quantify.lisp
;
; This is an optional extension of the sets library, and is not included by
; default when you run (include-book "top").
;
;
; Constructive Quantification over Sets and Lists.
;
; We create the macro, quantify-predicate, which introduces the following
; functions for any arbitrary predicate.
;
;     all<predicate>           all<not-predicate>
;     exists<predicate>        exists<not-predicate>
;     find<predicate>          find<not-predicate>
;     filter<predicate>        filter<not-predicate>
;
;     all-list<predicate>      all-list<not-predicate>
;     exists-list<predicate>   exists-list<not-predicate>
;     find-list<predicate>     find-list<not-predicate>
;     filter-list<predicate>   filter-list<not-predicate>
;
; In addition to introducing these functions, an entire rewriting strategy is
; introduced for reasoning about these functions with respect to sets and
; lists.
;
;
; Introductory Examples.
;
; Here are some of the most simple examples.  All of these predicates have only
; a single argument, and their guard is "t".
;
;     (SET::quantify-predicate (integerp x))
;     (SET::quantify-predicate (symbolp x))
;     (SET::quantify-predicate (rationalp x))
;     (SET::quantify-predicate (natp x))
;
; Notice that you cannot use macros here.  For example, the following is an
; error: (quantify-predicate (real/rationalp x)).  Once you have done the
; above, you can now run these functions, e.g.,
;
;     (SET::all<integerp> '(1 2 3)) = t
;     (SET::all<not-integerp> '(a b c)) = t
;     (SET::find<symbolp> '(1 2 3 a b c)) = a
;
;
; Controlling Packages.
;
; As you can see, all of these functions are introduced in the SETS package by
; default.  If you'd like them to be in a different place instead, you can
; specify the :in-package-of argument and provide a symbol from some other
; package.  For example, since defthm is in the ACL2 package, we might write:
;
;     (SET::quantify-predicate (eqlablep x)
;       :in-package-of defthm)
;
; And then the functions all<integerp>, all<not-integerp>, and so forth will be
; in the ACL2 package instead of the LISTS package.
;
;
; Multi-Argument Predicates.
;
; You can also quantify over predicates with many arguments.  As an example, we
; introduce the function lessp as follows:
;
;     (defun lessp (a b)
;       (declare (xargs :guard t))
;       (< (rfix a) (rfix b)))
;
;     (quantify-predicate (lessp a b))
;
; We could now ask, is every element in a set less than some maximum value?
; For example:
;
;     (all<lessp> '(1 2 3) 6) = t
;     (all<lessp> '(1 2 3) 2) = nil
;
;
; Supporting Guards.
;
; If efficiency is important, our predicate may have guards and we may want to
; put guards on the introduced functions.  For example, we might write
; fast-lessp below:
;
;     (defun fast-lessp (a b)
;       (declare (xargs :guard (and (rationalp a)
;                                   (rationalp b))))
;       (< a b))
;
; Now we need to supply an extra :guard argument so that the guards of
; all<fast-lessp>, exists<fast-lessp>, and so forth can be verified.
;
; When writing this guard, the list which all-list<fast-lessp> and so forth are
; iterating over will be called ?list, and the set that all<fast-lessp> and so
; forth are iterating over will be called ?set.  The other arguments will all
; be named with whatever names you gave them when you ran quantify-predicate.
; For example, below we name fast-lessp's second argument "max", so it will be
; named "max" in our guards as well.
;
; Here's an example:
;
;     (in-package "ACL2")
;
;     (SET::quantify-predicate (rationalp x)
;       :in-package-of defthm)
;
;     (SET::quantify-predicate (fast-lessp x max)
;       :set-guard  ((all<rationalp> ?set))
;       :list-guard ((all-list<rationalp> ?list))
;       :arg-guard  ((rationalp max))
;       :in-package-of defthm)
;
;
;
; Disabling the theory.
;
; Calling quantify-predicate will result in a lot of theorems being introduced.
; You can disable all of these theorems by using the deftheory event
; theory<predicate>.  For example,
;
;     (in-theory (disable theory<integerp>))
;     (in-theory (disable theory<fast-lessp>))
;
; And so forth.

(in-package "SET")
(include-book "top")
(set-verify-guards-eagerness 2)


(local (in-theory (enable expensive-rules definitions)))
; We introduce our theory as a constant so that we can derive new instances of
; it for concrete predicates

(defconst *positive-functions* '(

; We introduce "list versions" of the functions so that we can reason through
; mergesorts.

  (defun all-list (x)
    (declare (xargs :guard (true-listp x)
                    ;; SUBTLE/AWFUL: Make sure each of these functions has the
                    ;; verify-guards form directly in the declare.  We search
                    ;; for the it explicitly when we do our guard replacements.
                    :verify-guards nil))
    (if (endp x)
	t
      (and (predicate (car x))
	   (all-list (cdr x)))))

  (defun exists-list (x)
    (declare (xargs :guard (true-listp x)
                    :verify-guards nil))
    (cond ((endp x) nil)
	  ((predicate (car x)) t)
	  (t (exists-list (cdr x)))))

  (defun find-list (x)
    (declare (xargs :guard (true-listp x)
                    :verify-guards nil))
    (cond ((endp x) nil)
	  ((predicate (car x)) (car x))
	  (t (find-list (cdr x)))))

  (defun filter-list (x)
    (declare (xargs :guard (true-listp x)
                    :verify-guards nil))
    (cond ((endp x) nil)
	  ((predicate (car x))
	   (cons (car x) (filter-list (cdr x))))
	  (t (filter-list (cdr x)))))


; We also introduce "set versions" of the functions, so that we can reason
; about sets.

  (defun all (set-for-all-reduction)
    (declare (xargs :guard (setp set-for-all-reduction)
                    :verify-guards nil))
    (if (empty set-for-all-reduction)
	t
      (and (predicate (head set-for-all-reduction))
	   (all (tail set-for-all-reduction)))))

  (defun exists (X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (cond ((empty X) nil)
	  ((predicate (head X)) t)
	  (t (exists (tail X)))))

  (defun find (X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (cond ((empty X) nil)
	  ((predicate (head X)) (head X))
	  (t (find (tail X)))))

  (defun filter (X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (cond ((empty X) (sfix X))
	  ((predicate (head X))
	   (insert (head X) (filter (tail X))))
	  (t (filter (tail X)))))

  ))

; We then create "negative" versions of the above functions by performing a set
; of substitutions on the constants.

(defconst *negative-functions*
  (INSTANCE::instance-defuns *positive-functions*
     '(((predicate ?x)   (not (predicate ?x)))
       ((all ?x)         (all<not> ?x))
       ((exists ?x)      (exists<not> ?x))
       ((find ?x)        (find<not> ?x))
       ((filter ?x)      (filter<not> ?x))
       ((all-list ?x)    (all-list<not> ?x))
       ((exists-list ?x) (exists-list<not> ?x))
       ((find-list ?x)   (find-list<not> ?x))
       ((filter-list ?x) (filter-list<not> ?x)))))


; And then we smash together the positive and negative functions to create a
; single function list which can be instantiated later.

(defconst *functions*
  (append *positive-functions* *negative-functions*))


; Now we create the instance-*functions* macro which will allow us to actually
; derive an instance of all of the functions

(INSTANCE::instance *functions*)


; And we call the macro with no arguments, to introduce a verbatim copy of the
; theory.  In other words, we introduce the generic theory itself here.

(instance-*functions*)


(defconst *positive-theorems* '(

; List Theory Reasoning
;
; We begin with several theorems about the "list versions" of the above
; functions.

  (defthm all-list-type
    (or (equal (all-list x) t)
	(equal (all-list x) nil))
    :rule-classes :type-prescription)

  (defthm all-list-cdr
    (implies (all-list x)
	     (all-list (cdr x))))

  (defthm all-list-endp
    (implies (endp x)
	     (all-list x)))

  (defthm all-list-member
    (implies (and (all-list x)
		  (member a x))
	     (predicate a)))

  (defthm all-list-in-2
    (implies (and (all-list x)
		  (not (predicate a)))
	     (not (member a x))))

  (defthm all-list-cons
    (equal (all-list (cons a x))
	   (and (predicate a)
		(all-list x))))

  (defthm all-list-append
    (equal (all-list (append x y))
	   (and (all-list x)
		(all-list y))))

  (defthm all-list-nth
    (implies (and (all-list x)
		  (<= 0 n)
		  (< n (len x)))
	     (predicate (nth n x))))

  (encapsulate nil

    (local (defthm lemma1
	     (implies (and (all-list acc)
			   (all-list x))
		      (all-list (revappend x acc)))))

    (local (defthm lemma2
	     (implies (not (all-list acc))
		      (not (all-list (revappend x acc))))))

    (local (defthm lemma3
	     (implies (and (all-list acc)
			   (not (all-list x)))
		      (not (all-list (revappend x acc))))))

    (defthm all-list-revappend
      (equal (all-list (revappend x acc))
	     (and (all-list x)
		  (all-list acc))))
  )

  (defthm all-list-reverse
    (equal (all-list (reverse x))
	   (all-list x)))

  (defthm exists-list-elimination
    (equal (exists-list x)
	   (not (all-list<not> x))))

  (defthm filter-list-true-list
    (true-listp (filter-list x))
    :rule-classes :type-prescription)

  (defthm filter-list-membership
    (iff (member a (filter-list x))
         (and (predicate a)
              (member a x))))

  (defthm filter-list-all-list
    (all-list (filter-list x)))






; Set Theory Reasoning
;
; Of course, really we are more interested in reasoning about sets than lists.
; We write several theorems about our set functions.

  (defthm all-type
    (or (equal (all X) t)
	(equal (all X) nil))
    :rule-classes :type-prescription)

  (defthm all-sfix
    (equal (all (sfix X))
	   (all X)))

  ;; TODO: extend to forward chaining.

  (defthm all-tail
    (implies (all X)
	     (all (tail X))))

  (defthm all-empty
    (implies (empty X)
	     (all X)))

  (defthm all-in
    (implies (and (all X)
		  (in a X))
	     (predicate a)))

  (defthm all-in-2
    (implies (and (all X)
		  (not (predicate a)))
	     (not (in a X))))

  (defthm all-insert
    (equal (all (insert a X))
	   (and (predicate a)
		(all X)))
    :hints(("Goal" :induct (insert a X))))

  (defthm all-delete
    (implies (all X)
	     (all (delete a X))))

  (defthm all-delete-2
    (implies (predicate a)
	     (equal (all (delete a X))
		    (all X))))

  (defthm all-union
    (equal (all (union X Y))
	   (and (all X)
		(all Y))))

  (defthm all-intersect-X
    (implies (all X)
	     (all (intersect X Y))))

  (defthm all-intersect-Y
    (implies (all X)
	     (all (intersect Y X))))

  (defthm all-difference
    (implies (all X)
	     (all (difference X Y))))

  (defthm all-difference-2
    (implies (all Y)
	     (equal (all (difference X Y))
		    (all X))))


  (defthm exists-elimination
    (equal (exists X)
	   (not (all<not> X))))


  (defthm find-sfix
    (equal (find (sfix X))
	   (find X)))

  (defthm find-witness
    (implies (not (all X))
	     (and (in (find<not> X) X)
		  (not (predicate (find<not> X)))))
    :rule-classes :forward-chaining)


  (defthm filter-set
    (setp (filter X)))

  (defthm filter-sfix
    (equal (filter (sfix X))
	   (filter X)))

  (defthm filter-in
    (equal (in a (filter X))
	   (and (predicate a)
		(in a X)))
    :hints(("Goal" :induct (filter X))))

  (defthm filter-subset
    (subset (filter X) X))

  (defthm filter-all
    (all (filter X)))

  (defthm filter-all-2
    (implies (all X)
	     (equal (filter X) (sfix X)))
    :hints(("Goal" :in-theory (disable double-containment))))




; In order to reason past a mergesort, we need to provide some theorems that
; tie together our list and set theories.  We begin this here.

  (defthm all-mergesort
    (equal (all (mergesort X))
	   (all-list X)))

  (defthm all-list-applied-to-set
    (implies (setp X)
	     (equal (all-list X)
		    (all X)))
    :hints(("Goal" :in-theory (enable setp empty sfix head tail))))

))



; Notice that the positive functions and the negative functions are symmetric.
; We now invert the above theorem to create the corresponding theorems for the
; negative functions.

(defconst *negative-theorems*
  (INSTANCE::instance-rewrite *positive-theorems*

    ;; we first replace calls to "positive" functions with calls to temporary
    ;; symbols, which simply acts as placeholders.

   '(((predicate ?x)   (predicate-temp ?x))
     ((all ?x)         (all-temp ?x))
     ((exists ?x)      (exists-temp ?x))
     ((find ?x)        (find-temp ?x))
     ((filter ?x)      (filter-temp ?x))
     ((all-list ?x)    (all-list-temp ?x))
     ((exists-list ?x) (exists-list-temp ?x))
     ((find-list ?x)   (find-list-temp ?x))
     ((filter-list ?x) (filter-list-temp ?x))

     ;; now we replace calls to "negative" functions with calls to positive
     ;; functions.

     ((not (predicate ?x))  (predicate ?x))
     ((all<not> ?x)         (all ?x))
     ((exists<not> ?x)      (exists ?x))
     ((find<not> ?x)        (find ?x))
     ((filter<not> ?x)      (filter ?x))
     ((all-list<not> ?x)    (all-list ?x))
     ((exists-list<not> ?x) (exists-list ?x))
     ((find-list<not> ?x)   (find-list ?x))
     ((filter-list<not> ?x) (filter-list ?x))

     ;; and finally we replace our temporary placeholder symbols with calls to
     ;; the actual negative functions.

     ((predicate-temp ?x)   (not (predicate ?x)))
     ((all-temp ?x)         (all<not> ?x))
     ((exists-temp ?x)      (exists<not> ?x))
     ((find-temp ?x)        (find<not> ?x))
     ((filter-temp ?x)      (filter<not> ?x))
     ((all-list-temp ?x)    (all-list<not> ?x))
     ((exists-list-temp ?x) (exists-list<not> ?x))
     ((find-list-temp ?x)   (find-list<not> ?x))
     ((filter-list-temp ?x) (filter-list<not> ?x))
)))


; We now smash together the positive and negative theorems to form a single,
; complete theory.  Note that we have to rename all of the defthms in
; *negative-theorems* so that their names will not collide with the theorems in
; *theorems*.

(defconst *theorems*
  (append *positive-theorems*
	  (INSTANCE::rename-defthms *negative-theorems* '-not)))


; As with the functions, we create a new macro which will allow us to derive
; new instances of our theorems.

(INSTANCE::instance *theorems*)


; And as before, we call the resulting macro with no arguments, which gives us
; a verbatim copy of the positive and negative theorems.

(instance-*theorems*)







; We already have an all-by-membership theorem set up for sets.  But, we would
; like to have a corresponding theorem to use with lists.  We create that here.

(encapsulate
  (((all-list-hyps) => *)
   ((all-list-list) => *))

  (local (defun all-list-hyps () nil))
  (local (defun all-list-list () nil))

  (defthmd list-membership-constraint
    (implies (all-list-hyps)
             (implies (member arbitrary-element (all-list-list))
                      (predicate arbitrary-element)))))

(encapsulate ()

  (local (defthm witness-lemma
	   (implies (not (all-list x))
		    (and (member (find-list<not> x) x)
			 (not (predicate (find-list<not> x)))))))

  (defthmd all-list-by-membership
    (implies (all-list-hyps)
	     (all-list (all-list-list)))
    :hints(("Goal"
	    :use (:instance list-membership-constraint
		  (arbitrary-element (find-list<not> (all-list-list)))))))
)



(defconst *final-theorems* '(

  (defthm cardinality-filter
    (equal (cardinality X)
	   (+ (cardinality (filter X))
	      (cardinality (filter<not> X))))
    :rule-classes :linear)

  (defthm all-subset
    (implies (and (all Y)
		  (subset X Y))
	     (all X))
    :hints(("Goal"
	    :use (:functional-instance all-by-membership
		  (all-hyps (lambda () (and (all Y)
					    (subset X Y))))
		  (all-set  (lambda () X))))))

  (defthm all-subset-not
    (implies (and (all<not> Y)
		  (subset X Y))
	     (all<not> X))
    :hints(("Goal"
	    :use (:functional-instance all-by-membership
		  (all-hyps  (lambda () (and (all<not> Y)
				 	     (subset X Y))))
		  (all-set   (lambda () X))
		  (predicate (lambda (x) (not (predicate x))))
		  (all       (lambda (x) (all<not> x)))))))

))

(INSTANCE::instance *final-theorems*)
(instance-*final-theorems*)

(verify-guards all)
(verify-guards all<not>)
(verify-guards exists)
(verify-guards exists<not>)
(verify-guards find)
(verify-guards find<not>)
(verify-guards filter)
(verify-guards filter<not>)

(verify-guards all-list)
(verify-guards all-list<not>)
(verify-guards exists-list)
(verify-guards exists-list<not>)
(verify-guards find-list)
(verify-guards find-list<not>)
(verify-guards filter-list)
(verify-guards filter-list<not>)



; -------------------------------------------------------------------
;
;                   Instancing Concrete Theories
;
; -------------------------------------------------------------------

; Each concrete theory we instantiate will require the introduction of 16 new
; functions and a wealth of theorems.  We don't want to overburden the user
; with having to instantiate all of these and give them names, so we adopt a
; naming convention where the predicate's name is used to generate the names of
; the new functions.  Of course, we still have to generate the new names.

(defun mksym (name sym)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (acl2::string-upcase name) sym))

(defun app (x y)
  (declare (xargs :mode :program))
  (string-append x y))

(defun ?ify (args)
  (declare (xargs :mode :program))
  (if (endp args)
      nil
    (cons (mksym (app "?" (symbol-name (car args)))
		 (car args))
	  (?ify (cdr args)))))

(defun standardize-to-package (symbol-name replacement term)
  (declare (xargs :mode :program))
  (if (atom term)
      (if (and (symbolp term)
	       (equal (symbol-name term) symbol-name))
	  replacement
	term)
    (cons (standardize-to-package symbol-name replacement (car term))
	  (standardize-to-package symbol-name replacement (cdr term)))))


(defun quantify-simple-predicate (predicate
                                  in-package
			          set-guard
                                  list-guard
                                  arg-guard
                                  verify-guards)
  (declare (xargs :guard (symbolp in-package)
		  :mode :program))
  (let* ((name          (car predicate))
	 (args          (cons '?x (cddr predicate)))
	 (wrap          (app "<" (app (symbol-name name) ">")))
	 (not-wrap      (app "<" (app "not-" (app (symbol-name name) ">"))))

	 ;; First we build up all the symbols that we will use.

	 (all<p>             (mksym (app "all" wrap) in-package))
	 (exists<p>          (mksym (app "exists" wrap) in-package))
	 (find<p>            (mksym (app "find" wrap) in-package))
	 (filter<p>          (mksym (app "filter" wrap) in-package))
	 (all<not-p>         (mksym (app "all" not-wrap) in-package))
	 (exists<not-p>      (mksym (app "exists" not-wrap) in-package))
	 (find<not-p>        (mksym (app "find" not-wrap) in-package))
	 (filter<not-p>      (mksym (app "filter" not-wrap) in-package))
	 (all-list<p>        (mksym (app "all-list" wrap) in-package))
	 (exists-list<p>     (mksym (app "exists-list" wrap) in-package))
	 (find-list<p>       (mksym (app "find-list" wrap) in-package))
	 (filter-list<p>     (mksym (app "filter-list" wrap) in-package))
	 (all-list<not-p>    (mksym (app "all-list" not-wrap) in-package))
	 (exists-list<not-p> (mksym (app "exists-list" not-wrap) in-package))
	 (find-list<not-p>   (mksym (app "find-list" not-wrap) in-package))
	 (filter-list<not-p> (mksym (app "filter-list" not-wrap) in-package))

	 ;; And we create a substitution list, to instantiate the generic
	 ;; theory/functions with their new, concrete values.

	 (subs `(((predicate ?x)        (,name ,@args))
		 ((all ?x)              (,all<p> ,@args))
		 ((exists ?x)           (,exists<p> ,@args))
		 ((find ?x)             (,find<p> ,@args))
		 ((filter ?x)           (,filter<p> ,@args))
		 ((all<not> ?x)         (,all<not-p> ,@args))
		 ((exists<not> ?x)      (,exists<not-p> ,@args))
		 ((find<not> ?x)        (,find<not-p> ,@args))
		 ((filter<not> ?x)      (,filter<not-p> ,@args))
		 ((all-list ?x)         (,all-list<p> ,@args))
		 ((exists-list ?x)      (,exists-list<p> ,@args))
		 ((find-list ?x)        (,find-list<p> ,@args))
		 ((filter-list ?x)      (,filter-list<p> ,@args))
		 ((all-list<not> ?x)    (,all-list<not-p> ,@args))
		 ((exists-list<not> ?x) (,exists-list<not-p> ,@args))
		 ((find-list<not> ?x)   (,find-list<not-p> ,@args))
		 ((filter-list<not> ?x) (,filter-list<not-p> ,@args))))

	 ;; We use this hack to support alternate guards.  We basically use our
	 ;; rewriter to inject the extra guards into the function's existing
	 ;; guards.

	 (fn-subs
	  (list* `((xargs :guard (true-listp ?list)
                          :verify-guards nil)
		   (xargs :guard (and (true-listp ?list)
                                      ,@list-guard
                                      ,@arg-guard)
                          :verify-guards nil))
		 `((xargs :guard (setp ?set)
                          :verify-guards nil)
		   (xargs :guard (and (setp ?set)
                                      ,@set-guard
                                      ,@arg-guard)
                          :verify-guards nil))
		 subs))


	 ;; And we make some symbols for use in automating the
	 ;; all-by-membership strategy with computed hints.

	 (all-trigger<p>           (mksym (app "all-trigger" wrap) in-package))
	 (all-trigger<not-p>       (mksym (app "all-trigger" not-wrap) in-package))
	 (all-strategy<p>          (mksym (app "all-strategy" wrap) in-package))
	 (all-strategy<not-p>      (mksym (app "all-strategy" not-wrap) in-package))
	 (all-list-trigger<p>      (mksym (app "all-list-trigger" wrap) in-package))
	 (all-list-trigger<not-p>  (mksym (app "all-list-trigger" not-wrap) in-package))
	 (all-list-strategy<p>     (mksym (app "all-list-strategy" wrap) in-package))
	 (all-list-strategy<not-p> (mksym (app "all-list-strategy" not-wrap) in-package))

	 ;; We finally make a deftheory event with the following name, which
	 ;; holds all of these theorems:

	 (theory<p>         (mksym (app "theory" wrap) in-package))
	 (suffix            (mksym wrap in-package))
	 (thm-names         (append (INSTANCE::defthm-names *theorems*)
				    (INSTANCE::defthm-names *final-theorems*)))
	 (thm-name-map      (INSTANCE::create-new-names thm-names suffix))
	 (theory<p>-defthms (sublis thm-name-map thm-names))

	 )

    `(encapsulate ()

	;; It's now quite easy to instantiate all of our functions.

	(instance-*functions*
	 :subs ,fn-subs
	 :suffix ,name)

	;; And similarly we can instantiate all of the theorems.

	(instance-*theorems*
	 :subs ,subs
	 :suffix ,(mksym wrap in-package))
	 ;:extra-defs (empty))


	;; Automating the computed hints is a pain in the ass.  We
	;; first need triggers as aliases for all<p>, all<not-p>, etc.

	(defund ,all-trigger<p> (,@args)
          (declare (xargs :verify-guards nil))
	  (,all<p> ,@args))

	(defund ,all-trigger<not-p> (,@args)
          (declare (xargs :verify-guards nil))
	  (,all<not-p> ,@args))

	(defund ,all-list-trigger<p> (,@args)
	  (declare (xargs :verify-guards nil))
	  (,all-list<p> ,@args))

	(defund ,all-list-trigger<not-p> (,@args)
	  (declare (xargs :verify-guards nil))
	  (,all-list<not-p> ,@args))


	;; Now we need "tagging theorems" that instruct the rewriter
	;; to tag the appropriate terms.

	(defthm ,all-strategy<p>
	  (implies (and (syntaxp (rewriting-goal-lit mfc state))
			(syntaxp (rewriting-conc-lit (list ',all<p> ,@args)
				  mfc state)))
		   (equal (,all<p> ,@args)
			  (,all-trigger<p> ,@args)))
	  :hints(("Goal"
		  :in-theory (union-theories
			      (theory 'minimal-theory)
			      '((:d ,all-trigger<p>))))))

	(defthm ,all-strategy<not-p>
	  (implies (and (syntaxp (rewriting-goal-lit mfc state))
			(syntaxp (rewriting-conc-lit (list ',all<not-p> ,@args)
				  mfc state)))
		   (equal (,all<not-p> ,@args)
			  (,all-trigger<not-p> ,@args)))
	  :hints(("Goal"
		  :in-theory (union-theories
			      (theory 'minimal-theory)
			      '((:d ,all-trigger<not-p>))))))

	(defthm ,all-list-strategy<p>
	  (implies (and (syntaxp (rewriting-goal-lit mfc state))
			(syntaxp (rewriting-conc-lit (list ',all-list<p> ,@args)
				  mfc state)))
		   (equal (,all-list<p> ,@args)
			  (,all-list-trigger<p> ,@args)))
	  :hints(("Goal"
		  :in-theory (union-theories
			      (theory 'minimal-theory)
			      '((:d ,all-list-trigger<p>))))))

	(defthm ,all-list-strategy<not-p>
	  (implies (and (syntaxp (rewriting-goal-lit mfc state))
			(syntaxp (rewriting-conc-lit (list ',all-list<not-p> ,@args)
				  mfc state)))
		   (equal (,all-list<not-p> ,@args)
			  (,all-list-trigger<not-p> ,@args)))
	  :hints(("Goal"
		  :in-theory (union-theories
			      (theory 'minimal-theory)
			      '((:d ,all-list-trigger<not-p>))))))


	;; And then we call upon our computed hints routines to generate a
	;; computed hint for us to use, and add it to the default hints.

	(COMPUTED-HINTS::automate-instantiation
	  :new-hint-name ,(mksym (app "all-by-membership-hint" wrap) in-package)
	  :generic-theorem all-by-membership
	  :generic-predicate predicate
	  :generic-hyps all-hyps
	  :generic-collection all-set
	  :generic-collection-predicate all
	  :actual-collection-predicate ,all<p>
	  :actual-trigger ,all-trigger<p>
	  :predicate-rewrite (((predicate ,@(?ify args))
			       (,name ,@(?ify args))))
	  :tagging-theorem ,all-strategy<p>
	)

	(COMPUTED-HINTS::automate-instantiation
	  :new-hint-name ,(mksym (app "all-by-membership-hint" not-wrap) in-package)
	  :generic-theorem all-by-membership
	  :generic-predicate predicate
	  :generic-hyps all-hyps
	  :generic-collection all-set
	  :generic-collection-predicate all
	  :actual-collection-predicate ,all<not-p>
	  :actual-trigger ,all-trigger<not-p>
	  :predicate-rewrite (((predicate ,@(?ify args))
			       (not (,name ,@(?ify args)))))
	  :tagging-theorem ,all-strategy<not-p>
	)

	(COMPUTED-HINTS::automate-instantiation
	  :new-hint-name ,(mksym (app "all-list-by-membership-hint" wrap) in-package)
	  :generic-theorem all-list-by-membership
	  :generic-predicate predicate
	  :generic-hyps all-list-hyps
	  :generic-collection all-list-list
	  :generic-collection-predicate all-list
	  :actual-collection-predicate ,all-list<p>
	  :actual-trigger ,all-list-trigger<p>
	  :predicate-rewrite (((predicate ,@(?ify args))
			       (,name ,@(?ify args))))
	  :tagging-theorem ,all-list-strategy<p>
	)

	(COMPUTED-HINTS::automate-instantiation
	  :new-hint-name ,(mksym (app "all-list-by-membership-hint" not-wrap) in-package)
	  :generic-theorem all-list-by-membership
	  :generic-predicate predicate
	  :generic-hyps all-list-hyps
	  :generic-collection all-list-list
	  :generic-collection-predicate all-list
	  :actual-collection-predicate ,all-list<not-p>
	  :actual-trigger ,all-list-trigger<not-p>
	  :predicate-rewrite (((predicate ,@(?ify args))
			       (not (,name ,@(?ify args)))))
	  :tagging-theorem ,all-list-strategy<not-p>
	)


	(instance-*final-theorems*
	 :subs ,subs
	 :suffix ,(mksym wrap in-package))
	 ;:extra-defs (empty))


        ,@(and verify-guards
               `((local (in-theory (enable ,all<p>
                                           ,exists<p>
                                           ,find<p>
                                           ,filter<p>
                                           ,all<not-p>
                                           ,exists<not-p>
                                           ,find<not-p>
                                           ,filter<not-p>
                                           ,all-list<p>
                                           ,exists-list<p>
                                           ,find-list<p>
                                           ,filter-list<p>
                                           ,all-list<not-p>
                                           ,exists-list<not-p>
                                           ,find-list<not-p>
                                           ,filter-list<not-p>)))
                 (verify-guards ,all<p>)
                 (verify-guards ,exists<p>)
                 (verify-guards ,find<p>)
                 (verify-guards ,filter<p>)
                 (verify-guards ,all<not-p>)
                 (verify-guards ,exists<not-p>)
                 (verify-guards ,find<not-p>)
                 (verify-guards ,filter<not-p>)
                 (verify-guards ,all-list<p>)
                 (verify-guards ,exists-list<p>)
                 (verify-guards ,find-list<p>)
                 (verify-guards ,filter-list<p>)
                 (verify-guards ,all-list<not-p>)
                 (verify-guards ,exists-list<not-p>)
                 (verify-guards ,find-list<not-p>)
                 (verify-guards ,filter-list<not-p>)))

	;; In the end, we want to create a deftheory event so that you can
	;; easily turn off the reasoning about these functions when you don't
	;; need it.  We do that with the following event:

	(deftheory ,theory<p> '(,@theory<p>-defthms
				,all<p>              ,all-list<p>
				,exists<p>           ,exists-list<p>
				,find<p>             ,find-list<p>
				,filter<p>           ,filter-list<p>
				,all<not-p>          ,all-list<not-p>
				,exists<not-p>       ,exists-list<not-p>
				,find<not-p>         ,find-list<not-p>
				,filter<not-p>       ,filter-list<not-p>
				,all-trigger<p>      ,all-list-trigger<p>
				,all-trigger<not-p>  ,all-list-trigger<not-p>
				,all-strategy<p>     ,all-list-strategy<p>
				,all-strategy<not-p> ,all-list-strategy<not-p>
				))
	)))


(defmacro quantify-predicate (predicate
			      &key in-package-of
			           set-guard
                                   list-guard
                                   arg-guard
                                   (verify-guards 't)
                                   )
  (quantify-simple-predicate predicate
			     (if in-package-of in-package-of 'in)
			     (standardize-to-package "?SET" '?set set-guard)
			     (standardize-to-package "?LIST" '?list list-guard)
			     arg-guard
                             verify-guards))



; We don't want to keep all these generic theorems around, because many of them
; are rewrite rules with targets that are actual functions.  For example, if a
; rule concludes with (in a X), we don't want to start backchaining on it if
; its hypothese include generic rules.

(deftheory generic-quantification-theory
  `(,@(INSTANCE::defthm-names *theorems*)
    ,@(INSTANCE::defthm-names *final-theorems*)
    all exists find filter
    all-list exists-list find-list filter-list
    all<not> exists<not> find<not> filter<not>
    all-list<not> exists-list<not> find-list<not> filter-list<not>))

(in-theory (disable generic-quantification-theory))

