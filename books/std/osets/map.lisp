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


; map.lisp
;
; This is an optional extension of the sets library, and is not included by
; default when you run (include-book "sets").
;
; We introduce a macro map-function, which is somewhat like the higher-order
; function "map" in other functional languages.  Given a particular
; transformation function, this macro produces:
;
;      map<function>
;      map-list<function>
;
; In addition to introducing these functions, a large rewriting strategy is
; developed for reasoning about the new mapping functions.
;
;
; Introductory Examples.
;
; Here are some simple examples.  These transformation functions have only a
; single argument, and are guarded to operate on any inputs.
;
;     (SET::map-function (integerp x))
;       - (SET::map<integerp> '(1 2 3)) = (t)
;       - (SET::map-list<integerp> '(1 a 2 b)) = (t nil t nil)
;
;     (defun square (x)
;       (declare (xargs :guard t))
;       (* (rfix x) (rfix x)))
;
;     (SET::map-function (square x))
;       - (SET::map<square> '(1 2 3)) = (1 4 9)
;       - (SET::map<square> '(a b c)) = (0)
;
; Note that you can't use macros, e.g., real/rationalp cannot be used since it
; is not a function.
;
;
; Controlling Packages.
;
; As you can see, the new map<f> functions are added to the SETS package by
; default.  If you would like them to be in a new place, you can use the
; :in-package-of argument to map-function.  For example, since defthm is in the
; ACL2 package, we can run:
;
;     (SET::map-function (square x)
;       :in-package-of defthm)
;
; And map<square> will be created in the ACL2 package instead of the sets
; package.
;
;
; Multi-Argument Transformation Functions.
;
; You can also introduce transformations with multiple arguments.  As an
; example, we introduce the function square-then-add, which first squares its
; input and then adds some offset to it.
;
;     (defun square-then-add (input offset)
;       (declare (xargs :guard t))
;       (+ (* (rfix input) (rfix input))
;          (rfix offset)))
;
;     (SET::map-function (square-then-add input offset)
;        :in-package-of defthm)
;
;     (map<square-then-add> '(1 2 3) 5) => (6 9 14)
;
;
; Supporting Guards.
;
; We can support transformation functions that require guards by sending extra
; arguments to the map-function macro.  As an example, we consider what it
; would require to write a mapping function for the function below.
;
;   (defun plus (x y)
;     (declare (xargs :guard (and (integerp x) (rationalp y))))
;     (+ x y))
;
;   (quantify-predicate (integerp x))   ; see quantify.lisp for explanation
;
;   (map-function (plus arg1 arg2)
;     :set-guard ((all<integerp> ?set))        ; set's name must be ?set
;     :list-guard ((all-list<integerp> ?list)) ; list's name must be ?list
;     :element-guard ((integerp a))            ; element's name must be a
;     :arg-guard ((rationalp arg2)))           ; extra arg names specified above
;
;
; These examples can be found and run in map-tests.lisp.

(in-package "SET")
(include-book "quantify")
(set-verify-guards-eagerness 2)

(local (in-theory (enable definitions expensive-rules)))

; BOZO ugly extra theorems we probably shouldn't need

;; [Jared] I think these were basically meant to solve the problem of using the
;; pick-a-point strategy with subset disabled -- this is now solved in a
;; different way, namely via pick-a-point-subset-constraint-helper. Moreover,
;; these rules cause a loop with pick-a-point-subset-constraint-helper, and do
;; not seem to be necessary anymore, so let's get rid of them.

;; (defthm map-subset-helper
;;   (implies (in (head X) Y)
;; 	   (equal (subset (tail X) Y)
;; 		  (subset X Y)))
;;   :hints(("Goal" :expand (subset X Y))))

;; (defthm map-subset-helper-2
;;   (implies (not (in (head X) Y))
;;            (equal (subset X Y)
;;                   (empty X))))


; We will map an arbitrary transformation function across the set.  We don't
; assume anything about transform.

(encapsulate
  (((transform *) => *))
  (local (defun transform (x) x)))


; Now we introduce our mapping functions.  We allow the transform to be mapped
; across a list or a set.  Under the hood, we use MBE to ensure that we first
; transform every element of the set, and then mergesort the results.  This
; gives O(n) + O(n log n) performance intead of the O(n^2) required for
; repeated insertion.  We introduce these functions as a constant, so we can
; rewrite it later to actually create maps.

(defconst *map-functions* '(

  (defun map-list (x)
    (declare (xargs :guard (true-listp x)))
    (if (endp x)
	nil
      (cons (transform (car X))
	    (map-list (cdr X)))))

  (defun map (X)
    (declare (xargs :guard (setp X)))
    (declare (xargs :verify-guards nil))
    (mbe :logic (if (empty X)
		    nil
		  (insert (transform (head X))
			  (map (tail X))))
	 :exec (mergesort (map-list X))))

; A crucial component of our reasoning is the notion of the inverse of the
; transform.  We define the relation (inversep a b), which is true if and only
; if a is an inverse of b under transform -- that is, (inversep a b) is true
; when (transform a) = b.

  (defun inversep (a b)
    (declare (xargs :guard t))
    (equal (transform a) b))))

(INSTANCE::instance *map-functions*)
(instance-*map-functions*)


; We now quantify over the predicate inversep, allowing us to talk
; about the existence of inverses in sets.

(quantify-predicate (inversep a b))



; Again we begin introducing theorems as a constant, so that we can
; instantiate concrete theories of mapping by rewriting.

(defconst *map-theorems* '(

  (defthm map-setp
    (setp (map X)))

  (defthm map-sfix
    (equal (map (sfix X))
	   (map X)))


; The ordered sets library works really well when you can provide a
; concise statement about membership for your new functions.  Here, we
; use the idea of inverses in order to explain what it means to be a
; member in a map.  Basically, (in a (map X)) is exactly equal to
; (exists<inversep> X a), i.e., if there is an inverse of a in x.  We
; then manually apply our "exists elimination" to make this theorem a
; little more direct.

  (defthm map-in
    (equal (in a (map X))
	   (not (all<not-inversep> X a))))


; With this notion of membership in play, we can now use the
; properties of all<not-inversep> in order to prove many interesting
; theorems about mappings through standard membership arguments.

  (defthm map-subset
    (implies (subset X Y)
	     (subset (map X) (map Y))))

  (defthm map-insert
    (equal (map (insert a X))
	   (insert (transform a) (map X))))

  (defthm map-delete
    (subset (delete (transform a) (map X))
	    (map (delete a X))))

  (defthm map-union
    (equal (map (union X Y))
	   (union (map X) (map Y))))

  (defthm map-intersect
    (subset (map (intersect X Y))
	    (intersect (map X) (map Y))))

  (defthm map-difference
    (subset (difference (map X) (map Y))
	    (map (difference X Y))))

  (defthm map-cardinality
    (<= (cardinality (map X))
	(cardinality X))
    :rule-classes :linear)



; We now provide some theorems about mapping over lists.  These are
; somewhat nice in and of themselves, but also allow us to prove our
; mbe equivalence so that our mapping operations are more efficient.
; To begin, we prove the characteristic list membership theorem for
; mapping over lists.

  (defthm member-of-map-list
    (iff (member a (map-list X))
         (exists-list<inversep> X a)))

  (defthm map-mergesort
    (equal (map (mergesort X))
	   (mergesort (map-list X))))



; And finally we prove this theorem, which will be useful for
; verifying the guards of map.

  (defthm map-mbe-equivalence
    (implies (setp X)
	     (equal (mergesort (map-list X))
		    (map X))))


; We finish up our theory with some more, basic theorems about
; mapping over lists.

  (defthm map-list-cons
    (equal (map-list (cons a x))
	   (cons (transform a)
		 (map-list x))))

  (defthm map-list-append
    (equal (map-list (append x y))
	   (append (map-list x)
		   (map-list y))))

  (defthm map-list-nth
    (implies (and (integerp n)
		  (<= 0 n)
		  (< n (len x)))
	     (equal (nth n (map-list x))
		    (transform (nth n x)))))

  (defthm map-list-revappend
    (equal (map-list (revappend x acc))
	   (revappend (map-list x)
		      (map-list acc))))

  (defthm map-list-reverse
    (equal (map-list (reverse x))
	   (reverse (map-list x))))

))

(INSTANCE::instance *map-theorems*)
(instance-*map-theorems*)

(verify-guards map)



; This is a nice generic theory, but to be useful, we will need to be
; able to instantiate concrete theories based on it.  We do this with
; the following function, for which we introduce a corresponding
; macro.

(defun map-function-fn (function in-package
				 set-guard
				 list-guard
				 element-guard
				 arg-guard)

  (declare (xargs :mode :program))

  (let* ((name          (car function))
	 (extra-args    (cddr function))
	 (wrap          (app "<" (app (symbol-name name) ">")))

	 ;; First we build up all the symbols that we will use.

	 (map<f>                   (mksym (app "map" wrap) in-package))
	 (map-list<f>              (mksym (app "map-list" wrap) in-package))
	 (inversep                 (app "inversep" wrap))
	 (ipw                      (app "<" (app inversep ">")))
	 (not-ipw                  (app "<not-" (app inversep ">")))
	 (inversep<f>              (mksym inversep in-package))

	 (all<inversep<f>>     (mksym (app "all" ipw) in-package))
	 (exists<inversep<f>>  (mksym (app "exists" ipw) in-package))
	 (find<inversep<f>>    (mksym (app "find" ipw) in-package))
	 (filter<inversep<f>>  (mksym (app "filter" ipw) in-package))
	 (all-list<inversep<f>>     (mksym (app "all-list" ipw) in-package))
	 (exists-list<inversep<f>>  (mksym (app "exists-list" ipw) in-package))
	 (find-list<inversep<f>>    (mksym (app "find-list" ipw) in-package))
	 (filter-list<inversep<f>>  (mksym (app "filter-list" ipw) in-package))

	 (all<not-inversep<f>>     (mksym (app "all" not-ipw) in-package))
	 (exists<not-inversep<f>>  (mksym (app "exists" not-ipw) in-package))
	 (find<not-inversep<f>>    (mksym (app "find" not-ipw) in-package))
	 (filter<not-inversep<f>>  (mksym (app "filter" not-ipw) in-package))
	 (all-list<not-inversep<f>>     (mksym (app "all-list" not-ipw) in-package))
	 (exists-list<not-inversep<f>>  (mksym (app "exists-list" not-ipw) in-package))
	 (find-list<not-inversep<f>>    (mksym (app "find-list" not-ipw) in-package))
	 (filter-list<not-inversep<f>>  (mksym (app "filter-list" not-ipw) in-package))


	 (subs `(((transform ?x) (,name ?x ,@extra-args))
		 ((map ?x) (,map<f> ?x ,@extra-args))
		 ((map-list ?x) (,map-list<f> ?x ,@extra-args))
		 ((inversep ?a ?b) (,inversep<f> ?a ?b ,@extra-args))

		 ((all<inversep> ?a ?b)    (,all<inversep<f>> ?a ?b ,@extra-args))
		 ((exists<inversep> ?a ?b) (,exists<inversep<f>> ?a ?b ,@extra-args))
		 ((find<inversep> ?a ?b)   (,find<inversep<f>> ?a ?b ,@extra-args))
		 ((filter<inversep> ?a ?b) (,filter<inversep<f>> ?a ?b ,@extra-args))

		 ((all-list<inversep> ?a ?b)    (,all-list<inversep<f>> ?a ?b ,@extra-args))
		 ((exists-list<inversep> ?a ?b) (,exists-list<inversep<f>> ?a ?b ,@extra-args))
		 ((find-list<inversep> ?a ?b)   (,find-list<inversep<f>> ?a ?b ,@extra-args))
		 ((filter-list<inversep> ?a ?b) (,filter-list<inversep<f>> ?a ?b ,@extra-args))

		 ((all<not-inversep> ?a ?b)    (,all<not-inversep<f>> ?a ?b ,@extra-args))
		 ((exists<not-inversep> ?a ?b) (,exists<not-inversep<f>> ?a ?b ,@extra-args))
		 ((find<not-inversep> ?a ?b)   (,find<not-inversep<f>> ?a ?b ,@extra-args))
		 ((filter<not-inversep> ?a ?b) (,filter<not-inversep<f>> ?a ?b ,@extra-args))

		 ((all-list<not-inversep> ?a ?b)    (,all-list<not-inversep<f>> ?a ?b ,@extra-args))
		 ((exists-list<not-inversep> ?a ?b) (,exists-list<not-inversep<f>> ?a ?b ,@extra-args))
		 ((find-list<not-inversep> ?a ?b)   (,find-list<not-inversep<f>> ?a ?b ,@extra-args))
		 ((filter-list<not-inversep> ?a ?b) (,filter-list<not-inversep<f>> ?a ?b ,@extra-args))
	 ))

	 (theory<f>         (mksym (app "map-theory" wrap) in-package))
	 (suffix            (mksym wrap in-package))
	 (thm-names         (INSTANCE::defthm-names *map-theorems*))
	 (thm-name-map      (INSTANCE::create-new-names thm-names suffix))
	 (theory<f>-defthms (sublis thm-name-map thm-names))
	 )

  `(encapsulate ()

		(instance-*map-functions*
		 :subs ,(list* `((declare (xargs :guard (setp ?set)))
				 (declare (xargs :guard (and (setp ?set)
							     ,@set-guard
							     ,@arg-guard))))
			       `((declare (xargs :guard (true-listp ?list)))
				 (declare (xargs :guard (and (true-listp ?list)
							     ,@list-guard
							     ,@arg-guard))))
			       `((declare (xargs :guard t))
				 (declare (xargs :guard (and ,@element-guard
							     ,@arg-guard))))
			       subs)
		 :suffix ,name)

		(quantify-predicate (,inversep<f> a b ,@extra-args)
		 :in-package-of ,in-package
		 :set-guard ,set-guard
		 :list-guard ,list-guard
		 :arg-guard ,arg-guard)

		(instance-*map-theorems*
		 :subs ,subs
		 :suffix ,(mksym wrap in-package))

		(verify-guards ,map<f>)

		(deftheory ,theory<f>
		  (union-theories
		   (theory ',(mksym (app "theory" ipw) in-package))
		   '(,map<f> ,map-list<f> ,inversep<f>
	             ,@theory<f>-defthms)))

		)))


(defmacro map-function (function &key in-package-of
				      set-guard
				      list-guard
				      element-guard
				      arg-guard)
  (map-function-fn function
		   (if in-package-of in-package-of 'in)
		   (standardize-to-package "?SET" '?set set-guard)
		   (standardize-to-package "?LIST" '?list list-guard)
		   (standardize-to-package "A" 'a element-guard)
		   arg-guard
		   ))


(deftheory generic-map-theory
  (union-theories (theory 'theory<inversep>)
		  `(,@(INSTANCE::defthm-names *map-theorems*)
		      map
		      map-list
		      inversep)))

(in-theory (disable generic-map-theory))


