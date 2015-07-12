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

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

(error "Is anyone using this?  If so please remove this error.")

;; osets-definitions.lisp
;; John D. Powell
;(in-package "OSETS")

;;
;; This file isolates osets definitions and types. The file currently 
;; contains the following ACL2 constructs as they occur in the osets book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun in (a X)
  (declare (xargs :guard (setp X)))
  (and (not (empty X))
       (or (equal a (head X))
           (in a (tail X)))))

(defthmd open-set-in
  (implies
   (and
    (syntaxp (quotep x))
    (not (empty x)))
   (equal (in a x)
          (or (equal a (head x))
              (in a (tail x))))))

(defthm in-type
  (or (equal (in a X) t) 
      (equal (in a X) nil))
  :rule-classes :type-prescription)

(defthm in-sfix-cancel
  (equal (in a (sfix X)) (in a X)))

(defthm never-in-empty
  (implies (empty X) (not (in a X))))

(defthm in-set
  (implies (in a X) (setp X)))

(defthm in-head
  (equal (in (head X) X)
         (not (empty X))))

(defthm in-tail
  (implies (in a (tail X)) (in a X)))

(defthm in-tail-or-head
  (implies (and (in a X) 
                (not (in a (tail X))))
           (equal (head X) a)))

(defthm insert-identity
  (implies (in a X)
           (equal (insert a X) X))
  :hints(("Goal" :in-theory (enable insert-induction-case))))


(defthm in-insert
  (equal (in a (insert b X))
         (or (in a X) 
             (equal a b)))
  :hints(("Goal" :in-theory (enable primitive-order-theory)
                 :induct (insert b X))))

;;; The behavior of insert is, of course, determined by the set order.
;;; Yet, we often need to induct upon insert's definition to prove
;;; theorems.  So, here we introduce a new induction scheme which
;;; hides the set order, yet still allows us to induct on insert very
;;; nicely.  We then disable the induction scheme that insert normally
;;; uses, and set up an induction hint so that weak-insert-induction
;;; will automatically be used instead.
 
(defthmd weak-insert-induction-helper-1
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (head (insert a X)) (head X)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(defthmd weak-insert-induction-helper-2
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (tail (insert a X)) (insert a (tail X)))) 
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(defthmd weak-insert-induction-helper-3
  (implies (and (not (in a X))
                (equal (head (insert a X)) a))
           (equal (tail (insert a X)) (sfix X)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defun weak-insert-induction (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((in a X) nil)
        ((equal (head (insert a X)) a) nil)
        (t (list (weak-insert-induction a (tail X))))))

(in-theory (disable (:induction insert)))

(defthm use-weak-insert-induction t 
  :rule-classes ((:induction 
                  :pattern (insert a X)
                  :scheme (weak-insert-induction a X))))

;;; Subset Testing.
;;;
;;; Now we introduce subset.  This becomes complicated because we want
;;; to use MBE to make it fast.  The fast-subset function is a tail
;;; re- cursive, linear pass through both lists.  Subset, by
;;; comparison, is a nice to reason about definition and much simpler,
;;; but would require quadratic time if we didn't use MBE here.

(defun fast-subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (cond ((empty X) t)
        ((empty Y) nil)
        ((<< (head X) (head Y)) nil)
        ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
        (t (fast-subset X (tail Y)))))

(defun subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  t
                (and (in (head X) Y)
                     (subset (tail X) Y)))
       :exec (fast-subset X Y)))

(defthm subset-type
  (or (equal (subset X Y) t)
      (equal (subset X Y) nil))
  :rule-classes :type-prescription)

(defun all (set-for-all-reduction) 
  (declare (xargs :guard (setp set-for-all-reduction)))
  (if (empty set-for-all-reduction)
      t
    (and (predicate (head set-for-all-reduction))
         (all (tail set-for-all-reduction)))))

(defun find-not (X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((not (predicate (head X))) (head X))
        (t (find-not (tail X)))))

(defun subset-trigger (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (subset X Y))

(defthm pick-a-point-subset-strategy
  (implies (and (syntaxp (rewriting-goal-lit mfc state))
                (syntaxp (rewriting-conc-lit `(subset ,X ,Y) mfc state)))
           (equal (subset X Y)
                  (subset-trigger X Y))))

(in-theory (disable subset-trigger))

(defthm subset-sfix-cancel-X
  (equal (subset (sfix X) Y) 
         (subset X Y)))

(defthm subset-sfix-cancel-Y
  (equal (subset X (sfix Y)) 
         (subset X Y)))

(defthm empty-subset
  (implies (empty X) 
           (subset X Y)))

(defthm empty-subset-2
  (implies (empty Y)
           (equal (subset X Y) (empty X))))

(defthm subset-in
  (implies (and (subset X Y) 
                (in a X))
           (in a Y)))

(defthm subset-in-2
  (implies (and (subset X Y) 
                (not (in a Y)))
           (not (in a X))))

(defthm subset-insert-X
  (equal (subset (insert a X) Y)
         (and (subset X Y)
              (in a Y)))
  :hints(("Goal" :induct (insert a X))))

(defthm subset-reflexive
  (subset X X))

(defthm subset-transitive
  (implies (and (subset X Y) 
                (subset Y Z))
           (subset X Z)))

(defthm subset-membership-tail
  (implies (and (subset X Y) 
                (in a (tail X)))
           (in a (tail Y)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))
          
(defthm subset-membership-tail-2
  (implies (and (subset X Y) 
                (not (in a (tail Y))))
           (not (in a (tail X))))
  :hints(("Goal" :in-theory (disable subset-membership-tail)
                 :use (:instance subset-membership-tail))))

(defthm subset-insert
  (subset X (insert a X)))

(defthm subset-tail
  (subset (tail X) X)
  :rule-classes ((:rewrite) 
                 (:forward-chaining :trigger-terms ((tail x)))))

(in-theory (disable head-minimal
                    head-minimal-2))

(defthm map-subset-helper
  (implies (and (not (empty x))
                (in (head x) y))
           (equal (subset (tail x) y)
                  (subset x y)))
  :hints(("Goal" :expand (subset x y))))

(defthm map-subset-helper-2
  (implies (and (not (empty x))
                (not (in (head x) y)))
           (not (subset x y))))


; We will map an arbitrary transformation function across the set.  We
; don't assume anything about transform.

(encapsulate 
  (((transform *) => *))
  (local (defun transform (x) x)))

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


(in-theory (disable generic-map-theory))
                     
(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

;; bzo move to sets library
(defthm sfix-when-empty
  (implies (empty x)
           (equal (sfix x)
                  nil))
  :hints(("Goal" :in-theory (enable sfix))))

;; bzo this should be generated by quantify-predicate instead.
(defthm filter<true-listp>-of-insert
  (equal (filter<true-listp> (insert a x))
         (if (true-listp a)
             (insert a (filter<true-listp> x))
           (filter<true-listp> x))))

;; bzo this should be generated by quantify-predicate instead.
(defthm filter<true-listp>-of-union
  (equal (filter<true-listp> (union x y))
         (union (filter<true-listp> x)
                     (filter<true-listp> y))))

;; bzo is this a good rule??  if so, lets have it be generated by
;; quantify-predicate.  But, I'm not convinced that it is good, and it is
;; potentially expensive, although the free variable should help.
(defthm in-when-subset-of-filter<true-listp>s
  (implies (and (subset (filter<true-listp> x)
                        (filter<true-listp> y))
                (true-listp a)
                (in a x))
           (in a y)))

;; bzo it seems like we might not want this rule.  Normally we want rules that
;; rewrite (in a (set-operation ...)) to something we can reason about more
;; easily, so it seems like maybe this *is* a good rule to have.  On the other
;; hand, we have a lot of theorems that let us conlude (in a x) given some
;; hypotheses about other things in the environment, e.g., subset relations and
;; so forth.  And, this seems to interfere with that.  I guess the question is,
;; is the right hand side of this rule nice *enough*?
(in-theory (disable map-in<fix>))

(defthm all<true-listp>-of-map<fix>
  (all<true-listp> (map<fix> x)))

(defthm all-list<true-listp>-of-map-list<fix>
  (all-list<true-listp> (map-list<fix> list)))

(defthm map<fix>-identity-when-all<true-listp>
  (implies (all<true-listp> x)
           (equal (map<fix> x)
                  (sfix x))))

;; List Sets
;;
;; An object is a listsetp only when it satisfies (setp x) and also
;; (all<true-listp> x).  Historically, list sets were originally an
;; implementation of "U2 Graphs" for the records library.
;;
;; Any existing references to u2p's in comments should be understood to mean
;; listsetp's. TEMP comments can be removed, they are only there to explain the
;; differences between the previously stubbed out definition of u2 graphs.

(defund listsetp (x)
  (declare (xargs :guard t))
  (and (setp x)
       (all<true-listp> x)))

(defthm setp-when-listsetp
  (implies (listsetp x)
           (setp x))
  :hints(("Goal" :in-theory (enable listsetp))))

(defthm listsetp-when-empty
  (implies (empty x)
           (equal (listsetp x)
                  (setp x)))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - I think we don't want this, so I am removing it.
;; (defthm u2p-if
;;   (implies (and (u2p b)
;;                 (u2p c))
;;            (u2p (if a b c)))
;;   :rule-classes (:type-prescription :rewrite))

;; TEMP (jcd) - I think we want this now, so I am leaving it enabled.
;; (in-theory (disable (:type-prescription u2p)))

;; TEMP (jcd) - Although I believe that this is technically true because of the
;; way sets are defined, I don't think we want to prove it, because it is
;; "badly typed" now in that we should not list-fix sets.
;;
;; (defthm u2p-list-fix
;;   (implies
;;    (u2p x)
;;    (u2p (list::list-fix x)))
;;   :rule-classes (:type-prescription :rewrite)
;;   :hints (("goal" :in-theory (enable u2p))))

;; TEMP (jcd) - This was originally u2p of append, but now we should talk about
;; unions since u2's are sets instead of lists.
;;
;; (defthm u2p-of-union
;;   (implies (and (u2p x)
;;                 (u2p y))
;;            (u2p (set::union x y)))
;;   :rule-classes :rewrite
;;   :hints (("goal" :in-theory (enable u2p))))
;;
;; Actually I am taking it out in favor of this stronger rule:

;; TEMP (jcd) - added this rule
(defthm listsetp-of-insert
  (equal (listsetp (insert a x))
         (and (true-listp a)
              (listsetp (sfix x))))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - added this rule
(defthm listsetp-of-union
  (equal (listsetp (union x y))
         (and (listsetp (sfix x))
              (listsetp (sfix y))))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - added this rule
(defthm listsetp-of-delete-when-listsetp
  (implies (listsetp x)
           (listsetp (delete a x)))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - added this rule
(defthm listsetp-of-intersect-when-listsetp-one
  (implies (listsetp x)
           (listsetp (intersect x y)))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - added this rule
(defthm listsetp-of-intersect-when-listsetp-two
  (implies (listsetp y)
           (listsetp (intersect x y)))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - added this rule
(defthm listsetp-of-difference-when-listsetp-one
  (implies (listsetp x)
           (listsetp (difference x y)))
  :hints(("Goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - removing empty-u2, we will just use emptyset.

;; TEMP (jcd) - removing this, we just expand empty-u2 to nil now.
;; (in-theory (disable (empty-u2) (:type-prescription empty-u2)))

;; TEMP (jcd) - removing this, it is already well known in the osets library
;; (defthm union-empty-u2-u2
;;   (equal (union (empty-u2) u2)
;;          (sfix u2)))

;; TEMP (jcd) - removing this, execution should get it now.
;; (defthm listsetp-empty-u2
;;   (listsetp (empty-u2))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("goal" :in-theory (enable listsetp))))

;; TEMP (jcd) - originally we had a function "u2" that was supposed to "smash a
;; regular list into a u2 graph."  I've thought quite a bit about how to adapt
;; this to work with ordered sets. The theorems about u2 were a little odd in
;; the sense that we were told (listsetp (u2 list)) and also that (u2 (u2 list)) =
;; (u2 list).  But, that means that the argument to u2 could be either a list
;; or a set.  I don't like that kind of overloading.  Instead, I have written
;; two versions of the function, one which coerces a list into a listsetp (make-u2),
;; and one which simply "interprets" any ACL2 object as a listsetp (u2fix).

;; "mklistset" is relatively simple, and I haven't given it a whole lot of
;; though.  It coerces a list into a u2 graph, by first list::fix'ing every
;; element in the list, and then sorting the resulting lists in order to create
;; a set.

(defund mklistset (xs)
  (declare (xargs :guard (true-listp xs)))
  (mergesort (map-list<fix> xs)))

(defthm listsetp-of-mklistset
  (listsetp (mklistset xs))
  :hints(("Goal" :in-theory (enable mklistset listsetp))))

(defthm in-mklistset
  (equal (in a (mklistset xs))
         (list::memberp a (map-list<fix> xs)))
  :hints(("Goal" :in-theory (enable mklistset))))

;; How do we interpret "bad" U2 graphs?  There are alternatives here, and it is
;; not clear which is best.  To really weigh all the considerations, we need to
;; think about the u2equiv relation that is going to be based upon this.  The
;; u2equiv relation tests whether or not two objects are equivalent when
;; "interpreted" as u2 sets.  In other words, it is written as (equal
;; (listsetfix x) (listsetfix y)).
;;
;; Here are the options as I see them:
;;
;; Option 1.  Define listsetfix as map<fix>, so that any non-set is treated as
;; nil (in accordance with the non-sets convention), and any set will simply
;; have each of its elements list::fix'ed.

;; (defund listsetfix (u2)
;;   (declare (xargs :guard (listsetp u2)
;;                   :verify-guards nil))
;;   (mbe :logic (map<fix> u2)
;;        :exec u2))

;; Option 2.  Define listsetfix as (if (listsetp x) x nil), so that any
;; non-listset is treated as nil and anything else is treated as the empty set.

;; (defund listsetfix (u2)
;;   (declare (xargs :guard (listsetp u2)
;;                   :verify-guards nil))
;;   (mbe :logic (if (listsetp u2) u2 (emptyset))
;;        :exec u2))

;; Option 3.  Define listsetfix as filter<true-listp>, so that any non-set is
;; treated as nil (in accordance to the non-set convention), and any other set
;; will just have all of its non-true-lists "dropped" from it.  This is the
;; option I eventually decided to go with.

(defund listsetfix (x)
  (declare (xargs :guard (listsetp x)
                  :verify-guards nil))
  (mbe :logic (filter<true-listp> x)
       :exec x))

(defthm listsetp-of-listsetfix
  (listsetp (listsetfix x))
  :hints(("Goal" :in-theory (enable listsetp listsetfix))))

(defthm listsetfix-when-listsetp
  (implies (listsetp x)
           (equal (listsetfix x)
                  x))
  :hints(("Goal" :in-theory (enable listsetp listsetfix))))

;; So which option is better?  Before we address this, we will first define an
;; equivalence relation for u2's, namely u2equiv.  This operation asks if
;; the interpretations of objects x and y as u2 graphs are equivalent, and the
;; proof that it is an equivalence relation is trivial.

(defund listsetequiv (x y)
  (declare (xargs :guard (and (listsetp x)
                              (listsetp y))))
  (equal (listsetfix x)
         (listsetfix y)))

;; TEMP (jcd) - Originally there was a refinement relation here saying that
;; perm is a refinement of u2-equiv.  Even if this is true, I don't want to say
;; it, because we should be thinking now of u2's as sets rather than as bags,
;; so trying to apply bag reasoning to them seems like a type error.

;; With any of our options above, the listsetfix of a valid u2 is the identity
;; function, so regardless of which one we use, we can prove the following
;; rewrite rule:

(defthm listsetfix-under-listsetequiv
  (listsetequiv (listsetfix x)
                x)
  :hints(("Goal" :in-theory (enable listsetequiv))))

;; TEMP (jcd) - added this rule
(defthm cardinality-of-listsetfix
  (<= (cardinality (listsetfix x))
      (cardinality x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable listsetfix))))

;; TEMP (jcd) - added this rule
(defthm sfix-under-listsetequiv
  (listsetequiv (sfix x)
                x)
  :hints(("Goal" :in-theory (enable listsetequiv listsetfix))))

(defthm listsetequiv-union-x-x
  (listsetequiv (union x x)
                x))

;; There are some tradeoffs between Option 1 and Option 3.  Here are some basic
;; theorems that we have when using Option 1:

;; ;; TEMP (jcd) - added this rule
;; (defthm insert-of-listsetfix
;;   (equal (listsetfix (insert a x))
;;          (insert (list::fix a)
;;                       (listsetfix x)))
;;   :hints(("Goal" :in-theory (enable listsetfix))))

;; ;; TEMP (jcd) - added this rule
;; (defthm in-of-listsetfix
;;   (equal (in a (listsetfix x))
;;          (not (all<not-inversep<fix>> x a)))
;;   :hints(("Goal" :in-theory (enable listsetfix))))

;; ;; TEMP (jcd) - added this rule
;; (defthm empty-of-listsetfix
;;   (equal (empty (listsetfix x))
;;          (empty x))
;;   :hints(("Goal" :in-theory (enable listsetfix))))

;; And here are the corresponding theorems using Option 3:

;; TEMP (jcd) - added this rule
(defthm insert-of-listsetfix
  (equal (listsetfix (insert a x))
         (if (true-listp a)
             (insert a (listsetfix x))
           (listsetfix x)))
  :hints(("Goal" :in-theory (enable listsetfix))))

;; TEMP (jcd) - added this rule
(defthm in-of-listsetfix
  (equal (in a (listsetfix x))
         (and (in a x)
              (true-listp a)))
  :hints(("Goal" :in-theory (enable listsetfix))))

;; TEMP (jcd) - added this rule
(defthm empty-of-listsetfix
  (equal (empty (listsetfix x))
         (all<not-true-listp> x))
  :hints(("Goal" :in-theory (enable listsetfix))))

;; TEMP (jcd) - this rule is not necessary, we already know that union is
;; commutative with respect to equal
;;
;; (defthm listsetequiv-union-of-union
;;   (listsetequiv (union x (union y z))
;;                (union y (union x z)))
;;   :hints(("Goal" :in-theory (enable union))))

;; TEMP (jcd) - this rule is not necessary, we already know that union is
;; symmetric with respect to equal
;;
;; (defthm listsetequiv-union-x-y
;;   (listsetequiv (union x y)
;;                (union y x)))

;; TEMP (jcd) - this rule is not necessary, we already know that inserts can be
;; reordered with respect to equal.
;;
;; (defthm listsetequiv-insert-x-insert-y-z
;;   (listsetequiv (insert x (insert y z))
;;                (insert y (insert x z))))

;; TEMP (jcd) - this rule is not necessary, we already know that insert and
;; union can be distributed over one another.  (see union-insert-y)
;;
;; (defthm listsetequiv-union-x-insert-y-z
;;   (listsetequiv (union x (insert y z))
;;                (insert y (union x z))))

;; TEMP (jcd) - this rule is not necessary, we already know this using
;; union-outer-cancel.
;;
;; (defthm listsetequiv-union-x-union-x-y
;;   (listsetequiv (union x (union x y))
;;                (union x y)))

;; TEMP (jcd) - this is similar to map-list<fix>.  We should consider making a
;; macro alias for it, and an untranslate pattern, so that it can have a nicer
;; name.
;;
;; (defun map-list-fix (args)
;;   (declare (type t args))
;;   (if (consp args)
;;       (cons `(list::list-fix ,(car args))
;;             (map-list-fix (cdr args)))
;;     nil))

(defun ordered (a h)
  (or (equal h a)
      (acl2::<< a h)))

(defthmd head-of-insert
  (equal (set::head (set::insert x y))
         (if (set::empty y) x
           (if (ordered x (set::head y)) x
             (set::head y))))
  :otf-flg t
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :use (:instance SET::INSERT-PRODUCES-SET
                           (acl2::a x)
                           (acl2::x y))
           :expand (set::insert x y)
           :in-theory (e/d (set::head  SET::EMPTY set::sfix)
                           (SET::INSERT-PRODUCES-SET)))
          (and acl2::stable-under-simplificationp
               '(:expand ((SET::SETP (LIST X))
                          (SET::INSERT X NIL))))))

(defthmd tail-of-insert
  (equal (set::tail (set::insert x y))
         (if (set::empty y) (set::emptyset)
           (if (equal x (set::head y)) (set::tail y)
             (if (acl2::<< x (set::head y)) y
               (set::insert x (set::tail y))))))
  :otf-flg t
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :use (:instance SET::INSERT-PRODUCES-SET
                           (acl2::a x)
                           (acl2::x y))
           :expand (set::insert x y)
           :in-theory (e/d (set::head  set::tail SET::EMPTY set::sfix)
                           (SET::INSERT-PRODUCES-SET)))
          (and acl2::stable-under-simplificationp
               '(:expand ((SET::SETP (LIST X))
                          (SET::INSERT X NIL))))))

(defthm setp-when-listsetp-cheap
  (implies (listsetp x)
           (setp x))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  )

(in-theory (disable setp-when-listsetp))

(defun instance-variablep (x)
  (and (symbolp x)
       (equal (car (explode-atom x 10)) #\?)))

(mutual-recursion 

  (defun instance-unify-term (pattern term sublist)
    (if (atom pattern)
        (if (instance-variablep pattern)
            (let ((value (assoc pattern sublist)))
              (if (consp value)
                  (if (equal term (cdr value))
                      (mv t sublist)
                    (mv nil nil))
                (mv t (acons pattern term sublist))))
          (if (equal term pattern)
              (mv t sublist)
            (mv nil nil)))
      (if (or (atom term)
              (not (eq (car term) (car pattern))))
          (mv nil nil)
        (if (or (eq (car term) 'quote)
                (eq (car pattern) 'quote))
            (if (equal term pattern)
                (mv t sublist)
              (mv nil nil))
          (instance-unify-list (cdr pattern) (cdr term) sublist)))))
      
  (defun instance-unify-list (pattern-list term-list sublist)
    (if (or (atom term-list)
            (atom pattern-list))
        (if (and (atom term-list)
                 (atom pattern-list))
            (mv t sublist)
          (mv nil nil))
      (mv-let (successp new-sublist)
              (instance-unify-term (car pattern-list) 
                                   (car term-list) 
                                   sublist)
              (if successp
                  (instance-unify-list (cdr pattern-list) 
                                       (cdr term-list) 
                                       new-sublist)
                (mv nil nil)))))
)


; After a list of substitutions has been generated, we typically want
; to apply them to a term.  We recur over the list of substitutions, 
; simply calling subst to do our work throughout a term.
;
; For example:
; 
;   (instance-substitute '((?x . (car a))) '(not (predicate ?x)))
;   ==>
;   (not (predicate (car a)))

(defun instance-substitute (sublist term)
  (if (endp sublist)
      term
    (let* ((old (car (car sublist)))
           (new (cdr (car sublist)))
           (result (subst new old term)))
      (instance-substitute (cdr sublist) result))))



; We now introduce our actual rewriter.  We take three arguments: pat
; is the pattern to look for throughout the term, e.g., (predicate
; ?x), repl is the replacement to use, e.g., (not (predicate ?x)), and
; term is the term to match the pattern against in order to get the
; substitutions.
;
; For Example:
;  
;   (instance-rewrite1 '(predicate ?x) 
;                      '(not (predicate ?x))
;                      '(if (predicate (car x)) t nil))
;   =>
;   (if (not (predicate (car x))) t nil)

(mutual-recursion 

  (defun instance-rewrite1 (pat repl term)
    (mv-let (successful sublist)
            (instance-unify-term pat term nil)
            (if successful 
                (instance-substitute sublist repl)
              (if (atom term)
                  term
                (cons (instance-rewrite1 pat repl (car term))
                      (instance-rewrite-lst1 pat repl (cdr term)))))))

  (defun instance-rewrite-lst1 (pat repl lst)
    (if (endp lst)
        nil
      (cons (instance-rewrite1 pat repl (car lst))
            (instance-rewrite-lst1 pat repl (cdr lst)))))
)



; Finally, given that we can apply a rewrite a term with a single
; replacement, we go ahead and extend this notion to multiple
; replacements.  In other words, we walk through a list of
; substitutions, sequentially rewriting the term using each
; substitution.

(defun instance-rewrite (term subs)
  (if (endp subs)
      term
    (let ((first-sub (car subs)))
      (instance-rewrite (instance-rewrite1 (first first-sub)
                                           (second first-sub)
                                           term)
                        (cdr subs)))))




; Instantiating Defuns
;
;
; Theories consist mainly of definitions and theorems.  Given generic
; theorems, we will want to rewrite them so that they perform
; different functions.  For example, a generic "all" function might
; need to be rewritten so that its calls to (predicate x) are replaced
; with calls to (not (predicate x)) for all x.  
; 
; To begin, we instantiate the function's declarations (e.g., comment
; strings, xargs, ignores, and so forth).  We simply duplicate comment
; strings, but for declare forms we allow rewriting to occur.

(defun instance-decls (decls subs)
  (if (endp decls)
      nil
    (if (pseudo-termp (car decls))
        (cons (instance-rewrite (car decls) subs)
              (instance-decls (cdr decls) subs))
      (cons (car decls)
            (instance-decls (cdr decls) subs)))))


; For the defun itself, we retain the same defun symbol (e.g., defun
; or defund), but we change the name and args of the function by first
; creating the list '(oldname oldarg1 oldarg2 ...) then applying our
; substitutions to the new function.
;
; As a trivial example, 
;  (instance-defun '(defun f (x) (+ x 1)) '(((f x) (g x))))
;    =>
;  (defun g (x) (+ x 1))

(defun instance-defun (defun subs)
  (let* ((defun-symbol  (first defun))
          (defun-name    (second defun))
         (defun-args    (third defun))
         (defun-decls   (butlast (cdddr defun) 1))
         (defun-body    (car (last defun)))
         (name/args     (cons defun-name defun-args))
         (new-body      (instance-rewrite defun-body subs))
         (new-name/args (instance-rewrite name/args subs))
         (new-decls     (instance-decls defun-decls subs))
         (new-name      (car new-name/args))
         (new-args      (cdr new-name/args)))
    `(,defun-symbol 
       ,new-name ,new-args 
       ,@new-decls
       ,new-body)))

; We also provide a convenience function that allows you to instance
; a list of defuns.

(defun instance-defuns (defun-list subs)
  (if (endp defun-list)
      nil
    (cons (instance-defun (car defun-list) subs)
          (instance-defuns (cdr defun-list) subs))))



; Renaming theorems

(defun defthm-names (event-list)
  (if (endp event-list)
      nil
    (let* ((first-event (car event-list))
           (event-type  (first first-event)))
      (cond ((or (eq event-type 'defthm)
                 (eq event-type 'defthmd))
             (cons (second first-event)
                   (defthm-names (cdr event-list))))
            ((eq event-type 'encapsulate)
             (append (defthm-names (cddr first-event))
                     (defthm-names (cdr event-list))))
            (t (defthm-names (cdr event-list)))))))

(defun create-new-names (name-list suffix)
  (if (endp name-list)
      nil
    (acons (car name-list)
           (intern-in-package-of-symbol (string-append (symbol-name (car name-list))
                                                       (symbol-name suffix))
                                        suffix)
           (create-new-names (cdr name-list) suffix))))
        
(defun rename-defthms (event-list suffix)
  (sublis (create-new-names (defthm-names event-list) suffix)
          event-list))



; Instantiating Theorems
;
;
; To instantiate defthms, we will want to be able to provide
; functional instantiations of the generic theory.  This is much
; more complicated than instancing definitions, and involves:
;
;   a) determining what functional substitutions to make
;   b) determining the theory in which to conduct the proofs 
;   c) handling rule classes and other optional components
;   d) generating the actual defthm event
;
; My idea is essentially that if a substitution list can be used for
; functionally instantiating theorems, then it can also be used for 
; creating the new theorem.
;
; (a) Determining what functional substitutions to make.
;
; I pass in a list of substitutions of the following form.
;
;   (((predicate ?x)  (not (in ?x y)))
;    ((all ?x)        (all-not-in ?x y))
;    ((exists ?x)     (exists-not-in ?x y)))
; 
; From this list we can generate the functional instantiation hints.
; So, for example, we simply convert ((predicate ?x) (not (in ?x y)))
; into the substitution:
;
;   (predicate (lambda (?x) (not (in ?x y))))
;
; This is easy to do with the following functions:

(defun sub-to-lambda (sub)
  (let ((term (first sub))
        (repl (second sub)))
    (let ((function-symbol (car term))
          (lambda-args (cdr term)))
      `(,function-symbol (lambda ,lambda-args ,repl)))))

(defun subs-to-lambdas (subs)
  (if (endp subs)
      nil
    (cons (sub-to-lambda (car subs))
          (subs-to-lambdas (cdr subs)))))


; (b) Determining the theory in which to conduct the proofs.
;
; When we prove the functional instantiation constraints, ideally we
; should work in an environment where the only definitions that are
; enabled are the definitions used in the functional instantiation 
; hints.  
;
; Well, the definitions we need are (almost) simply all of the
; function symbols in the right-hand side of the substitution list.
; In other words, for the above substitutions, I would want to have
; the definitions of not, in, all-not-in, and exists-not-in available.
;
; Now, the problem with this approach is, what if those symbols don't
; have definitions?  This can occur if, for example, we are using a
; constrained function in the substitution list.  This is actually
; useful, e.g., for substituting (predicate ?x) -> (not (predicate
; ?x)).  
;
; My solution is a stupid hack.  We simply pass in the names of the 
; generic functions for which we do not want to generate definitions
; along with the substitutinos.
;
; To begin, the following function will extract all function symbols
; that occur within a term.

(mutual-recursion 

  (defun term-functions (term)
    (if (atom term)
        nil
      (cons (car term) 
            (term-list-functions (cdr term)))))

  (defun term-list-functions (list)
    (if (endp list)
        nil
      (append (term-functions (car list))
              (term-list-functions (cdr list)))))
)

; Next, I wrote the following function, which walks over the
; substitution list and extracts the function symbols from each right
; hand side, using term-functions.  The net result is the list of all
; functions that were used in replacements.
  
(defun subs-repl-functions (subs)
  (if (endp subs)
      nil
    (let* ((sub1 (car subs))
           (repl (second sub1)))
      (append (term-functions repl)
              (subs-repl-functions (cdr subs))))))

; Given the above, we could then convert the list of function symbols 
; into a list of (:definition f)'s with the following function.
   
(defun function-list-to-definitions (funcs)
  (if (endp funcs)
      nil
    (cons `(:definition ,(car funcs))
          (function-list-to-definitions (cdr funcs)))))

; And finally, here is a function that does "all of the work", calling
; function-list-to-definitions for all of the functions found in the
; substitution list, minus all of the generic functions that we don't
; want to generate :definition hints for.

(defun subs-to-defs (subs generics)
  (let* ((all-fns (subs-repl-functions subs))
         (real-fns (set-difference-eq all-fns generics)))
    (function-list-to-definitions real-fns)))


; (c) Handling rule classes and other optional components.
;
; We are interested in several parts of a defthm.  In addition to the
; conjecture itself, we need to consider the rule-classes used by the
; theorem, and the other optional attributes such as the :hints, :doc,
; :otf-flg, etc.  We parse these attributes into a five-tuple of pairs
; of the form (present . value), where present is a boolean that says
; whether or not the flag has been seen, value is its value, and the
; order of the elements is rule-classes, instructions, hints, otf-flg,
; and finally doc.  We parse these options with the following code:

(defun parse-defthm-option (option return-value)
  (cond ((equal (first option) :rule-classes)
         (update-nth 0 (list t (second option)) return-value))
        ((equal (first option) :instructions)
         (update-nth 1 (list t (second option)) return-value))
        ((equal (first option) :hints)
         (update-nth 2 (list t (second option)) return-value))
        ((equal (first option) :otf-flg)
         (update-nth 3 (list t (second option)) return-value))
        ((equal (first option) :doc)
         (update-nth 4 (list t (second option)) return-value))
        (t (er hard "Unknown flag in defthm options ~x0." (first option)))))

(defun parse-defthm-options (options return-value)
  (if (endp options)
      return-value
    (parse-defthm-options (cddr options)
                          (parse-defthm-option options return-value))))


; (d) Generating the actual defthm event.
;
; When we are ready to instance a defthm event, we combine the above
; work with a few new things.  First of all, we need the original
; theorem event, a new name to use, the substitutions to use, and the
; list of generic function symbols in use so that we do not create
; (:definition f) entries for them.
;
; We begin by making our substitutions in the body of the theorem.  We
; then parse the optional components of the defthm, but we only are
; interested in the rule-classes.  (Hints, instructions, and otf-flg
; will not be needed, because we will be proving this via functional
; instantiation.  Doc we ignore for no good reason.)  We construct a
; new theorem that has our new name and body, replicating the rule
; classes if necessary.  We also provide a functional instantiation
; hint of the generic theorem's name, along with a list of lambda
; substitutions to make.

(defun instance-defthm (event new-name subs generics extra-defs)
  (let* ((defthm-symbol (first event)) 
         (defthm-name   (second event))
         (defthm-body   (third event))
         (new-body      (instance-rewrite defthm-body subs))
         (options       (parse-defthm-options (cdddr event) 
                                              *default-parse-values*))
         (rc-opt        (first options)))
    `(,defthm-symbol ,new-name 
       ,new-body
       :hints(("Goal"
               :use (:functional-instance ,defthm-name
                                          ,@(subs-to-lambdas subs))
               :in-theory (union-theories (theory 'minimal-theory)
                           (union-theories ',extra-defs
                                           ',(subs-to-defs subs generics)))))
       ,@(if (car rc-opt) `(:rule-classes ,(cdr rc-opt)) nil))))



; Instantiating Encapsulates
;
;
; There are two reasons that I typically use encapsulation.  The first
; is as a purely structural/organizational purpose, where I am trying
; to prove some theorem is true, but I need some lemmas to do so.  In
; this case I use an (encapsulate nil ...) and wrap my lemmas in local
; forms.  The other reason is to actually go ahead and introduce
; constrained functions.
;
; Two strategies will be necessary for handling these situations.  In
; particular, if we are in an encapsulate which has no constrained
; function symbols, we will want to skip all local events and only add
; the non-local events (using functional instantiation to create the
; theorems).  On the other hand, for the case when we are introducing
; constrained functions, we will want to introduce new constrained 
; functions based on the encapsulate.
;
; So, encapsulates are handled separately based on whether or not any
; functions are constrained.
;
; Within an (encapsulate nil ...), local events will be skipped and
; defthm events will be proven using the functional instantiation of
; their generic counterparts.
;
; Within an (encapsulate (...) ...), local events will not be skipped
; but will instead be reintroduced with new names.  Further, defthm
; events will be copied using new names and will not be proven using
; functional instantiation.
;
; The only "extra" thing we really need for handling encapsulates is a
; system to make the substitutions within the signatures.  We do that
; here by simple rewriting.  Note that we do not allow the number of
; return values to change.  I don't really think of this as a major
; limitation, since almost always my constrained functions return a 
; single value.  If you have an example of where this would be useful,
; it would be interesting to see it.

(defun instance-signature (signature subs)
  (let ((name (first signature))
        (rest (rest signature)))
    (cons (instance-rewrite subs name) rest)))

(defun instance-signatures (signatures subs)
  (if (endp signatures)
      nil
    (cons (instance-signature (car signatures) subs)
          (instance-signatures (cdr signatures) subs))))

; Because encapsulates can contain many events within them, it is
; natural to make them mutually recursive with the main event list
; handler, which we are now ready to introduce.





; Instantiating Entire Theories
;
; 
; We are now ready to introduce the functions which will walk through
; a theory and call the appropriate instancing functions on each of 
; the forms we encounter.  To support encapsulation, our functions 
; here are all mutually recursive.
;
; The arguments that we pass around are the following:
;
;   - The event or event list to instantiate 
;
;   - The global list of substitutions used to derive the instance
;
;   - A suffix which will be appended to generate new names
;
;   - A list of generic functions which have no definitions
;
;   - A mode, which is either 'constrained to indicate that the
;     nearest encapsulate event has constrained functions, or is nil
;     to indicate that the nearest encapsulate is merely a structural
;     wrapper for local lemmas.
;
; Finally, we overload our behavior based on suffix, so that if no 
; suffix is given, we simply replicate the generic theory instead 
; of instantiating a concrete instance of it.


(mutual-recursion

  (defun instance-event (event subs suffix generics mode extra-defs)
    (if (null suffix)
        event
      (cond ((or (eq (car event) 'defun)
                 (eq (car event) 'defund))
             (instance-defun event subs))
            ((or (eq (car event) 'defthm)
                 (eq (car event) 'defthmd))
             (let* ((name (second event))
                    (new-name (intern-in-package-of-symbol
                               (string-upcase 
                                (concatenate 'string 
                                             (symbol-name name)
                                             (symbol-name suffix)))
                               suffix)))
               (instance-defthm event new-name subs generics extra-defs)))
            ((equal (car event) 'local)
             (if (eq mode 'constrained)
                 (instance-event (second event) subs suffix generics mode extra-defs)
               nil))
            ((equal (car event) 'encapsulate)
             (instance-encapsulate event subs suffix generics mode extra-defs))
            (t (er hard "Don't know how to handle ~x0" (car event))))))

  (defun instance-event-list (events subs suffix generics mode extra-defs)
    (if (endp events)
        nil
      (let ((first (instance-event (car events) subs suffix generics mode extra-defs))
            (rest  (instance-event-list (cdr events) subs suffix generics mode extra-defs)))
        (if first 
            (cons first rest)
          rest))))

  (defun instance-encapsulate (event subs suffix generics mode extra-defs)
    (declare (ignore mode))
    (let* ((signatures (second event))
           (new-sigs   (if signatures 
                           (instance-signatures subs signatures)
                         nil))
           (new-events (instance-event-list (cddr event) subs suffix generics
                                            (if signatures 
                                                'constrained
                                              nil)
                                            extra-defs)))
      `(encapsulate ,new-sigs ,@new-events)))

)


(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

;;; First we introduce some basic theory about cons and sets.  Note
;;; that this theory is disabled at the end of this file.  However, if
;;; you are introducing fast versions of new set functions, you can
;;; enable these theorems by enabling cons-theory.

(defthm cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X))))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-nonempty
  (implies (and (setp X) 
                (<< a (head X)))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory
                                    primitive-order-theory))))

(defthm cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))



;;; These fast versions recur on one or both of their arguments, but
;;; not always the same argument.  Hence, we need to introduce a more
;;; flexible measure to prove that they terminate.  Fortunately, this
;;; is still relatively simple:

(defun fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))




;;; Fast Union
;;;
;;; We want to show that fast union always produces a set, and has the
;;; expected membership property.  This is ugly because reasoning
;;; about set order is hard.

(defun fast-union (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) Y)
        ((empty Y) X)
        ((equal (head X) (head Y))
         (cons (head X) (fast-union (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (cons (head X) (fast-union (tail X) Y)))
        (t (cons (head Y) (fast-union X (tail Y))))))


;;; Fast Intersect
;;;
;;; We are only interested in showing that fast-intersect
;;; creates sets and has the expected membership property.  


(defun fast-intersect (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) (sfix Y))
        ((equal (head X) (head Y))
         (cons (head X) 
               (fast-intersect (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (fast-intersect (tail X) Y))
        (t (fast-intersect X (tail Y)))))

;;; Fast Difference
;;;
;;; We want to show that difference always creates a set and that 
;;; the produced set has the expected membership properties.


(defun fast-difference (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) X)
        ((equal (head X) (head Y))
         (fast-difference (tail X) (tail Y)))
        ((<< (head X) (head Y))
         (cons (head X) (fast-difference (tail X) Y)))
        (t (fast-difference X (tail Y)))))

(in-theory (disable fast-measure
                    fast-union
                    fast-intersect
                    fast-difference
                    fast-union-theory
                    fast-intersect-theory
                    fast-difference-theory
                    cons-theory))
                    
(defthmd open-set2list
  (implies
   (not (empty set))
   (equal (2list set)
          (CONS (HEAD SET)
                (|2LIST| (TAIL SET))))))


(defthmd in-implications
  (implies
   (and
    (not (empty set))
    (in a set)
    (not (equal (head set) a)))
   (acl2::<< (head set) a))
  :hints (("Subgoal *1/4" :use (:instance
                                HEAD-TAIL-ORDER
                                (acl2::x set)))
          ("Subgoal *1/3" :use (:instance
                                HEAD-TAIL-ORDER
                                (acl2::x set)))))

(defthmd head-is-least-element
  (implies
   (and
    (not (empty set))
    (in a (tail set)))
   (acl2::<< (head set) a))
  :hints (("goal" :use in-implications)))

(defthm ordering-over-subset
  (implies
   (and
    (not (empty set1))
    (not (empty set2))
    (subset set2 (tail set1)))
   (acl2::<< (head set1) (head set2)))
  :hints (("goal" :use (:instance head-is-least-element
                                  (a (head set2))
                                  (set set1)))))

(defthm head-of-insert-under-subset
  (implies
   (and
    ;(not (empty set2))
    (not (empty set1))
    (subset set2 (tail set1)))
   (equal (head (insert (head set1) set2))
          (head set1)))
  :hints (("goal" :in-theory (enable HEAD-INSERT))))

(defthm not-empty-setp
  (implies
   (and
    (setp set)
    (empty set))
   (not set))
  :rule-classes (:forward-chaining)
  :hints (("goal" :in-theory (enable setp empty))))

(defthm tail-of-insert-under-subset
  (implies
   (and
    (setp set2)
    (not (empty set1))
    (subset set2 (tail set1)))
   (equal (tail (insert (head set1) set2))
          set2))
  :hints (("goal" :in-theory (enable tail-INSERT))))

(defthm consp-of-insert
  (consp (insert a s))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable empty insert setp))))

;; ;bzo drop because we have consp-of-insert?
;; (defthm iff-of-insert
;;   (iff (insert a s)
;;        t)
;;   :hints (("Goal" :in-theory (enable empty insert setp))))


;these mix car/cdr and insert and perhaps that should never happen.  but it seems to in practice...

;or do we want to just turn (insert a nil) into (list nil), or perhaps a new function called singleton applied to a?
(defthm cdr-insert-nil
  (equal (cdr (insert a nil))
         nil)
  :hints (("Goal" :in-theory (enable insert))))

(defthm car-insert-nil
  (equal (car (insert a nil))
         a)
  :hints (("Goal" :in-theory (enable insert))))

;handle this better?
(defthm subset-singletons-hack
  (subset (list x) (insert x nil))
  :hints (("Goal" :expand ((insert x nil)))))

(defthm setp-of-singleton
  (setp (list x))
  :hints (("Goal" :expand ((setp (list x))))))

(defthm in-of-singleton-hack
  (in a (list a))
  :hints (("Goal" :in-theory (enable tail
                                     head
                                     empty)
           :expand ((in a (list a))))))

(defthm empty-when-setp-means-nil
  (implies (setp x)
           (equal (EMPTY x)
                  (equal x nil)))
  :hints (("Goal" :in-theory (enable EMPTY))))

;bzo expensive?
(defthm empty-implies-not-sfix
  (implies (empty set)
           (not (sfix set)))
  :hints (("Goal" :in-theory (enable sfix))))

(defthm union-iff
  (iff (union x y)
       (or (not (empty x))
           (not (empty y)))))

(defthmd delete-of-union-push-into-both
  (equal (DELETE A (UNION x y))
         (UNION (DELETE A x)
                     (DELETE A y))))

(defthm subset-of-two-unions
  (implies (and (subset x x2)
                (subset y y2))
           (subset (union x y)
                        (union x2 y2))))

(defthm delete-of-insert-both
  (equal (delete a (insert b x))
         (if (equal a b)
             (delete a x)
           (insert b (delete a x)))))

;expensive?
(defthm head-when-empty
  (implies (empty x)
           (equal (head x)
                  (emptyset)))
  :hints (("Goal" :in-theory (enable head))))

(defthm delete-equal-self
  (equal (equal s (delete a s))
         (and (setp s)
              (not (in a s)))))

;may be expensive?
;use a congruence?
;trying disabled, since this sort of takes us out of the set world
(defthmd insert-when-empty
  (implies (empty x)
           (equal (insert a x)
                  (list a)))
  :hints (("Goal" :in-theory (enable insert))))

;this sort of keeps us in the sets world (emptyset is a macro for nil - does that count as being in the sets world?)
(defthm insert-when-empty-2
  (implies (and (syntaxp (not (equal x ''nil))) ;prevents loops
                (empty x))
           (equal (insert a x)
                  (insert a (emptyset))))
  :hints (("Goal" :in-theory (enable insert))))


(defthm head-of-singleton
  (equal (head (list a))
         a)
  :hints (("Goal" :in-theory (enable head))))

(defthm tail-of-singleton
  (equal (tail (list a))
         nil)
  :hints (("Goal" :in-theory (enable tail))))

(defthm tail-of-singleton2
  (equal (TAIL (INSERT A NIL))
         (emptyset))
  :hints (("Goal" :in-theory (enable INSERT))))

;disable?        
(defthmd subset-of-delete-helper
  (implies (and (not (subset (delete a x) y))
                (setp y))
           (not (subset x (insert a y)))))

(defthm subset-of-delete
  (implies (and (setp x)
                (setp y))
           (equal (subset (delete a x) y)
                  (if (in a x)
                      (if (in a y)
                          (subset x (insert a y))    
                        (subset x (insert a y)))
                    (subset x y))))
  :hints (("Goal" :in-theory (enable subset-of-delete-helper))))

(defthm subset-of-insert-when-subset
  (implies (subset x y)
           (subset x (insert a y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm not-empty-of-singleton
  (not (empty (list a)))
  :hints (("Goal" :in-theory (enable empty))))

;may be expensive?
(defthm subset-delete-irrel-cheap
  (implies (not (in a x))
           (equal (subset x (delete a y))
                  (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd subset-delete-irrel
  (implies (not (in a x))
           (equal (subset x (delete a y))
                  (subset x y))))

;may be expensive?
(defthm subset-of-insert-irrel-cheap
  (implies (not (in a x))
           (equal (subset x (insert a y))
                  (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd subset-of-insert-irrel
  (implies (not (in a x))
           (equal (subset x (insert a y))
                  (subset x y))))

(defthmd subset-of-singleton
  (equal (subset x (insert a nil))
         (or (empty x)
             ;(equal x (insert a nil))
             (and (equal a (head x)) ;rephrasing...
                  (empty (tail x))))))

;Maybe restrict double-containment to not fire if either argument is a singleton?
;(theory-invariant (incompatible (:rewrite subset-of-singleton) (:rewrite double-containment)))

;semed to be expensive.
(defthmd empty-of-delete-rewrite
  (equal (empty (delete a s))
         (or (empty s)
             (equal s (insert a (emptyset))))))

(defthmd tail-when-empty                
  (implies (empty set) 
           (equal (tail set)
                  (emptyset)))
  :hints (("Goal" :in-theory (enable tail))))

(defthm tail-when-empty-cheap    
  (implies (empty set) 
           (equal (tail set)
                  (emptyset)))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable tail-when-empty))))

(defthm delete-head-of-self
  (equal (delete (head set) set)
         (tail set)))
 
(defthmd tail-when-not-setp
  (implies (not (setp s))
           (equal (tail s)
                  nil))
  :hints (("Goal" :in-theory (enable tail))))

(defthm tail-when-not-setp-cheap
  (implies (not (setp s))
           (equal (tail s)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable tail-when-not-setp))))

(defthm not-empty-when-something-in
  (implies (in a x) ;a is a free variable
           (not (empty x))))

(defun set::2list (set)
  (declare (type (satisfies setp) set))
  (if (empty set) nil
    (cons (head set)
          (set::2list (tail set)))))

(defthm true-listp-2list
  (true-listp (set::2list set)))

(defun list::2set (list)
  (declare (type t list))
  (if (consp list)
      (insert (car list)
              (list::2set (cdr list)))
    nil))

(defthm setp-2set
  (setp (list::2set list)))


;new stuff

(defthm car-of-2LIST
  (equal (CAR (SET::|2LIST| set))
         (if (set::empty set)
             nil
           (set::head set))))

(defthm cdr-of-2list
  (equal (CDR (SET::|2LIST| set))
         (if (set::empty set)
             nil
           (SET::|2LIST| (set::tail set))))
  :hints (("Goal" :in-theory (enable SET::|2LIST|))))

(defthm consp-of-2list
  (equal (CONSP (SET::|2LIST| set))
         (not (set::empty set))))


;expensive?
;move
(defthm sfix-when-not-setp
  (implies (not (setp s)) 
           (equal (sfix s)
                  nil))
  :hints (("Goal" :in-theory (enable sfix))))

;bzo do the other inverse?
(defthm 2set-of-2list
  (equal (list::2set (2list s))
         (sfix s))
  :hints (("Goal" :in-theory (enable set::empty))))


;where should this go?
(defthm in-of-2set
  (equal (set::in a (list::2set lst))
         (list::memberp a lst)))

(defthm memberp-of-2list
  (equal (list::memberp a (2list set))
         (set::in a set)))

(defthm 2set-rewrap
  (equal (set::insert (car lst) (list::2set (cdr lst)))
         (if (consp lst)
             (list::2set lst)
           (set::insert nil (set::emptyset))
           )))

(in-theory (disable LIST::2set)) 

(defthm 2set-of-cons
  (equal (list::2set (cons a x))
         (set::insert a (list::2set x)))
  :hints (("Goal" :in-theory (e/d (list::2set) (set::2set-rewrap)))))

(defthm remove-2list
  (list::setequiv (list::remove a (2list set))
                  (2list (delete a set))))

(defthm delete-2set
  (equal (delete a (list::2set list))
         (list::2set (list::remove a list))))

(defthm empty-2set
  (equal (empty (list::2set list))
         (not (consp list)))
  :hints (("Goal" :in-theory (e/d (list::2set)
                                  (|2SET-REWRAP|)))))

(defthm consp-2list
  (equal (consp (2list set))
         (not (empty set))))

;;; Introduction
;;;
;;; Suppose we have some predicate, P, of any number of arguments.  A
;;; natural operation is to extend this predicate to every element of
;;; a list, set, or other collection.  In other words, we would like
;;; to know if every element in the set, list, tree, or whatever has
;;; the property when applied to arguments.
;;;
;;; For example, we might have the predicate:
;;;
;;;  (defun integer-lessp (a b)
;;;    (and (integerp a)
;;;         (< a b)))
;;;
;;; We could now extend this concept to an entire list, to ask if
;;; every element in the list was an integer that is less than b.  The
;;; function might be written as:
;;;
;;;  (defun list-integer-lessp (a-list b)
;;;    (declare (xargs :guard (true-listp a-list)))
;;;    (or (endp a-list)
;;;        (and (integer-lessp (car a-list) b)
;;;             (list-integer-lessp (cdr a-list) b))))
;;;
;;; Similarly, we might want to map the function across sets or other
;;; types of collections.
;;;
;;; Take an abstract mathematical view for a moment.  Given some
;;; predicate P, what we would really like to do is be able to express
;;; the idea that given some collection x, every element of x
;;; satisfies P.  In other words, we want to define:
;;;
;;;  (collection-P x [args]) = forall a in x, (P x [args])
;;;
;;; And indeed, it would be nice to be working with this very abstract
;;; mathematical definition, for which we will not need to make
;;; inductive arguments.  Unfortunately, because all variables in
;;; ACL2's rewrite rules are implicitly universally quantified, we
;;; cannot express the above as a rewrite rule.
;;;
;;; However, through the use of constrained function symbols and
;;; functional instantiation, we can effectively accomplish the above
;;; reduction when it suits our purposes.  And, the process can be
;;; automated through the use of computed hints.  Overall, this is not
;;; as nice as working with a pure rewrite rule, and in fact has some
;;; unfortunate limitations.  However, it does turn out to be very
;;; broadly applicable and invaluable for reasoning about set
;;; theoretic concepts, where concepts such as "subset" are really
;;; nothing more than the extension of the predicate "in" across a
;;; set.
;;;
;;; Moreover, the reduction that we set out to achieve will reduce
;;; (collection-P x [args]) to the following implication:
;;;
;;;   (implies (in a x)
;;;            (P a [args]))
;;;
;;; I call this a "pick a point" reduction, because it is similar to
;;; and takes its inspiration from the well known set theoretic
;;; technique of picking an arbitrary element (or point) in one set,
;;; then showing it is also a member of another set.

;;; Tagging
;;;
;;; Suppose that we have (collection-P x a0 a1 ... an)  to a simpler
;;; argument.  We begin by defining a synonym for collection-P, e.g.,
;;;
;;; (defun collection-P-tag (x a0 a1 ... an) 
;;;   (collection-P x a0 a1 ... an))
;;;
;;; Now we instruct the theorem prover to rewrite instances of
;;; conclusion into conclusion-tag, as long as we are not backchaining
;;; and as long as conclusion occurs as the goal.  For example,
;;;
;;; (defthm tagging-theorem
;;;   (implies 
;;;     (and (syntaxp (rewriting-goal-lit mfc state))
;;;          (syntaxp (rewriting-conc-lit `(collection-P ,x ,a0 ... ,an) 
;;;                                       mfc state)))
;;;            (equal (collection-P x a0 ... an)
;;;                   (collection-P-tag x a0 ... an))))
;;;
;;; This theorem is trivial to prove, since collection-P-tag is merely
;;; a synonym for collection-P.  After the theorem is proven,
;;; collection-P-tag should be disabled.

(defun rewriting-goal-lit (mfc state)
  (declare (xargs :stobjs state)
           (ignore state))
  (null (mfc-ancestors mfc)))

(defun rewriting-conc-lit (term mfc state)
  (declare (xargs :stobjs state)
           (ignore state))
  (let ((clause (mfc-clause mfc)))
    (member-equal term (last clause))))

(defun harvest-trigger (clause trigger-fn)
  (if (endp clause)
      nil
    (if (eq (caar clause) trigger-fn)
        (cons (car clause) (harvest-trigger (cdr clause) trigger-fn))
      (harvest-trigger (cdr clause) trigger-fn))))

(defun others-to-negated-list (others)
  (if (endp others)
      nil
    (if (equal (caar others) 'not)  ; don't create ugly double not's
        (cons (second (car others))
              (others-to-negated-list (cdr others)))
      (cons (list 'not (car others))
            (others-to-negated-list (cdr others))))))

(defun others-to-hyps (others)
  (if (endp others)
      t
    (let ((negated (others-to-negated-list others)))
      (if (endp (cdr negated))  ; don't wrap single literals in and's
          (car negated)
        (cons 'and (others-to-negated-list others))))))

(defun build-hint (trigger                ; list, the actual trigger to use
                   generic-theorem        ; symbol, the name of generic-theorem
                   generic-hyps           ; symbol, the name of (hyps)
                   generic-collection     ; symbol, the name of (collection)
                   generic-predicate      ; symbol, the name of predicate
                   generic-collection-P   ; symbol, the name of collection-P
                   collection-P-sub       ; symbol, name of actual collection-P
                   hyps-sub               ; the computed substitution for hyps
                   predicate-rewrite)     ; rewrite rule for predicate
  (let* ((base-pred (cons generic-predicate (cons '?x (cddr trigger))))
         (pred-sub  (instance-rewrite base-pred predicate-rewrite)))
    `(:functional-instance 
      ,generic-theorem
      (,generic-hyps         
       (lambda () ,hyps-sub))
      (,generic-collection   
       (lambda () ,(second trigger)))
      (,generic-collection-P 
       (lambda (?x) ,(cons collection-P-sub (cons '?x (cddr trigger)))))
      (,generic-predicate 
       (lambda (?x) ,pred-sub)))))

(defun build-hints (triggers
                    generic-theorem
                    generic-hyps
                    generic-collection
                    generic-predicate
                    generic-collection-P
                    collection-P-sub
                    hyps-sub
                    predicate-rewrite)
  (if (endp triggers)
      nil
    (cons (build-hint (car triggers)
                      generic-theorem 
                      generic-hyps
                      generic-collection
                      generic-predicate
                      generic-collection-P
                      collection-P-sub
                      hyps-sub
                      predicate-rewrite)
          (build-hints (cdr triggers)
                       generic-theorem 
                       generic-hyps
                       generic-collection
                       generic-predicate
                       generic-collection-P
                       collection-P-sub
                       hyps-sub
                       predicate-rewrite))))


;;; Of course, some of those hints can be computed.  Here we write a function
;;; to actually provide these hints and install the computed hint function.

(defun automate-instantiation-fn (new-hint-name 
                                  generic-theorem
                                  generic-hyps
                                  generic-collection
                                  generic-predicate
                                  generic-collection-P
                                  collection-P-sub
                                  predicate-rewrite
                                  trigger-symbol
                                  tagging-theorem)
  `(encapsulate ()

     (defun ,new-hint-name (id clause world stable)
       (declare (xargs :mode :program)
                (ignore world))
       (if (not stable)
           nil
         (let ((triggers (harvest-trigger clause ,trigger-symbol)))
           (if (not triggers)
               nil 
             (let* ((others   (set-difference-equal clause triggers))
                    (hyps     (others-to-hyps others))
                    (phrase   (string-for-tilde-@-clause-id-phrase id))
                    (fi-hints (build-hints triggers
                                           ,generic-theorem
                                           ,generic-hyps
                                           ,generic-collection
                                           ,generic-predicate
                                           ,generic-collection-P
                                           ,collection-P-sub
                                           hyps
                                           ,predicate-rewrite))
                    (hints    (list :use fi-hints
                                    :expand triggers)))
               (prog2$ (cw *message* 
                           ,generic-theorem 
                           (list phrase hints) 
                           ,tagging-theorem)
                       hints))))))

     (add-default-hints!
      '((,new-hint-name id clause world stable-under-simplificationp)))

     ))

(defund multiappend (list x)
  (if (consp list)
      (set::multicons (car list)
                      (set::multiappend (cdr list) x))
    (set::sfix x)))

(local (in-theory (enable multiappend)))

(defthm multiappend-set
  (setp (multiappend list X)))

(defthm listsetp-of-multiappend
  (equal (listsetp (multiappend a X))
         (all<true-listp> X))
  :hints (("goal" :in-theory (enable listsetp))))

(defun multiappend-2-induction (list path x)
  (if (and (consp list)
           (consp path))
      (set::multicons (car list)
                      (set::multiappend-2-induction (cdr list) (cdr path) x))
    (cons path (set::sfix x))))

(defthm multiappend-in
  (equal (in path (multiappend a X))
         (and (equal (list::firstn (len a) path) (list::fix a))
              (in (list::nthcdr (len a) path) X)))
  :hints(("Goal" :in-theory (enable list::fix)
          :induct (multiappend-2-induction a path X))))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defund multicons (a X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  (emptyset)
                (insert (cons a (head X))
                        (multicons a (tail X))))
       :exec (if (atom X)
                 nil
               (cons (cons a (car X))
                     (multicons a (cdr X))))))

(local (in-theory (enable multicons)))

(defthm multicons-set
  (setp (multicons a X)))

(defthm listsetp-of-multicons
  (equal (listsetp (multicons a X))
         (all<true-listp> X))
  :hints(("Goal" :in-theory (enable listsetp))))

(defthm multicons-in
  (equal (in path (multicons a X))
         (and (consp path)
              (equal (car path) a)
              (in (cdr path) X)))
  :hints(("Goal" :induct (multicons a X))))

(local (defun multicons-list (a X)
         (declare (xargs :guard t))
         (if (atom X)
             nil
           (cons (cons a (car X))
                 (multicons-list a (cdr X))))))

(local (defthm in-list-multicons-list
         (equal (in-list path (multicons-list a X))
                (and (consp path)
                     (equal (car path) a)
                     (in-list (cdr path) X)))))

(local (defun weakly-ordered-p (x)
         (if (endp x)
             (null x)
           (or (null (cdr x))
               (and (consp (cdr x))
                    (lexorder (car x) (cadr x))
                    (weakly-ordered-p (cdr x)))))))

(local (defthm lexorder-cons
         (equal (lexorder (cons x a) 
                          (cons x b))
                (lexorder a b))
         :hints(("Goal" :in-theory (enable lexorder)))))

(local (defthm multicons-list-weakly-ordered
         (implies (weakly-ordered-p X)
                  (weakly-ordered-p (multicons-list a X)))))

(local (defthm member-equal-elim
         (iff (member-equal a x)
              (in-list a x))))

(local (defthm multicons-list-no-duplicates
         (implies (no-duplicatesp-equal X)
                  (no-duplicatesp-equal (multicons-list a X)))))

(local (defthm setp-redefinition
         (equal (setp x)
                (and (no-duplicatesp-equal x)
                     (weakly-ordered-p x)))
         :hints(("Goal"
                 :induct (setp x)
                 :in-theory (enable setp 
                                    tail
                                    sfix
                                    empty
                                    head
                                    <<
                                    lexorder)))))

(local (defthm setp-multicons-list
         (implies (setp X)
                  (setp (multicons-list a X)))))

(local (defthm in-multicons-list
         (implies (setp X)
                  (equal (in path (multicons-list a X))
                         (and (consp path)
                              (equal (car path) a)
                              (in (cdr path) X))))
         :hints(("Goal" 
                 :in-theory (disable in-list-multicons-list)
                 :use (:instance in-list-multicons-list)))))

(local (defthm lemma
         (implies (and (setp X)
                       (empty X))
                  (equal X nil))
         :rule-classes nil
         :hints(("Goal" :in-theory (enable setp empty)))))

(local (defthm main-lemma
         (implies (setp X)
                  (equal (multicons a X)
                         (multicons-list a X)))
         :hints(("Goal" :in-theory (disable setp-redefinition)
                 :use (:instance lemma)))))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

; -------------------------------------------------------------------
; Delete

(defun delete (a X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (cond ((empty X) nil)
        ((equal a (head X)) (tail X))   
        (t (insert (head X) (delete a (tail X))))))

(defthm delete-set
  (setp (delete a X)))

(defthm delete-preserves-empty
  (implies (empty X)
           (empty (delete a X))))

(defthm delete-in
  (equal (in a (delete b X))
         (and (in a X)
              (not (equal a b)))))

(defthm delete-sfix-cancel
  (equal (delete a (sfix X))
         (delete a X)))

(defthm delete-nonmember-cancel
  (implies (not (in a X))
           (equal (delete a X) (sfix X))))

(defthm delete-delete
  (equal (delete a (delete b X))
         (delete b (delete a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm repeated-delete
  (equal (delete a (delete a X))
         (delete a X)))

(defthm delete-insert-cancel
  (equal (delete a (insert a X))
         (delete a X)))

(defthm insert-delete-cancel
  (equal (insert a (delete a X))
         (insert a X)))

(defthm subset-delete
  (subset (delete a X) X))


; -------------------------------------------------------------------
; Union

(defun union (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  (sfix Y)
                (insert (head X) (union (tail X) Y)))
       :exec  (fast-union X Y)))

(defthm union-set
  (setp (union X Y)))

(defthm union-sfix-cancel-X
  (equal (union (sfix X) Y) (union X Y)))

(defthm union-sfix-cancel-Y
  (equal (union X (sfix Y)) (union X Y)))

(defthm union-empty-X
  (implies (empty X)
           (equal (union X Y) (sfix Y))))

(defthm union-empty-Y
  (implies (empty Y)
           (equal (union X Y) (sfix X))))

(defthm union-empty
  (equal (empty (union X Y))
         (and (empty X) (empty Y))))

(defthm union-in
  (equal (in a (union X Y)) 
         (or (in a X) (in a Y))))

(defthm union-symmetric
  (equal (union X Y) (union Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-subset-X
  (subset X (union X Y)))

(defthm union-subset-Y
  (subset Y (union X Y)))

(defthm union-insert-X
  (equal (union (insert a X) Y)
         (insert a (union X Y))))

(defthm union-insert-Y
  (equal (union X (insert a Y))
         (insert a (union X Y))))

(defthm union-delete-X
  (equal (union (delete a X) Y)
         (if (in a Y)
             (union X Y)
           (delete a (union X Y)))))

(defthm union-delete-Y
  (equal (union X (delete a Y))
         (if (in a X)
             (union X Y)
           (delete a (union X Y)))))

(defthm union-self
  (equal (union X X) (sfix X)))

(defthm union-associative
  (equal (union (union X Y) Z)
         (union X (union Y Z))))

(defthm union-commutative
  (equal (union X (union Y Z))
         (union Y (union X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-outer-cancel
  (equal (union X (union X Z))
         (union X Z)))



; -------------------------------------------------------------------
; Intersect

(defun intersect (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) 
                     (insert (head X) (intersect (tail X) Y)))
                    (t (intersect (tail X) Y)))
       :exec (fast-intersect X Y)))

(defthm intersect-set 
  (setp (intersect X Y)))

(defthm intersect-sfix-cancel-X
  (equal (intersect (sfix X) Y) (intersect X Y)))

(defthm intersect-sfix-cancel-Y
  (equal (intersect X (sfix Y)) (intersect X Y)))

(defthm intersect-empty-X
  (implies (empty X) (empty (intersect X Y))))
 
(defthm intersect-empty-Y
  (implies (empty Y) (empty (intersect X Y))))

(defthm intersect-symmetric
  (equal (intersect X Y) (intersect Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-subset-X
  (subset (intersect X Y) X))

(defthm intersect-subset-Y
  (subset (intersect X Y) Y))

(defthm intersect-insert-X
  (implies (not (in a Y))
           (equal (intersect (insert a X) Y) 
                  (intersect X Y))))

(defthm intersect-insert-Y
  (implies (not (in a X))
           (equal (intersect X (insert a Y))
                  (intersect X Y))))

(defthm intersect-delete-X
  (equal (intersect (delete a X) Y)
         (delete a (intersect X Y))))

(defthm intersect-delete-Y
  (equal (intersect X (delete a Y))
         (delete a (intersect X Y))))

(defthm intersect-self
  (equal (intersect X X) (sfix X)))

(defthm intersect-associative
  (equal (intersect (intersect X Y) Z)
         (intersect X (intersect Y Z))))

(defthm union-over-intersect
  (equal (union X (intersect Y Z))
         (intersect (union X Y) (union X Z))))

(defthm intersect-over-union
  (equal (intersect X (union Y Z))
         (union (intersect X Y) (intersect X Z))))

(defthm intersect-commutative
  (equal (intersect X (intersect Y Z))
         (intersect Y (intersect X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-outer-cancel
  (equal (intersect X (intersect X Z))
         (intersect X Z)))


; -------------------------------------------------------------------
; Difference

(defun difference (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) (difference (tail X) Y))
                    (t (insert (head X) (difference (tail X) Y))))
       :exec (fast-difference X Y)))

(defthm difference-set
  (setp (difference X Y)))

(defthm difference-sfix-X
  (equal (difference (sfix X) Y) (difference X Y)))

(defthm difference-sfix-Y
  (equal (difference X (sfix Y)) (difference X Y)))

(defthm difference-empty-X
  (implies (empty X) 
           (equal (difference X Y) (sfix X))))

(defthm difference-empty-Y
  (implies (empty Y) 
           (equal (difference X Y) (sfix X))))
           
(defthm difference-subset-X
  (subset (difference X Y) X))

(defthm subset-difference
  (equal (empty (difference X Y))
         (subset X Y)))

(defthm difference-over-union
  (equal (difference X (union Y Z))
         (intersect (difference X Y) (difference X Z))))

(defthm difference-over-intersect
  (equal (difference X (intersect Y Z))
         (union (difference X Y) (difference X Z))))

(defthm difference-insert-X
  (equal (difference (insert a X) Y)
         (if (in a Y)
             (difference X Y)
           (insert a (difference X Y)))))

(defthm difference-insert-Y
  (equal (difference X (insert a Y))
         (delete a (difference X Y))))

(defthm difference-delete-X
  (equal (difference (delete a X) Y)
         (delete a (difference X Y))))

(defthm difference-delete-Y
  (equal (difference X (delete a Y))
         (if (in a X)
             (insert a (difference X Y))
           (difference X Y))))

(defthm difference-preserves-subset
  (implies (subset X Y)
           (subset (difference X Z)
                   (difference Y Z))))
         

; -------------------------------------------------------------------
; Cardinality

(defun cardinality (X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  0
                (1+ (cardinality (tail X))))
       :exec  (len X)))

(defthm cardinality-type
  (and (integerp (cardinality X))
       (<= 0 (cardinality X)))
  :rule-classes :type-prescription)

(defthm cardinality-zero-empty
  (equal (equal (cardinality x) 0)             
         (empty x)))

(defthm cardinality-sfix-cancel
  (equal (cardinality (sfix X)) (cardinality X)))

(defthm delete-cardinality
  (equal (cardinality (delete a X))
         (if (in a X)
             (1- (cardinality X))
           (cardinality X))))

; Now that we have the delete function, we can prove an interesting
; theorem, namely that if (subset X Y) and |X| = |Y|, then X = Y.  In
; order to do this, we need to induct by deleting elements from both 
; X and Y.  This is a little ugly, but along the way we will show the
; nice theorem, subset-cardinality.

(defun double-delete-induction (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (if (or (empty X) (empty Y))
      (list X Y)
    (double-delete-induction (delete (head X) X)
                             (delete (head X) Y))))

(defthmd subset-double-delete
  (implies (subset X Y) 
           (subset (delete a X) (delete a Y))))

(defthmd equal-cardinality-subset-is-equality
  (implies (and (setp X) 
                (setp Y)
                (subset X Y)
                (equal (cardinality X) (cardinality Y)))
           (equal (equal X Y) t))
  :hints(("Goal" :induct (double-delete-induction X Y))
         ("Subgoal *1/2" 
          :use ((:instance subset-double-delete
                           (a (head X)) 
                           (X X) 
                           (Y Y))
                (:instance (:theorem 
                  (implies (equal X Y) 
                           (equal (insert a X) (insert a Y))))
                     (a (head X)) 
                     (X (tail X)) 
                     (Y (delete (head X) Y)))))))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y)) (cardinality X))
  :rule-classes :linear)

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y)) (cardinality Y))
  :rule-classes :linear)



; There are also some interesting properties about cardinality which 
; are more precise.

(defthm expand-cardinality-of-union
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm expand-cardinality-of-difference
  (equal (cardinality (difference X Y))
         (- (cardinality X) 
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm intersect-cardinality-subset
  (implies (subset X Y)
           (equal (cardinality (intersect X Y))
                  (cardinality X)))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-non-subset
  (implies (not (subset x y))
           (< (cardinality (intersect x y))
              (cardinality x)))
  :rule-classes :linear)

(defthm intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y)) (cardinality X))
         (subset X Y)))

(defthm intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y)) (cardinality x))
         (not (subset x y))))

;;; Replaced by Matt K. after Jared D.'s modification
;;; in svn 1015 of that book, since there is now a conflict:
(include-book "misc/total-order" :dir :system)
#||
(defun << (x y)
  (declare (xargs :guard t))
  (and (lexorder x y)
       (not (equal x y))))

(defthm <<-type
  (or (equal (<< a b) t)
      (equal (<< a b) nil))
  :rule-classes :type-prescription)

(defthm <<-irreflexive
  (not (<< a a)))

(defthm <<-transitive
  (implies (and (<< a b) (<< b c))
           (<< a c)))

(defthm <<-asymmetric
  (implies (<< a b)
           (not (<< b a))))

(defthm <<-trichotomy
  (implies (and (not (<< b a))
                (not (equal a b)))
           (<< a b)))

(in-theory (disable <<))
||#

;;; Now we can define sets.  Sets are those lists whose elements are
;;; fully ordered under the relation above.  Note that this implicitly
;;; means that sets contain no duplicate elements.  Testing for sets
;;; will inherently be somewhat slow since we have to check that the
;;; elements are in order.  However, its complexity is still only lin-
;;; ear with the size of X.
 
(defun setp (X)
  (declare (xargs :guard t))
  (if (atom X)
      (null X)
    (or (null (cdr X))
        (and (consp (cdr X))
             (<< (car X) (cadr X))
             (setp (cdr X))))))

(defthm setp-type
  (or (equal (setp X) t)
      (equal (setp X) nil))
  :rule-classes :type-prescription)

(defthm sets-are-true-lists
  (implies (setp X)
           (true-listp X)))

(defun empty (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (or (null X)
                  (not (setp X)))
       :exec  (null X)))
 
(defthm empty-type
  (or (equal (empty X) t)
      (equal (empty X) nil))
  :rule-classes :type-prescription)
 
(defun sfix (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X) nil X)
       :exec  X))
 
(defun head (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (car (sfix X))
       :exec  (car X)))
 
(defun tail (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (cdr (sfix X))
       :exec  (cdr X)))
 
(defun insert (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) (list a))
        ((equal (head X) a) X)
        ((<< a (head X)) (cons a X))
        (t (cons (head X) (insert a (tail X))))))

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defthmd setp-list-to-set
  (setp (list-to-set X))
  :hints (("Goal" :in-theory (enable insert))))

;;; Our goal is to "hide" the list primitives (car, cdr, ...) within
;;; head, tail, etc.  This means that an end-user's functions will end
;;; up recurring over tail.  It is therefore important to show that
;;; tail actually decreases some measure, so that they can prove their
;;; functions terminate.  Naturally, we show that acl2-count decreases
;;; with tail.  We also show that acl2-count decreases with head, in
;;; case this fact is needed.
 
(defthm tail-count
  (implies (not (empty X))
           (< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes :linear)

(defthm head-count
  (implies (not (empty X))
           (< (acl2-count (head X)) (acl2-count X)))
  :rule-classes :linear)

;;; Concluding that objects are sets is important for satisfying guard
;;; conjectures, and also for proofs of equality via a double contain-
;;; ment approach.  Here are some nice theorems to help with this:

(defthm sfix-produces-set
  (setp (sfix X)))

(defthm tail-produces-set
  (setp (tail X)))

(defthm insert-produces-set
  (setp (insert a X)))

(defthm nonempty-means-set
  (implies (not (empty X))
           (setp X)))

;;; Does every set have a unique representation?  Yes and no.  It is
;;; true in the sense that, if (setp X) holds, then there is no Y such
;;; that (in a X) <=> (in a Y) except for Y = X.  But what about when
;;; (setp X) does not hold?  Well, technically X is no longer a set,
;;; but our functions treat X as if it were empty.  We would like to
;;; be able to reason about this case.
;;;
;;; Well, although we cannot say (empty X) ^ (empty Y) => X = Y, we
;;; can state several similarly spirited theorems.  For example, we
;;; can say that the heads, tails, sfix's, and results of inserting
;;; elements into X and Y are always the same.  Here are several the-
;;; orems to this effect:

(defthm empty-set-unique
  (implies (and (setp X)
                (setp Y)
                (empty X)
                (empty Y))
           (equal (equal X Y) t)))

(defthm head-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (head X) (head Y)) t)))

(defthm tail-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (tail X) (tail Y)) t)))

(defthm insert-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (insert a X) (insert a Y)) t)))

(defthm sfix-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (sfix X) (sfix Y)) t)))

(defthm head-tail-same
  (implies (and (not (empty X))
                (not (empty Y))
                (equal (head X) (head Y))
                (equal (tail X) (tail Y)))
           (equal (equal X Y) t)))

;;; While the above theorems show a sort of equivalence between empty
;;; sets, it is also important to know what operations preserve and
;;; destroy emptiness.

(defthm insert-never-empty
  (not (empty (insert a X))))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

;;; While it did take quite a few theorems to have enough information
;;; about empty, the sfix function is more simple.  Sfix is the ident-
;;; ity function on sets, and maps all non-sets to nil.  We can show
;;; that all of the other primitives treat have a sort of equivalence
;;; under sfix, and quickly eliminate it when we see it:

(defthm sfix-set-identity
  (implies (setp X)
           (equal (sfix X) X)))

(defthm empty-sfix-cancel
  (equal (empty (sfix X)) (empty X)))

(defthm head-sfix-cancel
  (equal (head (sfix X)) (head X)))

(defthm tail-sfix-cancel
  (equal (tail (sfix X)) (tail X)))

(defthm insert-sfix-cancel
  (equal (insert a (sfix X)) (insert a X)))

;;; Now it is time to reason about insert.  These theorems are about
;;; as most complicated that we get.
;;;
;;; Historic Note: We used to require that nil was "greater than"
;;; everything else in our order.  This had the advantage that the
;;; following theorems could have a combined case for (empty X) and
;;; (<< a (head X)).  Starting in Version 0.9, we remove this res-
;;; triction in order to be more flexible about our order.

(defthm head-insert
  (equal (head (insert a X))
         (cond ((empty X) a)
               ((<< a (head X)) a)
               (t (head X)))))

(defthm tail-insert
  (equal (tail (insert a X))
         (cond ((empty X) (sfix X))
               ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthm insert-insert
  (equal (insert a (insert b X))
         (insert b (insert a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm repeated-insert
  (equal (insert a (insert a X))
         (insert a X)))

(defthm insert-head
  (implies (not (empty X))
           (equal (insert (head X) X) X)))

(defthm insert-head-tail
  (implies (not (empty X))
           (equal (insert (head X) (tail X)) X)))

;;; We also need to be able to reason about insertions into empty
;;; sets.  Do not move these theorems above head-insert and
;;; tail-insert, or they will be subsumed and proofs in
;;; membership.lisp will fail.

(defthm head-insert-empty
  (implies (empty X) 
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
            (empty (tail (insert a X)))))

;;; Insert can be reasoned about in terms of induction, but its induc-
;;; tive case contains a call to "cons", and we cannot let that escape
;;; into the wild.  Instead, we write a theorem to rephrase this cons
;;; into an insert.  WARNING: This can cause loops.  It is disabled by
;;; default for this reason.

(defthmd insert-induction-case
  (implies (and (not (empty X))
                (not (equal a (head X)))
                (not (<< a (head X))))
           (equal (insert a X)
                  (insert (head X) (insert a (tail X))))))

;;; The last thing we really need to do is reason about element order.
;;; The following theorems are crucial for proofs in the membership
;;; level, which must stricly use induction and arguments about the
;;; set elements' order for proofs.  Since we are disabling all of
;;; the functions at the end of this book, these are the only facts
;;; which membership.lisp will be able to use.

(defthm head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthm head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(defthm head-not-head-tail
  (implies (not (empty (tail X)))
           (not (equal (head X) (head (tail X))))))

;;; Finally, this is an obscure looking theorem, which is only used to
;;; prove (not (in X X)) in membership.lisp.  TODO: Make sure it gets
;;; disabled afterwards.  This is a really odd theorem to just leave
;;; lying around enabled.

(defthm head-not-whole
  (implies (not (empty X))
           (not (equal (head X) X))))

(in-theory (disable primitives-theory
                    primitive-order-theory))

#| 
   Multi-Argument Predicates.

   You can also quantify over predicates with many arguments.  As an 
   example, we introduce the function lessp as follows:

     (defun lessp (a b) 
       (declare (xargs :guard t))
       (< (rfix a) (rfix b)))
  
     (quantify-predicate (lessp a b))

|#

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

;; We introduce "list versions" of the functions so that we can reason
;; through mergesorts.

  (defun all-list (list-for-all-reduction) 
    (declare (xargs :guard (true-listp list-for-all-reduction)))
    (if (endp list-for-all-reduction)
        t
      (and (predicate (car list-for-all-reduction))
           (all-list (cdr list-for-all-reduction)))))

  (defun exists-list (x)
    (declare (xargs :guard (true-listp x)))
    (cond ((endp x) nil)
          ((predicate (car x)) t)
          (t (exists-list (cdr x)))))

  (defun find-list (x)
    (declare (xargs :guard (true-listp x)))
    (cond ((endp x) nil)
          ((predicate (car x)) (car x))
          (t (find-list (cdr x)))))
 
  (defun filter-list (x)
    (declare (xargs :guard (true-listp x)))
    (cond ((endp x) nil)
          ((predicate (car x)) 
           (cons (car x) (filter-list (cdr x))))
          (t (filter-list (cdr x)))))


;; We also introduce "set versions" of the functions, so that we can
;; reason about sets.

  (defun all (set-for-all-reduction) 
    (declare (xargs :guard (setp set-for-all-reduction)))
    (if (empty set-for-all-reduction)
        t
      (and (predicate (head set-for-all-reduction))
           (all (tail set-for-all-reduction)))))

  (defun exists (X)
    (declare (xargs :guard (setp X)))
    (cond ((empty X) nil)
          ((predicate (head X)) t)
          (t (exists (tail X)))))

  (defun find (X)
    (declare (xargs :guard (setp X)))
    (cond ((empty X) nil)
          ((predicate (head X)) (head X))
          (t (find (tail X)))))

  (defun filter (X)
    (declare (xargs :guard (setp X)))
    (declare (xargs :verify-guards nil))
    (cond ((empty X) (sfix X))
          ((predicate (head X))
           (insert (head X) (filter (tail X))))
          (t (filter (tail X)))))

; We begin with several theorems about the "list versions" of the 
; above functions.

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
  
  (defthm all-list-in
    (implies (and (all-list x)
                  (in-list a x))
             (predicate a)))

  (defthm all-list-in-2
    (implies (and (all-list x)
                  (not (predicate a)))
             (not (in-list a x))))

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
    (equal (in-list a (filter-list x))
             (and (predicate a)
                (in-list a x))))

  (defthm filter-list-all-list
    (all-list (filter-list x)))

; Set Theory Reasoning

; Of course, really we are more interested in reasoning about sets 
; than lists.  We write several theorems about our set functions.

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

; In order to reason past a mergesort, we need to provide some 
; theorems that tie together our list and set theories.  We begin
; this here.

  (defthm all-mergesort
    (equal (all (mergesort X))
           (all-list X)))

  (defthm all-list-applied-to-set
    (implies (setp X)
             (equal (all-list X)
                    (all X)))
    :hints(("Goal" :in-theory (enable setp empty sfix head tail))))

; -------------------------------------------------------------------
;
;                   Instancing Concrete Theories
;
; -------------------------------------------------------------------

; Each concrete theory we instantiate will require the introduction of
; 16 new functions and a wealth of theorems.  We don't want to
; overburden the user with having to instantiate all of these and give
; them names, so we adopt a naming convention where the predicate's
; name is used to generate the names of the new functions.  Of course,
; we still have to generate the new names.

(defun mksym (name sym)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (string-upcase name) sym))

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
        

(defun quantify-simple-predicate (predicate in-package 
                                  set-guard list-guard arg-guard)
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
         (enable-hints<p>    (mksym (app "enable-hints" wrap) in-package))
         (disable-hints<p>   (mksym (app "disable-hints" wrap) in-package))

         ;; And we create a substitution list, to instantiate the
         ;; generic theory/functions with their new, concrete values.

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

         ;; We use this hack to support alternate guards.  We
         ;; basically use our rewriter to inject the extra guards into
         ;; the function's existing guards.

         (fn-subs 
          (list* `((declare (xargs :guard (true-listp ?list)))
                   (declare (xargs :guard (and (true-listp ?list) 
                                               ,@list-guard
                                               ,@arg-guard))))
                 `((declare (xargs :guard (setp ?set)))
                   (declare (xargs :guard (and (setp ?set) 
                                               ,@set-guard
                                               ,@arg-guard))))
                 subs))

         ;; And we make some symbols for use in automating the all-by-membership
         ;; strategy with computed hints.

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

    `(encapsulate nil

        ;; It's now quite easy to instantiate all of our functions.

        (instance-*functions* 
           :subs ,fn-subs 
           :suffix ,name)

        ;; And similarly we can instantiate all of the theorems.

        (instance-*theorems* 
           :subs ,subs 
           :suffix ,(mksym wrap in-package))

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
                              '((:definition ,all-trigger<p>))))))

        (defthm ,all-strategy<not-p>
          (implies (and (syntaxp (rewriting-goal-lit mfc state))
                        (syntaxp (rewriting-conc-lit (list ',all<not-p> ,@args)
                                  mfc state)))
                   (equal (,all<not-p> ,@args)
                          (,all-trigger<not-p> ,@args)))
          :hints(("Goal" 
                  :in-theory (union-theories 
                              (theory 'minimal-theory)
                              '((:definition ,all-trigger<not-p>))))))

        (defthm ,all-list-strategy<p>
          (implies (and (syntaxp (rewriting-goal-lit mfc state))
                        (syntaxp (rewriting-conc-lit (list ',all-list<p> ,@args)
                                  mfc state)))
                   (equal (,all-list<p> ,@args)
                          (,all-list-trigger<p> ,@args)))
          :hints(("Goal" 
                  :in-theory (union-theories 
                              (theory 'minimal-theory)
                              '((:definition ,all-list-trigger<p>))))))

        (defthm ,all-list-strategy<not-p>
          (implies (and (syntaxp (rewriting-goal-lit mfc state))
                        (syntaxp (rewriting-conc-lit (list ',all-list<not-p> ,@args)
                                  mfc state)))
                   (equal (,all-list<not-p> ,@args)
                          (,all-list-trigger<not-p> ,@args)))
          :hints(("Goal" 
                  :in-theory (union-theories 
                              (theory 'minimal-theory)
                              '((:definition ,all-list-trigger<not-p>))))))

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

        (defmacro ,enable-hints<p> ()
          (list 'add-default-hints! 
           (list 'quote
                '((,(mksym (app "all-by-membership-hint" wrap) in-package)
                   id clause world stable-under-simplificationp)
                  (,(mksym (app "all-by-membership-hint" not-wrap) in-package)
                   id clause world stable-under-simplificationp)
                  (,(mksym (app "all-list-by-membership-hint" wrap) in-package)
                   id clause world stable-under-simplificationp)
                  (,(mksym (app "all-list-by-membership-hint" not-wrap) in-package)
                   id clause world stable-under-simplificationp)
                  ))))

        (defmacro ,disable-hints<p> ()
          (list 'remove-default-hints! 
            (list 'quote
                  '((,(mksym (app "all-by-membership-hint" wrap) in-package)
                     id clause world stable-under-simplificationp)
                    (,(mksym (app "all-by-membership-hint" not-wrap) in-package)
                     id clause world stable-under-simplificationp)
                    (,(mksym (app "all-list-by-membership-hint" wrap) in-package)
                     id clause world stable-under-simplificationp)
                    (,(mksym (app "all-list-by-membership-hint" not-wrap) in-package)
                     id clause world stable-under-simplificationp)
                    ))))

        (instance-*final-theorems* 
         :subs ,subs 
         :suffix ,(mksym wrap in-package))
         ;:extra-defs (empty))


        (verify-guards ,filter<p>)
        (verify-guards ,filter<not-p>)

        ;; In the end, we want to create a deftheory event so that you can
        ;; easily turn off the reasoning about these functions when you 
        ;; don't need it.  We do that with the following event:

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
                                   set-guard list-guard arg-guard)
  (quantify-simple-predicate predicate 
                             (if in-package-of in-package-of 'in)
                             (standardize-to-package "?SET" '?set set-guard)
                             (standardize-to-package "?LIST" '?list list-guard)
                             arg-guard))



(in-theory (disable generic-quantification-theory))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))


; -------------------------------------------------------------------
; order-reasoning

(defthmd <<-type
  (or (equal (<< a b) t)
      (equal (<< a b) nil))
  :rule-classes :type-prescription)

(defthmd <<-irreflexive
  (not (<< a a)))

(defthmd <<-transitive
  (implies (and (<< a b) (<< b c))
           (<< a c)))

(defthmd <<-asymmetric
  (implies (<< a b)
           (not (<< b a))))

(defthmd <<-trichotomy
  (implies (and (not (<< b a))
                (not (equal a b)))
           (<< a b)))

(defthmd head-insert
  (equal (head (insert a X))
         (cond ((empty X) a)
               ((<< a (head X)) a)
               (t (head X)))))

(defthmd tail-insert
  (equal (tail (insert a X))
         (cond ((empty X) (sfix X))
               ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthmd head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthmd head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

; -------------------------------------------------------------------
; cons-reasoning

(defthmd cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X)))))

(defthmd cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a)))

(defthmd cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X))))

(defthmd cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X))))

(defthmd cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))

;;
;; bzo start of stuff from jared - make this into a separate book?
;;

(defstub generic-pred (x) t)

(defstub process (x) t)

(defund process-set (set)
  (if (set::empty set)
      (set::emptyset)
    (let ((v (set::head set)))
      (if (generic-pred v)
          (set::insert (process v)
                  (process-set (set::tail set)))
        (process-set (set::tail set))))))

(defund filter-generic-pred (x)
  ;;  filter-generic-pred(x) = { x | (v \in x) ^ (generic-pred v) }
  (if (set::empty x)
      (set::emptyset)
    (let ((v (set::head x)))
      (if (generic-pred v)
          (set::insert v (filter-generic-pred (set::tail x)))
        (filter-generic-pred (set::tail x))))))

(defund process-all (x)
  ;; process-all(x) = { (process v) | v \in x }
  (if (set::empty x)
      (set::emptyset)
    (set::insert (process (set::head x))
            (process-all (set::tail x)))))

;; Now we can say that process-set is actually the following non-recursive
;; function, which just composes these two operations.

(defund my-process-set (x)
  (process-all (filter-generic-pred x)))

;; By breaking it up like this we can now reason about each part
;; separately and then talk about why process-all is hard to reason about.  To
;; begin, notice how well we can reason about filter-generic-pred, e.g., below.

(defthm setp-of-filter-generic-pred
  (set::setp (filter-generic-pred x))
  :hints(("Goal" :in-theory (enable filter-generic-pred))))

;; Unfortunately the process-all function is much more complicated.  We can
;; still easily say that it produces a set...

(defthm setp-of-process-all
  (set::setp (process-all x))
  :hints(("Goal" :in-theory (enable process-all))))

;; But what is the membership propery here?  It isn't as easy to say.  Really,
;; what we have is the following:
;;
;;   (set::in a (process-all x))
;;     =
;;   exists b in x such that (process b) = a.
;;
;; There are a few different ways we might introduce this.  One way would be to
;; just write a recursive function to try to see if such a b exists, e.g., as
;; below.

(defund has-process-inverse (a x)
  ;; (has-process-inverse a x) = exists b in x such that (process b) = a
  (if (set::empty x)
      nil
    (or (equal a (process (set::head x)))
       (has-process-inverse a (set::tail x)))))

;; Now we can say the following thing about membership in process-all.  It's
;; probably not very clear that we want to do this yet, but maybe since
;; has-process-inverse is a relatively simple function, there will be nice
;; properties about it that we can prove.

(defthm in-process-all
  (equal (set::in a (process-all x))
         (has-process-inverse a x))
  :hints(("Goal" :in-theory (enable process-all has-process-inverse))))

;; And now we have:

(defthm setp-of-my-process-set
  (set::setp (my-process-set x))
  :hints(("Goal" :in-theory (enable my-process-set))))

(defthm in-my-process-set
  (equal (set::in a (my-process-set x))
         (has-process-inverse a (filter-generic-pred x)))
  :hints(("Goal" :in-theory (enable my-process-set))))

;; Well, now lets just imagine that we wanted to prove the MBE equivalence
;; of process-set and my-process-set.  We can first note that process-set
;; creates a set.

(defthm setp-of-process-set
  (set::setp (process-set x))
  :hints(("Goal" :in-theory (enable process-set))))

;; Well then, all we need to do is prove the membership property for
;; process-set is the same as for in-process-all.  In other words, we
;; need to prove:
;;
;;   (set::in a (process-set x)) = (has-process-inverse a
;;                                                      (filter-generic-pred x))
;;
;; It took me awhile to prove this.  I haven't bothered to clean up the
;; lemmas I used, so this is reallly ugly. sorry.

(defthm subset-of-filter-each-when-subset
  (implies (set::subset x y)
           (set::subset (filter-generic-pred x) (filter-generic-pred y)))
  :hints(("Goal"
          ;; may not need to do this later
          :in-theory (enable set::subset))))

(defthm has-process-inverse-when-in
  (implies (set::in a x)
           (has-process-inverse (process a) x))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-equal-to-process-member
  (implies (and (set::in b x)
                (equal (process b) a))
           (has-process-inverse a x))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-has-process-inverse-of-subset
  (implies (and (set::subset x y)
                (has-process-inverse a x))
           (has-process-inverse a y))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-has-process-inverse-of-subset-alt
  (implies (and (has-process-inverse a x)
                (set::subset x y))
           (has-process-inverse a y)))

(defthm goal-both
  (implies (set::setp x)
           (equal (process-set (set::insert a x))
                  (if (generic-pred a)
                      (set::insert (process a)
                                   (process-set x))
                    (process-set x))))
  :hints (("Goal" :in-theory (disable MBE-EQUIVALENCE))))

;;bzo add to sets?
;disabling, since showed up high in accumulated persistence
(defthmd insert-into-non-setp
  (implies (NOT (SET::SETP X))
           (equal (SET::INSERT A X)
                  (SET::INSERT A (set::emptyset)))))

(local (in-theory (enable insert-into-non-setp)))

(defthm tail-of-singleton
  (equal (SET::TAIL (SET::INSERT A NIL))
         nil)
  :hints (("Goal" :in-theory (enable SET::INSERT SET::TAIL SET::SFIX))))

;bzo uncomment thos...
(defthm goal-both-better
  (equal (process-set (set::insert a x))
         (if (generic-pred a)
             (set::insert (process a)
                          (process-set x))
           (process-set x)))
  :hints (("Goal" :use (:instance goal-both)
           :expand (PROCESS-ALL (SET::INSERT A NIL))
           :in-theory (e/d (SET::EMPTY
                            FILTER-GENERIC-PRED
                            MY-PROCESS-SET)(goal-both)))))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))


; We begin with the definitions of the set theory functions and a 
; few trivial type prescriptions.

;;; Replaced by Matt K. after Jared D.'s modification
;;; in svn 1015 of that book, since there is now a conflict:
(include-book "misc/total-order" :dir :system)
#||
(defund << (x y)
  (declare (xargs :guard t))
  (and (lexorder x y)
       (not (equal x y))))
||#

(defund setp (X)
  (declare (xargs :guard t))
  (if (atom X)
      (null X)
    (or (null (cdr X))
        (and (consp (cdr X))
             (<< (car X) (cadr X))
             (setp (cdr X))))))

(defthm setp-type
  (or (equal (setp X) t)
      (equal (setp X) nil))
  :rule-classes :type-prescription)

(defund empty (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (or (null X)
                  (not (setp X)))
       :exec  (null X)))

(defthm empty-type
  (or (equal (empty X) t)
      (equal (empty X) nil))
  :rule-classes :type-prescription)

(defund sfix (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X) nil X)
       :exec  X))

(defund head (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (car (sfix X))
       :exec  (car X)))

(defund tail (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (cdr (sfix X))
       :exec  (cdr X)))

(defund insert (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) (list a))
        ((equal (head X) a) X)
        ((<< a (head X)) (cons a X))
        (t (cons (head X) (insert a (tail X))))))

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defun in (a X)
  (declare (xargs :guard (setp X)))
  (and (not (empty X))
       (or (equal a (head X))
           (in a (tail X)))))

(defthmd open-set-in
  (implies
   (and
    (syntaxp (quotep x))
    (not (empty x)))
   (equal (in a x)
          (or (equal a (head x))
              (in a (tail x))))))

(defthm in-type
  (or (equal (in a X) t)
      (equal (in a X) nil))
  :rule-classes :type-prescription)

(defund fast-subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (cond ((empty X) t)
        ((empty Y) nil)
        ((<< (head X) (head Y)) nil)
        ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
        (t (fast-subset X (tail Y)))))

(defun subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (if (empty X)
                  t
                (and (in (head X) Y)
                     (subset (tail X) Y)))
       :exec (fast-subset X Y)))

(defthm subset-type
  (or (equal (subset X Y) t)
      (equal (subset X Y) nil))
  :rule-classes :type-prescription)

(defund fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))

(defund fast-union (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) Y)
        ((empty Y) X)
        ((equal (head X) (head Y))
         (cons (head X) (fast-union (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (cons (head X) (fast-union (tail X) Y)))
        (t (cons (head Y) (fast-union X (tail Y))))))

(defund fast-intersect (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) (sfix Y))
        ((equal (head X) (head Y))
         (cons (head X)
               (fast-intersect (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (fast-intersect (tail X) Y))
        (t (fast-intersect X (tail Y)))))

(defund fast-difference (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) X)
        ((equal (head X) (head Y))
         (fast-difference (tail X) (tail Y)))
        ((<< (head X) (head Y))
         (cons (head X) (fast-difference (tail X) Y)))
        (t (fast-difference X (tail Y)))))

(defun delete (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((equal a (head X)) (tail X))
        (t (insert (head X) (delete a (tail X))))))

(defun union (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (if (empty X)
                  (sfix Y)
                (insert (head X) (union (tail X) Y)))
       :exec  (fast-union X Y)))

(defun intersect (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y)
                     (insert (head X) (intersect (tail X) Y)))
                    (t (intersect (tail X) Y)))
       :exec (fast-intersect X Y)))

(defun difference (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) (difference (tail X) Y))
                    (t (insert (head X) (difference (tail X) Y))))
       :exec (fast-difference X Y)))

(defun cardinality (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X)
                  0
                (1+ (cardinality (tail X))))
       :exec  (len X)))

(defund split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((endp (cdr x)) (mv (list (car x)) nil))
        (t (mv-let (part1 part2)
                   (split-list (cddr x))
                   (mv (cons (car x) part1)
                       (cons (cadr x) part2))))))

(defun in-list (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (or (equal a (car x))
        (in-list a (cdr x)))))

(defun mergesort-exec (x)
  (declare (xargs :measure (len x) :guard (true-listp x)))
  (cond ((endp x) nil)
        ((endp (cdr x)) (insert (car x) nil))
        (t (mv-let (part1 part2)
                   (split-list x)
                   (union (mergesort-exec part1) (mergesort-exec part2))))))

(defun mergesort (x)
  (declare (xargs :guard (true-listp x)))
  (mbe :logic (if (endp x)
                  nil
                (insert (car x)
                        (mergesort (cdr x))))
       :exec (mergesort-exec x)))

(defun all (set-for-all-reduction)
  (declare (xargs :guard (setp set-for-all-reduction)))
  (if (empty set-for-all-reduction)
      t
    (and (predicate (head set-for-all-reduction))
         (all (tail set-for-all-reduction)))))

(defthmd all-by-membership
  (implies (all-hyps)
           (all (all-set))))

(defund subset-trigger (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (subset X Y))

(defthm pick-a-point-subset-strategy
  (implies (and (syntaxp (rewriting-goal-lit mfc state))
                (syntaxp (rewriting-conc-lit `(subset ,X ,Y) mfc state)))
           (equal (subset X Y)
                  (subset-trigger X Y))))

(defthm double-containment
  (implies (and (setp X)
                (setp Y))
           (equal (equal X Y)
                  (and (subset X Y)
                       (subset Y X)))))

; -------------------------------------------------------------------
; Primitives Level Theorems

(defthm sets-are-true-lists
  (implies (setp X)
           (true-listp X)))

(defthm tail-count
  (implies (not (empty X))
           (< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes :linear)

(defthm head-count
  (implies (not (empty X))
           (< (acl2-count (head X)) (acl2-count X)))
  :rule-classes :linear)

(defthm insert-insert
  (equal (insert a (insert b X))
         (insert b (insert a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm sfix-produces-set
  (setp (sfix X)))

(defthm tail-produces-set
  (setp (tail X)))

(defthm insert-produces-set
  (setp (insert a X)))

(defthm insert-never-empty
  (not (empty (insert a X))))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

(defthm nonempty-means-set
  (implies (not (empty X)) (setp X)))

(defthm sfix-set-identity
  (implies (setp X) (equal (sfix X) X)))

(defthm empty-sfix-cancel
  (equal (empty (sfix X)) (empty X)))

(defthm head-sfix-cancel
  (equal (head (sfix X)) (head X)))

(defthm tail-sfix-cancel
  (equal (tail (sfix X)) (tail X)))

(defthm insert-head-tail
  (implies (not (empty X))
           (equal (insert (head X) (tail X)) X)))

(defthm repeated-insert
  (equal (insert a (insert a X))
         (insert a X)))

(defthm insert-sfix-cancel
  (equal (insert a (sfix X)) (insert a X)))

(defthm head-insert-empty
  (implies (empty X)
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
           (empty (tail (insert a X)))))

; -------------------------------------------------------------------
; Membership Level Theorems

(defthm not-in-self
  (not (in x x)))

(defthm in-sfix-cancel
  (equal (in a (sfix X)) (in a X)))

(defthm never-in-empty
  (implies (empty X) (not (in a X))))

(defthm in-set
  (implies (in a X) (setp X)))

(defthm in-head
  (equal (in (head X) X)
         (not (empty X))))

(defthm in-tail
  (implies (in a (tail X)) (in a X)))

(defthm in-tail-or-head
  (implies (and (in a X) (not (in a (tail X))))
           (equal (head X) a)))

(defthm head-unique
  (not (in (head X) (tail X))))

(defthm insert-identity
  (implies (in a X) (equal (insert a X) X)))

(defthm in-insert
  (equal (in a (insert b X))
         (or (in a X)
             (equal a b))))

(defthm subset-transitive
  (implies (and (subset X Y) (subset Y Z))
           (subset X Z)))

(defthm subset-insert-X
  (equal (subset (insert a X) Y)
         (and (subset X Y)
              (in a Y))))

(defthm subset-sfix-cancel-X
  (equal (subset (sfix X) Y) (subset X Y)))

(defthm subset-sfix-cancel-Y
  (equal (subset X (sfix Y)) (subset X Y)))

(defthm subset-in
  (implies (and (subset X Y) (in a X))
           (in a Y)))

(defthm subset-in-2
  (implies (and (subset X Y) (not (in a Y)))
           (not (in a X))))

(defthm empty-subset
  (implies (empty X) (subset X Y)))

(defthm empty-subset-2
  (implies (empty Y)
           (equal (subset X Y) (empty X))))

(defthm subset-reflexive
  (subset X X))

(defthm subset-insert
  (subset X (insert a X)))

(defthm subset-tail
  (subset (tail X) X)
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((tail x)))))

; -------------------------------------------------------------------
; Weakly Inducting over Insertions

(defthmd weak-insert-induction-helper-1
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (head (insert a X)) (head X))))

(defthmd weak-insert-induction-helper-2
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (tail (insert a X)) (insert a (tail X)))))

(defthmd weak-insert-induction-helper-3
  (implies (and (not (in a X))
                (equal (head (insert a X)) a))
           (equal (tail (insert a X)) (sfix X))))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defun weak-insert-induction (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((in a X) nil)
        ((equal (head (insert a X)) a) nil)
        (t (list (weak-insert-induction a (tail X))))))

(defthm use-weak-insert-induction t
  :rule-classes ((:induction
                  :pattern (insert a X)
                  :scheme (weak-insert-induction a X))))

; -------------------------------------------------------------------
; Outer Level Theorems

(defthm delete-delete
  (equal (delete a (delete b X))
         (delete b (delete a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm delete-set
  (setp (delete a X)))

(defthm delete-preserves-empty
  (implies (empty X)
           (empty (delete a X))))

(defthm delete-in
  (equal (in a (delete b X))
         (and (in a X)
              (not (equal a b)))))

(defthm delete-sfix-cancel
  (equal (delete a (sfix X))
         (delete a X)))

(defthm delete-nonmember-cancel
  (implies (not (in a X))
           (equal (delete a X) (sfix X))))

(defthm repeated-delete
  (equal (delete a (delete a X))
         (delete a X)))

(defthm delete-insert-cancel
  (equal (delete a (insert a X))
         (delete a X)))

(defthm insert-delete-cancel
  (equal (insert a (delete a X))
         (insert a X)))

(defthm subset-delete
  (subset (delete a X) X))

(defthm union-symmetric
  (equal (union X Y) (union Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-commutative
  (equal (union X (union Y Z))
         (union Y (union X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-insert-X
  (equal (union (insert a X) Y)
         (insert a (union X Y))))

(defthm union-insert-Y
  (equal (union X (insert a Y))
         (insert a (union X Y))))

(defthm union-delete-X
  (equal (union (delete a X) Y)
         (if (in a Y)
             (union X Y)
           (delete a (union X Y)))))

(defthm union-delete-Y
  (equal (union X (delete a Y))
         (if (in a X)
             (union X Y)
           (delete a (union X Y)))))

(defthm union-set
  (setp (union X Y)))

(defthm union-sfix-cancel-X
  (equal (union (sfix X) Y) (union X Y)))

(defthm union-sfix-cancel-Y
  (equal (union X (sfix Y)) (union X Y)))

(defthm union-empty-X
  (implies (empty X)
           (equal (union X Y) (sfix Y))))

(defthm union-empty-Y
  (implies (empty Y)
           (equal (union X Y) (sfix X))))

(defthm union-empty
  (equal (empty (union X Y))
         (and (empty X) (empty Y))))

(defthm union-in
  (equal (in a (union X Y))
         (or (in a X) (in a Y))))

(defthm union-subset-X
  (subset X (union X Y)))

(defthm union-subset-Y
  (subset Y (union X Y)))

(defthm union-self
  (equal (union X X) (sfix X)))

(defthm union-associative
  (equal (union (union X Y) Z)
         (union X (union Y Z))))

(defthm union-outer-cancel
  (equal (union X (union X Z))
         (union X Z)))

(defthm intersect-symmetric
  (equal (intersect X Y) (intersect Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-insert-X
  (implies (not (in a Y))
           (equal (intersect (insert a X) Y)
                  (intersect X Y))))

(defthm intersect-insert-Y
  (implies (not (in a X))
           (equal (intersect X (insert a Y))
                  (intersect X Y))))

(defthm intersect-delete-X
  (equal (intersect (delete a X) Y)
         (delete a (intersect X Y))))

(defthm intersect-delete-Y
  (equal (intersect X (delete a Y))
         (delete a (intersect X Y))))

(defthm intersect-set
  (setp (intersect X Y)))

(defthm intersect-sfix-cancel-X
  (equal (intersect (sfix X) Y) (intersect X Y)))

(defthm intersect-sfix-cancel-Y
  (equal (intersect X (sfix Y)) (intersect X Y)))

(defthm intersect-empty-X
  (implies (empty X) (empty (intersect X Y))))

(defthm intersect-empty-Y
  (implies (empty Y) (empty (intersect X Y))))

(defthm intersect-in
  (equal (in a (intersect X Y))
         (and (in a Y) (in a X))))

(defthm intersect-subset-X
  (subset (intersect X Y) X))

(defthm intersect-subset-Y
  (subset (intersect X Y) Y))

(defthm intersect-self
  (equal (intersect X X) (sfix X)))

(defthm intersect-associative
  (equal (intersect (intersect X Y) Z)
         (intersect X (intersect Y Z))))

(defthmd union-over-intersect
  (equal (union X (intersect Y Z))
         (intersect (union X Y) (union X Z))))

(defthm intersect-over-union
  (equal (intersect X (union Y Z))
         (union (intersect X Y) (intersect X Z))))

(defthm intersect-commutative
  (equal (intersect X (intersect Y Z))
         (intersect Y (intersect X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-outer-cancel
  (equal (intersect X (intersect X Z))
         (intersect X Z)))

(defthm difference-set
  (setp (difference X Y)))

(defthm difference-sfix-X
  (equal (difference (sfix X) Y) (difference X Y)))

(defthm difference-sfix-Y
  (equal (difference X (sfix Y)) (difference X Y)))

(defthm difference-empty-X
  (implies (empty X)
           (equal (difference X Y) (sfix X))))

(defthm difference-empty-Y
  (implies (empty Y)
           (equal (difference X Y) (sfix X))))

(defthm difference-in
  (equal (in a (difference X Y))
         (and (in a X)
              (not (in a Y)))))

(defthm difference-subset-X
  (subset (difference X Y) X))

(defthm subset-difference
  (equal (empty (difference X Y))
         (subset X Y)))

(defthm difference-over-union
  (equal (difference X (union Y Z))
         (intersect (difference X Y) (difference X Z))))

(defthm difference-over-intersect
  (equal (difference X (intersect Y Z))
         (union (difference X Y) (difference X Z))))

(defthm difference-insert-X
  (equal (difference (insert a X) Y)
         (if (in a Y)
             (difference X Y)
           (insert a (difference X Y)))))

(defthm difference-insert-Y
  (equal (difference X (insert a Y))
         (delete a (difference X Y))))

(defthm difference-delete-X
  (equal (difference (delete a X) Y)
         (delete a (difference X Y))))

(defthm difference-delete-Y
  (equal (difference X (delete a Y))
         (if (in a X)
             (insert a (difference X Y))
           (difference X Y))))

(defthm difference-preserves-subset
  (implies (subset X Y)
           (subset (difference X Z)
                   (difference Y Z))))

(defthm cardinality-type
  (and (integerp (cardinality X))
       (<= 0 (cardinality X)))
  :rule-classes :type-prescription)

(defthm cardinality-zero-empty
  (equal (equal (cardinality x) 0)
         (empty x)))

(defthm cardinality-sfix-cancel
  (equal (cardinality (sfix X)) (cardinality X)))

(defthm insert-cardinality
  (equal (cardinality (insert a X))
         (if (in a X)
             (cardinality X)
           (1+ (cardinality X)))))

(defthm delete-cardinality
  (equal (cardinality (delete a X))
         (if (in a X)
             (1- (cardinality X))
           (cardinality X))))

(defthm subset-cardinality
  (implies (subset X Y)
           (<= (cardinality X) (cardinality Y)))
  :rule-classes (:rewrite :linear))

(defthmd equal-cardinality-subset-is-equality
  (implies (and (setp X)
                (setp Y)
                (subset X Y)
                (equal (cardinality X) (cardinality Y)))
           (equal (equal X Y) t)))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y)) (cardinality X))
  :rule-classes :linear)

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y)) (cardinality Y))
  :rule-classes :linear)

(defthm expand-cardinality-of-union
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm expand-cardinality-of-difference
  (equal (cardinality (difference X Y))
         (- (cardinality X)
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm intersect-cardinality-subset
  (implies (subset X Y)
           (equal (cardinality (intersect X Y))
                  (cardinality X)))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-non-subset
  (implies (not (subset x y))
           (< (cardinality (intersect x y))
              (cardinality x)))
  :rule-classes :linear)

(defthm intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y)) (cardinality X))
         (subset X Y)))

(defthm intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y)) (cardinality x))
         (not (subset x y))))

; -------------------------------------------------------------------
; Mergesort Theorems

(defthm in-list-cons
  (equal (in-list a (cons b x))
         (or (equal a b)
             (in-list a x))))

(defthm in-list-append
  (equal (in-list a (append x y))
         (or (in-list a x)
             (in-list a y))))

(defthm in-list-revappend
  (equal (in-list a (revappend x y))
         (or (in-list a x)
             (in-list a y))))

(defthm in-list-reverse
  (equal (in-list a (reverse x))
         (in-list a x)))

(defthm in-list-on-set
  (implies (setp X)
           (equal (in-list a X)
                  (in a X))))

(defthm mergesort-set
  (setp (mergesort x)))

(defthm in-mergesort
  (equal (in a (mergesort x))
         (in-list a x)))

(defthm mergesort-set-identity
  (implies (setp X)
           (equal (mergesort X) X)))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

; A List Membership Function
;
; The current member-equal function has weird semantics, returning a
; list rather than a boolean value.  We provide a convenient
; alternative which always returns t or nil instead.
;
; We don't try to develop a complete theory for this function here,
; but we will provide several useful utility theorems for relating in
; with the common list functions such as cons, append, and reverse.
; In the future we might want to expand this section to include more
; theorems.

(defun in-list (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (or (equal a (car x))
        (in-list a (cdr x)))))

(defthm in-list-cons
  (equal (in-list a (cons b x))
         (or (equal a b)
             (in-list a x))))

(defthm in-list-append
  (equal (in-list a (append x y))
         (or (in-list a x)
             (in-list a y))))

(defthm in-list-reverse
  (equal (in-list a (reverse x))
         (in-list a x)))

(defthm in-list-on-set
  (implies (setp X)
           (equal (in-list a X)
                  (in a X)))
  :hints(("Goal" :in-theory (enable sfix head tail empty setp))))

; We now introduce a naive function to split a list into two.

(defun split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((endp (cdr x)) (mv (list (car x)) nil))
        (t (mv-let (part1 part2)
                   (split-list (cddr x))
                   (mv (cons (car x) part1)
                       (cons (cadr x) part2))))))

(local (defthm split-list-membership
         (equal (in-list a x)
                (or (in-list a (mv-nth 0 (split-list x)))
                    (in-list a (mv-nth 1 (split-list x)))))))

(local (defthm split-list-part1-truelist
         (true-listp (mv-nth 0 (split-list x)))
         :rule-classes :type-prescription))

(local (defthm split-list-part2-truelist
         (true-listp (mv-nth 1 (split-list x)))
         :rule-classes :type-prescription))

(local (defthm split-list-length-part1
         (implies (consp (cdr x))
                  (equal (len (mv-nth 0 (split-list x)))
                         (+ 1 (len (mv-nth 0 (split-list (cddr x)))))))))

(local (defthm split-list-length-part2
         (implies (consp (cdr x))
                  (equal (len (mv-nth 1 (split-list x)))
                         (+ 1 (len (mv-nth 1 (split-list (cddr x)))))))))

(local (defthm split-list-length-less-part1
         (implies (consp (cdr x))
                  (< (len (mv-nth 0 (split-list x)))
                     (len x)))))

(local (defthm split-list-length-less-part2
         (implies (consp (cdr x))
                  (< (len (mv-nth 1 (split-list x)))
                     (len x)))))

(local (in-theory (disable split-list-length-part1
                           split-list-length-part2)))

(defun mergesort-exec (x)
  (declare (xargs 
    :guard (true-listp x)
    :measure (len x)
    :hints(("Goal" :use ((:instance split-list-length-less-part1)
                         (:instance split-list-length-less-part2))))
    :verify-guards nil))
  (cond ((endp x) nil)
        ((endp (cdr x)) (insert (car x) nil))
        (t (mv-let (part1 part2)
                   (split-list x)
                   (union (mergesort-exec part1) (mergesort-exec part2))))))

(local (defthm mergesort-exec-set
         (setp (mergesort-exec x))))

(local (in-theory (disable split-list-membership)))

(local (defthm mergesort-membership-2
         (implies (in-list a x)
                  (in a (mergesort-exec x)))
         :hints(("Subgoal *1/3" :use (:instance split-list-membership)))))

(local (defthm mergesort-membership-1
         (implies (in a (mergesort-exec x))
                  (in-list a x))
         :hints(("Subgoal *1/6" :use (:instance split-list-membership))
                ("Subgoal *1/5" :use (:instance split-list-membership))
                ("Subgoal *1/4" :use (:instance split-list-membership)))))

(local (defthm mergesort-membership
         (iff (in a (mergesort-exec x))
              (in-list a x))))

(defun mergesort (x)
  (declare (xargs :guard (true-listp x)
                  :verify-guards nil))
  (mbe :logic (if (endp x)
                  nil
                (insert (car x)
                        (mergesort (cdr x))))
       :exec (mergesort-exec x)))
           
(defthm mergesort-set
  (setp (mergesort x)))

(defthm in-mergesort
  (equal (in a (mergesort x))
         (in-list a x)))

(defthm mergesort-set-identity
  (implies (setp X)
           (equal (mergesort X) X))
  :hints(("Goal" :in-theory (enable setp sfix head tail empty))))
