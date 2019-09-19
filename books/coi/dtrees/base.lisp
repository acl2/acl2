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

;;
;; Dependency Trees for Data Dependency Analysis
;; Jared Davis
;;
;;
;; INTRODUCTION
;;
;; We introduce the basic dtree functions, such as the dtree recognizer, fixing
;; functions, count, membership, get, and "domain" computation.

(in-package "DTREE")
;; DAG -- I do this globally here
(include-book "../util/iff")
(include-book "../maps/maps")
(include-book "../lists/basic")
(include-book "../osets/multicons")

(local (in-theory (enable set::weak-insert-induction-helper-1)))
(local (in-theory (enable set::weak-insert-induction-helper-2)))
(local (in-theory (enable set::weak-insert-induction-helper-3)))

;; [Jared] dumb accumulated persistence hacking
(local (in-theory (disable ;;SET::MAP-SUBSET-HELPER-2
                           SET::IN-TAIL-OR-HEAD
                           SET::ALL-IN-2-NOT<TRUE-LISTP>
                           SET::ALL-IN-2<TRUE-LISTP>
                           SET::ALL<NOT-TRUE-LISTP>
                           SET::ALL<TRUE-LISTP>
                           SET::ALL-TAIL-NOT<TRUE-LISTP>
                           SET::ALL-TAIL<TRUE-LISTP>
                           SET::ALL-SUBSET-NOT<TRUE-LISTP>
                           SET::ALL-SUBSET<TRUE-LISTP>)))

;; We implement dtrees as triples of the form (:dtree deps children) where
;; :dtree is just the literal keyword symbol :dtree, deps is the set of local
;; dependences, and children is a map whose range consists entirely of other
;; dtrees.  This idea is mutually recursive.
;;
;; Note an important choice: (dtreemapp x) does NOT guarantee (map? x).
;; Instead, in this case dtreemapp treats x just like any other map function,
;; so that any "bad" maps are just interpreted as the empty map.  As a
;; consequence, bad maps satisfy (dtreemapp x), but we also get the great fact
;; that mapequiv is a congruence for dtreemapp.

(mutual-recursion
 (defund dtreep (x)
   (declare (xargs :guard t))
   (and (true-listp x)
        (equal (len x) 3)
        (let ((tag (first x))
              (deps (second x))
              (children (third x)))
          (and (equal tag :dtree)
               (set::listsetp deps)
               (mapp children)
               (dtreemapp children)))))
 (defund dtreemapp (x)
   (declare (xargs :guard (mapp x)))
   (or (map::empty-exec x)
       (and (dtreep (map::get (map::head x) x))
            (dtreemapp (map::tail x))))))



;; The dtreemapp function is just a concrete instance of a typed map
;; recognizer, which we have developed a simple theory about in the book on
;; typed-maps.  We load up this book and functionally instantiate the main
;; theorems for dtreemapp.

(encapsulate
 ()

 (local (include-book "../maps/typed-maps"))

 (defthm dtreep-when-in-dtreemapp
   (implies (and (dtreemapp map)
                 (map::in a map))
            (dtreep (map::get a map)))
   :hints(("Goal"
           :in-theory (enable dtreemapp)
           :use (:functional-instance
                 predicate-when-in-typed-mapp
                 (map::predicate
                  (lambda (key val) (dtreep val)))
                 (typed-mapp
                  (lambda (map) (dtreemapp map)))))))

 (defthm dtreemapp-when-has-non-dtree
   (implies (and (map::in a map)
                 (not (dtreep (map::get a map))))
            (equal (dtreemapp map)
                   nil)))

 (defthm dtreemapp-of-set
   (implies (dtreemapp map)
            (equal (dtreemapp (map::set key val map))
                   (dtreep val)))
   :hints(("Goal"
           :in-theory (enable dtreemapp)
           :use (:instance (:functional-instance
                            typed-mapp-of-set
                            (map::predicate
                             (lambda (key val) (dtreep val)))
                            (typed-mapp
                             (lambda (map) (dtreemapp map))))
                           (map::key key)
                           (map::val val)))))

 (defthm dtreemapp-of-erase
   (implies (dtreemapp map)
            (dtreemapp (map::erase key map)))
   :hints(("Goal"
           :in-theory (enable dtreemapp)
           :use (:instance (:functional-instance
                            typed-mapp-of-erase
                            (map::predicate
                             (lambda (key val) (dtreep val)))
                            (typed-mapp
                             (lambda (map) (dtreemapp map))))
                           (map::key key)))))

 (defcong map::equiv equal (dtreemapp map) 1
   :package :legacy
   :hints(("Goal"
           :in-theory (enable dtreemapp)
           :use (:functional-instance
                 equiv-implies-equal-typed-mapp-1
                 (map::predicate
                  (lambda (key val) (dtreep val)))
                 (typed-mapp
                  (lambda (map) (dtreemapp map)))))))


 (encapsulate
  (((dtreemapp-hyps) => *)
   ((dtreemapp-map) => *))
  (local (defun dtreemapp-hyps () nil))
  (local (defun dtreemapp-map () nil))
  (defthm dtreemapp-constraint
    (implies (and (dtreemapp-hyps)
                  (map::in dtreemapp-key (dtreemapp-map)))
             (dtreep (map::get dtreemapp-key (dtreemapp-map))))))

 (defthm dtreemapp-by-membership-driver
   (implies (dtreemapp-hyps)
            (dtreemapp (dtreemapp-map)))
   :hints(("Goal"
           :use (:functional-instance
                 typed-mapp-by-membership
                 (map::predicate (lambda (key val) (dtreep val)))
                 (typed-mapp (lambda (map) (dtreemapp map)))
                 (typed-mapp-hyps (lambda () (dtreemapp-hyps)))
                 (typed-mapp-map (lambda () (dtreemapp-map)))))))

 (defadvice dtreemapp-by-membership
   (implies (dtreemapp-hyps)
            (dtreemapp (dtreemapp-map)))
   :rule-classes (:pick-a-point :driver dtreemapp-by-membership-driver))

 )




;; As usual, we will enforce a "non-dtree" convention.  When our functions
;; expect to operate on a dtree, they will typically call dtreefix in order to
;; coerce their argument to a dtree.  Bad dtrees will be converted to the
;; default dtree, which simply has no dependences and no children.

(defconst *default*
  (list :dtree
        (set::emptyset) ; no dependences
        (map::emptymap))) ; no children

(defund dtreefix (dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (mbt (dtreep dtree))
      dtree
    *default*))

(defthm dtreep-of-dtreefix
  (dtreep (dtreefix dtree))
  :hints(("Goal" :in-theory (enable dtreefix))))

(defthm dtreefix-when-dtreep
  (implies (dtreep dtree)
           (equal (dtreefix dtree)
                  dtree))
  :hints(("Goal" :in-theory (enable dtreefix))))




;; We also provide a fixing function for dtree maps.  To fix a dtree map, we
;; reconstruct the map by fixing each dtree within it.
;;
;; Originally I used a straightforward "if it's a dtree map, return it,
;; otherwise return nil" approach.  This approach was nice in that I didn't
;; need count below, and I could instead just use ACL2 counts for some
;; recursive functions.  It also had a stronger version of the identity
;; theorem, i.e., I could use "equal" instead of "map::equiv"
;;
;; However, this approach did not provide some important theorems, including
;; domain-of-dtreemapfix and the fact that dtreemapfix is the identity under
;; our equivalence relation for dtree maps.

(defund dtreemapfix (map)
  (declare (xargs :guard (and (mapp map)
                              (dtreemapp map))
                  :verify-guards nil))
  (if (map::empty-exec map)
      (map::emptymap)
    (map::set (map::head map)
              (dtreefix (map::get (map::head map) map))
              (dtreemapfix (map::tail map)))))

(defthm mapp-of-dtreemapfix
  (mapp (dtreemapfix map))
  :hints(("Goal" :in-theory (enable dtreemapfix))))

(verify-guards dtreemapfix)

(defthm dtreemapp-of-dtreemapfix
  (dtreemapp (dtreemapfix map))
  :hints(("Goal" :in-theory (enable dtreemapfix))))

(defthm dtreemapfix-when-dtreemapp
  (implies (dtreemapp map)
           (map::equiv (dtreemapfix map)
                       map))
  :hints(("Goal" :in-theory (enable dtreemapfix))))

(defthm get-of-dtreemapfix
  (implies (map::in a map)
           (equal (map::get a (dtreemapfix map))
                  (dtreefix (map::get a map))))
  :hints(("Goal" :in-theory (enable dtreemapfix))))

(encapsulate
 ()

 (local (defthm lemma
          (equal (map::in a (dtreemapfix map))
                 (map::in a map))
          :hints(("Goal" :in-theory (enable dtreemapfix)))))

 (defthm domain-of-dtreemapfix
   (equal (map::domain (dtreemapfix map))
          (map::domain map)))

)

(encapsulate
 ()

 (local (defthm lemma
          (implies (and (submap sub super)
                        (map::in key sub))
                   (equal (map::get key (dtreemapfix sub))
                          (map::get key (dtreemapfix super))))
          :hints(("Goal"
                  :in-theory (disable equal-of-gets-when-submap)
                  :use (:instance equal-of-gets-when-submap
                                  (map::sub sub)
                                  (map::super super)
                                  (map::key key)
                                  )))))

 (defthm submap-of-dtreemapfix-with-dtreemapfix-when-submap
   (implies (submap sub super)
            (submap (dtreemapfix sub)
                    (dtreemapfix super))))
)

(defcong map::equiv map::equiv (dtreemapfix map) 1
  :package :legacy
  :hints(("Goal" :in-theory (enable map::equiv))))

(defthm in-of-head-of-dtreemapfix-when-nonempty
  (implies (not (map::empty map))
           (map::in (map::head (dtreemapfix map)) map))
  :hints(("Goal"
          :in-theory (disable map::in-head)
          :use (:instance map::in-head
                          (map (dtreemapfix map))))))





;; Each dtree has a set of its own dependences, which we call its "local"
;; dependences.  This set can be accessed through (localdeps dtree).  We do
;; not expect that end users should ever use this function directly, instead
;; they should be primarily interested in (deps dtree).

(defund localdeps (dtree)
  (declare (xargs :guard (dtreep dtree)
                  :guard-hints (("Goal" :in-theory (enable dtreep)))))
  (mbe :logic (second (dtreefix dtree))
       :exec (second dtree)))

(defthm listsetp-of-localdeps
  (set::listsetp (localdeps dtree))
  :hints(("Goal" :in-theory (enable localdeps dtreefix dtreep))))

(defthm localdeps-of-dtreefix
  (equal (localdeps (dtreefix dtree))
         (localdeps dtree))
  :hints(("Goal" :in-theory (enable localdeps))))





;; Each dtree also has a map of named children, which we access with (children
;; dtree).  We do not expect these functions to be of much use to end users,
;; who should generally prefer to use functions like "deps" and "get"
;; instead.

(defund children (dtree)
  (declare (xargs :guard (dtreep dtree)
                  :guard-hints (("Goal" :in-theory (enable dtreep)))))
  (mbe :logic (third (dtreefix dtree))
       :exec (third dtree)))

(defthm children-of-dtreefix
  (equal (children (dtreefix dtree))
         (children dtree))
  :hints(("Goal" :in-theory (enable children))))

(defthm mapp-of-children
  (implies (dtreep dtree)
           (mapp (children dtree)))
  :hints(("Goal" :in-theory (enable children dtreep))))

(defthm dtreemapp-of-children
  (dtreemapp (children dtree))
  :hints(("Goal" :in-theory (enable children dtreefix dtreep))))





;; In order to write recursive functions over dtrees, we need to define a
;; measure which satisfies several properties, e.g., count of children should
;; be less than count of parent, count of any particular child in a dtree map
;; should be less than the count of the map, and so forth.  I had tried to
;; develop a non mutually-recursive implementation here, but ultimately I ended
;; up with this instead.

(mutual-recursion

 (defund count (dtree)
   (declare (xargs :hints (("Goal" :in-theory (enable dtreep dtreemapp)))))
   (if (dtreep dtree)
       (1+ (countmap (third dtree)))
     2))

 (defund countmap (map)
   (if (map::empty-exec map)
       1
     (+ (count (map::get (map::head map) map))
        (countmap (map::tail map)))))
 )

(defthm count-of-dtreefix
  (equal (count (dtreefix dtree))
         (count dtree))
  :hints(("Goal" :in-theory (enable count dtreefix))))

(defthm count-of-children-linear
  (< (countmap (children dtree))
     (count dtree))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable count children dtreefix))))


(encapsulate
 ()

 (local (defun flat-countmap (domain map)
          (if (set::empty domain)
              1
            (+ (count (map::get (set::head domain) map))
               (flat-countmap (set::tail domain) map)))))

 (local (defthm lemma
          (implies (not (set::in a domain))
                   (equal (flat-countmap (set::insert a domain) x)
                          (+ (count (map::get a x))
                             (flat-countmap domain x))))
          :hints(("Goal" :induct (set::insert a domain))
                 ("Subgoal *1/1"
                  :expand (flat-countmap (set::insert a domain) x)))))

 (local (defthm lemma2
          (implies (not (set::in a domain))
                   (equal (flat-countmap domain (map::erase a x))
                          (flat-countmap domain x)))))

 (local (defthm lemma3
          (implies (set::in a domain)
                   (equal (flat-countmap domain x)
                          (+ (count (map::get a x))
                             (flat-countmap (set::delete a domain) x))))
          :rule-classes :linear))

 (local (defun count-induction (x)
          (if (map::empty-exec x)
              nil
            (list (count-induction (map::get (map::head x) x))
                  (count-induction (map::tail x))))))

 (local (defthm flatten-map-count
          (equal (countmap x)
                 (flat-countmap (map::domain x) x))
          :hints(("Goal"
                  :in-theory (enable countmap)
                  :induct (count-induction x)))))

 (local (defcong map::equiv equal (flat-countmap domain map) 2))

 (local (defthm flat-countmap-fix-map
          (implies (set::subset domain (map::domain x))
                   (equal (flat-countmap domain (dtreemapfix x))
                          (flat-countmap domain x)))))

 (local (defthm flat-countmap-child
          (implies (set::in a domain)
                   (< (count (map::get a map))
                      (flat-countmap domain map)))
          :rule-classes :linear
          :hints(("Goal" :induct (flat-countmap domain map)))))

 (local (defthm flat-countmap-delete
          (implies (and (set::subset domain (map::domain x))
                        (set::in a domain))
                   (< (flat-countmap (set::delete a domain) x)
                      (flat-countmap domain x)))
          :rule-classes :linear))

 (defthm countmap-of-dtreemapfix
   (equal (countmap (dtreemapfix map))
          (countmap map)))

 (defthm count-of-get-strong-linear
   (implies (map::in key map)
            (< (count (map::get key map))
               (countmap map)))
   :rule-classes :linear)

 (defthm count-of-erase-strong-linear
   (implies (map::in key map)
            (< (countmap (map::erase key map))
               (countmap map)))
   :rule-classes :linear)

 )







;; We can naturally extend the idea of retrieving a child to the idea of
;; retrieving a sequence of named children, i.e., a path.
;;
;; Once upon a time, I thought this function should be mutually recursive so
;; that it would "correspond nicely" to the other functions (e.g., flag-deps
;; and flag-dtreep).  In retrospect, I think this is a misguided ambition.  In
;; particular, I could not come up with a mutually recursive definition that
;; satisfied get-of-get below.
;;
;; I kind of think, now, that get is a proper operation for dtrees alone to
;; have, not dtree maps.  It doesn't require us to look at the members of the
;; map in sequence, so there is really no reason to have a mutually recursive
;; component to it.
;;
;; A decision I struggled with was whether or not to have get return
;; *default* if path was not a true list.  A detailed discussion of this
;; decision can be found in the comments by the "in" function.

(defund get (path dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (consp path)
      (if (map::in (car path) (children dtree))
          (get (cdr path)
               (map::get (car path) (children dtree)))
        *default*)
    (dtreefix dtree)))

(defthm dtreep-of-get
  (dtreep (get path dtree))
  :hints(("Goal" :in-theory (enable get))))

(defthm get-of-dtreefix
  (equal (get path (dtreefix dtree))
         (get path dtree))
  :hints(("Goal" :in-theory (enable get))))

(defthm get-when-non-consp
  (implies (not (consp path))
           (equal (get path dtree)
                  (dtreefix dtree)))
  :hints(("Goal" :in-theory (enable get))))

(encapsulate
 ()

 ;; Can't quite use list::len-len-induction, because we need to take the
 ;; children of the dtree at each step as well.
 (local (defun my-induct (path1 path2 dtree)
          (if (and (consp path1)
                   (consp path2))
              (my-induct (cdr path1) (cdr path2)
                         (map::get (car path1) (children dtree)))
            (list path1 path2 dtree))))

 (defcong list::equiv equal (get path dtree) 1
   :hints(("Goal"
           :in-theory (enable get)
           :induct (my-induct path path-equiv dtree))))

)

(defthm get-of-get
  (equal (get x (get y dtree))
         (get (append y x) dtree))
  :hints(("Goal" :in-theory (enable get))))

;; Get is useful, but it doesn't give you "the whole story".  That is,
;; suppose you look up a path in the dtree and get the default dtree as a
;; result.  Does that mean that the dtree doesn't exist, or that you looked up
;; a dtree that happened to be the default one?
;;
;; In a sense, the question is very much like the distinction between the
;; domain of a map versus the set of all its "non default-valued" members.  We
;; are hopeful that this is a useful distinction in dtrees as well, so we
;; provide an additional function, "in", which can test if a path exists in a
;; dtree or not.
;;
;; There is a very natural correspondence between the recursive structure of
;; get and the recursive structure of in.  This closeness makes them easy to
;; reason about together, which is really good, as the comments below in domain
;; will elaborate on.
;;
;; How should "get" and "in" treat paths that are not true lists?
;; Originally I thought that it would be best if "in" only returned true on
;; true lists.  This had the appealing property that (in a dtree) was exactly
;; equal to (set::in a (domain dtree)).  Following this line of thinking, I
;; tried changing "get" so that it would only return *default* if you gave
;; it a non true-list, so that, e.g., (not (in path dtree)) would imply (equal
;; (get path dtree) *default*).
;;
;; I found that I could not reason about get well using this approach.  In
;; particular, the theorem get-get above is very important, but only a
;; weaker version could be proven with an added hypothesis that y was a true
;; list.  This screws up many theorems down the line, including the important
;; subtree-get-get theorem.  So, I decided that get should go ahead
;; and ignore the final cdr.
;;
;; That got me thinking about how "in" would work better if it were also
;; unconcerned with the final cdr.  The one downside of the approach is that
;; the close correspondence between set membership in the domain and dtree
;; membership is somewhat worse.  That is, instead of
;;
;;    (set::in a (domain dtree)) = (in a dtree)
;;
;; We now have:
;;
;;    (set::in a (domain dtree)) = (in a dtree) and (true-listp a)
;;
;; But this seems to still be workable.  And now, we have nicer theorems about
;; the relationship between "in" and "get", e.g., before we only could show:
;;
;;   (implies (not (in (list::fix path dtree)))
;;            (equal (get path dtree) *default*))
;;
;; But now we can show:
;;
;;   (implies (not (in path dtree))
;;            (equal (get path dtree) *default*))
;;
;; And we can also set up a congruence rule for the path argument of in, just
;; as we did for the path argument of get.

(defund in (path dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (consp path)
      (and (map::in (car path) (children dtree))
           (in (cdr path)
               (map::get (car path) (children dtree))))
    t))

(defthm in-of-dtreefix
  (equal (in path (dtreefix dtree))
         (in path dtree))
  :hints(("Goal" :in-theory (enable in))))

(defthm in-when-non-consp
  (implies (not (consp path))
           (in path dtree))
  :hints(("Goal" :in-theory (enable in))))

(encapsulate
 ()

 ;; Can't quite use list::len-len-induction, because we need to take the
 ;; children of the dtree at each step as well.
 (local (defun my-induct (path1 path2 dtree)
          (if (and (consp path1)
                   (consp path2))
              (my-induct (cdr path1) (cdr path2)
                         (map::get (car path1) (children dtree)))
            (list path1 path2 dtree))))

 (defcong list::equiv equal (in path dtree) 1
   :hints(("Goal"
           :in-theory (enable in)
           :induct (my-induct path path-equiv dtree))))

 )

(defthm in-of-get
  (equal (in x (get y dtree))
         (if (consp x)
             (in (append y x) dtree)
           t))
  :hints(("Goal" :in-theory (enable in get))))

(defthm get-when-not-in
  (implies (not (in path dtree))
           (equal (get path dtree)
                  *default*))
  :hints(("Goal" :in-theory (enable in get))))

(defthmd in-children-is-in-of-singleton-path
  (equal (map::in key (children dtree))
         (in (list key) dtree))
  :hints(("Goal" :in-theory (enable in))))

(defthmd get-of-children-is-get-of-singleton-path
  (implies (map::in key (children dtree))
           (equal (map::get key (children dtree))
                  (get (list key) dtree)))
  :hints(("Goal" :in-theory (enable get))))

;; Given that we have the notion of membership in a dtree, it is natural to
;; want to talk about a dtree's domain.  Below we introduce exactly this idea.
;;
;; I have wrestled with the definition of domain for a very long time.
;; Originally, I didn't even want to define "in" above, because I thought I
;; could simply reason about (set::in a (domain dtree)) instead.  I took this
;; approach and got relatively far, even defining subtrees and the dtree
;; equivalence relation without using "in" at all.  But domain and aux-domain
;; seem very difficult to reason about directly, most especially with respect
;; to the get function because of the fundamental differences in their
;; recursive structures.  And, I have found that the "in" function above is a
;; much better solution.
;;
;; The domain function is really strange.  Every leaf has a domain which is
;; simply { nil }, i.e., the set containing the empty path.  Interior nodes are
;; different, and must be built from all of their children.  In other words, we
;; need to recur over the children of the dtree in turn.  Why is that
;; significant?  Well, it means that there is something that is "mutual
;; recursive" in nature about this function -- it's not like get or in,
;; where we can just dive down through particular children -- we need to
;; consider them all.
;;
;; Then, suppose we have some particular child named C, and we have computed
;; its domain.  Suppose C's domain consists of { p1, p2, ..., pN }.  Well then,
;; our domain must include "C" plus p1, "C" plus p2, ..., "C" plus pN.  We
;; define the set::multicons operation (see "multicons.lisp" in directory
;; ../osets) for this purpose.
;;
;; You can imagine that we need to do this for each of our children and union
;; together all of the resulting paths.  As a final observation, we need to add
;; the path "nil", i.e., the path that doesn't lead us to any of our children.
;; We add this path in our base case.
;;
;; I once wrote domain using mutual-recursion directly, and then went ahead and
;; wrote its flag version.  The thing that jumped out at me about the
;; definition was that the :dtree case did hardly any work.  In fact, all it
;; did was invoke the map case on (children dtree).  Well then, we could
;; eliminate the mutual recursion by simply replacing calls of the dtree case
;; with calls of the map case on (children x).
;;
;; And ultimately that's what I did, but it's very weird because now, not only
;; do we have a very different recursive structure than get and in, but
;; furthermore we don't really take dtrees as our argument.  Indeed, the main
;; domain computation (aux-domain) operates over dtree maps instead.
;;
;; In any event, the definitions and such are quite bizarre.  But fortunately,
;; because of the double containment and subset by membership strategies in the
;; set theory library, all we really need to do is get to the point of showing
;; that membership in domain is the same as our "in" function with respect to
;; the original dtree.  Even proving this "simple" fact is very difficult, but
;; we are able to accomplish it.  My hope is that we will be saved from ever
;; needing to do this kind of thing again.

(defun aux-domain (map)
  (declare (xargs :guard (and (mapp map)
                              (dtreemapp map))
                  :measure (countmap map)
                  :verify-guards nil))
  (let ((map (dtreemapfix map)))
    (if (map::empty-exec map)
        (list nil)
      (set::union (set::multicons
                    (map::head map)
                    (aux-domain (children (map::get (map::head map) map))))
                   (aux-domain (map::tail map))))))

(defthm listsetp-of-aux-domain
  (set::listsetp (aux-domain map))
  :hints(("Goal" :in-theory (enable set::listsetp))))

(verify-guards aux-domain)

(encapsulate
 ()

 (local (defun path/domain-induct (path map)
          (declare (xargs :measure (countmap map)))
          (let ((map (dtreemapfix map)))
            (if (map::empty map)
                (list path map)
              (list (path/domain-induct
                     (cdr path)
                     (children (map::get (map::head map) map)))
                    (path/domain-induct path (map::tail map)))))))

 (local (defthm aux-domain-true-lists
          (implies (set::in path (aux-domain map))
                   (true-listp path))
          :hints(("Goal" :induct (path/domain-induct path map)))
          :rule-classes :forward-chaining))

 (defthm in-of-aux-domain-when-not-consp
   (implies (not (consp path))
            (equal (set::in path (aux-domain map))
                   (not path))))

 (local (defthm car-in-aux-domain
          (implies (and (consp path)
                        (dtreemapp map)
                        (set::in path (aux-domain map)))
                   (map::in (car path) (dtreemapfix map)))))

 (local (defthm car-in-aux-domain-2
          (implies (and (consp path)
                        (dtreemapp map)
                        (not (map::in (car path) map)))
                   (not (set::in path (aux-domain map))))))

 (local (defthm cdr-in-aux-domain-rest
          (implies (and (consp path)
                        (dtreemapp map)
                        (set::in path (aux-domain map)))
                   (set::in (cdr path)
                             (aux-domain (children (map::get (car path) map)))))
          :hints(("Goal" :induct (path/domain-induct path map))
                 ("Subgoal *1/2" :expand (aux-domain map)))))

 (local
  (defthm in-aux-domain-bothways
    (implies (and (consp path)
                  (dtreemapp map))
             (equal
              (set::in path (aux-domain map))
              (and (map::in (car path) map)
                   (set::in (cdr path)
                             (aux-domain (children
                                          (map::get (car path) map)))))))))

 (defthm in-of-aux-domain-when-consp
   (implies (consp path)
            (equal
             (set::in path (aux-domain map))
             (and (map::in (car path) (dtreemapfix map))
                  (set::in (cdr path)
                            (aux-domain (children
                                         (map::get (car path)
                                                   (dtreemapfix map))))))))
   :hints(("Goal"
           :use (:instance in-aux-domain-bothways
                           (map (dtreemapfix map))))))

 )


(encapsulate
 ()

 (local (defthm lemma
          (implies (set::in a (aux-domain (dtreemapfix map)))
                   (set::in a (aux-domain map)))))

 (local (defthm lemma2-for-aux-domain-of-dtreemapfix
          (implies (set::in a (aux-domain map))
                   (set::in a (aux-domain (dtreemapfix map))))))

 (defthm aux-domain-of-dtreemapfix
   (equal (aux-domain (dtreemapfix map))
          (aux-domain map)))
)




;; The domain function is now easy to define -- we just call aux-domain on our
;; dtree's children.  We can then show that the domain is a set, and give a
;; nice rewrite to explain when something is a member of the domain.  Our hope
;; is that membership-based reasoning can then be used to prove everything
;; else desired about domains.

(defund domain (dtree)
  (declare (xargs :guard (dtreep dtree)))
  (aux-domain (children dtree)))

(defthm domain-of-dtreefix
  (equal (domain (dtreefix dtree))
         (domain dtree))
  :hints(("Goal" :in-theory (enable domain))))

(defthm listsetp-of-domain
  (set::listsetp (domain dtree))
  :hints(("Goal" :in-theory (enable domain))))

(defthm in-of-domain
  (equal (set::in path (domain dtree))
         (and (in path dtree)
              (true-listp path)))
  :hints(("Goal" :in-theory (enable in domain))))

(defthm in-nil-domain
  (set::in nil (domain dtree))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((domain dtree)))))

(encapsulate
 ()

 ;; I thought this would be a good general purpose lemma, but it seems to screw
 ;; things up, so I'm just making it local for this proof.
 (local (defthm in-forward-to-nonempty
          (implies (set::in a x)
                   (not (set::empty x)))
          :rule-classes :forward-chaining))

 (defthm empty-of-domain
   (equal (set::empty (domain dtree))
          nil))
)
