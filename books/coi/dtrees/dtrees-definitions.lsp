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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "is anyone using this?  If so please remove this message.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; dtrees-definitions.lisp
;; John D. Powell
;(in-package "DTREES")

;;
;; This file isolates dtrees definitions and types. The file currently contains
;; the following ACL2 constructs as they occur in the dtrees book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

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

;; We introduce four functions: (haschild name dtree) returns true iff a dtree
;; has an immediate child with the given name.  Getchild returns such a child,
;; or dtree::*default* if no such child exists.  Setchild adds or updates a
;; child in the dtree, and erasechild erases a child.  These functions are
;; basically alternatives to in, get, set, and erase, but which are only useful
;; for manipulating single-level dtrees.
;;
;; These functions have really been added only as an afterthought, and we hope
;; they might be useful abstractions.  But, we realize that the reasoning
;; strategy we provide here is probably insufficient.  So, at the end of this
;; file, we provide four theorems, which are "abbreviation" rules (i.e., simple
;; rewrite rules) that should automatically eliminate all occurrences of these
;; functions from your proofs.
;;
;;  - haschild-is-in-of-singleton-list
;;  - setchild-is-set-of-singleton-list
;;  - getchild-is-get-of-singleton-list
;;  - erasechild-is-erase-of-singleton-list
;;
;; These theorems can be disabled if they are problematic, and you can then
;; fall back on the reasoning in this file.  However, generally we think it is
;; best to work with "the real thing" rather than these child functions.

(defund haschild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  (map::in name (children dtree)))

(defund getchild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  ;; (haschild name dtree))))
  (if (haschild name dtree)
      (map::get name (children dtree))
    dtree::*default*))

(defund setchild (name value dtree)
  (declare (xargs :guard (and (dtreep dtree)
                              (dtreep value))))
  (rawdtree (localdeps dtree)
            (map::set name (dtreefix value) (children dtree))))

(defund erasechild (name dtree)
  (declare (xargs :guard (dtreep dtree)))
  (rawdtree (localdeps dtree)
            (map::erase name (children dtree))))


(defthm dtreep-of-getchild
  (dtreep (getchild name dtree))
  :hints(("goal" :in-theory (enable getchild haschild))))

(defthm dtreep-of-setchild
  (dtreep (setchild name value dtree))
  :hints(("goal" :in-theory (enable setchild))))

(defthm dtreep-of-erasechild
  (dtreep (setchild name value dtree))
  :hints(("goal" :in-theory (enable setchild))))

(defthm haschild-of-setchild
  (equal (haschild a (setchild b value dtree))
         (if (equal a b)
             t
           (haschild a dtree)))
  :hints(("Goal" :in-theory (enable haschild setchild))))

(defthm haschild-of-erasechild
  (equal (haschild a (erasechild b dtree))
         (if (equal a b)
             nil
           (haschild a dtree)))
  :hints(("Goal" :in-theory (enable haschild erasechild))))

(defthm getchild-when-not-haschild
  (implies (not (haschild a dtree))
           (equal (getchild a dtree)
                  dtree::*default*))
  :hints(("Goal" :in-theory (enable haschild getchild))))

(defthm getchild-of-setchild
  (equal (getchild a (setchild b value dtree))
         (if (equal a b)
             (dtreefix value)
           (getchild a dtree)))
  :hints(("Goal" :in-theory (enable getchild setchild haschild))
         ("Subgoal 1" :cases ((haschild a dtree)))))

(defthm getchild-of-erasechild
  (equal (getchild a (erasechild b dtree))
         (if (equal a b)
             dtree::*default*
           (getchild a dtree)))
  :hints(("Goal" :in-theory (enable getchild erasechild haschild))))

(defthm erasechild-of-erasechild-different
  (implies (case-split (not (equal a b)))
           (equiv (erasechild a (erasechild b dtree))
                  (erasechild b (erasechild a dtree))))
  :hints(("Goal" :in-theory (enable erasechild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm erasechild-of-erasechild-same
  (equiv (erasechild a (erasechild a dtree))
         (erasechild a dtree))
  :hints(("Goal" :in-theory (enable erasechild))))



(defthm setchild-of-setchild-different
  (implies (case-split (not (equal a b)))
           (equiv (setchild a v1 (setchild b v2 dtree))
                  (setchild b v2 (setchild a v1 dtree))))
  :hints(("Goal" :in-theory (enable setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm setchild-of-setchild-same
  (equiv (setchild a v1 (setchild a v2 dtree))
         (setchild a v1 dtree))
  :hints(("Goal" :in-theory (enable setchild))))



(defthm erasechild-of-setchild-different
  (implies (case-split (not (equal a b)))
           (equiv (erasechild a (setchild b val dtree))
                  (setchild b val (erasechild a dtree))))
  :hints(("Goal" :in-theory (enable erasechild setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm erasechild-of-setchild-same
  (equiv (erasechild a (setchild a val dtree))
         (erasechild a dtree))
  :hints(("Goal" :in-theory (enable erasechild setchild))))



(defthm setchild-of-erasechild-different
  (implies (case-split (not (equal a b)))
           (equiv (setchild a val (erasechild b dtree))
                  (erasechild b (setchild a val dtree))))
  :hints(("Goal" :in-theory (enable erasechild setchild)))
  :rule-classes ((:rewrite :loop-stopper ((a b setchild)))))

(defthm setchild-of-erasechild-same
  (equiv (setchild a val (erasechild a dtree))
         (setchild a val dtree))
  :hints(("Goal" :in-theory (enable erasechild setchild))))





(defthm haschild-is-in-of-singleton-list
  (equal (haschild a dtree)
         (in (list a) dtree))
  :hints(("Goal" :in-theory (enable haschild in))))

(defthm setchild-is-set-of-singleton-list
  (equal (setchild a val dtree)
         (set (list a) val dtree))
  :hints(("Goal" :in-theory (enable setchild set))))

(defthm getchild-is-get-of-singleton-list
  (equal (getchild a dtree)
         (get (list a) dtree))
  :hints(("Goal" :in-theory (enable in getchild get))))


;; Not true anymore.

#+joe
(defthm erasechild-is-erase-of-singleton-list
  (equal (erasechild a dtree)
         (erase (list a) dtree))
  :hints(("Goal" :in-theory (enable erasechild erase))))



;; DEFINITION OF DEPS
;;
;; I like to think of the dependency set being defined using quantification as
;; follows:
;;
;;   deps(dtree) = Union_{path \in (domain dtree)}
;;                   (localdeps (lookup path dtree))
;;
;; To me this is an "ideal" definition from a reasoning perspective, and it
;; would be nice to be able to work with this definition when trying to prove
;; theorems.  We can implement this idea by writing two functions: deps1 will
;; compute the above union for any particular set of paths, and deps will just
;; invoke deps1 with the entire domain of the dtree.
;;
;; However, this is not ideal from an execution standpoint, as computing the
;; domain of a dtree could be an expensive operation.  So, for execution
;; efficiency, we will use the function mrdeps below, a mutually-recursive
;; implementation that simply walks down the tree and unions together all of
;; the localdeps it finds on the way.
;;
;; In the end, I will demonstrate that both definitions are equivalent, and
;; thus I will justify an MBE substitution allowing me to use mrdeps under the
;; hood for deps.  Finally, we also provide a function, depsmap, which computes
;; the dependency set for a map of dtrees.

(mutual-recursion

 (defund mrdeps (dtree)
   (declare (xargs :guard (dtreep dtree)
                   :measure (count dtree)
                   :verify-guards nil))
   (set::union (localdeps dtree)
               (mrdepsmap (children dtree))))

 (defund mrdepsmap (map)
   (declare (xargs :guard (and (mapp map)
                               (dtreemapp map))
                   :measure (countmap map)
                   :verify-guards nil))
   (if (map::empty-exec map)
       (set::emptyset)
     (set::union (mrdeps (map::get (map::head map) map))
                 (mrdepsmap (map::tail map)))))
 )

(defund deps1 (locs dtree)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep dtree))
                  :verify-guards nil))
  (if (set::empty locs)
      (set::emptyset)
    (set::union (localdeps (get (set::head locs) dtree))
                (deps1 (set::tail locs) dtree))))

(defund deps (dtree)
  (declare (xargs :guard (dtreep dtree)
                  :verify-guards nil))
  (mbe :logic (deps1 (domain dtree) dtree)
       :exec (mrdeps dtree)))

(defund depsmap (map)
  (declare (xargs :guard (and (mapp map)
                              (dtreemapp map))
                  :verify-guards nil))
  (mbe :logic (if (map::empty-exec map)
                  (set::emptyset)
                (set::union (deps (map::get (map::head map) map))
                            (depsmap (map::tail map))))
       :exec (mrdepsmap map)))






;; THE DEPS FUNCTIONS PRODUCE LIST SETS
;;
;; The equivalence proof which allows us to soundly make this substitution is
;; rather involved.  From a high level, we argue that both deps and mrdeps
;; produce sets, and then proceed to employ a double containment proof.  To
;; begin, lets show that all of these functions produce sets.

(local (defun mrdeps-induct (flag x)
         (declare (xargs :measure (if (equal flag :dtree)
                                      (count x)
                                    (countmap x))))
         (if (equal flag :dtree)
             (mrdeps-induct :map (children x))
           (if (map::empty-exec x)
               nil
             (list (mrdeps-induct :dtree (map::get (map::head x) x))
                   (mrdeps-induct :map (map::tail x)))))))

(defthm listsetp-of-deps1
  (set::listsetp (deps1 locs dtree))
  :hints(("Goal" :in-theory (enable deps1))))

(defthm listsetp-of-deps
  (set::listsetp (deps dtree))
  :hints(("Goal" :in-theory (enable deps))))

(defthm listsetp-of-depsmap
  (set::listsetp (depsmap map))
  :hints(("Goal" :in-theory (enable depsmap))))

;; MEMBERSHIP IN THE DEPS SET
;;
;; An essential and "obvious" property of the deps set is that, if a is an
;; element of the localdeps for any node within the tree, a is also a member
;; of the deps set.  This is relatively straightforward for the simple deps
;; function, but proving this property is more complicated for the mutually
;; recursive deps.
;;
;; Recall that what we want to prove is something like the following:
;;
;;   Given a dtree, dtree.
;;   Given a path p, with (in p dtree).
;;   Given *p = (get p dtree), i.e., the tree p points to.
;;   Given (set::in dep (localdeps *p)).
;;   Show that: (in dep (mrdeps dtree)).
;;
;; But because mrdeps is mutually recursive, we should simultaneously consider
;; the map case.  For that case, lets prove the following:
;;
;;   Given a dtree map, map.
;;   Given a path p, with (in-map p map).
;;   Given *p = (get-map p map), i.e., the tree p points to.
;;   Given (set::in dep (localdeps *p))
;;   Show that: (in dep (mrdepsmap dtree))
;;
;; If you're wondering what in-map and get-map are supposed to be, that
;; makes two of us (haha).  Of course, if p is nonempty, we have some idea of
;; what these ideas ought to be.  In fact, we could say, that whenever p is
;; nonempty, it would be nice to define
;;
;;  (in-map p map) as (in (cdr p) (map::get (car p) map))
;;
;; and
;;
;;  (get-map p map) as (get (cdr p) (map::get (car p) map))
;;
;; But what in the world do we do when p is empty?  My answer is that I am just
;; going to return nil, and our induction scheme should prevent us from ever
;; considering this case.  In other words, we will add an extra given to the
;; map case:
;;
;;   Given that p is a consp.
;;
;; Once we phrase the theorem right, it goes through without much of a problem.
;; The tricky part with mutual recursion seems to be just stating the property
;; that you are trying to prove.

(defthm in-deps1-when-in-localdeps
  (implies (and (set::in path locs)
                (set::in a (localdeps (get path dtree))))
           (set::in a (deps1 locs dtree)))
  :hints(("Goal" :in-theory (enable deps1))))

(defthm in-deps-when-in-localdeps-of-get
  (implies (set::in a (localdeps (get path dtree)))
           (set::in a (deps dtree)))
  :hints(("Goal" :in-theory (enable deps)
          :use (:instance in-deps1-when-in-localdeps
                          (locs (domain dtree))
                          (path (list::fix path))))))

(defthm in-deps-when-in-localdeps
  (implies (set::in a (localdeps dtree))
           (set::in a (deps dtree)))
  :hints(("Goal"
          :in-theory (disable in-deps-when-in-localdeps-of-get)
          :use (:instance in-deps-when-in-localdeps-of-get
                          (path nil)))))

(defthm empty-of-localdeps-of-get-when-deps-empty
  (implies (set::empty (deps dtree))
           (set::empty (localdeps (get path dtree))))
  :hints(("Goal"
          :in-theory (disable in-deps-when-in-localdeps-of-get)
          :use (:instance in-deps-when-in-localdeps-of-get
                          (a (set::head (localdeps (get path dtree))))))))

(defthm empty-of-localdeps-when-deps-empty
  (implies (set::empty (deps dtree))
           (set::empty (localdeps dtree)))
  :hints(("Goal"
          :in-theory (disable empty-of-localdeps-of-get-when-deps-empty)
          :use (:instance empty-of-localdeps-of-get-when-deps-empty
                          (path nil)))))

(defthm empty-of-deps-when-nonempty-of-localdeps-of-get
  (implies (not (set::empty (localdeps (get path dtree))))
           (equal (set::empty (deps dtree))
                  nil)))

(defthm empty-of-deps-when-nonempty-of-localdeps
  (implies (not (set::empty (localdeps dtree)))
           (equal (set::empty (deps dtree))
                  nil)))

(local (in-theory (enable mrdeps)))


;; Normally I really dislike having "open" theorems.  However, the ACL2
;; hieuristics for opening mutually recursive functions really don't seem to
;; work very well, so I am putting these in -- locally, of course.  They save
;; several :expand hints from needing to be attached to subgoals.

(local (defthm open-mrdepsmap-empty
         (implies (map::empty map)
                  (equal (mrdepsmap map)
                         (set::emptyset)))
         :hints(("Goal" :in-theory (enable mrdepsmap)))))

(local (defthm open-mrdepsmap-nonempty
         (implies (not (map::empty map))
                  (equal (mrdepsmap map)
                         (set::union (mrdeps (map::get (map::head map) map))
                                     (mrdepsmap (map::tail map)))))
         :hints(("Goal" :in-theory (enable mrdepsmap)))))


;; FINDING THE CAUSES OF DEPENDENCIES
;;
;; To conduct a membership proof of equivalence between mrdeps and deps, we
;; would like show that any member of (mrdeps dtree) is also in (deps dtree),
;; and vice versa.  Recall that both mrdeps and deps are essentially big unions
;; of many localdeps within a tree.  This makes it difficult to relate, say,
;; (in a (mrdeps dtree)) versus (in a (deps dtree)), because we are never very
;; sure "where" a comes from, i.e., which localdeps was it part of originally?
;;
;; To help answer this question, we write two functions (one for deps, and one
;; for mrdeps) that will go and "find" the proper path for us to look at.  For
;; each of these functions, we want to establish the following properties:
;;
;;  (1) whenever a is in the deps of the dtree, the "find" function returns a
;;  valid path into the dtree when instructed to find a.
;;
;;  (2) whenever a is in the deps of the dtree, then a is also a member of the
;;  localdeps of the dtree obtained by looking up the path returned by "find"
;;  in the dtree.
;;
;; Our find function for deps is relatively straightforward, but the find
;; function for mrdeps is, itself, mutually recursive.

(defund depsource1 (a locs dtree)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep dtree))))
  (if (set::empty locs)
      nil
    (if (set::in a (localdeps (get (set::head locs) dtree)))
        (set::head locs)
      (depsource1 a (set::tail locs) dtree))))

(defund depsource (a dtree)
  (declare (xargs :guard (dtreep dtree)))
  (depsource1 a (domain dtree) dtree))


;; We first establish our desired properties for depsource.  Towards this
;; end, we prove the corresponding properties for deps1, and then the proofs
;; for deps are just simple consequences.

(defthm in-depsource1-when-in-deps1
  (implies (set::in a (deps1 locs dtree))
           (set::in (depsource1 a locs dtree) locs))
  :hints(("Goal" :in-theory (enable deps1 depsource1))))

(local (defthm true-listp-of-depsource1
         (implies (set::all<true-listp> locs)
                  (true-listp (depsource1 a locs dtree)))
         :hints(("Goal" :in-theory (enable depsource1)))))

(defthm in-deps1-is-in-localdeps-of-get-depsource1
  (implies (not (set::in a (localdeps dtree)))
           (equal (set::in a (deps1 locs dtree))
                  (set::in a (localdeps
                               (get (depsource1 a locs dtree) dtree)))))
  :hints(("Goal" :in-theory (enable deps1 depsource1))))


(mutual-recursion

 (defund mrdepsource (a dtree)
   (declare (xargs :guard (dtreep dtree)
                   :measure (count dtree)
                   :verify-guards nil))
   (if (set::in a (localdeps dtree))
       (mv t nil)
     (mrdepsourcemap a (children dtree))))

 (defund mrdepsourcemap (a map)
   (declare (xargs :guard (dtreemapp map)
                   :measure (countmap map)
                   :verify-guards nil))
   (if (map::empty-exec map)
       (mv nil nil)
     (mv-let (foundp path)
             (mrdepsource a (map::get (map::head map) map))
             (if foundp
                 (mv t (cons (map::head map) path))
               (mrdepsourcemap a (map::tail map))))))

 )


;; Again we need some opener theorems in order to get these mutually recursive
;; definitions to expand properly.  We only define these locally because these
;; aren't good general purpose strategies.  Basically, these just save us a lot
;; of :expand hints.

(local (defthm open-mrdepsourcemap-empty
         (implies (map::empty map)
                  (equal (mrdepsourcemap a map)
                         (mv nil nil)))
         :hints(("Goal" :in-theory (enable mrdepsourcemap)))))

(local (defthm open-mrdepsourcemap-nonempty
         (implies (not (map::empty map))
                  (equal (mrdepsourcemap a map)
                         (mv-let (foundp path)
                                 (mrdepsource a (map::get (map::head map) map))
                                 (if foundp
                                     (mv t (cons (map::head map) path))
                                   (mrdepsourcemap a (map::tail map))))))
         :hints(("Goal" :in-theory (enable mrdepsourcemap)))))


;; THE EQUIVALENCE PROOF
;;
;; We are now ready to prove the equivalence of mrdeps and deps.  Since both
;; are sets, all we need to do to prove their equality is prove that membership
;; in one is the same as membership in the other.
;;
;; Given: (set::in a (deps dtree))
;; Show:  (set::in a (mrdeps dtree))
;;
;; Let PATH = (depsource a dtree).  Then, by thm:depsource-get, we see
;; that since (in a (deps dtree)), it must also be the case that (in a
;; (localdeps (get PATH dtree))))) as well.  Also, note that by
;; thm:depsource-in-domain, we see that (in PATH dtree).  These two facts
;; together relieve the hyps of thm:in-mrdeps-by-localdeps, which concludes
;; that (set::in a (mrdeps dtree)), and we are done. QED.
;;
;; The vice-versa case is just the same, but with mrdepsource instead.

(local (defthm in-mrdeps-when-in-deps
         (implies (set::in a (deps dtree))
                  (set::in a (mrdeps dtree)))
         :hints(("Goal" :in-theory (disable in-mrdeps-when-in-localdeps)
                 :use ((:instance in-mrdeps-when-in-localdeps
                                  (dep a)
                                  (path (depsource a dtree))
                                  (x dtree)))))))

(local (defthm in-deps-when-in-mrdeps
         (implies (set::in a (mrdeps dtree))
                  (set::in a (deps dtree)))
         :hints(("Goal" :in-theory (disable in-deps-when-in-localdeps-of-get)
                 :use ((:instance in-deps-when-in-localdeps-of-get
                                  (a a)
                                  (path (mv-nth 1 (mrdepsource a dtree)))
                                  (dtree dtree)))))))

(defthm mrdeps-is-deps
  (equal (mrdeps dtree)
         (deps dtree)))

(defthm mrdepsmap-is-depsmap
  (equal (mrdepsmap map)
         (depsmap map))
  :hints(("Goal" :in-theory (e/d (mrdepsmap depsmap)
                                 (set::double-containment)))))

;; GENERAL PURPOSE REASONING ABOUT DEPS AND DEPSMAP
;;
;; Most of what we have done so far has been bent on proving the above
;; equivalence between the mutually recursive and domain-oriented versions of
;; deps.  We now provide some more general purpose rewrite rules.

(defthm deps1-of-dtreefix
  (equal (deps1 locs (dtreefix dtree))
         (deps1 locs dtree))
  :hints(("Goal" :in-theory (e/d (deps1)
                                 (set::double-containment)))))

(defthm deps-of-dtreefix
  (equal (deps (dtreefix dtree))
         (deps dtree))
  :hints(("Goal" :in-theory (enable deps))))

(defthm depsmap-when-empty
  (implies (map::empty map)
           (equal (depsmap map)
                  (set::emptyset)))
  :hints(("Goal" :in-theory (enable depsmap))))

(defthm in-depsmap-when-in-deps-of-get
  (implies (and (map::in key map)
                (set::in a (deps (map::get key map))))
           (set::in a (depsmap map)))
  :hints(("Goal" :in-theory (enable depsmap))))

(defthm in-deps-of-get-when-not-in-depsmap
  (implies (and (map::in key map)
                (not (set::in a (depsmap map))))
           (equal (set::in a (deps (map::get key map)))
                  nil)))

(defthm in-depsmap-when-submap
  (implies (and (submap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/3"
          :in-theory (e/d (depsmap)
                          (equal-of-gets-when-submap))
          :use (:instance equal-of-gets-when-submap
                          (map::key (map::head sub))
                          (map::sub sub)
                          (map::super super)))
         ("Subgoal *1/2"
          :in-theory (e/d (depsmap)
                          (map::submap-transitive-one
                           map::submap-transitive-two))
          :use (:instance map::submap-transitive-one
                          (x (map::tail sub))
                          (y sub)
                          (z super)))))

(local (defund findtree (a map)
         (if (map::empty map)
             nil
           (if (set::in a (deps (map::get (map::head map) map)))
               (map::head map)
             (findtree a (map::tail map))))))

(local (defthm findtree-works
         (implies (set::in a (depsmap map))
                  (and (map::in (findtree a map) map)
                       (set::in a (deps (map::get (findtree a map) map)))))
         :hints(("Goal" :in-theory (enable depsmap findtree)))))

(defthm in-depsmap-when-in-depsmap-of-erase
  (implies (set::in a (depsmap (map::erase name map)))
           (set::in a (depsmap map)))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/2"
          :use (:instance findtree-works
                          (a a)
                          (map (map::erase name map))))))

(defthm in-deps-when-not-in-erase-from-map
  (implies (and (set::in a (depsmap map))
                (not (set::in a (depsmap (map::erase name map)))))
           (set::in a (deps (map::get name map))))
  :hints(("Goal" :in-theory (enable depsmap))
         ("Subgoal *1/3"
          :use (:instance findtree-works
                          (a a)
                          (map (map::erase name (map::tail map)))))
         ("Subgoal *1/2"
          :use (:instance in-depsmap-when-in-deps-of-get
                          (key (map::head map))
                          (map (map::erase name map))))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                               Simplest case                               |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defun d-empty ()
  '(:dtree nil nil))

(defthm d-simple-1
 (dtree::dtreep (d-empty)))

(defthm d-simple-2
 (equal (d-empty) dtree::*default*))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                Simple examples with non-trivial localdeps                 |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; Localdeps must be a set of true lists ordered lexicographically.
;; (Note: "true lists" includes empty sets in the sense of
;; set::empty.)

(defun d-localdeps-good ()
  '(:dtree ((bar) (foo) (:hokey :smokes))
           nil))

(defthm d-localdeps-1
 (dtree::dtreep (d-localdeps-good)))

(defthm d-localdeps-2
 (equal (d-localdeps-good)
        (dtree::leaf '((bar) (foo) (:hokey :smokes)))))

(defun d-localdeps-bad ()
  '(:dtree ((foo bar) (bas bat))
           nil))

(defthm d-localdeps-3
 (not (dtree::dtreep (d-localdeps-bad))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                 Simple examples with non-trivial children                 |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; Note that the keys of the children don't have to be arranged in any
;; particular order.

(defun d-children-good ()
  '(:dtree nil ((:pow :dtree ((:wow :xox)) nil)
                (:foo :dtree ((:bar :bas)) nil))))

(defthm d-children-1
  (dtree::dtreep (d-children-good)))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                   Leaf                                    |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defthm d-leaf-1
  (equal (dtree::leaf '((:hither) (:thither) (:yon)))
         '(:dtree ((:hither) (:thither) (:yon)) nil)))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                 Children                                  |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defthm dtree-children-1
  (equal (dtree::children (d-children-good))
         '((:pow :dtree ((:wow :xox)) nil)
           (:foo :dtree ((:bar :bas)) nil))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                          A more complex example                           |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defun d-composed ()
  '(:dtree nil
           ((1 :dtree nil nil)
            (2 :dtree nil nil)
            (:st :dtree
                 nil
                 ((:bar :dtree
                        ((:eeny)
                         (:meeny)
                         (:miney)
                         (:st :bar)
                         (:st :bas)
                         (:st :foo))
                        ((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))
                  (:bas :dtree
                        ((:paper) (:rock) (:scissors))
                        ((:pow :dtree
                               ((:wow :zow))
                               nil)
                         (:how :dtree
                               ((:brown :cow :now))
                               nil)))
                  (:bat :dtree
                        ((:eeny)
                         (:meeny)
                         (:miney)
                         (:st :bar)
                         (:st :bas)
                         (:st :foo))
                        nil)
                  (:foo :dtree
                        ((:eeny)
                         (:meeny)
                         (:miney)
                         (:st :bar)
                         (:st :bas)
                         (:st :foo))
                        nil))))))

(defthm d-composed-1
 (dtree::dtreep (d-composed)))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                    Get                                    |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defthm d-get-1
  (equal
   (dtree::get '(:st) (d-composed))
   '(:dtree nil
            ((:bar :dtree
                   ((:eeny)
                    (:meeny)
                    (:miney)
                    (:st :bar)
                    (:st :bas)
                    (:st :foo))
                   ((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))
             (:bas :dtree ((:paper) (:rock) (:scissors))
                   ((:pow :dtree ((:wow :zow)) nil)
                    (:how :dtree ((:brown :cow :now)) nil)))
             (:bat :dtree
                   ((:eeny)
                    (:meeny)
                    (:miney)
                    (:st :bar)
                    (:st :bas)
                    (:st :foo))
                   nil)
             (:foo :dtree
                   ((:eeny)
                    (:meeny)
                    (:miney)
                    (:st :bar)
                    (:st :bas)
                    (:st :foo))
                   nil)))))

(defthm d-get-2
  (equal
   (dtree::get '(:st :bar) (d-composed))
   '(:dtree ((:eeny)
             (:meeny)
             (:miney)
             (:st :bar)
             (:st :bas)
             (:st :foo))
            ((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))))

(defthm d-get-3
  (equal
   (dtree::get '(:st :bar :gug) (d-composed))
   '(:dtree nil ((:wug :dtree ((:yug)) nil)))))

(defthm d-get-4
  (equal
   (dtree::get '(:st :bar :gug :wug) (d-composed))
   '(:dtree ((:yug)) nil)))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                 Getchild                                  |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; Getchild is the same as get on a path of length one.

#+from-child-lisp
(defthm getchild-is-get-of-singleton-list
  (equal (getchild a dtree)
         (get (list a) dtree))
  :hints(("Goal" :in-theory (enable in getchild get))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                    Set                                    |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

(defthm d-set-1
  (equal (dtree::set '(:key)
                     (dtree::leaf '((:hither) (:thither) (:yon)))
                     (d-empty))
         '(:dtree nil
                  ((:key :dtree ((:hither) (:thither) (:yon)) nil)))))

(defthm d-set-2
  (equal (dtree::set '(:foo :eeny) (d-children-good) (d-composed))
         '(:dtree nil
                  ((:foo :dtree nil
                         ((:eeny :dtree nil
                                 ((:pow :dtree ((:wow :xox)) nil)
                                  (:foo :dtree ((:bar :bas)) nil)))))
                   (1 :dtree nil nil)
                   (2 :dtree nil nil)
                   (:st :dtree nil
                        ((:bar :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               ((:gug :dtree
                                      nil ((:wug :dtree ((:yug)) nil)))))
                         (:bas :dtree ((:paper) (:rock) (:scissors))
                               ((:pow :dtree ((:wow :zow)) nil)
                                (:how :dtree ((:brown :cow :now)) nil)))
                         (:bat :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)
                         (:foo :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)))))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                Leafdomain                                 |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; Follow the paths through keys of the nested children alists to get
;; the leafdomain.
;;
(defthm d-leafdomain-1
  (equal (dtree::leafdomain (d-composed))
         '((1)
           (2)
           (:st :bar :gug :wug)
           (:st :bas :how)
           (:st :bas :pow)
           (:st :bat)
           (:st :foo))))

(defthm d-leafdomain-2
  (equal
   (dtree::leafdomain
    (dtree::set '(:new :path) (d-localdeps-good) (d-composed)))
   '((1)
     (2)
     (:new :path)
     (:st :bar :gug :wug)
     (:st :bas :how)
     (:st :bas :pow)
     (:st :bat)
     (:st :foo))))

;; Note that since (d-children-good) itself has paths, they are
;; appended to '(:new :path)

(defthm d-leafdomain-3
  (equal
   (dtree::leafdomain
    (dtree::set '(:new :path) (d-children-good) (d-composed)))
   '((1)
     (2)
     (:new :path :foo)
     (:new :path :pow)
     (:st :bar :gug :wug)
     (:st :bas :how)
     (:st :bas :pow)
     (:st :bat)
     (:st :foo))))

#| In the context of book GRAPH the following theorem can be proved.

(defthm gkeys=leafdomain
 (equal (cpath::gkeys (d-composed))
        (dtree::leafdomain (d-composed))))
 |#

;; Warning: the leafdomain of the trivial dtree is not nil, but
;; (list nil).
;;
(defthm d-leafdomain-4
  (equal (dtree::leafdomain dtree::*default*)
         '(nil)))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                  Domain                                   |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; To my understanding, the domain of a dtree is the union of all
;; initial sublists of elements of its leafdomain (arranged in
;; lexicographic order).
;;
(defthm d-domain-1
  (equal (dtree::domain (d-composed))
         '(nil (1)
               (2)
               (:st)
               (:st :bar)
               (:st :bar :gug)
               (:st :bar :gug :wug)
               (:st :bas)
               (:st :bas :how)
               (:st :bas :pow)
               (:st :bat)
               (:st :foo))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                  Remove                                   |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; (dtree::remove path dtree) removes path entirely from dtree.

;; This prunes the path '(:st :bas :how) leaving '(:st :bas :pow) in
;; the gkeys of (d-composed), just as I'd expect.
;;
(defthm d-remove-1
  (equal
   (dtree::remove '(:st :bas :how) (d-composed))
   '(:dtree nil
            ((:st :dtree nil
                  ((:bas :dtree
                         nil ((:pow :dtree ((:wow :zow)) nil)))
                   (:bar :dtree
                         ((:eeny)
                          (:meeny)
                          (:miney)
                          (:st :bar)
                          (:st :bas)
                          (:st :foo))
                         ((:gug :dtree
                                nil ((:wug :dtree ((:yug)) nil)))))
                   (:bat :dtree
                         ((:eeny)
                          (:meeny)
                          (:miney)
                          (:st :bar)
                          (:st :bas)
                          (:st :foo))
                         nil)
                   (:foo :dtree
                         ((:eeny)
                          (:meeny)
                          (:miney)
                          (:st :bar)
                          (:st :bas)
                          (:st :foo))
                         nil)))
             (1 :dtree nil nil)
             (2 :dtree nil nil)))))

;; I would expect that the path '(:st :bar :gug :wug) would be pruned
;; at :wug, leaving everthing else associated with '(:st :bar :gug)
;; alone, but what happens is that everything associated with the gkey
;; (:st :bar) is removed.  It's true that '(:st :bar :gug :wug) is the
;; only gkey rooted at (:st :bar), but why doesn't the rest of the
;; sub-dtree associated with '(:st :bar) count?
;;
(defthm d-remove-2
  (equal
   (dtree::remove '(:st :bar :gug :wug) (d-composed))
   '(:dtree nil
                ((:st :dtree nil
                      ((:bas :dtree ((:paper) (:rock) (:scissors))
                             ((:pow :dtree ((:wow :zow)) nil)
                              (:how :dtree ((:brown :cow :now)) nil)))
                       (:bat :dtree
                             ((:eeny)
                              (:meeny)
                              (:miney)
                              (:st :bar)
                              (:st :bas)
                              (:st :foo))
                             nil)
                       (:foo :dtree
                             ((:eeny)
                              (:meeny)
                              (:miney)
                              (:st :bar)
                              (:st :bas)
                              (:st :foo))
                             nil)))
                 (1 :dtree nil nil)
                 (2 :dtree nil nil)))))

;; Maybe this is the answer to the question above.  A path that leads
;; to no associated value may as well not be in the dtree: a "get" on
;; the path will yield the same answer either way.  After the remove,
;; the localdeps are all associated with nil, so they may as well not
;; appear.
;;
(defthm d-remove-3
  (and (equal (dtree::get '(:st :bar :eeny) (d-composed)) '(:dtree nil nil))
       (equal (dtree::get '(:st :bar :eeny)
                          (dtree::remove '(:st :bar :gug :wug) (d-composed)))
              (dtree::get '(:st :bar :eeny)
                          (d-composed)))))

;; Here's what happens when you remove a non-leaf path: every path
;; extending it is pruned.
;;
(defthm d-remove-4
  (equal (dtree::remove '(:st :bas) (d-composed))
         '(:dtree nil
                  ((:st :dtree nil
                        ((:bar :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               ((:gug :dtree
                                      nil ((:wug :dtree ((:yug)) nil)))))
                         (:bat :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)
                         (:foo :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)))
                   (1 :dtree nil nil)
                   (2 :dtree nil nil)))))

#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                                                           |#
#|                                   Erase                                   |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#

;; Follow the path '(:bar :st :wug) through the nested alists and
;; replace the associated dtree '(:dtree ((:gug)) nil) with the empty
;; dtree '(:dtree nil nil)
;;
(defthm d-erase-1
  (equal (dtree::erase '(:st :bar :gug :wug) (d-composed))
         '(:dtree nil
                  ((:st :dtree nil
                        ((:bar :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               ((:gug :dtree nil ((:wug :dtree nil nil)))))
                         (:bas :dtree ((:paper) (:rock) (:scissors))
                               ((:pow :dtree ((:wow :zow)) nil)
                                (:how :dtree ((:brown :cow :now)) nil)))
                         (:bat :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)
                         (:foo :dtree
                               ((:eeny)
                                (:meeny)
                                (:miney)
                                (:st :bar)
                                (:st :bas)
                                (:st :foo))
                               nil)))
                   (1 :dtree nil nil)
                   (2 :dtree nil nil)))))


;; We say that x is a subtree of y if both (1) the domain of x is a subset of
;; the domain of y, and (2) for every path in the domain of x, the localdeps of
;; this path in x are a subset of the localdeps of this path in y.

(defund subtree1 (locs sub super)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep sub)
                              (dtreep super))))
  (or (set::empty locs)
      (and (in (set::head locs) super)
           (set::subset
            (localdeps (get (set::head locs) sub))
            (localdeps (get (set::head locs) super)))
           (subtree1 (set::tail locs) sub super))))

(defund subtree (sub super)
  (declare (xargs :guard (and (dtreep sub)
                              (dtreep super))))
  (subtree1 (domain sub) sub super))

(defthm subtree1-of-dtreefix-of-sub
  (equal (subtree1 locs (dtreefix sub) super)
         (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subtree1-of-dtreefix-of-super
  (equal (subtree1 locs sub (dtreefix super))
         (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm in-super-when-subtree1-and-in-locs
  (implies (and (subtree1 locs sub super)
                (set::in path locs))
           (in path super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm in-localdeps-of-get-when-in-localdeps-of-get-of-subtree
  (implies (and (subtree1 locs sub super)
                (set::in path locs)
                (set::in a (localdeps (get path sub))))
           (set::in a (localdeps (get path super))))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subset-of-localdeps-of-gets-when-subtree1
  (implies (and (subtree1 locs sub super)
                (set::in path locs))
           (set::subset (localdeps (get path sub))
                         (localdeps (get path super)))))

(defthm subtree1-when-empty-locs
  (implies (set::empty locs)
           (subtree1 locs sub super))
  :hints(("Goal" :in-theory (enable subtree1))))

(defthm subtree-of-dtreefix-of-sub
  (equal (subtree (dtreefix sub) super)
         (subtree sub super))
  :hints(("Goal" :in-theory (enable subtree))))

(defthm subtree-of-dtreefix-of-super
  (equal (subtree sub (dtreefix super))
         (subtree sub super))
  :hints(("Goal" :in-theory (enable subtree))))

(defthm in-get-of-super-when-in-get-of-subtree
  (implies (and (subtree sub super)
                (in a (get path sub)))
           (in a (get path super))))

(defthm in-localdeps-of-get-when-subtree
   (implies (and (subtree sub super)
                 (set::in a (localdeps (get path sub))))
            (set::in a (localdeps (get path super))))
   :hints(("Goal"
           :in-theory (disable subset-of-localdeps-of-gets-when-subtree)
           :use (:instance subset-of-localdeps-of-gets-when-subtree))))

(defthm subset-of-localdeps-when-subtree
  (implies (subtree sub super)
           (set::subset (localdeps sub)
                         (localdeps super)))
  :hints(("Goal" :use (:instance subset-of-localdeps-of-gets-when-subtree
                                 (path nil)))))

(defthm in-localdeps-of-super-when-in-localdeps-of-subtree
  (implies (and (subtree sub super)
                (set::in a (localdeps sub)))
           (set::in a (localdeps super)))
  :hints(("Goal" :use (:instance in-localdeps-of-get-when-subtree
                                 (path nil)))))

(defthm subtree-reflexive
  (subtree x x))

(defthm subtree-transitive-one
  (implies (and (subtree x y)
                (subtree y z))
           (subtree x z)))

(defthm subtree-transitive-two
  (implies (and (subtree y z)
                (subtree x y))
           (subtree x z)))

(defthm subtree-of-get-with-get
  (implies (subtree sub super)
           (subtree (get path sub)
                    (get path super))))

(defthm in-children-of-super-when-in-children-of-subtree
  (implies (and (subtree sub super)
                (map::in key (children sub)))
           (map::in key (children super)))
  :hints(("Goal"
          :in-theory (enable in-children-is-in-of-singleton-path))))

(defthm subset-of-domains-when-subtree
  (implies (subtree sub super)
           (set::subset (map::domain (children sub))
                         (map::domain (children super)))))

(defthm in-deps-of-get-super-when-in-deps-of-get-subtree
  ;; We want to show that for every path, (deps (get path x)) is a subset of
  ;; (deps (get path y)).  To show this, by membership all we must do is show
  ;; that (in a (deps (get path x))) implies (in a (deps (get path y))).
  ;;
  ;; We use the depsource function to choose the particular path to the node in
  ;; (get path x) that has a as its localdep.  Then, since x is a subtree of y,
  ;; we know that a is also a localdep when we follow that same path through (get
  ;; path y).  Then, since a is a localdep of some path in (get path y), it
  ;; follows that a is a dep of y.
  (implies (and (subtree sub super)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal"
          :in-theory (disable in-localdeps-of-get-when-subtree
                              in-deps-when-in-localdeps-of-get
                              get-of-get)
          :use ((:instance in-localdeps-of-get-when-subtree
                           (sub (get path sub))
                           (super (get path super))
                           (path (depsource a (get path sub)))
                           (a a))
                (:instance in-deps-when-in-localdeps-of-get
                           (path (depsource a (get path sub)))
                           (dtree (get path super))
                           (a a))))))

(defthm in-deps-of-super-when-in-deps-of-subtree
  (implies (and (subtree sub super)
                (set::in a (deps sub)))
           (set::in a (deps super)))
  :hints(("Goal"
          :use (:instance in-deps-of-get-super-when-in-deps-of-get-subtree
                          (path nil)))))

(defthm subset-of-deps-when-subtree
  (implies (subtree sub super)
           (set::subset (deps sub)
                         (deps super))))



;; We now introduce a slightly weaker notion, where only the "deps" rather than
;; "localdeps" must be identical.
;;
;; bzo do we *really* want all of these rules, since after all some of them
;; are just the same as subtree rules, and we have the implication that
;; (subtree x y) => (subdeps x y) ?

(defund subdeps1 (locs sub super)
  (declare (xargs :guard (and (set::setp locs)
                              (dtreep sub)
                              (dtreep super))))
  (or (set::empty locs)
      (and (in (set::head locs) super)
           (set::subset
            (deps (get (set::head locs) sub))
            (deps (get (set::head locs) super)))
           (subdeps1 (set::tail locs) sub super))))

(defund subdeps (sub super)
  (declare (xargs :guard (and (dtreep sub)
                              (dtreep super))))
  (subdeps1 (domain sub) sub super))

(defthm subdeps1-of-dtreefix-of-sub
  (equal (subdeps1 locs (dtreefix sub) super)
         (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subdeps1-of-dtreefix-of-super
  (equal (subdeps1 locs sub (dtreefix super))
         (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm in-super-when-subdeps1-and-in-locs
  (implies (and (subdeps1 locs sub super)
                (set::in path locs))
           (in path super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm in-deps-of-get-super-when-in-deps-of-get-subdeps
  (implies (and (subdeps1 locs sub super)
                (set::in path locs)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subset-of-deps-of-gets-when-subdeps1
  (implies (and (subdeps1 locs sub super)
                (set::in path locs))
           (set::subset (deps (get path sub))
                         (deps (get path super)))))

(defthm subdeps1-when-empty-locs
  (implies (set::empty locs)
           (subdeps1 locs sub super))
  :hints(("Goal" :in-theory (enable subdeps1))))

(defthm subdeps-of-dtreefix-of-sub
  (equal (subdeps (dtreefix sub) super)
         (subdeps sub super))
  :hints(("Goal" :in-theory (enable subdeps))))

(defthm subdeps-of-dtreefix-of-super
  (equal (subdeps sub (dtreefix super))
         (subdeps sub super))
  :hints(("Goal" :in-theory (enable subdeps))))

(defthm in-get-of-super-when-in-get-of-subdeps
  (implies (and (subdeps sub super)
                (in a (get path sub)))
           (in a (get path super))))

(defthm in-deps-of-get-when-subdeps
  (implies (and (subdeps sub super)
                (set::in a (deps (get path sub))))
           (set::in a (deps (get path super))))
  :hints(("Goal"
          :in-theory (disable subset-of-deps-of-gets-when-subdeps)
          :use (:instance subset-of-deps-of-gets-when-subdeps))))

(defthm subset-of-deps-when-subdeps
  (implies (subdeps sub super)
           (set::subset (deps sub)
                         (deps super)))
  :hints(("Goal" :use (:instance subset-of-deps-of-gets-when-subdeps
                                 (path nil)))))

(defthm in-deps-of-super-when-in-deps-of-subdeps
  (implies (and (subdeps sub super)
                (set::in a (deps sub)))
           (set::in a (deps super)))
  :hints(("Goal" :use (:instance in-deps-of-get-when-subdeps
                                 (path nil)))))

(defthm subdeps-reflexive
  (subdeps x x))

(defthm subdeps-transitive-one
  (implies (and (subdeps x y)
                (subdeps y z))
           (subdeps x z)))

(defthm subdeps-transitive-two
  (implies (and (subdeps x y)
                (subdeps y z))
           (subdeps x z)))

(defthm subdeps-of-get-with-get
  (implies (subdeps sub super)
           (subdeps (get path sub)
                    (get path super))))

(defthm in-children-of-super-when-in-children-of-subdeps
  (implies (and (subdeps sub super)
                (map::in key (children sub)))
           (map::in key (children super)))
  :hints(("Goal"
          :in-theory (enable in-children-is-in-of-singleton-path))))

(defthm subset-of-domains-when-subdeps
  (implies (subdeps sub super)
           (set::subset (map::domain (children sub))
                         (map::domain (children super)))))

(defthm subdeps-when-subtree
  (implies (subtree sub super)
           (subdeps sub super)))

;; We now extend our subtree and subdeps relations to maps.  We call the
;; extended relations subtreemap and subdepsmap.

(defund subtreemap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super)
                              (dtreemapp sub)
                              (dtreemapp super))))
  (or (map::empty-exec sub)
      (and (map::in (map::head sub) super)
           (subtree (map::get (map::head sub) sub)
                    (map::get (map::head sub) super))
           (subtreemap (map::tail sub) super))))

(defthm in-super-when-in-subtreemap
  (implies (and (subtreemap sub super)
                (map::in key sub))
           (map::in key super))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm in-subtreemap-when-not-in-super
  (implies (and (subtreemap sub super)
                (not (map::in key super)))
           (equal (map::in key sub)
                  nil))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm subtree-of-gets-when-subtreemap
  (implies (subtreemap sub super)
           (equal (subtree (map::get key sub)
                           (map::get key super))
                  (if (map::in key sub)
                      t
                    (subtree (map::emptymap)
                             (map::get key super)))))
  :hints(("Goal" :in-theory (enable subtreemap))))


(defthm subtreemap-reflexive
  (subtreemap x x))

(defthm subtreemap-transitive-one
  (implies (and (subtreemap x y)
                (subtreemap y z))
           (subtreemap x z))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm subtreemap-transitive-two
  (implies (and (subtreemap y z)
                (subtreemap x y))
           (subtreemap x z)))

(defthm in-depsmap-of-super-when-in-depsmap-of-subtree
  (implies (and (subtreemap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable subtreemap))))

(defthm subset-of-depsmaps-when-subtreemap
  (implies (subtreemap sub super)
           (set::subset (depsmap sub)
                         (depsmap super))))

(defthm subtreemap-of-children-when-subtree
  (implies (subtree sub super)
           (subtreemap (children sub)
                       (children super)))
  :hints(("Goal"
          :in-theory (enable get-of-children-is-get-of-singleton-path))))

(defund subdepsmap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super)
                              (dtreemapp sub)
                              (dtreemapp super))))
  (or (map::empty-exec sub)
      (and (map::in (map::head sub) super)
           (subdeps (map::get (map::head sub) sub)
                    (map::get (map::head sub) super))
           (subdepsmap (map::tail sub) super))))

(defthm in-super-when-in-subdepsmap
  (implies (and (subdepsmap sub super)
                (map::in key sub))
           (map::in key super))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm in-subdepsmap-when-not-in-super
  (implies (and (subdepsmap sub super)
                (not (map::in key super)))
           (equal (map::in key sub)
                  nil))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subdeps-of-gets-when-subdepsmap
  (implies (subdepsmap sub super)
           (equal (subdeps (map::get key sub)
                           (map::get key super))
                  (if (map::in key sub)
                      t
                    (subdeps (map::emptymap)
                             (map::get key super)))))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subdepsmap-reflexive
  (subdepsmap x x))

(defthm subdepsmap-transitive-one
  (implies (and (subdepsmap x y)
                (subdepsmap y z))
           (subdepsmap x z))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subdepsmap-transitive-two
  (implies (and (subdepsmap y z)
                (subdepsmap x y))
           (subdepsmap x z)))

(defthm in-depsmap-of-super-when-in-depsmap-of-subdeps
  (implies (and (subdepsmap sub super)
                (set::in a (depsmap sub)))
           (set::in a (depsmap super)))
  :hints(("Goal" :in-theory (enable subdepsmap))))

(defthm subset-of-depsmaps-when-subdepsmap
  (implies (subdepsmap sub super)
           (set::subset (depsmap sub)
                         (depsmap super))))

(defthm subdepsmap-of-children-when-subdeps
  (implies (subdeps sub super)
           (subdepsmap (children sub)
                       (children super)))
  :hints(("Goal"
          :in-theory (enable get-of-children-is-get-of-singleton-path))))

(defthm subdepsmap-when-subtreemap
  (implies (subtreemap sub super)
           (subdepsmap sub super)))

;; We introduce dtree equivalences using "mutual subtrees" and "mutual
;; subdeps", so that dtrees are equivalent iff (1) their domains are the same,
;; and (2) the localdeps/deps at every path within both trees are the same
;; sets.

(defund equiv (x y)
  (declare (xargs :guard (and (dtreep x)
                              (dtreep y))))
  (and (subtree x y)
       (subtree y x)))

(defund equivdeps (x y)
  (declare (xargs :guard (and (dtreep x)
                              (dtreep y))))
  (and (subdeps x y)
       (subdeps y x)))

;; dtreefix - We write this rule with equiv rather than equivdeps, because it
;; is basically like writing "equal" instead of "iff".

(defthm dtreefix-under-equiv
  (equiv (dtreefix dtree) dtree)
  :hints(("Goal" :in-theory (enable equiv))))

;; In this litany of :congruence rules, we unfortunately have no rule about
;; (children dtree).  But what could we prove?  It is not even true that the
;; children must be MAPS::map-equal, because each child would only be equiv or
;; equivdeps, rather than truly equal in the ACL2 sense.  What we need are new
;; equivalences that permit such differences.

(defund equivmap (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (dtreemapp x)
                              (dtreemapp y))))
  (and (subtreemap x y)
       (subtreemap y x)))

(defund equivdepsmap (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (dtreemapp x)
                              (dtreemapp y))))
  (and (subdepsmap x y)
       (subdepsmap y x)))

;; dtreemapfix - dtreemapfix dtree-fixes each of its results, so it is not
;; map::equiv to its result, but it is surely equivmap to its result.

(defthm dtreemapfix-under-equivmap
  (equivmap (dtreemapfix map) map)
  :hints(("Goal" :in-theory (enable equivmap))))


;; Here is the erase function.  It operates on dtrees, and handles its own
;; recursion down into the children, which is sort of nice because it is
;; similar to the recursive schemes of "in" or "get"

(defund erase (path dtree)
  (declare (xargs :guard (dtreep dtree)
                  :verify-guards nil))
  (if (atom path) *default*
    (let ((children (children dtree)))
      (rawdtree
       (localdeps dtree)
       (cond #+erase
             ((atom (cdr path))
              (map::erase (car path) children))
             ((map::in (car path) children)
              (map::set (car path)
                        (erase (cdr path)
                               (map::get (car path) children))
                        children))
             (t children))))))

(defthm erase-of-dtreefix
  (equal (erase path (dtreefix dtree))
         (erase path dtree))
  :hints(("Goal" :in-theory (enable erase))))

(defthm dtreep-of-erase
  (dtreep (erase path dtree))
  :hints(("Goal" :in-theory (enable erase))))

(defthm localdeps-of-erase
  (equal (localdeps (erase path dtree))
         (if (atom path)
             (SET::emptyset)
           (localdeps dtree)))
  :hints(("Goal" :in-theory (enable erase))))

;; Congruences for Erase
;;
;; We show that erase produces EQUAL results whenever it is given path-equal
;; paths on some dtree, and that it produces EQUIV! results whenever it is
;; applied to some path on EQUIV! dtrees.
;;
;; Note that it is NOT true that "!-less" equiv is a congruence over erase.
;; Imagine, for example, the dtrees x and y, each with the same child who has
;; dependencies { x1 }.  If x has localdeps { x1, x2 } and y has localdeps { x2
;; }, then x and y are equiv (but not equiv!).  But in this event, erasing the
;; child from both trees will result in non-equiv trees!  This discovery led us
;; to introduce the more strict equiv! relation.

(defun erase-induction (other path dtree)
  (if (or (atom other) (atom path))
      *default*
    (let ((children (children dtree)))
      (rawdtree
       (localdeps dtree)
       (cond #+erase
             ((atom (cdr path))
              (map::erase (car path) children))
             ((map::in (car path) children)
              (map::set (car path)
                        (erase-induction (cdr other) (cdr path)
                               (map::get (car path) children))
                        children))
             (t children))))))

;; Membership/Domains After Erasure
;;
;; In the following rule, we show how how membership in the tree is affected by
;; erasing some node in the tree.  I wondered for awhile if there is some
;; better way to explain this, but now I think this rule is probably about what
;; we want.  After all, anything we come up with to describe how the domain
;; itself is changed would need a new recursive function that would probably be
;; somewhat difficult to reason about.  This fact about membership still
;; describes, in a complete sense, the shape of the resulting domain, it's just
;; that you will need to reason in terms of membership later, as well.

(defun erase-induction (other path dtree)
  (if (or (atom other) (atom path))
      *default*
    (let ((children (children dtree)))
      (rawdtree
       (localdeps dtree)
       (cond #+erase
             ((atom (cdr path))
              (map::erase (car path) children))
             ((map::in (car path) children)
              (map::set (car path)
                        (erase-induction (cdr other) (cdr path)
                               (map::get (car path) children))
                        children))
             (t children))))))

(defthm in-erase
  (equal (in ipath (erase epath dtree))
         (and (or (not (CPATH::dominates epath ipath))
                  (CPATH::dominates ipath epath))
              (in ipath dtree)))
  :hints(("Goal"
          :in-theory (enable cpath::dominates in erase)
          :induct (erase-induction ipath epath dtree))))

(defthm in-of-erase-same
  (equal (in path (erase path dtree))
         (in path dtree)))

(defthm in-erase-2
  (implies (in ipath (erase epath dtree))
           (in ipath dtree)))

(defthm subset-domain-erase
  (set::subset (domain (erase path dtree))
               (domain dtree)))

;; Standard Erasure Cancellation
;;
;; We adapt the rules in maps.lisp to suit our new erase function.  We provide
;; two rules, one which cancels erasures when we know they are irrelevant, and
;; one which moves erasures next to one another based on the term order.  The
;; reordering rule isn't provided until later in this file.

(defthm erase-when-non-consp-one
  (implies (not (consp path))
           (equal (erase path dtree)
                  *default*))
  :hints(("Goal" :in-theory (enable erase))))

(defthm erase-when-not-in
  (implies (not (in path dtree))
           (equiv (erase path dtree)
                  dtree))
  :hints(("Goal" :in-theory (enable erase in))))

;; Get After Erasure
;;
;; Erasure can impact the retrieved values from a get in a number of ways.
;; Suppose we are looking up "lpath" after erasing "epath".
;;
;;  1. If epath dominated lpath, then lpath has also been erased because it was
;;  a child of epath.  So, in that case, the get retrieves the default
;;  value.
;;
;;  2. If epath and lpath diverge, i.e., if neither dominates the other, then
;;  lpath is not affected by erasing epath, and we have no change whatsoever.
;;
;;  3. If lpath dominates epath, then a portion of lpath has been erased.  We
;;  can actually describe the result using nthcdr, but it is a rather ugly rule
;;  as you can see below.
;;
;; We will now prove each of these rules individually, with the appropriate
;; hypotheses about domination.

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-erase-when-epath-dominates
  (implies (CPATH::dominates epath gpath)
           (equal (get gpath (erase epath dtree))
                  *default*))
  :hints(("Goal" :in-theory (enable erase CPATH::DOMINATES get)
          :induct (erase-induction gpath epath dtree))))

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-erase-when-diverge
  (implies (CPATH::diverge gpath epath)
           (equal (get gpath (erase epath dtree))
                  (get gpath dtree)))
  :hints(("Goal" :in-theory (enable get erase)
          :induct (erase-induction gpath epath dtree))))

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-erase-when-neither-dominates
  (implies (and (not (CPATH::dominates gpath epath))
                (not (CPATH::dominates epath gpath)))
           (equal (get gpath (erase epath dtree))
                  (get gpath dtree)))
  :hints(("Goal"
          :in-theory (disable get-of-erase-when-diverge)
          :use (:instance get-of-erase-when-diverge))))

;; note: they are not truly equal in this case, only equiv!
(defthm get-of-erase-when-gpath-dominates
  (implies (CPATH::dominates gpath epath)
           (equiv (get gpath (erase epath dtree))
                  (erase (nthcdr (len gpath) epath)
                         (get gpath dtree))))
  :hints(("Goal"
          :in-theory (enable get erase)
          :induct (erase-induction gpath epath dtree))))

;; We now combine the individual cases into a case-splitting rule capable of
;; rewriting any (get path1 (erase path2 dtree)) term that might arise.
;;
;; I was hesitant to put this rule in, because it seems overly-aggressive.  Its
;; name reflects this, so hopefully it should stand out if/when it causes
;; problems, and people can just disable it.
;;
;; This rule subsumes get-erase-dominator, get-erase-dominated, and
;; get-erase-divergent, but I leave those enabled so if you disable this,
;; you can still reason about the particular cases if they arise.

(defthm get-of-erase-with-aggressive-case-splitting
  (equiv (get gpath (erase epath dtree))
         (if (CPATH::dominates gpath epath)
             (erase (nthcdr (len gpath) epath) (get gpath dtree))
           (if (CPATH::dominates epath gpath)
               *default*
             (get gpath dtree)))))

;; Deps After Erasure
;;
;; Much like domains, it seems that there are few good rules that we can write
;; about deps after erasure directly.  However, between the rules in-erase and
;; get-erase, we should still be able to describe the deps in a membership
;; oriented fashion.  This might be sometimes complicated, because of the need
;; to reason about an "existential" sort of property.

(defthm in-deps-when-in-deps-of-erase
  (implies (set::in a (deps (erase path dtree)))
           (set::in a (deps dtree)))
  :hints(("Goal"
          :in-theory (disable in-localdeps-of-get-depsource)
          :use ((:instance in-localdeps-of-get-depsource
                           (a a)
                           (dtree (erase path dtree)))
                (:instance in-deps-when-in-localdeps-of-get
                           (a a)
                           (path (depsource a (erase path dtree)))
                           (dtree dtree))))))

(defthm subset-of-deps-of-erase-with-deps
  (set::subset (deps (erase path dtree))
               (deps dtree)))

;; Erase After Erase Reordering
;;
;; This proof goes through automatically using the pick a point method, which
;; is quite nice since I had spent some time trying to prove it inductively
;; without success.  This is essentially the same as the "restrained" approach
;; to reducing erase/erase nests described in maps.lisp.

(defthm erase-of-erase
  (equiv (erase path1 (erase path2 dtree))
         (erase path2 (erase path1 dtree)))
  :rule-classes ((:rewrite :loop-stopper ((path1 path2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-is-idempotent
  (equiv (erase path (erase path dtree))
         (erase path dtree))
  :hints(("goal" :in-theory (enable equiv))))

;; Here is another version of "erase" that does more of what we
;; probably want from such a function.  Following execution of (remove
;; path dtree), path will not be in the "gkeys" of the dtree.

(defund remove (path dtree)
  (declare (xargs :guard (dtreep dtree)
                  :verify-guards nil))
  (if (atom path) *default*
    (let ((children  (children dtree))
          (localdeps (set::emptyset)))
      (if (map::in (car path) children)
          (let ((subtree (remove (cdr path) (map::get (car path) children))))
            (let ((children (map::erase (car path) children)))
              (cond
               ((map::empty (children subtree))
                (rawdtree
                 localdeps
                 (map::erase (car path) children)))
               (t
                (rawdtree
                 localdeps
                 (map::set (car path) subtree children))))))
        (rawdtree
         localdeps
         children)))))

(defthm remove-of-dtreefix
  (equal (remove path (dtreefix dtree))
         (remove path dtree))
  :hints(("Goal" :in-theory (enable remove))))

(defthm dtreep-of-remove
  (dtreep (remove path dtree))
  :hints(("Goal" :in-theory (enable remove))))

(defthm localdeps-of-remove
  (equal (localdeps (remove path dtree))
         (SET::emptyset))
  :hints(("Goal" :in-theory (enable remove))))

(defthm remove-from-empty-dtree
  (equal (dtree::remove path dtree::*default*)
         dtree::*default*)
  :hints (("Goal"
           :in-theory (enable dtree::remove))))

(defun cdr? (x)
  (if (consp x) (cdr x) nil))

(defun remove-induction (other path dtree)
  (if (atom path) *default*
    (let ((children  (children dtree))
          (localdeps (set::emptyset)))
      (if (map::in (car path) children)
          (let ((subtree (remove-induction (cdr? other) (cdr path) (map::get (car path) children))))
            (let ((children (map::erase (car path) children)))
              (cond
               ((map::empty (children subtree))
                (rawdtree
                 localdeps
                 (map::erase (car path) children)))
               (t
                (rawdtree
                 localdeps
                 (map::set (car path) subtree children))))))
        (rawdtree
         localdeps
         children)))))

(defthm open-in
  (implies
   (consp path)
   (equal (in path dtree)
          (AND (MAP::IN (CAR PATH) (CHILDREN DTREE))
               (IN (CDR PATH)
                   (MAP::GET (CAR PATH) (CHILDREN DTREE))))))
  :hints (("goal" :in-theory (enable in))))

(defthm open-dominates
  (implies
   (consp cpath::x)
   (equal (CPATH::DOMINATES CPATH::X CPATH::Y)
          (OR (NOT (CONSP CPATH::X))
                (AND (CONSP CPATH::Y)
                     (EQUAL (CAR CPATH::X) (CAR CPATH::Y))
                     (CPATH::DOMINATES (CDR CPATH::X)
                                      (CDR CPATH::Y)))))))

(defthm remove-induction-is-remove
  (equal (remove-induction ipath epath dtree)
         (remove epath dtree))
  :hints (("goal" :induct (remove-induction ipath epath dtree)
           :in-theory (enable remove))))

;; What does (hooey ipath epath dtree) mean?  First there are the
;; nuisance cases:
;;
;;   1. Both ipath and epath are atoms, or
;;   2. Just ipath is an atom.
;;
;; The meat of the defun is the following case
;;
;;   3. Both epath and ipath are CONSPs: Get the value associated with
;;      ipath in dtree.  Take the tail of epath beyond the length of
;;      ipath and remove it from the value above.  The result is not
;;      an empty map.
;;
;;      The intuition seems to be that there is more stored at ipath in dtree
;;      than can be taken away by removing the tail of epath.

(defund hooey (ipath epath dtree)
  (if (cpath::dominates epath ipath)
      ;; 1. and therefore (not (consp epath))
      (not (consp ipath))
    (or
     ;; 2. and therefore (consp epath)
     (not (consp ipath))
        ;; 3.
        (not (map::empty (children (remove (nthcdr (len ipath) epath)
                                           (get ipath dtree))))))))

(in-theory
 (disable
  open-dominates
  ))

(defthmd open-nthcdr
  (implies
   (not (zp n))
   (equal (nthcdr n l)
          (NTHCDR (+ N -1) (CDR L))))
  :hints (("goal" :in-theory (enable nthcdr))))

(defthmd in-to-hooey
  (implies
   (and
    (in ipath dtree)
    (not (cpath::diverge epath ipath)))
   (equal (in ipath (remove epath dtree))
          (hooey ipath epath dtree)))
  :hints(("Goal"
          :do-not '(generalize eliminate-destructors)
          :in-theory (enable hooey get nthcdr cpath::diverge cpath::dominates in remove)
          :induct (remove-induction ipath epath dtree))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable open-nthcdr cpath::diverge cpath::dominates in remove)))))

(defthmd in-remove-1
  (equal (in ipath (remove epath dtree))
         (if (in ipath dtree)
             (if (cpath::diverge epath ipath) t
               (in ipath (remove epath dtree)))
           nil))
  :hints(("Goal"
          :do-not '(generalize eliminate-destructors)
          :in-theory (enable get nthcdr cpath::diverge cpath::dominates in remove)
          :induct (remove-induction ipath epath dtree))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable nthcdr hooey cpath::diverge cpath::dominates in remove)))))

(defthm in-remove
  (equal (in ipath (remove epath dtree))
         (if (in ipath dtree)
             (if (cpath::diverge epath ipath) t
               (hooey ipath epath dtree))
           nil))
  :hints (("goal" :in-theory (enable in-to-hooey)
           :use in-remove-1)))

(defthm subset-domain-remove
  (set::subset (domain (remove path dtree))
               (domain dtree)))

(defthm remove-when-non-consp-one
  (implies (not (consp path))
           (equal (remove path dtree)
                  *default*))
  :hints(("Goal" :in-theory (enable remove))))

;; Not true, hence joed.
#+joe
(defthm remove-when-not-in
  (implies (not (in path dtree))
           (equiv (remove path dtree)
                  dtree))
  :hints(("Goal" :in-theory (enable remove in))))

(defthm remove-path-from-leaf
  (equal (remove path (leaf v))
         *default*)
  :hints (("Goal"
           :expand (remove path (leaf v))
           :do-not-induct t)))

(in-theory (disable dtree::open-in))

;; Note the slight type mismatch here.  We are calling memberp on a set, rather
;; than a list.  We allow this slight sloppiness since sets are, after all,
;; just ordered lists.  But, maybe this is bad.  Maybe we should have an
;; explicit casting function (implemented as the identity) to coerce from sets
;; to lists.

;; bzo this should be moved to the sets library.
(defthm memberp-when-setp
  (implies (set::setp x)
           (equal (list::memberp a x)
                  (set::in a x)))
  :hints(("Goal" :in-theory (enable set::sfix
                                    set::setp
                                    set::in
                                    set::empty
                                    set::head
                                    set::tail))))



;; Mini Essay on The Definition of Leafp
;;
;; Although it seems like a simple idea, there are actually many ways that we
;; could go about defining leafp.
;;
;; One approach, and the approach that we use for the actual defun of leafp, is
;; to think of leafp as a recursive function that is basically a copy of "in",
;; except that in the base case, we ensure that the final node we arrive at has
;; no children.  This approach might be convenient to use in inductive proofs
;; about leafp.
;;
;; An alternate approach is to define leafp nonrecursively.  In particular,
;; since the only modification to "in" was a modification to its base case, we
;; could simply "wrap" in with another test.  In other words, we could define
;; leafp as follows: path is a leaf of dtree whenever path is in dtree, and
;; also getting path from dtree yields a dtree with no children.  This might be
;; a convenient definition since much is known about "in" already.  And, we
;; provide a :definition rule, leafp-redefinition-in, that allows you to take
;; this view of leafp.
;;
;; Yet another view of leafp is discovered by looking at the way leafp
;; interacts with the domination relations in the paths library.  It should be
;; clear that a leaf is distinguished from interior nodes in the dtree in that
;; it dominates only itself.  With this in mind, we can define leafp as
;; follows: path is a leaf of dtree whenever path is in dtree, and also path
;; does not strictly dominate any path in the domain of the dtree.  We provide
;; yet another :definition rule, leafp-redefinition-dominates, that allows you
;; to take this view of leafp as it suits you.  (This definition takes some
;; work to prove, and thus occurs farther down in this file.)
;;
;; Note that leafp-redefinition-dominates, by expanding the leaf definition
;; into a call of (not (strictly-dominates-some path (domain dtree))).  This
;; opens up possibilities for using pick a point proofs to show that any other
;; path in the tree is not strictly dominated by this path.

(defund leafp (path dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (consp path)
      (and (map::in (car path) (children dtree))
           (leafp (cdr path)
                  (map::get (car path) (children dtree))))
    (map::empty (children dtree))))

(defthmd leafp-redefinition-in
  (equal (leafp path dtree)
         (and (in path dtree)
              (map::empty (children (get path dtree)))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable leafp in get))))

(defthm in-when-leafp
  (implies (leafp path dtree)
           (in path dtree))
  :hints(("Goal" :in-theory (enable leafp-redefinition-in))))

(defthm leafp-when-non-consp
  (implies (not (consp path))
           (equal (leafp path dtree)
                  (map::empty (children dtree))))
  :hints(("Goal" :in-theory (enable leafp-redefinition-in))))

;; this seems bad
;; (defthm children-empty-when-in-dtree
;;   (implies (in path dtree)
;;            (equal (map::empty (children (get path dtree)))
;;                   (leafp path dtree)))
;;   :hints(("Goal" :in-theory (enable leafp-redefinition-in))))

;; (theory-invariant
;;  (incompatible (:rewrite children-empty-when-in-dtree)
;;                (:definition leafp-redefinition-in)))


;; An important property of leaves is that they dominate no other paths in the
;; domain of the dtree except for themselves.

(defthm dominates-when-leafp-one
  (implies (and (leafp a dtree) ;; dtree is free
                (in b dtree))
           (equal (cpath::dominates a b)
                  (list::equiv a b)))
  :hints(("Goal" :in-theory (enable leafp in cpath::dominates))))

(defthm dominates-when-leafp-two
  (implies (and (in b dtree)    ;; dtree is free
                (leafp a dtree))
           (equal (cpath::dominates a b)
                  (list::equiv a b))))

(defthm diverge-when-leafp-one
  (implies (and (leafp a dtree)  ;; dtree is free
                (in b dtree))
           (equal (cpath::diverge a b)
                  (not (cpath::dominates b a))))
  :hints(("Goal" :in-theory (enable cpath::diverge))))

(defthm diverge-when-leafp-two
  (implies (and (in b dtree)     ;; dtree is free
                (leafp a dtree))
           (equal (cpath::diverge a b)
                  (not (cpath::dominates b a)))))



;; As I commented on in the Mini Essay on The Definition of Leafp, there is a
;; very strong relationship between being a leaf and strictly dominating some
;; path in the domain of a dtree.  In fact, leaves are exactly those paths that
;; do not strictly dominate any other paths found in the tree.

(defthm strictly-dominates-when-leafp-one
  (implies (and (leafp a dtree) ;; dtree is free
                (in b dtree))
           (equal (cpath::strictly-dominates a b)
                  nil))
  :hints(("Goal"
          :in-theory (e/d (cpath::strictly-dominates)
                          (dominates-when-leafp-one))
          :use (:instance dominates-when-leafp-one))))

(defthm strictly-dominates-when-leafp-two
  (implies (and (in b dtree)    ;; dtree is free
                (leafp a dtree))
           (equal (cpath::strictly-dominates a b)
                  nil)))


(defthm strictly-dominates-some-when-leafp
  (implies (leafp a dtree)
           (equal (cpath::strictly-dominates-some a (domain dtree))
                  nil)))

(defthmd leafp-redefinition-dominates
  (equal (leafp path dtree)
         (and (in path dtree)
              (not (cpath::strictly-dominates-some path (domain dtree)))))
  :rule-classes :definition)

(defthm deps-of-get-when-leafp
  (implies (leafp path dtree)
           (equal (deps (get path dtree))
                  (localdeps (get path dtree))))
  :hints(("Goal"
          :in-theory (enable leafp-redefinition-in)
          :use (:instance mrdeps (dtree (get path dtree))))))

(defthm domain-of-get-when-leafp
  (implies (leafp path dtree)
           (equal (domain (get path dtree))
                  '(nil)))
  :hints(("Goal" :in-theory (enable leafp-redefinition-in domain))))

(defthm in-of-get-when-leafp
  (implies (leafp path dtree)
           (equal (in a (get path dtree))
                  (list::equiv a nil)))
  :hints(("Goal"
          :in-theory (enable leafp-redefinition-in)
          :use (:instance in-of-domain
                          (path (list::fix a))
                          (dtree (get path dtree))))))

(defthm in-of-append-when-leafp
  (implies (leafp path dtree)
           (equal (in (append path a) dtree)
                  (list::equiv a nil)))
  :hints(("Goal"
          :in-theory (disable in-of-get-when-leafp)
          :use (:instance in-of-get-when-leafp))))

(defthm get-of-get-when-leafp
  (implies (leafp path dtree)
           (equal (get a (get path dtree))
                  (if (list::equiv a nil)
                      (get path dtree)
                    *default*))))

(defthm empty-of-children-of-get-when-leafp
  (implies (leafp path dtree)
           (map::empty (children (get path dtree))))
  :hints(("Goal" :in-theory (enable leafp-redefinition-in))))






;; The leafdomain is the set of all paths that lead to leaves from the dtree.
;; We implement this by simply filtering out all non-leaves from the standard
;; domain of the dtree.

(defund leafdomain1 (paths dtree)
  (declare (xargs :guard (and (set::setp paths)
                              (dtree::dtreep dtree))
                  :verify-guards nil))
  (if (set::empty paths)
      (set::emptyset)
    (if (leafp (set::head paths) dtree)
        (set::insert (set::head paths)
                     (leafdomain1 (set::tail paths) dtree))
      (leafdomain1 (set::tail paths)
                   dtree))))

(defthm setp-of-leafdomain1
  (set::setp (leafdomain1 paths dtree))
  :hints(("Goal" :in-theory (enable leafdomain1))))

(defthm listsetp-of-leafdomain1
  (implies (set::listsetp paths)
           (set::listsetp (leafdomain1 paths dtree)))
  :hints(("Goal" :in-theory (enable set::listsetp leafdomain1))))

; bzo set::in should be universally disabled.
(defthm in-leafdomain1
  (equal (set::in path (leafdomain1 paths dtree))
         (and (set::in path paths)
              (leafp path dtree)))
  :hints(("Goal" :in-theory (e/d (leafdomain1)
                                 (set::in)))))

(defund leafdomain (dtree)
  (declare (xargs :guard (dtree::dtreep dtree)))
  (leafdomain1 (domain dtree) dtree))

(defthm listsetp-of-leafdomain
  (set::listsetp (leafdomain dtree))
  :hints(("Goal" :in-theory (enable leafdomain))))

(defthm in-leafdomain
  (equal (set::in path (leafdomain dtree))
         (and (in path dtree)
              (leafp path dtree)
              (true-listp path)))
  :hints(("Goal" :in-theory (enable leafdomain))))


;; Throughout the dtree manipulation functions (erase, update) it is often be
;; necessary to build new dtrees, but rather than writing rules about (list
;; :dtree ...), we prefer a new, unique target for our rules.  Towards this
;; purpose, we introduce raw-dtree below.

(defund rawdtree (localdeps children)
  (declare (xargs :guard (and (set::listsetp localdeps)
                              (mapp children)
                              (dtreemapp children))))
  (list :dtree
        (set::listsetfix localdeps)
        (dtreemapfix children)))

(defthm dtreep-of-rawdtree
  (dtreep (rawdtree localdeps children))
  :hints(("Goal" :in-theory (enable rawdtree dtreep))))

(defthm localdeps-of-rawdtree
  (equal (localdeps (rawdtree localdeps children))
         (set::listsetfix localdeps))
  :hints(("Goal" :in-theory (enable localdeps rawdtree dtreep))))

(defthm children-of-rawdtree
  (equal (children (rawdtree localdeps children))
         (dtreemapfix children))
  :hints(("Goal" :in-theory (enable children rawdtree dtreep))))

;; We would like to have users of the library use the leaf function to
;; construct new dependency sets, rather than just consing together lists with
;; :dtree tags, etc.  Essentially, (leaf '(1 2 3)) creates a new dtree with no
;; children and a dependency set of { 1, 2, 3 }.

(defund leaf (locals)
  (declare (xargs :guard (set::listsetp locals)))
  (rawdtree locals (map::emptymap)))

(defcong set::listsetequiv equal (leaf locals) 1
  :hints(("Goal" :in-theory (enable leaf))))

(defthm dtreep-of-leaf
  (dtreep (leaf locals))
  :hints(("Goal" :in-theory (enable leaf))))

(defthm localdeps-of-leaf
  (equal (localdeps (leaf locals))
         (set::listsetfix locals))
  :hints(("Goal" :in-theory (e/d (leaf) (set::double-containment)))))

(defthm children-of-leaf
  (equal (children (leaf locals))
         (map::emptymap))
  :hints(("Goal" :in-theory (enable leaf))))

(defthm deps-of-leaf
  (equal (deps (leaf locals))
         (set::listsetfix locals))
  :hints(("Goal"
          :in-theory (disable set::double-containment)
          :use (:instance mrdeps (dtree (leaf locals))))))

(defthm domain-of-leaf
  (equal (domain (leaf locals))
         '(nil))
  :hints(("Goal" :in-theory (enable domain aux-domain))))

(defthm in-leaf
  (equal (in path (leaf locals))
         (atom path))
  :hints(("Goal" :in-theory (enable in))))

(defthm get-of-leaf
  (equal (get path (leaf locals))
         (if (atom path)
             (leaf locals)
           *default*))
  :hints(("Goal" :in-theory (enable get))))


(defund royalp (path dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (consp path)
      (and (set::empty (localdeps dtree))
           (map::in (car path) (children dtree))
           (royalp (cdr path) (map::get (car path) (children dtree))))
    (not (set::empty (localdeps dtree)))))

;; Unlike leafp, equivdeps is not a congruence over royalp.  Consider for
;; example a childless dtree with dependencies {x}, and another dtree with a
;; single child, no localdeps, and the child has dependencies {x}.  These
;; dtrees are equivdeps, but yield different values for (royalp nil [dt]).

(defthm in-when-royalp
  (implies (royalp path dtree)
           (in path dtree))
  :hints(("Goal" :in-theory (enable royalp in))))

(defthm royalp-when-not-consp
  (implies (not (consp path))
           (equal (royalp path dtree)
                  (not (set::empty (localdeps dtree)))))
  :hints(("Goal" :in-theory (enable royalp))))

(defthm empty-of-localdeps-of-get-when-royalp
  (implies (royalp path dtree)
           (equal (set::empty (localdeps (get path dtree)))
                  nil))
  :hints(("Goal" :in-theory (enable royalp get))))

(defthm empty-of-deps-of-get-when-royalp
  (implies (royalp path dtree)
           (equal (set::empty (deps (get path dtree)))
                  nil)))

(defthm empty-of-deps-when-royalp
  (implies (royalp path dtree)
           (equal (set::empty (deps dtree))
                  nil))
  :hints(("Goal"
          :in-theory (disable empty-of-deps-when-nonempty-of-localdeps-of-get)
          :use (:instance empty-of-deps-when-nonempty-of-localdeps-of-get))))

(defthm royalp-when-dominated-by-royalp-one
  (implies (and (royalp a dtree)
                (cpath::dominates a b))
           (equal (royalp b dtree)
                  (list::equiv a b)))
  :hints(("goal" :in-theory (enable royalp cpath::dominates))))

(defthm royalp-when-dominated-by-royalp-two
  (implies (and (cpath::dominates a b)
                (royalp a dtree))
           (equal (royalp b dtree)
                  (list::equiv a b))))

(defthm royalp-when-strictly-dominated-by-royalp-one
  (implies (and (royalp a dtree)
                (cpath::strictly-dominates a b))
           (equal (royalp b dtree)
                  nil)))

(defthm royalp-when-strictly-dominated-by-royalp-two
  (implies (and (cpath::strictly-dominates a b)
                (royalp a dtree))
           (equal (royalp b dtree)
                  nil)))


;; Membership strategy for proving (royalp path dtree)

 ;; Suppose that (royalp-hyps) is true, that our constraints are true, and
 ;; suppose towards contradiction that the following is true:
 ;;  (not (royalp (royalp-path) (royalp-dtree)))

 ;; Now, since the domination constraint is true for any royalp-member, it is
 ;; true for royal-memberp = (find-royal (royalp-path) (royalp-dtree)), where
 ;; (find-royal path dtree) is defined as follows:

 (local (defund find-royal (path dtree)
          (declare (xargs :guard (dtreep dtree)))
          (if (not (set::empty (localdeps dtree)))
              nil
            (if (and (consp path)
                     (map::in (car path) (children dtree)))
                (cons (car path)
                      (find-royal (cdr path)
                                  (map::get (car path) (children dtree))))
              nil))))

 ;; To generate our contradiction, we will need to show that the hypotheses in
 ;; our constraints are satisifed.  Of course, the hypothesis for the localdeps
 ;; constraint is trivial, since we assumed (royalp-hyps) is true.  For the
 ;; domination constraint, this also relieves the first hypothesis.

 ;; The second hypothesis of the domination constraint can be shown using a
 ;; simple instance of the folloiwng lemma, by setting path=(royalp-path) and
 ;; dtree=(royalp-dtree):

 (local (defthm in-of-find-royal
          (in (find-royal path dtree) dtree)
          :hints(("Goal" :in-theory (enable in find-royal)))))


 ;; To show the last hypothesis is true, we first introduce (voidp path dtree),
 ;; a predicate which returns true only if every node encountered along a path
 ;; through a dtree has empty localdeps:

 (local (defund voidp (path dtree)
          (declare (xargs :guard (dtreep dtree)))
          (and (set::empty (localdeps dtree))
               (or (atom path)
                   (and (map::in (car path) (children dtree))
                        (voidp (cdr path)
                               (map::get (car path) (children dtree))))))))

 ;; We observe that no royal path is ever void:
 (local (defthm voidp-when-royalp
          (implies (royalp path dtree)
                   (equal (voidp path dtree)
                          nil))
          :hints(("Goal" :in-theory (enable voidp royalp)))))

 ;; We observe that any path whose localdeps are nonempty is not void.
 (local (defthm voidp-when-get-of-localdeps-nonempty
          (implies (not (set::empty (localdeps (get path dtree))))
                   (equal (voidp path dtree)
                          nil))
          :hints(("Goal" :in-theory (enable voidp get)))))

 ;; We observe that find-royal returns an equivalent path only when it is given
 ;; a royal or void path as its input:
 (local (defthmd find-royal-does-nothing
          (equal (list::equiv (find-royal path dtree) path)
                 (or (royalp path dtree)
                     (voidp path dtree)))
          :hints(("Goal" :in-theory (enable find-royal royalp voidp)))))

 ;; We observe that find-royal always returns a path that dominates its input
 (local (defthm dominates-of-find-royal-with-input
          (cpath::dominates (find-royal path dtree) path)
          :hints(("Goal" :in-theory (enable find-royal)))))

 ;; We chain together these last observations to show that, if a path is not
 ;; royal, then find-royal will always return a strictly dominating path unless
 ;; its input is void.
 (local (defthm strictly-dominates-of-find-royal-with-input-when-not-royal
          (implies (not (royalp path dtree))
                   (equal (cpath::strictly-dominates (find-royal path dtree)
                                                    path)
                          (not (voidp path dtree))))
          :hints(("Goal" :in-theory (enable cpath::strictly-dominates)
                  :use find-royal-does-nothing))))

 ;; Here is how we argue that the final hypothesis is true.  Since we assumed
 ;; (towards contradiction) that (not (royalp (royalp-path) (royalp-dtree))),
 ;; then we know that
 ;;  (cpath::strictly-dominates (find-royal (royalp-path) (royalp-dtree))
 ;;                            (royalp-path))
 ;; exactly when (not (voidp (royalp-path) (royalp-dtree))).  But by our
 ;; localdeps constraint, we know that:
 ;;  (not (set::empty (localdeps (get (royalp-path) (royalp-dtree)))))
 ;; which we can use with voidp-when-get-of-localdeps-nonempty to conclude
 ;; that (voidp (royalp-path) (royalp-dtree)) is nil, and we are done.

 (local (defthm localdeps-of-find-royal-nonempty-when-input-nonempty
          (implies (not (set::empty (localdeps (get path dtree))))
                   (not (set::empty (localdeps
                                     (get (find-royal path dtree) dtree)))))
          :hints(("Goal" :in-theory (enable find-royal get)))))

 (defthm royalp-by-membership-driver
   (implies (royalp-hyps)
            (royalp (royalp-path) (royalp-dtree)))
   :hints(("Goal"
           :use ((:instance royalp-constraint-localdeps)
                 (:instance royalp-constraint-domination
                            (royalp-member
                             (find-royal (royalp-path) (royalp-dtree))))))))

 (defadvice royalp-by-membership
   (implies (royalp-hyps)
            (royalp (royalp-path) (royalp-dtree)))
   :rule-classes (:pick-a-point :driver royalp-by-membership-driver))

(defund royaldomain1 (paths dtree)
  (declare (xargs :guard (and (set::setp paths)
                              (dtree::dtreep dtree))
                  :verify-guards nil))
  (if (set::empty paths)
      (set::emptyset)
    (if (royalp (set::head paths) dtree)
        (set::insert (set::head paths)
                     (royaldomain1 (set::tail paths) dtree))
      (royaldomain1 (set::tail paths) dtree))))

(defthm setp-of-royaldomain1
  (set::setp (royaldomain1 paths dtree))
  :hints(("Goal" :in-theory (enable royaldomain1))))

(defthm listsetp-of-royaldomain1
  (implies (set::listsetp paths)
           (set::listsetp (royaldomain1 paths dtree)))
  :hints(("Goal" :in-theory (enable set::listsetp royaldomain1))))

; bzo set::in should be universally disabled
(defthm in-royaldomain1
  (equal (set::in path (royaldomain1 paths dtree))
         (and (set::in path paths)
              (royalp path dtree)))
  :hints(("Goal" :in-theory (e/d (royaldomain1)
                                 (set::in)))))

(defun royaldomain (dtree)
  (declare (xargs :guard (dtree::dtreep dtree)))
  (royaldomain1 (domain dtree) dtree))

(defthm listsetp-of-royaldomain
  (set::listsetp (royaldomain dtree))
  :hints(("Goal" :in-theory (enable royaldomain))))

(defthm in-royaldomain
  (equal (set::in path (royaldomain dtree))
         (and (in path dtree)
              (royalp path dtree)
              (true-listp path)))
  :hints(("Goal" :in-theory (enable royaldomain))))


(defund set (path value dtree)
  (declare (xargs :guard (and (dtreep value)
                              (dtreep dtree))
                  :verify-guards nil))
  (if (atom path)
      (dtreefix value)
    (let ((children (children dtree)))
      (rawdtree
       (localdeps dtree)
       (map::set (car path)
                 (set (cdr path)
                      value
                      (if (map::in (car path) children)
                          (map::get (car path) children)
                        *default*))
                 children)))))

(defthm set-of-dtreefix-one
  (equal (set path (dtreefix value) dtree)
         (set path value dtree))
  :hints(("Goal" :in-theory (enable set))))

(defthm set-of-dtreefix-two
  (equal (set path value (dtreefix dtree))
         (set path value dtree))
  :hints(("Goal" :in-theory (enable set))))

(defthm dtreep-of-set
  (dtreep (set path value dtree))
  :hints(("Goal" :in-theory (enable set))))

(defthm set-when-non-consp-path
  (implies (not (consp path))
           (equal (set path value dtree)
                  (dtreefix value)))
  :hints(("Goal" :in-theory (enable set))))

(defthm set-nil-to-leaf
  (equal (set nil (leaf v) dtree)
         (leaf v))
  :hints (("Goal"
           :expand ((set nil (leaf v) dtree)))))

(defthm localdeps-of-set
  (equal (localdeps (set path value dtree))
         (if (atom path)
             (localdeps value)
           (localdeps dtree)))
  :hints(("Goal" :in-theory (enable set))))

(defthm set-of-get-same
  (implies (in path dtree)
           (equiv (set path (get path dtree) dtree)
                  dtree))
  :hints(("Goal" :in-theory (enable set get in))))

;; Congruences for Set
;;
;; We show that set produces EQUAL results whenever it is given path-equal
;; paths on some dtree and value, and that it produces EQUIV! results whenever
;; it is applied to some path and value/dtree on EQUIV! dtrees/values.

(defun two-path-induction (other path dtree)
  (if (atom path)
      (list other path dtree)
    (let ((children (children dtree)))
      (if (map::in (car path) children)
          (two-path-induction (cdr other) (cdr path)
                              (map::get (car path) children))
        (two-path-induction (cdr other) (cdr path) *default*)))))

;; Membership After Set
;;
;; Set can impact the domain of a dtree in many ways.  Suppose we want to
;; know if "ipath" is in the tree after updating "spath" with "value".
;;
;;  1. If ipath dominated spath, then ipath is certainly a member of the new
;;  dtree because spath has been written, hence spath exists in the tree, and
;;  hence every path leaving to spath must also exist in the tree.
;;
;;  2. If ipath and spath diverge, i.e., if neither dominates the other, then
;;  ipath's existence is not affected by writing to spath, because the change
;;  affects some unrelated part of the tree, and we have no change whatsoever.
;;
;;  3. If spath dominates ipath, then a portion of ipath leads to value.  We
;;  will need to check the remaining tail of ipath to see if it was a path in
;;  value, but this is a rather ugly rule.
;;
;; We will now prove each of these rules individually, with the appropriate
;; hypotheses about domination.

(defthm in-set-when-inpath-dominates
  (implies (cpath::dominates ipath spath)
           (in ipath (set spath value dtree)))
  :hints(("Goal"
          :in-theory (enable in set)
          :induct (two-path-induction ipath spath dtree))))

(defthm in-set-when-diverge
  (implies (cpath::diverge ipath spath)
           (equal (in ipath (set spath value dtree))
                  (in ipath dtree)))
  :hints(("Goal"
          :in-theory (enable in set)
          :induct (two-path-induction ipath spath dtree))))

(defthm in-set-when-neither-dominates
  (implies (and (not (cpath::dominates ipath spath))
                (not (cpath::dominates spath ipath)))
           (equal (in ipath (set spath value dtree))
                  (in ipath dtree)))
  :hints(("Goal"
          :in-theory (disable in-set-when-diverge)
          :use (:instance in-set-when-diverge))))

(defthm in-set-when-setpath-dominates
  (implies (cpath::dominates spath ipath)
           (equal (in ipath (set spath value dtree))
                  (in (nthcdr (len spath) ipath)
                      value)))
  :hints(("Goal"
          :in-theory (enable in set)
          :induct (two-path-induction ipath spath dtree))))

;; We now combine the individual cases into a case-splitting rule capable of
;; rewriting any (in path1 (set path2 value dtree)) term that might arise.
;;
;; I was hesitant to put this rule in, because it seems overly-aggressive.  Its
;; name reflects this, so hopefully it should stand out if/when it causes
;; problems, and people can just disable it.
;;
;; This rule subsumes in-set-dominates, in-set-diverge, and
;; in-set-dominated, but I leave those enabled so if you disable this, you
;; can still reason about the particular cases if they arise.

(local (in-theory (disable acl2::iff-reduction)))

(defthm in-set-with-aggressive-case-splitting
  (equal (in ipath (set spath value dtree))
         (if (cpath::dominates ipath spath)
             t
           (if (cpath::dominates spath ipath)
               (in (nthcdr (len spath) ipath) value)
             (in ipath dtree)))))

;; Get After Set
;;
;; The rules for get after set are very similar to the rules for
;; membership after set.  Again, we prove some hypothesis-bearing individual
;; rules, then provide an aggressive case-splitting rule that subsumes these
;; rules, but which can be disabled by the user.

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-set-when-getpath-dominates
  (implies (cpath::dominates gpath spath)
           (equal (get gpath (set spath value dtree))
                  (set (nthcdr (len gpath) spath)
                       value
                       (get gpath dtree))))
  :hints(("Goal"
          :in-theory (enable get set)
          :induct (two-path-induction gpath spath dtree))))

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-set-when-diverge
  (implies (cpath::diverge gpath spath)
           (equal (get gpath (set spath value dtree))
                  (get gpath dtree)))
  :hints(("Goal"
          :in-theory (enable get set)
          :induct (two-path-induction gpath spath dtree))))

;; note: they are truly equal in this case, not just equiv!
(defthm get-of-set-when-neither-dominates
  (implies (and (not (cpath::dominates gpath spath))
                (not (cpath::dominates spath gpath)))
           (equal (get gpath (set spath value dtree))
                  (get gpath dtree)))
  :hints(("Goal"
          :in-theory (disable get-of-set-when-diverge)
          :use (:instance get-of-set-when-diverge))))

;; note: they are only equiv in this case, not truly equal!
(defthm get-of-set-when-setpath-dominates
  (implies (cpath::dominates spath gpath)
           (equiv (get gpath (set spath value dtree))
                  (get (nthcdr (len spath) gpath)
                       value)))
  :hints(("Goal"
          :in-theory (enable get set)
          :induct (two-path-induction gpath spath dtree))))

(defthm get-of-set-with-aggressive-case-splitting
  (equiv (get gpath (set spath value dtree))
         (if (cpath::dominates gpath spath)
             (set (nthcdr (len gpath) spath) value (get gpath dtree))
           (if (cpath::dominates spath gpath)
               (get (nthcdr (len spath) gpath) value)
             (get gpath dtree)))))

;; Set after Set

(defthm set-of-set-when-first-dominates
  (implies (cpath::dominates p1 p2)
           (equiv (set p1 v1 (set p2 v2 dtree))
                  (set p1 v1 dtree)))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-set-when-neither-dominates
   (implies (and (not (cpath::dominates p1 p2))
                 (not (cpath::dominates p2 p1)))
            (equiv (set p1 v1 (set p2 v2 dtree))
                   (set p2 v2 (set p1 v1 dtree))))
   :rule-classes ((:rewrite :loop-stopper ((p1 p2 set))))
   :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-set-when-diverge
   (implies (cpath::diverge p1 p2)
            (equiv (set p1 v1 (set p2 v2 dtree))
                   (set p2 v2 (set p1 v1 dtree))))
   :rule-classes ((:rewrite :loop-stopper ((p1 p2 set)))))

;; (defthm lemma
;;   (implies (set::in a (deps value))
;;            (set::in a (deps (set path value dtree))))
;;   :hints(("Goal" :in-theory (enable set))))

;; (defthm deps-set-weak
;;   (implies (set::in a (deps (set path value dtree)))
;;            (set::in a (set::union (deps value)
;;                                     (deps dtree))))
;;   :hints(("Goal" :in-theory (enable set))))

;; (IMPLIES
;;  (AND (CONSP PATH)
;;       (set::IN (CAR PATH)
;;                 (MAPS::DOMAIN (CHILDREN DTREE)))
;;       (set::IN A
;;                 (DEPS (SET (CDR PATH)
;;                               VALUE
;;                               (MAPS::GET (CAR PATH)
;;                                          (CHILDREN DTREE)))))
;;       (set::IN A (DEPS VALUE))
;;       (NOT (set::IN A (LOCALDEPS DTREE))))
;;  (set::IN
;;   A
;;   (DEPSMAP (MAPS::SET (CAR PATH)
;;                       (SET (CDR PATH)
;;                               VALUE
;;                               (MAPS::GET (CAR PATH) (CHILDREN DTREE)))
;;                       (CHILDREN DTREE)))))
