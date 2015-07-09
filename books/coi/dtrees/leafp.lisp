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
;; We introduce functions for talking only about the leaves of a dtree.  The
;; function (leafp path dtree) is a predicate which returns true only if path
;; is (in path dtree) and (get path dtree) has no children.  We say that a
;; path is a leaf of a dtree whenever it satisfies leafp for that dtree.
;;
;; The function (leafdomain dtree) returns exactly the set paths which satisfy
;; (leafp path dtree).  We know that the deps of any leaf path are the same as
;; its localdeps, and other interesting properties, i.e., only atomic paths are
;; members of the dtrees retrieved from leaf paths, etc.

(in-package "DTREE")
(include-book "equiv")
(include-book "../paths/dominates")
(include-book "../paths/diverge")
(local (include-book "arithmetic/top-with-meta" :dir :system))


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

(defcong list::equiv equal (leafp path dtree) 1
  :hints(("Goal" :in-theory (enable leafp-redefinition-in))))

(defcong equivdeps equal (leafp path dtree) 2
  :hints(("Goal" :in-theory (enable leafp-redefinition-in))))

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


(encapsulate
 ()

 ;; We already know from above that any leaf will not strictly dominate any
 ;; path in the dtree.  We now need to reverse this, and show that when some
 ;; path does not strictly dominate any path, then it is a leaf.
 ;;
 ;; Suppose towards contradiction that there is some path that is not a leaf,
 ;; and yet does not strictly dominate any path in the tree.  Well, since it is
 ;; not a leaf, it has nonempty children, which means that it has at least one
 ;; child, the head of its children.  Consider the path obtained by appending
 ;; path to the singleton list containing only the name of this child.  Surely
 ;; this path is strictly dominated by path.  But we also can see that this new
 ;; path is itself in the dtree, contradicting our assumption. QED.

 (local (defthm lemma1
          (implies (and (consp path)
                        (map::in (car path) (children dtree)))
                   (equal (get (cdr path) (map::get (car path) (children dtree)))
                          (get path dtree)))
          :hints(("Goal" :in-theory (enable get)))))

 (local (defthm lemma2
          (implies (and (in path dtree)
                        (not (map::empty (children (get path dtree)))))
                   (in (append path (list (map::head (children (get path dtree)))))
                       dtree))
          :hints(("Goal" :in-theory (enable in)))))
;;                                         (children-empty-when-in-dtree))))))

 (local (defthm lemma3
          (implies (and (not (cpath::strictly-dominates-some path (domain dtree)))
                        (in path dtree))
                   (leafp path dtree))
          :hints(("Goal"
                  :in-theory (e/d (leafp-redefinition-in)
                                  (cpath::strictly-dominates-some-by-membership))
                  :use ((:instance cpath::strictly-dominates-some-by-membership
                                   (cpath::b (append path (list (map::head (children (get path dtree))))))
                                   (cpath::a path)
                                   (cpath::x (domain dtree))))))))

 (defthm leafp-when-not-strictly-dominates-some-of-domain
   (implies (not (cpath::strictly-dominates-some path (domain dtree)))
            (equal (leafp path dtree)
                   (in path dtree))))

)

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

(defcong dtree::equivdeps equal (leafdomain1 paths dtree) 2
  :hints(("Goal" :in-theory (enable leafdomain1))))

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

(verify-guards leafdomain1)

(defund leafdomain (dtree)
  (declare (xargs :guard (dtree::dtreep dtree)))
  (leafdomain1 (domain dtree) dtree))

(defcong dtree::equivdeps equal (leafdomain dtree) 1
  :hints(("Goal" :in-theory (enable leafdomain))))

(defthm listsetp-of-leafdomain
  (set::listsetp (leafdomain dtree))
  :hints(("Goal" :in-theory (enable leafdomain))))

(defthm in-leafdomain
  (equal (set::in path (leafdomain dtree))
         (and (in path dtree)
              (leafp path dtree)
              (true-listp path)))
  :hints(("Goal" :in-theory (enable leafdomain))))
