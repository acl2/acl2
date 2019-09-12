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

;; Dependency Trees for Data Dependency Analysis
;; Jared Davis
;;
;;
;; erase.lisp
;;
;; Introduces erase, the function for removing paths from dtrees.

(in-package "DTREE")
(include-book "set")
(include-book "../paths/dominates")
(include-book "../paths/diverge")
(local (include-book "arithmetic/top-with-meta" :dir :system))

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

(verify-guards erase)

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

(defcong list::equiv equal (erase path dtree) 1
  :hints(("Goal"
          :in-theory (enable erase)
          :induct (erase-induction path path-equiv dtree))))

(defcong equiv equiv (erase path dtree) 2
  :hints(("Goal" :in-theory (enable erase))))

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

(local
 (encapsulate
  ()

  ;; This is a test to ensure that our erasure strategy seems to be working as
  ;; intended.  Don't remove this just becuase it has no effect on the logical
  ;; world!

  (local (encapsulate
          (((foo1 *) => *)
           ((foo2 *) => *)
           ((foo3 *) => *)
           ((foo4 *) => *)
           ((foo5 *) => *)
           ((foo6 *) => *))
          (local (defun foo1 (x) x))
          (local (defun foo2 (x) x))
          (local (defun foo3 (x) x))
          (local (defun foo4 (x) x))
          (local (defun foo5 (x) x))
          (local (defun foo6 (x) x))
          (defthm test-constraint
            (equal (foo1 x)
                   (foo3 x)))))

  (local (defthm test-erasure-reductions
           (equiv (erase (foo1 x)
                         (erase (foo2 x)
                                (erase (foo3 x)
                                       (erase (foo4 x)
                                              (erase (foo5 x)
                                                     (erase (foo6 x)
                                                            Y))))))
                  (erase (foo6 x)
                         (erase (foo2 x)
                                (erase (foo4 x)
                                       (erase (foo3 x)
                                              (erase (foo5 x)
                                                     Y))))))))))

;; bzo - still need lots of theorems, e.g., erases of sets, and so forth.

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

(set-irrelevant-formals-ok t)

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

(defcong list::equiv equal (remove path dtree) 1
  :hints(("Goal"
          :in-theory (enable remove)
          :induct (remove-induction path path-equiv dtree))))

(defcong equiv equiv (remove path dtree) 2
  :hints(("Goal" :in-theory (enable remove))))

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

(verify-guards remove)
