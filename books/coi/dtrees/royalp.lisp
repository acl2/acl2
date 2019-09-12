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
;; We say that a path, p, is a "royal path" in a dtree exactly when all of the
;; following conditions hold:
;;
;;   (1) p is in the dtree, i.e., (in p dtree)
;;
;;   (2) the localdeps of p are nonempty, i.e.,
;;        (not (set::empty (localdeps (get p dtree))))
;;
;;   (3) for all a, the following is true:
;;       (implies (and (in a dtree)
;;                     (strictly-dominates a p))
;;                (set::empty (localdeps (get a dtree))))
;;
;; In other words, royal paths are the "first" nodes that actually have
;; localdeps in the dtree.  Hence, the deps of the entire dtree can be
;; understood through only the deps of its royal parts.  We recognize royal
;; paths using the predicate (royalp path dtree), and we define the royaldomain
;; of a dtree as the set of all royal paths in the dtree.

(in-package "DTREE")
(include-book "equiv")
(include-book "../paths/dominates")
(include-book "../paths/diverge")
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defund royalp (path dtree)
  (declare (xargs :guard (dtreep dtree)))
  (if (consp path)
      (and (set::empty (localdeps dtree))
           (map::in (car path) (children dtree))
           (royalp (cdr path) (map::get (car path) (children dtree))))
    (not (set::empty (localdeps dtree)))))

(encapsulate
 ()

 (local (defun my-induction (path path-equiv dtree)
          (if (and (consp path)
                   (consp path-equiv))
              (my-induction (cdr path) (cdr path-equiv)
                            (map::get (car path) (children dtree)))
            (list path path-equiv dtree))))

 (defcong list::equiv equal (royalp path dtree) 1
   :hints(("Goal" :in-theory (enable royalp)
           :induct (my-induction path path-equiv dtree))))
)


;; Unlike leafp, equivdeps is not a congruence over royalp.  Consider for
;; example a childless dtree with dependencies {x}, and another dtree with a
;; single child, no localdeps, and the child has dependencies {x}.  These
;; dtrees are equivdeps, but yield different values for (royalp nil [dt]).

(defcong equiv equal (royalp path dtree) 2
  :hints(("Goal" :in-theory (enable royalp))))

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

(encapsulate
 ()

 (encapsulate
  (((royalp-hyps) => *)
   ((royalp-path) => *)
   ((royalp-dtree) => *))
  (local (defun royalp-hyps () nil))
  (local (defun royalp-path () nil))
  (local (defun royalp-dtree () nil))

  (defthmd royalp-constraint-localdeps
    (implies (royalp-hyps)
             (not (set::empty
                   (localdeps (get (royalp-path) (royalp-dtree)))))))

  (defthmd royalp-constraint-domination
    (implies (and (royalp-hyps)
                  (in royalp-member (royalp-dtree))
                  (cpath::strictly-dominates royalp-member (royalp-path)))
             (set::empty (localdeps (get royalp-member (royalp-dtree)))))))

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

 )





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

(defcong dtree::equiv equal (royaldomain1 paths dtree) 2
  :hints(("Goal" :in-theory (enable royaldomain1))))

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

(verify-guards royaldomain1)

(defun royaldomain (dtree)
  (declare (xargs :guard (dtree::dtreep dtree)))
  (royaldomain1 (domain dtree) dtree))

(defcong dtree::equiv equal (royaldomain dtree) 1
  :hints(("Goal" :in-theory (enable royaldomain1))))

(defthm listsetp-of-royaldomain
  (set::listsetp (royaldomain dtree))
  :hints(("Goal" :in-theory (enable royaldomain))))

(defthm in-royaldomain
  (equal (set::in path (royaldomain dtree))
         (and (in path dtree)
              (royalp path dtree)
              (true-listp path)))
  :hints(("Goal" :in-theory (enable royaldomain))))
