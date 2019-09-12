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
;; update.lisp
;;
;; Introduces update, the function for overwriting locations in dtrees with new
;; dtrees.

(in-package "DTREE")
(include-book "raw")
(include-book "../paths/dominates")
(include-book "../paths/diverge")
(local (include-book "arithmetic/top-with-meta" :dir :system))

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

(verify-guards set)

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

(defcong list::equiv equal (set path value dtree) 1
  :hints(("Goal"
          :in-theory (enable set)
          :induct (two-path-induction path path-equiv dtree))))

(defcong equivdeps equivdeps (set path value dtree) 2
  :hints(("Goal" :in-theory (enable set))))

(defcong equiv equiv (set path value dtree) 2
  :hints(("Goal" :in-theory (enable set))))

(defcong equiv equiv (set path value dtree) 3
  :hints(("Goal" :in-theory (enable set))))

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

(local
 (encapsulate
     ()

;; DAG -- ok, why doesn't the subsequent theorem prove without these
;; helper lemmas?  In my effort, I saw a failed subgoal of the form:
#|
(IMPLIES (AND (CPATH::DOMINATES P1 P2)
              (CPATH::DOMINATES SUBTREE-PATH P1)
              (NOT (EQUAL (LEN SUBTREE-PATH) (LEN P1)))
              (EQUAL (LEN SUBTREE-PATH) (LEN P2)))
         (SET::SUBSET (LOCALDEPS V2)
                      (LOCALDEPS (GET SUBTREE-PATH DTREE))))
|#
;; which should be a contradiction, given linear reasoning.

(defthm dominates-implies-<=-fwd
  (implies
   (cpath::dominates x y)
   (<= (len x) (len y)))
  :rule-classes (:forward-chaining))

(defthm <=-chaining-fwd
  (implies
   (and
    (<= x y)
    (<= z x))
   (<= z y))
  :rule-classes (:forward-chaining))

(defthm <=-to-<-fwd
  (implies
   (and
    (<= x y)
    (integerp x)
    (integerp y)
    (not (equal x y)))
   (< x y))
  :rule-classes (:forward-chaining))

(defthm <-to-not-equal
  (implies
   (< x y)
   (not (equal x y)))
  :rule-classes (:forward-chaining))

))

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

(encapsulate
 ()

 (local (defthm in-set-of-set-when-dominated-forward
          (implies (and (cpath::dominates p2 p1)
                        (in path (set p1 v1 (set p2 v2 dtree))))
                   (in path (set p2 (set (nthcdr (len p2) p1) v1 v2)
                                    dtree)))))

 (local (defthm in-setd-of-set-when-dominated-backward
          (implies (and (cpath::dominates p2 p1)
                        (in path (set p2 (set (nthcdr (len p2) p1) v1 v2)
                                         dtree)))
                   (in path (set p1 v1 (set p2 v2 dtree))))))

 (local (in-theory (enable acl2::iff-reduction)))
 (local (defthm in-set-of-set-when-dominated
          (implies (cpath::dominates p2 p1)
                   (equal (in path (set p1 v1 (set p2 v2 dtree)))
                          (in path (set p2 (set (nthcdr (len p2) p1) v1 v2)
                                           dtree))))
          :hints(("Goal"
                  :in-theory (disable in-set-with-aggressive-case-splitting)))))

 (local (defthm in-localdeps-get-set-of-set-dominated-forward
          (implies (and (cpath::dominates p2 p1)
                        (set::in elem
                                 (localdeps (get path
                                                 (set p1 v1
                                                      (set p2 v2 dtree))))))
                   (set::in elem
                            (localdeps
                             (get path
                                  (set p2
                                       (set (nthcdr (len p2) p1) v1 v2)
                                       dtree)))))))

 (local (defthm in-localdeps-get-set-of-set-dominated-backward
          (implies (and (cpath::dominates p2 p1)
                        (set::in elem
                                 (localdeps
                                  (get path
                                       (set p2
                                            (set (nthcdr (len p2) p1) v1 v2)
                                            dtree)))))
                   (set::in elem
                            (localdeps
                             (get path (set p1 v1
                                            (set p2 v2 dtree))))))))

 (local (defthm in-localdeps-get-set-of-set-dominated
          (implies (cpath::dominates p2 p1)
                   (equal (set::in elem
                                   (localdeps (get path
                                                   (set p1 v1
                                                        (set p2 v2 dtree)))))
                          (set::in elem
                                   (localdeps
                                    (get path
                                         (set p2
                                              (set (nthcdr (len p2) p1) v1 v2)
                                              dtree))))))))

 (local (defthm localdeps-get-set-of-set-dominated
          (implies (cpath::dominates p2 p1)
                   (equal (localdeps (get path (set p1 v1
                                                    (set p2 v2 dtree))))
                          (localdeps (get path
                                          (set p2
                                               (set (nthcdr (len p2) p1) v1 v2)
                                               dtree)))))))

 (local (defthm subtree-set-of-set-dominated-forward
          (implies (cpath::dominates p2 p1)
                   (subtree (set p1 v1 (set p2 v2 dtree))
                            (set p2 (set (nthcdr (len p2) p1) v1 v2)
                                 dtree)))))

 (local (defthm subtree-set-of-set-dominated-backward
          (implies (cpath::dominates p2 p1)
                   (subtree (set p2 (set (nthcdr (len p2) p1) v1 v2) dtree)
                            (set p1 v1 (set p2 v2 dtree))))))

 (defthm set-of-set-when-second-dominates
   (implies (cpath::dominates p2 p1)
            (equiv (set p1 v1 (set p2 v2 dtree))
                   (set p2 (set (nthcdr (len p2) p1) v1 v2) dtree)))
   :hints(("Goal" :in-theory (enable equiv))))

 )

;; (i-am-here)

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
