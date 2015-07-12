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

(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; maps-definitions.lisp
;; John D. Powell
;(in-package "MAPS")

;;
;; This file isolates maps definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the maps book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(local (in-theory (enable predicate-boolean)))

;; Originally tried to force typed-mapp to also check that its argument was a
;; map.  However, I have found that dropping this requirement makes it much
;; easier to work with typed maps.  For example, equiv is now an equivalence
;; relation over typed-mapp.

(defun typed-mapp (map)
  (or (empty map)
      (and (predicate (head map) (get (head map) map))
           (typed-mapp (tail map)))))

(defthm predicate-when-in-typed-mapp
  (implies (and (typed-mapp map)
                (in a map))
           (predicate a (get a map))))

(defthm not-typed-mapp-when-bad-member
  (implies (and (in a map)
                (not (predicate a (get a map))))
           (not (typed-mapp map))))

(local (defun typed-mapp-badguy (map)
         (if (empty map)
             nil
           (if (predicate (head map) (get (head map) map))
               (typed-mapp-badguy (tail map))
             (head map)))))

(local (defthm typed-mapp-badguy-witnesses
         (implies (and (not (typed-mapp map)))
                  (and (in (typed-mapp-badguy map) map)
                       (not (predicate (typed-mapp-badguy map)
                                       (get (typed-mapp-badguy map) map)))))
         :rule-classes nil))

(defthmd typed-mapp-by-membership
  (implies (typed-mapp-hyps)
           (typed-mapp (typed-mapp-map)))
  :hints(("Goal" :use (:instance typed-mapp-badguy-witnesses
                                 (map (typed-mapp-map))))))

(defthm typed-mapp-of-erase
  (implies (typed-mapp map)
           (typed-mapp (erase key map)))
  :hints(("Goal" :use (:functional-instance
                       typed-mapp-by-membership
                       (typed-mapp-hyps
                        (lambda () (typed-mapp map)))
                       (typed-mapp-map
                        (lambda () (erase key map)))))))

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp x)
                       (booleanp y))
                  (equal (equal x y)
                         (iff x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defund mapp (map)
  (declare (xargs :guard t))
  (alistp map))

;; We don't want to export this theorem, because we don't want to expose the
;; underlying implementation of maps.
(local (defthm alistp-when-mapp
         (implies (mapp x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable mapp)))))


(defund domain (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     (set::emptyset))
                    ((atom (car map))
                     (domain (cdr map)))
                    (t (set::insert (caar map)
                                     (domain (cdr map)))))
       :exec (set::mergesort (strip-cars map))))

(defthm setp-of-domain
  (set::setp (domain map))
  :hints(("Goal" :in-theory (enable domain))))

(defund erase (key map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     (emptymap))
                    ((atom (car map))
                     (erase key (cdr map)))
                    ((equal (caar map) key)
                     (erase key (cdr map)))
                    (t (cons (car map)
                             (erase key (cdr map)))))
       :exec (cond ((atom map)
                    nil)
                   ((equal (caar map) key)
                    (erase key (cdr map)))
                   (t (cons (car map)
                            (erase key (cdr map)))))))

(defthm mapp-of-erase
  (mapp (erase key map))
  :hints(("Goal" :in-theory (enable mapp erase))))

(defthm domain-of-erase
  (equal (domain (erase key map))
         (set::delete key (domain map)))
  :hints(("Goal" :in-theory (enable erase domain))))

(defthm acl2-count-of-erase-strong-linear
  (implies (in key map)
           (< (acl2-count (erase key map))
              (acl2-count map)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable erase domain)
          :induct (erase key map))))

(defthm acl2-count-of-erase-weak-linear
  (<= (acl2-count (erase key map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable erase)
          :induct (erase key map))))



(defund fix (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (fix (cdr map)))
                    (t (cons (car map)
                             (fix (cdr map)))))
       :exec map))

(defthm mapp-of-fix
  (mapp (fix map))
  :hints(("Goal" :in-theory (enable mapp fix))))

(defthm fix-when-mapp
  (implies (mapp map)
           (equal (fix map)
                  map))
  :hints(("Goal" :in-theory (enable mapp fix))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm domain-of-fix
         (equal (domain (fix map))
                (domain map))
         :hints(("Goal" :in-theory (enable domain fix)))))

(defthm acl2-count-of-fix-weak-linear
  (<= (acl2-count (fix map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable fix))))



(defund set (key val map)
  (declare (xargs :guard (mapp map)))
  (mbe :logic (acons key val (fix map))
       :exec (cons (cons key val) map)))

(defthm mapp-of-set
  (mapp (set key val map))
  :hints(("Goal" :in-theory (enable mapp set))))

(defthm domain-of-set
  (equal (domain (set key val map))
         (set::insert key (domain map)))
  :hints(("Goal" :in-theory (enable domain set))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm set-of-fix
         (equal (set key val (fix map))
                (set key val map))
         :hints(("Goal" :in-theory (enable set fix)))))


;; DAG The default thing was too strong.

(defund get (key map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     (emptymap))
                    ((atom (car map))
                     (get key (cdr map)))
                    ((equal (caar map) key)
                     (cdar map))
                    (t (get key (cdr map))))
       :exec (cond ((atom map)
                    (emptymap))
                   ((equal (caar map) key)
                    (cdar map))
                   (t (get key (cdr map))))))

(defthm get-when-not-in
  (implies (not (in key map))
           (equal (get key map)
                  (emptymap)))
  :hints(("Goal" :in-theory (enable domain get))))

;; We will soon prove a stronger congruence rule, so we don't need to export
;; this theorem.
(local (defthm get-of-fix
         (equal (get key (fix map))
                (get key map))
         :hints(("Goal" :in-theory (enable get fix)))))

(defthm get-of-set
  (equal (get key1 (set key2 val map))
         (if (equal key1 key2)
             val
           (get key1 map)))
  :hints(("Goal" :in-theory (enable get set))))

(defthm get-of-erase
  (equal (get key1 (erase key2 map))
         (if (equal key1 key2)
             (emptymap)
           (get key1 map)))
  :hints(("Goal" :in-theory (enable get erase))))

(defthm acl2-count-of-get-strong-linear
  (implies (in key map)
           (< (acl2-count (get key map))
              (acl2-count map)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable get domain))))



(defund optimize (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (optimize (cdr map)))
                    (t (cons (car map)
                             (optimize
                              (erase (caar map) (cdr map))))))
       :exec (cond ((atom map)
                     nil)
                    (t (cons (car map)
                             (optimize
                              (erase (caar map) (cdr map))))))))

(defthm acl2-count-of-optimize-weak-linear
  (<= (acl2-count (optimize map))
      (acl2-count map))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable optimize))))

;; We don't export this because our congruence rule for domain is better.
(local (defthm domain-of-optimize
         (equal (domain (optimize map))
                (domain map))
         :hints(("Goal" :in-theory (enable domain optimize)))))

;; We don't export this because our congruence rule for get is better.
(local (defthm get-of-optimize
         (equal (get key (optimize map))
                (get key map))
         :hints(("Goal" :in-theory (enable get optimize)))))

(defund empty-exec (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (empty map)
       :exec (null map)))

(defthm empty-exec-is-empty
  (equal (empty-exec map)
         (empty map))
  :hints(("Goal" :in-theory (enable empty-exec))))

(defund head (map)
  (declare (xargs :guard (mapp map)
                  :verify-guards nil))
  (mbe :logic (cond ((atom map)
                     nil)
                    ((atom (car map))
                     (head (cdr map)))
                    ((caar map)))
       :exec (caar map)))

(defthm in-head
  (equal (in (head map) map)
         (not (empty map)))
  :hints(("Goal" :in-theory (enable head domain))))

(defund submap (sub super)
  (declare (xargs :guard (and (mapp sub)
                              (mapp super))))
  (or (empty sub)
      (let ((head (head sub)))
        (and (in head super)
             (equal (get head sub)
                    (get head super))
             (submap (erase head sub) super)))))

(defthm in-when-in-submap
  (implies (and (submap sub super)
                (in key sub))
           (in key super))
  :hints(("Goal" :in-theory (enable submap))))

(defthm not-in-when-not-in-supermap
  (implies (and (submap sub super)
                (not (in key super)))
           (not (in key sub))))

(defthm subset-of-submap-domain-with-supermap-domain
  (implies (submap sub super)
           (set::subset (domain sub)
                         (domain super))))


(defthm equal-of-gets-when-submap
  (implies (submap sub super)
           (equal (equal (get key sub) (get key super))
                  (if (in key sub)
                      t
                    (equal (get key super) (emptymap)))))
  :hints(("Goal" :in-theory (enable submap))))

(defthm empty-when-submap-of-empty-map
  (implies (and (submap sub super)
                (empty super))
           (empty sub))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-of-anything-when-empty
  (implies (empty sub)
           (submap sub super))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-of-empty-means-empty
  (implies (empty super)
           (equal (submap sub super)
                  (empty sub)))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-reflexive
  (submap map map))

(defthm submap-transitive-one
  (implies (and (submap x y)
                (submap y z))
           (submap x z))
  :hints(("Goal" :in-theory (enable submap))))

(defthm submap-transitive-two
  (implies (and (submap x y)
                (submap y z))
           (submap x z)))

(defthm submap-of-erase-with-self
  (submap (erase key map) map))

(defthm submap-of-erase-with-erase-when-submap
  (implies (submap sub super)
           (submap (erase key sub)
                   (erase key super))))

(defthm submap-of-set-with-set-when-submap
  (implies (submap sub super)
           (submap (set key val sub)
                   (set key val super))))

(defund equiv (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (and (submap x y)
       (submap y x)))

(defthm fix-under-equiv
  (equiv (fix map)
         map)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm optimize-under-equiv
  (equiv (optimize map)
         map)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-with-empty-one
  (implies (empty x)
           (equal (equiv x y)
                  (empty y)))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-with-empty-two
  (implies (empty y)
           (equal (equiv x y)
                  (empty x)))
  :hints(("Goal" :in-theory (enable equiv))))

;; The following rule is necessarily weaker than its variant in misc/records,
;; because of the way that the map's domain has been separated from its range.

(defthm set-of-get-same
  (equiv (set key (get key map) map)
         (if (in key map)
             map
           (set key (emptymap) map)))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-when-not-in
  (implies (not (in key map))
           (equiv (erase key map)
                  map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-erase
  (equiv (erase key1 (erase key2 map))
         (erase key2 (erase key1 map)))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

;; We add the following rule to cancel out adjacent erases.  This maybe isn't
;; strictly necessary, because ACL2 can easily figure this out using rewriting,
;; but we add the rule anyway because it is potentially faster to have a simple
;; rule like this than to have to do all of the otherwise-necessary
;; backchaining.

(defthm erase-of-erase-same
  (equiv (erase key (erase key map))
         (erase key map)))

;; Simplifying Set-of-Set Nests
;;
;; I had hoped that we could use the same strategy to simplify set nests as we
;; could for erase nests, particular since we spent so long thinking about the
;; right way to simplify erase of erase.  But, "set"s can't just be arbitrarily
;; reordered like "erase"s, unless they are to different locations.
;;
;; I thought for awhile that maybe the best thing to do for set-of-set would
;; then be to just do the case split.  But, I found that this doesn't work.  In
;; particular, we need a loop stopper in order to prevent ourselves from going
;; into infinite loops on the not-equal case.  But then the rule won't fire on
;; the equal case either!
;;
;; So, here is what I am going to do.  I will just write two rules: a simple
;; (hypothesis free) rewrite to handle the "same" case, and a conditional
;; rewrite rule to handle the "different" case.  But, I'll add a "case-split"
;; to the set-of-set case, so that even if the hypothesis fails, we'll break
;; into cases.  This way, we have an the aggressive splitting strategy that
;; nonetheless still applies to "same" addresses.

(defthm set-of-set-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (set key1 val1 (set key2 val2 map))
                  (set key2 val2 (set key1 val1 map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-set-same
  (equiv (set key val1 (set key val2 map))
         (set key val1 map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-erase-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (set key1 val (erase key2 map))
                  (erase key2 (set key1 val map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm set-of-erase-same
  (equiv (set key val (erase key map))
         (set key val map))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-set-different
  (implies (case-split (not (equal key1 key2)))
           (equiv (erase key1 (set key2 val map))
                  (set key2 val (erase key1 map))))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 set))))
  :hints(("Goal" :in-theory (enable equiv))))

(defthm erase-of-set-same
  (equiv (erase key (set key val map))
         (erase key map))
  :hints(("Goal" :in-theory (enable equiv))))

;; DAG theorems

(defthm map-erase-set
  (equal (map::erase key (map::set key v r))
         (map::erase key r))
  :hints (("goal" :in-theory (enable map::fix map::set map::erase))))

(defthm head-of-set
  (equal (map::head (map::set k v r))
         k)
  :hints (("goal" :in-theory (enable map::fix map::set map::head))))

(defthm tail-of-set
  (equal (map::tail (map::set k v r))
         (erase k (map::fix r)))
  :hints (("goal" :in-theory (enable map::fix map::set map::head map::erase))))
