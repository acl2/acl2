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


#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; paths-definitions.lisp
;; John D. Powell
;(in-package "PATHS")

(error "Is anyone using this?  If so please remove this error.")

;;
;; This file isolates paths definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the paths book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(local (in-theory (enable set::weak-insert-induction-helper-1)))
(local (in-theory (enable set::weak-insert-induction-helper-2)))
(local (in-theory (enable set::weak-insert-induction-helper-3)))

(defun cp-set (set st1 st2)
  "Set the value in ST2 of each path P in SET to the value of P in ST1"
  (if (set::empty set) st2
    (let ((p (set::head set)))
      (sp p (gp p st1)
          (cp-set (set::tail set) st1 st2)))))

(defthmd sp-gp-differential
  (equal (equal r1 r2)
         (and (equal (gp path r1) (gp path r2))
              (equal (clrp path r1)
                     (clrp path r2))))
  :hints (("Goal" :use (:instance sp-equal-rewrite-2
                                  (r r1)
                                  (v (gp path r1))))))

(local
 (defthm clrp-reduction
   (implies
    (equal (gp p st1)
           (gp p st2))
    (iff (equal (clrp p st1)
                (clrp p st2))
         (equal st1 st2)))
   :hints (("goal" :use (:instance sp-gp-differential
                                   (r1 st1)
                                   (r2 st2)
                                   (path p))))))

(defthm in-implies-gp-of-cp-set
  (implies
   (set::in path set)
   (equal (gp path (cp-set set st1 x))
          (gp path st1)))
  :hints (("goal" :in-theory (enable GP-OF-GP gp-of-sp))))

(local
 (defthm gp-domination-implies-equality
   (IMPLIES (AND (EQUAL (GP P1 ST1)
                        (GP P1 ST2))
                 (DOMINATES P1 P2))
            (iff (EQUAL (GP P2 ST1)
                        (GP P2 ST2))
                 t))
   :hints (("goal" :in-theory (enable gp dominates))))
 )

(local
 (defthm open-nthcdr
   (implies
    (not (zp n))
    (equal (nthcdr n list)
           (nthcdr (1- n) (cdr list)))))
 )

(local
 (defthm gp-dominates-implies-equality-2
   (implies
    (AND (EQUAL (GP PATH ST1)
                (GP PATH ST2))
         (DOMINATES P2 PATH)
         (EQUAL (CLRP (NTHCDR (LEN P2) PATH)
                      (GP P2 ST1))
                (CLRP (NTHCDR (LEN P2) PATH)
                      (GP P2 ST2))))
    (iff (EQUAL (GP P2 ST1)
               (GP P2 ST2)) t))
   :hints (("goal" :in-theory (enable gp dominates nthcdr))))
 )

(local
 (defthm gp-path-equality-implies-gp-path-cp-set-equality
   (implies
    (equal (gp path st1)
           (gp path st2))
    (iff (equal (gp path (cp-set set st1 x))
                (gp path (cp-set set st2 x))) t))
   :hints (("goal" :in-theory (enable gp-of-gp gp-of-sp))))
 )

(local
 (defthm clrp-cp-set-reduction
   (implies
    (equal (gp path st1)
           (gp path st2))
    (iff (equal (clrp path (cp-set set st1 x))
                (clrp path (cp-set set st2 x)))
         (equal (cp-set set st1 x)
                (cp-set set st2 x))))
   :hints (("goal" :in-theory (e/d (clrp-of-sp
                                    sp-equal-rewrite-2)
                                   (sp==r)))
           (and acl2::stable-under-simplificationp
                '(:in-theory (e/d (clrp-of-sp
                                   diverge
                                   sp-equal-rewrite-2)
                                  (sp==r))))))
 )

(defthmd equal-cp-set-reduction-reduction-helper
  (implies
   (set::in p set)
   (iff (equal (cp-set set st1 x)
               (cp-set set st2 x))
        (and (equal (gp p st1)
                    (gp p st2))
             (equal (cp-set set st1 x)
                    (cp-set set st2 x)))))
  :hints (("goal" :in-theory (e/d (sp-equal-rewrite-2)
                                  (sp==r)))))

(defthmd open-cp-set
  (implies
   (not (set::empty set))
   (equal (cp-set set st1 st2)
          (LET ((P (SET::HEAD SET)))
               (SP P (GP P ST1)
                   (CP-SET (SET::TAIL SET) ST1 ST2))))))

(local
 (defthm cp-set-and-gp-equal-implies-cp-set-insert-equal
   (implies
    (and
     (equal (cp-set set st1 x)
            (cp-set set st2 x))
     (equal (gp p st1)
            (gp p st2)))
    (iff (equal (cp-set (set::insert p set) st1 x)
                (cp-set (set::insert p set) st2 x)) t))
   :hints (("goal" :in-theory (e/d (open-cp-set sp-equal-rewrite-2)
                                   (sp==r)))))
 )

(defun cp-set-equal (set st1 st2)
  (if (set::empty set) t
    (and (equal (gp (set::head set) st1)
                (gp (set::head set) st2))
         (cp-set-equal (set::tail set) st1 st2))))

(defthmd equal-cp-set-to-cp-set-equal
  (iff (equal (cp-set set st1 x)
              (cp-set set st2 x))
       (cp-set-equal set st1 st2))
  :hints (("goal" :in-theory (e/d (open-cp-set sp-equal-rewrite-2)
                                  (sp==r)))))

(defthm equal-gp-from-cp-set-equal-membership
  (implies
   (and
    (set::in a set)
    (cp-set-equal set st1 st2))
   (iff (equal (gp a st1)
               (gp a st2)) t))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :corollary
                  (implies
                   (and
                    (set::in a set)
                    (cp-set-equal set st1 st2))
                   (equal (gp a st1) (gp a st2))))))

(defthm cp-set-equal-from-subset
  (implies
   (and
    (cp-set-equal set2 st1 st2)
    (set::subset set1 set2))
   (cp-set-equal set1 st1 st2)))

(local
 (defthm cp-set-insert-equal-implies-cp-set-equal
   (implies
    (equal (cp-set (set::insert a set) st1 x)
           (cp-set (set::insert a set) st2 x))
    (iff (equal (cp-set set st1 x)
                (cp-set set st2 x)) t))
   :hints (("goal" :in-theory (enable equal-cp-set-to-cp-set-equal))))
 )

;; There is a similar theorem for set::union

(defthm equal-cp-set-insert-reduction
  (iff (equal (cp-set (set::insert p set) st1 x)
              (cp-set (set::insert p set) st2 x))
       (and (equal (gp p st1)
                   (gp p st2))
            (equal (cp-set set st1 x)
                   (cp-set set st2 x))))
  :hints (("goal"
           :in-theory nil
           :use (:instance equal-cp-set-reduction-reduction-helper
                           (set (set::insert p set))))
          ("goal'" :cases ((not (set::in p set)))
           :in-theory (current-theory :here))))

(defthm cp-set-equal-insert-reduction
  (iff (cp-set-equal (set::insert p set) st1 st2)
       (and (equal (gp p st1) (gp p st2))
            (cp-set-equal set st1 st2)))
  :hints (("goal" :use (:instance equal-cp-set-insert-reduction)
           :in-theory '(equal-cp-set-to-cp-set-equal))))

(defthm cp-set-equal-union-reduction
  (iff (cp-set-equal (set::union s1 s2) st1 st2)
       (and (cp-set-equal s1 st1 st2)
            (cp-set-equal s2 st1 st2))))

(defthm equal-cp-set-union-reduction
  (iff (equal (cp-set (set::union s1 s2) st1 x)
              (cp-set (set::union s1 s2) st2 x))
       (and (equal (cp-set s1 st1 x)
                   (cp-set s1 st2 x))
            (equal (cp-set s2 st1 x)
                   (cp-set s2 st2 x))))
  :hints (("goal" :use (:instance cp-set-equal-union-reduction)
           :in-theory '(equal-cp-set-to-cp-set-equal))))

;;
;; clrp is another important "function" ..
;;

(defthmd cp-set-equal-to-equal-cp-set
  (iff (cp-set-equal set st1 st2)
       (equal (cp-set set st1 nil)
              (cp-set set st2 nil)))
  :hints (("goal" :in-theory (enable EQUAL-CP-SET-TO-CP-SET-EQUAL))))

(defthm gp-of-gp-domination
  (implies
   (dominates a y)
   (equal (gp (nthcdr (len a) y) (gp a x))
          (gp y x)))
  :hints (("goal" :in-theory (enable gp-of-gp))))

(defthm outer-domination
  (equal (sp a v (cp-set set (sp a v x1) x2))
         (sp a v (cp-set set x1 x2)))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (CLRP-COMMUTE-2
                            ;;gp-of-gp
                            gp-of-sp
                            clrp-of-sp
                            sp-equal-rewrite-2)
                           (CLRP-OF-CLRP
                            sp==r)))))

(defthm cp-set-over-sp
  (implies
   (equal v (gp a st1))
   (equal (cp-set set st1 (sp a v st2))
          (sp a v (cp-set set st1 st2))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (CLRP-COMMUTE-2
                            ;;gp-of-gp
                            gp-of-sp
                            clrp-of-sp
                            sp-equal-rewrite-2)
                           (CLRP-OF-CLRP
                            sp==r)))))

(defthm cp-set-cp-set
  (equal (cp-set set (cp-set set st1 st2) st3)
         (cp-set set st1 st3))
  :hints (("goal" :in-theory (disable SP==R))))



(defun clrp-set (set st)
  (if (set::empty set) st
    (clrp-set (set::tail set) (clrp (set::head set) st))))

(defthm open-clrp-set-on-constants
  (implies (syntaxp (quotep set))
           (equal (clrp-set set st)
                  (if (set::empty set)
                      st
                    (clrp-set (set::tail set)
                              (clrp (set::head set) st)))))
  :hints (("Goal" :in-theory (enable clrp-set))))

(defun clrp-set-induction (set r1 r2)
  (if (set::empty set) (cons r1 r2)
    (clrp-set-induction (set::tail set)
                        (clrp (set::head set) r1)
                        (clrp (set::head set) r2))))

(defthm cp-set-equal-identity
  (cp-set-equal set x x))

(defthm cp-set-equal-dominance
  (implies
   (cp-set-equal set x y)
   (cp-set-equal set (clrp a x) (clrp a y))))

(defthmd record-equal-to-gp-set-equal-helper
  (iff (equal r1 r2)
       (and (cp-set-equal set r1 r2)
            (equal (clrp-set set r1)
                   (clrp-set set r2))))
  :hints (("goal" :induct (clrp-set-induction set r1 r2))))

(defthmd record-equal-to-gp-set-equal
  (iff (equal r1 r2)
       (and (equal (gp-set set r1)
                   (gp-set set r2))
            (equal (clrp-set set r1)
                   (clrp-set set r2))))
  :hints (("goal" :use (:instance record-equal-to-gp-set-equal-helper)
           :in-theory (enable cp-set-equal-to-equal-cp-set))))

;;
;; In support of incremental-cp-set-equality-reduction
;;

(defthmd open-cp-set-equal
  (implies
   (not (set::empty set))
   (equal (cp-set-equal set st1 st2)
          (AND (EQUAL (GP (SET::HEAD SET) ST1)
                      (GP (SET::HEAD SET) ST2))
               (CP-SET-EQUAL (SET::TAIL SET)
                             ST1 ST2)))))

(defun keep-exposed-elements (a x)
  (if (set::empty x) (set::emptyset)
    (let ((head (set::head x)))
      (if (dominates a head)
          (set::insert (list::fix (nthcdr (len a) head))
                       (keep-exposed-elements a (set::tail x)))
        (if (dominates head a)
            (set::insert nil
                         (keep-exposed-elements a (set::tail x)))
          (keep-exposed-elements a (set::tail x)))))))

(defthmd incremental-cp-set-equality-reduction-helper-1
  (implies
   (and
    (cp-set-equal (keep-exposed-elements a x) v1 v2)
    (equal (gp a xx1) (gp a xx2)))
   (equal (cp-set-equal x (sp a v1 xx1) (sp a v2 xx2))
          (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (diverge open-clrp-list open-cp-set-equal gp-of-sp)
                                  (acl2::equal-booleans-reducton)))))

(defthm multicons-over-insert
  (equal (set::multicons a (set::insert x list))
         (set::insert (cons a x) (set::multicons a list))))

(defthm multicons-empty
  (implies
   (set::empty x)
   (equal (set::multicons a x) nil))
  :hints (("goal" :expand (set::multicons a x))))

(defthm multiappend-empty
  (implies
   (set::empty x)
   (equal (set::multiappend a x) nil))
  :hints (("goal" :in-theory (enable set::multiappend))))

(defthm open-multiappend-on-insert
  (equal (set::multiappend a (set::insert x list))
         (set::insert (append a x)
                      (set::multiappend a list)))
  :hints (("goal" :induct (set::multiappend a list)
           :in-theory (e/d (append set::multiappend)
                            (SET::DOUBLE-CONTAINMENT)))))

(defthmd cp-set-equal-mapappend-reduction
  (equal (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) s1 s2)
         (cp-set-equal (keep-exposed-elements a x) (gp a s1) (gp a s2)))
  :hints (("goal" :in-theory (enable set::multiappend))))

(defthmd incremental-cp-set-equality-reduction-helper-2
  (implies
   (and
    (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) st1 st2)
    (equal (gp a xx1)
           (gp a xx2)))
   (equal (cp-set-equal x
                        (sp a (gp a st1) xx1)
                        (sp a (gp a st2) xx2))
          (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (cp-set-equal-mapappend-reduction
                                   incremental-cp-set-equality-reduction-helper-1)
                                  (cp-set-equal)))))

(defthm cp-set-equal-implies-cp-set-equal-keep-exposed
  (implies
   (cp-set-equal x s1 s2)
   (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) s1 s2)))

(defthmd incremental-cp-set-equality-reduction-helper-3
  (implies
   (and
    (cp-set-equal x st1 st2)
    (equal (gp a xx1)
           (gp a xx2)))
   (equal (cp-set-equal x
                        (sp a (gp a st1) xx1)
                        (sp a (gp a st2) xx2))
          (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (incremental-cp-set-equality-reduction-helper-2)
                                  (cp-set-equal)))))

(defthm incremental-cp-set-equality-reduction
  (implies
   (and
    (equal (cp-set x st1 nil)
           (cp-set x st2 nil))
    (equal (gp a xx1)
           (gp a xx2)))
   (iff (equal (cp-set x (sp a (gp a st1) xx1) nil)
               (cp-set x (sp a (gp a st2) xx2) nil))
        (equal (cp-set x xx1 nil)
               (cp-set x xx2 nil))))
  :hints (("goal" :in-theory `(equal-cp-set-to-cp-set-equal
                               incremental-cp-set-equality-reduction-helper-3))))

(defthmd cp-set-extensionality
  (implies
   (and
    (equal (cp-set x1 st1 nil)
           (cp-set x2 st2 nil))
    (equal x1 a1)
    (equal x2 a2))
   (iff (equal (cp-set a1 st1 nil)
               (cp-set a2 st2 nil)) t)))

;;
;; some additional clrp reasoning
;;

(defun clrp-set-equal (set x y)
  (if (set::empty set) (equal x y)
    (clrp-set-equal (set::tail set)
                    (cpath::clrp (set::head set) x)
                    (cpath::clrp (set::head set) y))))

(defthm clrp-set-equal-of-clrp
  (implies
   (set::in a set)
   (equal (clrp-set-equal set (cpath::clrp a x) (cpath::clrp a y))
          (clrp-set-equal set x y))))

(defthmd clrp-set-equal-implies-1
  (implies
   (clrp-set-equal set x y)
   (equal (cpath::clrp-set set x)
          (cpath::clrp-set set y)))
  :hints (("goal" :in-theory (enable cpath::clrp-set))))

(defthmd clrp-set-equal-implies-2
  (implies
   (not (clrp-set-equal set x y))
   (not (equal (cpath::clrp-set set x)
               (cpath::clrp-set set y))))
  :hints (("goal" :in-theory (enable cpath::clrp-set))))

(defthmd equal-clrp-set-to-clrp-set-equal
  (iff (equal (cpath::clrp-set set x)
              (cpath::clrp-set set y))
       (clrp-set-equal set x y))
  :hints (("Goal" :in-theory (enable
                              clrp-set-equal-implies-1
                              clrp-set-equal-implies-2
                              ))))

(defthm clrp-set-equal-chaining
  (implies
   (and
    (set::subset set1 set2)
    (clrp-set-equal set1 x y))
   (clrp-set-equal set2 x y))
  :hints (("Goal" :in-theory (enable set::subset))))

(defthm clrp-set-chaining
  (implies
   (and
    (set::subset set1 set2)
    (equal (cpath::clrp-set set1 x)
           (cpath::clrp-set set1 y)))
   (iff (equal (cpath::clrp-set set2 x)
               (cpath::clrp-set set2 y)) t))
  :hints (("goal" :in-theory (enable equal-clrp-set-to-clrp-set-equal))))

(defund dominates (x y)
  (declare (type t x y))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (dominates (cdr x) (cdr y)))
    t))

(defund strictly-dominates (x y)
  (declare (type t x y))
  (and (dominates x y)
       (not (list::equiv x y))))

(defund dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates a (car x))
          (dominates-some a (cdr x)))
    nil))

(defund strictly-dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates a (car x))
          (strictly-dominates-some a (cdr x)))
    nil))

(defund dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates (car x) a)
          (dominated-by-some a (cdr x)))
    nil))

(defund strictly-dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates (car x) a)
          (strictly-dominated-by-some a (cdr x)))
    nil))

(defund first-dominator (a x)
  (declare (type t a x))
  (if (atom x)
      nil
    (if (dominates (car x) a)
        (car x)
      (first-dominator a (cdr x)))))

(defund diverge (x y)
  (declare (type t x y))
  (and (not (dominates x y))
       (not (dominates y x))))

(defund diverges-from-all (a x)
  (declare (type t a x))
  (if (consp x)
      (and (diverge a (car x))
           (diverges-from-all a (cdr x)))
    t))

(defund all-diverge-from-all (x y)
  (declare (type t x y))
  (if (consp x)
      (and (diverges-from-all (car x) y)
           (all-diverge-from-all (cdr x) y))
    t))

(defund all-diverge (x)
  (declare (type t x))
  (if (consp x)
      (and (diverges-from-all (car x) (cdr x))
           (all-diverge (cdr x)))
    t))

;; bzo (jcd) - Diverge is symmetric; should we prove each rule for both of the
;; symmetric cases?  Right now I am doing this, but perhaps it is redundant and
;; therefore bad to do this.  Maybe we should have OR's of each case in our
;; hypotheses instead?

(defund diverge (x y)
  (declare (type t x y))
  (and (not (dominates x y))
       (not (dominates y x))))

(defthm not-diverge-forward-to-dominates-cases
  (implies (not (diverge x y))
           (or (dominates x y)
               (dominates y x)))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverge))))


;; bzo (jcd) - I'm not sure why we have the above rule but not other forward
;; chaining rules.  For example, perhaps we want a rule that says if they do
;; diverge, then neither dominates.  And, if one dominates, then they do not
;; diverge.  I have added the following three forward chaining rules to go
;; along with this idea.  I'm not sure if this will break anything.

(defthm diverge-forward-to-non-domination
  (implies (diverge x y)
           (and (not (dominates x y))
                (not (dominates y x))))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverge))))

(defthm dominates-forward-to-non-divergence
  (implies (dominates x y)
           (and (not (diverge x y))
                (not (diverge y x))))
  :rule-classes :forward-chaining)

(defthm not-dominates-forward-to-diverge-cases
  (implies (not (dominates x y))
           (or (dominates y x)
               (diverge x y)))
  :rule-classes :forward-chaining)



(defthm diverge-type-1
  (implies (not (consp x))
           (equal (diverge x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-type-2
  (implies (not (consp y))
           (equal (diverge x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-of-non-consp-one
  (implies (not (consp x))
           (equal (diverge x y)
                  nil)))

(defthm diverge-of-non-consp-two
  (implies (not (consp y))
           (equal (diverge x y)
                  nil)))

(defthm diverge-irreflexive
  (not (diverge x x))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-symmetric
  (equal (diverge x y)
         (diverge y x))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-commute-fwd
  (implies
   (diverge x y)
   (diverge y x))
  :rule-classes (:forward-chaining))

(defthm not-diverge-commute-fwd
  (implies
   (not (diverge x y))
   (not (diverge y x)))
  :rule-classes (:forward-chaining))

(defthm diverge-of-cons-one
  (equal (diverge (cons a x) y)
         (and (consp y)
              (or (not (equal a (car y)))
                  (diverge x (cdr y)))))
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-of-cons-two
  (equal (diverge x (cons a y))
         (and (consp x)
              (or (not (equal a (car x)))
                  (diverge y (cdr x))))))

(defthm diverge-of-append-self-one
  (equal (diverge (append x y) x)
         nil)
  :hints (("Goal" :in-theory (enable append))))

(defthm diverge-of-append-self-two
  (equal (diverge x (append x y))
         nil)
  :hints (("Goal" :in-theory (enable append))))

;; bzo (jcd) - Originally we had all of the following rules to allow ourselves
;; to backchain between diverge and dominates.  I have dropped all of these in
;; favor of the extra forward chaining rules above, but this may break things.

;; (defthm not-diverge-when-dominates-one
;;   (implies (dominates x y)
;;            (not (diverge x y)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; (defthm not-diverge-when-dominates-two
;;   (implies (dominates y x)
;;            (not (diverge x y)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; (defthm not-dominates-when-diverge-one
;;   (implies (diverge x y)
;;            (not (dominates x y))))

;; (defthm not-dominates-when-diverge-two
;;   (implies (diverge x y)
;;            (not (dominates y x))))

(defthm two-dominators-cannot-diverge
  (implies (and (dominates x z)
                (dominates y z))
           (not (diverge x y)))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-one
  (implies (and (diverge x z)
                (dominates z y))
           (diverge x y))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-one-alt
  (implies (and (dominates z y)
                (diverge x z))
           (diverge x y)))

(defthm diverge-when-diverge-with-dominator-two
  (implies (and (diverge y z)
                (dominates z x))
           (diverge x y))
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-two-alt
  (implies (and (dominates z x)
                (diverge y z))
           (diverge x y)))


;; jcd - the following theorem was actually provided as a really bizarre fact
;; about all-diverge.  Changing it to be a property about diverge itself seems
;; to be a much better approach:

(defthm diverge-implies-unequal-extensions
  (implies (diverge x y)
           (equal (equal (append x a)
                         (append y b))
                  nil))
  :hints(("Goal" :in-theory (enable diverge
                                    dominates
                                    ))))

(defund diverges-from-all (a x)
  (declare (type t a x))
  (if (consp x)
      (and (diverge a (car x))
           (diverges-from-all a (cdr x)))
    t))

(defthmd diverges-from-all-redefinition
  (equal (diverges-from-all p paths)
         (and (not (dominated-by-some p paths))
              (not (dominates-some p paths))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable diverges-from-all))))

(defthm diverges-from-all-type-1
  (implies (not (consp x))
           (equal (diverges-from-all a x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-type-2
  (implies (and (consp x)
                (not (consp a)))
           (equal (diverges-from-all a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-of-non-consp-one
  (implies (not (consp a))
           (equal (diverges-from-all a x)
                  (not (consp x)))))

(defthm diverges-from-all-of-non-consp-two
  (implies (not (consp x))
           (diverges-from-all a x)))

(defthm diverges-from-all-of-cons
  (equal (diverges-from-all a (cons b x))
         (and (diverge a b)
              (diverges-from-all a x)))
  :hints (("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-of-cdr
  (implies (diverges-from-all a x)
           (diverges-from-all a (cdr x))))

(defthm diverges-of-cdr-by-diverges-from-all
  (implies (diverges-from-all a x)
           (equal (diverge a (car x))
                  (consp x))))

(defthm diverges-from-all-of-append
  (equal (diverges-from-all a (append x y))
         (and (diverges-from-all a x)
              (diverges-from-all a y)))
  :hints (("Goal" :in-theory (enable append))))

;; To effectively reason about diverge-from-all through membership, we need to
;; know that whenever (memberp a x) and (diverges-from-all b x), then
;; (diverge a b) and also (diverge b a).  To cover the free variable matching
;; alternatives, there are actually four different versions of these theorems
;; (Note that x is a free variable in all of these rules.)

(defthm diverge-when-memberp-and-diverges-from-all-one
  (implies (and (memberp a x)
                (diverges-from-all b x))
           (diverge a b))
  :hints (("Goal" :in-theory( enable diverges-from-all-redefinition))))

(defthm diverge-when-memberp-and-diverges-from-all-two
  (implies (and (diverges-from-all b x)
                (memberp a x))
           (diverge a b)))

(defthm diverge-when-memberp-and-diverges-from-all-three
  (implies (and (memberp b x)
                (diverges-from-all a x))
           (diverge a b))
  :hints (("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverge-when-memberp-and-diverges-from-all-four
   (implies (and (diverges-from-all a x)
                 (memberp b x))
            (diverge a b)))

(defthm diverges-from-all-forward-to-diverge
  (implies (and (diverges-from-all a x)
                (memberp b x))
           (and (diverge a b)
                (diverge b a)))
  :rule-classes :forward-chaining)




;; We now use our membership strategy to prove divergence from all of subbags.
;; Again because of free variable matching, there are two versions of this rule
;; (Note that y is a free variable.)

(defthm diverges-from-all-by-subbagp-one
  (implies (and (diverges-from-all a y)
                (bag::subbagp x y))
           (diverges-from-all a x)))

(defthm diverges-from-all-by-subbagp-two
  (implies (and (bag::subbagp x y)
                (diverges-from-all a y))
           (diverges-from-all a x)))



;; There are probably other nice facts we could prove about diverges-from-all
;; especially as it relates to the list and bag functions.  For now we will
;; just prove these:

(defthm diverges-from-all-of-nthcdr
  (implies (diverges-from-all a x)
           (diverges-from-all a (nthcdr n x))))

(defthm diverges-from-all-of-firstn
  (implies (diverges-from-all a x)
           (diverges-from-all a (firstn n x))))

(defthm diverges-from-all-of-remove-1
  (implies (diverges-from-all a x)
           (diverges-from-all a (bag::remove-1 b x))))

(defthm diverges-from-all-of-remove-all
  (implies (diverges-from-all a x)
           (diverges-from-all a (bag::remove-all b x))))

(defthm diverges-from-all-when-dominated
  (implies (and (dominates a b) ; a is a free var
                (diverges-from-all a x))
           (diverges-from-all b x)))



;; Forward chaining to dominated-by-some and dominates-some

(defthm diverge-from-all-forward
  (implies (diverges-from-all a x)
           (and (not (dominated-by-some a x))
                (not (dominates-some a x))))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-when-no-domination
  (implies (and (not (dominated-by-some a x))
                (not (dominates-some a x)))
           (diverges-from-all a x))
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

;; (defthm not-dominated-by-some-when-diverges-from-all
;;   (implies (diverges-from-all p paths)
;;            (not (dominated-by-some p paths)))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; ;bzo drop? other rules handle this?
;; (defthm not-dominated-by-some
;;   (implies (and (diverges-from-all a x) ; a is a free variable
;;                 (dominates b a))
;;            (not (dominated-by-some b x))))

;; (defthm not-strictly-dominated-by-some-when-diverges-from-all
;;   (implies (diverges-from-all p paths)
;;            (not (strictly-dominated-by-some p paths))))

;; (defthm diverges-from-when-not-strictly-dominated-by-some-and-not-dominates-some
;;   (implies (and (not (strictly-dominated-by-some p paths))
;;                 (not (dominates-some p paths)))
;;            (diverges-from-all p paths)))

;; (defthm diverges-from-all-when-no-domination-alt
;;   (implies (and (not (strictly-dominated-by-some p paths))
;;                 (not (dominates-some p paths)))
;;            (diverges-from-all p paths)))

;; ----------------------------------------------------------------------------
;;
;;                                   PART 3
;;
;;                     The All-Diverge-From-All Relation
;;
;; ----------------------------------------------------------------------------

;; Given x and y, both list of lists, we say that (all-diverge-from-all x y)
;; whenever every path a in x and every path b in y satisfy (diverge x y).

(defund all-diverge-from-all (x y)
  (declare (type t x y))
  (if (consp x)
      (and (diverges-from-all (car x) y)
           (all-diverge-from-all (cdr x) y))
    t))


;; To get any use out of the strategy, we have to be able to reason about
;; membership in all-diverge-from-all.  The following are crucial lemmas that
;; show how arbitrary members diverge when x and y satisfy
;; all-diverge-from-all.

(defthm diverge-when-members-of-all-diverge-from-all-one
  (implies (and (all-diverge-from-all x y) ;; x and y are free
                (memberp a x)
                (memberp b y))
           (diverge a b))
  :hints(("Goal" :in-theory (enable all-diverge-from-all))))

(defthm diverge-when-members-of-all-diverge-from-all-two
  (implies (and (all-diverge-from-all x y) ;; x and y are free
                (memberp a x)
                (memberp b y))
           (diverge b a)))



;; Here are some mundane theorems about all-diverge-from-all.  We could prove
;; these with the definition of all-diverge-from-all, but we prefer to try out
;; our membership strategy some more.

(defthm all-diverge-from-all-type-1
  (implies (not (consp x))
           (equal (all-diverge-from-all x y) t))
  :rule-classes :type-prescription)

(defthm all-diverge-from-all-type-2
  (implies (not (consp y))
           (equal (all-diverge-from-all x y) t))
  :rule-classes :type-prescription)

(defthm all-diverge-from-all-of-non-consp-one
  (implies (not (consp x))
           (all-diverge-from-all x y)))

(defthm all-diverge-from-all-of-non-consp-two
  (implies (not (consp y))
           (all-diverge-from-all x y)))



;; We'll now show that all-diverge-from-all is commutative.  This is a pretty
;; straightforward membership argument now.  I've left the original proofs in
;; comments below so that you can see the improvement:
;;
;; ;bzo generalize the car to any memberp?
;; (defthm not-all-diverge-from-all-when-not-diverges-from-all-of-car
;;   (implies (not (diverges-from-all (car paths1) paths2))
;;            (equal (all-diverge-from-all paths1 paths2)
;;                   (not (consp paths1))))
;;   :hints (("Goal" :in-theory (enable all-diverge-from-all))))
;;
;; (defthm all-diverge-from-all-alternate-definition
;;   (implies (consp paths2) ;this hyp helps prevent this rule from looping
;;            (equal (all-diverge-from-all paths1 paths2)
;;                   (and (all-diverge-from-all paths1 (cdr paths2))
;;                        (diverges-from-all (car paths2) paths1))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ( (ALL-DIVERGE-FROM-ALL PATHS2 PATHS1))
;;            :in-theory (enable all-diverge-from-all))) )
;;
;; (defthm all-diverge-from-all-commutative
;;   (equal (all-diverge-from-all paths1 paths2)
;;          (all-diverge-from-all paths2 paths1))
;;   :otf-flg t
;;   :hints (("Goal" :expand ( (ALL-DIVERGE-FROM-ALL PATHS2 PATHS1))
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable all-diverge-from-all))) )

;; I noticed that the original proof of symmetry had a nice lemma about car,
;; and a note that it could be generalized.  I've generalized it here to any
;; arbitrary member, and proven the symmetric version as well.

(defthm all-diverge-from-all-when-bad-member-one
  (implies (and (not (diverges-from-all a y))
                (memberp a x))
           (equal (all-diverge-from-all x y)
                  (not (consp y))))
   :hints (("Goal" :in-theory (enable all-diverge-from-all))))

(defthm all-diverge-from-all-when-bad-member-two
  (implies (and (not (diverges-from-all a x))
                (memberp a y))
           (equal (all-diverge-from-all x y)
                  (not (consp x))))
  :hints(("Goal"
          :in-theory (disable all-diverge-from-all-symmetric)
          :use (:instance all-diverge-from-all-symmetric
                          (x y) (y x)))))


;; We can prove some nice rewrites about how all-diverge-from-all distributes
;; over cons.  We'll do both symmetric cases below.  These are easier to prove
;; from the definition and symmetry than by membership.

(defthm all-diverge-from-all-of-cons-one
  (equal (all-diverge-from-all (cons a x) y)
         (and (diverges-from-all a y)
              (all-diverge-from-all x y)))
  :hints(("Goal"
          :use (:instance all-diverge-from-all
                          (x (cons a x))
                          (y y)))))

(defthm all-diverge-from-all-of-cons-two
  (equal (all-diverge-from-all x (cons a y))
         (and (diverges-from-all a x)
              (all-diverge-from-all x y)))
  :hints(("Goal"
          :in-theory (disable all-diverge-from-all-symmetric)
          :use ((:instance all-diverge-from-all-symmetric
                           (x (cons a y)) (y x))
                (:instance all-diverge-from-all-symmetric
                           (x y) (y x))))))



;; Here are several easy membership-based proofs of some basic properties of
;; all-diverge-from-all.

(defthm all-diverge-from-all-of-cdr-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (cdr x) y)))

(defthm all-diverge-from-all-of-cdr-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (cdr y))))

(defthm all-diverge-from-all-of-firstn-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (firstn n x) y)))

(defthm all-diverge-from-all-of-firstn-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (firstn n y))))

(defthm all-diverge-from-all-of-nthcdr-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (nthcdr n x) y)))

(defthm all-diverge-from-all-of-nthcdr-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (nthcdr n y))))

(defthm all-diverge-from-all-of-remove-1-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (bag::remove-1 a x) y)))

(defthm all-diverge-from-all-of-remove-1-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (bag::remove-1 a y))))

(defthm all-diverge-from-all-of-remove-all-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (bag::remove-all a x) y)))

(defthm all-diverge-from-all-of-remove-all-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (bag::remove-all a y))))

(defthm all-diverge-from-all-when-subbag-one
  (implies (and (all-diverge-from-all y z) ;; y is a free variable
                (bag::subbagp x y))
           (all-diverge-from-all x z)))

(defthm all-diverge-from-all-when-subbag-two
  (implies (and (all-diverge-from-all y z) ;; z is a free variable
                (bag::subbagp x z))
           (all-diverge-from-all y x)))

;; ----------------------------------------------------------------------------
;;
;;                                   PART 3
;;
;;                           The All-Diverge Relation
;;
;; ----------------------------------------------------------------------------

;; Given x, a list of lists, we say that (all-diverge x) if and only if every
;; member of x diverges from every other member in x.

(defund all-diverge (x)
  (declare (type t x))
  (if (consp x)
      (and (diverges-from-all (car x) (cdr x))
           (all-diverge (cdr x)))
    t))

(defthm all-diverge-type-1
  (implies (not (consp x))
           (equal (all-diverge x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable all-diverge))))

(defthm all-diverge-of-non-consp
  (implies (not (consp x))
           (equal (all-diverge x) t)))

(defthm all-diverge-of-cons
  (equal (all-diverge (cons a x))
         (and (diverges-from-all a x)
              (all-diverge x)))
  :hints(("Goal" :in-theory (enable all-diverge))))

 ;; These hints look a little extreme.  Basically the proof is the following:
 ;; By our constraints, we can assume that (all-diverge-term) satisfies both
 ;; bag::unique and our property that any two members which are not equal must
 ;; diverge.  Suppose towards contradiction that this list does not satisfy
 ;; (all-diverge (all-diverge-term)).
 ;;
 ;; Let (all-diverge-term) be "x".  Since x does not satisfy all-diverge, by
 ;; the theorem adfa-badguy-works, we know that (adfa-badguy x) is a member of
 ;; x.  Call this member "a".  By the same theorem, we also know that the
 ;; following is true: (not (diverges-from-all a (bag::remove-1 a x))).
 ;;
 ;; Since (not (diverges-from-all a (bag::remove-1 a x))), we know by the
 ;; theorem dfa-badguy-works that (dfa-badguy a (bag::remove-1 a x)) is a
 ;; member of (bag::remove-1 a x).  Call this member "b".  From the same
 ;; theorem, we also know that the following is true: (not (diverge a b)).
 ;;
 ;; Finally, note that since we have assumed (bag::unique x) and we know that
 ;; (memberp b (bag::remove-1 a x)), it must be the case that a != b and also
 ;; we know that b is a member of x.
 ;;
 ;; Well now, we are set up to show our contradiction.  We know that a and
 ;; b are both members of x, they are not equal, and they do not diverge.  But
 ;; this is a direct violation of our second constraint!  QED.

 (defthm all-diverge-by-membership-driver
   (implies (all-diverge-hyps)
            (all-diverge (all-diverge-term)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance all-diverge-constraint-unique)
                 (:instance all-diverge-constraint-membership
                            (all-diverge-member-a
                             (adfa-badguy (all-diverge-term)))
                            (all-diverge-member-b
                             (dfa-badguy
                              (adfa-badguy (all-diverge-term))
                              (bag::remove-1
                               (adfa-badguy (all-diverge-term))
                               (all-diverge-term)))))
                 (:instance adfa-badguy-works
                            (x (all-diverge-term)))
                 (:instance dfa-badguy-works
                            (a (adfa-badguy (all-diverge-term)))
                            (x (bag::remove-1 (adfa-badguy (all-diverge-term))
                                              (all-diverge-term))))))))

;; To effectively use the all-diverge-by-membership approach, we need to be
;; able to know that arbitrary members of a list which satisfies all-diverge
;; must themselves diverge.  I was quite surprised that this wasn't already a
;; theorem -- it seems like "the main fact" about all-diverge.

(defthm diverge-when-members-of-all-diverge
  (implies (and (all-diverge x) ;; x is a free variable
                (memberp a x)
                (memberp b x))
           (equal (diverge a b)
                  (not (equal a b))))
  :hints(("Goal" :in-theory (enable all-diverge))))


;; Given our membership strategy, we can now painlessly prove a number of nice
;; rewrite rules about all-diverge.

(defthm all-diverge-of-cdr
  (implies (all-diverge x)
           (all-diverge (cdr x))))

(defthm all-diverge-of-remove-1
  (implies (all-diverge x)
           (all-diverge (bag::remove-1 a x))))

(defthm all-diverge-of-remove-all
  (implies (all-diverge x)
           (all-diverge (bag::remove-all a x))))

(defthm all-diverge-of-nthcdr
  (implies (all-diverge x)
           (all-diverge (nthcdr n x))))

(defthm all-diverge-of-firstn
  (implies (all-diverge x)
           (all-diverge (firstn n x))))

(defthm all-diverge-when-subbag
  (implies (and (all-diverge y)
                (bag::subbagp x y))
           (all-diverge x)))

;; jcd - Removing.  This is redundant with diverges-from-all-of-non-consp-one.
;;
;; (defthm diverges-from-all-of-nil
;;   (equal (diverges-from-all nil x)
;;          (not (consp x)))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd - We replaced this rule with diverge-of-cons-one and
;; diverge-of-cons-two, each of which is stronger.
;;
;; (defthm diverge-of-cons-and-cons
;;   (equal (diverge (cons a p1) (cons b p2))
;;          (or (not (equal a b))
;;              (diverge p1 p2)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - removed this, is it legitimate to do so?  is it needed anywhere?
;;
;; (defthm diverges-from-all-when-diverges-from-all-of-cdr
;;   (implies (diverges-from-all p (cdr paths))
;;            (equal (diverges-from-all p paths)
;;                   (if (consp paths)
;;                       (diverge p (car paths))
;;                     t))))

;; jcd - Removing this -- I think this is now handled by adding the rule
;; diverge-when-diverge-with-dominator-two and its alt form.
;;
;; (defthm diverge-when-dominate-divergent
;;   (implies (and (dominates q p)   ;q is a free var
;;                 (dominates q2 p2) ;q2 is a free var
;;                 (diverge q q2))
;;            (diverge p p2))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - This is a really bizarre theorem, and I am getting rid of it.  I have
;; proven a similar rule above but for "diverge" itself, an this is a pretty
;; easy consequence of it.
;;
;; (defthm all-diverge-implies-unequal-extensions
;;   (implies (all-diverge (list x y))
;;            (not (equal (append x a)
;;                        (append y b)))))

;; ----------------------------------------------------------------------------
;;
;;                                   PART 1
;;
;;                          The Dominates Relations
;;
;; ----------------------------------------------------------------------------


;; Dominates
;;
;; We say that list x dominates list y if x is a prefix of y.  We can extend
;; this relation to all ACL2 objects by merely interpreting the objects as
;; lists, i.e., with list::fix.  It is easy to write the dominates function in a
;; straightforward, recursive manner, and that is what we do.

(defund dominates (x y)
  (declare (type t x y))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (dominates (cdr x) (cdr y)))
    t))

;; Another way to look at domination is as follows: x dominates y whenever x is
;; equivalent (in the list sense) to (firstn (len x) y).  This can be a nice
;; way to work with dominates, because now theorems about firstn are available
;; for simplifying terms about dominates.  By default, we keep this alternate
;; definition disabled, but you can enable dominates-redefinition if you would
;; like to use it.

(defthmd dominates-redefinition
  (equal (dominates x y)
         (list::equiv x (firstn (len x) y)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable dominates))))

(defthm dominates-type-1
  (implies (not (consp x))
           (equal (dominates x y) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-type-2
  (implies (and (consp x)
                (not (consp y)))
           (equal (dominates x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-non-consp-one
  (implies (not (consp x))
           (dominates x y))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-non-consp-two
  (implies (not (consp y))
           (equal (dominates x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm list-equiv-when-dominated
  (implies (dominates x y)
           (equal (list::equiv x y)
                  (equal (len x) (len y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-reflexive
  (dominates x x)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-transitive-one
  (implies (and (dominates x y)
                (dominates y z))
           (dominates x z))
  :rule-classes (:rewrite :forward-chaining)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-transitive-two
  (implies (and (dominates y z)
                (dominates x y))
           (dominates x z))
  :rule-classes (:rewrite :forward-chaining)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-weakly-asymmetric
  ;; I think this theorem is more clear when list::equiv is used as the
  ;; conclusion, but I prefer to normalize list::equiv under dominates to a
  ;; simple equality test on the lengths of the list, hence the corollary.
  ;; (See the theorem list-equiv-when-dominated, above).
  (implies (dominates x y)
           (equal (dominates y x)
                  (list::equiv x y)))
  :rule-classes ((:rewrite :corollary
                           (implies (dominates x y)
                                    (equal (dominates y x)
                                           (equal (len x) (len y))))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-cons-one
  (equal (dominates (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (dominates x (cdr y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-cons-two
  (equal (dominates x (cons a y))
         (or (not (consp x))
             (and (equal a (car x))
                  (dominates (cdr x) y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-append-self-one
  (equal (dominates (append x y) x)
         (not (consp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm dominates-of-append-self-two
  (dominates x (append x y))
  :hints(("Goal" :in-theory (enable append))))

(defthm dominates-of-append-and-append
  (equal (dominates (append x z) (append x y))
         (dominates z y))
  :hints(("Goal" :in-theory (enable append))))

(defthm len-when-dominated
  (implies (dominates x y)
           (<= (len x) (len y)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm len-larger-when-dominated
  (implies (dominates x y)
           (equal (< (len y) (len x))
                  nil)))

(defthm len-smaller-when-dominated
  (implies (dominates x y)
           (equal (< (len x) (len y))
                  (not (list::equiv x y))))
  :rule-classes ((:rewrite :corollary
                           (implies (dominates x y)
                                    (equal (< (len x) (len y))
                                           (not (equal (len x) (len y)))))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

;; jcd - can we switch this to be about (equal (len x) (len y)) ?
(defthm dominates-same-len-cheap
  (implies (equal (len x) (len y))
           (equal (dominates x y)
                  (list::equiv x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm nthcdr-len-when-dominates
  (implies (dominates x y)
           (equal (nthcdr (len y) x)
                  (if (equal (len x) (len y))
                      (finalcdr x)
                    nil))))

(defthm append-nthcdr-identity-when-dominates
  (implies (dominates x y)
           (equal (append x (nthcdr (len x) y))
                  y))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-nthcdr-and-nthcdr-from-dominates
  (implies (dominates x y)
           (dominates (nthcdr n x) (nthcdr n y)))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm linear-domination-hierarchy
  ;; Given two dominators of z, one of them must dominate the other.  If we
  ;; think of only "well formed" dominators (i.e., those that end with nil),
  ;; then we imagine that this rule shows how all such dominators can be put
  ;; into a hierarchy of domination, where nil is the most superior, followed
  ;; by (list (car z)), on and on until we reach z itself.  Dropping our well
  ;; formedness assumption, what we actually have is a hierarchy of domination
  ;; classes, where each class's members are list::equiv to one another.
  (implies (and (dominates x z)
                (dominates y z)
                (not (dominates x y)))
           (dominates y x))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-from-dominates-of-nthcdr-etc
  ;; bzo - This proof is ugly and relies on using "dominates" rather than
  ;; dominates-redefinition.  This is probably a weakness that should be
  ;; addressed when we have more time.
  (implies (and (dominates (nthcdr (len x) y)
                           (nthcdr (len x) z))
                (dominates x y)
                (dominates x z))
           (dominates y z))
  :hints(("Goal" :in-theory (enable dominates))))





;; Strictly Dominates
;;
;; Given lists a and b, we say that a strictly dominates b whenever a dominates
;; b but a has a smaller length than b.  In other words, whenever a dominates b
;; but a and b are not "the same" (in the sense of list::equiv) list.  In a way,
;; dominates is like <=, and strictly-dominates is like <.

(defund strictly-dominates (x y)
  (declare (type t x y))
  (and (dominates x y)
       ;; bzo - I want to change this to read
       ;; (not (equal (len x) (len y))), since after all our strategy is to
       ;; rewrite list::equiv to equal lengths when dominates is known.
       ;; But, we have to leave this as (not (list::equiv x y)) for now,
       ;; because otherwise the old theory in records/path.lisp won't work
       ;; quite right.
       ;; bzo - use me instead: (not (equal (len x) (len y)))))
       (not (list::equiv x y))))


;; Note: of course strictly-dominates is nonrecursive, so we might have just
;; left it enabled or even defined it as a macro.  Instead, we have chosen to
;; essentially reprove most of the above theorems about dominates.  In exchange
;; for proving these theorems, we are now able to use strictly-dominates as a
;; target for rewrite rules just like any other function.

(defthm strictly-dominates-forward-to-dominates
  ;; Many of the theorems about dominates also apply to strictly-dominates, so
  ;; we write a forward chaining rule that allows us to note whenever we see
  ;; (strictly-dominates x y) that (dominates x y) is also true.
  (implies (strictly-dominates x y)
           (dominates x y))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm not-dominates-forward-to-not-strictly-dominates
  ;; Many of the theorems about dominates also apply to strictly-dominates, so
  ;; we write a forward chaining rule that allows us to note whenever we see
  ;; (strictly-dominates x y) that (dominates x y) is also true.
  (implies (not (dominates x y))
           (not (strictly-dominates x y)))
  :rule-classes :forward-chaining)

(defthm strictly-dominates-implies-dominates
  ;; Even though we have already proven this as a forward chaining rule, we
  ;; also want this available as a rewrite so that theorems about "dominates"
  ;; can also be used to simplify strictly-dominates terms when backchaining.
  (implies (strictly-dominates x y)
           (dominates x y)))

(defthm strictly-dominates-type-1
  (implies (and (not (consp x))
                (consp y))
           (equal (strictly-dominates x y) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-type-2
  (implies (and (consp x)
                (not (consp y)))
           (equal (strictly-dominates x y) nil))
  :rule-classes :type-prescription)

(defthm strictly-dominates-of-non-consp-one
  (implies (not (consp x))
           (equal (strictly-dominates x y)
                  (consp y)))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-non-consp-two
  (implies (not (consp y))
           (equal (strictly-dominates x y)
                  nil))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-irreflexive
  (not (strictly-dominates x x))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-transitive-one
  (implies (and (strictly-dominates x y)
                (strictly-dominates y z))
           (strictly-dominates x z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-transitive-two
  (implies (and (strictly-dominates y z)
                (strictly-dominates x y))
           (strictly-dominates x z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-asymmetric
  (implies (strictly-dominates x y)
           (equal (strictly-dominates y x)
                  nil))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-cons-one
  (equal (strictly-dominates (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (strictly-dominates x (cdr y))))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-cons-two
  (equal (strictly-dominates x (cons a y))
         (or (not (consp x))
             (and (equal a (car x))
                  (strictly-dominates (cdr x) y))))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-append-self-one
  (equal (strictly-dominates (append x y) x)
         nil)
  :hints (("Goal" :in-theory (enable append))))

(defthm strictly-dominates-of-append-self-two
  (equal (strictly-dominates x (append x y))
         (consp y))
  :hints(("Goal" :in-theory (enable append))))

(defthm strictly-dominates-of-append-and-append
  (equal (strictly-dominates (append x z) (append x y))
         (strictly-dominates z y))
  :hints(("Goal" :in-theory (enable append))))

(defthm len-when-strictly-dominated
  (implies (strictly-dominates x y)
           (< (len x) (len y)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm len-equal-when-strictly-dominated
  (implies (strictly-dominates x y)
           (equal (equal (len x) (len y))
                  nil)))

(defthm len-equal-when-strictly-dominated-2
  (implies (strictly-dominates x y)
           (equal (equal (len y) (len x))
                  nil)))

(defthm len-smaller-when-strictly-dominated
  (implies (strictly-dominates x y)
           (equal (< (len x) (len y))
                  t)))

(defthm not-strictly-dominates-of-append-when-not-strictly-dominates
  (implies (not (strictly-dominates a b))
           (not (strictly-dominates (append a x) b)))
  :hints(("goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-from-strictly-dominates-of-nthcdr-etc
  (implies (and (strictly-dominates (nthcdr (len x) y)
                                    (nthcdr (len x) z))
                (dominates x y)
                (dominates x z))
           (strictly-dominates y z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

;; ----------------------------------------------------------------------------
;;
;;                                   PART 2
;;
;;                Extending the Dominates Relations over Lists
;;
;; ----------------------------------------------------------------------------

;; All Conses
;;
;; We are about to extend our notion of dominates to lists of lists, e.g., so
;; that given some list a and some list of lists x, we can talk about whether
;; or not there are any paths in x that dominate or are dominated by a.  It is
;; useful to be able to talk about the "base" cases where a is an atom, or when
;; x contains some atom, or when x contains no atoms.  (In these cases, the
;; domination relations are trivial).
;;
;; Historical Note: originally we had the function contains-a-non-consp here,
;; which returned true only if the list had an atom as a member.  This is, of
;; course, the same idea as (not (all-conses x)).  However, I prefer to use
;; all-conses, because I think it has nicer rules, particularly for car and cdr
;; and so forth.

(defund all-conses (x)
  (declare (type t x))
  (if (consp x)
      (and (consp (car x))
           (all-conses (cdr x)))
    t))

(defthm all-conses-type-1
  (implies (not (consp x))
           (equal (all-conses x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable all-conses))))

(defthm all-conses-of-consp
  (equal (all-conses (cons a x))
         (and (consp a)
              (all-conses x)))
  :hints(("Goal" :in-theory (enable all-conses))))

(defthm all-conses-of-cdr-when-all-conses
  (implies (all-conses x)
           (all-conses (cdr x))))

(defthm consp-of-car-when-all-conses
  (implies (all-conses x)
           (equal (consp (car x))
                  (consp x))))

(defthm all-conses-from-car/cdr
  (implies (and (consp (car x))
                (all-conses (cdr x)))
           (all-conses x)))

(defthmd consp-when-member-of-all-conses
  (implies (and (all-conses x) ; x is a free variable
                (memberp a x))
           (consp a))
  :hints(("Goal" :in-theory (enable memberp))))

(local (in-theory (enable consp-when-member-of-all-conses)))

(defthmd not-all-conses-when-non-consp-member
  (implies (and (memberp a x)
                (not (consp a)))
           (not (all-conses x)))
  :hints(("Goal" :in-theory (enable memberp))))

(local (in-theory (enable not-all-conses-when-non-consp-member)))

(defthm all-conses-of-append
  (equal (all-conses (append x y))
         (and (all-conses x)
              (all-conses y)))
  :hints(("Goal" :in-theory (enable append))))

(defund no-conses (x)
  (declare (type t x))
  (if (consp x)
      (and (not (consp (car x)))
           (no-conses (cdr x)))
    t))

(defthm no-conses-type-1
  (implies (not (consp x))
           (equal (no-conses x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable no-conses))))

(defthm no-conses-of-consp
  (equal (no-conses (cons a x))
         (and (not (consp a))
              (no-conses x)))
  :hints(("Goal" :in-theory (enable no-conses))))

(defthm no-conses-of-cdr-when-no-conses
  (implies (no-conses x)
           (no-conses (cdr x))))

(defthm consp-of-car-when-no-conses
  (implies (no-conses x)
           (equal (consp (car x))
                  nil)))

(defthm no-conses-from-car/cdr
  (implies (and (not (consp (car x)))
                (no-conses (cdr x)))
           (no-conses x)))

(defthm not-consp-when-member-of-no-conses
  (implies (and (no-conses x) ; x is a free variable
                (memberp a x))
           (equal (consp a)
                  nil))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm not-no-conses-when-consp-member
  (implies (and (memberp a x)
                (consp a))
           (not (no-conses x)))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm no-conses-of-append
  (equal (no-conses (append x y))
         (and (no-conses x)
              (no-conses y)))
  :hints(("Goal" :in-theory (enable append))))

;; Dominates Some
;;
;; Given some list a, and some list of lists x, we say that a "dominates some"
;; list in x whenever there is some list b in x such that a dominates b.

(defund dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates a (car x))
          (dominates-some a (cdr x)))
    nil))

(defthm dominates-some-type-1
  (implies (not (consp x))
           (equal (dominates-some a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-type-2
  (implies (and (consp x)
                (not (consp a)))
           (equal (dominates-some a x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-non-consp-two
  (implies (not (consp x))
           (not (dominates-some a x))))

(defthm dominates-some-non-consp-one
  (implies (not (consp a))
           (equal (dominates-some a x)
                  (consp x))))

(defthm dominates-some-of-cons
  (equal (dominates-some a (cons b x))
         (or (dominates a b)
             (dominates-some a x)))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-of-append
  (equal (dominates-some a (append x y))
         (or (dominates-some a x)
             (dominates-some a y)))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (dominates a b))
           (dominates-some a x))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm not-dominates-some-forward-to-not-dominates
  (implies (and (not (dominates-some b x))
                (memberp a x)) ;; a is a free variable
           (not (dominates b a)))
  :rule-classes :forward-chaining)

;; Strictly Dominates Some
;;
;; Given some list a, and some list of lists x, we say that a "strictly
;; dominates some" list in x whenever there is some list b in x such that a
;; strictly dominates b.

(defund strictly-dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates a (car x))
          (strictly-dominates-some a (cdr x)))
    nil))

(defthm strictly-dominates-some-type-1
  (implies (not (consp x))
           (equal (strictly-dominates-some a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-non-consp-two
  (implies (not (consp x))
           (not (strictly-dominates-some a x))))

(defthm strictly-dominates-some-non-consp-one
  (implies (not (consp a))
           (equal (strictly-dominates-some a x)
                  (not (no-conses x))))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-of-cons
  (equal (strictly-dominates-some a (cons b x))
         (or (strictly-dominates a b)
             (strictly-dominates-some a x)))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-of-append
  (equal (strictly-dominates-some a (append x y))
         (or (strictly-dominates-some a x)
             (strictly-dominates-some a y)))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (strictly-dominates a b))
           (strictly-dominates-some a x))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm not-strictly-dominates-some-forward-to-not-strictly-dominates
  (implies (and (not (strictly-dominates-some b x))
                (memberp a x)) ;; a is a free variable
           (not (strictly-dominates b a)))
  :rule-classes :forward-chaining)

;; Dominated By Some
;;
;; Given some list a, and some list of lists x, we say a is "dominated by some"
;; list in x whenever there is some list b in x such that b dominates a.

(defund dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates (car x) a)
          (dominated-by-some a (cdr x)))
    nil))

(defthm dominated-by-some-type-1
  (implies (not (consp x))
           (equal (dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-non-consp-one
  (implies (not (consp a))
           (equal (dominated-by-some a x)
                  (not (all-conses x))))
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-non-consp-two
  (implies (not (consp x))
           (equal (dominated-by-some a x)
                  nil)))

(defthm dominated-by-some-of-cons
  (equal (dominated-by-some a (cons b x))
         (or (dominates b a)
             (dominated-by-some a x)))
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-from-car
  (implies (and (consp x)
                (dominates (car x) a))
           (dominated-by-some a x)))

(defthm dominated-by-some-from-cdr
  (implies (dominated-by-some a (cdr x))
           (dominated-by-some a x)))

(defthm not-dominated-by-some-from-car/cdr
  (implies (and (consp x)
                (not (dominated-by-some a (cdr x)))
                (not (dominates (car x) a)))
           (not (dominated-by-some a x))))

(defthm not-dominated-by-some-from-weaker
  (implies (and (not (dominated-by-some a x))
                (dominates b a))
           (not (dominated-by-some b x)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-append
  (equal (dominated-by-some a (append x y))
         (or (dominated-by-some a x)
             (dominated-by-some a y)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (dominates b a))
           (dominated-by-some a x))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm not-dominated-by-some-forward-to-not-dominates
  (implies (and (not (dominated-by-some b x))
                (memberp a x)) ;; a is a free variable
           (not (dominates a b)))
  :rule-classes :forward-chaining)

;; Strictly Dominated By Some
;;
;; Given some list a, and some list of lists x, we say a is "strictly dominated
;; by some" list in x whenever there is some list b in x such that b strictly
;; dominates a.

(defund strictly-dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates (car x) a)
          (strictly-dominated-by-some a (cdr x)))
    nil))

(defthm strictly-dominated-by-some-forward-to-dominated-by-some
  (implies (strictly-dominated-by-some a x)
           (dominated-by-some a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm not-dominated-by-some-forward-to-not-strictly-dominated-by-some
  (implies (not (dominated-by-some a x))
           (not (strictly-dominated-by-some a x)))
  :rule-classes :forward-chaining)

(defthm strictly-dominated-by-some-implies-dominated-by-some
  (implies (strictly-dominated-by-some a x)
           (dominated-by-some a x)))

(defthm strictly-dominated-by-some-type-1
  (implies (not (consp x))
           (equal (strictly-dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-type-2
  (implies (not (consp a))
           (equal (strictly-dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-non-consp-one
  (implies (not (consp a))
           (equal (strictly-dominated-by-some a x)
                  nil))
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-non-consp-two
  (implies (not (consp x))
           (equal (strictly-dominated-by-some a x)
                  nil)))

(defthm strictly-dominated-by-some-of-cons
  (equal (strictly-dominated-by-some a (cons b x))
         (or (strictly-dominates b a)
             (strictly-dominated-by-some a x)))
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-from-car
  (implies (and (consp x)
                (strictly-dominates (car x) a))
           (strictly-dominated-by-some a x)))

(defthm strictly-dominated-by-some-from-cdr
  (implies (strictly-dominated-by-some a (cdr x))
           (strictly-dominated-by-some a x)))

(defthm not-strictly-dominated-by-some-from-car/cdr
  (implies (and (consp x)
                (not (strictly-dominated-by-some a (cdr x)))
                (not (strictly-dominates (car x) a)))
           (not (strictly-dominated-by-some a x))))

(defthm not-strictly-dominated-by-some-from-weaker
  (implies (and (not (dominated-by-some a x))
                (strictly-dominates b a))
           (not (strictly-dominated-by-some b x)))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-append
  (equal (strictly-dominated-by-some a (append x y))
         (or (strictly-dominated-by-some a x)
             (strictly-dominated-by-some a y)))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (strictly-dominates b a))
           (strictly-dominated-by-some a x))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm not-strictly-dominated-by-some-forward-to-not-strictly-dominates
  (implies (and (not (strictly-dominated-by-some b x))
                (memberp a x)) ;; a is a free variable
           (not (strictly-dominates a b)))
  :rule-classes :forward-chaining)

;; First Dominator
;;
;; Given a list a, and a list of lists x, we define (first-dominator a x) as
;; the first list in x which dominates a, or nil otherwise.
;;
;; Historical note: first-dominator used to return 'no-dominator-found if it
;; reached the end of the list.  But, I changed it so that it instead returns
;; nil.  This has a couple of advantages.  For one, it yields better type
;; prescription rules, because nil is its own type whereas 'no-dominator-found
;; is not.  Furthermore, because nil dominates everything, the theorem
;; first-dominator-dominates is now a global truth with no hyps about whether a
;; is dominated-by-some or not.

(defund first-dominator (a x)
  (declare (type t a x))
  (if (atom x)
      nil
    (if (dominates (car x) a)
        (car x)
      (first-dominator a (cdr x)))))

(defthm first-dominator-type-1
  (implies (not (consp x))
           (equal (first-dominator a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable first-dominator))))

(defthm first-dominator-of-non-consp-two
  (implies (not (consp x))
           (equal (first-dominator a x)
                  nil)))

(defthm first-dominator-dominates
  (dominates (first-dominator a x) a)
  :hints(("Goal" :in-theory (enable first-dominator))))


(defthm first-dominator-cons
  (equal (first-dominator a (cons b x))
         (if (dominates b a)
             b
           (first-dominator a x)))
  :hints(("Goal" :in-theory (enable first-dominator))))

(defthm first-dominator-of-cdr
  (implies (and (consp x)
                (not (dominates (car x) a)))
           (equal (first-dominator a (cdr x))
                  (first-dominator a x))))

(defthm first-dominator-when-car-dominates
  (implies (and (consp x)
                (dominates (car x) a))
           (equal (first-dominator a x)
                  (car x))))

;; It is almost true that (iff (first-dominator a x) (dominated-by-some a x)).
;; unfortunately, if nil is a member of x, then the first-dominator of a might
;; be nil, even though a is dominated by some.  Nevertheless, we have some
;; fairly powerful rules about this relationship:

(defthm first-dominator-implies-dominated-by-some
  (implies (first-dominator a x)
           (dominated-by-some a x))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-when-first-dominator-nil
  (implies (not (first-dominator a x))
           (equal (dominated-by-some a x)
                  (memberp nil x)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))


;; Another thing you might think is true is the following, but it isn't because
;; nil might occur near the front or near the end of a list that also contains
;; other dominators.
;;
;; (defcong BAG::perm iff (first-dominator a x) 2




;; bzo whats this for?

(defthm first-dominator-when-p-dominates-it-yuck
  (implies (and (dominates a b)
                (equal (first-dominator a x) b))
           (equal (list::equiv b a)
                  t)))

;; ----------------------------------------------------------------------------
;;
;;                                 Appendix A
;;
;;                       Pile of Dead Rules (bzo Remove Me)
;;
;; ----------------------------------------------------------------------------

;; jcd - removed this, redundant with dominates-of-non-consp-two

; (defthm dominates-of-nil-two
;   (equal (dominates p1 nil)
;          (not (consp p1)))
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with dominates-of-non-consp-one

; (defthm dominates-of-nil-one
;   (equal (dominates nil p2)
;          t)
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with congruence rule

; (defthm dominates-of-list-fix-one
;   (equal (dominates (list::fix p1) p2)
;          (dominates p1 p2))
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with congruence rule

; (defthm dominates-of-list-fix-two
;   (equal (dominates p1 (list::fix p2))
;          (dominates p1 p2))
;   :hints (("Goal" :in-theory (enable dominates))))


;; jcd - removing this rule since it is never used anywhere and was disabled
;; to begin with.  It just doesn't seem like a good rule at all.
;;
;; (defthmd dominates-of-cdr-and-cdr-one
;;   (implies (and (equal (car p1) (car p2))
;;                 (consp p1)
;;                 (consp p2))
;;            (equal (dominates (cdr p1) (cdr p2))
;;                   (dominates p1 p2))))
;;

;; jcd - removed this rule.  in its place, i have proven the two rules
;; dominates-of-cons-one and dominates-of-cons-two, which are each stronger.
;;
;; (defthm dominates-of-cons-and-cons
;;   (equal (dominates (cons a p1) (cons b p2))
;;          (and (equal a b)
;;               (dominates p1 p2))))

;; jcd - these rules seem bad.  i understand that we want to be able to
;; reason about singletons and domination, but where does it end?  why not
;; write similar rules for doubles and triples?  I think at some point we
;; have to let destructor elimination do its job.
;;
;; of course, I could be wrong.  Maybe it's not too much to ask to have
;; special rules for singletons.  We'll see if anythign breaks.


;; ;make a -one version
;; ;make analogue for diverge?
;; (defthm dominates-of-singleton-two
;;   (implies (not (consp (cdr p2)))
;;            (equal (dominates p1 p2)
;;                   (if (consp p2)
;;                       (or (not (consp p1))
;;                           (and (equal (car p1) (car p2))
;;                                (not (consp (cdr p1)))))
;;                     (not (consp p1))))))

;; (defthm not-dominates-by-cadr-inequality
;;   (implies (and (consp p1)
;;                 (consp p2)
;;                 (consp (cdr p1))
;;                 (consp (cdr p2))
;;                 (not (equal (cadr p1) (cadr p2))))
;;            (not (dominates p1 p2))))



;; jcd - Removed this: redundant with dominated-by-some-of-non-consp-one.
;;
;; (defthm dominated-by-some-of-nil-one
;;   (equal (dominated-by-some nil paths)
;;          (contains-a-non-consp paths)))

;; jcd - Removed this: redundant with dominated-by-some-of-non-consp-two
;; and has-atom-of-non-consp
;;
;; (defthm dominated-by-some-of-nil-two
;;   (equal (dominated-by-some paths nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

; bzo - consider instead...
;(defthm dominates-of-nthcdr-and-nthcdr-from-dominates
;  (implies (dominates p1 p2)
;           (equal (dominates (nthcdr n1 p1) (nthcdr n2 p2))
;                  (equal (nfix n1)
;                         (nfix n2)))))

;; two-dominators-hack: given two dominators of p, one of the must dominate the
;; other

;; jcd - I have tried some variations of this rule.  I first tried case
;; splitting explicitly using
;;
;; (defthm two-dominators-hack
;;   (implies (and (dominates a p)
;;                 (dominates b p))
;;            (equal (dominates a b)
;;                   (if (dominates b a)
;;                       (list::equiv a b)
;;                     t))))
;;
;; But it turned out that this caused loops.  I also tried adding a case-split
;; around (not (dominates a b)) to make things more explicit.  That seemed to
;; work well, but sometimes misdirects proofs?
;;
;; (defthm two-dominators-hack
;;   (implies (and (dominates a p)
;;                 (dominates b p)
;;                 (case-split (not (dominates a b))))
;;            (dominates b a)))

; jcd - i don't like this rule, but i had to add it for a case
; where it came up.  can we make it more general?
;(defthm not-dominates-append-by-unequal-cars
;  (implies (and (consp path)
;                (not (equal (car path) (car path2))))
;           (not (dominates (append path rest)
;                           path2)))
;  :hints(("Goal" :in-theory (enable dominates))))

(local
 (defthm open-nthcdr
   (implies
    (not (zp n))
    (equal (nthcdr n list)
           (nthcdr (1- n) (cdr list))))))

(local
 (defthm open-list-equiv-on-consp
   (equal (list::equiv x y)
          (if (consp x)
              (and (consp y)
                   (equal (car x) (car y))
                   (list::equiv (cdr x) (cdr y)))
            (not (consp y))))
   :rule-classes (:definition)))

(defun gg (path r)
  (if (consp path)
      (gg (cdr path) (alist::getv (car path) (cdr r)))
    r))

(defun gg-2-induction (p1 p2 r)
  (if (consp p1)
      (gg-2-induction (cdr p1) (cdr p2) (alist::getv (car p1) (cdr r)))
    (list p1 p2 r)))

(defun sg (path g r)
  (if (consp path)
      (cons (car r) (alist::setv (car path) (sg (cdr path) g (alist::getv (car path) (cdr r)))
                                 (cdr r)))
    g))

;; The problem is that we ultimatley _need_ (budsubp x x) in order to
;; prove the equivalence relation.  Perhaps "getv" (as defined) is too strong?
;; Perhaps what we really want is something less lossy.  We want something
;; whose consp nature can be encoded to identify membership.

;; You need something stronger than "subset" for the keys ..
;; you need some notion that the value actually exists (?)

(defund budsubp (r1 r2)
  (and (implies (consp r1) (consp r2))
       (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
       (implies (consp (car r1)) (consp (car r2)))
       (all-dominated-by-some (caar r1) (caar r2))))

(defund budequiv (r1 r2)
  (and (budsubp r1 r2)
       (budsubp r2 r1)))

(defthm budsubp-id
  (budsubp x x)
  :hints (("Goal" :in-theory (enable budsubp))))

(defthm budsubp-chaining-1
  (implies
   (and
    (budsubp x y)
    (budsubp y z))
   (budsubp x z))
  :hints (("Goal" :in-theory (enable budsubp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm budsubp-chaining-2
  (implies
   (and
    (budsubp y z)
    (budsubp x y))
   (budsubp x z))
  :rule-classes (:rewrite :forward-chaining))

(defthm budsubp-consp-forward
  (implies
   (and
    (budsubp r1 r2)
    (consp r1))
   (consp r2))
  :hints (("Goal" :in-theory (enable budsubp)))
  :rule-classes (:forward-chaining))

(defthm budsubp-subset-forward
  (implies
   (budsubp r1 r2)
   (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2))))
  :hints (("Goal" :in-theory (enable budsubp)))
  :rule-classes (:rewrite :forward-chaining))


(defthm consp-get-implies-memberp-keys
  (implies
   (consp (alist::getv a alist))
   (memberp a (alist::keys alist)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable alist::getv))))

(defun treesubp-aux (alist1 alist2)
  (if (consp alist1)
      (let ((key (caar alist1)))
        (and (memberp key (alist::keys alist2))
             (budsubp (alist::getv key alist1) (alist::getv key alist2))
             (treesubp-aux (cdr (alist::getv key alist1)) (cdr (alist::getv key alist2)))
             (treesubp-aux (alist::clr key alist1) (alist::clr key alist2))))
    t))

(defund treesubp (r1 r2)
  (and (budsubp r1 r2)
       (treesubp-aux (cdr r1) (cdr r2))))

(defthm treesubp-implies-budsup
  (implies
   (treesubp r1 r2)
   (budsubp r1 r2))
  :hints (("Goal" :in-theory (enable treesubp)))
  :rule-classes (:forward-chaining))

(defthmd treesubp-aux-definition
  (equal (treesubp-aux alist1 alist2)
         (if (consp alist1)
             (let ((key (caar alist1)))
               (and (memberp key (alist::keys alist2))
                    (treesubp (alist::getv key alist1) (alist::getv key alist2))
                    (treesubp-aux (alist::clr key alist1) (alist::clr key alist2))))
           t))
  :hints (("Goal" :in-theory (enable treesubp)
           :expand (treesubp-aux alist1 alist2)))
  :rule-classes (:definition))

;; It is (very) convenient to move to a representation in which the recursion
;; does not change the real "arguments"

(defun treesubp-keyed-aux (keys alist1 alist2)
  (if (consp keys)
      (let ((key (car keys)))
        (and (memberp key (alist::keys alist1))
             (memberp key (alist::keys alist2))
             (treesubp (alist::getv key alist1) (alist::getv key alist2))
             (treesubp-keyed-aux (cdr keys) alist1 alist2)))
    t))

(defthmd treesubp-keyed-aux-clr-reduction
  (implies
   (not (memberp key keys))
   (equal (treesubp-keyed-aux keys (alist::clr key alist1) (alist::clr key alist2))
          (treesubp-keyed-aux keys alist1 alist2))))

(defthm treesubp-keyed-aux-implies-treesubp
  (implies
   (and
    (treesubp-keyed-aux keys x y)
    (memberp a keys))
   (treesubp (alist::getv a x)
             (alist::getv a y))))

(defthm treesubp-aux-to-treesubp-keyed-aux
  (implies
   (subsetp (alist::keys alist1) (alist::keys alist2))
   (equal (treesubp-aux alist1 alist2)
          (treesubp-keyed-aux (alist::keys alist1) alist1 alist2)))
  :hints (("Goal" :in-theory (enable treesubp-aux-definition)
           :use (:functional-instance generic-alist-aux-to-generic-keyed-aux
                                      (generic-alist-aux treesubp-aux)
                                      (generic-keyed-aux treesubp-keyed-aux)
                                      (generic-alist-base (lambda () t))
                                      (generic-alist-pred treesubp)))))


(defthm treesubp-keyed-aux-implications
  (implies
   (treesubp-keyed-aux keys alist1 alist2)
   (and (subsetp keys (alist::keys alist1))
        (subsetp keys (alist::keys alist2))))
  :rule-classes (:forward-chaining))

(local
 (defthm equal-1-reduction
   (implies
    (and
     (integerp x)
     (integerp y))
    (equal (equal (+ 1 x) (+ 1 y))
           (equal x y)))))


(defun treesubp-keyed-induction (xkeys ykeys alist1 alist2 alist3)
  (declare (xargs :hints (("Goal" :in-theory (enable treesubp)))
                  :measure `((1 . ,(1+ (acl2-count alist1))) . ,(len xkeys))))
  (if (consp xkeys)
      (let ((key (car xkeys)))
        (let ((r1 (alist::getv key alist1))
              (r2 (alist::getv key alist2))
              (r3 (alist::getv key alist3)))
          (and (memberp key (alist::keys alist1))
               (memberp key (alist::keys alist2))
               (memberp key (alist::keys alist3))
               (treesubp r1 r2)
               (treesubp r2 r3)
               (cons (treesubp-keyed-induction (alist::keys (cdr r1)) (alist::keys (cdr r2))
                                               (cdr r1) (cdr r2) (cdr r3))
                     (treesubp-keyed-induction (remove key xkeys) (remove key ykeys)
                                               alist1 alist2 alist3)))))
    (list xkeys ykeys alist1 alist2 alist3)))

(defthmd open-treesubp-keyed-aux-on-memberp
  (implies
   (memberp a keys)
   (equal (treesubp-keyed-aux keys alist1 alist2)
          (and (memberp a (alist::keys alist1))
               (memberp a (alist::keys alist2))
               (treesubp (alist::getv a alist1) (alist::getv a alist2))
               (treesubp-keyed-aux (remove a keys) alist1 alist2)))))

(defthmd consp-implies-memberp-car-forward
  (implies
   (consp x)
   (memberp (car x) x))
  :rule-classes (:forward-chaining))

(defthmd treesubp-keyed-aux-alt
  (equal (treesubp-keyed-aux keys alist1 alist2)
         (if (consp keys)
             (let ((key (car keys)))
               (and (memberp key (alist::keys alist1))
                    (memberp key (alist::keys alist2))
                    (treesubp (alist::getv key alist1) (alist::getv key alist2))
                    (treesubp-keyed-aux (remove (car keys) keys) alist1 alist2)))
           t))
  :hints (("goal" :in-theory `(open-treesubp-keyed-aux-on-memberp
                               consp-implies-memberp-car-forward))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here))))
  :rule-classes (:definition))

(defthm treesubp-keyed-aux-chaining
  (implies
   (and
    (treesubp-keyed-aux xkeys x y)
    (treesubp-keyed-aux ykeys y z)
    (subsetp xkeys (alist::keys x))
    (subsetp xkeys ykeys))
   (treesubp-keyed-aux xkeys x z))
  :hints (("Goal" :in-theory (enable
                              treesubp
                              treesubp-keyed-aux-alt
                              open-treesubp-keyed-aux-on-memberp
                              consp-implies-memberp-car-forward
                              )
           :induct (treesubp-keyed-induction xkeys ykeys x y z))))

(defthm treesubp-chaining
  (implies
   (and
    (treesubp x y)
    (treesubp y z))
   (treesubp x z))
  :hints (("Goal" :in-theory (enable treesubp))))

(in-theory (disable treesubp-aux))

(defthm open-treesubp-on-consp
  (implies
   (consp r1)
   (equal (treesubp r1 r2)
          (and (budsubp r1 r2)
               (treesubp-keyed-aux (alist::keys (cdr r1)) (cdr r1) (cdr r2)))))
  :hints (("Goal" :in-theory (enable treesubp))))

(defun treesubp-aux-check (key alist1 alist2)
  (and (treesubp (alist::getv key alist1)
                 (alist::getv key alist2))
       (memberp key (alist::keys alist1))
       (memberp key (alist::keys alist2))))

(defun treequiv (x y)
  (and (treesubp x y)
       (treesubp y x)))

(defthm treesubp-id
  (treesubp x x))

(defun gg-induction-2 (path x y)
  (if (and (consp path) (consp x) (memberp (car path) (alist::keys (cdr x))))
      (gg-induction-2 (cdr path) (alist::getv (car path) (cdr x))
                      (alist::getv (car path) (cdr y)))
    (list path x y)))

(defthm getv-non-memberp
  (implies
   (not (memberp a (alist::keys x)))
   (equal (alist::getv a x)
          nil))
  :hints (("Goal" :in-theory (enable alist::getv))))

(defthm gg-nil
  (equal (gg path nil)
         nil))

(defthm budsubp-nil
  (budsubp nil x)
  :hints (("Goal" :in-theory (enable budsubp))))

(defthm treesubp-implies-budsubp-path
  (implies
   (treesubp x y)
   (budsubp (gg path x)
            (gg path y)))
  :hints (("Goal" :in-theory (enable alist::keys)
           :expand ((treesubp x y) (gg path x) (gg path y))
           :induct (gg-induction-2 path x y))))

(defthmd gg-of-gg
  (equal (gg path1 (gg path2 x))
         (gg (append path2 path1) x)))

(defthm treesubp-implies-treesubp-path
  (implies
   (treesubp x y)
   (treesubp (gg path x)
             (gg path y)))
  :hints (("Goal" :in-theory (enable gg-of-gg))))

(in-theory (disable treequiv))

(defthm treesubp-aux-id
  (treesubp-aux x x))

(defund treequiv-aux (x y)
  (and (list::setequiv (alist::keys x) (alist::keys y))
       (treesubp-aux x y)
       (treesubp-aux y x)))

(defthmd treequiv-definition
  (equal (treequiv x y)
         (and (budequiv x y)
              (treequiv-aux (cdr x) (cdr y))))
  :hints (("Goal" :in-theory (enable treequiv treequiv-aux treesubp budequiv treequiv-aux))))

(defthm treequiv-treequiv-gp
  (implies
   (treequiv x y)
   (treequiv (gg path x) (gg path y)))
  :rule-classes nil)

(defund buddepequiv (x y)
  (and (consequiv x y)
       (cpath::setequiv (car x) (car y))))

(defthmd budequiv-definition
  (equal (budequiv x y)
         (and (consequiv x y)
              ;; Is this what we _really_ want for "keyquiv"?
              (list::setequiv (alist::keys (cdr x)) (alist::keys (cdr y)))
              (buddepequiv (car x) (car y))))
  :hints (("Goal" :in-theory (enable budequiv budsubp buddepequiv))))

(defthm consp-sg
  (equal (consp (sg path g r))
         (if (consp path) t (consp g))))

(defthm cdr-sg
  (equal (cdr (sg path g r))
         (if (consp path)
             (alist::setv (car path)
                          (sg (cdr path)
                              g (alist::getv (car path) (cdr r)))
                          (cdr r))
           (cdr g))))

(defthm car-sg
  (equal (car (sg path g r))
         (if (consp path) (car r) (car g))))

;;
;; These proofs need the adviser patch in CVS/adviser
;;

(in-theory (enable diverge memberp))

(defthm nth-i-dominates-same-1
  (implies
   (and
    (dominates p1 p2)
    (< (nfix i) (len p1)))
   (equal (equal (nth i p2) (nth i p1)) t)))

(defthm nth-i-dominates-same-2
  (implies
   (and
    (dominates p1 p2)
    (< (nfix i) (len p1)))
   (equal (equal (nth i p1) (nth i p2)) t)))

(defthm dominates-implies-<-len
  (implies
   (and
    (dominates x y)
    (not (list::equiv x y)))
   (< (len x) (len y)))
  :rule-classes (:linear))

(defthm sp-dominates-sp
  (implies
   (dominates p1 p2)
   (treequiv (sg p1 v1 (sg p2 v2 r))
             (sg p1 v1 r)))
  :hints (("Goal" :in-theory (enable budequiv-definition))))

(defthm sp-diverge-sp
  (implies
   (diverge p1 p2)
   (treequiv (sg p1 v1 (sg p2 v2 r))
             (sg p2 v2 (sg p1 v1 r))))
  :hints (("Goal" :in-theory (enable budequiv-definition))))

(defthm sp-dominated-sp
  (implies
   (dominates p2 p1)
   (treequiv (sg p1 v1 (sg p2 v2 r))
             (sg p2 (sg (nthcdr (len p2) p1) v1 v2) r)))
  :hints (("Goal" :in-theory (enable budequiv-definition))))

(defthm sg-of-sg
  (treequiv (sg p1 v1 (sg p2 v2 r))
            (if (dominates p1 p2)
                (sg p1 v1 r)
              (if (diverge p1 p2)
                  (sg p2 v2 (sg p1 v1 r))
                (sg p2 (sg (nthcdr (len p2) p1) v1 v2) r))))
  :hints (("Goal" :in-theory (disable ADVISER-TREEQUIV-TRIGGER)))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))


;;
;; Depset
;;

(defun depset-aux (alist)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((r (alist::getv key alist)))
          (append (depset-aux (cdr r)) (caar r)
                  (depset-aux (alist::clr key alist)))))
    nil))

(defthm not-consp-depset-aux
  (implies
   (not (consp alist))
   (equal (depset-aux alist) nil)))

(defthm not-consp-getv
  (implies
   (not (consp alist))
   (equal (alist::getv key alist) nil))
  :hints (("Goal" :in-theory (enable alist::getv))))

(defund depset (r)
  (append (depset-aux (cdr r)) (caar r)))

(defthm not-consp-depset
  (implies
   (not (consp r))
   (equal (depset r) nil))
  :hints (("Goal" :in-theory (enable depset))))

(defthm depset-aux-definition
  (equal (depset-aux alist)
         (if (consp alist)
             (let ((key (caar alist)))
               (let ((r (alist::getv key alist)))
                 (append (depset r)
                         (depset-aux (alist::clr key alist)))))
           nil))
  :hints (("Goal" :in-theory (enable depset)))
  :rule-classes (:definition))

(defthm setequiv-remove-reduction
  (implies
   (and
    (memberp key x)
    (memberp key y))
   (equal (list::setequiv (remove key x) (remove key y))
          (list::setequiv x y)))
  :hints (("Goal" :in-theory (enable list::setequiv))))

;;
;; I think you could move this up a bit.
;;
(defthm open-treequiv-aux-on-memberp
  (implies
   (memberp key (alist::keys x))
   (equal (treequiv-aux x y)
          (and (memberp key (alist::keys y))
               (treequiv (alist::getv key x) (alist::getv key y))
               (treequiv-aux (alist::clr key x) (alist::clr key y)))))
  :hints (("Goal" :in-theory (e/d (treesubp-keyed-aux-clr-reduction
                                   TREEQUIV
                                   LIST::SETEQUIV
                                   OPEN-TREESUBP-KEYED-AUX-ON-MEMBERP
                                   treequiv-aux)
                                  (TREESUBP-AUX-BY-MULTIPLICITY
                                   TREESUBP-BY-MULTIPLICITY)))))


(defthmd consp-implies-memberp-caar
  (implies
   (consp x)
   (memberp (caar x) (alist::keys x)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable alist::keys))))

(defun depset-equiv-induction (alist y)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((r1 (alist::getv key alist))
              (r2 (alist::getv key y)))
          (append (depset-equiv-induction (cdr r1) (cdr r2))
                  (depset-equiv-induction (alist::clr key alist) (alist::clr key y)))))
    (list alist y)))

(defthm not-consp-treequiv-aux-implies-not-consp
  (implies
   (and
    (treequiv-aux x y)
    (not (consp x)))
   (not (consp y)))
  :hints (("Goal" :in-theory (enable alist::keys treequiv-aux))))

(defthm treequiv-aux-implies-setequiv-depset-aux
  (implies
   (treequiv-aux x y)
   (cpath::setequiv (depset-aux x)
                   (depset-aux y)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (consp-implies-memberp-caar
                                   BUDEQUIV-DEFINITION
                                   TREEQUIV-DEFINITION
                                   depset)
                                  (SETEQUIV-BY-MULTIPLICITY))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :induct (depset-equiv-induction x y))))

(defthm treequiv-implies-setequiv-depset
  (implies
   (treequiv x y)
   (cpath::setequiv (depset x) (depset y)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable TREEQUIV-DEFINITION
                                     depset))))

;; The notion of "depequiv" is soo weak that I cannot imagine using it in the
;; hypothesis in any interesting way.  We are structuring the library to
;; prove, rather than use, depequiv and we will do so by proving treequiv.

(defund depequiv (x y)
  (cpath::setequiv (depset x) (depset y)))

;; We use the following fact to create a pick-a-point strategy to replaces
;; questions of "setequiv depset" with treequiv.

(defthm treequiv-implies-depequiv
  (implies
   (treequiv x y)
   (depequiv x y))
  :hints (("Goal" :in-theory (enable depequiv)))
  :rule-classes (:forward-chaining))

(defthm setequiv-depset-to-depequiv
  (equal (cpath::setequiv (depset x) (depset y))
         (depequiv x y))
  :hints (("Goal" :in-theory (enable depequiv))))

(in-theory (enable BUDDEPEQUIV))
(in-theory (enable BUDEQUIV-definition))

;; Dependency sets that are submissive to the path
;; (path dominates them)
(defund sub-deps (path g)
  (depset (gg path g)))

(defthm sub-deps-sg
  (cpath::setequiv (sub-deps path1 (sg path2 g r))
                  (if (diverge path1 path2)
                      (sub-deps path1 r)
                    (if (dominates path2 path1)
                        (sub-deps (nthcdr (len path2) path1) g)
                      (depset (sg (nthcdr (len path1) path2) g (gg path1 r))))))
  :hints (("Goal" :in-theory (enable sub-deps))))

;; Dependency sets that dominate path
(defun dom-deps (path d g)
  (if (consp path)
      (let ((d (if (consp (car g)) (caar g) d)))
        (dom-deps (cdr path) d (alist::getv (car path) (cdr g))))
    d))

(defthm dom-deps-not-consp
  (implies
   (not (consp g))
   (equal (dom-deps path d g)
          d)))

(defun dom-deps-2p-induction (path p2 d g)
  (if (consp path)
      (let ((d (if (consp (car g)) (caar g) d)))
        (dom-deps-2p-induction (cdr path) (cdr p2) d (alist::getv (car path) (cdr g))))
    (list path p2 d g)))

(defun dom-deps-2g-induction (path d g g2)
  (if (consp path)
      (let ((d (if (consp (car g)) (caar g) d)))
        (if (memberp (car path) (alist::keys (cdr g)))
            (dom-deps-2g-induction (cdr path) d (alist::getv (car path) (cdr g)) (alist::getv (car path) (cdr g2)))
          (list path d g g2)))
    (list path d g g2)))

(defthm open-dom-deps-on-consp
  (implies
   (consp path)
   (equal (dom-deps path d g)
          (let ((d (if (consp (car g)) (caar g) d)))
            (dom-deps (cdr path) d (alist::getv (car path) (cdr g)))))))

(in-theory (enable BUDDEPEQUIV))
(in-theory (enable BUDEQUIV-definition))

(defund u2g (u)
  (cons (list u) nil))

(defund sd (path u g)
  (sg path (u2g u) g))

(defun ddeps (path d g)
  (if (consp (car (gg path g))) nil
    (dom-deps path d g)))

(defthm consp-car-gg-reduction
  (implies
   (and
    (treequiv r1 r2)
    (syntaxp (acl2::smaller-term r2 r1)))
   (equal (consp (car (gg path r1)))
          (consp (car (gg path r2)))))
  :hints (("Goal" :in-theory (e/d (treequiv-definition)
                                  (TREEQUIV-IMPLIES-TREEQUIV-GG-2))
           :use (:instance treequiv-treequiv-gp (x r1) (y r2))))
  :rule-classes ((:rewrite :loop-stopper ((r1 r2)))))

(defund gdia (r path g)
  (let ((d (list path)))
    (if (consp (car r)) (depset r)
      (append (dom-deps path d g) (depset r)))))


(defthm treequiv-consp-car-reduction
  (implies
   (and
    (treequiv r1 r2)
    (syntaxp (acl2::smaller-term r2 r1)))
   (equal (consp (car r1))
          (consp (car r2))))
  :hints (("Goal" :in-theory (enable treequiv-definition)))
  :rule-classes ((:rewrite :loop-stopper ((r1 r2)))))

(defun dia (path g)
  (let ((r (gg path g)))
    (gdia r path g)))

(defthm gdia-consp-car
  (implies
   (consp (car g))
   (equal (gdia g path r)
          (depset g)))
  :hints (("Goal" :in-theory (enable gdia))))

;; dkeys (dominant keys)

(defun dkeys-aux (alist)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((r (alist::getv key alist)))
          (if (consp (car r))
              (cons (list key)
                    (dkeys-aux (alist::clr key alist)))
            (append (list::map-cons key (dkeys-aux (cdr r)))
                    (dkeys-aux (alist::clr key alist))))))
    nil))

(defthm not-consp-dkeys-aux
  (implies
   (not (consp alist))
   (equal (dkeys-aux alist) nil)))

(defund dkeys (r)
  (if (consp (car r)) (list nil)
    (dkeys-aux (cdr r))))

(defthm not-consp-dkeys
  (implies
   (not (consp r))
   (equal (dkeys r) nil))
  :hints (("Goal" :in-theory (enable dkeys))))

(defthm dkeys-aux-definition
  (equal (dkeys-aux alist)
         (if (consp alist)
             (let ((key (caar alist)))
               (let ((r (alist::getv key alist)))
                 (append (list::map-cons key (dkeys r))
                         (dkeys-aux (alist::clr key alist)))))
           nil))
  :hints (("Goal" :in-theory (enable dkeys)))
  :rule-classes (:definition))

(defun dkeys-equiv-induction (alist y)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((r1 (alist::getv key alist))
              (r2 (alist::getv key y)))
          (append (dkeys-equiv-induction (cdr r1) (cdr r2))
                  (dkeys-equiv-induction (alist::clr key alist) (alist::clr key y)))))
    (list alist y)))

(defthm consp-reduction
  (implies
   (and
    (setequiv x y)
    (syntaxp (acl2::smaller-term y x)))
   (equal (consp x) (consp y)))
  :hints (("Goal" :in-theory (enable setequiv))))

(defthm dominated-by-some-map-cons
  (equal (dominated-by-some path (list::map-cons a list))
         (if (consp path) (and (equal (car path) a) (dominated-by-some (cdr path) list))
           nil))
  :hints (("Goal" :induct (list::map-cons a list)
           :in-theory (enable list::map-cons dominated-by-some))))

(defthm treequiv-aux-implies-setequiv-dkeys-aux
  (implies
   (treequiv-aux x y)
   (cpath::setequiv (dkeys-aux x)
                   (dkeys-aux y)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (consp-implies-memberp-caar
                                   BUDEQUIV-DEFINITION
                                   TREEQUIV-DEFINITION
                                   dkeys)
                                  (SETEQUIV-BY-MULTIPLICITY))
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :induct (dkeys-equiv-induction x y))))

(defthm treequiv-implies-setequiv-dkeys
  (implies
   (treequiv x y)
   (cpath::setequiv (dkeys x) (dkeys y)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable TREEQUIV-DEFINITION
                                     dkeys))))

(defund dkeyquiv (x y)
  (cpath::setequiv (dkeys x) (dkeys y)))

(defthm treequiv-implies-dkeyquiv
  (implies
   (treequiv x y)
   (dkeyquiv x y))
  :hints (("Goal" :in-theory (enable dkeyquiv)))
  :rule-classes (:forward-chaining))

(defthm setequiv-dkeys-to-dkeyquiv
  (equal (cpath::setequiv (dkeys x) (dkeys y))
         (dkeyquiv x y))
  :hints (("Goal" :in-theory (enable dkeyquiv))))

(defun map-append (path list)
  (if (consp path)
      (list::map-cons (car path)
                      (map-append (cdr path) list))
    list))

(defthm dominated-by-some-map-append
  (equal (dominated-by-some p1 (map-append p2 list))
         (and (dominates p2 p1)
              (dominated-by-some (nthcdr (len p2) p1) list)))
  :hints (("Goal" :in-theory (enable dominates))))

(defthm path-remove-nil-path
  (implies
   (not (consp path))
   (setequiv (path-remove path list) nil)))

(defthm open-dkeys-on-consp
  (implies
   (consp r)
   (equal (dkeys r)
          (IF (CONSP (CAR R))
              (LIST NIL)
              (DKEYS-AUX (CDR R)))))
  :hints (("Goal" :in-theory (enable dkeys))))

(defun dkey-rec (path r)
  (if (consp path)
      (if (consp (car r)) t
        (dkey-rec (cdr path) (alist::getv (car path) (cdr r))))
    nil))

(defthm open-dkey-rec-on-consp
  (implies
   (consp path)
   (equal (dkey-rec path r)
          (if (consp (car r)) t
            (dkey-rec (cdr path) (alist::getv (car path) (cdr r)))))))

(defun dkey-rec-2-path (path p2 r)
  (if (and (consp path) (consp p2))
      (if (consp (car r)) (list path p2 r)
        (dkey-rec-2-path (cdr path) (cdr p2) (alist::getv (car path) (cdr r))))
    nil))

(defun dkey-rec-induction-2 (path r1 r2)
  (if (consp path)
      (if (and (not (consp (car r1))) (memberp (car path) (alist::keys (cdr r1))))
          (dkey-rec-induction-2 (cdr path) (alist::getv (car path) (cdr r1)) (alist::getv (car path) (cdr r2)))
        (list path r1 r2))
    (list path r1 r2)))

(defthm cons-path-remove-reduction
  (implies
   (dominates p1 p2)
   (setequiv (cons p1 (path-remove p2 r))
             (cons p1 r)))
  :hints (("Goal" :in-theory (enable DOMINATED-BY-SOME))))

(defthm append-path-remove-reduction
  (implies
   (dominated-by-some p2 list)
   (setequiv (append list (path-remove p2 r))
             (append list r)))
  :hints (("Goal" :in-theory (enable DOMINATED-BY-SOME))))

(defthm path-remove-append
  (equal (path-remove path (append x y))
         (append (path-remove path x)
                 (path-remove path y)))
  :hints (("Goal" :in-theory (enable path-remove append))))

(defthm path-remove-map-cons
  (setequiv (path-remove path (list::map-cons a list))
            (if (consp path)
                (if (equal (car path) a)
                    (list::map-cons a (path-remove (cdr path) list))
                  (list::map-cons a list))
              nil))
  :hints (("Goal" :induct (list::map-cons a list)
           :in-theory (e/d (DOMINATED-BY-SOME path-remove list::map-cons)
                           (SETEQUIV-BY-MULTIPLICITY)))))

(defthm map-append-singleton
  (equal (map-append path (cons a nil))
         (list (append path a))))

(defthm not-memberp-clr
  (implies
   (not (memberp a (alist::keys alist)))
   (equal (alist::clr a alist)
          alist))
  :hints (("Goal" :in-theory (enable alist::keys alist::clr))))

(defthm not-consp-setequiv
  (implies
   (and
    (not (consp a))
    (syntaxp (or (not (quotep r))
                 (not (quotep a)))))
   (setequiv (cons a r)
             (cons nil nil))))

(defthm dkeys-aux-setv
  (setequiv (dkeys-aux (alist::setv a g alist))
            (append (list::map-cons a (dkeys g))
                    (dkeys-aux (alist::clr a alist))))
  :hints (("Goal" :in-theory (e/d (alist::getv alist::clr alist::setv)
                                  (setequiv-by-multiplicity)))))

(defun dkeys-aux-key-induction (alist)
  (if (consp alist)
      (dkeys-aux-key-induction (alist::clr (caar alist) alist))
    alist))

(defthm all-conses-dkeys-aux
  (all-conses (dkeys-aux alist))
  :hints (("Goal" :induct (dkeys-aux-key-induction alist))))

(defthm not-dominated-by-some-if-not-memberp
  (implies
   (not (memberp (car path) (alist::keys alist)))
   (not (dominated-by-some path (dkeys-aux alist)))))

(defthm path-remove-keys-reduction
  (implies
   (not (memberp (car path) (alist::keys alist)))
   (setequiv (path-remove path (dkeys-aux alist))
             (if (consp path)
                 (dkeys-aux alist)
               nil)))
  :hints (("Goal" :in-theory (disable SETEQUIV-BY-MULTIPLICITY
                              )
           :induct (dkeys-aux-key-induction alist))))

(defthm all-conses-map-cons
  (all-conses (list::map-cons a list)))

(defthm all-conses-implies-not-strictly-dominated-by-some-singleton
  (implies
   (all-conses list)
   (not (strictly-dominated-by-some (cons x nil) list)))
  :otf-flg t)

;; This was much harder than it seemingly should have been ..  (perhaps a
;; proof about dkeys-aux more directly would have been more efficient?)

#+joe
(defthm dkeys-aux-clr-to-path-remove-dkeys-aux
  (setequiv (dkeys-aux (alist::clr a alist))
            (path-remove (list a) (dkeys-aux alist)))
  :hints (("Goal" :induct (dkeys-aux-key-induction alist)
           :in-theory (enable consp-implies-memberp-caar alist::clr))
          (acl2::rewrite-equiv-hint setequiv)
          ("Subgoal *1/1" :cases ((equal (caar alist) a)))))

;;

;; (IN-THEORY (DISABLE OPEN-DKEYS-AUX-ON-MEMBERP-FREE))
;; (IN-THEORY (DISABLE DKEYS-AUX-CLR-TO-PATH-REMOVE-DKEYS-AUX))

#+joe
(defthm open-dkeys-aux-on-memberp-free
   (implies
    (and
     (memberp key list)
     (memberp key (alist::keys alist)))
    (cpath::setequiv (dkeys-aux alist)
                    (let ((r (alist::getv key alist)))
                      (append (list::map-cons key (dkeys r))
                              (dkeys-aux (alist::clr key alist)))))))

(defthm dkeys-sd
  (setequiv (dkeys (sd path u r))
            (cons path (dkeys r)))
  :hints (("Goal" :in-theory (enable u2g sd))))

(defund dkey (path r)
  (or (consp (car (gg path r)))
      (dkey-rec path r)))

;; A bit harder than (list::equiv ..)


(defthm dkey-sd
  (equal (dkey p1 (sd p2 u r))
         (or (dominates p2 p1)
             (dkey p1 r)))
  :hints (("Goal" :in-theory (enable STRICTLY-DOMINATES dkey u2g sd))))

(defund g2u (g)
  (depset g))

(defthm u2g-g2u
  (setequiv (g2u (u2g u)) u)
  :hints (("Goal" :in-theory (enable depset g2u u2g))))

(local
 (defthm gg-of-sd-helper
   (IMPLIES (AND (NOT (LIST::EQUIV GP SP))
                 (DOMINATES SP GP))
            (NOT (GG (NTHCDR (LEN SP) GP) (U2G U))))
   :hints (("Goal" :expand (GG GP (LIST (LIST U)))
            :in-theory (enable dominates u2g)))))

(defthm gg-of-sd
  (equal (gg gp (sd sp u r))
         (if (diverge gp sp)
             (gg gp r)
           (if (dominates gp sp)
               (sd (nthcdr (len gp) sp) u (gg gp r))
             nil)))
  :hints (("Goal" :in-theory (enable gg sd))))

(defthm consp-car-sd
  (equal (consp (car (sd path u r)))
         (implies (consp path) (consp (car r))))
  :hints (("Goal" :in-theory (enable U2G sd))))

(defthm consp-car-sg
  (equal (consp (car (sg path g r)))
         (if (consp path) (consp (car r))
           (consp (car g)))))

(defthm depset-u2g
  (equal (depset (u2g u)) u)
  :hints (("Goal" :in-theory (enable depset u2g))))

;;
;; Default graph
;;

(defun default-graph () nil)

(defthm gg-default-graph
  (equal (gg path (default-graph)) (default-graph)))

(defthm depset-default-graph
  (equal (depset (default-graph)) nil))

(defthm dkey-default-graph
  (equal (dkey path (default-graph)) nil)
  :hints (("Goal" :in-theory (enable dkey))))

(defthm dkeys-default-graph
  (equal (dkeys (default-graph)) nil))

(defthm car-default-graph
  (equal (car (default-graph)) nil))

(in-theory (disable default-graph))
(in-theory (disable (default-graph)))
(in-theory (disable (:type-prescription default-graph)))

(in-theory (disable gg sg))
(in-theory (disable (u2g)))

#|
(defthm not-dkey-implications
  (implies
   (and
    (not (dkey path g))
    (or (diverges-from-all path (dkeys g))
        (dominates-all path (dkeys g))))))

;; Proof follows from gwv-clrp
(defthm gp-over-foo
  (implies
   (or (diverges-from-all path (dkeys g))
       (dominates-all path (dkeys g)))
   (equal (gp path (foo io))
          (gp path io))))

;; We prove this theorem by cases:
(defthm gwv-r1
  (implies
   (stequiv (dia path (gr io1)) io1 io2)
   (equal (gp path (foo io1))
          (gp path (foo io2)))))

;; Proof via workhorse directly
(defthm gwv-r1-1
  (implies
   (dkey path (gr io1))
   (stequiv (dia path (gr io1)) io1 io2)
   (equal (gp path (foo io1))
          (gp path (foo io2)))))

;; Proof via dkey-characterization and workhorse
(defthm gwv-r1-2
  (implies
   (and
    (dkey path (gr io2))
    (stequiv (dia path (gr io1)) io1 io2))
   (equal (gp path (foo io1))
          (gp path (foo io2)))))

;; Proof via gp-over-foo and not-dkey-implications
(defthm gwv-r1-3
  (implies
   (and
    (not (dkey path (gr io1)))
    (not (dkey path (gr io2)))
    (stequiv (dia path (gr io1)) io1 io2))
   (equal (gp path (foo io1))
          (gp path (foo io2)))))

|#

 #|

;; push
(defthmd treesubp-keyed-aux-over-remove
  (implies
   (treesubp-pred a alist1 alist2)
   (equal (treesubp-keyed-aux (remove a key) alist1 alist2)
          (treesubp-keyed-aux key alist1 alist2)))
  :hints (("goal" :in-theory (disable treesubp))))

(defthmd treesubp-keyed-aux-over-clr
  (implies
   (treesubp-pred a alist1 alist2)
   (equal (treesubp-keyed-aux key (alist::clr a alist1) (alist::clr a alist2))
          (treesubp-keyed-aux key alist1 alist2)))
  :hints (("goal" :in-theory (disable treesubp))))

(defthmd open-treesubp-keyed-aux-on-memberp
  (implies
   (memberp a keys)
   (equal (treesubp-keyed-aux keys alist1 alist2)
          (and (treesubp-pred a alist1 alist2)
               (treesubp-keyed-aux (remove a keys) (alist::clr a alist1) (alist::clr a alist2)))))
  :hints (("Goal" :in-theory (e/d (treesubp-keyed-aux-over-remove treesubp-keyed-aux-over-clr)
                                  (treesubp)))))

(defthm treesubp-from-implications-1
  (implies
   (and (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
        (all-dominated-by-some (caar r1) (caar r2))
        (consp (car r2))
        (treesubp-aux (cdr r1) (cdr r2)))
   (treesubp r1 r2))
  :rule-classes (:forward-chaining))

(defthm treesubp-from-implications-2
  (implies
   (and (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
        (all-dominated-by-some (caar r1) (caar r2))
        (not (consp r1))
        (treesubp-aux (cdr r1) (cdr r2)))
   (treesubp r1 r2))
  :rule-classes (:forward-chaining))


(defthm treesubp-forward-1
  (implies
   (treesubp r1 r2)
   (and (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
        (all-dominated-by-some (caar r1) (caar r2))
        (treesubp-aux (cdr r1) (cdr r2))))
  :rule-classes (:forward-chaining))

(defthm treesubp-forward-2
  (implies
   (and
    (treesubp r1 r2)
    (consp (car r1)))
   (consp (car r2)))
  :rule-classes (:forward-chaining))

(defthm treesubp-aux-implies-treesubp-keyed-aux
  (implies
   (treesubp-aux alist1 alist2)
   (treesubp-keyed-aux (alist::keys alist1) alist1 alist2))
  :rule-classes (:forward-chaining))

(defthmd open-treesubp-aux-on-memberp
  (implies
   (memberp a (alist::keys alist1))
   (equal (treesubp-aux alist1 alist2)
          (and (treesubp-pred a alist1 alist2)
               (treesubp-aux (alist::clr a alist1) (alist::clr a alist2)))))
  :hints (("Goal" :in-theory (enable open-treesubp-keyed-aux-on-memberp))))

(defun treesubp-aux-induction-3 (x y z)
  (if (and (consp x) (memberp (caar x) (alist::keys y)))
      (let ((key (caar x)))
        (and (treesubp-pred key x y)
             (treesubp-pred key y z)
             (cons
              (treesubp-aux-induction-3 (cdr (alist::getv key x)) (cdr (alist::getv key y)) (cdr (alist::getv key z)))
              (treesubp-aux-induction-3 (alist::clr key x) (alist::clr key y) (alist::clr key z)))))
    (list x y z)))

(defthmd consp-implies-memberp-caar-forward
  (implies
   (consp x)
   (memberp (caar x) (alist::keys x)))
  :rule-classes (:forward-chaining))

(defthm treesubp-aux-chaining
  (implies
   (and
    (subsetp (alist::keys x) (alist::keys y))
    (subsetp (alist::keys y) (alist::keys z))
    (treesubp-aux x y)
    (treesubp-aux y z))
   (treesubp-aux x z))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (consp-implies-memberp-caar-forward
                            open-treesubp-aux-on-memberp)
                           (treesubp-aux-to-treesubp-keyed-aux))
           :induct (treesubp-aux-induction-3 x y z))))

(defthm treesubp-chaining-1
  (implies
   (and
    (treesubp x y)
    (treesubp y z))
   (treesubp x z))
  :rule-classes (:forward-chaining))

(defthm treesubp-chaining-2
  (implies
   (and
    (treesubp y z)
    (treesubp x y))
   (treesubp x z))
  :rule-classes (:forward-chaining))

(defthm treesubp-keyed-aux-memberp-implications
  (implies
   (and
    (treesubp-keyed-aux keys alist1 alist2)
    (memberp a keys))
   (TREESUBP (ALIST::GETV a alist1) (ALIST::GETV a alist2)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (disable TREESUBP))))

(defthm treesubp-definition
  (equal (treesubp r1 r2)
         (and (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
              (all-dominated-by-some (caar r1) (caar r2))
              (implies (consp (car r1)) (consp (car r2)))
              (treesubp-keyed-aux (alist::keys (cdr r1)) (cdr r1) (cdr r2)))))


(defun subleafp (path r1 r2)
  (and (all-dominated-by-some (caar r1) (caar r2))
       (implies (consp (car r1)) (consp (car r2)))
       (subsetp (alist::keys (cdr r1)) (alist::keys (cdr r2)))
       (if (and (consp path) (memberp (car path) (alist::keys (cdr r1))))
           (and (memberp (car path) (alist::keys (cdr r2)))
                (subleafp (cdr path) (alist::getv (car path) (cdr r1))
                          (alist::getv (car path) (cdr r2))))
         t)))

(defthm subleafp-id
  (subleafp path x x))

(defthm subleafp-chaining-1
  (implies
   (and
    (subleafp path x y)
    (subleafp path y z))
   (subleafp path x z))
  :rule-classes (:forward-chaining))

(defthm subleafp-chaining-2
  (implies
   (and
    (subleafp path y z)
    (subleafp path x y))
   (subleafp path x z))
  :rule-classes (:forward-chaining))

(defthm subleaf-dominance-chaining-1
  (implies
   (and
    (dominates p2 p1)
    (subleafp p1 x y))
   (subleafp p2 x y))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable dominates))))

(defthm subleaf-dominance-chaining-2
  (implies
   (and
    (subleafp p1 x y)
    (dominates p2 p1))
   (subleafp p2 x y))
  :rule-classes (:forward-chaining))

(defthm treesubp-implies-subleafp
  (implies
   (treesubp r1 r2)
   (subleafp path r1 r2))
  :hints (("Goal" :in-theory (disable treesubp-definition treesubp))))

(defthm treesubp-id
  (treesubp x x)
  :hints (("Goal" :in-theory (disable treesubp treesubp-definition))))

(defun treequiv (r1 r2)
  (and (treesubp r1 r2)
       (treesubp r2 r1)))

(in-theory (disable treesubp treesubp-definition))

DAG
;; Budcount:

(defund bud (u) (if (consp u) 1 0))

(defthm natp-bud
  (natp (bud u)))

(defun budcount-aux (alist)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((r (alist::getv key alist)))
          (+ (bud (car r))
             (budcount-aux (cdr r))
             (budcount-aux (alist::clr key alist)))))
    0))

(defthm natp-budcount-aux
  (natp (budcount-aux alist)))

(defund budcount (r)
  (+ (bud (car r)) (budcount-aux (cdr r))))

(defthm open-budcount-on-cons
  (implies
   (consp r)
   (equal (budcount r)
          (+ (bud (car r)) (budcount-aux (cdr r)))))
  :hints (("Goal" :in-theory (enable budcount))))

(defthm natp-budcount
  (natp (budcount r)))

(defthmd budcount-aux-definition
  (equal (budcount-aux alist)
         (if (consp alist)
             (let ((key (caar alist)))
               (let ((r (alist::getv key alist)))
                 (+ (budcount r)
                    (budcount-aux (alist::clr key alist)))))
           0))
  :hints (("Goal" :in-theory (enable budcount)))
  :rule-classes (:definition))

;; Now rules about budcount and sg:

(defthm budcount-aux-setv
  (equal (budcount-aux (alist::setv a g r))
         (+ (budcount g)
            (- (budcount-aux r)
               (budcount (alist::getv a r)))))
  :hints (("Goal" :in-theory (enable budcount-aux-definition
                                     alist::clr alist::getv alist::setv))))

(defthm budcount-sg
  (equal (budcount (sg path g1 r))
         (+ (budcount g1)
            (- (budcount r) (budcount (gg path r)))))
  :hints (("Goal" :induct (sg path g1 r))
          (and stable-under-simplificationp
               '(:expand (BUDCOUNT R)))))

(defund clrg (path r)
  (sg path nil r))

(defthm budcount-clrg
  (equal (budcount (clrg path r))
         (- (budcount r) (budcount (gg path r))))
  :hints (("Goal" :in-theory (enable clrg))))

(defthm clrg-definition
  (equal (clrg path r)
         (if (consp path)
             (cons (car r) (alist::setv (car path) (clrg (cdr path) (alist::getv (car path) (cdr r))) (cdr r)))
           nil))
  :hints (("Goal" :in-theory (enable clrg)))
  :rule-classes (:definition))

(defthm open-clrg-on-consp
  (implies
   (consp path)
   (equal (clrg path r)
          (cons (car r) (alist::setv (car path) (clrg (cdr path) (alist::getv (car path) (cdr r))) (cdr r))))))

;; dkeyquiv

(defun subdep-aux (alist zlist)
  (if (consp alist)
      (let ((key (caar alist)))
        (let ((ra (alist::getv key alist))
              (rz (alist::getv key zlist)))
          (and (equal (consp (car ra)) (consp (car rz)))
               (cpath::setequiv (caar ra) (caar rz))
               (subdep-aux (cdr ra) (cdr rz))
               (subdep-aux (alist::clr key alist) zlist))))
    t))

(defund subdep (ra rz)
  (and (equal (consp (car ra)) (consp (car rz)))
       (cpath::setequiv (caar ra) (caar rz))
       (subdep-aux (cdr ra) (cdr rz))))

(defun subdep-aux-definition
  (equal (subdep-aux alist zlist)
         (if (consp alist)
             (let ((key (caar alist)))
               (let ((ra (alist::getv key alist))
                     (rz (alist::getv key zlist)))
                 (and (subdep ra rz)
                      (subdep-aux (alist::clr key alist) zlist))))
           t)))

;;
;; depset
;;

(local (in-theory (disable LIST::SETEQUIV-APPEND-REDUCTION-1)))
(local (in-theory (enable LIST::MEMBERP-OF-APPEND)))
(local (in-theory (enable memberp)))

(defthm
  (implies
   (cpath::setequiv (caar (gp path a1)) (caar (gp path a2)))
   (cpath::setequiv (depset-aux a1) (depset-aux a2))))

(defthm depset-aux-definition
  (equal (depset-aux alist)
         (if (consp alist)
             (let ((key (caar alist)))
               (let ((r (alist::getv key alist)))
                 (append (depset r)
                         (depset-aux (alist::clr key alist)))))
           nil))
  :hints (("Goal" :in-theory (enable depset)))
  :rule-classes (:definition))

(defun depset-keyed-aux-cdr (def use alist)
  (if (consp use)
      (let ((key (car use)))
        (if (memberp key def)
            (depset-keyed-aux-cdr def (cdr use) alist)
          (let ((r (alist::getv key alist)))
            (append (depset r) (depset-keyed-aux-cdr (cons key def) (cdr use) alist)))))
    nil))

(defthmd depset-keyed-aux-cdr-remove
  (implies
   (memberp key def)
   (equal (depset-keyed-aux-cdr def (remove key use) alist)
          (depset-keyed-aux-cdr def use alist)))
  :hints (("Goal" :in-theory (enable remove))))

(defun depset-keyed-aux (def use alist)
  (if (consp use)
      (let ((key (car use)))
        (if (memberp key def)
            (depset-keyed-aux def (remove (car use) use) alist)
          (let ((r (alist::getv key alist)))
            (append (depset r) (depset-keyed-aux (cons key def) (remove (car use) use) alist)))))
    nil))

(defthmd depset-keyed-aux-to-depset-keyed-aux-cdr
  (equal (depset-keyed-aux def use alist)
         (depset-keyed-aux-cdr def use alist))
  :hints (("Goal" :in-theory (enable depset-keyed-aux-cdr-remove))))

(defthmd depset-keyed-aux-remove
  (implies
   (memberp key def)
   (equal (depset-keyed-aux def (remove key use) alist)
          (depset-keyed-aux def use alist)))
  :hints (("Goal" :in-theory (enable
                              depset-keyed-aux-cdr-remove
                              depset-keyed-aux-to-depset-keyed-aux-cdr
                              ))))

(defthm open-depset-keyed-aux-on-consp
  (implies
   (consp use)
   (equal (depset-keyed-aux def use alist)
          (let ((key (car use)))
            (if (memberp key def)
                (depset-keyed-aux def (remove (car use) use) alist)
              (let ((r (alist::getv key alist)))
                (append (depset r) (depset-keyed-aux (cons key def) (remove (car use) use) alist))))))))


(defun depset-keyed-aux-2d (d1 def use alist)
  (if (consp use)
      (let ((key (car use)))
        (if (memberp key def)
            (depset-keyed-aux-2d d1 def (remove (car use) use) alist)
          (let ((r (alist::getv key alist)))
            (append (depset r) (depset-keyed-aux-2d (cons key d1) (cons key def) (remove (car use) use) alist)))))
    (list d1 def use alist)))

(defcong list::setequiv equal (depset-keyed-aux def use alist) 1
  :hints (("Goal" :induct (depset-keyed-aux-2d LIST::DEF-EQUIV DEF USE ALIST))
          (and stable-under-simplificationp
               '(:in-theory (enable list::setequiv)))))

(defthmd depset-keyed-aux-clr
  (implies
   (memberp key def)
   (equal (depset-keyed-aux def use (alist::clr key alist))
          (depset-keyed-aux def use alist))))

(defthm disjoint-subset-chaining
  (implies
   (and
    (bag::disjoint x y)
    (list::subsetp z y))
   (bag::disjoint x z))
  :hints (("Goal" :in-theory (enable bag::disjoint list::subsetp))))

(defun depset-aux-to-depset-keyed-aux-induction (def alist)
  (if (consp alist)
      (let ((key (caar alist)))
        (depset-aux-to-depset-keyed-aux-induction (cons key def) (alist::clr key alist)))
    (list def alist)))

(defthmd depset-keyed-aux-to-depset-aux
  (implies
   (bag::disjoint def (alist::keys alist))
   (cpath::setequiv (depset-keyed-aux def (alist::keys alist) alist)
                   (depset-aux alist)))
  :hints (("Goal" :in-theory (enable depset-keyed-aux-clr depset-keyed-aux-remove BAG::DISJOINT ALIST::KEYS)
           :expand ((ALIST::KEYS ALIST) (DEPSET-AUX ALIST))
           :induct (depset-aux-to-depset-keyed-aux-induction def alist))))

;; Now we can prove our interesting theorems about the more congenial
;; depset-keyed-aux function.

(defthm open-depset-on-consp
  (implies
   (consp r)
   (cpath::setequiv (depset r)
                   (append (caar r) (depset-keyed-aux nil (alist::keys (cdr r)) (cdr r)))))
  :hints (("Goal" :in-theory (e/d
                              (bag::disjoint
                               depset-keyed-aux-to-depset-aux
                               depset
                               )))))

(LOCAL (INCLUDE-BOOK "../util/rewrite-equiv"))
;;
;; The issues above occured because the wrong setequiv was being used.

(defthm open-depset-keyed-aux-on-member
  (implies
   (and
    (memberp a (alist::keys r))
    (not (memberp a def))
    (memberp a use))
   (cpath::setequiv (depset-keyed-aux def use r)
                   (append (depset (alist::getv a r))
                           (depset-keyed-aux (cons a def) use r))))
  :hints (("Goal" :induct (depset-keyed-aux def use r)
           :in-theory (disable LIST::SETEQUIV-BY-MULTIPLICITY))
          (acl2::rewrite-equiv-hint list::setequiv)))

DAG

(defthm depset-keyed-aux-setv
  (list::setequiv (depset-keyed-aux def use (alist::setv a g r))
                  (if (or (memberp a def)
                          (not (memberp a use)))
                      (depset-keyed-aux def use r)
                    (append (depset g)
                            (depset-keyed-aux (cons a def) use r))))
  :hints (("Goal" :in-theory (enable alist::setv))))


DAG
(defthm depset-clrg
  (list::setequiv (depset (clrg path r))
                  (list::remove-list (depset (gg path r)) (depset r)))
  :hints (("Goal" :induct (gg path r)
           :expand (depset r))))

DAG

(defthm depset-aux-setv
  (list::setequiv (depset-aux keys (alist::setv a r alist))
                  (if (memberp a keys)
                      (depset-aux keys alist)
                    (append (depset r)
                            (depset-aux (cons a keys) alist))))
  :hints (("Goal" :in-theory (enable alist::setv))))

(defthm depset-sg
  (list::setequiv (depset (sg path g r))
                  (append (depset g)
                          (depset (clrg path r))))
  :hints (("Goal" :induct (sg path g1 r))))


;;
;; I think this is the notion we want.
;;

(defun treequiv (g1 g2)
  (and (equal (budcount g1) (budcount g2))
       (list::setequiv (depset g1) (depset g2))))

(defun treequiv (g1 g2)
  (forall (path):
    (and (equal (bud (car (gp path g1))) (bud (car (gp path g2))))
         (list::setequiv (car (gp path g1)) (car (gp path g2))))))

DAG

;; OK .. now we need to strengthen it to talk about budcount

(defun budcount (r)
  (+ (budcount-aux (cdr r))
     (if (consp (car r)) 1 0)))

(defun budcount-aux (alist)
  (if (consp alist)
      (+ (budcount (cdar alist))
         (budcount-aux (alist::clr (caar alist) alist)))
    0))

;; If there are no buds beyond a certain point, that portion of the
;; tree can be ignored (it is dead).  Our collection functions should
;; respect dead branches.

;; Budcount equivalence is very strong.
;;
;; We should have a notion of dependency that is similarly strong.
;; It can use "budcount" to ignore dead branches of the tree without
;; requiring the "default" value we carry along in "ddeps"




;; If two trees have budcounts that are exactly the same for every
;; possible path, the trees have similar "dep" structure.  (key
;; membership properties and all).

;; Leaf count is somewhat more difficult.  It doesn't decrease in the
;; nice linear way budcount does .. it jumps around a lot more.  It
;; is more like

(defthm
  (implies
   (bag::unique keys)
   ..))

DAG
(defthm hack1
 (IMPLIES (AND (NOT (ALL-DOMINATED-BY-SOME (CAAR R1)
                                          (CAAR R2)))
              (DIVERGE P1 P2))
         (NOT (SUBLEAFP P1 (SG P2 G1 R1)
                        (SG P2 G2 R2))))
 :hints (("Goal" :cases ((consp p2)))))

(defthm open-sg-on-consp
  (implies
   (consp path)
   (equal (sg path g r)
          (CONS (CAR R)
                         (ALIST::SETV (CAR PATH)
                                      (SG (CDR PATH)
                                          G (ALIST::GETV (CAR PATH) (CDR R)))
                                      (CDR R))))))



(defun 2-path-induction (p1 p2 r)
  (if (and (consp p1)
           (consp p2))
      (2-path-induction (cdr p1) (cdr p2) (alist::getv (car p1) (cdr r)))
    (list p1 p2 r)))

(defthm open-diverge-on-consp-1
  (implies
   (consp x)
   (equal (diverge x y)
          (and (consp y)
               (if (equal (car x) (car y))
                   (diverge (cdr x) (cdr y))
                 t)))))

(defthm open-diverge-on-consp-2
  (implies
   (consp y)
   (equal (diverge x y)
          (and (consp x)
               (if (equal (car x) (car y))
                   (diverge (cdr x) (cdr y))
                 t)))))

(defthm open-subleafp-on-consp
  (implies
   (consp path)
   (equal (subleafp path r1 r2)
          (AND (ALL-DOMINATED-BY-SOME (CAAR R1)
                                              (CAAR R2))
                       (IMPLIES (CONSP (CAR R1))
                                (CONSP (CAR R2)))
                       (SUBSETP (ALIST::KEYS (CDR R1))
                                (ALIST::KEYS (CDR R2)))
                       (IF (AND (CONSP PATH)
                                (MEMBERP (CAR PATH)
                                         (ALIST::KEYS (CDR R1))))
                           (AND (MEMBERP (CAR PATH)
                                         (ALIST::KEYS (CDR R2)))
                                (SUBLEAFP (CDR PATH)
                                          (ALIST::GETV (CAR PATH) (CDR R1))
                                          (ALIST::GETV (CAR PATH) (CDR R2))))
                           T)))))

(defun 2-path-2-state-induction (p1 p2 r1 r2)
  (if (and (consp p1)
           (consp p2)
           (equal (car p1) (car p2)))
      (2-path-2-state-induction (cdr p1) (cdr p2) (alist::getv (car p2) (cdr r1)) (alist::getv (car p2) (cdr r2)))
    (list p1 p2 r1 r2)))

;; Your induction is not strong enough.

(defthm subleafp-diverge-sg
  (implies
   (diverge p1 p2)
   (equal (subleafp p1 (sg p2 g1 r1) r2)
          (subleafp p1 (delete p2 r1) r2)
          (and (subleafp (common-prefix p1 p2) r1 r2)
               (let ((root (common-prefix p1 p2)))
                 (and (subleafp (nthcdr (len root) p1) (gg root r1) (gg root r2))
                      (subleafp (nthcdr (len root) p2) (gg root r1) (gg root r2)))))))
  :hints (("Goal" :induct (2-path-2-state-induction p1 p2 r1 r2)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))
          (and stable-under-simplificationp
               '(:cases ((consp p1) (consp p2))))
          ))


(defthmd sp-of-sp-value
  (treequiv (sg p1 (sg p2 v r2) r1)
            (sg (append p1 p2) v (sg p1 r2 r1)))
  :hints (("Goal" :in-theory (enable sp))))

(defun 2-path-induction (p1 p2 r)
  (if (and (consp p1)
           (consp p2))
      (2-path-induction (cdr p1) (cdr p2) (alist::getv (car p1) (cdr r)))
    (list p1 p2 r)))

(defthm sp-dominates-sp
  (implies
   (dominates p1 p2)
   (treequiv (sg p1 v1 (sg p2 v2 r))
             (sg p1 v1 r)))
  :hints (("Goal" :induct (2-path-induction p1 p2 r))))

(defthm sp-dominated-by-sp
  (implies
   (dominates p2 p1)
   (equal (sp p1 v1 (sp p2 v2 r))
          (sp p2 (sp (nthcdr (len p2) p1) v1 v2) r)))
  :hints (("Goal" :induct (2-path-induction p1 p2 r))))

(defthm sp-diverge-sp
  (implies
   (diverge p1 p2)
   (equal (sp p1 v1 (sp p2 v2 r))
          (sp p2 v2 (sp p1 v1 r))))
  :hints (("Goal" :induct (2-path-induction p1 p2 r)))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))

(defun exceeds (path r)
  (if (consp path)
      (if (consp r)
          (let ((a     (car path))
                (alist (cdr r))
                (path  (cdr path)))
            (and (memberp a (alist::keys alist))
                 (exceeds path (alist::getv a alist))))
        t)
    nil))

(defun exceeds-aux (a path alist)
  (if (consp alist)
      (let ((key  (caar alist))
            (getv (cdar alist)))
        (if (equal key a)
            (exceeds path getv)
          (exceeds-aux a path (cdr alist))))
    nil))

(defthmd open-getv-on-consp
  (implies
   (consp alist)
   (equal (alist::getv a alist)
          (if (equal a (caar alist))
              (cdar alist)
            (alist::getv a (cdr alist)))))
  :hints (("Goal" :in-theory (enable alist::getv))))

(defthmd open-aux-to-exceeds
  (equal (exceeds-aux a path alist)
         (and (memberp a (alist::keys alist))
              (exceeds path (alist::getv a alist))))
  :hints (("Goal" :in-theory (enable open-getv-on-consp))))

(defthm open-exceeds-to-aux
  (equal (exceeds path r)
         (if (consp path)
             (if (consp r)
                 (let ((a     (car path))
                       (alist (cdr r))
                       (path  (cdr path)))
                   (exceeds-aux a path alist))
               t)
           nil))
  :hints (("Goal" :in-theory (enable open-aux-to-exceeds)))
  :rule-classes nil)

(defthm exceeds-aux-definition
  (equal (exceeds-aux a path alist)
         (if (consp alist)
             (let ((key  (caar alist))
                   (r    (cdar alist)))
               (if (equal key a)
                   (if (consp path)
                       (if (consp r)
                           (let ((a     (car path))
                                 (alist (cdr r))
                                 (path  (cdr path)))
                             (exceeds-aux a path alist))
                         t)
                     nil)
                 (exceeds-aux a path (cdr alist))))
           nil))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory nil
           :expand (exceeds-aux a path alist)
           :use (:instance open-exceeds-to-aux
                           (r (cdar alist))))))

;; The question is whether you want to collect information along the path.
;; Eventually you are considering returning the default payload.  Perhaps your
;; initial default payload should be the path itself.
;;
;; We could be more rigorous and have an equivalent (reduced) tree in which we
;; collapse the empty branches.  The "setp" test would establish whether any
;; dominated subtree had, in fact, been set.  If not, we would return our
;; default payload.  The default payload would be replaced incrementally each
;; time we encounter a new set element.  In the end, if the leaf element has
;; been set, we return that set plus the set of every dominated tree.

(defun unsetp-aux (alist)
  (if (consp alist)
      (let ((r (cdar alist)))
        (and (not (consp (car r)))
             (unsetp-aux (cdr r))
             (unsetp-aux (alist::clr (caar alist) alist))))
    t))

(defun unsetp (r)
  (and (not (consp (car r)))
       (unsetp-aux (cdr r))))

(defthm unsetp-aux-implies-unsetp-aux-assoc
  (implies
   (unsetp-aux alist)
   (unsetp-aux (cddr (assoc a alist)))))

(defthm unsetp-aux-implies-not-consp-cadr-assoc
  (implies
   (unsetp-aux alist)
   (not (consp (cadr (assoc a alist))))))

(defthm unsetp-aux-implies-unsetp-aux-clrp
  (implies
   (unsetp-aux alist)
   (unsetp-aux (alist::clr a alist))))

(defthm unsetp-implies-unsetp-getv
  (implies
   (unsetp r)
   (unsetp (alist::getv a (cdr r))))
  :hints (("Goal" :in-theory (enable alist::getv))))

(defthm unsetp-aux-setv
  (implies
   (unsetp-aux r)
   (equal (unsetp-aux (alist::setv a g r))
          (unsetp g)))
  :hints (("Goal" :in-theory (enable alist::setv))))

(defthm unsetp-cons
  (equal (unsetp (cons u a))
         (and (not (consp u))
              (unsetp-aux a))))

;;
;; unsetp over sg
;;
(defthm unsetp-sg
  (implies
   (unsetp r)
   (equal (unsetp (sg path g r))
          (unsetp g)))
  :hints (("Goal" :in-theory (disable unsetp)
           :induct (sg path g r))))

;;
;; treeset
;;

(defun treeset-aux (alist)
  (declare (xargs :measure (acl2-count alist)))
  (if (consp alist)
      (let ((r (cdar alist)))
        (append (caar r)
                (treeset-aux (cdr r))
                (treeset-aux (alist::clr (caar alist) alist))))
    nil))

(defun treeset (r)
  (append (caar r) (treeset-aux (cdr r))))

(in-theory (disable SETEQUIV-BY-MULTIPLICITY))

(defthm unsetp-aux-treeset-aux
  (implies
   (unsetp-aux alist)
   (equal (treeset-aux alist) nil)))

(defthm unsetp-treeset
  (implies
   (unsetp r)
   (equal (treeset r) nil)))

(defthm treeset-cons
  (equal (treeset (cons s a))
         (append (car s) (treeset-aux a))))

(defthm treeset-aux-setv
  (cpath::setequiv (treeset-aux (alist::setv a g r))
                  (append (treeset g)
                          (treeset-aux (alist::clr a r))))
  :hints (("Goal" :in-theory (enable alist::setv))))

(defun tree-remove (path r)
  (if (consp path)
      (cons (car r)
            (alist::setv (car path) (tree-remove (cdr path) (alist::getv (car path) (cdr r)))
                         (cdr r)))
    nil))


(defthm treeset-sg
  (cpath::setequiv (treeset (sg path g r))
                  (append (treeset g)
                          (treeset (tree-remove path r))))
  :hints (("Goal" :in-theory (disable unsetp treeset) :induct (sg path g r))
          (acl2::rewrite-equiv-hint cpath::setequiv)))


;; We now need an equivalence relation over graphs
;; that will provide us with some more powerful rewrite rules.


   DAG

(defthm dom-deps-sg
  (cpath::setequiv (dom-deps path1 d (sg path2 g r))
                  (if (diverge path1 path2)
                      (dom-deps path1 d r)
                    (if (dominates path2 path1)
                        (dom-deps (nthcdr (len path2) path1) (caar g) g)
                      (dom-deps path1 d r)))))

(defthm non-memberp-not-exceeds
  (implies
   (not (memberp a (alist::keys list)))
   (not (exceeds-aux a path list))))

(defthm not-getv-exceeds
  (implies
   (and
    (consp path)
    (memberp a (alist::keys r))
    (not (consp (ALIST::GETV a r))))
   (exceeds-aux a path r)))



(defthm open-keys
  (implies
   (consp alist)
   (equal (alist::keys alist)
          (cons (caar alist)
                (alist::keys (cdr alist))))))

(defthm exceeds-to-exceeds-aux
  (equal (exceeds-aux a path alist)
         (exceeds (cons a path) (cons nil alist)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable memberp)
           :induct (exceeds-aux a path alist))))


(defun deps (alist)
  (if (consp alist)
      (let ((key (car alist))
            (rec (cdr alist)))
        (if (consp rec)
            (append (car rec)
                    (deps (cdr rec))
                    (deps (cdr alist)))
          (deps (cdr alist))))
    nil))



(defun keys-aux (alist)
  (if (consp alist)
      (let ((key (car alist))
            (rec (cdr alist)))
        (if (consp rec)
            (append (list::map-cons key (keys-aux (cdr rec)))
                    (keys-aux (cdr alist)))
          (cons (list key)
                (keys-aux (cdr alist)))))
    nil))

;; When we do "get-deps", should we accumulate dominating dependencies along
;; with way?  What would that complicate?  It would allow us to define increasing
;; levels of dependency .. Does GWV support this notion?
;;
;; No .. this flies in the face of our notion of dependency.

;; Pick-a-point: Prove that the dtrees are "the same" for every possible path.
;; - the existence of the path is the same
;; - the value stored on the path is the same

;; I think it might be ugly to support "overlay" (?)

;; Or perhaps that is just the way it should work (we always leave a chunk of
;; our path along the way)?

(defun keys (x) (keys-aux (cdr x)))
(defun deps (x) (append (car x) (deps-aux (cdr x))))

(defun equiv (x y)
  (and (setequiv (keys x) (keys y))
       (getequiv (keys x) x y)
       (getequiv (keys y) y x)))

(defun gaux (path alist)
  (if (consp path)


(defthm gg-of-sg
  (equal (gg p1 (sg p2 g r))
         (if (diverge p1 p2)
             (gg p1 r)
           (if (dominates p1 p2)
               (sg (nthcdr (len p1) p2) (cdr (gg p1 r)))
             (gg (nthcdr (len p2) p1) (cdr g))))))
|#

(local (in-theory (enable DOMINATED-BY-SOME)))

;; dominated-by-some     <-> memberp
;; all-dominated-by-some <-> subsetp

(defthm dominated-by-some-from-dominated-by-some-all-dominated-by-some
  (implies
   (and
    (all-dominated-by-some x y)
    (dominated-by-some path x))
   (dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm all-dominated-by-some-chaining-1
  (implies
   (and
    (all-dominated-by-some x y)
    (all-dominated-by-some y z))
   (all-dominated-by-some x z))
  :rule-classes (:rewrite :forward-chaining))

(defthm all-dominated-by-some-chaining-2
  (implies
   (and
    (all-dominated-by-some y z)
    (all-dominated-by-some x y))
   (all-dominated-by-some x z))
  :rule-classes (:rewrite :forward-chaining))

(local (in-theory (enable strictly-dominated-by-some)))

(defthm strictly-dominates-from-dominates-strictly-dominates-1
  (implies
   (and
    (strictly-dominates x path)
    (dominates a x))
   (strictly-dominates a path))
  :hints (("Goal" :in-theory (enable strictly-dominates)))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-dominates-strictly-dominates-2
  (implies
   (and
    (dominates a x)
    (strictly-dominates x path))
   (strictly-dominates a path))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-strictly-dominates-dominates-1
  (implies
   (and
    (dominates x path)
    (strictly-dominates a x))
   (strictly-dominates a path))
  :hints (("Goal" :in-theory (enable strictly-dominates)))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-strictly-dominates-dominates-2
  (implies
   (and
    (strictly-dominates a x)
    (dominates x path))
   (strictly-dominates a path))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominated-by-some-from-strictly-dominated-dominated-by-some-1
  (implies
   (and
    (strictly-dominates x path)
    (dominated-by-some x list))
   (strictly-dominated-by-some path list))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominated-by-some-from-strictly-dominated-dominated-by-some-2
  (implies
   (and
    (dominated-by-some x list)
    (strictly-dominates x path))
   (strictly-dominated-by-some path list))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominated-by-some-from-striclty-dominated-by-some-all-dominated-by-some-1
  (implies
   (and
    (all-dominated-by-some x y)
    (strictly-dominated-by-some path x))
   (strictly-dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm strictly-dominated-by-some-from-striclty-dominated-by-some-all-dominated-by-some-2
  (implies
   (and
    (strictly-dominated-by-some path x)
    (all-dominated-by-some x y))
   (strictly-dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm non-divergence-from-common-domination
  (implies
   (and
    (dominates x a)
    (dominates y a))
   (not (diverge x y)))
  :rule-classes (:forward-chaining))

(defthm strictly-dominates-from-not-diverge-and-not-dominates-1
  (implies
   (and
    (not (diverge x y))
    (not (dominates x y)))
   (strictly-dominates y x))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable diverge strictly-dominates))))

(defthm strictly-dominates-from-not-diverge-and-not-dominates-2
  (implies
   (and
    (not (dominates x y))
    (not (diverge x y)))
   (strictly-dominates y x))
  :rule-classes (:forward-chaining))

(defthm all-dominated-by-some-id
  (all-dominated-by-some x x))

(defun setequiv (x y)
  (and (all-dominated-by-some x y)
       (all-dominated-by-some y x)))

(defthm setequiv-cons-reduction
  (implies
   (dominated-by-some path x)
   (setequiv (cons path x) x)))

(defthm setequiv-append-reduction
  (implies
   (all-dominated-by-some x y)
   (setequiv (append x y) y)))

;;
;; I think we should get these rules from refinement of list::setequiv
;;

(defthm setequiv-cons-commute
  (setequiv (cons a (cons b x))
            (cons b (cons a x))))

(defthm setequiv-cons-duplicate
  (setequiv (cons a (cons a x))
            (cons a x)))

(defthm setequiv-append-commute
  (setequiv (append x (append y z))
            (append y (append x z))))

(defthm setequiv-append-duplicate
  (setequiv (append x (append x y))
            (append x y)))

(in-theory (disable setequiv))

;;
;; path-remove <-> remove
;;
(defun path-remove (path set)
  (if (consp set)
      (if (dominates path (car set))
          (path-remove path (cdr set))
        (cons (car set) (path-remove path (cdr set))))
    set))

;; member of remove
(defthm dominated-by-some-remove
  (equal (dominated-by-some a (path-remove path list))
         (if (dominates path a)
             (strictly-dominated-by-some path list)
           (dominated-by-some a list)))
  :hints (("Goal" :induct (path-remove path list)
           :in-theory (disable NOT-STRICTLY-DOMINATED-BY-SOME-BY-MEMBERSHIP))))

;; strict-member of remove
(defthm strictly-dominated-by-some-remove
  (equal (strictly-dominated-by-some a (path-remove path list))
         (if (dominates path a)
             (strictly-dominated-by-some path list)
           (strictly-dominated-by-some a list)))
  :hints (("Goal" :induct (path-remove path list)
           :in-theory (disable strictly-dominates-implies-dominates
                               NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
                               DIVERGES-FROM-WHEN-NOT-STRICTLY-DOMINATED-BY-SOME-AND-NOT-DOMINATES-SOME
                               DIVERGES-OF-CDR-BY-DIVERGES-FROM-ALL
                               FIRST-DOMINATOR-OF-CDR
                               DIVERGES-FROM-ALL-WHEN-NO-DOMINATION-ALT
                               NOT-DOMINATES-FROM-<-OF-LEN-AND-LEN
                               ))))

#|

Just checking setequiv reduction.

(defthm iff-reduction
  (equal (iff a b)
         (and
          (implies a b)
          (implies b a))))

(defthm dominated-by-some-remove-reduction
  (implies
   (strictly-dominated-by-some a x)
   (setequiv (path-remove a x) x))
  :hints (("Goal" :induct (path-remove a x))))

(defthm dominates-some-car-consp
  (implies
   (consp x)
   (dominates-some (car x) x)))

(defthm len-path-remove
  (implies
   (dominates-some path x)
   (< (len (path-remove path x)) (len x)))
  :hints (("Goal" :induct (path-remove path x)))
  :rule-classes (:linear))

(defun path-remove-induction-2 (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (path-remove-induction-2 (path-remove (car x) x) (path-remove (car x) y))
    (list x y)))

|#

#|
(defun path-member (x list)
  (if (consp list)
      (or (list::equiv x (car list))
          (path-member x (cdr list)))
    nil))

(defcong list::equiv equal (path-member x list) 1)

(defcong list::list-equiv equal (path-member x list) 2
  :hints (("goal" :induct (list::len-len-induction list list::list-equiv))))

(defun path-subset (a b)
  (if (consp a)
      (and (path-member (car a) b)
           (path-subset (cdr a) b))
    t))

(defthm path-member-chaining
  (implies
   (and
    (path-subset a b)
    (path-member x a))
   (path-member x b))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-member-chaining-free
  (implies
   (and
    (path-member x a)
    (path-subset a b))
   (path-member x b)))

(defthm path-subset-chaining-1
  (implies
   (and
    (path-subset b c)
    (path-subset a b))
   (path-subset a c))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subset-chaining-free-1
  (implies
   (and
    (path-subset a b)
    (path-subset b c))
   (path-subset a c)))

(defthm path-subset-chaining-2
  (implies
   (and
    (path-subset a y)
    (path-subset y z))
   (path-subset a z))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subset-chaining-free-2
  (implies
   (and
    (path-subset y z)
    (path-subset a y))
   (path-subset a z)))

(defthm path-subset-self
  (path-subset a a))

(defund path-equiv (a b)
  (and (path-subset a b)
       (path-subset b a)))

(defthmd path-equiv-double-containment
  (equal (path-equiv a b)
         (and (path-subset a b)
              (path-subset b a)))
  :hints (("goal" :in-theory (enable path-equiv))))

(defthm path-subset-cdr
  (path-subset (cdr y) y))

(defthmd path-subset-cdr-forward
  (path-subset (cdr y) y)
  :rule-classes ((:forward-chaining :trigger-terms ((cdr y)))))

(defun path-remove (x list)
  (if (consp list)
      (if (list::equiv x (car list))
          (path-remove x (cdr list))
        (cons (car list) (path-remove x (cdr list))))
    nil))

(defthm acl2-count-path-remove
  (<= (acl2-count (path-remove x list))
      (acl2-count list))
  :rule-classes (:linear))

(defthm path-member-of-path-remove
  (equal (path-member a (path-remove b list))
         (if (list::equiv a b) nil
           (path-member a list))))

(defthmd path-subset-membership-reduction
  (implies
   (path-member a y)
   (equal (path-subset y z)
          (and (path-member a z)
               (path-subset (path-remove a y) (path-remove a z)))))
  :hints (("goal" :in-theory (disable BOOLEANP-COMPOUND-RECOGNIZER
                                      PATH-SUBSET-BY-MEMBERSHIP))))

(defthmd car-membership-forward
  (implies
   (consp x)
   (path-member (car x) x))
  :rule-classes (:forward-chaining))

(defthmd non-membership-path-remove-reduction
  (implies
   (not (path-member a x))
   (equal (path-remove a x)
          (list::fix x))))

(defthm membership-implies-membership
  (implies
   (bag::memberp a x)
   (path-member a x)))

(defthm path-membership-from-subbagp
  (implies
   (and
    (bag::subbagp x y)
    (path-member path x))
   (path-member path y)))

(defthm path-subset-from-subbag
  (implies
   (bag::subbagp x y)
   (path-subset x y)))

|#
#|

;;
;; Here is an even stronger equivalence
;;

(defthm subset-remove
  (path-subset (path-remove a x) x)
  :rule-classes ((:forward-chaining :trigger-terms ((path-remove a x)))))

(defthmd open-path-subset-on-membership
  (implies
   (path-member a x)
   (equal (path-subset x y)
          (and (path-member a y)
               (path-subset (path-remove a x) (path-remove a y))))))

(defthmd open-path-equiv-on-membership
  (implies
   (path-member a x)
   (equal (path-equiv x y)
          (and (path-member a y)
               (path-equiv (path-remove a x)
                           (path-remove a y)))))
  :hints (("goal" :in-theory (enable open-path-subset-on-membership path-equiv))))

(defthmd path-equiv-reduction
  (equal (path-equiv x y)
         (and (equal (path-member a x)
                     (path-member a y))
              (path-equiv (path-remove a x)
                          (path-remove a y))))
  :hints (("goal" :in-theory (enable non-membership-path-remove-reduction
                                     open-path-equiv-on-membership))))


;; I'm not sure this is what we want to do.  I think for
;; congruences we want to reason using double-containment.

(defun path-equiv-induction (x y)
  (if (consp x)
      (and (path-member (car x) y)
           (path-equiv-induction (path-remove (car x) (cdr x)) (path-remove (car x) y)))
    (not (consp y))))

(defthm not-consp-path-equiv
  (implies
   (not (consp x))
   (and (equal (path-equiv x y)
               (not (consp y)))
        (equal (path-equiv y x)
               (not (consp y)))))
  :hints (("goal" :in-theory (enable path-equiv))))

(defthmd open-path-equiv
  (implies
   (consp x)
   (and (equal (path-equiv x y)
               (and (path-member (car x) y)
                    (path-equiv (path-remove (car x) (cdr x))
                                (path-remove (car x) y))))
        (equal (path-equiv y x)
               (and (path-member (car x) y)
                    (path-equiv (path-remove (car x) y)
                                (path-remove (car x) (cdr x)))))))
  :hints (("goal" :use (:instance path-equiv-reduction
                                  (a (car x))))))

(defthm not-strictly-dominated-by-some-subset
  (IMPLIES (AND (PATH-SUBSET sub sup)
                (NOT (STRICTLY-DOMINATED-BY-SOME A sup)))
           (NOT (STRICTLY-DOMINATED-BY-SOME A sub)))
  :hints (("goal" :in-theory (enable STRICTLY-DOMINATED-BY-SOME))))

(defthm path-subset-dominates-some
  (implies
   (and
    (path-subset sub sup)
    (dominates-some x sub))
   (dominates-some x sup)))

(defthm path-subset-dominated-by-some
  (implies
   (and
    (path-subset sub sup)
    (dominated-by-some x sub))
   (dominated-by-some x sup)))

;; This is our dom membership function

(defun path-subdom (x y)
  (if (consp x)
      (and (or (dominated-by-some (car x) (cdr x))
               (dominates-some (car x) y))
           (path-subdom (cdr x) y))
    t))

(defthm path-subset-path-subdom
  (implies
   (and
    (path-subset sub sup)
    (path-subdom sup x))
   (path-subdom sub x)))

DAG

(in-theory (enable dominates-some))
(in-theory (enable dominated-by-some))
;;
;; and even this goes thru only with pain ..
;;

(defthm hack-lemma
  (IMPLIES (AND
            (PATH-SUBDOM LIST B)
            (NOT (DOMINATED-BY-SOME X LIST))
            (DOMINATES X A)
            (DOMINATED-BY-SOME A LIST)
            )
           (DOMINATES-SOME X B)))

(defthm dominates-some-chaining
  (implies
   (and
    (path-subdom a b)
    (not (dominated-by-some x a))
    (dominates-some x a))
   (dominates-some x b))
  :rule-classes (:rewrite :forward-chaining))

(defthm dominates-some-chaining-free
  (implies
   (and
    (dominates-some x a)
    (not (dominated-by-some x a))
    (path-subdom a b))
   (dominates-some x b)))

(thm
  (IMPLIES (AND (PATH-SUBDOM B C)
                (PATH-SUBDOM LIST B)
                (NOT (DOMINATED-BY-SOME R LIST))
                (DOMINATES-SOME R B))
           (DOMINATES-SOME R C))
  :hints (("goal" :induct (PATH-SUBDOM LIST B))))

(defthm path-subdom-chaining-1
  (implies
   (and
    (path-subdom b c)
    (path-subdom a b))
   (path-subdom a c))
  :hints (("goal" :induct (path-subdom a c)))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subdom-chaining-free-1
  (implies
   (and
    (path-subdom a b)
    (path-subdom b c))
   (path-subdom a c)))

(defthm path-subdom-chaining-2
  (implies
   (and
    (path-subdom a y)
    (path-subdom y z))
   (path-subdom a z))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subdom-chaining-free-2
  (implies
   (and
    (path-subdom y z)
    (path-subdom a y))
   (path-subdom a z)))


DAG

(defun path-domequiv (x y)
  (and (path-subdom x y)
       (path-subdom y x)))

(defun path-domequiv (x y)
  (and (all-dominate-some x y)
       (all-dominate-some y x)))


(defun all-dominate-some

;; dominates-or-diveres-from-all

(defun path-dominates-some (x list)
  )

(defun contains-dominators (x list)
  )

(defun remove-dominators (x list)
  )

(defun dom (x)
  (if (consp x)
      (if (cpath::strictly-dominated-by-some (car x) (cdr x))
          (dom (cdr x))
        (cons (car x)
              (dom (cpath::remove-dominators (cdr x))))
    nil))

(defun path-subdom (x y)
  (if (consp x)
      (if (cpath::strictly-dominated-by-some (car x) (cdr x))
          (path-subdom (cdr x) y)
        (and (not (cpath::strictly-dominated-by-some (car x) y))
             (path-subdom (cdr x) y)))
    t))

(defthm test
  (implies
   (and
    (path-subdom sub sup)
    (not (cpath::strictly-dominated-by-some x sup))
    (dominates-some x sup))
   (and
    (not (cpath::strictly-dominated-by-some x sub))
    (dominates-some x sub))))

(defthm path-subdom-subset
  (implies
   (and
    (path-subdom sub sup)
    (path-subdom x sub))
   (path-subdom x sup)))

(defun cpath::domequiv (x y)
  (and (cpath::subdom x y)
       (cpath::subdom y x)))
|#

;; Just not the right direction
(in-theory
 (disable
  cpath::clrp-of-nil-two
  CPATH::CLRP-OF-SP
  CPATH::SP-TO-CLRP
  CPATH::SP-OF-SP
  CPATH::SP-DOES-NOTHING
  CPATH::SP-OF-SP-DIVERGE
  CPATH::GP-OF-SP
  CPATH::GP-OF-NON-CONSP
  ))

;; Introduce CPATH::EFFECT-ON-SPOT
(in-theory
 (disable
  cpath::gp-of-mp-better
  cpath::mp-of-sp-when-not-dominated-by-some
  cpath::mp-of-sp
  ))

;; Expensive disjointness
;; jcd Cheapened with a backchain limit, trying to leave enabled
;; (in-theory
;;  (disable
;;   CPATH::DOMINATES-WHEN-NOT-DIVERGE-AND-NOT-DOMINATES
;;   ))

;; Introduces nthcdr
(in-theory
 (disable
  ;cpath::gp-of-sp-subpath-case-one
  ;cpath::gp-of-sp-subpath-case-two
  cpath::sp-of-sp-dominating-case-two
  cpath::gp-of-mp-when-dominated-by-some-all-diverge
  cpath::gp-of-mp-all-diverge
  cpath::gp-of-mp-when-dominated-by-some
  cpath::gp-of-mp
  CPATH::DOMINATES-MEANS-NOT-DIVERGE-ALT
  CPATH::GP-OF-MP-WHEN-P-DOMINATES
  LIST::MEMBERP-OF-CONS-IRREL
  LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
  CPATH::NOT-DIVERGES-FROM-ALL-WHEN-MEMBERP

  CPATH::DIVERGE-WHEN-FIRSTNS-DIVERGE
  CPATH::DIVERGE-FROM-ALL-DIVERGE-AND-UNIQUE-MEMBERPS
  CPATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP-ALT
  CPATH::DIVERGE-WHEN-ALL-DIVERGE-FROM-ALL-AND-MEMBERP-AND-MEMBERP

;; jcd these got renamed
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
;  CPATH::DIVERGE-FROM-MEMBERP-AND-DIVERGES-FROM-ALL-TWO
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-FOUR
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-THREE
  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-TWO

  CPATH::DIVERGE-WHEN-MEMBERP-AND-DIVERGES-FROM-ALL-ONE
;jcd removed this  CPATH::DIVEREG-WHEN-DOMINATE-DIVERGENT

;; jcd this got renamed  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ALT
;; why are we disabling this but not the other rules?  maybe it should
;; just be left enabled?
  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE-ALT

  CPATH::DIVERGE-OF-NON-CONSP-TWO
  CPATH::DIVERGE-OF-NON-CONSP-ONE
  CPATH::TWO-DOMINATORS-CANNOT-DIVERGE

  CPATH::SP-OF-SP-DOMINATING-CASE-ONE
;;  LIST::EQUAL-OF-IF-HACK
;;  CPATH::FIRST-DOMINATOR-WHEN-P-DOMINATES-IT-YUCK
  CPATH::DIVERGES-FROM-WHEN-NOT-STRICTLY-DOMINATED-BY-SOME-AND-NOT-DOMINATES-SOME
  ;CPATH::SP-OF-NON-CONSP
  ))


;; This is introduced and must simplify
;; bzo we have rules about this now... maybe we should disable it?
(in-theory (enable nthcdr))


(in-theory
 (disable
  CPATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION-ALT
  CPATH::NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
  CPATH::DIVERGES-FROM-ALL-WHEN-NO-DOMINATION
  CPATH::NOT-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL

;; jcd renamed this  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR
  CPATH::DIVERGE-WHEN-DIVERGE-WITH-DOMINATOR-ONE
  ))

(in-theory
 (e/d (cpath::keys)
      (cpath::keys-of-cdr)))

(in-theory
 (disable
  CPATH::DIVERGES-FROM-ALL-WHEN-DOMINATED
  CPATH::DIVERGES-FROM-ALL-OF-NON-CONSP-ONE

;jcd these got renamed
;  CPATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP
;  CPATH::DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-AND-SUBBAGP-ALT
  CPATH::diverges-from-all-by-subbagp-one
  CPATH::diverges-from-all-by-subbagp-two

  CPATH::DIVERGES-FROM-ALL-OF-NON-CONSP-TWO
  CPATH::MP-OF-NON-CONSP
  CPATH::ALL-DIVERGE-WHEN-MEMBERP-NIL
;; jcd this got renamed  CPATH::ALL-DIVERGE-WHEN-ALL-DIVERGE-AND-SUBBAGP
  CPATH::all-diverge-when-subbag
  ))

;; jcd removed this entirely
;; (in-theory
;;  (disable
;;   CPATH::DIVERGE-OF-CONS-AND-CONS
;;   ))

(in-theory
 (disable
  CPATH::ALL-DIVERGE-FROM-ALL-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-DIVERGE
  CPATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
  CPATH::CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-APPEND-1
;;  LIST::LEN-FW-TO-CONSP
  LIST::LEN-OF-NON-CONSP
  LIST::APPEND-OF-NON-CONSP-ONE
  LIST::APPEND-OF-NON-CONSP-2
  ))

(in-theory
 (disable
  CPATH::DOMINATES-OF-NON-CONSP-TWO
  CPATH::DOMINATES-OF-NON-CONSP-ONE
;; jcd removed this  CPATH::DOMINATES-OF-CONS-AND-CONS
  CPATH::DOMINATES-OF-APPEND-TWO-ONE
  CPATH::DOMINATES-OF-SINGLETON-TWO
  CPATH::DOMINATES-OF-APPEND-AND-APPEND
  CPATH::DOMINATES-TRANSITIVE-ONE
  CPATH::EQUAL-PRUNE-LEN-IMPLIES-DOMINATION
;; jcd renamed this CPATH::TWO-DOMINATORS-HACK
  CPATH::linear-domination-hierarchy

  CPATH::DOMINATES-TRANSITIVE-THREE
  CPATH::DOMINATES-FROM-DOMINATES-OF-NTHCDR-ETC
  ))

(in-theory
 (disable
  CPATH::DIVERGE-TAIL-DOMINATOR-BODY-BODY-REC-IMPLIES-DIVERGE
;; jcd renamed this  CPATH::DIVERGE-COMMUTATIVE
  CPATH::DIVERGE-SYMMETRIC
  CPATH::ALL-DIVERGE-FROM-ALL-TAIL-DOMINATOR-BODY-IMPLIES-DIVERGE
  ))

#+joe
(in-theory
 (disable
  CPATH::GP-OF-USE
  ))

(in-theory
 (disable
  CPATH::GP-OF-SP-SUBPATH-CASE-ONE
  CPATH::GP-OF-SP-SUBPATH-CASE-TWO
  ;CPATH::GP-OF-DEF
  ))

(in-theory
 (disable
  ;jcd - removed this theorem entirely - CPATH::OPEN-DIVERGES-FROM-ALL
  DIVERGES-FROM-ALL
  CPATH::DIVERGE-OF-APPEND-FROM-DIVERGE-ONE
  CPATH::DIVERGE-OF-APPEND-FROM-DIVERGE-TWO
  CPATH::DIVERGE-OF-APPEND-AND-APPEND
  cpath::sp-of-non-consp
  ;CPATH::OPEN-USE
  ;CPATH::OPEN-DEFS
  ))

;; We don't yet have the cp infrastructure ..

(in-theory
 (disable
  CPATH::MP-OF-SP-WHEN-DIVERGES-FROM-ALL
  CPATH::GP-OF-MP-DIVERGES-FROM-ALL-CASE
  ))

(in-theory
 (enable
  mp
  ))

(in-theory
 (enable
  sp==r
  ))

;; jcd - bzo - this seems bad!
(in-theory
 (enable
  dominated-by-some
  diverges-from-all
  ))

(in-theory
 (e/d
  (
   member
   )
  (
   ;; JCD - updated these
   LIST::member-is-memberp-propositionally
   LIST::member-eq-is-memberp-propositionally
   LIST::member-equal-is-memberp-propositionally
   ;; REDUCE-MEMBERX-TO-MEMBERP
   )))

(in-theory
 (disable
  g-to-gp
  s-to-sp
  ))
 (in-package "ACL2")

;;This book provides functions to translate back and forth between lists
;;(which are accessed positionally) and records (which are accessed by named
;;keys).  The order of names in the KEY-NAMES arguments to RECORD-TO-LIST and
;;LIST-TO-RECORD indicates how the keys for the record correspond to the
;;positions in the list.

;;bzo Maybe this book should be renamed, since it doesn't really include any path stuff (now it does, at the bottom)

;rename and move
(defthm list::memberp-of-nth-cdr
  (implies (bag::unique lst)
           (equal (list::memberp (nth 0 lst) (cdr lst))
                  nil)))

(defthm nth-equal-car-when-unique-rewrite
  (implies (and (bag::unique lst)
                (< n (len lst))
                (consp lst))
           (equal (equal (nth n lst) (car lst))
                  (equal (nfix n) 0)))
  :hints (("Goal" :in-theory (enable NTH BAG::UNIQUE-OF-CONS))))

(defthm list::find-index-of-nth-same
  (implies (and (bag::unique key-names)
                (< (nfix n) (len key-names))
                (natp n) ;bzo drop?
                )
           (equal (list::find-index (nth n key-names) key-names)
                  n))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list::find-index nth)
                           (;find-index-of-cdr
                            )))))



(local (in-theory (enable G-OF-S-REDUX)))

;;
;; LIST-TO-RECORD
;;

(defund list-to-record (lst key-names)
  (if (endp key-names)
      nil ;the emoty record
    (s (car key-names)
       (car lst)
       (list-to-record (cdr lst) (cdr key-names)))))

;;
;; RECORD-TO-LIST
;;

;the order of the key-names determines the order in which their corresponding values end up in the list
(defund record-to-list (r key-names)
  (if (endp key-names)
      nil ;the empty list
    (cons (g (car key-names) r)
          (record-to-list
           ;(clr (car key-names)
                r;
                ;) ;trying...
           (cdr key-names)))))

;; (defun my-ind (lst key-names)
;;   (if (not (consp key-names))
;;       (list lst key-names)
;;     (my-ind (lst key-names)

(defthm RECORD-TO-LIST-of-s-irrel
  (implies (not (list::memberp key key-names))
           (equal (RECORD-TO-LIST (S key val r) KEY-NAMES)
                  (RECORD-TO-LIST r KEY-NAMES)))
  :hints (("Goal" :in-theory (enable record-to-list))))


(defthm record-to-list-of-list-to-record
  (implies (and (equal (len lst) (len key-names))
                (bag::unique key-names))
           (list::equiv (record-to-list (list-to-record lst key-names) key-names)
                        lst))
  :hints (("Goal" :in-theory (enable list-to-record record-to-list)
           :do-not '(generalize eliminate-destructors))))

;; (defun ind (keys r)
;;   (declare (xargs :verify-guards nil))
;;   (if (not (consp keys))
;;       (list keys r)
;;     (ind (cdr keys)
;;          (clr (set::head (RKEYS R)) r);
;;          ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
;;          )))

(defthm record-to-list-of-clr-irrel
  (implies (not (list::memberp key keys))
           (equal (record-to-list (clr key r) keys)
                  (record-to-list r keys)))
  :hints (("Goal" :in-theory (enable record-to-list))))


;bzo redo everything to make key-names a set?

;; (local
;;  (defthm list-to-record-of-record-to-list
;;    (implies (and (equal rk (list::2set key-names))
;;                  (equal (rkeys r) rk)
;;                  (bag::unique key-names) ;can drop??
;;                  )
;;             (equal (list-to-record (record-to-list r key-names) key-names)
;;                    r))
;;    :hints (("Goal" ;:induct (ind key-names r)
;;             :in-theory (e/d (list-to-record)
;;                             (SET::DOUBLE-CONTAINMENT))
;; ;           :induct t
;;             :induct (ind101 rk key-names r)
;;             :expand ((RECORD-TO-LIST R KEY-NAMES)
;; ;(RECORD-TO-LIST R (CDR KEY-NAMES))
;;                      )
;;             :do-not '(generalize eliminate-destructors)))))

;; ;drop?
;; (defthm list-to-record-of-record-to-list-better
;;   (implies (and (equal (rkeys r) (list::2set key-names))
;;                 (bag::unique key-names) ;can drop??
;;                 )
;;            (equal (list-to-record (record-to-list r key-names) key-names)
;;                   r)))




;bzo tons of stuff to move out...

;bzo what other theorems do we need?
(defthm g-of-list-to-record
  (implies (list::memberp key key-names) ;bzo use list::memberp?
           (equal (g key (list-to-record lst key-names))
                  (nth (list::find-index key key-names) lst)))
  :hints (("Goal" :in-theory (enable list-to-record))))

(local
 (defun cdr-cdr-minus1-induct (x y n)
   (if (endp x)
       (list x y n)
     (cdr-cdr-minus1-induct (cdr x) (cdr y) (+ -1 n)))))

(defthm clr-of-list-to-record
  (implies (bag::unique key-names) ;t;(consp key-names)
           (equal (clr key (list-to-record lst key-names))
                  (list-to-record (list::clear-nth (list::find-index key key-names) lst) key-names)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list-to-record
                            list::find-index
                            list::CDR-OF-clear-NTH
                            )
                           (;FIND-INDEX-OF-CDR
                            )))))



(defthm g-of-list-to-record-irrel
  (implies (not (list::memberp key keys))
           (equal (g key (list-to-record lst keys))
                  nil))
  :hints (("Goal" :in-theory (enable LIST-TO-RECORD))))


;; (thm
;;  (equal (LIST-TO-RECORD (UPDATE-NTH n val lst) key-names)
;;         (if (< (nfix n) (len key-names))
;;             (cpath::s (nth n key-names) val (LIST-TO-RECORD lst key-names))
;;           (LIST-TO-RECORD lst key-names)))
;;  :hints (("Goal" :in-theory (enable LIST-TO-RECORD))))

;(in-theory (disable TAG-LOCATION-ELIMINATION))

(local (defun cdr-minus1-induction (x n)
         (if (endp x)
             (list x n)
           (cdr-minus1-induction (cdr x) (+ -1 n)))))

(defthm nth-of-record-to-list
  (implies (and (natp n)
                (bag::unique keys)
                (< n (len keys)))
           (equal (nth n (record-to-list r keys))
                  (g (nth n keys) r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-cdr-minus1-induct keys lst n)
           :in-theory (e/d (list::nth-0-becomes-car
                            record-to-list) ()))))


;now characterize how s and update-nth change what these functions do?


;bzo delete this old stuff if we don't need it

;; ;functions to map back and forth from a list (accessed positionally with nth
;; ;and update-nth) to a nested record suitable for accessing with paths
;; ;The list in question can be the logical representation of a stobj.

;; (defun wrap (x)
;;   (s :val x nil))

;; (defun unwrap (wrapped-x)
;;   (g :val wrapped-x))

;; ;This wraps the values so that, looking at a record, we can tell the
;; ;difference between a wrapped nil and nothing at all?
;; (defun list-to-record-aux (n lst)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (or (not (integerp n))
;;           (< n 0))
;;       nil
;;     (s n
;;        (wrap (nth n lst))
;;        (list-to-record-aux (+ -1 n) lst))))

;; (defun list-to-record (lst)
;;   (list-to-record-aux (len lst) lst))

;; (defund record-to-list-aux (keys r)
;;   (if (set::empty keys)
;;       nil ;the empty typed record
;;     (update-nth (set::head keys) ;nfix?
;;                 (unwrap (g (set::head keys) r))
;;                 (record-to-list-aux (set::tail keys) r))))

;; (defun record-to-list (r)
;;   (record-to-list-aux (rkeys r) r))

;; (defund all-values-wrapped-aux (keys r)
;;   (if (set::empty keys)
;;       t
;;     (let ((value (g (set::head keys) r)))
;;       (and (consp value)
;;            (equal (car value) ':val)))))

;; (defun all-values-wrapped (r)
;;   (all-values-wrapped-aux (rkeys r) r))

;; (defthm nth-of-record-to-list-aux
;;   (implies (set::all-list<natp> keys) ;otherwise might be a that nfixes to n but isn't equal to n (or several such keys)
;;            (equal (nth n (record-to-list-aux keys r))
;;                   (if (set::in (nfix n) keys) ;could say n is among the nfixed keys?
;;                       (unwrap (g (nfix n) r))
;;                     nil)))
;;   :hints (("Goal" :induct (record-to-list-aux keys r)
;;            :in-theory (enable record-to-list-aux)
;;            :do-not '(generalize eliminate-destructors))))

;; (defun convertible-to-list (r)
;;   (and (set::all-list<natp> (rkeys r))
;;        (all-values-wrapped r)))

;; ;for dave
;; (defthm nth-of-record-to-list
;;   (implies (convertible-to-list r)
;;            (equal (nth n (record-to-list r))
;;                   (if (set::in (nfix n) (rkeys r))
;;                       (unwrap (g (nfix n) r))
;;                     nil))))

;; Is the wrapping okay?

;; how do we really want these accessors to look?

;; (gp '(:st *aamp.tos* :val) st)

;; ;i'd rather have:
;; (gp '(:st :tos) st)

;; pass in sotbj field descriptor?

;; g of list-to-record
;; list-to-record of update-nth
;; wf-list of update-nth
;; convertible-to-list of s?

;; 2 inverses

(defthm len-of-record-to-list
  (equal (len (record-to-list r keys))
         (len keys))
  :hints (("Goal" :in-theory (enable record-to-list))))

(local (defun cdr-sub1-induct (x n)
         (if (endp x)
             (list x n)
           (cdr-sub1-induct (cdr x) (+ -1 n)))))

(defthm clear-nth-of-record-to-list
  (implies (and (natp n)
                (< n (len keys))
                (bag::unique keys)
                )
           (equal (list::clear-nth n (record-to-list r keys))
                  (record-to-list (clr (nth n keys) r) keys)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-sub1-induct keys n)
           :in-theory (enable record-to-list))))

(defun ind101 (keys r)
  (if (endp keys)
      (list keys r)
    (ind101 (cdr keys) (clr (car keys) r))))

(local
 (defthm unique-implies-open-subsetp
   (implies
    (and
     (bag::unique list)
     (consp list))
    (equal (subsetp x list)
           (subsetp (remove (car list) x) (cdr list))))
   :hints (("Goal" :in-theory (enable bag::memberp))))
 )

(local
 (defthm list-to-record-of-record-to-list-better2
   (implies (and
             (list::subsetp (rkeys r) key-names)
             (bag::unique key-names))
            (equal (list-to-record (record-to-list r key-names) key-names)
                   r))
   :hints (("Goal"
            :in-theory (e/d (list-to-record)
                            (REMOVE))
            :induct (ind101 key-names r)
            :expand ((RECORD-TO-LIST R KEY-NAMES))
            :do-not '(generalize eliminate-destructors))))
 )

(defthm list-to-record-of-record-to-list-better3
  (implies (and (list::subsetp (rkeys r) key-names)
                (bag::unique key-names) ;can drop??
                )
           (equal (list-to-record (record-to-list r key-names) key-names)
                  r)))

(defthm clrp-singleton-of-list-to-record
  (implies (bag::unique key-names)
           (equal (cpath::clrp (list key) (list-to-record lst key-names))
                  (list-to-record
                   (update-nth (list::find-index key key-names)
                               nil lst)
                   key-names)))
  :hints (("Goal" :in-theory (e/d (cpath::clrp cpath::sp s-becomes-clr)
                                  (cpath::sp==r cpath::s-to-sp s==r CPATH::SP-TO-CLRP)))))

;gen to non singletons?
(defthm gp-singleton-of-list-to-record
  (implies (list::memberp key key-names)
           (equal (cpath::gp (list key)
                            (list-to-record lst key-names))
                  (nth (list::find-index key key-names)
                       lst)))
  :hints (("Goal" :in-theory (enable cpath::gp))))



(defthm list-to-record-of-update-nth-usual-case
  (implies (and (< (nfix n) (len key-names))
                (natp n)
                (bag::unique key-names)
                )
           (equal (list-to-record (update-nth n val lst) key-names)
                  (cpath::s (nth n key-names) val (list-to-record lst key-names))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-cdr-minus1-induct lst key-names n)
           :expand ((list-to-record (update-nth 0 nil (update-nth n nil lst))
                                          key-names))
           :in-theory (e/d (list::clear-nth
                            list-to-record
                            list::update-nth-of-cdr
                            list::clear-nth-of-cdr)
                           (list::cdr-of-update-nth
                            LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
                            LIST::UPDATE-NTH-EQUAL-REWRITE
                            )))))

(defthm acl2::record-to-list-of-s-not-irrel
  (implies (and (list::memberp acl2::key acl2::key-names)
                (bag::unique acl2::key-names))
           (equal (acl2::record-to-list (s acl2::key acl2::val acl2::r)
                                        acl2::key-names)
                  (update-nth (list::find-index acl2::key acl2::key-names)
                              acl2::val (acl2::record-to-list acl2::r acl2::key-names))))
  :hints (("Goal" :in-theory (enable acl2::record-to-list))))

;; jcd - moved to :lists/map-cons
;; (defun map-cons (a list)
;;   (declare (type t a list))
;;   (if (consp list)
;;       (cons (cons a (car list))
;;             (map-cons a (cdr list)))
;;     nil))

;; jcd - moved to :lists/basic
;; (defun appendx (x y)
;;   (declare (type t x y))
;;   (if (consp x)
;;       (cons (car x) (appendx (cdr x) y))
;;     y))

;; jcd - we use mbe now, no need for this rule
;; (defthm appendx-is-append
;;   (equal (appendx x y)
;;          (append x y)))

;  1.36          12.00
;  CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-MEMBERSHIP-DECONSTRUCTION

;jcd Trying this. -ews
(local (in-theory (disable not-dominates-from-diverge-one
                           not-dominates-from-diverge-two)))

;; Normalization: assume that (append (cons a b) list) = (cons a (append b list))
;; (for quoted (cons a b) terms, too)

(in-theory
 (disable
  LENS-<-WHEN-DOMINATES-BUT-NOT-CONG
  NOT-DOMINATES-FROM-<-OF-LEN-AND-LEN
  DOMINATES-WHEN-LENS-EQUAL
;; jcd - Cheapened this, going to try leaving it enabled
;;   DOMINATES-WHEN-NOT-DIVERGE-AND-NOT-DOMINATES
  DOMINATES-ASYMMETRIC
  DOMINATES-TRANSITIVE-TWO
  dominates-means-not-diverge
  dominates-means-not-diverge-alt
  ))

(in-theory
 (enable
  BAG::APPEND-COMMUTATIVE-INSIDE-PERM
  ))

(local (in-theory (disable syn::open-len)))

(defun syn::ts-consp (term fact)
  (declare (type (satisfies acl2::type-alist-entryp) fact)
           (xargs :guard-hints (("goal" :in-theory (enable acl2::type-alist-entryp)))))
  (let ((ts     (cadr fact))
        (tsterm (car  fact)))
    (and (or (not (= (logand ts acl2::*ts-proper-cons*) acl2::*ts-empty*))
             (not (= (logand ts acl2::*ts-improper-cons*) acl2::*ts-empty*)))
         (equal term tsterm))))

(defun sudo-len (term)
  (declare (type t term))
  (if (syn::consp term)
      (1+ (sudo-len (syn::cdr term)))
    (if (syn::appendp term)
        (1+ (sudo-len (syn::arg 2 term)))
      (if (syn::quotep term)
          1
        0))))

(defthm integerp-sudo-len
  (integerp (sudo-len term))
  :rule-classes (:rewrite :type-prescription))

(defthm sudo-len-linear
  (<= 0 (sudo-len ter))
  :rule-classes (:linear))

(defun equal-len (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((and (syn::quotep path1)
         (syn::quotep path2))
    (equal (len (syn::dequote path1))
           (len (syn::dequote path2))))
   ((and (syn::consp path1)
         (syn::consp path2))
    (equal-len (syn::cdr path1)
               (syn::cdr path2)))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (and (equal-len (syn::arg 1 path1) (syn::arg 1 path2))
         (equal-len (syn::arg 2 path1) (syn::arg 2 path2))))
   (t (equal path1 path2))))

(defthm equal-len-identity
  (equal-len x x))

(defun syntax-quote-diverge (path1 path2)
  (declare (type t path1 path2))
  (if (consp path1)
      (cond
       ((syn::consp path2)
        (let ((v (syn::car path2)))
          (or (and (syn::quotep v)
                   (not (equal (car path1) (syn::dequote v)))
                   (syn::true))
              (syntax-quote-diverge (cdr path1) (syn::cdr path2)))))
       ((syn::quotep path2)
        (and (diverge path1 (syn::dequote path2))
             (syn::true)))
       (t nil))
    nil))

(defthm syntax-quote-diverge-implies-quote-true
  (implies
   (syntax-quote-diverge path1 path2)
   (equal (syntax-quote-diverge path1 path2) (syn::true))))

(defthm syntax-quote-diverge-implies-diverge
  (implies
   (syntax-quote-diverge x1 t2)
   (diverge x1 (syn::eval t2 a)))
  :hints (("goal" :in-theory (enable diverge-append-len-equal))))

(defun syntax-diverge (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((syn::quotep path1)
    (syntax-quote-diverge (syn::dequote path1) path2))
   ((syn::quotep path2)
    (syntax-quote-diverge (syn::dequote path2) path1))
   ((and (syn::consp path1)
         (syn::consp path2))
    (let ((car1 (syn::car path1))
          (car2 (syn::car path2)))
      (if (and (syn::quotep car1)
               (syn::quotep car2)
               (not (equal (syn::dequote car1)
                           (syn::dequote car2))))
          (syn::true)
        (syntax-diverge (syn::cdr path1) (syn::cdr path2)))))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (let ((arg11 (syn::arg 1 path1))
          (arg12 (syn::arg 1 path2)))
      (and (equal arg11 arg12)
           (syntax-diverge (syn::arg 2 path1) (syn::arg 2 path2)))))
   (t nil)))

(defthm syntax-diverge-implies-diverge
  (implies
   (syntax-diverge t1 t2)
   (diverge (syn::eval t1 a) (syn::eval t2 a)))
  :hints (("goal" :in-theory (enable syn::open-nth diverge-append-len-equal))))

(defun remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (if (and (consp path1)
           (consp path2))
      (if (equal (car path1) (car path2))
          (remove-common-prefix (cdr path1) (cdr path2))
        (mv path1 path2))
    (mv nil nil)))

(defthm remove-common-prefix-identity
  (and
   (equal (v0 (remove-common-prefix x x)) nil)
   (equal (v1 (remove-common-prefix x x)) nil)))

(defun syntax-quote-remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (if (consp path1)
      (cond
       ((syn::consp path2)
        (let ((v (syn::car path2)))
          (if (and (syn::quotep v)
                   (equal (car path1) (syn::dequote v)))
              (syntax-quote-remove-common-prefix (cdr path1) (syn::cdr path2))
            (mv path1 path2))))
       ((syn::quotep path2)
        (met ((path1 path2) (remove-common-prefix path1 (syn::dequote path2)))
             (mv path1 (syn::enquote path2))))
       (t
        (mv path1 path2)))
    (mv path1 path2)))

(defthm pseudo-termp-syntax-quote-remove-common-prefix
  (implies
   (and
    (pseudo-termp y))
   (pseudo-termp (v1 (syntax-quote-remove-common-prefix x y))))
  :hints (("goal" :in-theory (enable pseudo-termp))))

(defthm diverge-remove-common-prefix-noop
  (equal (diverge (v0 (remove-common-prefix t1 t2))
                  (v1 (remove-common-prefix t1 t2)))
         (diverge t1 t2)))

(defthm syntax-quote-diverge-syntax-quote-remove-common-prefix-noop
  (equal (syntax-quote-diverge (v0 (syntax-quote-remove-common-prefix t1 t2))
                               (v1 (syntax-quote-remove-common-prefix t1 t2)))
         (syntax-quote-diverge t1 t2)))

(defun syntax-remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((syn::quotep path1)
    (met ((path1 path2) (syntax-quote-remove-common-prefix (syn::dequote path1) path2))
         (mv (syn::enquote path1) path2)))
   ((syn::quotep path2)
    (met ((path2 path1) (syntax-quote-remove-common-prefix (syn::dequote path2) path1))
         (mv path1 (syn::enquote path2))))
   ((and (syn::consp path1)
         (syn::consp path2))
    (let ((car1 (syn::car path1))
          (car2 (syn::car path2)))
      (if (equal car1 car2)
          (syntax-remove-common-prefix (syn::cdr path1) (syn::cdr path2))
        (mv path1 path2))))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (let ((arg11 (syn::arg 1 path1))
          (arg12 (syn::arg 1 path2)))
      (if (equal arg11 arg12)
          (syntax-remove-common-prefix (syn::arg 2 path1) (syn::arg 2 path2))
        (mv path1 path2))))
   ((equal path1 path2)
    (mv (syn::nil) (syn::nil)))
   (t (mv path1 path2))))

(defthm pseudo-termp-syntax-remove-common-prefix
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y))
   (and (pseudo-termp (v0 (syntax-remove-common-prefix x y)))
        (pseudo-termp (v1 (syntax-remove-common-prefix x y)))))
  :hints (("goal" :in-theory (enable pseudo-termp))))

(defthmd syntax-diverge-commute
  (equal (syntax-diverge x y)
         (syntax-diverge y x))
  :rule-classes ((:rewrite :loop-stopper ((y x)))))

(defthm syntax-diverge-syntax-remove-common-prefix-noop
  (equal (syntax-diverge (v0 (syntax-remove-common-prefix t1 t0))
                         (v1 (syntax-remove-common-prefix t1 t0)))
         (syntax-diverge t1 t0))
  :hints (("goal" :in-theory (e/d (syntax-diverge-commute)
                                  (;for efficiency:
                                   SYN::OPEN-LEN
                                   SYNTAX-QUOTE-DIVERGE)))))

(defun syntax-diverge-wrapper (term)
  (declare (type t term))
  (if (syn::funcall 'diverge 2 term)
      (let ((arg1 (syn::arg 1 term))
            (arg2 (syn::arg 2 term)))
        (met ((arg1 arg2) (syntax-remove-common-prefix arg1 arg2))
             (let ((hit (syntax-diverge arg1 arg2)))
               (if hit
                   hit
                 term))))
    term))

(defthm equal-len-implies-equal-len
  (implies
   (equal-len t1 t2)
   (iff (equal (len (syn::eval t1 a))
               (len (syn::eval t2 a)))
        t))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm syntax-diverge-implies-eval-commute
  (implies
   (syntax-diverge t1 t2)
   (equal (diverge (syn::eval t1 a) (syn::eval t2 a))
          (syn::eval (syntax-diverge t1 t2) a)))
  :hints (("goal" :in-theory (enable diverge-append-len-equal))))

(defthmd *meta*-syntax-diverge
  (iff (diverge-eval term a)
       (diverge-eval (syntax-diverge-wrapper term) a))
  :hints (("goal" :in-theory (enable syn::open-nth)))
  :rule-classes ((:meta :trigger-fns (diverge))))

;; Syntactic tail domination ..

(defun true-p (x)
  (declare (type t x)
           (ignore x))
  t)

(defun remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (remove-prefix (cdr prefix) (cdr x))
        (mv nil nil))
    (mv t x)))

(defun v0-remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (v0-remove-prefix (cdr prefix) (cdr x))
        nil)
    t))

(defun v1-remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (v1-remove-prefix (cdr prefix) (cdr x))
        nil)
    x))

(defthm v0-remove-prefix-reduction
  (equal (v0 (remove-prefix prefix x))
         (v0-remove-prefix prefix x)))

(defthm v1-remove-prefix-reduction
  (equal (v1 (remove-prefix prefix x))
         (v1-remove-prefix prefix x)))

(defthm list-fix-v1-remove-prefix
  (equal (list::fix (v1-remove-prefix prefix x))
         (v1-remove-prefix prefix (list::fix x))))

(defthm v0-remove-prefix-append
  (equal (v0-remove-prefix (append x y) z)
         (and (v0-remove-prefix x z)
              (v0-remove-prefix y (v1-remove-prefix x z)))))

(defthm v1-remove-prefix-append
  (equal (v1-remove-prefix (append x y) z)
         (and
          (v0-remove-prefix x z)
          (v1-remove-prefix y (v1-remove-prefix x z)))))

(defthm not-v0-implies-nil-v1-remove-prefix
  (implies
   (not (v0-remove-prefix x y))
   (equal (v1-remove-prefix x y) nil)))

#|
(defthm v0-to-v0-syntax-quote-remove-prefix
  (equal (v0 (syntax-quote-remove-prefix prefix x))
         (v0-syntax-quote-remove-prefix prefix x)))

(defthm v1-to-v1-syntax-quote-remove-prefix
  (equal (v1 (syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix x)))

(defthm list-fix-v1-syntax-quote-remove-prefix
  (equal (list::fix (v1-syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix (list::fix x))))

(defthm not-v0-implies-nil-v1-syntax-quote-remove-prefix
  (implies
   (not (v0-syntax-quote-remove-prefix x y))
   (equal (v1-syntax-quote-remove-prefix x y) nil)))

|#

(defun tail-p (x y)
  (declare (type t x y))
  (or (list::equiv x y)
      (and (consp y)
           (tail-p x (cdr y)))))

(defthm v1-remove-prefix-is-tail-x
  (implies
   (v0-remove-prefix prefix x)
   (tail-p (v1-remove-prefix prefix x) x)))

(defthm tail-p-implies
  (implies
   (tail-p x y)
   (<= (len x) (len y)))
  :rule-classes (:linear :rewrite))

#|

(defthmd list-fix-commutes-over-syntax-quote-remove-prefix
  (implies
   (syntaxp (symbolp x))
   (and
    (equal (list::fix (v1 (syntax-quote-remove-prefix prefix x)))
           (v1 (syntax-quote-remove-prefix prefix (list::fix x))))
    (equal (v0 (syntax-quote-remove-prefix prefix x))
           (v0 (syntax-quote-remove-prefix prefix (list::fix x)))
           ))))

(defthm v0-syntax-quote-remove-prefix-reduction
  (equal (v0 (syntax-quote-remove-prefix prefix x))
         (v0-syntax-quote-remove-prefix prefix x)))

(defthm v1-syntax-quote-remove-prefix-reduction
  (equal (v1 (syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix x)))

(defthmd vx-list-fix-commutes-over-syntax-quote-remove-prefix
  (implies
   (syntaxp (symbolp x))
   (and
    (equal (list::fix (v1-syntax-quote-remove-prefix prefix x))
           (v1-syntax-quote-remove-prefix prefix (list::fix x)))
    (equal (v0-syntax-quote-remove-prefix prefix x)
           (v0-syntax-quote-remove-prefix prefix (list::fix x)))))
  :hints (("goal" :use (:instance list-fix-commutes-over-syntax-quote-remove-prefix))))

(defthm not-v0-implies-nil-v1-syntax-quote-remove-prefix
  (implies
   (not (v0-syntax-quote-remove-prefix prefix x))
   (equal (v1-syntax-quote-remove-prefix prefix x) nil)))

(defthm v0-syntax-quote-remove-prefix-implies-v2-cong
  (implies
   (v0-syntax-quote-remove-prefix prefix x)
   (and (list::equiv (v1-syntax-quote-remove-prefix prefix x)
                         (v1-remove-prefix (syn::eval prefix bag::a) x))
        (v0-remove-prefix (syn::eval prefix bag::a) x)))
  :hints (("goal" :induct (syntax-quote-remove-prefix prefix x))))

|#

(defthmd dominates-append-2
  (equal (dominates x (append y z))
         (or (dominates x y)
             (and
              (v0-remove-prefix y x)
              (dominates (v1-remove-prefix y x) z))))
  :hints (("goal" :in-theory (enable dominates))))

(defthm syntax-quote-dominates-implies-dominates
  (implies
   (syntax-quote-dominates-p x y)
   (dominates x (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable dominates
                                     dominates-append-2))))

(defthm pseudo-termp-hyp-for-show-syntax-consp-from-alist
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-consp-from-alist term type-alist))))

(defthm show-syntax-consp-from-alist-to-hyp-for
  (iff (show-syntax-consp-from-alist term type-alist)
       (hyp-for-show-syntax-consp-from-alist term type-alist)))

(defthm show-syntax-consp-from-alist-works
  (implies
   (and
    (hyp-for-show-syntax-consp-from-alist x type-alist)
    (syn::eval (hyp-for-show-syntax-consp-from-alist x type-alist) bag::a))
   (consp (syn::eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

;; DAG -- This could be improved by checking each append term for
;; consp.

(defthm show-syntax-consp-to-hyp-for
  (iff (show-syntax-consp term type-alist)
       (hyp-for-show-syntax-consp term type-alist))
  :hints (("goal" :in-theory (enable
                              show-syntax-consp
                              hyp-for-show-syntax-consp
                              ))))

(defthm pseudo-termp-hyp-for-show-syntax-consp
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-consp term type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp
                              ))))

(defthm show-syntax-consp-works
  (implies
   (and
    (hyp-for-show-syntax-consp term type-alist)
    (syn::eval (hyp-for-show-syntax-consp term type-alist) bag::a))
   (consp (syn::eval term bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp
                              ))))

(defthm show-syntax-dominates-p-to-hyp-for
  (iff (show-syntax-dominates-p flg x y type-alist)
       (hyp-for-show-syntax-dominates-p flg x y type-alist))
  :hints (("goal" :induct (hyp-for-show-syntax-dominates-p-fn bag::a flg x y type-alist))))

(defthm pseudo-termp-hyp-for-show-syntax-dominates-p
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-dominates-p flg x y type-alist)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defun contains (symbol term)
  (declare (type t symbol term))
  (if (consp term)
      (if (consp (car term))
          (or (contains symbol (car term))
              (contains symbol (cdr term)))
        (or (equal symbol (car term))
            (contains symbol (cdr term))))
    (equal symbol term)))

(defthmd syntax-domination-implies-domination
  (implies
   (and
    (hyp-for-show-syntax-dominates-p flg x y type-alist)
    (syntaxp (contains 'syn::eval logical-x))
    (equal (syn::eval x bag::a) logical-x))
   (dominates logical-x (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm syntax-domination-implies-domination-helper
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (syn::eval x bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syntax-domination-implies-domination))))

(defthmd syntax-domination-implies-consp
  (implies
   (and
    (hyp-for-show-syntax-dominates-p flg x y type-alist)
    (syn::eval (hyp-for-show-syntax-dominates-p flg x y type-alist) bag::a)
    (syntaxp (contains 'syn::eval logical-x))
    (not flg)
    (equal logical-x (syn::eval x bag::a)))
   (consp logical-x))
  :hints (("goal" :in-theory (enable SYN::CONJOIN syn::open-nth))))

(defun tail-dominates-p (x y)
  (declare (type t x y))
  (cond
   ((consp x)
    (or (dominates x y)
        (tail-dominates-p (cdr x) y)))
   (t nil)))

(defun tail-dominates (x y)
  (declare (type t x y))
  (cond
   ((consp x)
    (met ((hit prefix) (tail-dominates (cdr x) y))
         (let ((dom (dominates x y)))
           (if (or hit dom)
               (mv t (cons (cons dom (car x)) prefix))
             (mv nil nil)))))
   (t (mv nil nil))))

(defthm booleanp-v0-tail-dominates
  (booleanp (v0 (tail-dominates x y))))

(defthm wf-prefix-v1-tail-dominates
  (wf-prefix (v1 (tail-dominates val v))))

(defthm v0-tail-dominates-to-tail-dominates-p
  (equal (v0 (tail-dominates x y))
         (tail-dominates-p x y)))

(defun prefixes (prefix)
  (declare (type (satisfies alistp) prefix))
  (if (consp prefix)
      (let ((list (list::map-cons (cdar prefix) (prefixes (cdr prefix)))))
        (if (caar prefix) (cons nil list)
          list))
    nil))

;; jcd removing this for list::map-cons
;; (defthm non-consp-memberp-map-cons
;;   (implies
;;    (not (consp x))
;;    (not (list::memberp x (map-cons a z)))))

(defthm consp-prefixes-v1-tail-dominates
  (implies
   (v0 (tail-dominates x y))
   (consp (prefixes (v1 (tail-dominates x y))))))

(defun true-listp-list (list)
  (declare (type t list))
  (if (consp list)
      (and (true-listp (car list))
           (true-listp-list (cdr list)))
    (null list)))

(defthm true-listp-car-true-listp-list
  (implies
   (true-listp-list list)
   (true-listp (car list))))

(defthm true-listp-list-prefixes
  (true-listp-list (prefixes list)))

(defun prefixed-tail-dominator-p (x prefix y)
  (declare (type t x prefix y))
  (and (consp x)
       (if (consp prefix)
           (and (equal (car prefix) (car x))
                (prefixed-tail-dominator-p (cdr x) (cdr prefix) y))
         (dominates x y))))

(defthm not-consp-y-not-prefixed-tail-dominator-p
  (implies
   (not (consp y))
   (not (prefixed-tail-dominator-p x prefix y))))

(defun list-prefixed-tail-dominator-p (x prefixes y)
  (declare (type t x prefixes y))
  (if (consp prefixes)
      (or (prefixed-tail-dominator-p x (car prefixes) y)
          (list-prefixed-tail-dominator-p x (cdr prefixes) y))
    nil))

(defthm not-consp-y-not-list-prefixed-tail-dominator-p
  (implies
   (not (consp y))
   (not (list-prefixed-tail-dominator-p x prefix y))))

(defthm not-consp-x-not-list-prefixed-tail-dominator-p
  (implies
   (not (consp x))
   (not (list-prefixed-tail-dominator-p x prefix y))))

(defthm list-prefixed-tail-dominator-p-from-memberp-prefixed-tail-dominator-p
  (implies
   (and
    (prefixed-tail-dominator-p x prefix y)
    (list::memberp prefix prefixes))
   (list-prefixed-tail-dominator-p x prefixes y)))

#+joe
(defthm list-prefixed-tail-dominator-p-from-memberp-prefixed-tail-dominator-membership
  (implies
   (and
    (prefixed-tail-dominator-p x prefix y)
    (list::memberp prefix prefixes))
   (list::memberp prefix (list-prefixed-tail-dominator-p x prefixes y))))

(defthm prefixed-tail-dominator-p-implies-len
  (implies
   (prefixed-tail-dominator-p x prefix y)
   (< (len prefix) (len x)))
  :rule-classes (:forward-chaining))

(defthm consp-dominates-implies-tail-dominates-p
  (implies
   (and
    (consp x)
    (dominates x y))
   (tail-dominates-p x y)))

(defthm not-consp-not-tail-dominates-p
  (implies
   (not (consp y))
   (not (tail-dominates-p x y))))

(defthm not-tail-dominates-p-implies-nil-prefix
  (implies
   (not (tail-dominates-p x y))
   (equal (v1 (tail-dominates x y)) nil)))

(defthm tail-dominates-append
  (implies
   (tail-dominates-p x z)
   (tail-dominates-p (append y x) z))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (append y x))))

(defun wf-syntax-prefix (prefix)
  (declare (type t prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (and (consp entry)
             (case (car entry)
                   (:cons
                    (wf-syntax-prefix (cdr prefix)))
                   (:append
                    (wf-syntax-prefix (cdr prefix)))
                   (:quote
                    (and (null (cdr prefix))
                         (true-listp (cdr entry))))
                   (t
                    nil))))
    (null prefix)))

(defthm wf-syntax-prefix-implies-true-listp
  (implies
   (wf-syntax-prefix prefix)
   (true-listp prefix))
  :rule-classes (:rewrite :forward-chaining))

(defun s2l (prefix a)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (cons (syn::eval (cdr entry) a)
                     (s2l (cdr prefix) a)))
              (:append
               (list::appendx (syn::eval (cdr entry) a)
                              (s2l (cdr prefix) a)))
              (:quote
               (cdr entry))
              (t
               nil)))
    nil))

(defthm true-listp-s2l
  (implies
   (wf-syntax-prefix pre)
   (true-listp (s2l pre a))))

(defthm wf-syntax-prefix-syntax-quote-tail-dominates
  (wf-syntax-prefix (v1 (syntax-quote-tail-dominates x y))))

(defthm syntax-quote-tail-dominates-implies-tail-dominates
  (implies
   (v0 (syntax-quote-tail-dominates x y))
   (tail-dominates-p x (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable syntax-domination-implies-consp
                                     syntax-domination-implies-domination))))

(defthmd not-consp-membership-implies-dominates
  (implies (and (not (consp pre))
                (list::memberp pre (prefixes (v1 (tail-dominates x y)))))
           (dominates x y)))

;; jcd removing this for list::map-cons
;; (defthm memberp-x-map-cons
;;   (equal (list::memberp x (map-cons a y))
;;          (and (consp x)
;;               (equal (car x) a)
;;               (list::memberp (cdr x) y))))

(defthmd memberp-not-consp-prefixes
  (implies
   (not (consp pre))
   (equal (list::memberp pre (prefixes (val 1 (tail-dominates x y))))
          (and (null pre) (consp x) (dominates x y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     not-consp-membership-implies-dominates)
           :expand (tail-dominates x y))))

(defthm s2l-membership-in-syntax-quote-tail-dominates
  (implies
   (v0 (syntax-quote-tail-dominates x y))
   (list::memberp (s2l (v1 (syntax-quote-tail-dominates x y)) bag::a)
                 (prefixes (v1 (tail-dominates x (syn::eval y bag::a))))))
  :hints (("goal" :induct (syntax-quote-tail-dominates-fn bag::a x y))
          (and acl2::stable-under-simplificationp
               `(:in-theory
                 (enable
                  memberp-not-consp-prefixes
                  syntax-domination-implies-domination
                  syntax-domination-implies-consp
                  memberp-not-consp-prefixes
                  )))))

(defthm show-syntax-tail-dominates-to-hyp-for
  (iff (v0 (show-syntax-tail-dominates x y type-alist))
       (hyp-for-show-syntax-tail-dominates x y type-alist)))

(defthm pseduo-termp-hyp-for-show-syntax-tail-dominates
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-tail-dominates x y type-alist))))

(defthm wf-syntax-prefix-show-syntax-tail-dominates
  (wf-syntax-prefix (v1 (show-syntax-tail-dominates x y type-alist))))

#+joe
(defthm tail-dominates-p-from-dominates
  (implies
   (dominates x y)
   (tail-dominates-p x y)))

(defthm show-syntax-tail-dominates-implies-tail-dominates
  (implies
   (and
    (hyp-for-show-syntax-tail-dominates x y type-alist)
    (syn::eval (hyp-for-show-syntax-tail-dominates x y type-alist) bag::a))
   (tail-dominates-p (syn::eval x bag::a) (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable syn::open-nth
                                     syn::conjoin
                                     syntax-domination-implies-consp
                                     syntax-domination-implies-domination))))

(defthm memberp-prefixes-implies-memberp-prefixes-append
  (implies
   (list::memberp list (prefixes (v1 (tail-dominates x y))))
   (list::memberp (append z list) (prefixes (v1 (tail-dominates (append z x) y)))))
  :hints (("goal" :induct (len z)
           :in-theory (enable binary-append))))

(defthm s2l-membership-in-prefixes
  (implies
   (and
    (hyp-for-show-syntax-tail-dominates x y type-alist)
    (syn::eval (hyp-for-show-syntax-tail-dominates x y type-alist) bag::a))
   (list::memberp (s2l (v1 (show-syntax-tail-dominates x y type-alist)) bag::a)
                  (prefixes (v1 (tail-dominates (syn::eval x bag::a) (syn::eval y bag::a))))))
  :hints (("goal"
           :in-theory (e/d
                       (syn::open-nth
                        syn::conjoin
                        syn::open-len

                        syntax-domination-implies-domination
                        syntax-domination-implies-consp
                        memberp-not-consp-prefixes

                        )
                       ( ;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
                        (:REWRITE WF-SYNTAX-PREFIX-IMPLIES-TRUE-LISTP)
                        (:DEFINITION TRUE-LISTP)
                        (:REWRITE SYN::CONSP-REC-IMPLIES-CONSP)
                        (:DEFINITION SYN::CONSP-REC)
                        ;(:REWRITE list::EQUAL-OF-BOOLEANS-REWRITE)
                        (:rewrite acl2::equal-booleans-reducton)
                        (:REWRITE list::EQUAL-CAR-DIFFERENTIAL)
                        (:REWRITE list::CONSP-APPEND)
                        (:REWRITE list::CDR-APPEND)
                        (:REWRITE list::APPEND-OF-NON-CONSP-ONE)
                        (:TYPE-PRESCRIPTION SYN::CONSP-REC)
                        SYNTAX-QUOTE-DOMINATES-P-FN
                        TAIL-DOMINATES-P
                        SYNTAX-QUOTE-TAIL-DOMINATES-FN
                        DOMINATES-SAME-LEN-CHEAP

                        ))
           :induct (show-syntax-tail-dominates-fn bag::a x y type-alist))
          ))

(defthm syntax-quote-quote-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
  (implies
   (syntax-quote-quote-prefixed-tail-dominator-p x prefix y)
   (prefixed-tail-dominator-p x prefix (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syntax-domination-implies-consp
                                     syntax-domination-implies-domination)))
  :rule-classes (:rewrite :forward-chaining))

(defthm show-syntax-prefixed-tail-dominator-p-to-hyp-for
  (iff (show-syntax-prefixed-tail-dominator-p x prefix y type-alist)
       (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist)))

(defthm pseudo-termp-hyp-for-show-syntax-prefixed-tail-dominator-p
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist))))

(defthm prefixed-tail-dominator-p-append
  (implies
   (and
    (prefixed-tail-dominator-p x y z)
    (equal w k))
   (prefixed-tail-dominator-p (append w x) (append k y) z))
  :hints (("goal" :induct (list::len-len-induction w k))))

#+joe
(defthm list-prefixed-tail-dominator-p-append
  (implies
   (and
    (list-prefixed-tail-dominator-p x y z)
    (equal w k))
   (list-prefixed-tail-dominator-p (append w x) (map-append k y) z))
  :hints (("goal" :induct (list::len-len-induction w k))))

(defun len-len-len-induction (x y z)
  (if (and (consp x)
           (consp y)
           (consp z))
      (len-len-len-induction (cdr x) (cdr y) (cdr z))
    (list x y z)))

(defthm show-syntax-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
  (implies
   (and
    (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist)
    (syn::eval (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist) bag::a))
   (prefixed-tail-dominator-p (syn::eval x bag::a) (s2l prefix bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth
                                     syn::conjoin
                                     syntax-domination-implies-consp
                                     syntax-domination-implies-domination)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-membership-implies-prefixed-tail-dominator
  (implies
   (list::memberp pre (prefixes (v1 (tail-dominates x y))))
   (prefixed-tail-dominator-p x pre y))
  :hints (("goal" :in-theory (enable list::memberp)
           :induct (list::len-len-induction pre x))))

(defthm prefixed-tail-dominator-membership-implies-tail-dominates-p
  (implies
   (list::memberp pre (prefixes (v1 (tail-dominates x y))))
   (tail-dominates-p x y))
  :hints (("goal" :in-theory (enable list::memberp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-p-implies-v0-tail-dominates
  (implies
   (prefixed-tail-dominator-p x pre y)
   (and (v0 (tail-dominates x y))
        (tail-dominates-p x y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm list-prefixed-tail-dominator-p-implies-v0-tail-dominates
  (implies
   (list-prefixed-tail-dominator-p x pre y)
   (and (v0 (tail-dominates x y))
        (tail-dominates-p x y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-implies-membership-tail-dominates
  (implies
   (prefixed-tail-dominator-p x pre y)
   (equal (list::memberp pre (prefixes (v1 (tail-dominates x y))))
          (true-listp pre)))
  :hints (("goal" :in-theory (enable list::memberp)
           :induct (list::len-len-induction pre x))))

(defthm show-syntax-prefixed-tail-dominator-p-implies-memberp
  (implies
   (and
    (hyp-for-show-syntax-prefixed-tail-dominator-p x pre y type-alist)
    (syn::eval (hyp-for-show-syntax-prefixed-tail-dominator-p x pre y type-alist) bag::a)
    (wf-syntax-prefix pre))
   (list::memberp (s2l pre bag::a) (prefixes (v1 (tail-dominates (syn::eval x bag::a) (syn::eval y bag::a))))))
  :hints (("goal" :in-theory '(true-listp-s2l
                               show-syntax-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
                               prefixed-tail-dominator-implies-membership-tail-dominates
                               ))))

(defun contains-prefixed-tail-dominator-p (list pre x)
  (declare (type t x pre list))
  (if (consp list)
      (or (prefixed-tail-dominator-p (car list) pre x)
          (contains-prefixed-tail-dominator-p (cdr list) pre x))
    nil))

(defthm contains-prefixed-tail-dominator-p-membership-reduction
  (implies
   (list::memberp v list)
   (equal (contains-prefixed-tail-dominator-p list pre y)
          (or (prefixed-tail-dominator-p v pre y)
              (contains-prefixed-tail-dominator-p (bag::remove-1 v list) pre y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len list))))

#+joe
(defthm not-prefixed-tail-dominator-p-remove-1-reduction
  (implies
   (not (list-prefixed-tail-dominator-p x pre y))
   (equal (contains-prefixed-tail-dominator-p (bag::remove-1 x list) pre y)
          (contains-prefixed-tail-dominator-p list pre y)))
  :hints (("goal" :in-theory (enable bag::remove-1))))

#+joe
(defthm membership-reduction
  (implies
   (and
    (list::memberp x list)
    (prefixed-tail-dominator-p x pre y))
   (contains-prefixed-tail-dominator-p list pre y))
  :hints (("goal" :in-theory (enable list::memberp))))

(defthm contains-prefixed-tail-dominator-p-append-2
  (implies
   (contains-prefixed-tail-dominator-p list pre x)
   (contains-prefixed-tail-dominator-p (append y list) pre x))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append y list))))

(defthm contains-prefixed-tail-dominator-p-append-1
  (implies
   (contains-prefixed-tail-dominator-p z pre x)
   (contains-prefixed-tail-dominator-p (append z a) pre x)))

(defun contains-list-prefixed-tail-dominator-p (list prefixes x)
  (declare (type t x prefixes list))
  (if (consp list)
      (or (list-prefixed-tail-dominator-p (car list) prefixes x)
          (contains-list-prefixed-tail-dominator-p (cdr list) prefixes x))
    nil))

(local (in-theory (disable LIST-PREFIXED-TAIL-DOMINATOR-P)))

(defthm contains-list-prefixed-tail-dominator-p-membership-reduction
  (implies
   (list::memberp v list)
   (equal (contains-list-prefixed-tail-dominator-p list prefixes x)
          (or (list-prefixed-tail-dominator-p v prefixes x)
              (contains-list-prefixed-tail-dominator-p (bag::remove-1 v list) prefixes x))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len list))))

(defthm contains-list-prefixed-tail-dominator-p-append-2
  (implies
   (contains-list-prefixed-tail-dominator-p list pre x)
   (contains-list-prefixed-tail-dominator-p (append y list) pre x))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append y list))))

(defthm contains-list-prefixed-tail-dominator-p-append-1
  (implies
   (contains-list-prefixed-tail-dominator-p z pre x)
   (contains-list-prefixed-tail-dominator-p (append z a) pre x)))

(defthmd member-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
  (implies
   (and
    (contains-prefixed-tail-dominator-p list pre x)
    (list::memberp pre prefixes))
   (contains-list-prefixed-tail-dominator-p list prefixes x))
  :hints (("goal" :in-theory (enable list::memberp))))

(in-theory
 (disable
  NOT-CONSP-MEMBERSHIP-IMPLIES-DOMINATES
  MEMBERP-NOT-CONSP-PREFIXES
  PREFIXED-TAIL-DOMINATOR-IMPLIES-MEMBERSHIP-TAIL-DOMINATES
  ))

(defthm syntax-quote-contains-prefixed-tail-dominator-implies-contains-prefixed-tail-dominator-p
  (implies
   (syntax-quote-contains-prefixed-tail-dominator list pre n x)
   (contains-prefixed-tail-dominator-p list pre (syn::eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-contains-prefixed-tail-dominator-to-hyp-for
  (iff (syntax-contains-prefixed-tail-dominator list pre n x type-alist)
       (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)))

(defthm pseudo-termp-hyp-for-syntax-contains-prefixed-tail-dominator
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist))))

(defthm syntax-contains-prefixed-tail-dominator-implies-contains-prefixed-tail-dominator-p
  (implies
   (and
    (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)
    (syn::eval (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist) bag::a))
   (contains-prefixed-tail-dominator-p (syn::eval list bag::a) (s2l pre bag::a) (syn::eval x bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth syn::conjoin)))
  :rule-classes (:rewrite :forward-chaining))

(defthm member-syntax-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
  (implies
   (and
    (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)
    (syn::eval (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist) bag::a)
    (list::memberp (s2l pre bag::a) prefixes))
   (contains-list-prefixed-tail-dominator-p (syn::eval list bag::a) prefixes (syn::eval x bag::a)))
  :hints (("goal" :use (:instance member-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
                                  (list (syn::eval list bag::a))
                                  (pre  (s2l pre bag::a))
                                  (x    (syn::eval x bag::a))
                                  (prefixes prefixes)))))

(defund tail-dominator-body (val rest x y)
  (declare (type t x y))
  (met ((hit prex) (tail-dominates val x))
       (or (and hit (contains-list-prefixed-tail-dominator-p rest (prefixes prex) y))
           (met ((hit prey) (tail-dominates val y))
                (and hit (contains-list-prefixed-tail-dominator-p rest (prefixes prey) x))))))

(defthm list-prefixed-tail-dominator-p-map-cons
  (equal (list-prefixed-tail-dominator-p w (list::map-cons a list) y)
         (and (consp w)
              (equal (car w) a)
              (list-prefixed-tail-dominator-p (cdr w) list y)))
  :hints (("goal" :in-theory (enable LIST-PREFIXED-TAIL-DOMINATOR-P)
           :induct (len list))))

(defun tail-dominator-body-body (v w x y)
  (met ((hitx prex) (tail-dominates v x))
       (met ((hity prey) (tail-dominates v y))
            (or (and hitx (list-prefixed-tail-dominator-p w (prefixes prex) y))
                (and hity (list-prefixed-tail-dominator-p w (prefixes prey) x))))))

(defun tail-dominator-body-rec (val rest x y)
  (if (consp rest)
      (or (tail-dominator-body-body val (car rest) x y)
          (tail-dominator-body-rec val (cdr rest) x y))
    nil))

(defthm tail-dominator-boody-to-tail-dominator-body-rec
  (equal (tail-dominator-body val rest x y)
         (tail-dominator-body-rec val rest x y))
  :hints (("goal" :in-theory (enable tail-dominator-body)
           :induct (len rest))))

(in-theory
 (disable
  tail-dominator-body
  ))

(defun tail-dominator-body-body-rec (w v x y)
  (if (and (consp w)
           (consp v))
      (or (and (dominates w x)
               (dominates v y))
          (and (dominates v x)
               (dominates w y))
          (and (equal (car w) (car v))
               (tail-dominator-body-body-rec (cdr w) (cdr v) x y)))
    nil))

(defthm open-tail-dominates
  (implies
   (consp x)
   (equal (tail-dominates x y)
          (met ((hit prefix)
                (tail-dominates (cdr x) y))
               (let ((dom (dominates x y)))
                    (if (or hit dom)
                        (mv t (cons (cons dom (car x)) prefix))
                        (mv nil nil)))))))

(defthm tail-dominator-body-body-is-tail-dominator-body-body-rec
  (equal (tail-dominator-body-body w v x y)
         (tail-dominator-body-body-rec w v x y))
  :hints (("Goal" :in-theory (e/d (LIST-PREFIXED-TAIL-DOMINATOR-P)
                                  ( TAIL-DOMINATES ;efficiency
                                      CONSP-PREFIXES-V1-TAIL-DOMINATES
                                      STRICTLY-DOMINATES-IMPLIES-DOMINATES
                                      ;LIST::MV-NTH-TO-VAL
                                      ;LIST-PREFIXED-TAIL-DOMINATOR-P
                                      ;TAIL-DOMINATES-P
                                      ))))
  )

(defthm tail-dominator-body-body-commutes-first-2
  (equal (tail-dominator-body-body-rec v w x y)
         (tail-dominator-body-body-rec w v x y)))

(defthm tail-dominator-body-body-commutes-last-2
  (equal (tail-dominator-body-body-rec v w x y)
         (tail-dominator-body-body-rec v w y x)))

(defthm tail-dominator-body-commutes-last-2
  (equal (tail-dominator-body-rec val rest x y)
         (tail-dominator-body-rec val rest y x)))

(in-theory
 (disable
  tail-dominator-body-body
  ))

(defthm tail-dominator-body-rec-membership-reduction
  (implies
   (list::memberp v rest)
   (equal (tail-dominator-body-rec val rest x y)
          (or (tail-dominator-body-body-rec val v x y)
              (tail-dominator-body-rec val (bag::remove-1 v rest) x y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len rest))))

(defun contains-unique-prefixed-tail-dominators (list x y)
  (declare (type t list x y))
  (if (consp list)
      (let ((rest (cdr list))
            (val  (car list)))
        (or (tail-dominator-body val rest x y)
            (contains-unique-prefixed-tail-dominators rest x y)))
    nil))

(defthm contains-unique-prefixed-tail-dominators-membership-deconstruction
  (implies
   (list::memberp v list)
   (equal (contains-unique-prefixed-tail-dominators list x y)
          (or (tail-dominator-body v (bag::remove-1 v list) x y)
              (contains-unique-prefixed-tail-dominators (bag::remove-1 v list) x y))))
  :hints (("goal" :in-theory (enable bag::remove-1))))

(defthm contains-unique-prefixed-tail-dominators-commutes
  (equal (contains-unique-prefixed-tail-dominators list x y)
         (contains-unique-prefixed-tail-dominators list y x)))

(defthm contains-unique-prefixed-tail-dominators-append-1
  (implies
   (contains-unique-prefixed-tail-dominators list x y)
   (contains-unique-prefixed-tail-dominators (append z list) x y))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append z list))))

(defthm contains-unique-prefixed-tail-dominators-append-2
  (implies
   (contains-unique-prefixed-tail-dominators z x y)
   (contains-unique-prefixed-tail-dominators (append z a) x y)))

(defthm syntax-contains-unique-prefixed-tail-dominators-to-hyp-for
  (iff (syntax-contains-unique-prefixed-tail-dominators list x y type-alist)
       (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist))
  :hints (("Goal" :in-theory (disable ;efficiency:
                              HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                              HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                              SYN::OPEN-LEN
                              SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES-P
                              HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES
                              HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                              ))))

(defthm pseudo-termp-hyp-for-syntax-contains-unique-prefixed-tail-dominators
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist)))
  :hints (("Goal" :in-theory (disable ;efficiency:
                              HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                              HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                              SYN::OPEN-LEN
                              SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES-P
                              HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES
                              HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                              ))))


(defthm syntax-contains-unique-prefixed-tail-dominators-implies-contains-unique-prefixed-tail-dominators
  (implies
   (and
    (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist)
    (syn::eval (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist) bag::a))
   (contains-unique-prefixed-tail-dominators (syn::eval list bag::a) (syn::eval x bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (e/d
                              (syn::conjoin syn::open-nth TAIL-DOMINATOR-BODY)
                              (;TAIL-DOMINATOR-BODY
                               SYNTAX-QUOTE-DOMINATES-P-FN ;these for efficiency
                               TAIL-DOMINATES
                               TAIL-DOMINATES-P
                               CONTAINS-LIST-PREFIXED-TAIL-DOMINATOR-P
                               LIST-PREFIXED-TAIL-DOMINATOR-P
                               HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                               SYNTAX-QUOTE-TAIL-DOMINATES-FN
                               HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                               HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                               SHOW-SYNTAX-TAIL-DOMINATES-FN
                               HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                               SHOW-SYNTAX-DOMINATES-P-FN

                               TAIL-DOMINATOR-BOODY-TO-TAIL-DOMINATOR-BODY-REC
                               (:REWRITE SYN::CONSP-REC-IMPLIES-CONSP)
                               (:DEFINITION SYN::CONSP-REC)
                               (:REWRITE BAG::SUBBAGP-CDR-LEMMA)
                               ;(:REWRITE list::EQUAL-OF-BOOLEANS-REWRITE)
                               (:rewrite acl2::equal-booleans-reducton)
                               (:REWRITE list::EQUAL-CAR-DIFFERENTIAL)
                               (:REWRITE BAG::SUBBAGP-WHEN-CDR-IS-NON-CONSP))
                              ))))

(defthm diverge-tail-dominator-body-body-rec-implies-diverge
  (implies
   (and
    (tail-dominator-body-body-rec a b x y)
    (diverge a b))
   (diverge x y))
  :hints (("goal" :induct (tail-dominator-body-body-rec a b x y))))

(defthm all-diverge-from-all-tail-dominator-body-implies-diverge
  (implies
   (and
    (tail-dominator-body-rec val rest x y)
    (diverges-from-all val rest))
   (diverge x y))
  :hints (("goal" :in-theory (enable diverges-from-all))))

(defthm all-diverge-from-all-contains-unique-prefixed-tail-dominators-implies-diverge
  (implies
   (and
    (all-diverge list)
    (contains-unique-prefixed-tail-dominators list x y))
   (diverge x y))
  :hints (("goal" :in-theory (enable all-diverge))))

(local (in-theory (disable HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN)))

(defthm to-hyp-for-show-prefix-diverge-from-type-alist
  (iff (show-prefix-diverge-from-type-alist a b alist wlist)
       (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist))
  :hints (("goal" :in-theory (enable show-prefix-diverge-from-type-alist
                                     hyp-for-show-prefix-diverge-from-type-alist))))

(defthm psedu-termp-hyp-for-show-prefix-diverge-from-type-alist
  (implies
   (and
    (acl2::type-alistp type-alist)
    (acl2::type-alistp whole-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-type-alist a b type-alist whole-alist)))
  :hints (("goal" :in-theory (enable hyp-for-show-prefix-diverge-from-type-alist))))

(DEFTHM
  PD-EVAL-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
  (IMPLIES
   (and
    (hyp-for-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS LIST X Y type-alist)
    (pd-eval (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist) bag::a))
   (CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS (PD-EVAL LIST BAG::A)
                                             (PD-EVAL X BAG::A)
                                             (PD-EVAL Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :HINTS
  (("Goal"
    :in-theory (enable pd-eval-constraint-0)
    :USE
    (:FUNCTIONAL-INSTANCE
     (:INSTANCE
      SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
      (bag::A bag::A)
      (Y Y)
      (X X)
      (type-alist type-alist)
      (LIST LIST))
     (SYN::EVAL PD-EVAL)
     (SYN::EVAL-LIST PD-EVAL-LIST)))))

(defthm pd-eval-show-not-equal-from-type-alist-works-right
  (implies
   (and
    (bag::hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)
    (pd-eval (bag::hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist) bag::a)
    )
   (not (equal (pd-eval x bag::a)
               (pd-eval y bag::a))))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal"
    :in-theory (enable pd-eval-constraint-0)
    :USE
    (:FUNCTIONAL-INSTANCE
     (:INSTANCE
      bag::show-not-equal-from-type-alist-works-right
      (bag::A bag::A)
      (bag::Y Y)
      (bag::X X)
      (bag::N n)
      (bag::type-alist type-alist)
      (bag::whole-type-alist whole-type-alist)
      )
     (BAG::syntax-EV PD-EVAL)
     (bag::syntax-ev-list PD-EVAL-LIST)))))

(defthm show-prefix-diverge-from-type-alist-works
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist)
    (pd-eval (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist) bag::a))
   (diverge (pd-eval a bag::a) (pd-eval b bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d (syn::conjoin
                                   syn::open-nth
                                   hyp-for-show-prefix-diverge-from-type-alist)
                                  (
(:DEFINITION HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN)
(:DEFINITION HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN)
(:REWRITE PREFIXED-TAIL-DOMINATOR-MEMBERSHIP-IMPLIES-PREFIXED-TAIL-DOMINATOR)
(:DEFINITION TAIL-DOMINATES-P)
(:DEFINITION TAIL-DOMINATES)
;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN)
(:DEFINITION PREFIXED-TAIL-DOMINATOR-P)
(:REWRITE acl2::MV-NTH-TO-VAL)
(:REWRITE NOT-TAIL-DOMINATES-P-IMPLIES-NIL-PREFIX)
(:REWRITE NOT-DOMINATES-FROM-DIVERGE-ONE)
(:DEFINITION CONTAINS-PREFIXED-TAIL-DOMINATOR-P)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN)
(:REWRITE V0-TAIL-DOMINATES-TO-TAIL-DOMINATES-P)
(:DEFINITION SHOW-SYNTAX-TAIL-DOMINATES-FN)
)))))

(defthm pd-eval-syntax-diverge-implies-eval-commute
  (implies
   (syntax-diverge t1 t2)
   (diverge (pd-eval t1 a) (pd-eval t2 a)))
  :hints (("Goal"
           :USE
           (:FUNCTIONAL-INSTANCE
            (:INSTANCE
             syntax-diverge-implies-diverge
             (a a)
             (t1 t1)
             (t2 t2))
            (SYN::EVAL PD-EVAL)
            (SYN::EVAL-LIST PD-EVAL-LIST)))))

(defun syn::singleton (term)
  (declare (type t term))
  (cond
   ((syn::consp term)
    (syn::null (syn::cdr term)))
   ((syn::quotep term)
    (let ((term (syn::dequote term)))
      (and (consp term)
           (not (consp (cdr term))))))
   (t nil)))

(defund syn::single-car (term)
  (declare (type (satisfies syn::singleton) term))
  (if (syn::consp term)
      (syn::car term)
    (syn::enquote (car (syn::dequote term)))))

(defthm pseudo-termp-single-car
  (implies
   (pseudo-termp term)
   (pseudo-termp (syn::single-car term)))
  :hints (("goal" :in-theory (enable
                              pseudo-termp
                              syn::single-car
                              ))))

(in-theory
 (disable
  syn::singleton
  ))

(defthm pseudo-termp-hyp-for-show-prefix-diverge-from-alist-body
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-alist-body x y type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist-body
                              ))))

(defthm show-prefix-diverge-from-alist-body-to-hyp-for
  (iff (show-prefix-diverge-from-alist-body x y type-alist)
       (hyp-for-show-prefix-diverge-from-alist-body x y type-alist))
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist-body
                              hyp-for-show-prefix-diverge-from-alist-body
                              ))))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist-body
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist-body x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist-body x y type-alist) bag::a))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d
                              (hyp-for-show-prefix-diverge-from-alist-body
                               bag::make-conjunction
                               )
                              (
                               pd-eval-show-not-equal-from-type-alist-works-right
                               ))
           :use (:instance
                 pd-eval-show-not-equal-from-type-alist-works-right
                 (x (syn::single-car x))
                 (y (syn::single-car y))
                 (n (BAG::USB16-FIX (LEN TYPE-ALIST)))
                 (whole-type-alist type-alist)
                 ))
          (and acl2::stable-under-simplificationp
               `(:in-theory (e/d
                             (
                              syn::single-car
                              syn::singleton
                              diverge
                              )
                             (pd-eval-show-not-equal-from-type-alist-works-right
                              ))))))

(defthmd syntax-quote-remove-common-prefix-pd-eval-diverge
  (implies
   (diverge (v0 (syntax-quote-remove-common-prefix x y))
            (pd-eval (v1 (syntax-quote-remove-common-prefix x y)) bag::a))
   (diverge x (pd-eval y bag::a))))

(defthmd syntax-remove-common-prefix-pd-eval-diverge
  (implies
   (diverge (pd-eval (v0 (syntax-remove-common-prefix x y)) bag::a)
            (pd-eval (v1 (syntax-remove-common-prefix x y)) bag::a))
   (diverge (pd-eval x bag::a)
            (pd-eval y bag::a)))
  :hints (("goal"
           :in-theory (e/d
                       (syn::open-nth
                        syntax-quote-remove-common-prefix-pd-eval-diverge)
                       (;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
                        (:REWRITE WF-SYNTAX-PREFIX-IMPLIES-TRUE-LISTP)
                        (:DEFINITION WF-SYNTAX-PREFIX)
                        (:DEFINITION TRUE-LISTP)
                        (:REWRITE PD-EVAL-SYNTAX-DIVERGE-IMPLIES-EVAL-COMMUTE)
                        (:DEFINITION SYNTAX-DIVERGE))))))

(defthm show-prefix-diverge-from-alist-to-hyp-for
  (iff (show-prefix-diverge-from-alist x y type-alist)
       (hyp-for-show-prefix-diverge-from-alist x y type-alist))
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(defthm pseudo-termp-hyp-for-show-prefix-diverge-from-alist
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-alist x y type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist x y type-alist) bag::a))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable
                              syntax-remove-common-prefix-pd-eval-diverge
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(defun show-prefix-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc))
  (if (syn::funcall 'diverge 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((zed #+joe(and (@ show-prefix-diverge-from-mfc)
                             (cw "** show-prefix-diverge-from-mfc(~x0,~x1)?~%" x y))
                   nil))
          (declare (ignore zed))
          (let ((type-alist (acl2::mfc-type-alist mfc)))
            (if (show-prefix-diverge-from-alist-fn nil x y type-alist)
                (acl2::prog2$
                 #+joe
                 (and (@ show-prefix-diverge-from-mfc)
                      (cw "** show-prefix-diverge-from-mfc!~%"))
                 nil
                 (syn::true))
              term))))
    term))

(defun hyp-for-show-prefix-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverge 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (let ((hyp (hyp-for-show-prefix-diverge-from-alist-fn nil x y type-alist)))
            (if hyp (bag::bind-extra-vars-in-hyp hyp term)
              (syn::nil)))))
    (syn::nil)))

(defthm meta-rule-to-show-prefix-diverge
  (implies (pd-eval (hyp-for-show-prefix-diverge-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
                  (pd-eval (show-prefix-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       syn::open-nth
                       syn::conjoin
                       hyp-for-show-prefix-diverge-from-alist-irrelevant
                       bag::make-conjunction
                       )
           :do-not '(generalize eliminate-destructors))))

(defun show-domination-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (syn::funcall 'dominates 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (if (show-syntax-dominates-p-fn nil t x y type-alist)
              (syn::true)
            (if (show-syntax-dominates-p-fn nil t y x type-alist)
                `(if (list::equiv ,y ,x) ,(syn::true) ,(syn::nil))
              term))))
    term))

(defun hyp-for-show-domination-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (syn::funcall 'dominates 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (let ((hyp (hyp-for-show-syntax-dominates-p-fn nil t x y type-alist)))
            (if hyp
                (bag::bind-extra-vars-in-hyp hyp term)
              (let ((hyp (hyp-for-show-syntax-dominates-p-fn nil t y x type-alist)))
                (if hyp
                    (bag::bind-extra-vars-in-hyp hyp term)
                  (syn::nil)))))))
    (syn::nil)))

(defthm pd-eval-syntax-domination-implies-domination
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (pd-eval x bag::a) (pd-eval y bag::a)))
  :hints (("goal" :use (:functional-instance syntax-domination-implies-domination-helper
                                             (syn::eval pd-eval)
                                             (syn::eval-list pd-eval-list)))))

(defthmd non-domination-from-not-equal-dominates
  (implies
   (and
    (dominates x y)
    (not (list::equiv x y)))
   (not (dominates y x)))
  :hints (("goal" :in-theory
           (enable
            dominates
            ))))

(defthm meta-rule-to-show-prefix-domination
  (implies (pd-eval (hyp-for-show-domination-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
                  (pd-eval (show-domination-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (dominates)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       syn::open-nth
                       syn::conjoin
                       non-domination-from-not-equal-dominates
                       hyp-for-show-syntax-dominates-p-irrelevant
                       bag::make-conjunction
                       )
           :do-not '(generalize eliminate-destructors))))

(defun all-diverge-remove-prefix (paths)
  (if (not (syn::consp paths)) paths
      (syn::cons (syn::cdr (syn::car paths)) (all-diverge-remove-prefix (syn::cdr paths)))))

(defthm all-diverge-remove-prefix-open
  (implies
   (syn::consp paths)
   (equal (all-diverge-remove-prefix paths)
          (syn::cons (syn::cdr (syn::car paths)) (all-diverge-remove-prefix (syn::cdr paths))))))

(defun all-diverge-prefix-meta-fn (term)
  (if (and (syn::consp term)
           (syn::consp (syn::cdr term))
           (equal 'all-diverge (car term)))
      (if (syn-prefix-p (syn::cdr term))
          (let ((pruned (all-diverge-remove-prefix (syn::cdr term))))
                 (list 'all-diverge pruned))
        term)
    term))

(defthm not-syn-consp-all-diverge-prefix-meta-fn
  (implies (not (syn::consp term))
           (equal (all-diverge-prefix-meta-fn term)
                  term)))

(defun syntax-dominates (p1 p2)
  (if (syn::consp p1)
      (and (syn::consp p2)
           (equal (syn::car p1) (syn::car p2))
           (syntax-dominates (syn::cdr p1) (syn::cdr p2)))
    t))

#+joe ;; better definition later
(defun syntax-dominated-by-some (p paths)
  (if (syn::consp paths)
      (if (syntax-dominates (syn::car paths) p)
          t
        (syntax-dominated-by-some p (syn::cdr paths)))
    nil))

(defun remove-dominator (p paths)
  (if (syn::consp paths)
      (if (syntax-dominates (syn::car paths) p)
          (syn::cdr paths)
        (syn::cons (syn::car paths) (remove-dominator p (syn::cdr paths))))
      paths))

(defthm meta-all-diverge-prefix
  (equal (meta-all-diverge-prefix-ev term alist)
         (meta-all-diverge-prefix-ev (all-diverge-prefix-meta-fn term) alist))
  :rule-classes ((:meta :trigger-fns (all-diverge)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :induct (all-diverge-remove-prefix term))
          ("Subgoal *1/1" :in-theory (disable all-diverge-prefix-meta-fn)))
:otf-flg t)

(in-theory (disable (:rewrite wf-syntax-prefix-implies-true-listp)
                    (:definition wf-syntax-prefix)))

;; jcd - I think we want to use this as a replacement for dominates-weakly-
;; asymmetric.  basically, just change the normal form for mutually dominating
;; paths from "equal lengths" to "list equiv".
(defthm dominates-asymmetric
  (implies (dominates p2 p1)
           (equal (dominates p1 p2)
                  (list::equiv p1 p2)))
  :hints (("Goal" :in-theory (enable dominates))))

(in-theory (disable dominates-weakly-asymmetric))


;; add a bachchain limit to diverges-from-all-when-no-domination
(defthm diverges-from-all-when-no-domination-cheap
  (implies (and (not (dominated-by-some a x))
                (not (dominates-some a x)))
           (diverges-from-all a x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable diverges-from-all-when-no-domination))


;; jcd - move this rule to dominates.lisp
(defthm first-dominator-dominates-free
  (implies (equal (first-dominator a x) b)
           (dominates b a)))


;; jcd - added this
;; jcd bzo move to dominates.lisp
(defthm dominated-by-some-of-cdr-forward-to-dominated-by-some
  (implies (dominated-by-some a (cdr x))
           (dominated-by-some a x))
  :rule-classes :forward-chaining)

;; jcd - added this
;; jcd bzo move to dominates.lisp
(defthm dominated-by-some-when-car-dominates
  (implies (dominates (car x) a)
           (equal (dominated-by-some a x)
                  (consp x))))

;; jcd - added this.  in some sense this is a replica of dominated-by-some-when
;; car-dominates, but by targetting the strip-cars directly we can apply more
;; often.
;; jcd bzo move to dominates.lisp
(defthm dominated-by-some-of-strip-cars-when-caar-dominates
  (implies (dominates (caar x) a)
           (equal (dominated-by-some a (strip-cars x))
                  (consp x))))




;; jcd - good rule?  move to diverge?
(defthm dominates-means-not-diverge
  (implies (dominates p1 p2)
           (equal (diverge p1 p2)
                  nil)))

;; jcd - good rule?  move to diverge?
(defthm dominates-means-not-diverge-alt
  (implies (dominates p2 p1)
           (equal (diverge p1 p2)
                  nil)))

;; jcd - good rule? move to diverge?
(defthm not-dominates-from-diverge-one
  (implies (diverge a b)
           (not (dominates a b))))

;; jcd - good rule? move to diverge?
(defthm not-dominates-from-diverge-two
  (implies (diverge b a)
           (not (dominates a b))))



(defthm diverges-from-all-when-diverges-from-all-of-cdr
  (implies (diverges-from-all p (cdr paths))
           (equal (diverges-from-all p paths)
                  (if (consp paths)
                      (diverge p (car paths))
                    t))))

(defthm not-dominated-by-some-when-diverges-from-all
  (implies (diverges-from-all p paths)
           (not (dominated-by-some p paths)))
  :hints (("Goal" :in-theory (enable dominated-by-some))))


;; jcd - good rule?  redundant rule?
(defthm not-dominated-by-some
  (implies (and (diverges-from-all path paths) ;path is a free variable
                (dominates p path))
           (not (dominated-by-some p paths)))
  :hints (("Goal" :in-theory (enable dominated-by-some))))


;; jcd good rule? bad rule?
(defthm not-strictly-dominated-by-some-when-diverges-from-all
  (implies (diverges-from-all p paths)
           (not (strictly-dominated-by-some p paths))))


(defthm diverges-from-all-when-no-domination-alt
  (implies (and (not (strictly-dominated-by-some p paths))
                (not (dominates-some p paths)))
           (diverges-from-all p paths)))



;make a -one version
;make analogue for diverge?
(defthm dominates-of-singleton-two
  (implies (not (consp (cdr p2)))
           (equal (dominates p1 p2)
                  (if (consp p2)
                      (or (not (consp p1))
                          (and (equal (car p1) (car p2))
                               (not (consp (cdr p1)))))
                    (not (consp p1)))))
  :hints (("Goal" :in-theory (enable dominates))))







;; jcd i think we can get rid of this
(defthmd dominates-of-cdr-and-cdr-one
  (implies (and (equal (car p1) (car p2))
                (consp p1)
                (consp p2))
           (equal (dominates (cdr p1) (cdr p2))
                  (dominates p1 p2)
                  )))

;bzo generalize the car to any memberp?
;; bzo good rule? bad rule? move to diverge.lisp?
(defthm not-all-diverge-from-all-when-not-diverges-from-all-of-car
  (implies (not (diverges-from-all (car paths1) paths2))
           (equal (all-diverge-from-all paths1 paths2)
                  (not (consp paths1)))))


;; bzo good rule? bad rule? move to diverge.lisp?
;; do we want this enabled?
(defthm all-diverge-from-all-alternate-definition
  (implies (consp paths2) ;this hyp helps prevent this rule from looping
           (equal (all-diverge-from-all paths1 paths2)
                  (and (all-diverge-from-all paths1 (cdr paths2))
                       (diverges-from-all (car paths2) paths1))))
  :hints (("Goal" :in-theory (disable acl2::equal-booleans-reducton))))
;;LIST::EQUAL-OF-BOOLEANS-REWRITE))))

;; jcd copy of diverge.lisp:all-diverge-from-all-symmetric
;; (defthm all-diverge-from-all-commutative
;;   (equal (all-diverge-from-all paths1 paths2)
;;          (all-diverge-from-all paths2 paths1))
;;   :otf-flg t
;;   :hints (("Goal" :expand ( (ALL-DIVERGE-FROM-ALL PATHS2 PATHS1))
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable all-diverge-from-all))) )

;; jcd good rule bad rule? move to diverge.lisp?
(defthm not-all-diverge-from-all-when-not-diverges-from-all-of-car-two
  (implies (not (diverges-from-all (car paths2) paths1))
           (equal (all-diverge-from-all paths1 paths2)
                  (not (consp paths2))))
  :hints (("Goal"
           :use (:instance
                 ;; jcd - unusually long name...
                 not-all-diverge-from-all-when-not-diverges-from-all-of-car
                 (paths1 paths2)
                 (paths2 paths1))
           :in-theory (disable not-all-diverge-from-all-when-not-diverges-from-all-of-car))))







;; jcd bzo - lots of the rules that follow are probably good candidates to
;; either remove or more fully integrate into diverge.lisp.


;; bzo move to bag::?
(defthm unique-memberps-of-non-consp
  (implies (not (consp x))
           (equal (bag::unique-memberps a b x)
                  nil))
 :hints (("Goal" :in-theory (enable bag::unique-memberps))))

(defthm unique-memberps-of-cons
  (equal (bag::unique-memberps a b (cons x1 x2))
         (or (and (equal a x1)
                  (list::memberp b x2))
             (and (equal b x1)
                  (list::memberp a x2))
             (and (not  (equal b x1))
                  (not  (equal a x1))
                  (bag::unique-memberps a b x2))))
  :hints (("Goal"
           :cases ((equal a b))
           :in-theory (enable bag::unique-memberps))))

;; nice rule! move to diverge.lisp
(defthm not-diverges-from-all-when-memberp
  (implies (list::memberp a x)
           (not (diverges-from-all a x)))
  :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd good rule? bad rule? subsumed rule?
(defthm diverge-when-all-diverge-from-all-and-memberp-and-memberp
  (implies (and (all-diverge-from-all x y)
                (list::memberp a x)
                (list::memberp b y))
           (diverge a b))
  :hints (("Goal" :in-theory (enable all-diverge-from-all))))

(defthm diverge-when-all-diverge-from-all-and-memberp-and-memberp-alt
  (implies (and (all-diverge-from-all x y)
                (list::memberp b x)
                (list::memberp a y))
           (diverge a b))
  :hints (("Goal" :in-theory (enable all-diverge-from-all))))

;would like this to go thru without the elim (prove a rule about unique-memberps when you know unique-memberps of cdr?
(defthm diverge-from-all-diverge-and-unique-memberps
  (implies (and (all-diverge x)
                (bag::unique-memberps a b x))
           (diverge a b))
  :hints (("Goal" :in-theory (enable all-diverge))))

;; jcd - moved to diverge.lisp:all-diverge-of-remove-1
;; (defthm all-diverge-despite-remove-1
;;   (implies (all-diverge bag::x)
;;            (all-diverge (bag::remove-1 bag::a bag::x)))
;;   :hints (("Goal" :in-theory (enable all-diverge))))

;; jcd - Strange variable names?
;; jcd - move to diverge.lisp?
(defthm all-diverge-means-not-memberp-of-remove-1-same
  (implies (all-diverge bag::x)
           (not (list::memberp bag::a (bag::remove-1 bag::a bag::x))))
  :hints(("Goal" :in-theory (enable all-diverge))))

(defthm subbagp-false-from-witness-2
  (implies (and (not (diverges-from-all a x)) ;a is a free var
                (diverges-from-all a y))
           (not (bag::subbagp x y))))

(defthm subbagp-false-from-witness-2-alt
  (implies (and (diverges-from-all a y) ;a is a free var
                (not (diverges-from-all a x)))
           (not (bag::subbagp x y))))

(defthm diverges-from-all-hack
  (implies (and (list::memberp a y)
                (all-diverge y))
           (diverges-from-all a (bag::remove-1 a y))))
;;   :hints (("Goal" :in-theory (enable diverges-from-all
;;                                      bag::remove-1
;;                                      list::memberp))))

;; jcd this seems redundant...
(defthm not-subbagp-when-blah
  (implies (and (not (all-diverge x))
                (all-diverge y))
           (not (bag::subbagp x y))))
;;   :hints (("Goal" :do-not   '(generalize eliminate-destructors)
;;            :in-theory (enable bag::subbagp all-diverge))))

;; jcd - moved to diverge.lips:all-diverge-when-subbag
;; (defthm all-diverge-when-all-diverge-and-subbagp
;;   (implies (and (all-diverge y)
;;                 (bag::subbagp x y))
;;            (all-diverge x)))






;; jcd - added this lemma, which seems to be good for doing proofs by
;; multiplicity, etc.
;; bzo move to diverge.lisp
(defthm count-of-member-when-all-diverge
  (implies (all-diverge bag)
           (equal (bag::count a bag)
                  (if (bag::memberp a bag)
                      1
                    0)))
  :hints(("Goal" :in-theory (enable all-diverge))))

;; jcd - this proof is now easy to do by membership with our count lemma
(defthm diverges-from-all-when-diverge-and-memberp-and-subbagp
  (implies (and (list::memberp a x)
                (bag::subbagp x bag)
                (all-diverge bag))
           (diverges-from-all a (bag::remove-bag x bag))))
;;   :hints (("Goal" :in-theory (enable diverges-from-all
;;                                      all-diverge
;;                                      bag::SUBBAGP
;;                                      bag::REMOVE-BAG))))


(defthm all-diverge-from-all-when-unique-subbagps-and-all-diverge
  (implies (and (all-diverge bag)
                (bag::unique-subbagps x y bag))
           (all-diverge-from-all x y)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable all-diverge-from-all
;;                               bag::subbagp-chaining
;;                               ;;bag::remove-bag
;;                               bag::unique-subbagps))))



;; jcd - moved this to diverge.lisp
;; (defthm all-diverge-from-all-of-remove-1
;;   (implies (all-diverge-from-all x y)
;;            (all-diverge-from-all x (bag::remove-1 a y)))
;;   :hints (("Goal" :in-theory (enable all-diverge-from-all))))


;; jcd - good rule?
(defthm all-diverge-from-all-from-all-diverge-from-all-etc
  (implies (and (all-diverge-from-all x2 y2)
                (bag::subbagp x x2)
                (bag::subbagp y y2))
           (all-diverge-from-all x y)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable (:induction bag::subbagp)
;;                               bag::subbagp
;;                               all-diverge-from-all))))

(defthm all-diverge-from-all-from-all-diverge-from-all-etc-alt
  (implies (and (all-diverge-from-all y2 x2)
                (bag::subbagp x x2)
                (bag::subbagp y y2))
           (all-diverge-from-all x y)))




(defthm dominates-of-append-two-one
 (implies (<= (len x) (len y))
          (equal (dominates x (append y z))
                 (dominates x y)))
 :hints (("Goal" :in-theory (enable dominates))))

;; bzo expensive?  -- probably not, since n is free?
(defthm diverge-when-firstns-diverge
  (implies (diverge (list::firstn n x)
                    (list::firstn n y))
           (diverge x y))
  :hints (("Goal" :in-theory (enable list::firstn))))

;; jcd good rule?
(defthm not-dominates-from-<-of-len-and-len
  (implies (< (len y) (len x))
           (not (dominates x y))))

(defthm not-diverges-from-all-when-memberp-nil
  (implies (list::memberp nil paths)
           (not (diverges-from-all p paths)))
  :hints (("Goal" :in-theory (enable diverges-from-all list::memberp))))

(defthm all-diverge-when-memberp-nil
  (implies (list::memberp nil paths)
           (equal (all-diverge paths)
                  (list::equiv paths (list nil))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable all-diverge
                              list::memberp
                              ))))


(defthmd diverge-append-len-equal
  (implies
   (and
    (equal (len a) (len b))
    (diverge x y))
   (diverge (append a x)
            (append b y)))
  :hints (("goal" :induct (list::len-len-induction a b))))


;; jcd - bzo we already have dominates-same-len-cheap, which is the same as the
;; following rule but has a backchain limit.  do we really want this rule?

;; jcd - I don't think so, it seems like it is slowing things down.


(defthmd dominates-when-lens-equal
  (implies (equal (len x) (len y))
           (equal (dominates x y)
                  (list::equiv x y)))
  :hints (("Goal" :in-theory (enable dominates))))

;; jcd - this is expensive and is causing problems, trying disabled.
(defthmd dominates-from-equiv-hack
  (implies (and (list::equiv x (list::firstn (len x) y))
                (<= (len x) (len y)))
           (dominates x y))
  :hints (("Goal" :do-not '(generalize eliminate-destructors preprocess)
           :in-theory (e/d (acl2::cons-equal-rewrite
                              list::fix dominates list::firstn)
                           (list::EQUAL-OF-FIXES)))))

(defthm diverge-of-firstn-hack
  (implies (and (diverge x y)
                (<= (len x) (len y)))
           (diverge x (list::firstn (len x) y)))
  :hints (("Goal"
           :cases ((< (LEN X) (LEN Y)))
           :in-theory (enable dominates-when-lens-equal
                              dominates-from-equiv-hack
                              list::firstn
                              diverge))))

;make this better?
(defthm diverge-of-append-and-append
  (implies (diverge x y)
           (diverge (append x x2)
                    (append y y2)))
  :otf-flg t
  :hints (("Goal"
           :use (:instance diverge-when-firstns-diverge
                           (n (min (len x) (len y)))
                           (x (append x x2))
                           (y (append y y2))))))



;; jcd we already have len-when-dominated and dominates-same-len-cheap...


;; bzo move to dominates.lisp?
(defthm lens-<-when-dominates-but-not-cong
  (implies (and (dominates p p2)
                (not (list::equiv p2 p)))
           (< (len p) (len p2))))


;; jcd - expensive! trying backchain limit
(defthm dominates-when-not-diverge-and-not-dominates-cheap
  (implies (and (not (dominates p2 p))
                (not (diverge p p2)))
           (dominates p p2))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))




(defun all-dominated-by-some (paths1 paths2)
  (if (endp paths1)
      t
    (and (dominated-by-some (car paths1) paths2)
         (all-dominated-by-some (cdr paths1) paths2))))

(defthm dominated-by-some-of-caar
  (implies (all-dominated-by-some (keys a32) paths)
           (equal (dominated-by-some (caar a32) paths)
                  (if (consp a32)
                      t
                    (dominated-by-some nil paths)))))

;prove a congruence?
(defthm dominated-by-some-of-list-fix
  (equal (dominated-by-some p (list::fix paths))
         (dominated-by-some p paths))
  :hints (("Goal" :in-theory (enable dominated-by-some))))

;prove a congruence?
(defthm all-dominated-by-some-of-list-fix
  (equal (all-dominated-by-some paths1 (list::fix paths))
         (all-dominated-by-some paths1 paths))
  :hints (("Goal" :in-theory (enable all-dominated-by-some))))



;; slow proof!
(defthm diverge-of-append-and-append-same-1
  (equal (diverge (append x y) (append x z))
         (diverge y z))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-of-append-from-diverge-two
  (implies (DIVERGE x z)
           (DIVERGE (APPEND x y) z))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-of-append-from-diverge-one
  (implies (DIVERGE x z)
           (DIVERGE z (APPEND x y)))
  :hints (("Goal" :in-theory (enable diverge))))











;This file contains several kinds of stuff (stuff about alists, stuff
;about copy (which uses atomic addresses, and stuff about paths).
;Maybe we should move these different things into different
;books. -Eric

(in-theory (enable g-of-s-redux)) ;add this to records?

(local (in-theory (enable list::memberp-of-cons)))
(local (in-theory (enable bag::unique-of-cons)))


;; jcd - removed this, it's a duplicate of the rule in :lists
;; ;bzo okay?
;; ;add a backchain-limit?
;; (defthm equal-of-booleans-rewrite
;;   (implies (and (booleanp x)
;;                 (booleanp y))
;;            (equal (equal x y)
;;                   (iff x y))))
;; ;; 04/13/05 CDH Duplicate of list::equal-of-booleans-rewrite, but
;; ;; without a :backchain-limit-lst.  Let's use the restricted one.
;; (in-theory (disable equal-of-booleans-rewrite))

;where should this go?
(defthm memberp-of-cadr
  (equal (list::memberp (cadr l2) l2)
         (or (and (consp l2)
                  (consp (cdr l2)))
             (list::memberp nil l2))))




;;
;; append-onto-lists (rename? append-onto-each?)
;;

;Append VAL onto each member of LISTS and return the result.
(defund append-onto-lists (val lists)
  (if (endp lists)
      nil
    (cons (append val (car lists))
          (append-onto-lists val (cdr lists)))))

;; jcd - generalized this
;; (defthm append-onto-lists-of-nil-one
;;   (equal (append-onto-lists nil lists)
;;          (list::fix lists))
;;   :hints (("Goal" :in-theory (enable append-onto-lists))))

(defthm append-onto-lists-of-non-consp-one
  (implies (not (consp val))
           (equal (append-onto-lists val lists)
                  (list::fix lists)))
  :hints(("Goal" :in-theory (enable append-onto-lists))))

;; jcd - generalized this
;; (defthm append-onto-lists-of-nil-two
;;   (equal (append-onto-lists lists nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable append-onto-lists))))

(defthm append-onto-lists-of-non-consp-two
  (implies (not (consp lists))
           (equal (append-onto-lists val lists)
                  nil))
  :hints(("Goal" :in-theory (enable append-onto-lists))))

(defthm dominated-by-some-of-append-onto-lists-self
  (equal (dominated-by-some p (append-onto-lists p keys))
         (not (all-conses keys)))
  :hints (("Goal" :in-theory (enable append-onto-lists))))

;; bzo rename
(defthm not-strictly-dominated-by-some-of-append-onto-lists
  (implies (not (dominates p2 p))
           (not (strictly-dominated-by-some p (append-onto-lists p2 blah))))
  :hints (("Goal" :in-theory (enable append-onto-lists))))

;; bzo rename
(defthm not-strictly-dominated-by-some-of-append-onto-lists-better
  (implies (not (strictly-dominates p2 p))
           (not (strictly-dominated-by-some p (append-onto-lists p2 blah))))
  :hints (("Goal" :in-theory (enable append-onto-lists))))


(defthm diverges-from-all-of-append-onto-lists
  (implies (diverge p p2)
           (diverges-from-all p (append-onto-lists p2 vals)))
  :hints (("Goal" :in-theory (enable append-onto-lists))))




;; jcd - a bunch of stuff about alists got taken out of here and pushed into
;; its own library, :alists.  a copy of the removed rules live in
;; the file old-alists.txt.



;counts how many keys genuinely map to val in alist.  should this be enabled or
;disabled?

; bzo move to alists?  develop a theory for this?
(defun num-keys-for (val alist)
  (len (pre-image val alist)))






;; bzo move to alists?  lists?  leave here?
;walks down keys and vals in lock step and returns the val corresponding to the
;first occurrence of key.  if we add a guard later, we make to deal with cdring
;off the end of vals.
(defun assoc-2 (key keys vals)
  (if (endp keys)
      nil
    (if (equal key (car keys))
        (car vals)
      (assoc-2 key (cdr keys) (cdr vals)))))


; bzo move to alists
;possible efficiency change: don't keep calling keys on alist2!
;assumes shadowed pairs have been removed
(defun compose-alists-aux (alist1 alist2)
  (if (endp alist1)
      nil
    (if (list::memberp (cdar alist1) (keys alist2))
        (cons (cons (caar alist1) (cdr (assoc (cdar alist1) alist2)))
              (compose-alists-aux (cdr alist1) alist2))
      (compose-alists-aux (cdr alist1) alist2))))

(defun compose-alists (alist1 alist2)
  (compose-alists-aux (remove-shadowed-pairs alist1)
                      (remove-shadowed-pairs alist2)))

;(compose-alists '((1 . a) (2 . b) (3 . c) (4 . d))
;                '((blah . hah) (b . bb) (d . dd)))
; '((2 . bb) (4 . dd))

(defthm not-in-keys-of-compose-alists-aux
  (implies (not (list::memberp key (keys alist)))
           (not (list::memberp key (keys (compose-alists-aux alist alist2))))))

(defthm not-in-keys-of-compose-alists
  (implies (not (list::memberp key (keys alist)))
           (not (list::memberp key (keys (compose-alists alist alist2))))))

(defthm unique-of-keys-of-compose-alists-aux
  (implies (bag::unique (keys a1))
           (bag::unique (keys (compose-alists-aux a1 a2)))))

(defthm unique-of-keys-of-compose-alists
  (bag::unique (keys (compose-alists a1 a2))))


;(compose-alists '((1 . a) (2 . b) (2 . d) (3 . c) (4 . d))
;                '((blah . hah) (b . bb) (d . dd)))
;  '((2 . bb) (4 . dd))


; bzo move to alists
;removes pairs from alist1 whose keys are also in alist2
(defun alist-diff (alist1 alist2)
  (if (endp alist1)
      nil
    (if (list::memberp (caar alist1) (keys alist2))
        (alist-diff (cdr alist1) alist2)
      (cons (car alist1) (alist-diff (cdr alist1) alist2)))))

;;
;;
;; s-list (make a g-list?)
;;
;;

;; bzo move to records?


;guard?  doesn't stop, even if we run out of values; okay?  we could stop when
;either keys or vals is empty.  whatever we choose, we should be consistent.
(defund s-list (keys vals r)
  (if (consp keys)
      (let ((k (car keys))
            (v (car vals)))
        (s k v (s-list (cdr keys) (cdr vals) r)))
    r))

(defthm s-list-when-keys-is-not-a-consp
  (implies (not (consp keys))
           (equal (s-list keys vals r)
                  r))
  :hints (("Goal" :in-theory (enable s-list))))

(defthm s-list-of-cons-and-cons
  (equal (s-list (cons k keys) vals r)
         (s k (car vals) (s-list keys (cdr vals) r)))
  :hints (("Goal" :in-theory (enable s-list))))


(defthm open-slist-when-consp-keys
  (implies (consp keys)
           (equal (s-list keys vals ram)
                  (s (car keys) (car vals) (s-list (cdr keys) (cdr vals) ram)))))

(defthm g-of-s-list-non-memberp-case
  (implies (not (list::memberp key keys))
           (equal (g key (s-list keys vals r))
                  (g key r)))
  :hints (("Goal" :in-theory (enable s-list))))

(defthm g-of-s-list-memberp-case
  (implies (list::memberp key keys)
           (equal (g key (s-list keys vals r))
                  (assoc-2 key keys vals)
                  ))
  :hints (("Goal" :in-theory (enable s-list))))

(defthm g-of-s-list-both
  (equal (g key (s-list keys vals r))
         (if (list::memberp key keys)
             (assoc-2 key keys vals)
           (g key r)))
  :hints (("Goal" :in-theory (enable s-list))))

;; ;bzo change to use nil instead of 0
;; ;do we use this?
;; (defund clr (a r)
;;   (s a 0 r))

(defthmd s-of-s-list-not-memberp-case
  (implies (not (list::memberp key keys))
           (equal (s key val (s-list keys vals r))
                  (s-list keys vals (s key val r))))
  :hints (("subgoal *1/2" :in-theory (e/d (s-list) (S-DIFF-S))
           :use ((:instance S-DIFF-S
                            (acl2::a key)
                            (acl2::x 0)
                            (acl2::b  (CAR KEYS))
                            (acl2::y (CAR VALS))
                            (acl2::r (S-LIST (CDR KEYS) (CDR VALS) R)))
                 (:instance S-DIFF-S
                            (acl2::a key)
                            (acl2::x 0)
                            (acl2::b  (CAR KEYS))
                            (acl2::y (CAR VALS))
                            (acl2::r (S-LIST (CDR KEYS) (CDR VALS) (S KEY VAL R))))))
          ("Goal" :in-theory (enable s-list))))

(defthm s-list-of-s-not-memberp-case
  (implies (not (list::memberp key keys))
           (equal (s-list keys vals (s key val r))
                  (s key val (s-list keys vals r))))
  :hints (("Goal" :use (:instance s-of-s-list-not-memberp-case))))

(defthm s-list-of-s-memberp-case
  (implies (list::memberp key keys)
           (equal (s-list keys vals (s key val r))
                  (s-list keys vals r)))
  :hints (("Goal" :in-theory (e/d (s-list
                                   s-of-s-list-not-memberp-case)
                                  (s-list-of-s-not-memberp-case)))))


(defthm s-list-of-s
  (equal (s-list keys vals (s key val r))
         (if (list::memberp key keys)
             (s-list keys vals r)
           (s key val (s-list keys vals r))))
  :hints (("Goal" :in-theory (enable))))

;;
;; G-LIST
;;

(defund g-list (list r)
  (if (consp list)
      (cons (g (car list) r)
            (g-list (cdr list) r))
    nil))

(defthm len-of-g-list
  (equal (len (g-list key-lst r))
         (len key-lst))
  :hints (("Goal" :in-theory (enable g-list))))

(defthm g-list-of-cons
  (equal (g-list (cons key keys) r)
         (cons (g key r) (g-list keys r)))
  :hints (("Goal" :in-theory (enable g-list))))

(defthm g-list-when-lst-is-not-a-consp
  (implies (not (consp lst))
           (equal (g-list lst r)
                  nil))
  :hints (("Goal" :in-theory (enable g-list))))

;bzo dup (move to utilities?)
#+joe
(DEFUN ACL2::SMALLER-TERM (ACL2::X ACL2::Y)
  (DECLARE (XARGS :MODE :PROGRAM))
  (AND (ACL2::TERM-ORDER ACL2::X ACL2::Y)
       (NOT (EQUAL ACL2::X ACL2::Y))))

(defthmd g-when-g-lists-agree
  (implies (and (equal (g-list lst st1) (g-list lst st2)) ;st2 is a free variable
                (syntaxp (acl2::smaller-term st2 st1))
                (list::memberp key lst))
           (equal (g key st1)
                  (g key st2)))
  :hints (("Goal" :in-theory (enable g-list))))

(defthm consp-of-g-list
  (equal (consp (g-list lst r))
         (consp lst))
  :hints (("Goal" :in-theory (enable g-list))))

(defthm g-list-of-fix
  (equal (g-list (list::fix lst) r)
         (g-list lst r))
  :hints (("Goal" :in-theory (enable g-list))))

(defthm g-list-of-remove-1-helper
  (implies (equal (g-list lst st1) (g-list lst st2))
           (equal (equal (g-list (bag::remove-1 val lst) st1)
                         (g-list (bag::remove-1 val lst) st2))
                  t))
  :hints (("Goal" :in-theory (enable g-list
                                     bag::remove-1))))

(local
 (defun 2-list-induct (l1 l2)
   (if (endp l1)
       (list l1 l2)
     (2-list-induct (cdr l1) (bag::remove-1 (car l1) l2)))))

(defthm g-list-when-bigger-g-lists-agree
  (implies (and (equal (g-list lst2 st1) (g-list lst2 st2)) ;lst2 and st2 are a free variables
                (syntaxp (acl2::smaller-term st2 st1))
                (bag::subbagp lst lst2)
                )
           (equal (g-list lst st1)
                  (g-list lst st2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (2-list-induct lst lst2)
           :in-theory (enable g-list
                              G-WHEN-G-LISTS-AGREE
                              bag::memberp-of-car-from-subbagp
                              ))))


;;
;;
;; copy (uses atomic addresses, not paths)
;;
;;


;bzo make a version which uses gp and sp
;this should do the first bindings last!
;Change r2 as follows:  For each pair (x . y) in ALIST, setx in R2 to the value at y in R1.
;bzo disabled copy (and the other functions defined in this book) eventually.
(defun copy (alist r1 r2)
  (if (endp alist)
      r2
    (let* ((pair (car alist))
           (d (car pair))
           (u (cdr pair)))
      (s d (g u r1) (copy (cdr alist) r1 r2)))))

(defthm copy-of-non-consp
  (implies (not (consp alist))
           (equal (copy alist r1 r2)
                  r2)))

(defthmd g-of-copy-1
  (implies (not (list::memberp a (keys alist)))
           (equal (g a (copy alist r1 r2))
                  (g a r2))))

(defthmd g-of-copy-2
  (implies (list::memberp a (keys alist))
           (equal (g a (copy alist r1 r2))
                  (g (cdr (assoc a alist)) r1))))

(defthm g-of-copy-both
  (equal (g a (copy alist r1 r2))
         (if (list::memberp a (keys alist))
             (g (cdr (assoc a alist)) r1)
           (g a r2)))
  :hints (("Goal" :in-theory (e/d (g-of-copy-2
                                   g-of-copy-1)
                                  (copy)))))

;; jcd - turned this into a congruence rule
;; (defthm copy-of-list-fix
;;   (equal (copy (list::fix alist) r1 r2)
;;          (copy alist r1 r2)))

(defthm copy-of-s-1-non-memberp-case-helper
  (implies (and (bag::unique (keys alist)) ;drop this hyp in the non-helper lemma!
                (not (list::memberp a (range alist))))
           (equal (copy alist (s a v r1) r2)
                  (copy alist r1 r2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable copy
                              bag::UNIQUE-OF-CONS
                              ))))

(defthm copy-of-clr-key
  (equal (copy (clr-key k alist) r1 r2)
         (s k (g k r2) (copy alist r1 r2))))

(defthm copy-ignores-remove-shadowed-pairs
  (equal (copy (remove-shadowed-pairs alist) r1 r2)
         (copy alist r1 r2))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable copy remove-shadowed-pairs))))

;bzo add a not memberp vals version of this?
(defthm copy-of-s-1-non-memberp-case
  (implies (not (list::memberp a (range alist)))
           (equal (copy alist (s a v r1) r2)
                  (copy alist r1 r2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable copy)
           :use (:instance copy-of-s-1-non-memberp-case-helper
                           (alist (remove-shadowed-pairs alist))))))

;; jcd - added this
(defthm assoc-2-of-non-member
  (implies (not (memberp key keys))
           (equal (assoc-2 key keys vals)
                  nil)))

(defthm copy-of-s-1-memberp-both
  (equal (copy alist (s a v r1) r2)
         (if (list::memberp a (range alist))
             (s-list (pre-image a alist)
                     (repeat (num-keys-for a alist) v)
                     (copy alist r1 r2))
           (copy alist r1 r2))))

;other case?
(defthmd s-of-copy-non-memberp-case
  (implies (not (list::memberp key (keys alist)))
           (equal (s key val (copy alist r1 r2))
                  (copy alist r1 (s key val r2)))))

(defthmd copy-of-s-2-memberp-case
  (implies (list::memberp a (keys alist)) ;say domain instead of keys?
           (equal (copy alist r1 (s a v r2))
                  (copy alist r1 r2)))
  :hints (("Goal" :in-theory (enable copy keys s-of-copy-non-memberp-case))))

(defthmd copy-of-s-2-non-memberp-case
  (implies (not (list::memberp a (keys alist))) ;say domain instead of keys?
           (equal (copy alist r1 (s a v r2))
                  (s a v (copy alist r1 r2))))
  :hints (("Goal"
           :in-theory (e/d (copy keys s-of-copy-non-memberp-case)
                           (copy-of-s-2-memberp-case)))))

(defthm copy-of-s-2-both
  (equal (copy alist r1 (s a v r2))
         (if (list::memberp a (keys alist))
             (copy alist r1 r2)
           (s a v (copy alist r1 r2))))
  :hints (("Goal" :in-theory (enable copy-of-s-2-memberp-case
                                     copy-of-s-2-non-memberp-case))))

;; jcd - Assoc is bad.  Consider for example the hyp that is
;; needed in the following theorem.  It would be better if assoc "properly
;; interpreted" its argument as an alist, and didn't behave, e.g., such that
;; (assoc nil '(3)) = 3 and so forth.  Instead, it should interpret 3 as '(nil
;; . nil) and return the pair '(nil . nil).
;;
;; (defthm assoc-iff-memberp-strip-cars
;;   (implies (alistp x)
;;            (iff (assoc a x)
;;                 (memberp a (strip-cars x)))))

;; bzo localize?
(defthm not-member-caar-of-cdr-of-strip-cars-when-unique-cars
  ;; This theorem is just not-memberp-of-car-in-cdr-when-unique where x has
  ;; been instantiated with (strip-cars x).  We prove this because, even though
  ;; we have the rule for x in general, we will never see (car (strip-cars x))
  ;; since it will just be replaced by (caar x).  Hence, the rule never gets
  ;; the chance to fire here.  Perhaps not-memberp-of-car-in-cdr-when-unique
  ;; should use a free variable instead?  Would that be too expensive?
  (implies (bag::unique (strip-cars x))
           (not (memberp (caar x)
                         (cdr (strip-cars x))))))

(defthm copy-commutativity-2
  (equal (copy a31 r1 (copy a32 r2 r3))
         (copy (alist-diff a32 a31) r2 (copy a31 r1 r3)))
  :hints (("Goal" :in-theory (enable copy))))



;; A path is a true-listp of indices that are applied recursively to a
;; hierarchical record data structure.

;; Implementation question: true list or not?
;;
;; A true list is nice in that when one goes to specify a path a . b . c one
;; does not accidentally specify nil as the final index value as in '(a b c)
;;
;; A cons list is nice in that we can rewrite (g a r) into (gp a r) rather
;; than (gp (list a) r) and the subsequent build-up/tear-down that ensues
;; in reasoning about it.  Of course, if we only use gp/sp, this wouldn't
;; be so much of an issue.
;;
;; Note that our abstract paths (see definition of gap/sap below) are
;; implemented using cons lists to differentiate between atoms and
;; sub-structures.  Additionally, it may be quite rare that we actually deal
;; with gp/sp directly once gap/sap have been defined.  It might be nice to be
;; able to re-use some of the functions that operate on raw paths when we
;; start dealing with abstract paths (?)  since many of the properties will be
;; the same ..
;;
;; Nonetheless, for now we use a true list ..




;;
;;
;; dominates
;;
;;

;; We say that path P1 dominates path P2 iff P1 is a prefix of P2.
;; Conceptually, the piece of state indicated by P1 includes the piece of state indicated by P2.





;; (defund dominates (p1 p2)
;;   (declare (type t p1 p2))
;;   (if (consp p1)
;;       (and (consp p2)
;;            (equal (car p1) (car p2))
;;            (dominates (cdr p1) (cdr p2)))
;;     t))


;; jcd - copy of dominates rule
;; (defthm dominates-of-non-consp-two
;;   (implies (not (consp p2))
;;            (equal (dominates p1 p2)
;;                   (not (consp p1))))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - copy of dominates rule
;; (defthm dominates-of-non-consp-one
;;   (implies (not (consp p1))
;;            (equal (dominates p1 p2)
;;                   t))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd bzo get rid of this
;; (defthm dominates-of-nil-two
;;   (equal (dominates p1 nil)
;;          (not (consp p1)))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd bzo get rid of this
;; (defthm dominates-of-nil-one
;;   (equal (dominates nil p2)
;;          t)
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - same as dominates-reflexive
;; (defthm dominates-self
;;   (dominates p p)
;;   :hints (("Goal" :in-theory (enable dominates))))


;; jcd - copy of dominates rule
;; (defthm dominates-of-append-self-two
;;   (dominates p (append p paths))
;;   :hints (("Goal" :in-theory (enable dominates))))


;; jcd bzo remove this, we have congruence rule now
;; (defthm dominates-of-list-fix-one
;;   (equal (dominates (list::fix p1) p2)
;;          (dominates p1 p2))
;;   :hints (("Goal" :in-theory (enable dominates ))))

;; jcd bzo remove this, we have congruence rule now
;; (defthm dominates-of-list-fix-two
;;   (equal (dominates p1 (list::fix p2))
;;          (dominates p1 p2))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - copy of dominates rule
;; (defthm dominates-of-append-self-one
;;   (equal (dominates (append p paths) p)
;;          (not (consp paths)))
;;   :hints (("Goal" :in-theory (enable dominates
;;                                      (:induction binary-append)
;;                                      ))))

;; jcd - good rule?  move to dominates?
;; I think i decided this was a bad rule, trying removing it...

;; (defthm dominates-of-cons-and-cons
;;   (equal (dominates (cons a p1) (cons b p2))
;;          (and (equal a b)
;;               (dominates p1 p2)))
;;   :hints (("Goal" :in-theory (enable dominates))))


;; jcd - copy of dominates rule
;; (defthm dominates-transitive-one
;;   (implies (and (dominates p1 p2) ;p2 ia a free var
;;                 (dominates p2 p3))
;;            (dominates p1 p3))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - copy of dominates rule
;; (defthm dominates-transitive-two
;;   (implies (and (dominates p2 p3) ;p2 ia a free var
;;                 (dominates p1 p2))
;;            (dominates p1 p3))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removing, see dominates.lisp:dominates-weakly-asymmetric

;; jcd - copy of dominates rule APPEND-NTHCDR-IDENTITY-WHEN-DOMINATES
;; (defthm dominates-tells-you-append-of-nthcdr-of-len-does-nothing
;;   (implies (dominates p2 p1)
;;            (equal (append p2 (nthcdr (len p2) p1))
;;                   p1))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable dominates append nthcdr))))

;; jcd - copy of dominates rule len-when-dominated
;; (defthm dominates-means-len-<=
;;   (implies (dominates p1 p2)
;;            (<= (len p1) (len p2)))
;;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - copy of dominates rule nthcdr-len-when-dominates
;; (defthm nthcdr-when-dominates
;;   (implies (dominates p1 p2)
;;            (equal (nthcdr (len p2) p1)
;;                   (if (list::equiv p1 p2)
;;                       (list::finalcdr p1)
;;                     nil)))
;;   :hints (("Goal" :in-theory (enable nthcdr dominates)))
;;   :otf-flg t)

; jcd - copy of dominates rule
;; (defthm dominates-from-dominates-of-nthcdr-etc
;;   (implies (and (dominates (nthcdr (len big) p2)
;;                            (nthcdr (len big) p))
;;                 (dominates big p2)
;;                 (dominates big p))
;;            (dominates p2 p))
;;   :hints (("Goal" :in-theory (enable dominates nthcdr))))

;; jcd - copy of dominates rule
;; (defthm dominates-of-nthcdr-and-nthcdr-from-dominates
;;   (implies (dominates p1 p2)
;;            (dominates (nthcdr n p1) (nthcdr n p2)))
;;   :hints (("Goal" :in-theory (enable nthcdr dominates))))

;; jcd - copy of dominates:linear-domination-hierarchy
;; (defthm two-dominators-hack
;;   (implies (and (dominates a p) ; p is a free var
;;                 (dominates b p)
;;                 (not (dominates a b)))
;;            (dominates b a))
;;   :hints (("Goal" :in-theory (enable dominates))))

;;
;;
;; strictly-dominates
;;
;;

; A path P1 strictly dominates a path P2 iff P1 is a proper prefix of P2 (that is, if P1 dominates P2 but is not equal to P2).
;This function could just call dominates and compare the length (would eliminate mention of list::equiv)...
;; (defun strictly-dominates (p1 p2)
;;   (declare (type t p1 p2))
;;   (and (dominates p1 p2)
;;        (not (list::equiv p1 p2))))


;;
;;
;; contains-a-non-consp
;;
;;

;; bzo get rid of this, see dominates.lisp:all-conses
;; (defun contains-a-non-consp (list)
;;   (declare (type t list))
;;   (if (consp list)
;;       (if (not (consp (car list)))
;;           t
;;         (contains-a-non-consp (cdr list)))
;;     nil))

;;
;;
;; dominated-by-some
;;
;;

;; P is dominated by some element of PATHS.
;; (defund dominated-by-some (p paths)
;;   (declare (type t p paths))
;;   (if (consp paths)
;;       (if (dominates (car paths) p)
;;           t
;;         (dominated-by-some P (cdr paths)))
;;     nil))

;; jcd - copy of dominates rule
;; (defthm dominated-by-some-of-non-consp-one
;;   (implies (not (consp p))
;;            (equal (dominated-by-some p paths)
;;                   (contains-a-non-consp paths)))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; jcd - copy of dominates rule
;; (defthm dominated-by-some-of-non-consp-two
;;   (implies (not (consp paths))
;;            (equal (dominated-by-some p paths)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; jcd - bzo remove this
;; (defthm dominated-by-some-of-nil-one
;;   (equal (dominated-by-some nil paths)
;;          (contains-a-non-consp paths)))

;; jcd - bzo remove this
;; (defthm dominated-by-some-of-nil-two
;;   (equal (dominated-by-some paths nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; jcd - copy of NOT-DOMINATED-BY-SOME-FROM-WEAKER
;; (defthm not-dominated-by-some-lemma
;;   (implies (and (not (dominated-by-some p paths))
;;                 (dominates p2 p))
;;            (not (dominated-by-some p2 paths)))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; jcd - copy of rule in dominates.lisp
;; (defthm dominated-by-some-of-cons
;;   (equal (dominated-by-some p1 (cons p2 paths))
;;          (or (dominates p2 p1)
;;              (dominated-by-some p1 paths)))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))




;;
;;
;; strictly-dominated-by-some
;;
;;

;; (defun strictly-dominated-by-some (p paths)
;;   (declare (type t p paths))
;;   (if (consp paths)
;;       (if (strictly-dominates (car paths) p)
;;         t
;;       (strictly-dominated-by-some p (cdr paths)))
;;     nil))

;; bzo enabling since it was enabled
;; (in-theory (enable strictly-dominated-by-some))

;; jcd - copy of theorem already in dominates.lisp
;; (defthm strictly-dominated-by-some-of-append
;;   (equal (strictly-dominated-by-some p (append x y))
;;          (or (strictly-dominated-by-some p x)
;;              (strictly-dominated-by-some p y))))



;;
;;
;; dominates-some
;;
;;

;; (defun dominates-some (p paths)
;;   (if (endp paths)
;;       nil
;;     (if (dominates p (car paths))
;;         t
;;       (dominates-some p (cdr paths)))))

;; bzo enabling since it was previously enabled
;; (in-theory (enable dominates-some))

;; jcd - copy of existing rule in dominates.lisp
;; (defthm dominates-some-of-append
;;   (equal (dominates-some p (append x y))
;;          (or (dominates-some p x)
;;              (dominates-some p y))))



;;
;;
;; diverge
;;
;;



;; bzo Need backchain limit on this.



;We could write this recursively...
;Conceptually, P1 and P2 diverge iff they indicate non-ovelapping pieces of state.
;Paths are lists of indices, and if P1 and P2 diverge, there must some position in which theis indices disagree.
;; (defund diverge (p1 p2)
;;   (declare (type t p1 p2))
;;   (and (not (dominates p1 p2))
;;        (not (dominates p2 p1))))

;Given two paths, P1 and P2, either P1 dominates P2, or P2 dominates P1, or P1 and P2 diverge.

;; jcd - copy of diverge.lisp:not-diverge-forward-to-dominates-cases
;; (defthm not-diverge-cases
;;   (implies (not (diverge x y))
;;            (or (dominates x y)
;;                (dominates y x)))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp
;; (defthm two-dominators-cannot-diverge
;;   (implies (and (dominates p1 p) ;p is a free var
;;                 (dominates p2 p))
;;            (not (diverge p1 p2)))
;;   :hints (("Goal" :in-theory (enable diverge dominates))))

;; jcd - moved to diverge.lisp
;; (defthm diverge-of-non-consp-one
;;   (implies (not (consp p1))
;;            (equal (diverge p1 p2)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp
;; (defthm diverge-of-non-consp-two
;;   (implies (not (consp p2))
;;            (equal (diverge p1 p2)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp:diverge-symmetric
;; (defthm diverge-commutative
;;   (equal (diverge p1 p2)
;;          (diverge p2 p1))
;;    :rule-classes ((:rewrite :loop-stopper ((p1 p2))))
;;    :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp:diverge-irreflexive
;; (defthm not-diverge-self
;;   (not (diverge p p))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp
;; (defthm diverge-of-append-self-two
;;   (equal (diverge p (append p paths))
;;          nil)
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - moved to diverge.lisp
;; (defthm diverge-of-append-self-one
;;   (equal (diverge (append p paths) p)
;;          nil)
;;   :hints (("Goal" :in-theory (enable diverge))))


;; jcd -  move to diverge?
;; jcd bzo remove this
;; (defthm diverge-of-cons-and-cons
;;   (equal (diverge (cons a p1) (cons b p2))
;;          (or (not (equal a b))
;;              (diverge p1 p2)))
;;   :hints (("Goal" :in-theory (enable diverge))))


;; jcd - moved to diverge.lisp (-one)
;; (defthm diverge-when-diverge-with-dominator
;;   (implies (and (diverge x z) ;z is a free var
;;                 (dominates z y))
;;            (diverge x y)))

;; jcd - moved to diverge.lisp (-one)
;; (defthm diverge-when-diverge-with-dominator-alt
;;   (implies (and (dominates z y) ;z is a free var
;;                 (diverge x z))
;;            (diverge x y))
;;   :hints (("Goal" :in-theory (enable diverge dominates))))



;; bzo try to remove this
;; (defthm divereg-when-dominate-divergent
;;   (implies (and (dominates q p)   ;q is a free var
;;                 (dominates q2 p2) ;q2 is a free var
;;                 (diverge q q2))
;;            (diverge p p2))
;;   :hints (("Goal" :in-theory (enable diverge))))

;;
;;
;; diverges-from-all
;;
;;

;Checks whether PATH diverges from each member of PATHS.
;; (defund diverges-from-all (path paths)
;;   (declare (type t path paths))
;;   (if (consp paths)
;;       (and (diverge path (car paths))
;;            (diverges-from-all path (cdr paths)))
;;     t))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-of-cons
;;   (equal (diverges-from-all p (cons p2 paths))
;;          (and (diverge p p2)
;;               (diverges-from-all p paths)))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-of-non-consp-one
;;   (implies (not (consp p))
;;            (equal (diverges-from-all p paths)
;;                   (not (consp paths))))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-of-non-consp-two
;;   (implies (not (consp paths))
;;            (diverges-from-all p paths))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-of-append
;;   (equal (diverges-from-all p (append paths1 paths2))
;;          (and (diverges-from-all p paths1) (diverges-from-all p paths2)))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-of-remove-1
;;   (implies (diverges-from-all p paths)
;;            (diverges-from-all p (bag::remove-1 a paths)))
;;   :hints (("Goal" :in-theory (enable bag::remove-1-of-cons-both
;;                                      diverges-from-all))))

;; jcd removing this
;; (defthm diverges-from-all-of-nil
;;   (equal (diverges-from-all nil paths)
;;          (not (consp paths)))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverge-when-memberp-and-diverges-from-all-one
;;   (implies (and (list::memberp p2 paths) ;paths is a free var
;;                 (diverges-from-all p1 paths)
;;                 )
;;            (diverge p1 p2))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverge-from-memberp-and-diverges-from-all-two
;;   (implies (and (diverges-from-all p1 paths) ;paths is a free var
;;                 (list::memberp p2 paths)
;;                 )
;;            (diverge p1 p2))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverge-from-memberp-and-diverges-from-all-three
;;   (implies (and (list::memberp p1 paths)  ;paths is a free var
;;                 (diverges-from-all p2 paths)
;;                 )
;;            (diverge p1 p2))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverge-from-memberp-and-diverges-from-all-four
;;   (implies (and (diverges-from-all p2 paths) ;paths is a free var
;;                 (list::memberp p1 paths)
;;                 )
;;            (diverge p1 p2))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-when-diverges-from-all-and-subbagp
;;   (implies (and (diverges-from-all p paths2) ;paths2 is a free var
;;                 (bag::subbagp paths paths2))
;;            (diverges-from-all p paths))
;;   :hints (("Goal" :in-theory (enable diverges-from-all
;;                                      bag::subbagp))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-when-diverges-from-all-and-subbagp-alt
;;   (implies (and (bag::subbagp paths paths2) ;paths2 is a free var
;;                 (diverges-from-all p paths2))
;;            (diverges-from-all p paths))
;;   :hints (("Goal" :in-theory (enable diverges-from-all
;;                                      bag::subbagp))))



;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-when-dominated
;;   (implies (and (dominates p p2) ;p is a free var
;;                 (diverges-from-all p paths)
;;                 )
;;            (diverges-from-all p2 paths)
;;            )
;;   :hints (("Goal" :in-theory (enable diverges-from-all dominates))))

;; jcd moved to diverge.lisp
;; (defthm diverges-from-all-when-no-domination
;;   (implies (and (not (dominated-by-some p paths))
;;                 (not (dominates-some p paths)))
;;            (diverges-from-all p paths)))




;;
;;
;; all-diverge-from-all
;;
;;

;tests whether every path in PATHS1 diverges from every path in PATHS2.
;; (defund all-diverge-from-all (paths1 paths2)
;;   (declare (type t paths1 paths2))
;;   (if (consp paths1)
;;       (and (diverges-from-all (car paths1) paths2)
;;            (all-diverge-from-all (cdr paths1) paths2))
;;     t))

;; jcd moved to diverge.lisp
;; (defthm all-diverge-from-all-of-non-consp-one
;;   (implies (not (consp paths1))
;;            (all-diverge-from-all paths1 paths2))
;;   :hints (("Goal" :in-theory (enable all-diverge-from-all))))

;; jcd moved to diverge.lisp
;; (defthm all-diverge-from-all-of-non-consp-two
;;   (implies (not (consp paths2))
;;            (all-diverge-from-all paths1 paths2))
;;   :hints (("Goal" :in-theory (enable all-diverge-from-all))))

;; jcd moved to diverge.lisp
;; (defthm all-diverge-from-all-of-cons-two
;;   (equal (all-diverge-from-all paths1 (cons p paths2))
;;          (and (diverges-from-all p paths1)
;;               (all-diverge-from-all paths1 paths2)))
;;   :hints (("Goal" :in-theory (enable))))




;;
;;
;; all-diverge
;;
;;

;Tests whether every path in PATHS diverges from all other paths in PATHS.
;; (defund all-diverge (paths)
;;   (declare (type t paths))
;;   (if (consp paths)
;;       (and (diverges-from-all (car paths) (cdr paths))
;;            (all-diverge (cdr paths)))
;;     t))

;; jcd moved to diverge.lisp
;; (defthm all-diverge-of-cons
;;   (equal (all-diverge (cons p paths))
;;          (and (diverges-from-all p paths)
;;               (all-diverge paths)))
;;   :hints (("Goal" :in-theory (enable all-diverge))))

;; (defthm all-diverge-of-remove-1
;;   (implies (all-diverge paths2)
;;            (all-diverge (bag::remove-1 p paths2)))
;;   :hints (("Goal" :in-theory (e/d (bag::remove-1 all-diverge)
;;                                   ((:induction all-diverge)
;;                                    bag::cons-car-onto-remove-1-of-cdr)))))

;; jcd possibly remove this
;; (defthm divergence-implies-unequal-extensions
;;   (implies (all-diverge `(,x ,y))
;;            (not (equal (append x a) (append y b))))
;;   :hints (("Goal"
;;            :in-theory (enable all-diverge
;;                               diverge
;;                               dominates))))








;;
;;
;; remove-pairs-dominated-by
;;
;;


;Removes all pairs in alist whose keys are dominated by p
;Should this do alist::alistfixing? It seems okay without it.
(defun remove-pairs-dominated-by (p alist)
  (if (endp alist)
      nil
    (if (dominates p (caar alist))
        (remove-pairs-dominated-by p (cdr alist))
      (cons (car alist) (remove-pairs-dominated-by p (cdr alist))))))

(defthm remove-pairs-dominated-by-of-append
  (equal (remove-pairs-dominated-by p (append x y))
         (append (remove-pairs-dominated-by p x)
                 (remove-pairs-dominated-by p y))))

(defthm remove-pairs-dominated-by-of-remove-pairs-dominated-by-one
  (implies (dominates p1 p2)
           (equal (remove-pairs-dominated-by p1 (remove-pairs-dominated-by p2 alist))
                  (remove-pairs-dominated-by p1 alist))))

(defthm remove-pairs-dominated-by-of-remove-pairs-dominated-by-two
  (implies (dominates p2 p1)
           (equal (remove-pairs-dominated-by p1 (remove-pairs-dominated-by p2 alist))
                  (remove-pairs-dominated-by p2 alist))))

(defthm remove-pairs-dominated-by-of-remove-pairs-dominated-by-three
  (implies (diverge p2 p1)
           (equal (remove-pairs-dominated-by p1 (remove-pairs-dominated-by p2 alist))
                  (remove-pairs-dominated-by p2 (remove-pairs-dominated-by p1 alist))))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))

(defthm remove-pairs-dominated-by-of-remove-pairs-dominated-by
  (equal (remove-pairs-dominated-by p1 (remove-pairs-dominated-by p2 alist))
         (if (dominates p1 p2)
             (remove-pairs-dominated-by p1 alist)
           (if (dominates p2 p1)
               (remove-pairs-dominated-by p2 alist)
             (remove-pairs-dominated-by p2 (remove-pairs-dominated-by p1 alist)))))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))


;dup?
(defthm diverges-from-all-of-keys-of-remove-pairs-dominated-by
  (implies (diverges-from-all p (keys alist))
           (diverges-from-all p (keys (remove-pairs-dominated-by p2 alist)))))


;;
;;
;; remove-shadowed-pairs2
;;
;;

;remove pairs whose key is dominated by an earlier key

(defun remove-shadowed-pairs2 (alist)
  (if (endp alist)
      nil
    (cons (car alist)
          (remove-shadowed-pairs2
           (remove-pairs-dominated-by (caar alist) (cdr alist))))))

(defthm remove-shadowed-pairs2-of-cons
  (equal (remove-shadowed-pairs2 (cons pair alist))
         (cons pair (remove-shadowed-pairs2
                     (remove-pairs-dominated-by (car pair) alist)))))

(defthm remove-shadowed-pairs2-of-remove-pairs-dominated-by
  (equal (remove-shadowed-pairs2 (remove-pairs-dominated-by p alist))
         (remove-pairs-dominated-by p (remove-shadowed-pairs2 alist))))

(defthm remove-shadowed-pairs2-idempotent
  (equal (remove-shadowed-pairs2 (remove-shadowed-pairs2 alist))
         (remove-shadowed-pairs2 alist)))

(defthm subbagp-of-keys-of-remove-pairs-dominated-by
  (bag::subbagp (keys (remove-pairs-dominated-by p alist))
                (keys alist)))


;bzo perhaps all the alist stuff could go after gp and sp?

;; A "path alist" is an alist whose keys and values are true-listps.
;; Does this really need to fix the vals too?
(defun path-alist-fix (alist)
  (declare (type t alist))
  (if (consp alist)
      (if (consp (car alist))
          (cons (cons (list::fix (caar alist))
                      (list::fix (cdar alist)))
                (path-alist-fix (cdr alist)))
        (cons (cons nil nil) (path-alist-fix (cdr alist))))
    nil))





;;
;;
;; gp
;;
;;

;get the value in R at path P.
(defund gp (path r)
  (declare (type t path r))
  (if (consp path)
      (gp (cdr path) (g (car path) r))
    r))


(defthmd open-gp
  (implies
   (consp path)
   (equal (gp path r)
          (gp (cdr path) (g (car path) r))))
  :hints (("goal" :in-theory (enable gp))))

(defthm gp-of-non-consp
  (implies (not (consp p))
           (equal (gp p r) r))
  :hints (("Goal" :in-theory (enable gp))))

;; jcd - i tried to remove this, thinking it was redundant with the above.
;; but, some proofs broke because of it.  this "adds something" to the strategy
;; merely because it is a "simple" or "abbreviation" rule and so it gets a
;; chance to fire in more contexts.
(defthm gp-of-nil
  (equal (gp nil r)
         r))

(defthmd g-to-gp
  (equal (g a r)
         (gp (list a) r))
  :hints (("goal" :in-theory (enable open-gp))))

(defthmd gp-of-gp
  (equal (gp p1 (gp p2 r))
         (gp (append p2 p1) r))
  :hints (("Goal" :in-theory (enable gp))))

(defthm gp-of-append
  (equal (gp (append p2 p1) r)
         (gp p1 (gp p2 r)))
  :hints (("Goal" :in-theory (enable gp))))

;;
;;
;; sp
;;
;;

;set the value in R at path P to V.
(defund sp (path v r)
  (declare (type t path v r))
  (if (consp path)
      (s (car path)
         (sp (cdr path) v (g (car path) r))
         r)
    v))

(defthm sp-of-nil-and-nil
  (equal (sp p nil nil)
         nil)
  :hints (("Goal" :in-theory (enable sp))))


(defthmd open-sp
  (implies
   (consp path)
   (equal (sp path v r)
          (s (car path) (sp (cdr path) v (g (car path) r)) r)))
  :hints (("goal" :in-theory (enable sp))))

(defthm sp-of-non-consp
  (implies (not (consp p))
           (equal (sp p val r2)
                  val))
  :hints (("Goal" :in-theory (enable sp))))

(defthmd s-to-sp
  (equal (s a v r)
         (sp `(,a) v r))
  :hints (("goal" :in-theory (enable open-sp))))

(defthm g-of-sp-one
  (implies (and (equal k (car p))
                (consp p))
           (equal (g k (sp p val r))
                  (sp (cdr p) val (g k r))))
  :hints (("Goal" :in-theory (enable sp))))

(defthm g-of-sp-two
  (implies (and (not (equal k (car p)))
                (consp p))
           (equal (g k (sp p val r))
                  (g k r)))
  :hints (("Goal" :in-theory (enable sp))))

(defthm g-of-sp
  (equal (g k (sp p val r))
         (if (consp p)
             (if (equal k (car p))
                 (sp (cdr p) val (g k r))
               (g k r))
           (g k val))))

(defthm gp-of-s-diff
  (implies (not (equal k (car p)))
           (equal (gp p (s k val r))
                  (if (consp p)
                      (gp p r)
                    (s k val r))))
           :hints (("Goal" :in-theory (enable gp))))

(defthm sp-of-s-diff
  (implies (not (equal k (car p)))
           (equal (sp p v (s k val r))
                  (if (consp p)
                      (s k val (sp p v r))
                    v)))
  :hints (("Goal" :in-theory (enable sp))))

(defthm sp-of-s-same
  (implies (equal k (car p))
           (equal (sp p v (s k val r))
                  (if (consp p)
                      (s k (sp (cdr p) v val) r)
                    v)))
  :hints (("Goal" :in-theory (enable sp))))

(defthm gp-of-s-same
  (implies (equal k (car p))
           (equal (gp p (s k val r))
                  (if (consp p)
                      (gp (cdr p) val)
                    (s k val r))))
  :hints (("Goal" :in-theory (enable gp))))

;; ;generalize?
;; (defthm gp-of-s-car
;;   (equal (GP P (S (CAR P) v R))
;;          (if (consp p)
;;              (gp (cdr p) v)
;;            (S (CAR P) v R)))
;;   :hints (("Goal" :in-theory (enable gp))))

(defthm gp-of-s
  (equal (gp p (s k val r))
         (if (consp p)
             (if (equal k (car p))
                 (gp (cdr p) val)
               (GP P R))
           (s k val r)))
  :hints (("Goal" :in-theory (enable gp))))

(defthm sp-of-s
  (equal (sp p v (s k val r))
         (if (consp p)
             (if (equal k (car p))
                 (s k (sp (cdr p) v val) r)
               (s k val (sp p v r)))
           v)))

(defthm sp-equal-rewrite
  (implies (syntaxp (not (equal v ''nil)))
           (equal (equal (sp path v r) r2)
                  (and (equal v (gp path r2))
                       (equal (sp path nil r)
                              (sp path nil r2)))))
  :hints (("Goal" :in-theory (enable gp sp))))

(defthm s-of-sp-same
  (implies (equal k (car p))
           (equal (s k v1 (sp p v2 r))
                  (if (consp p)
                      (s k v1 r)
                    (s nil v1 v2))))
  :hints (("Goal" :in-theory (enable sp))))


;; jcd trying to remove this, use list::len-len-induction instead
;;
;; (defun 2-cdrs-induct (x y)
;;   (if (or (endp x) (endp y))
;;       (cons x y)
;;     (2-cdrs-induct (cdr x) (cdr y))))

;; bzo rename this to something about paths, make it local, do something?
(defun 2-cdrs-induct-and-more (x y r)
  (if (or (endp x)
          (endp y))
      (list x y r)
    (2-cdrs-induct-and-more (cdr x) (cdr y) (G (CAR x) R))))

(defthm sp-of-sp-dominating-case-one
  (implies (dominates p1 p2)
           (equal (sp p1 v1 (sp p2 v2 r))
                  (sp p1 v1 r)))
  :hints (("Goal" :in-theory (enable sp)
           :induct (2-cdrs-induct-and-more p1 p2 r))))

(defthm gp-of-sp-diverge-case
  (implies (diverge p1 p2)
           (equal (gp p1 (sp p2 v r))
                  (gp p1 r)))
  :hints (("Goal"
           :in-theory (enable dominates
                              diverge
                              gp))))



;remove all mentions of subpath

(defthm gp-of-sp-subpath-case-one
  (implies (dominates p2 p1)
           (equal (gp p1 (sp p2 v r))
                  (gp (nthcdr (len p2) p1) v)))
  :hints (("Goal" :in-theory (enable dominates
                                     sp))))


;this isn't as nice as case1 because r appears in the RHS, as does a call to sp.
(defthm gp-of-sp-subpath-case-two
  (implies (dominates p1 p2)
           (equal (gp p1 (sp p2 v r))
                  (sp (nthcdr (len p1) p2) v (gp p1 r))))
  :hints (("Goal" :in-theory (enable dominates
                                     gp))))

;handles all the cases.
(defthm gp-of-sp
  (equal (gp p1 (sp p2 v r))
         (if (diverge p1 p2)
             (gp p1 r)
           (if (dominates p2 p1)
                (gp (nthcdr (len p2) p1) v)
             (sp (nthcdr (len p1) p2) v (gp p1 r))))))


;;
;; Here are some rules to "normalize" the following expression:
;;
;; (sp '(:a) (sp '(:b) 0 (sp '(:C) 1 (gp :a r))) r)


;sp-sp-composition
;sort of an sp-associative rule
(defthm sp-of-sp-one
  (equal (sp p1 (sp p2 v r2) r1)
         (sp (append p1 p2) v (sp p1 r2 r1)))
  :hints (("Goal" :in-theory (enable sp))))

(defthm sp-of-gp-reduction
  (equal (sp p1 (gp p1 r) r)
         r)
  :hints (("Goal" :in-theory (enable gp sp))))

;a more general version of sp-of-gp-reduction
;consider disabling?
(defthm sp-does-nothing
  (implies (equal v (gp p1 r))
           (equal (sp p1 v r)
                  r))
  :hints (("Goal" :in-theory (enable gp sp))))

(defthm sp-does-nothing-rewrite
  (equal (equal r (sp p v r))
         (equal v (gp p r))))

;; (sp '(:a) (sp '(:b) 0 (sp '(:c) 1 (gp '(:a) r))) r) =
;; (sp '(:a :b) 0 (sp '(:a) (sp '(:c) 1 (gp '(:a) r)))) =
;; (sp '(:a :b) 0 (sp '(:a :c) 1 (sp '(:a) (gp '(:a) r) r))) =
;; (sp '(:a :b) 0 (sp '(:a :c) 1 r))

(defthm sp-of-sp-diverge
  (implies (diverge p1 p2)
           (equal (sp p1 v1 (sp p2 v2 r))
                  (sp p2 v2 (sp p1 v1 r))))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2))))
  :hints (("Goal"
           :induct (2-cdrs-induct-and-more p1 p2 r)
           :in-theory (enable sp))))

(defthm sp-of-sp-dominating-case-two
  (implies (dominates p2 p1)
           (equal (sp p1 v1 (sp p2 v2 r))
                  (sp p2 (sp (nthcdr (len p2) p1) v1 v2) r)))
  :hints (("Goal" :in-theory (enable sp))))

;bzo maybe this is the wrong thing to disable?
(in-theory (disable sp-of-sp-one))

(defthm sp-of-sp
  (equal (sp p1 v1 (sp p2 v2 r))
         (if (dominates p1 p2)
             (sp p1 v1 r)
           (if (diverge p1 p2)
               (sp p2 v2 (sp p1 v1 r))
             (sp p2 (sp (nthcdr (len p2) p1) v1 v2) r))))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))

;rename?
(defthm clear-small-equality-implies-clear-big-equality
  (implies (and (equal (sp small v r1)
                       (sp small v r2))
                (dominates big small))
           (equal (equal (sp big v r1) (sp big v r2))
                  t))
  :hints (("Goal" :in-theory (enable dominates
                                     sp))))




;; ;;
;; ;; nthcdr-from-keys (remove this?)
;; ;;

;; (defund nthcdr-from-keys (n alist)
;;   (if (endp alist)
;;       nil
;;     (cons (cons (nthcdr n (caar alist)) (cdar alist))
;;           (nthcdr-from-keys n (cdr alist)))))

;; (defthm nthcdr-from-keys-of-0
;;   (equal (nthcdr-from-keys 0 alist)
;;          (alist::alistfix alist))
;;   :hints (("Goal" :in-theory (enable nthcdr-from-keys))))

;; (defthm nthcdr-from-keys-of-non-consp
;;   (implies (not (consp alist))
;;            (equal (nthcdr-from-keys n alist)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable nthcdr-from-keys))))




;;
;; cons-onto-keys
;;


;; bzo develop a theory about me and disable me
;; bzo move me to alists
(defun cons-onto-keys (val alist)
  (if (endp alist)
      nil
    (cons (cons (cons val (caar alist)) (cdar alist))
          (cons-onto-keys val (cdr alist)))))

;; jcd - added this
(defcong alist::alist-equiv equal (cons-onto-keys val alist) 2
  :hints(("Goal" :induct (list::len-len-induction alist alist::alist-equiv))))

;; jcd - added this
(defthm alistp-of-cons-onto-keys
  (alistp (cons-onto-keys val alist)))

;; jcd - added this
(defthm vals-of-cons-onto-keys
  (equal (vals (cons-onto-keys val alist))
         (vals alist)))

;; jcd - add something like, keys of cons-onto-keys is map-cons of keys...





;;
;; append-onto-keys
;;

;; bzo try to disable me eventually
;; bzo move me to alists
(defun append-onto-keys (val alist)
  (if (endp alist)
      nil
    (cons (cons (append val (caar alist)) (cdar alist))
          (append-onto-keys val (cdr alist)))))

;; jcd - added this
(defthm alistp-of-append-onto-keys
  (alistp (append-onto-keys val alist)))

;; jcd - generalized this
;; (defthm append-onto-keys-of-nil
;;   (equal (append-onto-keys nil alist)
;;          (alist::alistfix alist)))

(defthm append-onto-keys-of-non-consp
  (implies (not (consp val))
           (equal (append-onto-keys val alist)
                  (alist::alistfix alist))))

(defthm vals-of-append-onto-keys
  (equal (vals (append-onto-keys p alist))
         (vals alist)))

(defthm keys-of-append-onto-keys
  (equal (keys (append-onto-keys path alist))
         (append-onto-lists path (keys alist)))
  :hints (("Goal" :in-theory (enable append-onto-lists))))

(defthm remove-pairs-dominated-by-of-append-onto-keys-same
  (equal (remove-pairs-dominated-by p (append-onto-keys p alist))
         nil))

(defthm remove-pairs-dominated-by-of-append-onto-keys-dominates
  (implies (dominates p p2)
           (equal (remove-pairs-dominated-by p (append-onto-keys p2 alist))
                  nil)))


;;
;;
;; mp (was called my-copy)
;;
;;

;bzo rename
;could write this in terms of gp-list and sp-list?
;For each pair (R . S) in ALIST, change spot R in R2 to have the value at spot S in R1.
(defun mp (alist r1 r2)
  (declare (type (satisfies alistp) alist))
  (if (endp alist)
      r2
    (let* ((pair (car alist))
           (d (car pair))
           (u (cdr pair)))
      (sp d (gp u r1) (mp
                       ;(remove-pairs-dominated-by (car alist) (cdr alist)) ;
                       (cdr alist)
                       r1
                       r2)))))

(defun cp (list r1 r2)
  (declare (type t list))
  (if (consp list)
      (sp (car list) (gp (car list) r1)
          (cp (cdr list) r1 r2))
    r2))

(defthm mp-of-non-consp
  (implies (not (consp alist))
           (equal (mp alist r1 r2)
                  r2)))

;could also say diverges from all non-dominated keys?

(defthmd gp-of-mp-diverges-from-all-case
  (implies (diverges-from-all p (keys alist))
           (equal (gp p (mp alist r1 r2))
                  (gp p r2))))

(defthm mp-of-g
  (equal (mp alist r1 (g k r2))
         (g k (mp (cons-onto-keys k alist) r1 r2))))

;might loop?
(defthm mp-of-gp
  (equal (mp alist r1 (gp p r2))
         (gp p (mp (append-onto-keys p alist) r1 r2))))

(defthm sp-of-mp-of-remove-pairs-dominated-by
  (implies (dominates p1 p2)
           (equal (sp p1 val (mp (remove-pairs-dominated-by p2 alist) r1 r2))
                  (sp p1 val (mp alist r1 r2))))

  :hints (("subgoal *1/2" :cases ((dominates (caar alist) p1)
                                  (dominates p1 (caar alist))))))

(defthm mp-of-remove-shadowed-pairs2
  (equal (mp (remove-shadowed-pairs2 alist) r1 r2)
         (mp alist r1 r2))
  :hints (("Goal" :induct (mp alist r1 r2))))



;; ;if x diverges from y, and y dominates z, then x diverges from z?

;; p can diverge from all keys - done - generalize to diverges from all non-dominated keys?
;; ;aha!  now domain and keys are more different

;; a (non-shadowed) path subsumes p - forget r2.  now we're copying values into r1?

;; say we set these bits of r2
;; 1234
;; 123
;; 12

;; to get 1, we must read 1 from r2 and then copy in some vals from r1
;; to get 123, say, we just get from r1 whatever 123 was set to and the copy in some vals from r1

;; For any two paths, p1 and p2, at least one of the follwowing is true:
;;   (diverge p1 p2)
;;   (dominates p1 p2)
;;   (dominates p2 p1)

;; Let's handle the case where p is dominated by some key in alist:




;; ...


;; (defthm cdr-of-assoc-of-caar
;;   (equal (cdr (assoc (caar alist) alist))
;;          (if (consp alist)
;;              (cdar alist)
;;            nil)))



;result is only valid when there is a dominator.

;; jcd - changed this to return nil on the empty case, makes
;; first-dominator-dominates a lot better.

;; jcd moved this to dominates.lisp
;; (defun first-dominator (p paths)
;;   (if (endp paths)
;;       nil
;;     (if (dominates (car paths) p)
;;         (car paths)
;;       (first-dominator p (cdr paths)))))

;; jcd moved this to dominates.lisp
;; (defthm first-dominator-dominates
;;   (dominates (first-dominator p paths) p))

;Biggest-dominator finds the key, D, which domintes P.  We look up (with assoc)
;D in ALIST to find the spot in R1 associated with it.  Then we read the value
;of that spot in R1.  This gives us a chunk which might be bigger than the
;chunk indicated by P.  So if P is longer than D, we call gp again with the
;tail of P which is missing from d.  This gives us a result of the right size.
(defthm gp-of-mp-when-dominated-by-some-all-diverge
  (implies (and (dominated-by-some p (keys alist))
                (all-diverge (keys alist)) ;the easy case
                )
           (equal (gp p (mp alist r1 r2))
                  ;could make a single call to gp?
                  (gp (nthcdr (len (first-dominator p (keys alist))) p)
                      (gp (cdr (assoc (first-dominator p (keys alist)) alist))
                          r1)))))



;; (defthm gp-of-mp-when-dominated-by-some
;;   (implies (and (dominated-by-some p (keys alist))
;; ;                (all-diverge (keys alist)) ;the easy case
;;                 )
;;            (equal (gp p (mp alist r1 r2))
;;                   (gp (nthcdr (len (biggest-dominator p (keys alist))) p)
;;                       (mp (keep-but-chop-strictly-dominated-pairs (biggest-dominator p (keys alist)) alist)
;;                                r1
;;                                (gp (cdr (assoc (biggest-dominator p (keys alist)) alist)) r1)
;;                                ))))
;;   :hints (("Goal" ;:induct t
;;     ;:induct (MP ALIST R1 R2)
;;            :in-theory (e/d (keep-but-chop-strictly-dominated-pairs
;;                             diverge
;;                             all-diverge
;;                             )
;;                            ((:induction KEEP-BUT-CHOP-STRICTLY-DOMINATED-PAIRS)
;;                             MP-OF-GP
;;                             ))
;;            :do-not '(generalize eliminate-destructors))))


(in-theory (enable gp-of-mp-diverges-from-all-case))

;we keep only those pairs which are (strictly) dominated by P and which come before any pair which dominates P.
;can we use effect-on-spot somehow instead of this?
(defun keep-but-chop-relevant-pairs (p alist)
  (if (endp alist)
      nil
    (if (dominates (caar alist) p)
        nil ; we stop looking, since (car alist) dominates any relevant pairs we might find later on
      (if (dominates p (caar alist))
          (cons (cons (nthcdr (len p) (caar alist)) (cdar alist))
                (keep-but-chop-relevant-pairs p (cdr alist)))
        (keep-but-chop-relevant-pairs p (cdr alist))))))


(defthm keep-but-chop-relevant-pairs-when-diverges-from-all
  (implies (diverges-from-all p (keys alist))
           (equal (keep-but-chop-relevant-pairs p alist)
                  nil)))

;crud.  what if several keys are dominated by p?
;We have the luxury of knowing that we can always remove all of p from each of the relevant paths, since none of them dominate p but we have to say that

(defthm gp-of-mp-when-p-dominates
  (implies (and (not (diverges-from-all p (keys alist)))  ;drop?
                (not (dominated-by-some p (keys alist))))
           (equal (gp p (mp alist r1 r2))
                  (mp (keep-but-chop-relevant-pairs p alist) r1 (gp p r2)))))


;bzo get rid of the "all-diverge"
(defthm gp-of-mp-all-diverge
  (implies (all-diverge (keys alist))
           (equal (gp p (mp alist r1 r2))
                  (if (diverges-from-all p (keys alist))
                      (gp p r2)
                    (if (dominated-by-some p (keys alist))
                        (gp (nthcdr (len (first-dominator p (keys alist))) p)
                            (gp (cdr (assoc (first-dominator p (keys alist)) alist)) r1))
                      (mp (keep-but-chop-relevant-pairs p alist) r1 (gp p r2)))))))

;2HARDCASE
;this comment is out of date!
; This is the case where one or more of the keys in ALIST dominate P.  So the result of calling gp on mp
;doesn't depend on R2 at all (note that R2 does not appear in the conclusion).

;We know at least one key in ALIST dominates P. Biggest-dominator finds the biggest such key.  Call it D.  We look
;up (with assoc) D in ALIST to find the spot in R1 associated with it.  Then we read the value of that spot in R1.
;This gives us a chunk which might be bigger than the chunk indicated by P.  So if P is longer than D, we later
;call gp again with the tail of P which is missing from D; that gives us a result of the right size.  But first we
;might have to copy more data into the chunk associated with D, since pairs from ALIST which come after D and are
;dominated by it may cause changes to it too.

(defthm gp-of-mp-when-dominated-by-some
  (implies (dominated-by-some p (keys alist))
           (equal (gp p (mp alist r1 r2))
                  (mp (keep-but-chop-relevant-pairs p alist)
                           r1
                           (gp (nthcdr (len (first-dominator p (keys alist))) p)
                               (gp (cdr (assoc (first-dominator p (keys alist)) alist)) r1))
                           )))
  :hints (("Goal" :in-theory (disable mp-of-gp))))

;prove rules to simplify the RHS when we do know that all keys in ALIST diverge?
;MAIN LEMMA so far
;no hypotheses!
(defthm gp-of-mp
  (equal (gp p (mp alist r1 r2))
         (if (diverges-from-all p (keys alist))
             (gp p r2)
           (if (dominated-by-some p (keys alist))
               (mp (keep-but-chop-relevant-pairs p alist)
                        r1
                        (gp (nthcdr (len (first-dominator p (keys alist))) p)
                            (gp (cdr (assoc (first-dominator p (keys alist)) alist))
                                r1)))
             (mp (keep-but-chop-relevant-pairs p alist) r1 (gp p r2))))))

(in-theory (disable mp-of-gp)) ;looped

(defthm mp-of-append
  (equal (mp (append alist1 alist2) r1 r2)
         (mp alist1 r1 (mp alist2 r1 r2)))
  :hints (("Goal" :in-theory (e/d ((:induction binary-append)
                                   ) ( ;efficiency:
                                   KEEP-BUT-CHOP-RELEVANT-PAIRS
                                   ALL-DOMINATED-BY-SOME
                                   SP-DOES-NOTHING ;was expensive...
                                   )))))






;Process ALIST by handling each pair as follows:
;If the key of the pair diverges with P, drop the pair.
;If P dominates the key of the pair, chop P off of the front of the key.
;If the key of the pair dominates P (i.e., the key indicates a piece of state bigger than the piece P indicates), replace the
;key with P and append the tail of P (the part of P which is not included in the key of the pair) onto the value field
;of the pair.
;bzo once we find a key that dominates p, can we stop searching?

;this should have a better name?
;effect-on-path
;
;generate a new alist which indicates how ALIST affects the piece of state indicated by P.
;keys in the result are with respect to the piece of state indicated by P, not to the whole state.
;keys in the ALIST argument are with respect to the whole state.
(defund effect-on-spot (p alist)
;  (declare (type t p alist)) ;bzo what should the guard be?
  (if (consp alist)
      (if (diverge p (caar alist))
          (effect-on-spot p (cdr alist))
        (if (strictly-dominates p (caar alist))
            (cons (cons (list::fix (nthcdr (len p) (caar alist))) (list::fix (cdar alist)))
                  (effect-on-spot p (cdr alist)))
    ;In this case, (caar alist) must dominate p:
          (let ((tail (list::fix (nthcdr (len (caar alist)) p))))
            (cons (cons nil ;this means this pair in the alist for (mp alist r1 r2) will set all of r2!
                        (append (cdar alist) tail) ; we move part of the path from the car of the pair to the cdr of the pair!
                        )
    ;                nil
                  (effect-on-spot p (cdr alist))
                  ))))
    nil))

(defthm effect-on-spot-of-non-consp-one
  (implies (not (consp p))
           (equal (effect-on-spot p alist)
                  (path-alist-fix alist)))
  :hints (("Goal" :in-theory (enable effect-on-spot))))

(defthm effect-on-spot-of-non-consp-two
  (implies (not (consp alist))
           (equal (effect-on-spot p alist)
                  nil))
    :hints (("Goal" :in-theory (enable effect-on-spot))))

;; jcd removing, redundant with non-consp-one
;; (defthm effect-on-spot-of-nil-one
;;   (equal (effect-on-spot nil alist)
;;          (path-alist-fix alist)))

;; jcd - removing, redundant with non-consp-two
;; (defthm effect-on-spot-of-nil-two
;;   (equal (effect-on-spot p nil)
;;          nil))

(defthm effect-on-spot-of-append
  (equal (effect-on-spot p (append alist1 alist2))
         (append (effect-on-spot p alist1)
                 (effect-on-spot p alist2)))
  :hints (("Goal" :in-theory (enable append effect-on-spot))))

(defthm effect-on-spot-when-diverges-from-all
  (implies (diverges-from-all p (keys alist))
           (equal (effect-on-spot p alist)
                  nil))
  :hints (("Goal" :in-theory (enable effect-on-spot))))

(defthm effect-on-spot-of-append-onto-keys
  (equal (effect-on-spot p (append-onto-keys p alist))
         (path-alist-fix alist))
  :hints (("Goal" :in-theory (enable effect-on-spot))))

;; jcd removing this, we have the congruence rule now
;; (defthm effect-on-spot-of-alistfix
;;   (equal (effect-on-spot p (alist::alistfix alist))
;;          (effect-on-spot p alist))
;;   :hints (("Goal" :in-theory (enable effect-on-spot))))



(in-theory (disable gp-of-mp))

;; bzo slow proof
;; bzo figure out why :definition of strictly-dominates is necessary
(defthm gp-of-mp-better
  (equal (gp p (mp alist r1 r2))
         (mp (effect-on-spot p alist) r1 (gp p r2)))
  :hints (("Goal" :in-theory (e/d (effect-on-spot
                                     ;; bzo why do we need this?
                                     strictly-dominates
                                     )
                                  (SP-DOES-NOTHING ;efficiency
                                   )))))



;in certain cases, effect-on-spot contains a key of nil, so r2 is not relevant.
;if the alist contains a key of nil, (mp alist r1 r2) is (mp (drop that pair and everything after from the alist) r1 (lookup nil in the alist))

;find the first dominator of p, look it up in the alist, and g the associated value from r1.  then, g with what's left of P to get a p-sized chunk.
;this could be a single call to g?
;then have a call to mp to update

(in-theory (disable MP-OF-GP)) ;looped!

;which values from r1 should be copied to which spots in r3?
;walk down a32.  For each spot, S, in r3, there is a spot, R, in r2. Go see which spots in R1 affect R and pair
;those guys with S directly..  we must remove later keys from a32 which are dominated by the current key!
;(Consider the case where nothing from R1 gets copied to R but a later key dominated by S corresponds to a
;different R' which does have stuff copied in from R1.  That copying should not manifest itself in the result of
;my-compose-alists.

; call (effect-on-spot R a21), then append S to all the keys in the result what if not all of R gets set by
;guys in R1?  set the rest using R2?

;The call to remove-pairs-dominated-by is necessary.  Here's an example that illustrates why.
;Let a32 be '(((1 2) . (:z)) ((1 2) . (:x))) and let a21 be '(((:x) . (:foo)))

;Now, a32 tells us that spot (1 2) in r3 is getting set to what's at spot (:z) in r2.  The shadowed set of spot (1
;2) to what's at (:x) is irrelevant.  But when computing the composition, we ignore the pair of a32; since a21
;doesn't affect (:z), the composition need not include a pair fo (1 2).  But if we processed the second pair of
;a32, we might add the pair ((1 2) . (:foo)) to the composition.  This would be wrong!  As we said, the second
;pair of a32 is irrelevant, so we should not add anything to the composition on its behalf.

;Let a32 be '(((1 2) . (:z)) ((1) . (:x))) and let a21 be '(((:x) . (:foo)))

;bzo guard
;did we need to call remove-shadowed-pairs2?  should effect-on-spot do that?  does it already?
(defun my-compose-alists (a32 a21)
  (if (endp a32)
      nil
    (append (append-onto-keys (caar a32)
                              (remove-shadowed-pairs2
                               (effect-on-spot (cdar a32) a21)))
            (my-compose-alists
             (remove-pairs-dominated-by (caar a32)
                                        (cdr a32))
             a21))))

;; (my-compose-alists '(((3) . (2))) '(((2) . (1))))
;; (my-compose-alists '(((3) . (2))) '((nil . (1))))
;; (my-compose-alists '(((3) . (2))) '(((2 4) . (1))))
;; (my-compose-alists '(((3) . (2))) '(((2 4 6 7) . (1))((2 4 6 8) . (1))))
;; (my-compose-alists '(((3) . (c))) '(((c) . (a))(nil . (b))))
;; (my-compose-alists '(((3) . (c))) '(((c 1) . (a))(nil . (b))))
;; (my-compose-alists '(((3) . (c))(nil . (d))) '(((c 1) . (a))(nil . (b))))
;; (my-compose-alists '((nil . (e))((3) . (c))(nil . (d))) '(((c 1) . (a))(nil . (b))))

(defthm my-compose-alists-of-non-consp-two
  (implies (not (consp a21))
           (equal (my-compose-alists a32 a21)
                  nil)))

(defthm my-compose-alists-of-non-consp-one
  (implies (not (consp a32))
           (equal (my-compose-alists a32 a21)
                  nil)))

;; (defthm effect-on-spot-of-append-onto-keys
;;   (equal (effect-on-spot p (append-onto-keys p alist))
;;          (remove-pairs-dominated-by p alist)
;;          )
;;   :hints (("Goal"; :expand ((APPEND-ONTO-KEYS P ALIST))
;;            :in-theory (enable REMOVE-SHADOWED-PAIRS)
;;            :do-not '(generalize eliminate-destructors))))


(defthm diverges-from-all-of-keys-of-my-compose-alists
  (implies (diverges-from-all p (keys alist1))
           (diverges-from-all p (keys (my-compose-alists alist1 alist2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm sp-of-mp-of-append-onto-keys
  (equal (sp p v (mp (append-onto-keys p alist) r1 r2))
         (sp p v r2)))

(defthmd sp-of-mp-diverges-from-all-case
  (implies (diverges-from-all p (keys alist))
           (equal (sp p v (mp alist r1 r2))
                  (mp alist r1 (sp p v r2)))))

(defthmd mp-of-sp-diverges-from-all-case
  (implies (diverges-from-all p (keys alist))
           (equal (mp alist r1 (sp p v r2))
                  (sp p v (mp alist r1 r2)))))

;bzo loops with defn remove-1? bag::CONS-CAR-ONTO-REMOVE-1-OF-CDR

;; (defthm all-diverges-from-all-diverge-and-subbagp
;;   (implies (and (all-diverge paths2)
;;                 (bag::subbagp paths paths2))
;;            (all-diverge paths))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct t
;;            :expand (ALL-DIVERGE PATHS)
;;            :in-theory (enable bag::subbagp
;;                                      ;all-diverge
;;                                      )))
;;   )
;;
;; ;kill
;; (defthm all-diverges-from-all-diverge-and-subbagp
;;   (implies (and (all-diverge paths2)
;;                 (bag::subbagp paths paths2))
;;            (all-diverge paths))
;;   :hints (("Goal" ;:induct (2-cdrs-induct paths paths2)
;;            ;:induct (len paths2)
;;            :do-not '(generalize eliminate-destructors)
;; ;           :expand (bag::SUBBAGP PATHS PATHS2)
;;           :in-theory (enable all-diverge
;;                              bag::SUBBAGP-OF-REMOVE-1-IMPLIES-SUBBAGP
;;                               bag::subbagp
;;                               (:induction len)
;; ;bag::subbagp
;;                               ))))
;;

(defthm all-diverge-of-keys-of-remove-pairs-dominated-by
  (implies (all-diverge (keys alist))
           (all-diverge (keys (remove-pairs-dominated-by p alist))))
  :hints (("Goal" :in-theory (enable all-diverge))))

(in-theory (disable gp-of-mp-better))

(defthm sp-of-mp-when-not-dominated-by-some
  (implies (not (dominated-by-some p (keys alist)))
           (equal (sp p v (mp alist r1 r2))
                  (mp (remove-pairs-dominated-by p alist) r1 (sp p v r2)))))

(defthm mp-of-sp-when-dominated-by-some
  (implies (dominated-by-some p (keys alist))
           (equal (mp alist r1 (sp p v r2))
                  (mp alist r1 r2))))

;; (defthm mp-of-sp-when-p-dominates-some
;;   (implies (and (dominates-some p (keys alist))
;;                 (not (dominated-by-some p (keys alist)))
;;                 )
;;            (equal (mp alist r1 (sp p v r2))
;;                   what?)))
;; do we need sp-list to state this?

(defun no-shadowed-pairs (alist)
  (if (endp alist)
      t
    (if (dominates-some (caar alist) (keys (cdr alist)))
        nil
      (no-shadowed-pairs (cdr alist)))))

(in-theory (enable gp-of-mp-better))

(defthm not-dominated-by-some-of-keys-of-remove-pairs-dominated-by
  (implies (not (dominated-by-some p (keys alist)))
           (not (dominated-by-some p (keys (remove-pairs-dominated-by p2 alist))))))

(defthm not-dominates-some-of-keys-of-remove-pairs-dominated-by-self
  (not (dominates-some p (keys (remove-pairs-dominated-by p alist)))))

;add ti. did we turn the right one off?
(in-theory (disable SP-OF-MP-WHEN-NOT-DOMINATED-BY-SOME))
;(in-theory (disable MP-of-sp-DIVERGES-FROM-ALL-CASE))

;; jcd - this proof improved tremendously using the new dominates stuff
(defthm mp-of-sp-when-not-dominated-by-some
  (implies (not (dominated-by-some p (keys alist))) ;drop?
           (equal (mp alist r1 (sp p v r2))
                  (sp p
                      (mp (effect-on-spot p alist) r1 v)
                      (mp alist r1 r2)))))

(defthmd helper-eric
  (implies (dominated-by-some p (keys alist))
           (equal (mp (effect-on-spot p alist) r1 v)
                  (gp p (mp alist r1 r2))))
  :hints (("Goal" :in-theory (e/d (effect-on-spot)
                                  (sp-does-nothing
                                   )))))

;watch for loops
(defthm mp-of-sp
  (equal (mp alist r1 (sp p v r2))
         (sp p
             (mp (effect-on-spot p alist) r1 v)
             (mp alist r1 r2)))
  :hints (("Goal"
           :use (helper-eric
                 (:instance mp-of-sp-when-not-dominated-by-some))
           :in-theory (disable mp-of-sp-when-not-dominated-by-some))))




;; (thm
;;  (implies (not (dominated-by-some p (keys alist))) ;drop?
;;           (equal (mp alist r1 (sp p v r2))
;;                  (sp p (g p (mp alist r1 (sp p v r2)))  (mp alist r1 r2))
;;                  )))



;move up?  A "submissive" is a dominated pair which comes before its dominator
;in an alist (thus, its effect comes after the effect of its dominator).
(defun no-submissives (paths)
  (declare (type t paths))
  (if (consp paths)
      (if (strictly-dominated-by-some (car paths) (cdr paths))
          nil
        (no-submissives (cdr paths)))
    t))

(defthm no-submissives-from-all-diverge
  (implies (all-diverge paths)
           (no-submissives paths)))

;; jcd - Cumbersome name
(defthm strictly-dominated-by-some-of-keys-when-strictly-dominated-by-some-of-keys-of-remove-pairs-dominated-by
  (implies (strictly-dominated-by-some p (keys (remove-pairs-dominated-by p2 alist)))
           (strictly-dominated-by-some p (keys alist))))

;; ;bzo just the contrapositive
(defthm not-strictly-dominated-by-some-of-keys-of-remove-pairs-dominated-by
  (implies (not (strictly-dominated-by-some p (keys alist)))
           (not (strictly-dominated-by-some p (keys (remove-pairs-dominated-by p2 alist))))))

(defthm not-strictly-dominated-by-some-of-keys-of-my-compose-alists
  (implies (not (strictly-dominated-by-some p (keys a32)))
           (not (strictly-dominated-by-some p (keys (my-compose-alists a32 a21)))))
  :hints (("Goal" :in-theory (e/d (my-compose-alists)
                                  ;; jcd bzo too bad this needs to be disabled
                                  (not-strictly-dominated-by-some-by-membership)))))



;if not strictly dominated by somebody and not dominates somebody, then diverges from all.
;not true! another pair in a32 may have the same key as the caar of a32 and may set other pieces of the corresponding spot...
;wait! can it?
;where should the alist::alistfix go?
(defthm effect-on-spot-of-my-compose-alists-lemma
  (implies (and (consp a32)
                (not (strictly-dominated-by-some (caar a32) (keys (cdr a32)))))
           (equal (effect-on-spot (caar a32) (my-compose-alists a32 a21))
                  (path-alist-fix
                   (remove-shadowed-pairs2 (effect-on-spot (cdar a32) a21)))))
  :hints (("Goal" :expand (my-compose-alists a32 a21))))

(defthmd sp-of-mp-hack
  (equal (sp p v (mp a32 r2 r3))
         (sp p v (mp (remove-pairs-dominated-by p a32) r2 r3))))


;; (thm
;;  (equal (my-compose-alists (remove-pairs-dominated-by p alist) a21)
;;         (remove-pairs-dominated-by p (my-compose-alists alist a21)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;generalize?
(defthm remove-pairs-dominated-by-of-my-compose-alists-remove-pairs-dominated-by
  (equal (remove-pairs-dominated-by p (my-compose-alists (remove-pairs-dominated-by p alist) a21))
         (remove-pairs-dominated-by p (my-compose-alists alist a21)))
  :hints (("Goal"
           :expand (my-compose-alists
                    (cons (car alist)
                          (remove-pairs-dominated-by p (cdr alist))) a21)
           )))

(defthm remove-pairs-dominated-by-of-caar-and-my-compose-alists
  (equal (remove-pairs-dominated-by (caar a32) (my-compose-alists a32 a21))
         (remove-pairs-dominated-by (caar a32) (my-compose-alists (cdr a32) a21))))

(defthm mp-ignores-path-alist-fix
  (equal (mp (path-alist-fix alist) r1 r2)
         (mp alist r1 r2))
  :hints (("Goal":in-theory (enable effect-on-spot))))



; some odd forcing occurs in the proof?

; We do not believe that the hyp (no-submissives (keys a32)) can be dropped.
; If there are submissives, it's impossible to write compose-alists to do the
; right thing.
(defthm mp-associative
  (implies (no-submissives (keys a32)) ;can't drop this hyp!
           (equal (mp a32 (mp a21 r1 r2) r3)
                  (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3))))

  :hints (("Subgoal *1/3"
           :use ((:instance sp-of-mp-hack
                            (p (caar a32))
                            (v nil)
                            (a32 (my-compose-alists (cdr a32) a21))
                            (r2 r1)
                            (r3  (mp (cdr a32) r2 r3)))
                 (:instance sp-of-mp-hack
                            (p (caar a32))
                            (v nil)
                            (a32  (my-compose-alists a32 a21))
                            (r2 r1)
                            (r3  (mp (cdr a32) r2 r3)))))
          ("Goal"
           :in-theory (e/d (strip-cars)
                           (my-compose-alists)))))


(defthm mp-associative-all-diverge-case
  (implies (all-diverge (keys a32))
           (equal (mp a32 (mp a21 r1 r2) r3)
                  (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3)))))

(defthm mp-commutative-2
  (implies (all-diverge-from-all (keys a31) (keys a32))
           (equal (mp a31 r1 (mp a32 r2 r3))
                  (mp a32 r2 (mp a31 r1 r3)))))

;; (DEFUN MP-induct (ALIST R1 R2)
;;   (IF (ENDP ALIST)
;;       R2
;;       (LET* ((PAIR (CAR ALIST))
;;              (D (CAR PAIR))
;;              (U (CDR PAIR)))
;;             (MP-induct (CDR ALIST) R1 (sp d (gp u r1) R2)))))

;; ;(in-theory (disable keys vals))

;; ;show that clears are the same and the gp-lists of (keys a32) are the same?

;; ;what do we know about my-compose-alists...?

;; (defthm mp-associative-easy-case-better-helper
;;   (implies (and; (no-submissives (keys a32)) ;drop this hyp?
;;                ; (no-submissives (keys a21))
;;     ;(no-shadowed-pairs a32)
;;                 (list-of-true-listps (keys a32))
;;                 (list-of-true-listps (keys a21))
;;                 (list-of-true-listps (vals a32))
;;                 (list-of-true-listps (vals a21))
;;                 (equal blah (my-compose-alists a32 a21) )
;;                 )
;;            (equal (mp a32 (mp a21 r1 r2) r3)
;;                   (mp blah  r1 (mp a32 r2 r3))))
;;   :hints (("Subgoal *1/1" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/2" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/3" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/4" :expand ( ;(MY-COMPOSE-ALISTS A32 A21)
;;     ;(MP A32 (MP A21 R1 R2) R3)
;;                                    )
;;            )
;;           ("Subgoal *1/5" :expand ((MY-COMPOSE-ALISTS A32 A21)

;;                                    )
;;            )
;;           ("Goal" ;:induct (MP-induct a32 r2 r3)
;;            :induct (len a32)
;;            :in-theory (e/d (mp
;;                                                         (:induction len)
;;                             ALL-DIVERGE) (;sp-equal-rewrite
;;                                           ;GP-OF-MP-BETTER
;;                                           ;my-compose-alists
;;     ;mp-of-sp
;;                           ;  (:induction my-compose-alists)
;;                             (:induction keys)

;;                             (:induction vals)
;;        (:induction mp)
;;                             ))
;;            :do-not '(generalize eliminate-destructors))))



;; (defthm mp-associative-easy-case-better-helper
;;   (implies (and (no-submissives (keys a32)) ;drop this hyp?
;;                 (no-submissives (keys a21))
;;     ;(no-shadowed-pairs a32)
;;                 (list-of-true-listps (keys a32))
;;                 (list-of-true-listps (keys a21))
;;                 (list-of-true-listps (vals a32))
;;                 (list-of-true-listps (vals a21))
;; ;                (equal a32-prime a32)
;;                 )
;;            (equal (mp a32 (mp a21 r1 r2) r3)
;;                   (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3))))
;;   :hints (("Subgoal *1/1" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/2" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/3" :expand ((MP A32 (MP A21 R1 R2) R3))
;;            )
;;           ("Subgoal *1/4" :expand ( ;(MY-COMPOSE-ALISTS A32 A21)
;;     ;(MP A32 (MP A21 R1 R2) R3)
;;                                    )
;;            )
;;           ("Subgoal *1/5" :expand ((MY-COMPOSE-ALISTS A32 A21)

;;                                    )
;;            )
;;           ("Goal" ;:induct (MP-induct a32 r2 r3)
;;            :induct (len a32)
;;            :in-theory (e/d (mp
;;                                                         (:induction len)
;;                             ALL-DIVERGE) (;sp-equal-rewrite
;;                                           ;GP-OF-MP-BETTER
;;                                           ;my-compose-alists
;;     ;mp-of-sp
;;                           ;  (:induction my-compose-alists)
;;                             (:induction keys)

;;                             (:induction vals)
;;        (:induction mp)
;;                             ))
;;            :do-not '(generalize eliminate-destructors))))

;; ;should REMOVE-PAIRS-DOMINATED-BY, etc. work on paths or keys?

;; (defthm strictly-dominated-by-some-of-keys-of-remove-pairs-dominated-by
;;   (equal (strictly-dominated-by-some path (keys (remove-pairs-dominated-by path alist)))
;;          (strictly-dominated-by-some path (keys alist))))

;; (defthm strictly-dominated-by-some-of-keys-of-remove-pairs-dominated-by-gen
;;   (implies (list::equiv path path2)
;;            (equal (strictly-dominated-by-some path (keys (remove-pairs-dominated-by path2 alist)))
;;                   (strictly-dominated-by-some path (keys alist)))))

;; (defthm strictly-dominated-by-some-of-keys-of-remove-pairs-dominated-by-gen-2
;;   (implies (not (dominates path2 path))
;;            (equal (strictly-dominated-by-some path (keys (remove-pairs-dominated-by path2 alist)))
;;                   (strictly-dominated-by-some path (keys alist)))))

;; (defthm strictly-dominated-by-some-of-keys-of-remove-shadowed-pairs2
;;   (equal (strictly-dominated-by-some p (keys (remove-shadowed-pairs2 alist)))
;;          (strictly-dominated-by-some p (keys alist)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (defthm no-submissives-of-keys-of-remove-pairs-dominated-by
;;   (implies  (no-submissives (keys alist))
;;             (no-submissives (keys (remove-pairs-dominated-by p alist)))))

;; (defthm no-submissives-of-keys-of-remove-shadowed-pairs2
;;   (implies (no-submissives (keys a32))
;;            (no-submissives (keys (remove-shadowed-pairs2 a32))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable remove-shadowed-pairs2))))

;; (defthm no-shadowed-pairs-of-remove-shadowed-pairs2
;;   (no-shadowed-pairs (remove-shadowed-pairs2 a32))
;;   )

;; (defun remove-pairs-dominated-by-list (p-list alist)
;;   (if (endp p-list)
;;       alist
;;     (remove-pairs-dominated-by (car p-list) (remove-pairs-dominated-by-list (cdr p-list) alist))))

;; (defun remove-pairs-dominated-by-list2 (p-list alist)
;;   (if (endp p-list)
;;       alist
;;     (remove-pairs-dominated-by-list2 (cdr p-list) (remove-pairs-dominated-by (car p-list) alist))))

;; (defthm remove-shadowed-pairs2-of-non-consp
;;   (implies (not (consp alist1))
;;            (equal (remove-shadowed-pairs2 alist1)
;;                   nil)))

;; (defthm remove-pairs-dominated-by-of-append
;;   (equal (remove-pairs-dominated-by p (append alist1 alist2))
;;          (append (remove-pairs-dominated-by p alist1)
;;                  (remove-pairs-dominated-by p alist2))))

;; (defthm remove-pairs-dominated-by-list2-of-non-consp
;;   (implies (not (consp alist))
;;            (equal (remove-pairs-dominated-by-list2 p-list alist)
;;                   (if (endp p-list)
;;                       alist
;;                     nil))))


;; (defthm remove-pairs-dominated-by-list2-of-remove-pairs-dominated-by
;;   (equal (remove-pairs-dominated-by-list2 p-list (remove-pairs-dominated-by p alist))
;;          (remove-pairs-dominated-by p (remove-pairs-dominated-by-list2 p-list alist))))


;; ;bzo gross subgoal hint
;; (defthm remove-shadowed-pairs2-of-append
;;   (equal (remove-shadowed-pairs2 (append alist1 alist2))
;;          (append (remove-shadowed-pairs2 alist1)
;;                  (remove-pairs-dominated-by-list2 (keys alist1)  (remove-shadowed-pairs2 alist2))))
;;   :hints (("Subgoal *1/1'" :in-theory (enable REMOVE-PAIRS-DOMINATED-BY-OF-APPEND))
;;           ("Goal" :expand (REMOVE-SHADOWED-PAIRS2 ALIST1)
;;            :induct t
;;            :in-theory (e/d (append) (REMOVE-SHADOWED-PAIRS2
;;                                      REMOVE-PAIRS-DOMINATED-BY-OF-APPEND
;;                                      ))
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm dominates-of-append-and-append
;;      (equal (dominates (append p p1)
;;                        (append p p2))
;;             (dominates p1
;;                        p2))
;;      :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;               :in-theory (enable dominates append))))


;; ;go the other way?
;; (defthm remove-pairs-dominated-by-of-append-onto-keys
;;   (equal (remove-pairs-dominated-by (append p path) (append-onto-keys p alist))
;;          (append-onto-keys p (remove-pairs-dominated-by path alist)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defthm remove-shadowed-pairs2-of-append-onto-keys
;;   (equal (remove-shadowed-pairs2 (append-onto-keys p alist))
;;          (append-onto-keys p (remove-shadowed-pairs2 alist)))
;;   :hints (("Goal" :in-theory (disable remove-shadowed-pairs2-of-remove-pairs-dominated-by)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm remove-pairs-dominated-by-of-remove-pairs-dominated-by-list2
;;   (equal (remove-pairs-dominated-by p (remove-pairs-dominated-by-list2 p-list alist))
;;          (remove-pairs-dominated-by-list2 p-list (remove-pairs-dominated-by p alist))))



;; (in-theory (disable remove-pairs-dominated-by-list2-of-remove-pairs-dominated-by))

;; (defthm remove-pairs-dominated-by-list2-of-remove-shadowed-pairs2
;;  (equal (remove-pairs-dominated-by-list2 p-list (remove-shadowed-pairs2 alist))
;;         (remove-shadowed-pairs2 (remove-pairs-dominated-by-list2 p-list alist)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors preprocess))))

;; ;LIST is a list of paths.  Extact the values from each of those paths in R.
;; (defund gp-list (list r)
;;   (if (consp list)
;;       (cons (gp (car list) r)
;;             (gp-list (cdr list) r))
;;     nil))



;; (defun lookup (val alist)
;;   (cdr (assoc val alist)))

;; (defund lookup-list (keys alist)
;;   (if (consp keys)
;;       (cons (lookup (car keys) alist)
;;             (lookup-list (cdr keys) alist))
;;     nil))

;; (defthm gp-list-of-nil
;;   (equal (gp-list nil r)
;;          nil)
;;   :hints (("Goal" :in-theory (enable gp-list))))

;; (defun all-pairs-dominated-somehow (alist1 alist2)
;;   (if (endp alist1)
;;       t
;;     (and (dominated-by-some (caar alist1) (keys alist2))
;;          (all-pairs-dominated-somehow (cdr alist1) alist2))))

;; ;try going the other way?
;; (defthm mp-associative-hard
;;   (implies (no-shadowed-pairs a32);t;(all-diverge (keys a32)) ;drop this hyp!
;;            (equal (mp a32 (mp a21 r1 r2) r3)
;;                   (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3))))
;;   :hints (("Subgoal *1/3'''" :in-theory (enable mp-of-sp))
;;           ("Goal" ;:induct (2-cdrs-induct a32 a21)

;;            :in-theory (e/d (ALL-DIVERGE)
;;                            (;(:induction mp)
;;                             ;SP-EQUAL-REWRITE
;;                             ;MY-COMPOSE-ALISTS
;;                             ;GP-OF-MP-BETTER
;;                             ;MP-OF-Sp
;;                             ;(:induction NO-SHADOWED-PAIRS)
;;                             ;(:induction MY-COMPOSE-ALISTS)
;;                             ))
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm mp-associative-hard-case
;;   (implies ;t;(all-diverge (keys a32)) ;drop this hyp!
;;            (and (no-shadowed-pairs a32)
;;                 ;(no-shadowed-pairs a21)
;;                 )

;;            (equal (mp a32 (mp a21 r1 r2) r3)
;;                   (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3))))
;;   :hints (;("Subgoal *1/3''" :in-theory (enable  sp-of-mp-diverges-from-all-case))
;;           ("Goal" :induct (MP A32 R2 R3)
;;            :in-theory (enable all-diverge
;;                                      REMOVE-SHADOWED-PAIRS2
;;                                      )
;;            :do-not '(generalize eliminate-destructors))))

;; ;this isn't terribly satisfying.
;; ;and it's not true!
;; ;what if there's a key that's shorter then (len p)
;; (defthmd gp-of-mp
;;   (equal (gp p (mp alist r1 r2))
;;          (mp (nthcdr-from-keys (len p) alist) r1 (gp p r2))
;;          )
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ( ;(NTHCDR-FROM-KEYS (LEN P) ALIST)
;;                     )
;;            :in-theory (enable ;gp
;;                               nthcdr-from-keys
;;                               mp
;; ;len
;;                               ))))


;; (defthmd g-of-mp-2
;;   (implies (list::memberp a (keys alist))
;;            (equal (g a (mp alist r1 r2))
;;                   (g (cdr (assoc a alist)) r1))))

;; (defthm g-of-mp-both
;;   (equal (g a (mp alist r1 r2))
;;          (if (list::memberp a (keys alist))
;;              (g (cdr (assoc a alist)) r1)
;;            (g a r2)))
;;   :hints (("Goal" :in-theory (e/d (g-of-mp-2
;;                                    g-of-mp-1)
;;                                   (mp)))))

;; (defthm mp-ignores-list-fix
;;   (equal (mp (list::fix alist) r1 r2)
;;          (mp alist r1 r2)))

;; (defthm mp-of-s-1-non-memberp-case-helper
;;   (implies (and (bag::unique (keys alist)) ;drop this hyp in the non-helper lemma!
;;                 (not (list::memberp a (range alist))))
;;            (equal (mp alist (s a v r1) r2)
;;                   (mp alist r1 r2)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable mp
;;                               bag::UNIQUE-OF-CONS
;;                               ))))

;; (defthm mp-of-clr-key
;;   (equal (mp (clr-key k alist) r1 r2)
;;          (s k (g k r2) (mp alist r1 r2))))

;; (defthm mp-ignores-remove-shadowed-pairs
;;   (equal (mp (remove-shadowed-pairs alist) r1 r2)
;;          (mp alist r1 r2))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable mp remove-shadowed-pairs))))

;; ;bzo add a not memberp vals version of this?
;; (defthm mp-of-s-1-non-memberp-case
;;   (implies (not (list::memberp a (range alist)))
;;            (equal (mp alist (s a v r1) r2)
;;                   (mp alist r1 r2)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (disable mp)
;;            :use (:instance mp-of-s-1-non-memberp-case-helper (alist (remove-shadowed-pairs alist))))))

;; (defthm mp-of-s-1-memberp-both
;;   (equal (mp alist (s a v r1) r2)
;;          (if (list::memberp a (range alist))
;;              (s-list (pre-image a alist) (repeat (num-keys-for a alist) v) (mp alist r1 r2))
;;            (mp alist r1 r2))))

;; ;other case?
;; (defthmd s-of-mp-non-memberp-case
;;   (implies (not (list::memberp key (keys alist)))
;;            (equal (s key val (mp alist r1 r2))
;;                   (mp alist r1 (s key val r2)))))

;; (defthmd mp-of-s-2-memberp-case
;;   (implies (list::memberp a (keys alist)) ;say domain instead of keys?
;;            (equal (mp alist r1 (s a v r2))
;;                   (mp alist r1 r2)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable mp keys  s-of-mp-non-memberp-case)
;;            )))

;; (defthmd mp-of-s-2-non-memberp-case
;;   (implies (not (list::memberp a (keys alist))) ;say domain instead of keys?
;;            (equal (mp alist r1 (s a v r2))
;;                   (s a v (mp alist r1 r2))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (mp keys s-of-mp-non-memberp-case) ( mp-of-s-2-memberp-case))
;;            )))

;; (defthm mp-of-s-2-both
;;   (equal (mp alist r1 (s a v r2))
;;          (if (list::memberp a (keys alist))
;;              (mp alist r1 r2)
;;            (s a v (mp alist r1 r2))))
;;   :hints (("Goal" :in-theory (enable mp-of-s-2-memberp-case
;;                                      mp-of-s-2-non-memberp-case))))

;; ;; A function to increase the depth of a list of index paths with a
;; ;; single index (a) using cons.

;; ;bzo should be prefix-bag?
;; (defund prefix-list (a list)
;;   (declare (type t a list))
;;   (if (consp list)
;;       (cons (cons a (car list))
;;             (prefix-list a (cdr list)))
;;     nil))

;; ;; A function to increase the depth of a list of index paths with a prefix
;; ;; path (x) of arbitrary length using append. (is this useful?)

;; (defund prepend-list (x list)
;;   (declare (xargs :guard (true-listp x)))
;;   (if (consp list)
;;       (cons (append x (car list))
;;             (prepend-list x (cdr list)))
;;     nil))

;; ;; A function that creates a bag of "path parts" (pp) that fully
;; ;; describe the D/U behavior of gp and sp.  Is this useful??
;; ;; (Is this the formulation we want to use to reason about gp/sp
;; ;; or is there an easier recursion?)

;; ;bzo use the bag constructors instead of cons?
;; ;Returns the bag of all (non-empty) prefixes of PATH, including PATH itself (unless PATH is empty)
;; (defund pp (path)
;;   (declare (type t path))
;;   (if (consp path)
;;       (cons (list (car path)) (prelist-fix (car path) (pp (cdr path))))
;;     nil))

;; ;drop?
;; (defthm true-listp-of-car-of-pp
;;   (true-listp (car (pp path)))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("Goal" :in-theory (enable pp))))



;; ;; Of course, pp is unique:

;; (defthm not-memberp-cons-prelist-fix
;;   (implies (not (list::memberp x yy))
;;            (not (list::memberp (cons a x) (prelist-fix a yy))))
;;   :hints (("Goal" :in-theory (enable prelist-fix))))

;; (defthm unique-of-prelist-fix-from-unique
;;   (implies (bag::unique list)
;;            (bag::unique (prelist-fix a list)))
;;   :hints (("Goal" :in-theory (enable bag::UNIQUE-OF-CONS bag::unique prelist-fix))))

;; (defthm car-of-pp-non-nil
;;   (implies (consp path)
;;            (car (pp path)))
;;   :hints (("Goal" :in-theory (enable pp))))

;; (defthm not-memberp-nil-of-prelist-fix
;;   (NOT (bag::MEMBERP NIL (PRELIST-FIX a x)))
;;   :hints (("Goal" :in-theory (enable prelist-fix))))

;; (defthm nil-not-memberp-of-cdr-path
;;   (not (list::memberp nil (pp path)))
;;   :hints (("Goal" :in-theory (enable pp))))

;; (defthm consp-of-pp
;;   (equal (consp (pp path))
;;          (consp path))
;;   :hints (("Goal" :in-theory (enable pp))))

;; (defthm singleton-not-memberp-of-prelist-fix
;;   (implies (not (list::memberp nil path))
;;            (not (list::memberp (list a) (prelist-fix a path)))))


;; (defthm unique-pp
;;   (bag::unique (pp path))
;;   ;:rule-classes nil
;;   :hints (("Goal" :in-theory (enable pp
;;                                      bag::unique
;;                                      bag::UNIQUE-OF-CONS)))
;;   )


;; ;; subpath/subgag-p relationship ..
;; (defthm subpath-implies-subbag-pp
;;   (implies (dominates p1 p2)
;;            (bag::subbagp (pp p1) (pp p2)))
;;   :rule-classes nil
;;   :hints (("Goal" :in-theory (enable dominates pp))))

;; ;; A rule that employs pp to describe non-interference




;; (defthm disjoint-pps-mean-cannot-interfere
;;   (implies (and (bag::disjoint (pp p1) (pp p2))
;;                 (consp p1)
;;                 (consp p2)
;;                 )
;;            (diverge p1 p2))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable pp diverge bag::disjoint DOMINATES))))


;; ;prove from dominates version?
;; (defthm gp-over-sp-disjoint
;;   (implies (and (bag::disjoint (pp p1) (pp p2))
;;                 (consp p1) ;added by Eric; okay?
;;                 (consp p2) ;added by Eric; okay?
;;                 )
;;            (equal (gp p1 (sp p2 v r))
;;                   (gp p1 r))))

;; bzo why does this call s instead of sp?
;; ;Change R by setting the values at the paths in PATHS to the corresponding values in VALS.
;; ;PATHS is a list of paths.  VALS is a list of values
;; ;Returns a changed version of R.
;; ;bzo perhap this does the calls to sp in the wrong order.  maybe this should not be tail-recursive.  bzo are there other functions which do stuff in the wrong order?
;; ;bzo maybe this should stop when it runs out of vals?

;; (defund sp-list (paths vals r)
;;   (if (consp paths)
;;       (s (car paths) (car vals)
;;          (sp-list (cdr paths) (cdr vals) r))
;;     r))



;; ;; The copy function is implemented using gp/sp ..

;; ;change R2 to match R1 on the values at the paths in LIST
;; (defund mp-list (list r1 r2)
;;   (sp-list list (gp-list list r1) r2))

;; ;; A generalization of pp ..

;; ;make a list (bag?) of all the prefixes of all the paths in LIST.
;; (defund pp-list (list)
;;   (if (consp list)
;;       (append (pp (car list))
;;               (pp-list (cdr list)))
;;     nil))




;; (defthm diverge-from-diverges-from-all
;;   (implies (and (diverges-from-all path1 list) ;list is a free var
;;                 (list::memberp path2 list))
;;            (diverge path1 path2))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))



;; (defthm diverge-from-diverges-from-all-two
;;   (implies (and (diverges-from-all path2 list) ;list is a free var
;;                 (list::memberp path1 list))
;;            (diverge path1 path2))
;;   :hints (("Goal" :use (:instance diverge-from-diverges-from-all (path1 path2) (path2 path1))
;;            :in-theory (disable diverge-from-diverges-from-all))))


;; (defthm DIVERGES-FROM-ALL-of-cons
;;   (equal (DIVERGES-FROM-ALL PATH (CONS a LIST))
;;          (and (diverge path a)
;;               (DIVERGES-FROM-ALL PATH LIST)))
;;   :hints (("Goal" :in-theory (enable DIVERGES-FROM-ALL))))


;; (defthm gp-list-of-sp
;;   (implies (diverges-from-all path list)
;;            (equal (gp-list list (sp path v r))
;;                   (gp-list list r)))
;;   :hints (("Goal" :in-theory (enable gp-list))))

;; (defthm gp-of-sp-list
;;   (implies (diverges-from-all path list)
;;            (equal (gp path (sp-list list v r))
;;                   (gp path r)))
;;   :hints (("Goal" :in-theory (enable sp-list))))

;; ;hyp was    (disjoint (pp-list list1)
;; ;             (pp-list list2))
;; ;consider a cannot-interfere version of this? <-- huh?
;; (defthm gp-list-over-sp-list-disjoint
;;   (implies (all-diverge-from-all list1 list2)
;;            (equal (gp-list list1 (sp-list list2 values r))
;;                   (gp-list list1 r)))
;;   :hints (("Goal" :in-theory (enable gp-list sp-list all-diverge-from-all))))



;; ;;
;; ;;
;; ;; alists (bzo eric is starting with alists that contain atomic addresses, but all this should be changed to allow addresses that are paths)
;; ;;
;; ;;



;; ;we use the built-in function acons: (acons key datum alist)

;; ;add new binding to ALIST by binding keys from KLIST to the corresponding values from VLIST
;; ;stuff coming early in KLIST and VLIST shadows stuff coming later (and stuff already in ALIST)
;; (defun aappend (klist vlist alist)
;;   (declare (type (satisfies alistp) alist))
;;   (if (and (consp klist)
;;            (consp vlist))
;;       (acons (car klist) (car vlist)
;;              (aappend (cdr klist) (cdr vlist) alist))
;;     alist))

;; (defun swap (alist)
;;   (declare (type (satisfies alistp) alist))
;;   (if (consp alist)
;;       (acons (cdar alist) (caar alist)
;;              (swap (cdr alist)))
;;     nil))


;; ;move hyp into conclusion.   make an alist::alistfix.
;; (defthm aappend-keys-vals
;;   (equal (aappend (keys alist1) (vals alist1) alist2)
;;          (append (alist::alistfix alist1) alist2))
;;   :hints (("Goal" :in-theory (enable append))))

;; (defthm swap-swap
;;   (equal (swap (swap alist))
;;          (alist::alistfix alist)))

;; (defthm aappend-over-append
;;   (implies (equal (len w) (len y))
;;            (equal (aappend (append w x) (append y z) alist)
;;                   (aappend w y
;;                            (aappend x z alist)))))






;; ;We'll use records to do this

;; ;;
;; ;; A mapping is something that maps indices in one data structure
;; ;; to indices in another.  A mapping is an association list between
;; ;; two bags.
;; ;;

;; ;; The use set (bag) of the map is just the keys of an association list ..

;; ;bzo consider using strip-cars? or just use records.
;; (defun use (map)
;;   (if (consp map)
;;       (let ((key (caar map)))
;;         (cons key (use (cdr map))))
;;     nil))

;; ;; The def set (bag) of a map are the values of the alist

;; ;bzo consider using strip-cdrs?
;; (defun def (map)
;;   (if (consp map)
;;       (let ((key (cdar map)))
;;         (cons key (def (cdr map))))
;;     nil))

;; ;; The mp-list ("map list") function is the function that actually moves the
;; ;; values from one data structure to another.  It is just a generalization of
;; ;; the copy function ..

;; (defun mp-list (map r1 r2)
;;   (sp-list (def map) (gp-list (use map) r1) r2))


;; ;rcar; returns a pair
;; ;you shouldn't count on the order in which pair are returned
;; (defun rcar2 (r)
;;   (cons (car r) (g (car r) r)))





;; (defthm acl2-count-of-consp
;;   (implies (consp x)
;;            (< 0 (acl2-count x)))
;;   :rule-classes (:rewrite :linear))






;; ;redo this?  use the measure rob mentions in maps.lisp?
;; (defun rempty2 (r)
;;   (endp (acl2->rcd r)))


;; ;; The xlat function maps an index from the use side of a map into the def side
;; ;; of a map.

;; (defun xlat (a map)
;;   (if (consp map)
;;       (if (equal a (caar map))
;;           (cdar map)
;;         (xlat a (cdr map)))
;;     a))

;; ;; The "dot" function creates an association list given two lists of indices.

;; (defun dot (list1 list2)
;;   (if (and (consp list1) (consp list2))
;;       (cons (cons (car list1) (car list2))
;;             (dot (cdr list1) (cdr list2)))
;;     nil))

;; ;; The swap function swaps the direction of the map (swaps the keys and values
;; ;; of the alist).

;; (defun swap (map)
;;   (if (consp map)
;;       (cons (cons (cdar map) (caar map))
;;             (swap (cdr map)))
;;     nil))

;; #+joe
;; (defthm swap-dot
;;   (equal (swap (dot x y))
;;          (dot y x)))

;; #+joe
;; (defthm xlat-identity
;;   (equal (xlat a (dot x x)) a))

;; ;; The xlat-list function applies the xlat function to a list.

;; (defun xlat-list (list map)
;;   (if (consp list)
;;       (cons (xlat (car list) map)
;;             (xlat-list (cdr list) map))
;;     nil))

;; ;; Some helper functions ..

;; (defun remove-all (x list)
;;   (if (consp x)
;;       (let ((list (remove (car x) list)))
;;         (remove-all (cdr x) list))
;;     list))

;; ;; remove every alist instance whose key matches the key argument

;; (defun remove-all-key (key alist)
;;   (if (consp alist)
;;       (if (equal (caar alist) key)
;;           (remove-all-key key (cdr alist))
;;         (cons (car alist)
;;               (remove-all-key key (cdr alist))))
;;     nil))

;; ;; remove every alist instance whose key is a member of x

;; (defun remove-all-keys (x alist)
;;   (if (consp x)
;;       (let ((alist (remove-all-key (car x) alist)))
;;         (remove-all-keys (cdr x) alist))
;;     alist))

;; (defun split-map (mab mcd)
;;   (let ((b (def mab)))
;;     (let ((c (use mcd)))
;;       (let ((b-c (remove-all c b)))
;;         (let ((mba (swap mab)))
;;           (let ((mba (remove-all-keys b-c mba)))
;;             (let ((b^c (use mba)))
;;               (let ((bd (xlat-list b^c mcd)))
;;                 (let ((mad (dot (def mba) bd)))
;;                   (let ((mcd (remove-all-keys b^c mcd)))
;;                     (mv mad mcd)))))))))))

;; #+joe
;; (defthm mp-list-normalization
;;   (implies
;;    (and
;;     (unique (pp-list (use mcd))) ; are there more hyps?
;;     (equal pair (split-map mab mcd))) ; doing this here provides some efficiency ..
;;    (equal (mp-list mcd (mp-list mab rx ry) rz)
;;           (mp-list (v0 pair) rx
;;                    (mp-list (v1 pair) ry rz)))))

;; (defmacro m* (&rest args)
;;   (if (consp args)
;;       (if (consp (cdr args))
;;           `(mp-list ,(caar args) ,(cdar args) (m* ,@(cdr args)))
;;         (car args))
;;     args))

;; #+joe
;; (defthm mp-list-push-of-lift
;;   (implies
;;    (unique (pp-list (def map)))
;;    (equal (mp-list (swap map) (mp-list map r1 r2) r1)
;;           r1)))

;; ;;
;; ;; We will eventually want a z*-style function for comparing data
;; ;; structures ..
;; ;;

;; ;; We will probably need something like this rule eventually ..

;; #+joe
;; (defthm z*-equal-free-reduction
;;   (implies
;;    (equal (z* list1 r1)
;;           (z* list1 r2))
;;    (iff (equal (z* list r1)
;;                (z* list r2))
;;         (equal (g* (- list1 list) r1)
;;                (g* (- list1 list) r2)))))

;; ;; =====================================================
;; ;;
;; ;; Data Structure Substrate
;; ;;
;; ;; =====================================================

;; (defun new-structure (type value)
;;   (s :type type
;;      (s :base 0
;;         (s :value value nil))))

;; (defun new-array-body (size type default)
;;   (if (zp size) nil
;;     (let ((size (1- size)))
;;       (s size (new-structure type default)
;;          (new-array-body size type default)))))

;; (defun new-array (size type default)
;;   (new-structure :str (new-array-body size type default)))



;; ;; These are the functions we would use to access the fields of a data
;; ;; structure .. the functions that would be used directly by the defstructure
;; ;; interface functions.  Note that we will have to distinguish between atomic
;; ;; entries in the data structure and hierarchical data structure descriptions.

;; ;; To access sub-structures ..

;; (defun gs (index ds)
;;   (gp `(:value ,index) ds))

;; (defun ss (index v ds)
;;   (sp `(:value ,index) v ds))

;; ;; To access atomic values ..

;; (defun gval (index ds)
;;   (gp `(:value ,index :value) ds))

;; (defun sval (index v ds)
;;   (sp `(:value ,index :value) v ds))

;; ;; So we use abstract paths to describe the elements of the data structure.
;; ;; At the abstract level, all we need to manipulate are index values.  The
;; ;; functions gap/sap (get abstract path, set abstract path) interpret abstract
;; ;; paths using gs/ss as primitives.  Abstract paths use true lists to
;; ;; designate structures and cons lists to designate atoms.

;; (defun gap (path ds)
;;   (if (consp path)
;;       (gap (cdr path) (gs (car path) ds))
;;     (if (null path)
;;         ds
;;       (gval path ds))))

;; (defun sap (path v ds)
;;   (if (consp path)
;;       (ss (car path) (sap (cdr path) v (gs (car path) ds)) ds)
;;     (if (null path)
;;         v
;;       (sval path v ds))))

;; ;; We can define a function to map abstract paths into raw paths ..

;; (defun raw-path (path)
;;   (if (consp path)
;;       (cons :value
;;             (cons (car path)
;;                   (raw-path (cdr path))))
;;     (if (null path)
;;         nil
;;       (list :value (car path) :value))))

;; ;; Such that ..

;; #+joe
;; (defthm gap-apath-to-gp-raw-path
;;   (equal (gap apath ds)
;;          (gp (raw-path apath) ds)))

;; ;; Here is are some functions that create simple data structure
;; ;; descriptions ..

;; (defun add-slot (name type value r)
;;   (s name (new-structure type value) r))

;; (defun sspec ()
;;   (let* ((body nil)
;;          (body (add-slot :pc  :str (new-array 4 :int -1) body))
;;          (body (add-slot :tos :str (new-array 4 :int -2) body))
;;          (body (add-slot :ram :str (new-array 4 :int -3) body)))
;;     (new-structure :str body)))

;; ;;
;; ;; ===================================================
;; ;;
;; ;; Extensions to the records library to enable
;; ;; recursion over records ..
;; ;;
;; ;; ===================================================
;; ;;

;; (defun rendp (r) (endp r)) ;; (not (wf-record r))
;; (defun rcaar (r) (caar r))
;; (defun rcdar (r) (cdar r))
;; (defun rcdr  (r) (cdr  r))
;; (defun rcons (k v r) (cons (cons k v) r))

;; ;; Here is how we would use them ..

;; (defthm rcdr-measure
;;   (implies
;;    (not (rendp r))
;;    (o< (acl2-count (rcdr r))
;;        (acl2-count r))))

;; (defthm rcdar-measure
;;   (implies
;;    (not (rendp r))
;;    (o< (acl2-count (rcdar r))
;;        (acl2-count r))))

;; ;; Compute all of the keys in a record.

;; (defun rkeys (r)
;;   (if (rendp r) r
;;     (cons (rcaar r)
;;           (rkeys (rcdr r)))))

;; (defstub reserved? (key) nil)
;; (defstub ptr? (val) nil)

;; ;; Another example of how we might use these functions ..

;; (defun modify (r)
;;   (if (rendp r) r
;;     (let ((key (rcaar r))
;;           (val (rcdar r))
;;           (r   (rcdr r)))
;;       (if (reserved? key) (rcons key val (modify r))
;;         (let ((val (if (ptr? val) (modify val) val)))
;;           (rcons key val (modify r)))))))

;; (defun zed-keys
;;   (append (foo-keys)
;;           (list a b)))

;; (defun zed-p (st)
;;   (and (foo-p st)
;;        (integerp (a-val st))
;;        (listp (b-val st))))

;clrp of sp??

(defthm gp-of-nil-two
  (equal (gp p nil)
         nil)
  :hints (("Goal" :in-theory (enable gp))))

;;
;; CLRP
;;

;"zero out" whatever is at P (actually, set it to nil)
(defund clrp (p r)
  (declare (type t p r))
  (sp p nil r))

(defthm sp-to-clrp
  (equal (sp p nil r)
         (clrp p r))
  :hints (("Goal" :in-theory (enable clrp))))

(defthm clrp-of-nil-two
  (equal (clrp p nil)
         nil)
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

(defthm clrp-of-nil-one
  (equal (clrp nil p)
         nil)
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

;see also CLRP-OF-NIL-ONE
;disabling, since might be expensive
(defthmd clrp-when-p-not-consp
  (implies (not (consp p))
           (equal (CLRP p r)
                  nil))
  :hints (("Goal" :in-theory (e/d (CLRP) (sp-to-clrp)))))


(defthmd clrp-singleton-becomes-clr
  (equal (clrp (list key) r)
         (acl2::clr key r))
  :hints (("Goal" :in-theory (e/d (clrp sp ACL2::CLR) (;SP==R ;bzo looped
                                                       SP-TO-CLRP
                                                       acl2::s==r
                                                       )))))
(defthmd clr-becomes-clrp-singleton
  (equal (acl2::clr key r)
         (clrp (list key) r))
  :hints (("Goal" :in-theory (enable clrp-singleton-becomes-clr))))



;zero out each path in PATHS
;This is the function that Greve calls "z".
(defund clrp-list (paths r)
  (declare (type t paths r))
  (if (consp paths)
      (clrp (car paths) (clrp-list (cdr paths) r))
    r))

(defthmd open-clrp-list
  (implies
   (consp paths)
   (equal (clrp-list paths r)
          (clrp (car paths) (clrp-list (cdr paths) r))))
  :hints (("goal" :in-theory (enable clrp-list))))

(defthm clrp-list-of-non-consp
  (implies (not (consp paths))
           (equal (clrp-list paths r)
                  r))
  :hints (("Goal" :in-theory (enable clrp-list))))

(defthmd clrp-to-clrp-list
  (equal (clrp p r)
         (clrp-list (list p) r))
  :hints (("goal" :in-theory (enable open-clrp-list))))

; we could define a record clr function (just calls S with a value of
; nil .. some versions of the records/maps stuff have this)


;replace SP-EQUAL-REWRITE with this?
;bzo should we rewrite (equal v (clrp path r)) ?
(defthmd sp-equal-rewrite-2
  (equal (equal (sp path v r) r2)
         (and (equal v (gp path r2))
              (equal (clrp path r)
                     (clrp path r2))))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

;or we could combine the calls to clrp into a single call to clrp-list
(defthm clrp-of-clrp
  (equal (clrp p (clrp p2 r))
         (clrp p2 (clrp p r)))
  :rule-classes ((:rewrite :loop-stopper ((p p2))))
  :hints (("Goal" :in-theory (e/d (clrp)
                                  (sp-to-clrp)))))


;which way should this go?
(defthm clrp-of-clrp-list
  (equal (clrp p (clrp-list paths r))
         (clrp-list paths (clrp p r)))
  :hints (("Goal" :in-theory (enable clrp-list))))

(defthmd clrp-list-of-clrp
  (equal (clrp-list paths (clrp p r))
         (clrp p (clrp-list paths r)))
  :hints (("Goal" :in-theory (enable clrp-list))))

(defthm clrp-of-sp-when-dominates
  (implies (dominates p p2)
           (equal (clrp p (sp p2 v r))
                  (clrp p r)))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

;Is the hyp weak enough?
(defthm clrp-list-of-sp-when-dominated-by-some
  (implies (dominated-by-some p paths)
           (equal (clrp-list paths (sp p v r))
                  (clrp-list paths r)))
 :hints (("Goal" :in-theory (enable clrp-list))))

(defthm gp-of-clrp-when-diverge
  (implies (diverge p p2)
           (equal (gp p (clrp p2 r))
                  (gp p r)))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))) )

(defthm gp-of-clrp-when-dominates
  (implies (dominates p2 p)
           (equal (gp p (clrp p2 r))
                  nil))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))) )

(defthm gp-of-clrp-list-when-diverges-from-all
  (implies (diverges-from-all p paths)
           (equal (gp p (clrp-list paths r))
                  (gp p r)))
  :hints (("Goal" :in-theory (e/d (clrp-list clrp-list-of-clrp)
                                  (clrp-of-clrp-list)))))



;Greve might want this disabled?
(defthm clrp-list-of-sp-when-diverges-from-all
  (implies (diverges-from-all p paths)
           (equal (clrp-list paths (sp p v r))
                  (sp p v (clrp-list paths r))))
 :hints (("Goal" :in-theory (enable clrp-list))))

;more like this?  should we combine the cclears or reorder them?
(defthm clrp-list-of-clrp-combine
  (equal (clrp-list paths (clrp p r))
         (clrp-list (append paths (list p)) r))
  :hints (("Goal" :in-theory (enable clrp-list))))


;; ;; what is this stuff for
;; (defun failed-location (key)
;;   (declare (ignore key))
;;   nil)

;; (defun tag-location (key bool)
;;   (implies (not bool)
;;            (failed-location key)))

;; (defthm tag-location-reduction
;;   (implies bool
;;            (tag-location key bool)))


;is the order of  (append paths (list p)) okay?
(defthm clrp-list-equal-clrp-list-rewrite
  (implies (diverges-from-all p paths)
           (equal (equal (clrp-list paths (sp p v r1))
                         (clrp-list paths r2))
                  (and (tag-location p (equal v (gp p r2)))
                       (equal (clrp-list (append paths (list p)) r1)
                              (clrp-list (append paths (list p)) r2))))))

(defthmd sp==r
  (equal (equal (sp path v r) r2)
         (and (tag-location path (equal v (gp path r2)))
              (equal (clrp-list (list path) r)
                     (clrp-list (list path) r2))))
  :hints (("Goal" :in-theory (enable open-clrp-list))))

(defthm gp-of-clrp-when-not-gp
  (implies (not (gp p r))
           (equal (gp p (clrp p2 r))
                  nil))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

(defthm gp-of-clrp-list-when-dominated-by-some
  (implies (dominated-by-some p paths)
           (equal (gp p (clrp-list paths r))
                  nil))
  :hints (("Goal" :in-theory (e/d (clrp-list  clrp-list-of-clrp) ( clrp-of-clrp-list)))) )


(defthm path-syntax-ev-of-make-conjunction
  (iff (path-syntax-ev (bag::make-conjunction term1 term2) alist)
       (and (path-syntax-ev term1 alist)
            (path-syntax-ev term2 alist)))
  :hints (("Goal" :in-theory (enable bag::make-conjunction))))


;lifting this lemma up to be about the new evaluator...
(defthm show-unique-memberps-from-type-alist-works-right-for-paths
  (implies (and (path-syntax-ev
                 (bag::hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg) bag::a)
                (bag::hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg))
           (bag::unique-memberps (path-syntax-ev v  bag::a)
                                 (path-syntax-ev b  bag::a)
                                 (path-syntax-ev bag bag::a)))
  :otf-flg t
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use (:functional-instance (:instance bag::show-unique-memberps-from-type-alist-works-right
                                                        (bag::a bag::a)
                                                        (bag::v v)
                                                        (bag::b b)
                                                        (bag::bag bag)
                                                        (bag::n n)
                                                        (bag::type-alist type-alist)
                                                        (bag::whole-type-alist whole-type-alist)
                                                        (bag::flg flg)
                                                        )
                                             (bag::syntax-ev path-syntax-ev)
                                             (bag::syntax-ev-list path-syntax-ev-list))
           :in-theory (enable path-syntax-ev-constraint-0))))

;lifting this lemma up to be about the new evaluator...

(defthm show-unique-subbagps-from-type-alist-works-right-for-paths
  (implies (and (path-syntax-ev (bag::hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg) bag::a)
                (bag::hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
                (equal v (path-syntax-ev x bag::a))
                (equal w (path-syntax-ev y bag::a)))
           (bag::unique-subbagps v
                                 w
                                 (path-syntax-ev bag bag::a)))
  :otf-flg t
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use (:functional-instance (:instance bag::show-unique-subbagps-from-type-alist-works-right
                                                        (bag::x x)
                                                        (bag::y y)
                                                        (bag::bag bag)
                                                        (bag::n n)
                                                        (bag::w w)
                                                        (bag::v v)
                                                        (bag::type-alist type-alist)
                                                        (bag::whole-type-alist whole-type-alist)
                                                        (bag::flg flg)
                                                        (bag::a bag::a))
                                             (bag::syntax-ev path-syntax-ev)
                                             (bag::syntax-ev-list path-syntax-ev-list)))))

;lifting this lemma up to be about the new evaluator...
(defthm show-memberp-from-type-alist-works-right-for-paths
  (implies (and (path-syntax-ev (bag::hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg) bag::a)
                (bag::hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
                )
           (list::memberp (path-syntax-ev x bag::a)
                         (path-syntax-ev y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use (:functional-instance (:instance bag::show-memberp-from-type-alist-works-right
                                                        (bag::x x)
                                                        (bag::y y)
                                                        (bag::n n)
                                                        (bag::type-alist type-alist)
                                                        (bag::whole-type-alist whole-type-alist)
                                                        (bag::flg flg)
                                                        (bag::a bag::a))
                                             (bag::syntax-ev path-syntax-ev)
                                             (bag::syntax-ev-list path-syntax-ev-list)))))

;lifting this lemma up to be about the new evaluator...
(defthm show-subbagp-from-type-alist-works-right-for-paths
  (implies (and (path-syntax-ev (bag::hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg) bag::a)
                (bag::hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
                )
           (bag::subbagp (path-syntax-ev x bag::a)
                         (path-syntax-ev y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use (:functional-instance (:instance bag::show-subbagp-from-type-alist-works-right
                                                        (bag::x x)
                                                        (bag::y y)
                                                        (bag::n n)
                                                        (bag::type-alist type-alist)
                                                        (bag::whole-type-alist whole-type-alist)
                                                        (bag::flg flg)
                                                        (bag::a bag::a))
                                             (bag::syntax-ev path-syntax-ev)
                                             (bag::syntax-ev-list path-syntax-ev-list)))))

(defthm show-diverge-from-type-alist-iff-hyp-for-show-diverge-from-type-alist
  (iff (show-diverge-from-type-alist a b n type-alist whole-type-alist)
       (hyp-for-show-diverge-from-type-alist a b n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-diverge-from-type-alist
                                     hyp-for-show-diverge-from-type-alist
                                     ))))


(defthm show-diverge-from-type-alist-works-right
  (implies (and (path-syntax-ev (hyp-for-show-diverge-from-type-alist a b n type-alist whole-type-alist) bag::a)
                (hyp-for-show-diverge-from-type-alist a b n type-alist whole-type-alist))
           (diverge (path-syntax-ev a bag::a)
                    (path-syntax-ev b bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-diverge-from-type-alist
                            )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-diverge-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-diverge-from-type-alist a x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable hyp-for-show-diverge-from-type-alist))))

(local (in-theory (enable bag::unsigned-byte-p-from-bounds)))

(defun show-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'diverge (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (if (and (show-diverge-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
                 )
            ''t
          term))
    term))

(defun hyp-for-show-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'diverge (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (bag::bind-extra-vars-in-hyp (hyp-for-show-diverge-from-type-alist-fn
                                      nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))

(defthm meta-rule-to-show-diverge
  (implies (path-syntax-ev (hyp-for-show-diverge-from-mfc term mfc state) bag::a)
           (equal (path-syntax-ev term bag::a)
                  (path-syntax-ev (show-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable hyp-for-show-diverge-from-type-alist-irrelevant)
           :do-not '(generalize eliminate-destructors))))


(defthm show-all-diverge-from-type-alist-iff-hyp-for-show-all-diverge-from-type-alist
  (iff (show-all-diverge-from-type-alist x n type-alist whole-type-alist)
       (hyp-for-show-all-diverge-from-type-alist x n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-all-diverge-from-type-alist
                                     hyp-for-show-all-diverge-from-type-alist
                                     ))))



(defthm show-all-diverge-from-type-alist-works-right
  (implies (and (path-syntax-ev (hyp-for-show-all-diverge-from-type-alist x n type-alist whole-type-alist) bag::a)
                (hyp-for-show-all-diverge-from-type-alist x n type-alist whole-type-alist))
           (all-diverge (path-syntax-ev x bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-all-diverge-from-type-alist
                            )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-all-diverge-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-all-diverge-from-type-alist x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable hyp-for-show-all-diverge-from-type-alist))))



(defun show-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'all-diverge (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (if (show-all-diverge-from-type-alist-fn nil (cadr term) len type-alist type-alist)
            ''t
          term))
    term))

(defun hyp-for-show-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'all-diverge (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (bag::bind-extra-vars-in-hyp (hyp-for-show-all-diverge-from-type-alist-fn nil (cadr term) len type-alist type-alist) term))
    ''nil))


(defthm meta-rule-to-show-all-diverge
  (implies (path-syntax-ev (hyp-for-show-all-diverge-from-mfc term mfc state) bag::a)
           (equal (path-syntax-ev term bag::a)
                  (path-syntax-ev (show-all-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (all-diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable hyp-for-show-all-diverge-from-type-alist-irrelevant
                              )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defun make-syntactic-nil (x)
  (declare (ignore x))
  ''nil)

(defun meta-twins-p (term)
  (cond
   ((and (syn::funcall 'cons 2 term)
         (syn::funcall 'cons 2 (syn::arg 2 term)))
    (or (equal (syn::arg 1 term)
               (syn::arg 1 (syn::arg 2 term)))
        (meta-twins-p (syn::arg 2 term))))
   (t
    nil)))

(defun meta-all-diverge-on-twins-p (term)
  (if (syn::funcall 'all-diverge 1 term)
      (let ((plist (syn::arg 1 term)))
        (if (meta-twins-p plist)
            ''t
          ''nil))
    ''nil))

(defthm meta-not-all-diverge-if-twins
  (implies (meta-twins-ev (meta-all-diverge-on-twins-p term) alist)
           (equal (meta-twins-ev term alist)
                  (meta-twins-ev (make-syntactic-nil term) alist)))
  :rule-classes ((:meta :trigger-fns (all-diverge)))
  :hints (("Goal'4'" :in-theory (enable SYN::open-NTH) :induct (meta-twins-p term3))
          ("Subgoal *1/1''" :in-theory (enable all-diverge))))


(defthm show-all-diverge-from-all-from-type-alist-iff-hyp-for-show-all-diverge-from-all-from-type-alist
  (iff (show-all-diverge-from-all-from-type-alist x y n type-alist whole-type-alist)
       (hyp-for-show-all-diverge-from-all-from-type-alist x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-all-diverge-from-all-from-type-alist
                                     hyp-for-show-all-diverge-from-all-from-type-alist))))

(defthm show-all-diverge-from-all-from-type-alist-works-right
  (implies (and (path-syntax-ev (hyp-for-show-all-diverge-from-all-from-type-alist x y n type-alist whole-type-alist) bag::a)
                (hyp-for-show-all-diverge-from-all-from-type-alist x y n type-alist whole-type-alist))
           (all-diverge-from-all (path-syntax-ev x bag::a)
                                 (path-syntax-ev y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-all-diverge-from-all-from-type-alist
                            )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-all-diverge-from-all-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-all-diverge-from-all-from-type-alist x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable hyp-for-show-all-diverge-from-all-from-type-alist))))



(defun show-all-diverge-from-all-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'all-diverge-from-all (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (if (show-all-diverge-from-all-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
            ''t
          term))
    term))

(defun hyp-for-show-all-diverge-from-all-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (consp (cdr term))
           (equal 'all-diverge-from-all (car term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist))))
        (bag::bind-extra-vars-in-hyp
         (hyp-for-show-all-diverge-from-all-from-type-alist-fn
          nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))


(defthm meta-rule-to-show-all-diverge-from-all
  (implies (path-syntax-ev (hyp-for-show-all-diverge-from-all-from-mfc term mfc state) bag::a)
           (equal (path-syntax-ev term bag::a)
                  (path-syntax-ev (show-all-diverge-from-all-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (all-diverge-from-all)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       hyp-for-show-all-diverge-from-all-from-type-alist-irrelevant
                       )
           :do-not '(generalize eliminate-destructors))))


;; (defun syntax-dominates (x y)

(defthm clrp-list-of-mp-when-all-diverge-from-all
  (implies (all-diverge-from-all paths (keys alist))
           (equal (clrp-list paths (mp alist r1 r2))
                  (mp alist r1 (clrp-list paths r2)))))


(defthm consp-of-keys
  (equal (consp (keys alist))
         (consp alist)))

(defthm consp-of-vals
  (equal (consp (vals alist))
         (consp alist)))

(defthm keys-of-cdr
  (equal (keys (cdr alist))
         (cdr (keys alist))))

(defthmd cdr-of-keys
  (equal (cdr (keys alist))
         (keys (cdr alist))))

(in-theory (disable keys))

(defthm mp-commutative-2-when-all-dominated-by-some
  (implies (all-dominated-by-some (keys a32)
                                  (keys a31))
           (equal (mp a31 r1 (mp a32 r2 r3))
                  (mp a31 r1 r3)))
  :hints (("Goal" :induct (len a32)
           :in-theory (e/d ((:induction len)
                            )
                           (keys
                            sp-of-mp-of-remove-pairs-dominated-by
                            my-compose-alists mp-of-sp))
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable CLRP-OF-CLRP-LIST))

(defthm car-of-keys
  (equal (car (keys alist))
         (caar alist))
  :hints (("Goal" :in-theory (e/d (keys) (keys-of-cdr)))))

(defthm clrp-of-clrp-same
  (equal (clrp p (clrp p r))
         (clrp p r))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

;(clrp p (sp p v r))

(defthm clrp-of-sp
  (equal (clrp p1 (sp p2 v2 r))
         (if (dominates p1 p2)
             (clrp p1 r)
           (if (diverge p1 p2)
               (sp p2 v2 (clrp p1 r))
             (sp p2 (clrp (nthcdr (len p2) p1) v2)
                 r))))
  :hints (("Goal" :in-theory (e/d (clrp
;; jcd trying backchain limit dominates-when-not-diverge-and-not-dominates

                                   ) (sp-to-clrp))
           :do-not '(generalize eliminate-destructors))))

;hung on equal.
(defthmd equal-from-equal-of-clrps-and-equal-of-gps
  (implies (and (equal (clrp p r1) (clrp p r2))
                (equal (gp p r1) (gp p r2)))
           (equal (equal r1 r2)
                  t))
  :hints (("Goal" :use (:instance  sp-equal-rewrite-2 (r r1) (path p) (v (gp p r1)))
           :in-theory (e/d (clrp) (sp-to-clrp)))))


(defthm clrp-of-clrp-when-dominates-one
  (implies (dominates p1 p2)
           (equal (CLRP P1 (CLRP p2 r))
                  (CLRP p1 r)))
  :hints (("Goal"            :in-theory (e/d (clrp) (sp-to-clrp)))))

(defthm clrp-of-clrp-when-dominates-two
  (implies (dominates p2 p1)
           (equal (CLRP P1 (CLRP p2 r))
                  (CLRP p2 r)))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

(defthm equal-of-clrps-when-equal-of-clrps-and-dominates
  (implies (and (equal (clrp p r1) ; p is a free var
                       (clrp p r2))
                (dominates p2 p))
           (equal (equal (clrp p2 r1) (clrp p2 r2))
                  t))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

;this is kind of gross.
(defthm clrp-of-duplicate-inside-mp
  (equal (clrp p (mp alist r1 r2))
         (clrp p (mp alist r1 (clrp p r2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable equal-from-equal-of-clrps-and-equal-of-gps)
           :do-not '(generalize eliminate-destructors))))

(defthm mp-of-clrp-when-dominated-by-some
  (implies (dominated-by-some p (keys alist))
           (equal (mp alist r1 (clrp p r2))
                  (mp alist r1 r2)))
  :hints (("subgoal *1/2" :use ((:instance  clrp-of-duplicate-inside-mp (p (CAAR ALIST)) (alist (CDR ALIST)) (r2 (CLRP P R2)))
                                (:instance  clrp-of-duplicate-inside-mp (p (CAAR ALIST)) (alist (CDR ALIST)) (r2 R2))))
          ("Goal" :in-theory (enable dominated-by-some)
           :induct t

           :do-not '(generalize eliminate-destructors))))


;rule for clrp does nothing?
;also one for sp does nothing?
;prove for clrp all the thms for sp (just imagien putting in nil for v)


(defthm gp-of-clrp
  (equal (gp p1 (clrp p2 r))
         (if (diverge p1 p2)
             (gp p1 r)
             (if (dominates p2 p1)
                 nil
                 (clrp (nthcdr (len p1) p2) (gp p1 r)))))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

(defthm clrp-does-nothing-rewrite
  (equal (equal (clrp p r) r)
         (equal (gp p r)
                nil))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))

(defun make-alist-with-all-nil-vals (keys)
  (if (endp keys)
      nil
    (cons (cons (car keys) nil)
          (make-alist-with-all-nil-vals (cdr keys)))))

;Strange, the RHS uses path as an alist (whoe vals are all nil)
(defthmd clrp-list-in-terms-of-mp
  (equal (clrp-list paths r)
         (mp (make-alist-with-all-nil-vals paths) nil r))
  :hints (("Goal" :in-theory (enable clrp-list)
           :do-not '(generalize eliminate-destructors)) ))

(defthm keys-of-make-alist-with-all-nil-vals
  (equal (keys (make-alist-with-all-nil-vals paths))
         (list::fix paths))
  :hints (("Goal" :in-theory (e/d (keys) (KEYS-OF-CDR)))))



(defthm clrp-list-of-mp-when-all-dominated-by-some
  (implies (all-dominated-by-some (keys alist) paths)
           (equal (clrp-list paths (mp alist r1 r2))
                  (clrp-list paths r2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable  clrp-list-in-terms-of-mp))))

;; ;make a gp-list function!
;; ;prove clrp-list of mp lemmas
;; ;

;; ;clrp of mp lemma?  call remove-dominated-pairs?

;; ;change the notion of no-submissives?

;; ;mp from nil becomes clrp-list?

;; ;handle other cases!
;; (thm
;;  (implies (all-diverge-from-all paths (keys alist))
;;           (equal (clrp-list paths (mp alist r1 r2))
;;                  (mp alist r1 (clrp-list paths r2)))))


;; for each key in alist
;; if it diverges with all in paths, move it outside
;; if it is dominated by something in paths, drop it
;; otherwise, it (strictly) dominates one or more things in paths


;; :pl (mp alist r0 (mp alist r1 r2))


;; could this improve:

;; (defthm mp-commutative-2
;;   (implies (all-diverge-from-all (keys a31)
;;                                  (keys a32))
;;            (equal (mp a31 r1 (mp a32 r2 r3))
;;                   (mp a32 r2 (mp a31 r1 r3))))
;;   :hints
;;   (("Goal" :in-theory
;;     (e/d (mp)
;;          (sp-of-mp-of-remove-pairs-dominated-by
;;           my-compose-alists mp-of-sp))
;;     :do-not
;;     '(generalize eliminate-destructors))))


;; for each key in a32:
;; if it diverges with all keys in a31 move it outside
;; if it is dominated by a key of a31 drop it
;; otherwise, it (strictly) dominates one or more keys of a31..

;; we could decide that either all-diverge-from-all or all-dominated-by-some,
;; but perhaps it should be on a per-key basis

(in-theory (disable mp)) ;move up?

(defund pair-with-selves (list)
  (if (endp list)
      nil
    (cons (cons (car list) (car list))
          (pair-with-selves (cdr list)))))

;; jcd - we have a congruence rule, getting rid of this.
;; (defthm diverge-of-list-fix-one
;;   (equal (diverge (list::fix x) y)
;;          (diverge x y))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - we have a congruence rule, getting rid of this
;; (defthm diverge-of-list-fix-two
;;   (equal (diverge x (list::fix y))
;;          (diverge x y))
;;   :hints (("Goal" :in-theory (enable diverge))))




;do we need this?
(defthm min-of-if
  (equal (min (if test x y) z)
         (if test (min x z)
           (min y z))))

(in-theory (disable all-diverge-of-cons)) ;this is analogous to how we disabled many of the basic theorems about bags

;characterize effect-on-spot of pair-with-selves

;These should be disabled!
(in-theory (disable bag::NOT-SUBBAGP-OF-CONS-FROM-NOT-SUBBAGP
                    bag::SUBBAGP-OF-CONS
                    DOMINATES-FROM-equiv-hack
                    UNIQUE-MEMBERPS-OF-CONS))

;; (defun number-of-divergers (p paths)
;;   (if (endp paths)

(defthm effect-on-spot-of-pair-with-selves-of-cons-diverges
  (implies (diverge p p2)
           (equal (effect-on-spot p (pair-with-selves (cons p2 x)))
                  (effect-on-spot p (pair-with-selves x))))
  :hints (("Goal" :expand ( (effect-on-spot p
                                                  (cons (cons p2 p2)
                                                        (pair-with-selves x)))
                            (pair-with-selves (cons p2 x))))))

(defthm effect-on-spot-of-pair-with-selves-of-cons-equal
  (equal (effect-on-spot p (pair-with-selves (cons p x)))
         (cons (cons nil (list::fix p))
               (effect-on-spot p (pair-with-selves x))))
  :hints (("Goal" :expand ( (effect-on-spot p
                                                  (cons (cons p p)
                                                        (pair-with-selves x)))
                            (pair-with-selves (cons p x))))))


;Mention of nthcdr here is ill-advised?
(defthm effect-on-spot-of-pair-with-selves-of-cons-dominates
  (implies (dominates p p2)
           (equal (effect-on-spot p (pair-with-selves (cons p2 x)))
                  (cons (cons (nthcdr (len p) (list::fix p2))
                              (list::fix p2))
                        (effect-on-spot p (pair-with-selves x)))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable strictly-dominates)
           :expand ( (effect-on-spot p
                                     (cons (cons p2 p2)
                                           (pair-with-selves x)))
                     (pair-with-selves (cons p2 x))))))



(defthm mp-of-cons-of-cons-of-nil
  (equal (mp (cons (cons nil p) anything) st st2)
         (gp p st))
  :hints (("Goal" :in-theory (enable mp))))

(defthm effect-on-spot-of-cons-of-cons-diverge
  (implies (diverge p p2)
           (equal (effect-on-spot p (cons (cons p2 v) rest))
                  (effect-on-spot p rest)))
  :hints (("Goal" :expand ((effect-on-spot p (cons (cons p2 v) rest))))))

(defthm effect-on-spot-of-cons-of-cons-dominates
  (implies (dominates p p2)
           (equal (effect-on-spot p (cons (cons p2 v) x))
                  (cons (cons (nthcdr (len p) (list::fix p2))
                              (list::fix v))
                        (effect-on-spot p x))))
  :hints (("Goal"
           :in-theory (enable strictly-dominates)
           :expand (  (effect-on-spot p (cons (cons p2 v) x))))))

(defthm effect-on-spot-of-cons-of-cons-equal
  (equal (effect-on-spot p (cons (cons p v) rest))
         (cons (cons nil (list::fix v))
               (effect-on-spot p rest)))
  :hints (("Goal" :expand ( (effect-on-spot p (cons (cons p v) rest))))))

(in-theory (enable PAIR-WITH-SELVES)) ;remove this enable eventually?

(defthm clrp-of-mp-when-diverges-from-all
  (implies (diverges-from-all p (keys alist))
           (equal (CLRP p (MP alist r1 r2))
                  (MP alist r1 (clrp p r2))))
  :hints (("Goal" :in-theory (e/d (clrp) (SP-TO-CLRP)))))

(defthm mp-of-cons-of-cons-same
  (equal (MP (cons pair (cons pair rest)) r1 r2)
         (MP (cons pair rest) r1 r2))
  :hints (("Goal" :expand  (MP (cons pair (cons pair rest)) r1 r2))))

;generalize to dominates?

(defthm clrp-of-mp-of-cons-same
  (equal (CLRP P (MP (cons (CONS P V) rest) r1 r2))
         (CLRP P (MP rest r1 r2)))
  :hints (("Goal" :expand ( (MP (cons (CONS P V) rest) r1 r2)))))


;introduces another call to mp; okay?
(defthm clrp-of-mp-of-cons-of-cons-when-diverges
  (implies (diverge p p2)
           (equal (clrp p (mp (cons (cons p2 v) rest) r1 r2))
                  (mp (cons (cons p2 v) nil) r1 (clrp p  (mp rest r1 r2)))))
 :hints (("Goal" :expand ( (mp (cons (cons p2 v) rest) r1 r2)))))

(defthm mp-collect
  (equal (MP alist1 r1 (MP alist2 r1 r2))
         (MP (append alist1 alist2) r1 r2))
  :hints (("Goal" :in-theory (enable mp))))

(in-theory (disable MP-OF-APPEND))

(defthm mp-of-sp-when-diverges-from-all
  (implies (diverges-from-all p (vals alist))
           (equal (mp alist (sp p v r1) r2)
                  (mp alist r1 r2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable mp diverges-from-all vals))))

(defthm mp-of-mp-of-cons
  (implies (diverges-from-all p (vals alist))
           (equal (mp alist (mp (cons (cons p v) rest) r1 r2) r3)
                  (mp alist (mp rest r1 r2) r3)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable mp diverges-from-all vals))))


(in-theory (disable DIVERGES-FROM-ALL-OF-CONS
                    STRICTLY-DOMINATED-BY-SOME))

;is this okay?
(defthm mp-of-singleton
  (equal (MP (cons (cons p v) nil) r1 r2)
         (sp p (gp v r1) r2)))

;rule for mp-does-nothing?


(defthm show-not-equal-from-type-alist-path-version-iff-hyp-for-show-not-equal-from-type-alist-path-version
  (iff (show-not-equal-from-type-alist-path-version x y n type-alist whole-type-alist)
       (hyp-for-show-not-equal-from-type-alist-path-version x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-not-equal-from-type-alist-path-version
                                     hyp-for-show-not-equal-from-type-alist-path-version
                                     ))))

;prove that all-diverge implies unique

(defthmd not-equal-from-all-diverge-and-unique-memberps
  (IMPLIES (AND (ALL-DIVERGE bag)
                (bag::unique-memberps a b bag))
           (NOT (EQUAL a b)))
  :hints (("Goal" :in-theory (enable ALL-DIVERGE bag::UNIQUE-MEMBERPS))))

(defthm show-not-equal-from-type-alist-path-version-works-right
  (implies (and (path-syntax-ev (hyp-for-show-not-equal-from-type-alist-path-version x y n type-alist whole-type-alist) bag::a)
                (hyp-for-show-not-equal-from-type-alist-path-version x y n type-alist whole-type-alist)
                )
           (not (equal (path-syntax-ev x bag::a)
                       (path-syntax-ev y bag::a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( bag::not-equal-when-unique-and-unique-memberps
                             hyp-for-show-not-equal-from-type-alist-path-version
                             bag::not-equal-from-member-of-disjoint-facts
                             bag::not-equal-from-member-of-disjoint-facts-alt
                             not-equal-from-all-diverge-and-unique-memberps
                             )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-not-equal-from-type-alist-path-version
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-not-equal-from-type-alist-path-version x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-NOT-EQUAL-FROM-TYPE-ALIST-PATH-VERSION))))

(defun show-not-equal-from-mfc-path-version (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal (car term) 'equal) ;should always succeed
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (bag::usb16-fix (len type-alist)))
                  )
             (show-not-equal-from-type-alist-path-version-fn nil (cadr term) (caddr term) len type-alist type-alist))
           (equal (cdddr term) nil))
      ''nil
    term))

(defun hyp-for-show-not-equal-from-mfc-path-version (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (equal (cdddr term) nil))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (bag::usb16-fix (len type-alist)))
             )
        (bag::bind-extra-vars-in-hyp
          (hyp-for-show-not-equal-from-type-alist-path-version-fn
           nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))


;This rule is hung on equal; is it expensive?  I've tried to write my
;metafunctions efficiently.  If this rule proves too expensive, we
;could introduce a new function, neq, for inequality.  But that seems
;unfortunate...

(defthm meta-rule-to-show-not-equal
  (implies (path-syntax-ev (hyp-for-show-not-equal-from-mfc-path-version term mfc state) bag::a)
           (equal (path-syntax-ev term bag::a)
                  (path-syntax-ev (show-not-equal-from-mfc-path-version term mfc state) bag::a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (equal)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       hyp-for-show-not-equal-from-type-alist-path-version-irrelevant
                       ))))

;;
;; (in-theory (path-representation-theory))
;;

(defthm acl2-count-gp-decreasing
  (<= (acl2-count (gp p r))
      (acl2-count r))
  :hints (("goal" :induct (gp p r)
           :in-theory (e/d (gp) (g-to-gp))))
  :rule-classes (:rewrite :linear))


;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Path permutations
;;
;; We define a unique congruence to limit its application
;; to paths.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun pperm (x y)
  (bag::perm x y))

(defthm pperm-cons
  (pperm (cons a (cons b c))
         (cons b (cons a c)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthmd clrp-list-membership-rewrite
 (implies
  (list::memberp a list)
  (equal (clrp-list list r)
         (clrp a (clrp-list (bag::remove-1 a list) r))))
 :hints (("goal" :in-theory (e/d (list::memberp bag::remove-1 clrp-list)
                                 (clrp-to-clrp-list)))))

(defthmd perm-clp-list
  (implies (bag::perm plist plist-equiv)
           (iff (equal (clrp-list plist r)
                       (clrp-list plist-equiv r)) t))
  :hints (("goal" :in-theory (e/d (clrp-list-membership-rewrite
                                   list::memberp bag::perm clrp-list)
                                  (clrp-to-clrp-list)))))

(in-theory (disable pperm))

(defun <<= (a b)
  (declare (type t a b))
  (or (acl2::<< a b)
      (equal a b)))

(defun psorted-rec (a list)
  (declare (type t list))
  (if (consp list)
      (and (<<= a (car list))
           (psorted-rec (car list) (cdr list)))
    t))

(defun psorted (list)
  (declare (type t list))
  (if (consp list)
      (psorted-rec (car list) (cdr list))
    t))

(defun pinsert (a list)
  (declare (type t list))
  (if (consp list)
      (if (acl2::<< a (car list))
          (cons a list)
        (cons (car list) (pinsert a (cdr list))))
    (list a)))

(defthmd perm-pinsert-1
  (bag::perm (cons a list)
             (pinsert a list))
  :hints (("goal" :induct (pinsert a list))))

(defthmd perm-pinsert
  (bag::perm (pinsert a list)
             (cons a list))
  :hints (("goal" :in-theory (enable perm-pinsert-1))))

(defun psort-rec (list1 list2)
  (declare (type t list1 list2))
  (if (consp list1)
      (let ((list2 (pinsert (car list1) list2)))
        (psort-rec (cdr list1) list2))
    list2))

(defthmd perm-psort-rec
  (bag::perm (psort-rec a list)
             (append a list))
  :hints (("goal" :induct (psort-rec a list)
           :in-theory (enable append perm-pinsert))))

(defun psort (list)
  (declare (type t list))
  (psort-rec list nil))

(defthm pperm-psort
  (pperm (psort list) list)
  :hints (("goal" :in-theory (enable perm-psort-rec pperm))))

(defthm psort-clrp-list
  (implies
   (syntaxp (and (quotep list)
                 (not (psorted (cadr list)))))
   (equal (clrp-list list r)
          (clrp-list (psort list) r)))
  :hints (("goal" :in-theory (enable perm-psort-rec))))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; WFR and paths ..
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun wfpath (path)
  (declare (type t path))
  (and (consp path)
       (wfkey (car path))
       (if (consp (cdr path))
           (wfpath (cdr path))
         t)))

(defun wfpath-rec (path)
  (declare (type t path))
  (if (consp path)
      (wfpath path)
    t))

(defthmd open-wfpath
  (implies
   (consp path)
   (equal (wfpath path)
          (and (wfkey (car path))
               (wfpath-rec (cdr path))))))

(defthmd wfpath-nil
  (implies
   (not (consp path))
   (equal (wfpath path) nil)))

(defthmd open-wfpath-rec
  (implies
   (consp path)
   (equal (wfpath-rec path)
          (and (wfkey (car path))
               (wfpath-rec (cdr path))))))

(defthmd wfpath-rec-nil
  (implies
   (not (consp path))
   (equal (wfpath-rec path) t)))

(in-theory
 (e/d
  (open-wfpath-rec wfpath-rec-nil)
  (wfpath-rec)
  ))

(in-theory
 (e/d
  (open-wfpath wfpath-nil)
  (wfpath)
  ))

(defthm wfr-sp
  (implies
   (and (wfpath path)
        (wfr r))
   (wfr (sp path v r)))
  :hints (("goal" :in-theory (e/d (sp) (s-to-sp))
           :induct (sp path v r))))

(defthm non-nil-if-gp-non-nil
  (implies
   (gp p r) r)
  :rule-classes (:forward-chaining))

(defthm acl2-count-gp-decreases
  (implies
   (and
    (wfr r)
    (wfpath path)
    (gp path r))
   (< (acl2-count (gp path r))
      (acl2-count r)))
  :hints (("goal" :in-theory (e/d (gp) (g-to-gp))
           :induct (gp path r)))
  :rule-classes (:rewrite :linear))


;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Existential reasoning with paths
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

;bzo swithing these to use acl2::clr instead of cpath::clr
(defthmd atom-record-reduction
  (implies
   (syntaxp (and (symbolp r1)
                 (symbolp r2)))
   (iff (equal r1 r2)
        (and (equal (g a r1) (g a r2))
             (equal (acl2::clr a r1) (acl2::clr a r2)))))
  :hints (("goal" :in-theory (e/d () (s-to-sp g-to-gp)))))

(defthmd atom-record-reduction-binding-1
  (implies
   (equal (g a r1) (g a r2))
   (iff (equal (acl2::clr a r1) (acl2::clr a r2))
        (equal r1 r2)))
  :hints (("goal" :in-theory (enable atom-record-reduction))))

(defthmd atom-record-reduction-binding-2
  (implies
   (equal (acl2::clr a r1) (acl2::clr a r2))
   (iff (equal r1 r2)
        (equal (g a r1) (g a r2))))
  :hints (("goal" :in-theory (enable atom-record-reduction))))

(defthmd atom-record-reduction-binding-3
  (implies
   (and
    (equal (acl2::clr a r1) (acl2::clr a r2))
    (equal (g a r1) (g a r2)))
   (equal r1 r2))
  :hints (("goal" :in-theory (enable atom-record-reduction)))
  :rule-classes (:forward-chaining))

(defun gp-path-induction (list r1 r2)
  (declare (type t list r1 r2))
  (if (consp list)
      (let ((r1 (g (car list) r1))
            (r2 (g (car list) r2)))
        (gp-path-induction (cdr list) r1 r2))
    (cons r1 r2)))

(defthmd open-sp
  (implies
   (consp path)
   (equal (sp path v r)
          (S (CAR PATH) (SP (CDR PATH) V (G (CAR PATH) R)) r)))
  :hints (("goal" :in-theory (e/d (sp) (s-to-sp)))))

(defthmd path-record-reduction
  (implies
   (syntaxp (and (symbolp r1)
                 (symbolp r2)))
   (iff (equal r1 r2)
        (and (equal (gp path r1) (gp path r2))
             (equal (clrp path r1) (clrp path r2)))))
  :hints (("goal" :in-theory (e/d (open-sp ;acl2::clr
                                           clrp atom-record-reduction-binding-1 gp)
                                  (g-to-gp s-to-sp clrp-to-clrp-list SP-TO-CLRP sp==r ;acl2::S==R
                                           )))))

(defthmd path-record-reduction-binding-1
  (implies
   (equal (gp path r1) (gp path r2))
   (iff (equal (clrp path r1) (clrp path r2))
        (equal r1 r2)))
  :hints (("goal" :in-theory (enable path-record-reduction))))

(defthmd path-record-reduction-binding-2
  (implies
   (equal (clrp path r1) (clrp path r2))
   (iff (equal r1 r2)
        (equal (gp path r1) (gp path r2))))
  :hints (("goal" :in-theory (enable path-record-reduction))))

(defthmd path-record-reduction-binding-3
  (implies
   (and
    (equal (clrp path r1) (clrp path r2))
    (equal (gp path r1) (gp path r2)))
   (equal r1 r2))
  :hints (("goal" :in-theory (enable path-record-reduction)))
  :rule-classes (:forward-chaining))


(defun gp-list (list r)
  (if (consp list)
      (cons (gp (car list) r)
            (gp-list (cdr list) r))
    nil))

(defthmd gp-list-equal-sp-reduction
  (implies
   (equal (gp-list list r1)
          (gp-list list r2))
   (iff (equal (gp-list list (sp a v r1))
               (gp-list list (sp a v r2))) t)))

(defthmd gp-list-equal-clrp-reduction
  (implies
   (equal (gp-list list r1)
          (gp-list list r2))
   (iff (equal (gp-list list (clrp a r1))
               (gp-list list (clrp a r2))) t))
  :hints (("goal" :in-theory (e/d (gp-list-equal-sp-reduction clrp)
                                  (SP-TO-CLRP clrp-to-clrp-list)))))

(defun clrp-list-induction (list r1 r2)
  (declare (type t list r1 r2))
  (if (consp list)
      (let ((r1 (clrp (car list) r1))
            (r2 (clrp (car list) r2)))
        (clrp-list-induction (cdr list) r1 r2))
    (cons r1 r2)))

(defthm clrp-list-over-clrp
  (equal (clrp-list list (clrp p r))
         (clrp p (clrp-list list r)))
  :hints (("goal" :in-theory (e/d (clrp-list)
                                  (clrp-to-clrp-list)))))

(defthmd path-list-record-reduction
  (implies
   (syntaxp (and (symbolp r1)
                 (symbolp r2)))
   (iff (equal r1 r2)
        (and (equal (gp-list list r1) (gp-list list r2))
             (equal (clrp-list list r1) (clrp-list list r2)))))
  :hints (("goal" :in-theory (e/d (path-record-reduction-binding-1
                                   path-record-reduction-binding-2
                                   path-record-reduction-binding-3
                                   gp-list-equal-clrp-reduction
                                   clrp-list) (CLRP-LIST-OF-CLRP-COMBINE clrp-to-clrp-list))
           :induct (clrp-list-induction list r1 r2))))

(defthmd path-list-record-reduction-1
  (implies
   (equal (gp-list list r1) (gp-list list r2))
   (iff (equal (clrp-list list r1) (clrp-list list r2))
        (equal r1 r2)))
  :hints (("goal" :in-theory (enable path-list-record-reduction))))

(defthmd path-list-record-reduction-2
  (implies
   (equal (clrp-list list r1) (clrp-list list r2))
   (iff (equal r1 r2)
        (equal (gp-list list r1) (gp-list list r2))))
  :hints (("goal" :in-theory (enable path-list-record-reduction))))

(defthmd path-list-record-reduction-2-bool
  (implies
   (and
    (not (clrp-list list r1))
    (not (clrp-list list r2)))
   (iff (equal r1 r2)
        (equal (gp-list list r1) (gp-list list r2))))
  :hints (("goal" :use (:instance path-list-record-reduction-2))))

(defthmd path-list-record-reduction-3
  (implies
   (and
    (equal (clrp-list list r1) (clrp-list list r2))
    (equal (gp-list list r1) (gp-list list r2)))
   (equal r1 r2))
  :hints (("goal" :in-theory (enable path-list-record-reduction)))
  :rule-classes (:forward-chaining))

(in-theory
 (disable
  CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL
  GP-OF-CLRP-LIST-WHEN-DIVERGES-FROM-ALL
  ))


;; returns the common portion of two paths (if any)
(defun common-prefix (p1 p2)
  (if (or
       (not (consp p1))
       (not (consp p2)))
      nil
    (if (equal (car p1) (car p2))
        (cons (car p1) (common-prefix (cdr p1) (cdr p2)))
      nil)))

(defthm common-prefix-assoc
  (equal
   (common-prefix p1 p2)
   (common-prefix p2 p1)))

(defthm common-prefix-length
  (let ((pre (common-prefix p1 p2)))
    (and
     (<= (len pre) (len p1))
     (<= (len pre) (len p2)))))

(defthm common-prefix-subset
  (let ((pre (common-prefix p1 p2)))
    (and
     (subsetp pre p1)
     (subsetp pre p2))))

(defthm common-prefix-not-equal-subset
  (let ((pre (common-prefix p1 p2)))
    (and
     (implies
      (not (equal pre p1))
      (subsetp pre p1))
     (implies
      (not (equal pre p2))
      (subsetp pre p2)))))

(in-theory (disable (common-prefix)))

(defun common-prefix-all (paths)
  (if (not (consp paths))
      nil
    (if (not (consp (cdr paths)))
        (car paths)
      (common-prefix-all (cons (common-prefix (car paths) (cadr paths)) (cddr paths))))))

(defthm common-prefix-all-open
  (implies
   (and (consp paths) (consp (cdr paths)))
   (equal (common-prefix-all paths)
          (common-prefix-all (cons (common-prefix (car paths) (cadr paths)) (cddr paths))))))

(defun prefix-p (paths)
  (if (consp (cdr paths))
    (if (equal (car (car paths)) (car (car (cdr paths))))
        (prefix-p (cdr paths))
      nil)
    t))

#+joe
(defthm common-prefix-exists-len>0
  (implies
   (and
    (consp paths)
    (prefix-p paths))
   (< 0 (len (common-prefix-all paths)))))

(defun syn-prefix-p (paths)
  (if (syn::consp (syn::cdr paths))
    (if (equal (syn::car (syn::car paths)) (syn::car (syn::car (syn::cdr paths))))
        (syn-prefix-p (syn::cdr paths))
      nil)
    t))

; jcd - moved to lists library
;(defthm finalcdr-under-equiv
;  (list::equiv (finalcdr x) nil))

(defthm gp-of-sp-exact
  (equal (gp p (sp p v r))
         v))



;very much like the rkeys of s rule...
(defthm rkeys-of-sp-singleton
  (list::setequiv (acl2::rkeys (sp (list key) val r))
                  (if val
                      (cons key (acl2::rkeys r))
                    (list::remove key (acl2::rkeys r))))
  :hints (("Goal" :in-theory (e/d (sp) (s-to-sp)))))

(defthm clrp-list-of-singleton
  (equal (clrp-list (list p) nr)
         (clrp p nr))
  :hints (("Goal" :in-theory (enable clrp-list))))

(defthm sp==r-2
  (implies (syntaxp (not (equal v ''nil))) ;seems to help prevent loops (we probably want to rewrite to clrp in the nil case anyway)
           (equal (equal (sp path v r) r2)
                  (and (tag-location path (equal v (gp path r2)))
                       (equal (clrp-list (list path) r)
                              (clrp-list (list path) r2)))))
  :hints (("Goal" :by sp==r)))

;gen to non-singletons?
(defthm rkeys-of-clrp-singleton
  (list::setequiv (acl2::rkeys (clrp (list key) r))
                  (list::remove key (acl2::rkeys r)))
  :hints (("Goal" :in-theory (e/d (clrp) (sp-to-clrp)))))



;am i sure i want this enabled?
;maybe only if keys is itself a cons?
(defthmd clrp-of-cons
  (equal (clrp (cons key keys) r)
         (s key (clrp keys (g key r)) r))
  :hints (("Goal" :in-theory (e/d (CLRP OPEN-SP) (SP-TO-CLRP S-TO-SP
                                                             ACL2::S==R ;bzo looped
                                                             )))))

(defthm diverge-of-non-consp-one-cheap
  (implies (not (consp x))
           (equal (diverge x y) nil))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(local (in-theory (enable (:rewrite wf-syntax-prefix-implies-true-listp)
                          (:definition wf-syntax-prefix))))

;(defcong list::equiv list::equiv
;  (cons a x) 2)

(DEFTHM SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST
     BAG::X
     BAG::Y BAG::BAG BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST
                     BAG::X
                     BAG::Y BAG::BAG BAG::N BAG::TYPE-ALIST
                     BAG::WHOLE-TYPE-ALIST BAG::FLG)
                    BAG::A))
   (BAG::UNIQUE-SUBBAGPS (PD-EVAL BAG::X BAG::A) (PD-EVAL BAG::Y BAG::A) (PD-EVAL BAG::BAG BAG::A)))
  :HINTS
  (("Goal" :use (:functional-instance (:instance bag::SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-WORKS-RIGHT
                                                 (bag::v (PD-EVAL BAG::X BAG::A))
                                                 (w (PD-EVAL BAG::Y BAG::A)))
                                      (bag::syntax-ev pd-eval)
                                      (bag::syntax-ev-list pd-eval-list))
    :in-theory (enable pd-eval-constraint-0)))
  :RULE-CLASSES (:REWRITE :FORWARD-CHAINING))

(DEFTHM SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST
     BAG::V
     BAG::X BAG::BAG BAG::N BAG::TYPE-ALIST
     W BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST
                     BAG::V
                     BAG::X BAG::BAG BAG::N BAG::TYPE-ALIST
                     W BAG::WHOLE-TYPE-ALIST BAG::FLG)
                    BAG::A)
    )
   (BAG::UNIQUE-MEMBERP-AND-SUBBAGP
    (PD-EVAL BAG::V BAG::A)
    (PD-EVAL BAG::X BAG::A)
    (PD-EVAL BAG::BAG BAG::A)))
  :HINTS (("goal" :use (:functional-instance bag::SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST-WORKS-RIGHT
                                             (bag::syntax-ev pd-eval)
                                             (bag::syntax-ev-list pd-eval-list))))
  :rule-classes (:rewrite :forward-chaining))

(DEFTHM SHOW-MEMBERP-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST
     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST
                     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
                     BAG::WHOLE-TYPE-ALIST BAG::FLG)
                    BAG::A))
   (MEMBERP (PD-EVAL BAG::X BAG::A)
            (PD-EVAL BAG::Y BAG::A)))
  :HINTS (("goal" :use (:functional-instance bag::SHOW-MEMBERP-FROM-TYPE-ALIST-WORKS-RIGHT
                                             (bag::syntax-ev pd-eval)
                                             (bag::syntax-ev-list pd-eval-list))))
  :rule-classes (:rewrite :forward-chaining))


(defthm show-subbagp-from-type-alist-works-right
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST
     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST
                     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
                     BAG::WHOLE-TYPE-ALIST BAG::FLG)
                    BAG::A))
   (BAG::SUBBAGP (PD-EVAL BAG::X BAG::A)
                 (PD-EVAL BAG::Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance bag::show-subbagp-from-type-alist-works-right
                                             (bag::syntax-ev pd-eval)
                                             (bag::syntax-ev-list pd-eval-list)))))

(defthm SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
  (implies
   (BAG::SYNTAX-SUBBAGP-FN BAG::A BAG::TERM1 BAG::TERM2)
   (BAG::SUBBAGP (pd-eval BAG::TERM1 BAG::A)
                 (pd-eval BAG::TERM2 BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance bag::SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
                                             (bag::syntax-ev pd-eval)
                                             (bag::syntax-ev-list pd-eval-list)))))

(defthm sp-of-nil
  (equal (sp nil val r) val)
  :hints (("goal" :in-theory '(cpath::sp-of-non-consp))))

(defun shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (if (consp p1)
      (if (consp p2)
          (let ((v (car p1)))
            (if (equal v (car p2))
                (met ((pre p1 p2) (shared-prefix (cdr p1) (cdr p2)))
                     (mv (cons v pre) p1 p2))
              (mv nil p1 p2)))
        (mv nil p1 p2))
    (mv nil p1 p2)))

;; #|
;; (defthm not-consp-implies-identity
;;   (implies
;;    (not (consp (v0 (shared-prefix p1 p2))))
;;    (and (equal (v1 (shared-prefix p1 p2)) p1)
;;         (equal (v2 (shared-prefix p1 p2)) p2))))

;; (defun shared-prefix-1 (p1 p2)
;;   (if (and (consp p1)
;;            (consp p2)
;;            (equal (car p1) (car p2)))
;;       (shared-prefix-1 (cdr p1) (cdr p2))
;;     p1))

;; (defun shared-prefix-0 (p1 p2)
;;   (if (and (consp p1)
;;            (consp p2)
;;            (equal (car p1) (car p2)))
;;       (cons (car p1) (prefix (cdr p1) (cdr p2)))
;;     nil))

;; (defthm shared-prefix-0-commutes
;;   (list::equiv (shared-prefix-0 p1 p2)
;;                    (shared-prefix-0 p2 p1))
;;   :rule-classes ((:rewrite :loop-stopper (p2 p1))))
;; |#

(defun syntax-quote-shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (if (consp p1)
      (cond
       ((syn::consp p2)
        (let ((v (syn::car p2)))
          (if (syn::quotep v)
              (let ((v (syn::dequote v)))
                (if (equal v (car p1))
                    (met ((pre p1 p2) (syntax-quote-shared-prefix (cdr p1) (syn::cdr p2)))
                         (mv (cons v pre) p1 p2))
                  (mv nil p1 p2)))
            (mv nil p1 p2))))
       ((syn::quotep p2)
        (met ((pre p1 p2) (shared-prefix p1 (syn::dequote p2)))
             (mv pre p1 (syn::enquote p2))))
       (t (mv nil p1 p2)))
    (mv nil p1 p2)))

(defun syntax-shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (cond
   ((syn::quotep p1)
    (met ((pre p1 p2) (syntax-quote-shared-prefix (syn::dequote p1) p2))
         (mv (syn::enquote pre) (syn::enquote p1) p2)))
   ((syn::quotep p2)
    (met ((pre p2 p1) (syntax-quote-shared-prefix (syn::dequote p2) p1))
         (mv (syn::enquote pre) p1 (syn::enquote p2))))
   ((syn::consp p1)
    (if (syn::consp p2)
        (let ((v1 (syn::car p1))
              (v2 (syn::car p2)))
          (if (equal v1 v2)
              (met ((pre p1 p2) (syntax-shared-prefix (syn::cdr p1) (syn::cdr p2)))
                   (mv (syn::cons v1 pre) p1 p2))
            (mv (syn::nil) p1 p2)))
      (mv (syn::nil) p1 p2)))
   ((syn::appendp p1)
    (let ((v1 (syn::arg 1 p1)))
      (cond
       ((syn::appendp p2)
        (let ((v2 (syn::arg 1 p2)))
          (if (equal v1 v2)
              (met ((pre p1 p2) (syntax-shared-prefix (syn::arg 2 p1) (syn::arg 2 p2)))
                   (mv (syn::append v1 pre) p1 p2))
            (mv (syn::nil) p1 p2))))
       ((equal v1 p2)
        (mv v1 v1 (syn::nil)))
       (t
        (mv (syn::nil) p1 p2)))))
   ((equal p1 p2)
    (mv p1 (syn::nil) (syn::nil)))
   (t
    (mv (syn::nil) p1 p2))))

(defun bind-shared-prefix-fn (p1 p2 r0 r1 r2)
  (declare (type t p1 p2 r0 r1 r2))
  (met ((v0 v1 v2) (syntax-shared-prefix p1 p2))
       `((,r0 . ,v0)
         (,r1 . ,v1)
         (,r2 . ,v2))))

(defthmd gp-sp-append
  (equal (gp p1 (sp p2 v (gp r0 st)))
         (gp (append r0 p1) (sp (append r0 p2) v st)))
  :hints (("goal" :in-theory (e/d (append
                                   ;cpath::open-gp  ;looped
                                   gp
                                   sp)
                                  (cpath::g-to-gp)))))

;; Trigger theorem .. we use bind-shared-prefix instead
;; of triggering a meta-evaluation of shared-prefix
;; since the meta-evaluation will only ever be an
;; approximation (I don't know how we would prove the
;; theory in that case??)
;;
;; That being the case, how will we extend this to
;; lists of paths??  By triggering on gp?
;;
(defthm gp-of-sp-bind-shared-prefix
  (implies
   (and
    (bind-free (bind-shared-prefix p1 p2 r0 r1 r2) (r0 r1 r2))
    (consp r0)
    (equal p1 (append r0 r1))
    (equal p2 (append r0 r2)))
   (equal (gp p1 (sp p2 v st))
          (gp r1 (sp r2 v (gp r0 st)))))
  :hints (("goal" :in-theory `(gp-sp-append))))

(in-theory
 (enable
  pseudo-termp
  ))

;; You could strengthen this if x and y were "boolean"
;; This would require that meta functions return (syn::bool)
;; values.  That would allow you to

(defthm booleanp-conjoin
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (booleanp (pd-eval (syn::conjoin x y) a)))
   :hints (("goal" :in-theory (enable syn::conjoin))))


(defthm pd-eval-conjoin-equal
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a))
    (and x y))
   (equal (pd-eval (syn::conjoin x y) a)
          (and (pd-eval x a)
               (pd-eval y a))))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm pd-eval-conjoin-iff
  (implies
   (and x y)
   (iff (pd-eval (syn::conjoin x y) a)
        (and (pd-eval x a)
             (pd-eval y a))))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm booleanp-make-conjunction
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (booleanp (pd-eval (bag::make-conjunction x y) a)))
 :hints (("goal" :in-theory (enable bag::make-conjunction))))

(defthm pd-eval-make-conjunction-equal
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (equal (pd-eval (bag::make-conjunction x y) a)
          (and (pd-eval x a)
               (pd-eval y a))))
  :hints (("goal" :in-theory (enable bag::make-conjunction))))

(defthm pd-eval-make-conjunction-iff
  (iff (pd-eval (bag::make-conjunction x y) a)
       (and (pd-eval x a)
            (pd-eval y a)))
  :hints (("goal" :in-theory (enable bag::make-conjunction))))

(defthm type-alistp-pseudo-termp
  (implies
   (ACL2::TYPE-ALISTP TYPE-ALIST)
   (pseudo-termp (caar type-alist)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable ACL2::TYPE-ALISTP))))

(defthm pseudo-termp-hyp-for-show-diverges-from-all-from-type-alist
  (implies
   (and
    (acl2::type-alistp type-alist)
    (acl2::type-alistp whole-alist)
    (pseudo-termp x)
    (pseudo-termp list))
   (pseudo-termp (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)))
  :hints (("goal" :in-theory (enable syn::conjoin syn::open-nth))))

(defthm show-diverges-from-all-from-type-alist-to-hyp-for
  (iff (show-diverges-from-all-from-type-alist x list type-alist whole-alist)
       (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)))


(defthm diverges-from-all-from-unique-memberp-and-subbagp-all-diverge
  (implies
   (and
    (all-diverge bag)
    (bag::unique-memberp-and-subbagp x list bag))
   (diverges-from-all x list))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable diverges-from-all))))

(defthmd diverges-from-all-from-memberp-subbagp-all-diverge-from-all-1
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::memberp a x)
    (bag::subbagp list y))
   (diverges-from-all a list)))

(defthmd diverges-from-all-from-memberp-subbagp-all-diverge-from-all-2
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::memberp a y)
    (bag::subbagp list x))
   (diverges-from-all a list)))

(defthm pd-eval-hyp-for-show-diverges-from-all-from-type-alist-implies-diverges-from-all
  (implies
   (and
    (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)
    (pd-eval (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist) bag::a))
   (diverges-from-all (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (diverges-from-all-from-memberp-subbagp-all-diverge-from-all-2
                            diverges-from-all-from-memberp-subbagp-all-diverge-from-all-1
                            syn::open-nth syn::conjoin) (DIVERGES-FROM-ALL-BY-MEMBERSHIP))))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-hyp-for-show-diverges-from-all-from-quote-list
  (implies
   (and
    (acl2::type-alistp type-alist)
    (pseudo-termp x))
   (pseudo-termp (hyp-for-show-diverges-from-all-from-quote-list x list type-alist))))

(defthm show-diverges-from-all-from-quote-list-to-hyp-for
  (iff (show-diverges-from-all-from-quote-list x list type-alist)
       (hyp-for-show-diverges-from-all-from-quote-list x list type-alist)))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist-stronger
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist x y type-alist) bag::a)
    (equal yv (pd-eval y bag::a)))
   (diverge yv (pd-eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm show-diverges-from-all-from-quote-list-implies-diverges-from-all
  (implies
   (and
    (hyp-for-show-diverges-from-all-from-quote-list x list type-alist)
    (pd-eval (hyp-for-show-diverges-from-all-from-quote-list x list type-alist) bag::a))
   (diverges-from-all (pd-eval x bag::a) list))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d (syn::open-nth syn::conjoin diverges-from-all)
                                  (DIVERGES-FROM-ALL-OF-CDR ;efficiency
                                   NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
                                   )))))

(defthm iff-hyp-for-simplify-diverges-from-all-from-cons-list
  (iff (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist) t))

(defthm iff-v1-simplify-diverges-from-all-from-cons-list
  (iff (v1 (simplify-diverges-from-all-from-cons-list x list type-alist)) t))

(defthm pseudo-termp-hyp-for-simplify-diverges-from-all-from-cons-list
  (implies
   (and
    (acl2::type-alistp type-alist)
    (pseudo-termp x)
    (pseudo-termp list))
   (pseudo-termp (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist))))

#+joe
(defthm simplify-diverges-from-all-from-cons-list-to-hyp-for
  (iff (simplify-diverges-from-all-from-cons-list x list type-alist)
       (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist)))

(defthm simplify-diverges-from-all-from-cons-list-implies-diverges-from-all
  (implies
   (pd-eval (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-diverges-from-all-from-cons-list x list type-alist)) bag::a)
          (diverges-from-all (pd-eval x bag::a) (pd-eval list bag::a))))
  ;; :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (simplify-diverges-from-all-from-cons-list x list type-alist)
           :in-theory (enable syn::open-nth diverges-from-all))
          (and acl2::stable-under-simplificationp
               `(:in-theory (enable syn::conjoin)))))

(defthm pseudo-termp-hyp-for-show-all-diverge-from-all-type-alist
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp list)
    (acl2::type-alistp type-alist)
    (acl2::type-alistp full-alist)
    )
   (pseudo-termp (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist))))

(defthm iff-show-all-diverge-from-all-type-alist-hyps
  (iff (show-all-diverge-from-all-type-alist x list n type-alist full-alist)
       (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)))

(defthmd all-diverge-from-all-diverge-subbagp-1
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::subbagp a x)
    (bag::subbagp b y))
   (all-diverge-from-all a b)))

(defthmd all-diverge-from-all-diverge-subbagp-2
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::subbagp a y)
    (bag::subbagp b x))
   (all-diverge-from-all a b)))

(defthmd all-diverge-from-all-from-unique-subbagps-all-diverge
  (implies
   (and
    (all-diverge list)
    (bag::unique-subbagps x y list))
   (and (all-diverge-from-all x y)
        (all-diverge-from-all y x)))
  :rule-classes (:rewrite :forward-chaining))


(defthm show-all-diverge-from-all-type-alist-works
  (implies
   (and
    (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)
    (pd-eval (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist) bag::a))
   (all-diverge-from-all (pd-eval x bag::a) (pd-eval list bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (syn::open-nth
                            SYN::CONJOIN
                            all-diverge-from-all-from-unique-subbagps-all-diverge
                            all-diverge-from-all-diverge-subbagp-1
                            all-diverge-from-all-diverge-subbagp-2
                            )
                           (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP)))))

(defthm show-all-diverge-from-all-type-alist-works-2
  (implies
   (and
    (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)
    (pd-eval (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist) bag::a))
   (all-diverge-from-all (pd-eval list bag::a) (pd-eval x bag::a)))
  :hints (("goal" :in-theory (disable show-all-diverge-from-all-type-alist-works)
           :use show-all-diverge-from-all-type-alist-works))
  :rule-classes (:rewrite :forward-chaining))


(defthm pseudo-termp-hyp-for-simplify-all-diverge-from-all-cons-list
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp list)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist))))

(defthm iff-simplify-all-diverge-from-all-cons-list-to-hyp-for
  (and (iff (v1 (simplify-all-diverge-from-all-cons-list swap x list type-alist)) t)
       (iff (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist) t)))

;; DAG -- move me!! -- this rules belong in "path"

(defthmd all-diverge-from-all-append-1
  (equal (all-diverge-from-all (append x y) z)
         (and (all-diverge-from-all x z)
              (all-diverge-from-all y z)))
  :hints (("goal" :in-theory (enable append all-diverge-from-all))))

(defthmd all-diverge-from-all-append-2
  (equal (all-diverge-from-all z (append x y))
         (and (all-diverge-from-all z x)
              (all-diverge-from-all z y)))
  :hints (("goal" :in-theory (enable append all-diverge-from-all))))


(defthm all-diverge-from-all-commute
  (implies
   (all-diverge-from-all x y)
   (all-diverge-from-all y x))
  :rule-classes (:forward-chaining))

(defthm simplify-all-diverge-from-all-cons-list-works
  (implies
   (pd-eval (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-all-diverge-from-all-cons-list swap x list type-alist)) bag::a)
          (all-diverge-from-all (pd-eval x bag::a) (pd-eval list bag::a))))
  ;;:rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (simplify-all-diverge-from-all-cons-list swap x list type-alist)
           :in-theory (e/d (syn::open-nth
                            all-diverge-from-all-append-1
                            all-diverge-from-all-append-2)
                           (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP)))
          (and acl2::stable-under-simplificationp
               `(:in-theory (enable syn::conjoin)))))

;; end all-diverge-from-all

(DEFTHM SHOW-ALL-DIVERGE-FROM-TYPE-ALIST-WORKS-RIGHT-pd-eval
  (IMPLIES
   (AND (HYP-FOR-SHOW-ALL-DIVERGE-FROM-TYPE-ALIST
         X N TYPE-ALIST WHOLE-TYPE-ALIST)
        (PD-EVAL (HYP-FOR-SHOW-ALL-DIVERGE-FROM-TYPE-ALIST
                         X N TYPE-ALIST WHOLE-TYPE-ALIST)
                        BAG::A)
        )
   (ALL-DIVERGE (PD-EVAL X BAG::A)))
  :RULE-CLASSES (:REWRITE :FORWARD-CHAINING)
  :HINTS (("Goal" :use (:functional-instance SHOW-ALL-DIVERGE-FROM-TYPE-ALIST-WORKS-RIGHT
                                             (path-syntax-ev  pd-eval)
                                             (path-syntax-ev-list pd-eval-list))
           :in-theory (enable pd-eval-constraint-0))))


(defthm pd-eval-show-all-diverge-from-all-from-type-alist-works-right
  (IMPLIES
   (AND (PD-EVAL (HYP-FOR-SHOW-ALL-DIVERGE-FROM-ALL-FROM-TYPE-ALIST
                         X Y N TYPE-ALIST WHOLE-TYPE-ALIST)
                        BAG::A)
        (HYP-FOR-SHOW-ALL-DIVERGE-FROM-ALL-FROM-TYPE-ALIST
         X Y N TYPE-ALIST WHOLE-TYPE-ALIST))
   (ALL-DIVERGE-FROM-ALL (PD-EVAL X BAG::A)
                         (PD-EVAL Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :HINTS (("Goal" :use (:functional-instance show-all-diverge-from-all-from-type-alist-works-right
                                             (path-syntax-ev  pd-eval)
                                             (path-syntax-ev-list pd-eval-list)))))


(defthm iff-hyp-for-simplify-all-diverge-from-cons-list
  (iff (hyp-for-simplify-all-diverge-from-cons-list list type-alist) t))

(defthm iff-v1-simplify-all-diverge-from-cons-list
  (iff (v1 (simplify-all-diverge-from-cons-list list type-alist)) t))

(defthm pseudo-termp-hyp-for-simplify-all-diverge-from-cons-list
  (implies
   (and
    (pseudo-termp list)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-simplify-all-diverge-from-cons-list list type-alist))))

(defthmd all-diverge-cons
  (equal (all-diverge (cons a x))
         (and (diverges-from-all a x)
              (all-diverge x)))
  :hints (("goal" :in-theory (enable append all-diverge all-diverge-from-all))))

(defthmd all-diverge-append
  (equal (all-diverge (append x y))
         (and (all-diverge x)
              (all-diverge y)
              (all-diverge-from-all x y)))
  :hints (("goal" :in-theory (enable append all-diverge all-diverge-from-all))))

(defthm hyp-for-simplify-all-diverge-from-cons-list-works
  (implies
   (pd-eval (hyp-for-simplify-all-diverge-from-cons-list list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-all-diverge-from-cons-list list type-alist)) bag::a)
          (all-diverge (pd-eval list bag::a))))
  ;; :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (SIMPLIFY-ALL-DIVERGE-FROM-CONS-LIST-FN BAG::A LIST TYPE-ALIST)
           :in-theory (e/d (syn::open-nth)
                           (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
                            ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
                            ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP
                            ALL-DIVERGE-BY-MEMBERSHIP)))
          (and acl2::stable-under-simplificationp
               '(:in-theory (e/d (all-diverge-cons
                                  all-diverge-append
                                  syn::open-nth
                                  syn::conjoin)
                                 (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
                                  ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
                                  ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP
                                  ALL-DIVERGE-BY-MEMBERSHIP))))))

(set-state-ok t)

(defun appears-negated (term clause)
  (declare (type t term clause))
  (if (consp clause)
      (let ((fact (car clause)))
        (or (equal term fact) ;; oh, for eq!
            (appears-negated term (cdr clause))))
    nil))

(defun simplify-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge 1 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
            (clause     (acl2::mfc-clause mfc)))
        (if (or (acl2::mfc-ancestors mfc)
                (appears-negated term clause))
            (let ((bag (syn::arg 1 term)))
              (met ((simp tx) (simplify-all-diverge-from-cons-list-fn nil bag type-alist))
                (if simp tx term)))
          term))
    term))

(defun hyp-for-simplify-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge 1 term)
      (let ((bag  (syn::arg 1 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (let ((hyp (hyp-for-simplify-all-diverge-from-cons-list-fn nil bag type-alist)))
            (bag::bind-extra-vars-in-hyp hyp term))))
    (syn::nil)))

(defthm meta-rule-to-simplify-all-diverge
  (implies (pd-eval (hyp-for-simplify-all-diverge-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
                  (pd-eval (simplify-all-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (all-diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
                              syn::open-nth
                              hyp-for-simplify-all-diverge-from-cons-list-irrelevant
                              simplify-all-diverge-from-cons-list-irrelevant
                              ))))

(defun show-all-diverge-from-all-from-mfc-2 (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
            (clause     (acl2::mfc-clause mfc)))
        (let ((x (syn::arg 1 term))
              (y (syn::arg 2 term))
              (n (bag::usb16-fix (len type-alist))))
          (if (or (acl2::mfc-ancestors mfc)
                  (appears-negated term clause))
              (if (show-all-diverge-from-all-from-type-alist-fn nil x y n type-alist type-alist)
                  (syn::true)
                (met ((s1 t1) (simplify-all-diverge-from-all-cons-list-fn nil :swap x y type-alist))
                  (if s1 t1 term)))
            term)))
    term))

;; DAG -- who is using this name ??
(defun hyp-for-show-all-diverge-from-all-from-mfc-2 (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc)))
        (let ((x (syn::arg 1 term))
              (y (syn::arg 2 term))
              (n (bag::usb16-fix (len type-alist))))
          (let ((hyp (hyp-for-show-all-diverge-from-all-from-type-alist-fn nil x y n type-alist type-alist)))
            (let ((hyp (or hyp
                           (hyp-for-simplify-all-diverge-from-all-cons-list-fn nil :swap x y type-alist))))
              (bag::bind-extra-vars-in-hyp hyp term)))))
    term))

(defthm *meta*-all-diverge-from-all
  (implies
   (pd-eval (hyp-for-show-all-diverge-from-all-from-mfc-2 term mfc state) bag::a)
   (equal (pd-eval term bag::a)
          (pd-eval (show-all-diverge-from-all-from-mfc-2 term mfc state) bag::a)))
  :hints (("goal" :in-theory (e/d
                              (
                               syn::open-nth
                               show-all-diverge-from-all-from-type-alist-irrelevant
                               SIMPLIFY-ALL-DIVERGE-FROM-ALL-CONS-LIST-irrelevant
                               hyp-for-show-all-diverge-from-all-from-type-alist-irrelevant
                               hyp-for-simplify-all-diverge-from-all-cons-list-irrelevant
                               )
                              nil
                              )))
  :rule-classes ((:meta :trigger-fns (all-diverge-from-all)
                        :backchain-limit-lst 0
                        )))

(defun show-diverges-from-all-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverges-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
            (clause     (acl2::mfc-clause mfc)))
        (let ((x    (syn::arg 1 term))
              (list (syn::arg 2 term)))
          (if (or (acl2::mfc-ancestors mfc)
                  (appears-negated term clause))
              (if (show-diverges-from-all-from-type-alist-fn nil x list type-alist type-alist)
                  (syn::true)
                (met ((s1 t1) (simplify-diverges-from-all-from-cons-list-fn nil x list type-alist))
                  (if s1 t1 term)))
            term)))
    term))

(defun hyp-for-show-diverges-from-all-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverges-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc)))
        (let ((x    (syn::arg 1 term))
              (list (syn::arg 2 term)))
          (let ((hyp (hyp-for-show-diverges-from-all-from-type-alist-fn nil x list type-alist type-alist)))
            (let ((hyp (or hyp
                           (hyp-for-simplify-diverges-from-all-from-cons-list-fn nil x list type-alist))))
              (bag::bind-extra-vars-in-hyp hyp term)))))
    term))

(defthm *meta*-diverges-from-all
  (implies
   (pd-eval (hyp-for-show-diverges-from-all-from-mfc term mfc state) bag::a)
   (equal (pd-eval term bag::a)
          (pd-eval (show-diverges-from-all-from-mfc term mfc state) bag::a)))
  :hints (("goal" :in-theory (e/d
                              (
                               syn::open-nth
                               hyp-for-show-diverges-from-all-from-type-alist-irrelevant
                               simplify-diverges-from-all-from-cons-list-irrelevant
                               hyp-for-simplify-diverges-from-all-from-cons-list-irrelevant
                               )
                              (DIVERGES-FROM-ALL-BY-MEMBERSHIP
                               ))))
  :rule-classes ((:meta :trigger-fns (diverges-from-all)
                        :backchain-limit-lst 0
                        )))


;; All diverge from all .. assuming we are dealing in atomic functions.

;; (show-all-diverge-from-all-from-mfc term mfc state)

;; (show-diverges-from-all term mfc state)
;; (bag::subbagp x y)
;;  => (show-diverges-..)
;;
;; (show-diverge-from-mfc term mfc state)
;; (bag::memberp x list)
;; => (show-diverges-from-all a x mfc state)

;; ================================================
;;
;; Some possible all-diverge-from-all directions ..
;;
;; ================================================

(defthm dominates-transitive-three
  (implies
   (and
    (dominates b x)
    (dominates s b))
   (dominates s x)))

(defun fix-prefix (prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (cons entry (fix-prefix (cdr prefix))))
              (:append
               (cons entry (fix-prefix (cdr prefix))))
              (:quote
               (let ((entry (cons :quote (list::fix (cdr entry)))))
                 (cons entry nil)))
              (t nil)))
    nil))

(defun prefix-equiv (x y)
  (declare (type (satisfies wf-syntax-prefix) x y))
  (equal (fix-prefix x)
         (fix-prefix y)))

(defun prefix-len (prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (1+ (prefix-len (cdr prefix))))
              (:append
               (1+ (prefix-len (cdr prefix))))
              (:quote
               (len (list::fix (cdr entry))))
              (t 0)))
    0))

(defthm prefix-len-prop
  (<= 0 (prefix-len prefix))
  :rule-classes (:linear))

(defthm zp-prefix-len-reduction
  (iff (equal (prefix-len prefix) 0)
       (if (consp prefix)
           (let ((entry (car prefix)))
             (case (car entry)
                   (:cons
                    nil)
                   (:append
                    nil)
                   (:quote
                    (equal (len (list::fix (cdr entry))) 0))
                   (t t)))
         t)))

(defun firstn-prefix (n prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix)
           (type (integer 0 *) n))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (if (zp n) nil
                 (cons entry (firstn-prefix (1- n) (cdr prefix)))))
              (:append
               (if (zp n) nil
                 (cons entry (firstn-prefix (1- n) (cdr prefix)))))
              (:quote
               (let ((entry (cons :quote (acl2::firstn n (list::fix (cdr entry))))))
                 (cons entry nil)))
              (t nil)))
    nil))

(defthm wf-sytnax-prefix-firstn-prefix
  (implies
   (wf-syntax-prefix prefix)
   (wf-syntax-prefix (firstn-prefix n prefix)))
  :rule-classes (:rewrite :type-prescription))

(defthm list-cong-first-n
  (implies
   (<= (len list) (nfix n))
   (list::equiv (acl2::firstn n list)
                    list)))

(defthm prefix-equiv-firstn-prefix
  (implies
   (and
    (wf-syntax-prefix prefix)
    (<= (prefix-len prefix) (nfix n)))
   (prefix-equiv (firstn-prefix n prefix)
                 prefix)))


(defun prune-prefix (n prefix list2)
  (declare (type integer n))
  (if (and (consp prefix)
           (consp list2)
           (equal (car prefix) (car list2)))
      (prune-prefix (1+ n) (cdr prefix) (cdr list2))
    n))

(defthm integerp-prune-prefix
  (implies
   (integerp n)
   (integerp (prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm prune-prefix-len
  (implies
   (integerp n)
   (and (<= (prune-prefix n prefix list2)
            (+ n (len prefix)))
        (<= n (prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm consp-open-firstn
  (implies
   (consp list)
   (equal (acl2::firstn n list)
          (if (zp n) nil
            (cons (car list) (acl2::firstn (1- n) (cdr list)))))))

(defthm prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (prune-prefix n prefix x) n)))
   (dominates (acl2::firstn m prefix) x)))

(defun syntax-quote-prune-prefix (n prefix list2)
  (declare (type (satisfies wf-syntax-prefix) prefix)
           (type integer n))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (if (and (consp list2)
                        (syn::quotep (cdr entry))
                        (equal (syn::dequote (cdr entry)) (car list2)))
                   (syntax-quote-prune-prefix (1+ n) (cdr prefix) (cdr list2))
                 n))
              (:quote
               (prune-prefix n (cdr entry) list2))
              (t n)))
    n))

(defthm integerp-syntax-quote-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-quote-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-quote-prune-prefix-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-quote-prune-prefix n prefix list2)
            (+ n (prefix-len prefix)))
        (<= n (syntax-quote-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-quote-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-quote-prune-prefix n prefix x) n)))
   (dominates (s2l (firstn-prefix m prefix) a) x)))

(defun syntax-alist-prune-prefix (n prefix list2)
  (declare (type t prefix list2)
           (type integer n))
  (if (consp prefix)
      (cond
       ((syn::consp list2)
        (let ((v (syn::car list2)))
          (cond
           ((syn::quotep v)
            (if (equal (car prefix) (syn::dequote v))
                (syntax-alist-prune-prefix (1+ n) (cdr prefix) (syn::cdr list2))
              n))
           ((syn::quotep list2)
            (prune-prefix n prefix (syn::dequote list2)))
           (t n))))
       (t n))
    n))

(defthm integerp-syntax-alist-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-alist-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-alist-prune-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-alist-prune-prefix n prefix list2)
            (+ n (len prefix)))
        (<= n (syntax-alist-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-alist-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-alist-prune-prefix n prefix x) n)))
   (dominates (acl2::firstn m prefix) (syn::eval x a))))


(defun syntax-prune-prefix (n prefix list2)
  (declare (type (satisfies wf-syntax-prefix) prefix)
           (type integer n))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (cond
                ((syn::consp list2)
                 (if (equal (cdr entry) (syn::car list2))
                     (syntax-prune-prefix (1+ n) (cdr prefix) (syn::cdr list2))
                   n))
                ((syn::quotep list2)
                 (syntax-quote-prune-prefix n prefix (syn::dequote list2)))
                (t n)))
              (:append
               (if (and (syn::appendp list2)
                        (equal (cdr entry) (syn::arg 1 list2)))
                   (syntax-prune-prefix (1+ n) (cdr prefix) (syn::arg 2 list2))
                 n))
              (:quote
               (syntax-alist-prune-prefix n (cdr entry) list2))
              (t n)))
    n))

(defthm integerp-syntax-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-prune-prefix-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-prune-prefix n prefix list2)
            (+ n (prefix-len prefix)))
        (<= n (syntax-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-prune-prefix n prefix x) n)))
   (dominates (s2l (firstn-prefix m prefix) a) (syn::eval x a)))
  :hints (("Goal" :in-theory (enable syn::open-nth))))

(defun syntax-term-to-prefix (term)
  (declare (type t term))
  (cond
   ((syn::consp term)
    (met ((hit n prefix) (syntax-term-to-prefix (syn::cdr term)))
         (mv hit (1+ n) (cons (cons :cons (syn::car term)) prefix))))
   ((syn::appendp term)
    (met ((hit n prefix) (syntax-term-to-prefix (syn::arg 2 term)))
         (mv hit (1+ n) (cons (cons :append (syn::arg 1 term)) prefix))))
   ((syn::quotep term)
    (let ((term (syn::dequote term)))
      (if (true-listp term)
          (mv t (len term) (cons (cons :quote term) nil))
        (mv nil 0 nil))))
   (t (mv nil 0 nil))))

(defthm integerp-v1-syntax-term-to-prefix
  (integerp (v1 (syntax-term-to-prefix term))))

(defthm wf-syntax-prefix-v2-syntax-term-to-prefix
  (wf-syntax-prefix (v2 (syntax-term-to-prefix term))))

(defthm v0-implies-v1-is-prefix-len-v2
  (implies
   (v0 (syntax-term-to-prefix term))
   (equal (v1 (syntax-term-to-prefix term))
          (prefix-len (v2 (syntax-term-to-prefix term))))))

(defthm v0-implies-invertability
  (implies
   (v0 (syntax-term-to-prefix term))
   (equal (s2l (v2 (syntax-term-to-prefix term)) a)
          (syn::eval term a)))
  :hints (("Goal" :in-theory (enable syn::open-nth))))

(defthm prefix-len-firstn-prefix
  (implies
   (and
    (integerp m)
    (<= 0 m)
    (<= m (prefix-len prefix)))
   (equal (prefix-len (firstn-prefix m prefix))
          m)))

(defun syntax-quote-reduce-prefix (n prefix list)
  (declare (xargs :guard (and (integerp n)
                              (wf-syntax-prefix prefix)
                              (equal n (prefix-len prefix)))))
  (if (consp list)
      (let ((m (syntax-quote-prune-prefix 0 prefix (car list))))
        (if (zp m) nil
          (let ((prefix (if (< m n) (firstn-prefix m prefix) prefix))
                (n      (if (< m n) m n)))
            (syntax-quote-reduce-prefix n prefix (cdr list)))))
    prefix))

(defthm firstn-dominates-prefix
  (dominates (acl2::firstn n list) list)
  :hints(("Goal" :in-theory (enable acl2::firstn))))

(defthm s2l-firstn-prefix-dominates-prefix
  (dominates (s2l (firstn-prefix n prefix) a) (s2l prefix a)))

(defthm dominates-self-syntax-quote-reduce-prefix
  (dominates (s2l (syntax-quote-reduce-prefix n prefix list) a)
             (s2l prefix a)))

(defthm prefix-dominates-backchain
  (implies
   (and
    (integerp n)
    (dominates (s2l prefix a) x))
   (dominates (s2l (syntax-quote-reduce-prefix n prefix list) a) x)))

(defun dominates-all (x list)
  (declare (type t x list))
  (if (consp list)
      (and (dominates x (car list))
           (dominates-all x (cdr list)))
    t))

(defthm prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (prune-prefix n prefix x)
          (if (< 0 n)
              (+ 1 (prune-prefix (1- n) prefix x))
            (- 1 (prune-prefix (1+ n) prefix x))))))

(defthm prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (prune-prefix n prefix x)
          (+ n (prune-prefix 0 prefix x)))))

(defthm syntax-quote-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-quote-prune-prefix n prefix x)
          (if (< 0 n)
              (+ 1 (syntax-quote-prune-prefix (1- n) prefix x))
            (- 1 (syntax-quote-prune-prefix (1+ n) prefix x))))))

(defthm syntax-quote-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-quote-prune-prefix n prefix x)
          (+ n (syntax-quote-prune-prefix 0 prefix x)))))

(defthm syntax-alist-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-alist-prune-prefix n prefix x)
          (if (< 0 n)
              (+ 1 (syntax-alist-prune-prefix (1- n) prefix x))
            (- 1 (syntax-alist-prune-prefix (1+ n) prefix x))))))

(defthm syntax-alist-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-alist-prune-prefix n prefix x)
          (+ n (syntax-alist-prune-prefix 0 prefix x)))))

(defthm syntax-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-prune-prefix n prefix x)
          (if (< 0 n)
              (+ 1 (syntax-prune-prefix (1- n) prefix x))
            (- 1 (syntax-prune-prefix (1+ n) prefix x))))))

(defthm syntax-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-prune-prefix n prefix x)
          (+ n (syntax-prune-prefix 0 prefix x)))))

(defthm equal-prune-len-implies-domination
  (implies
   (and
    (equal (prune-prefix n prefix x) m)
    (equal m (+ n (len prefix))))
   (dominates prefix x)))

(defthm equal-syntax-quote-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-quote-prune-prefix n prefix x) m)
    (equal m (+ n (prefix-len prefix))))
   (dominates (s2l prefix a) x)))

(defthm equal-syntax-alist-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-alist-prune-prefix n prefix x) m)
    (equal m (+ n (len prefix))))
   (dominates prefix (syn::eval x a))))

(defthm equal-syntax-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-prune-prefix n prefix x) m)
    (equal m (+ n (prefix-len prefix))))
   (dominates (s2l prefix a) (syn::eval x a)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm nil-dominates-all
  (dominates-all nil list))

(defthm dominates-all-syntax-quote-reduce-prefix
  (implies
   (equal n (prefix-len prefix))
   (dominates-all (s2l (syntax-quote-reduce-prefix n prefix list) a) list))
  :hints (("goal" :induct (syntax-quote-reduce-prefix n prefix list))))

(defun syntax-reduce-prefix (n prefix list)
  (declare (xargs :guard (and (integerp n)
                              (wf-syntax-prefix prefix)
                              (equal n (prefix-len prefix)))))
  (cond
   ((syn::consp list)
    (let ((m (syntax-prune-prefix 0 prefix (syn::car list))))
      (if (zp m) nil
        (let ((prefix (if (< m n) (firstn-prefix m prefix) prefix))
              (n      (if (< m n) m n)))
          (syntax-reduce-prefix n prefix (syn::cdr list))))))
   ((syn::quotep list)
    (syntax-quote-reduce-prefix n prefix (syn::dequote list)))
   (t nil)))

(defthm dominates-self-syntax-reduce-prefix
  (dominates (s2l (syntax-reduce-prefix n prefix list) a)
             (s2l prefix a)))

(defthm syntax-reduce-prefix-dominates-backchain
  (implies
   (and
    (integerp n)
    (dominates (s2l prefix a) x))
   (dominates (s2l (syntax-reduce-prefix n prefix list) a) x)))

(defthm dominates-all-syntax-reduce-prefix
  (implies
   (equal n (prefix-len prefix))
   (dominates-all (s2l (syntax-reduce-prefix n prefix list) a) (syn::eval list a)))
  :hints (("goal" :induct (syntax-reduce-prefix n prefix list))))


(defun syntax-prefix (list)
  (declare (type t list))
  (if (syn::consp list)
      (let ((term (syn::car list)))
        (met ((hit n prefix) (syntax-term-to-prefix term))
             (and hit (syntax-reduce-prefix n prefix (syn::cdr list)))))
    nil))

(defthm dominates-all-syntax-prefix
  (dominates-all (s2l (syntax-prefix list) a) (syn::eval list a)))

;; ===================
;;
;; Meta key extraction
;;
;; ===================


(defun keyx (list)
  (declare (type t list))
  (if (consp list)
      (if (consp (car list))
          (cons (caar list)
                (keyx (cdr list)))
        (cons nil (keyx (cdr list))))
    nil))

(defthm keyx-reduction
  (equal (keyx list)
         (keys list)))

;; jcd - had to change a few "keys" to "strip-cars" here since keys is just a
;; macro alias now and isn't a real function.

(defund syntax-keys (hit list)
  (declare (type t list))
  (cond
   ((syn::consp list)
    (let ((x (syn::car list)))
      (let ((v (if (syn::consp x) (syn::car x) `(car ,x))))
        (syn::cons v (syntax-keys t (syn::cdr list))))))
   ((syn::quotep list)
    (let ((list (syn::dequote list)))
      (syn::enquote (keyx list))))
   ((syn::appendp list)
    (syn::append (syntax-keys t (syn::arg 1 list))
                 (syntax-keys t (syn::arg 2 list))))
   (t
    (and hit `(strip-cars ,list)))))

(defthm syntax-keys-true
  (implies
   hit
   (syntax-keys hit list))
  :hints (("goal" :in-theory (enable
                              syntax-keys
                              ))))

(defthm key-eval-syntax-keys
  (implies
   (syntax-keys hit term)
   (equal (key-eval (syntax-keys hit term) a)
          (keys (key-eval term a))))
  :hints (("goal" :in-theory (e/d (syn::open-nth
                                   keys syntax-keys)
                                  (keys-of-cdr)))))

(defun syntax-keys-wrapper (term)
  (declare (type t term))
  (if (syn::funcall 'strip-cars 1 term)
      (let ((list (syn::arg 1 term)))
        (let ((list (syntax-keys nil list)))
          (or list
              term)))
    term))

(defthm *meta*-key-eval-keys
  (equal (key-eval term a)
         (key-eval (syntax-keys-wrapper term) a))
  :hints (("goal" :in-theory (enable syn::open-nth)))
  :rule-classes ((:meta :trigger-fns (strip-cars))))
;  :rule-classes ((:meta :trigger-fns (keys))))



;; jcd - this is redundant, removing
;; (in-theory
;;  (disable
;;   keys
;;   ))

;; #|

;; (defun common-prefixes (prefixes a list2)
;;   (if (consp list2)
;;       (let ((prefixes (common-prefix prefixes (car list2) a)))
;;         (common-prefixes prefixes a (cdr list2)))
;;     prefixes))

;; (defun common-prefixes-list (prefixes list1 list2)
;;   (if (consp list1)
;;       (let ((prefixes (common-prefixes (car list1) list2)))
;;         (common-prefixes-list prefixes (cdr list1) list2))
;;     prefixes))


(in-theory (disable sp-to-clrp))

(defthm clrp-sp-domination
  (implies
   (dominates a r)
   (equal (clrp r (sp a v st))
          (sp a (clrp (nthcdr (len a) r) v) st)))
  :hints (("goal" :in-theory (enable dominates
                                     clrp
                                     sp
                                     gp
                                     nthcdr))))

(defun dominated (a list)
  (declare (type t list))
  (if (consp list)
      (if (dominates a (car list))
          (cons (car list) (dominated a (cdr list)))
        (dominated a (cdr list)))
    nil))

(defthm dominated-when-no-domination
  (implies
   (not (dominates-some a list))
   (equal (dominated a list) nil)))

(defthm nthcdr-not-consp
  (implies
   (not (consp list))
   (equal (nthcdr n list) (if (zp n) list nil))))

(defun nthcdrx (n list)
  (declare (type (integer 0 *) n))
  (if (zp n) list
    (if (consp list)
        (nthcdrx (1- n) (cdr list))
      nil)))

(defthm nthcdrx-to-nthcdr
  (equal (nthcdrx n list)
         (nthcdr n list))
  :hints (("goal" :in-theory (enable nthcdr))))

(defun map-nthcdr (n list)
  (declare (type (integer 0 *) n))
  (if (consp list)
      (cons (nthcdrx n (car list))
            (map-nthcdr n (cdr list)))
    nil))

(defthm sp-of-clrp
  (implies
   (dominates a x)
   (equal (sp a v (clrp x r))
          (sp a v r)))
  :hints (("goal" :in-theory (enable dominates sp clrp))))

(defthm clrp-of-sp-identity
  (equal (clrp a (sp a v r))
         (clrp a r))
  :hints (("goal"  :induct (sp a v r)
           :in-theory (enable sp clrp))))

(defthmd clrp-commute-2
  (equal (clrp a (clrp b r))
         (clrp b (clrp a r)))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))

(defthm clrp-clrp-list-sp-reduction
  (equal (clrp a (clrp-list list (sp a v r)))
         (clrp a (clrp-list list r)))
  :hints (("goal" :in-theory (e/d
                              (
                               clrp-list
                               clrp-commute-2
                               )
                              (
                               clrp-of-clrp
                               meta-rule-to-show-prefix-domination
                               )))))

(defthm nthcdr-of-dominator
  (implies
   (dominates x a)
   (list::equiv (nthcdr (len a) x)
                    nil))
  :hints (("goal" :in-theory (enable dominates nthcdr))))

(defthm diverges-from-all-from-non-domination
  (implies
   (and
    (not (dominates-some a list))
    (not (dominated-by-some a list)))
   (diverges-from-all a list))
  :hints (("goal" :in-theory (enable diverges-from-all
                                     dominates-some
                                     dominated-by-some)))
  :rule-classes (:forward-chaining))

(defthm clrp-list-sp-domination
  (implies
   (not (dominated-by-some a list))
   (equal (clrp-list list (sp a v st))
          (sp a (clrp-list (map-nthcdr (len a) (dominated a list)) v)
              (clrp-list list st))))
  :hints (("goal" :induct (clrp-list list st)
           :in-theory (e/d
                       (
                        clrp-commute-2
                        diverge
                        ;jcd - removing graph.lisp - equal-sp-reduction
                        dominates-some
                        dominated-by-some
                        clrp-list
                        CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL)
                       (
                        clrp-of-clrp
;jcd                        NTHCDR-WHEN-DOMINATES
                        )))))

(defthm gp-clrp
  (implies
   (dominates a x)
   (equal (gp a (clrp x st))
          (clrp (nthcdr (len a) x) (gp a st))))
  :hints (("goal" :in-theory (enable
                              diverge
                              clrp
                              GP-OF-SP
                              ))))

(defthm gp-clrp-list
  (implies
   (not (dominated-by-some a list))
   (equal (gp a (clrp-list list st))
          (clrp-list (map-nthcdr (len a) (dominated a list)) (gp a st))))
  :hints (("goal" :induct (clrp-list list st)
           :in-theory (e/d
                       (
                        ;; jcd - not necessary clrp-commute-2
                        ;; jcd - not necessary diverge
                        ;; jcd - removing graph.lisp - equal-sp-reduction
                        ;; jcd - not necessary dominates-some
                        ;; jcd - not necessary dominated-by-some
                        clrp-list
                        ;; jcd not necessary CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL
                        )
                       (
                        ;; jcd - not necessary clrp-of-clrp
                        ;; jcd - not necessary NTHCDR-WHEN-DOMINATES
                        )))))

#|


(defthm syntax-quote-dominates-implies-dominates-pd-eval
  (implies
   (syntax-quote-dominates-p x y)
   (dominates x (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance syntax-quote-dominates-implies-dominates
                                             (syn::eval pd-eval)
                                             (syn::eval-list pd-eval-list)))))

(defthm syntax-domination-implies-domination-helper-pd-eval
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance syntax-domination-implies-domination-helper
                                             (syn::eval pd-eval)
                                             (syn::eval-list pd-eval-list)))))

(defthm syntax-domianted-by-some-quote-implies-domianted-by-some
  (implies
   (syntax-dominated-by-some-quote x qlist)
   (dominated-by-some (pd-eval x bag::a) qlist))
  :hints (("goal" :in-theory (enable dominated-by-some)))
  :rule-classes (:forward-chaining :rewrite))


(defthm syntax-domianted-by-some-better-implies-domianted-by-some
  (implies
   (syntax-dominated-by-some x list alist)
   (dominated-by-some (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominated-by-some)))
  :rule-classes (:forward-chaining :rewrite))

(defthm syntax-domiantes-some-implies-domiantes-some
  (implies
   (syntax-dominates-some x list alist)
   (dominates-some (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominates-some)))
  :rule-classes (:forward-chaining :rewrite))

(defthm syntax-domiantes-some-quote-implies-domiantes-some
  (implies
   (syntax-dominates-some-quote x list)
   (dominates-some x (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominates-some)))
  :rule-classes (:forward-chaining :rewrite))

(defun all-dominate-some (x y)
  (if (consp x)
      (and (dominates-some (car x) y)
           (all-dominate-some (cdr x) y))
    t))

(include-book "equiv")

(defthm all-dominate-some-subset
  (implies
   (path-subset x y)
   (all-dominate-some x y)))

(defthm all-dominate-some-id
  (all-dominate-some x x))

(defthm all-dominate-some-append-2
  (implies
   (all-dominate-some x y)
   (all-dominate-some x (append y z))))

(defthm all-dominate-some-append-3
  (implies
   (all-dominate-some x z)
   (all-dominate-some x (append y z))))

(defthm memberp-v0-split-list-by-dominators
  (equal (memberp a (v0 (split-list-by-dominators-quote list x rx ry)))
         (or (memberp a rx)
             (and (memberp a list)
                  (syntax-dominates-some-quote a x)))))

(defthm promote-rx
  (implies
   (consp rx)
   (bag::perm (v0 (split-list-by-dominators-quote list x rx ry))
              (cons (car rx) (v0 (split-list-by-dominators-quote list x (cdr rx) ry)))))
  :hints (("goal" :in-theory (e/d (BAG::PERM-BY-DOUBLE-CONTAINMENT)
                                  (BAG::PERM-OF-CONS-MEMBERP-CASE
                                   BAG::PERM-OF-cons)))))

(defthm all-diverge-from-all-split-list-by-dominatros-quote
  (implies
   (and
    (all-diverge list)
    (all-diverge-from-all rx ry))
   (all-diverge-from-all (v0 (split-list-by-dominators-quote list x rx ry))
                         (v1 (split-list-by-dominators-quote list x rx ry))))
  :hints (("goal" :in-theory (enable all-diverge))))

(defun split-list-by-dominators (list x rx ry alist)
  (cond
   ((syn::consp list)
    (if (syntax-dominates-some (syn::car list) x alist)
        (split-list-by-dominators (syn::cdr list) x (syn::cons (syn::car list) rx) ry alist)
      (split-list-by-dominators (syn::cdr list) x rx (syn::cons (syn::car list) ry) alist)))
   ((syn::appendp list)
    (met ((rx ry) (split-list-by-dominators (syn::arg 1 list) x rx ry alist))
      (split-list-by-dominators (syn::arg 2 list) x rx ry alist)))
   ((syn::quotep list)
    (met ((vx vy) (split-list-by-dominators-quote (syn::dequote list) x nil nil))
      (mv (syn::append rx vx) (syn::append ry vy))))
   (t
    (if (syntax-all-dominate-some list x)
        (mv (syn::append list rx) ry)
      (mv rx (syn::append list ry))))))

(defthm syntax-all-dominate-some-implies-all-dominate-some
  (implies
   (syntax-all-dominate-some x y)
   (all-dominate-some (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("goal" :in-theory (enable syn::open-nth))))





(defun all-diverge-from-all-decompose-2 (x y alist)
  (cond
   ((syn::consp x)
    (and (show-diverges-from-all (syn::car x) y alist)
         (all-diverge-from-all-decompose-2 (syn::cdr x) y alist)))
   ((syn::appendp x)
    (and (all-diverge-from-all-decompose-1 (syn::arg 1 x) y alist)
         (all-diverge-from-all-decompose-1 (syn::arg 2 x) y alist)))
   ((syn::quotep x)
    (all-diverge-from-all-decompose-1-quote (syn::dequote x) y alist))
   (t
    (show-all-diverge-from-all-decompose-2 x y alist))))

(defun all-diverge-from-all-decompose-1 (x y alist)
  (cond
   ((syn::consp x)
    (and (show-diverges-from-all-decompose-2 (syn::car x) y alist)
         (all-diverge-from-all-decompose-1 (syn::cdr x) y alist)))
   ((syn::appendp x)
    (and (all-diverge-from-all-decompose-1 (syn::arg 1 x) y alist)
         (all-diverge-from-all-decompose-1 (syn::arg 2 x) y alist)))
   ((syn::quotep x)
    (all-diverge-from-all-decompose-1-quote (syn::dequote x) y alist))
   (t
    (show-all-diverge-from-all-decompose-2 x y alist))))


(defun all-diverge-from-all-decompose (x y alist)
  )

;; It might be best to break up the input (as well as intermediate
;; results) into atomic segments and then reason about those
;; segments one at a time.  This would unify many of the routines
;; and make them more general.

(defun list::constituant (list c a q)
  (cond
   ((syn::consp list)
    (let ((x (syn::car list)))
      (if (syn::quotep x)
          (constituant (syn::cdr list) c a (cons (syn::dequote x) q))
        (constituant (syn::cdr list) (cons x c) a q))))
   ((syn::append list)
    (met ((c a q) (constituant (syn::arg 1 list) c a q))
      (constituant (syn::arg 2 list) c a q)))
   ((syn::quotep list)
    (mv c a (append (syn::dequote list) q)))
   (t
    (mv c (cons list a) q))))

(defun list::reconstitute-c (c)
  (if (consp c)
      (syn::cons (car c)
                 (list::reconstitute-c (cdr c)))
    (syn::nil)))

(defun list::reconstitute-a (a)
  (if (consp a)
      (syn::append (car a)
                   (list::reconstitute-a (cdr a)))
    (syn::nil)))

(defun list::reconstitute-q (q)
  (syn::quote q))

(defun list::reconstitute (c a q)
  (syn::append (list::reconstitute-a a)
               (syn::append (list::reconstitute-c c)
                            (list::reconstitute-q q))))

(defthm reconstitution
  (met ((c a q) (list::constituant list))
    (bag::perm (pd-eval (list::reconstitute c a q) bag::a)
               (pd-eval list bag::a))))

(defthm
  (implies
   (member fn *supported-functions*)
   (equal (pd-eval (simplify goals) bag::a)
          (pd-eval (reconstruct goals) bag::a))))

(defun simplify (stack)
  (if (consp stack)
      (let ((op (car stack)))
        (let ((stack (reduce op stack)))
          (simplify stack)))
    ..))

(defun elaborate (fn x alist)
  )

(defun show (fn x y n alist whole)
  )

(defun simplify-term-list (fn term-list x)
  )

(defun simplify-quote-list (fn quote-list x)
  )

(defun simplify (fn x y n alist whole)
  (if (or (zp n) (endp type-alist))
      nil
    (let* ((entry (car type-alist))
           (fact  (car entry)))
      (case fn
        (:all-diverge-from-all
         (cond
          ((syn::funcall 'all-diverge-from-all 2 fact)
           (met ((sx a sy b) (match-subbags x y (syn::arg 1 fact) (syn::arg 2 fact) whole))
             (or (and sx sy)
                 (and sx (met ((c2 a2 q2) (deconstruct a))
                           (and (simplify-list :diverges-from-all c2 y)
                                (simplify-list :all-diverge-from-all a2 y)
                                (simplify-quote-list :all-diverge-from-all q2 y))))
                 (and sy (met ((c2 a2 q2) (deconstruct b))
                           (and (simplify-list :diverges-from-all c2 x)
                                (simplify-list :all-diverge-from-all a2 x)
                                (simplify-quote-list :all-diverge-from-all q2 x))))
                 (simplify fn x y n (cdr alist) whole))))
          (and (syn::funcall 'all-diverge 1 fact)
               (bag::ts-non-nil (cadr entry))
               (bag::show-unique-subbagps-from-type-alist x list
                                                          (syn::arg 1 fact)
                                                          (bag::usb16-fix (len whole-alist)) whole-alist whole-alist 1))))
        (:diverge
         (cond
          ((syn::funcall 'diverge)
           (or (and (equal x (syn::arg 1 fact))
                    (equal y (syn::arg 2 fact)))
               (and (equal x (syn::arg 2 fact))
                    (equal y (syn::arg 1 fact)))
               (simplify fn x y n (cdr alist) whole)))
          ((syn::funcall 'diverges-from-all)
           (or (and (equal x (syn::arg 1 fact))
                    (show-membership y (syn::arg 2 fact)))
               (and (equal y (syn::arg 2 fact))
                    (show-membership x (syn::arg 2 fact)))))
          ((syn::funcall 'all-diverge-from-all)
           (or (and (show-membership x (syn::arg 1 fact))
                    (show-membership y (syn::arg 2 fact)))
               (and (show-membership x (syn::arg 2 fact))
                    (show-membership y (syn::arg 1 fact)))))
          ((syn::funcall 'all-diverge)
           (bag::show-unique-membership-from-type-alist x list
                                                        (syn::arg 1 fact)
                                                        (bag::usb16-fix (len whole-alist))))))
        (:diverges-from-all
         )

             (or (and sx sy)
                 (and sx (met ((c2 a2 q2) (deconstruct a))
                           (and (simplify-list :diverges-from-all c2 y)
                                (simplify-list :all-diverge-from-all a2 y)
                                (simplify-quote-list :all-diverge-from-all q2 y))))
                 (and sy (met ((c2 a2 q2) (deconstruct b))
                           (and (simplify-list :diverges-from-all c2 x)
                                (simplify-list :all-diverge-from-all a2 x)
                                (simplify-quote-list :all-diverge-from-all q2 x))))
                 (simplify fn x y n (cdr alist) whole))))
          (and (syn::funcall 'all-diverge 1 fact)
               (bag::ts-non-nil (cadr entry))
               (bag::show-unique-subbagps-from-type-alist x list
                                                          (syn::arg 1 fact)
                                                          (bag::usb16-fix (len whole-alist)) whole-alist whole-alist 1)))
          (t
           (simplify fn x y n (cdr alist) whole))))

          (:


    (:all-diverge
     (case fn
       (:diverge
        (unique-members
     )

  (case fn
    (:neq
     )
    (:diverge
     )
    (:perm
     )
    (:member
     )
    (:not-member
     )
    (:subbagp
     )
    (:allmembers
     )
    ))

(defthm diverge-from-syntax-dominating-divergence
  (implies
   (and
    (diverge a b)
    (syntax-quote-dominates-p a v)
    (syntax-quote-dominates-p b w))
   (diverge (pd-eval v bag::a) (pd-eval w bag::a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm diverge-from-syntax-dominated-by-some-diverges-from-all
  (implies
   (and
    (diverges-from-all a qlist)
    (syntax-quote-dominates-p a v)
    (syntax-dominated-by-some-quote w qlist))
   (diverge (pd-eval v bag::a) (pd-eval w bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable diverges-from-all)
           :induct (syntax-dominated-by-some-quote w qlist))))

(defun syntax-not-dominates (x y)
  (cond
   ((syn::consp x)
    (or (not (syn::consp y))
        (let ((v (syn::car x))
              (w (syn::car y)))
          (or (not (syn::quotep v))
              (not (syn::quotep w))
              (not (equal (syn::dequote v) (syn::dequote w)))
              (syntax-not-dominates (syn::cdr x) (syn::cdr y))))))
   ((syn::quotep x)
    (not (dominates (syn::dequote x) (syn::dequote y))))
   (t ;; For our purposes, this is a no-op
    t)))

(defthm not-dominates-when-syntax-not-equal
  (implies
   (and
    (consp a)
    (SYNTAX-QUOTE-DOMINATES-P A Y)
    (syntax-not-dominates y x))
   (not (SYNTAX-QUOTE-DOMINATES-P A X))))


(defun syntax-unique-portions (list x xr yr)
  (cond
   ((syn::consp list)
    (if (syntax-dominates-some (syn::car list) x)
        (syntax-unique-portions (syn::cdr list) x (cons xr) y yr)




;;
;; Cannot seem to independently say what we want
;;

(defthm diverge-from-syntax-dominated-by-some-all-diverge
  (implies
   (and
    (all-diverge qlist)
    (not (equal x y))
    (syntax-dominated-by-some-quote x qlist)
    (syntax-dominated-by-some-quote y qlist))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :hints (("goal" :in-theory (e/d (all-diverge)
                                  (open-dominates)))))



|#
