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

(in-package "CPATH")
(include-book "../lists/repeat")
(include-book "../bags/top")
(include-book "../alists/top")
(include-book "../records/records")
(include-book "../records/domain") ;because we mention rkeys below
(include-book "compatibility")
(include-book "dominates")
(include-book "diverge")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "../util/iff"))


;; Leftover Dominates/Diverge Stuff ------------------------------------------
;;
;; Here are a bunch of rules that should either
;;  (1) be deleted, or
;;  (2) be properly moved into diverge.lisp or dominates.lisp
;;
;; And other things to do to these files:

;; These theorems should be given backchain limits instead of disabling them.
(in-theory (disable consp-of-car-when-all-conses))
(in-theory (disable consp-of-car-when-no-conses))

;; jcd - bzo it seems like this causes problems
(in-theory (disable list-equiv-when-dominated))

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


;; add this rule
(encapsulate
 ()
 (local (defthm lemma
          (implies (and (not (dominated-by-some p paths))
                        (not (dominates-some p paths)))
                   (diverges-from-all p paths))))

 (local (defthm lemma2
          (implies (and (not (strictly-dominated-by-some p paths))
                        (not (dominates-some p paths)))
                   (not (dominated-by-some p paths)))

          :hints(("Subgoal 1"
                  :in-theory (e/d (strictly-dominates)
                                  (not-dominates-some-forward-to-not-dominates
                                   not-strictly-dominates-some-forward-to-not-strictly-dominates))
                  :use ((:instance not-dominates-some-forward-to-not-dominates
                                   (a DOMINATED-BY-SOME-MEMBER)
                                   (b p)
                                   (x paths))
                        (:instance
                         not-strictly-dominates-some-forward-to-not-strictly-dominates
                         (b p)
                         (x paths)
                         (a DOMINATED-BY-SOME-MEMBER)))))))

 (defthm diverges-from-when-not-strictly-dominated-by-some-and-not-dominates-some
   (implies (and (not (strictly-dominated-by-some p paths))
                 (not (dominates-some p paths)))
            (diverges-from-all p paths))))

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

(theory-invariant (incompatible (:rewrite dominates-of-cdr-and-cdr-one)
                                (:definition dominates)))





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

(theory-invariant (incompatible (:rewrite s-of-s-list-not-memberp-case)
                                (:rewrite s-list-of-s-not-memberp-case)))

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

(include-book "../util/syntaxp")
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

(defcong list::equiv equal (copy alist r1 r2) 1
  :hints(("Goal" :induct (list::len-len-induction alist alist-equiv))))

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

;; jcd - added this
(encapsulate
 ()

 (local (defun my-induct (keys n)
          (if (consp keys)
              (my-induct (cdr keys) (1- n))
            (list keys n))))

 (defthm assoc-2-of-repeat-of-when-memberp
   (implies (<= (len keys) (nfix n))
            (equal (assoc-2 a keys (repeat n v))
                   (if (memberp a keys)
                       v
                     nil)))
   :hints(("Goal" :induct (my-induct keys n)))))

(encapsulate
 ()
 (local (defthm copy-of-s-1-memberp-case-helper
          (implies (and (bag::unique (keys alist))
                        (list::memberp a (range alist)))
                   (equal (copy alist (s a v r1) r2)
                          (s-list (pre-image a alist)
                                  (repeat (num-keys-for a alist) v)
                                  (copy alist r1 r2))))
          :hints (("Goal" :in-theory (enable copy s-list)))))


 ;; Since one spot in r1 can provide a value for many spots in r2, setting A in
 ;; r1 may require us to set many things in r2.  ( if many spots in r2 are
 ;; getting the value from spot A in r1).

 (defthm copy-of-s-1-memberp-case
   (implies (list::memberp a (range alist))
            (equal (copy alist (s a v r1) r2)
                   (s-list (pre-image a alist)
                           (repeat (num-keys-for a alist) v)
                           (copy alist r1 r2))))
   :hints (("Goal"
            :in-theory (disable copy-of-s-1-memberp-case-helper)
            :use (:instance copy-of-s-1-memberp-case-helper
                            (alist (remove-shadowed-pairs alist)))))))

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

(theory-invariant (incompatible (:rewrite s-of-copy-non-memberp-case)
                                (:rewrite copy-of-s-2-memberp-case)))

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

(encapsulate
 ()
 ;; jcd - Strange variable names?
 (local (defthm copy-associative-helper
          (implies (and (bag::unique (keys a32))
                        (bag::unique (keys a21)))
                   (equal (copy a32 (copy a21 r1 r2) r3)
                          (copy (compose-alists-aux a32 a21) r1 (copy a32 r2 r3))))
          :hints (("Goal"
                   :in-theory (enable copy)))))

 (defthm copy-associative
   (equal (copy a32 (copy a21 r1 r2) r3)
          (copy (compose-alists a32 a21) r1 (copy a32 r2 r3)))
   :hints (("Goal"
            :use (:instance  copy-associative-helper
                             (a21 (remove-shadowed-pairs a21))
                             (a32 (remove-shadowed-pairs a32)))
            :in-theory (disable copy-associative-helper)))))

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

;; jcd - copy of dominates rule
;; (defcong list::equiv equal (dominates p1 p2) 1
;;   :hints (("Goal" :in-theory (e/d (list::equiv dominates)
;;                                   (list::EQUAL-OF-FIXES)))))

;; jcd - copy of domiantes rule
;; (defcong list::equiv equal (dominates p1 p2) 2
;;   :hints (("Goal" :in-theory (e/d (list::equiv dominates)
;;                                   (list::EQUAL-OF-FIXES)))))

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

;; jcd - moved to dominates.lisp
;; (encapsulate
;;  ()
;;  (local (defthm dominates-of-append-and-append-forward
;;           (implies (dominates (append x z) (append x y))
;;                    (dominates z y))
;;           :hints (("Goal" :in-theory (enable dominates append)))))
;;  (local (defthm dominates-of-append-and-append-back
;;           (implies (dominates z y)
;;                    (dominates (append x z) (append x y)))
;;           :hints (("Goal" :in-theory (enable dominates append)))))
;;  (defthm dominates-of-append-and-append
;;    (equal (dominates (append x z) (append x y))
;;           (dominates z y)
;;           )
;;    :hints (("Goal" :in-theory (enable dominates)))))



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

;; jcd - copy in diverge.lisp
;; (defcong list::equiv equal (diverge p1 p2) 1
;;   :hints (("Goal" :in-theory (e/d (diverge) ()))))

;; jcd - copy in diverge.lisp
;; (defcong list::equiv equal (diverge p1 p2) 2
;;   :hints (("Goal" :in-theory (e/d (diverge) ()))))


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

;; jcd - moved to diverge.lisp
;; (defcong list::equiv equal (all-diverge paths) 1
;;   :hints(("Goal" :in-theory (enable all-diverge)
;;           :induct (list::len-len-induction paths list::paths-equiv))))

;; jcd moved to diverge.lisp
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

(encapsulate
 ()
 (local (defthm gp-of-list-fix
          (equal (gp (list::fix p) r)
                 (gp p r))
          :hints (("Goal" :in-theory (enable gp)))))

 (defcong list::equiv equal (gp p r) 1
   :hints (("Goal"
            :in-theory (disable gp-of-list-fix)
            :use ((:instance gp-of-list-fix (p p))
                  (:instance gp-of-list-fix (p p-equiv)))))))

(defthmd gp-of-gp
  (equal (gp p1 (gp p2 r))
         (gp (append p2 p1) r))
  :hints (("Goal" :in-theory (enable gp))))

(defthm gp-of-append
  (equal (gp (append p2 p1) r)
         (gp p1 (gp p2 r)))
  :hints (("Goal" :in-theory (enable gp))))

(theory-invariant (incompatible (:rewrite gp-of-gp)
                                (:rewrite gp-of-append)))


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

(theory-invariant (incompatible (:rewrite SP-OF-SP-DOMINATING-CASE-TWO)
                                (:rewrite SP-OF-SP-ONE)))

(defthm sp-of-sp
  (equal (sp p1 v1 (sp p2 v2 r))
         (if (dominates p1 p2)
             (sp p1 v1 r)
           (if (diverge p1 p2)
               (sp p2 v2 (sp p1 v1 r))
             (sp p2 (sp (nthcdr (len p2) p1) v1 v2) r))))
  :rule-classes ((:rewrite :loop-stopper ((p1 p2)))))

(encapsulate
 ()

 (local (defthm sp-of-list-fix
          (equal (sp (list::fix p) v r)
                 (sp p v r))
          :hints (("Goal" :in-theory (enable sp)))))

 (defcong list::equiv equal (sp p v r) 1
   :hints (("Goal"
            :in-theory (disable sp-equal-rewrite
                                sp-of-list-fix)
            :use ((:instance sp-of-list-fix (p p))
                  (:instance sp-of-list-fix (p p-equiv))))))
)

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
  :hints(("Goal" :induct (list::len-len-induction alist alist-equiv))))

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
(defcong list::equiv equal (append-onto-keys a x) 1)

;; jcd - added this
(defcong alist::alist-equiv equal (append-onto-keys a x) 2
  :hints(("Goal" :induct (list::len-len-induction x x-equiv))))

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

(encapsulate
 ()
 ;; jcd localized this
 (local (defthm mp-ignores-alistfix
          (equal (mp (alist::alistfix alist) r1 r2)
                 (mp alist r1 r2))))

 ;; jcd added this congruence
 (defcong alist::alist-equiv equal (mp alist r1 r2) 1
   :hints(("Goal"
           :in-theory (disable mp-ignores-alistfix)
           :use ((:instance mp-ignores-alistfix (alist alist))
                 (:instance mp-ignores-alistfix (alist alist-equiv))))))
)


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

;; jcd - added this


;2 This is the case where (exactly) one of the keys in ALIST dominates P.  So the result of calling gp on mp
;doesn't depend on R2 at all (note that R2 does not appear in the conclusion).  We know at least one key dominates
;P, and, since all the keys diverge, only one key can dominate P.

;; jcd - added these
;; jcd redundant with dominates.lisp (defcong list::equiv equal (first-dominator p paths) 1)
;; jcd redundant with dominates.lisp (defcong list::equiv equal (dominated-by-some p paths) 1)
;; jcd redundant with dominates.lisp (defcong list::equiv equal (dominates-some p paths) 1)
;; jcd redundant with diverge.lisp   (defcong list::equiv equal (diverges-from-all p paths) 1
;;   :hints(("Goal" :in-theory (enable diverges-from-all))))

;; jcd redundant with alistfix-equiv proven above
;; (defcong list::equiv equal (mp alist r1 r2) 1
;;  :hints(("Goal" :induct (list::len-len-induction alist list::alist-equiv))))





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


;; (thm
;;  (implies (and (dominated-by-some p (keys alist))
;;                )
;;           (equal (gp p (mp alist r1 r2))
;;                  (mp (keep-but-chop-strictly-dominated-pairs (biggest-dominator p (keys alist)) alist)
;;                           r1
;;                           (gp (cdr (assoc (biggest-dominator p (keys alist)) alist)) r1))))
;;  :hints (("Goal" ;:induct t
;; ;:induct (MP ALIST R1 R2)
;;           :in-theory (e/d (keep-but-chop-strictly-dominated-pairs
;;                              diverge
;;                              )
;;                           ((:induction KEEP-BUT-CHOP-STRICTLY-DOMINATED-PAIRS)
;;                            MP-OF-GP
;;                            assoc
;;                            ))
;;           :do-not '(generalize eliminate-destructors))))





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


;; jcd - added this
(defcong list::equiv equal (keep-but-chop-relevant-pairs p alist) 1)

;; jcd - added this
(defcong alist::alist-equiv equal (keep-but-chop-relevant-pairs p alist) 2
  :hints(("Goal" :induct (list::len-len-induction alist alist-equiv))))

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

;; jcd - added this
(defcong list::equiv equal (effect-on-spot p alist) 1
  :hints(("Goal" :in-theory (enable effect-on-spot))))

;; jcd - added this
(defcong alist::alist-equiv equal (effect-on-spot p alist) 2
  :hints(("Goal"
          :in-theory (enable effect-on-spot)
          :induct (list::len-len-induction alist alist-equiv))))

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

(theory-invariant (incompatible (:rewrite mp-of-sp-diverges-from-all-case)
                                (:rewrite sp-of-mp-diverges-from-all-case)))


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
;; (thm
;;  (equal (mp (remove-pairs-dominated-by p alist) r2 r3)
;;         (sp p (gp p r3) (mp alist r2 r3)))
;;  :hints (("Goal" :induct t
;;           :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (mp) ((:induction REMOVE-PAIRS-DOMINATED-BY))))))


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

;; jcd - added this
(defcong alist::alist-equiv equal (no-shadowed-pairs alist) 1
  :hints(("Goal" :induct (list::len-len-induction alist alist-equiv))))

(in-theory (enable gp-of-mp-better))



;; (thm
;;  (implies (and (not (diverges-from-all p paths))
;;                (not (dominated-by-some p paths)))
;;           (dominates-some p paths) ; in fact, we know strictly dominated?
;;           ))

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

;; jcd - added this rule
(defcong list::equiv equal (no-submissives paths) 1
  :hints(("Goal" :induct (list::len-len-induction paths paths-equiv))))

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







;; (thm
;;  (implies (and (consp a32)
;;                (list-of-true-listps (keys a21))
;;                (list-of-true-listps (keys a32))
;;                (list-of-true-listps (vals a32))
;;                (list-of-true-listps (vals a21)))
;;           (equal (effect-on-spot (caar a32) (my-compose-alists a32 a21))
;;                  (append (effect-on-spot (cdar a32) a21)
;;                          (effect-on-spot (caar a32) (my-compose-alists (cdr a32) a21)))))
;;  :hints (("Goal" :expand (my-compose-alists a32 a21)
;;           :do-not '(generalize eliminate-destructors))       ))





;; (thm
;;  (implies (consp a32);t;(list::memberp p a32)
;;           (equal (effect-on-spot (caar a32) (my-compose-alists a32 a21))
;;                  (effect-on-spot (cdar a32) a21)))
;;  :hints (("Goal" :expand (my-compose-alists a32 a21)
;;           :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable; effect-on-spot my-compose-alists
;;                       ))))


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

;; (thm
;;  (IMPLIES
;;  (NOT (bag::MEMBERP (CAR A32) (CDR A32)))
;;  (EQUAL
;;   (EFFECT-ON-SPOT (CDAR A32) A21)
;;   (APPEND (EFFECT-ON-SPOT (CAAR A32)
;;                           (APPEND-ONTO-KEYS (CAAR A32)
;;                                             (EFFECT-ON-SPOT (CDAR A32) A21)))
;;           (EFFECT-ON-SPOT (CAAR A32)
;;                           (MY-COMPOSE-ALISTS (CDR A32) A21)))))


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

;; (thm
;;  (implies
;;   (not (dominates p p2))
;;   (not (dominates p (append p2 p3))))
;;  :hints (("Goal" :in-theory (enable dominates))))

;; (thm
;;  (implies (not (dominates p p2))
;;           (equal (remove-pairs-dominated-by p (append-onto-keys p2 alist))
;;                  (append-onto-keys p2 alist)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; ;what if a pair is dominated after my-compose-alists but wasn't dominated in p?
;; (thm
;;  (equal (remove-pairs-dominated-by p (my-compose-alists alist1 alist2))
;;         (my-compose-alists (remove-pairs-dominated-by p alist1) alist2))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (equal (remove-pairs-dominated-by-list2 p-list (my-compose-alists alist1 alist2))
;;         (my-compose-alists (remove-pairs-dominated-by-list2 p-list alist1) alist2))
;;  :hints (("Goal" :in-theory (disable remove-pairs-dominated-by-list2-of-remove-pairs-dominated-by) ;bzo add ti
;;           :do-not '(preprocess generalize eliminate-destructors))))

;; (thm
;;  (equal (remove-shadowed-pairs2 (my-compose-alists a32 a21))
;;         (my-compose-alists (remove-shadowed-pairs2 a32) (remove-shadowed-pairs2 a21)))
;;  :hints (("Goal" :expand  (REMOVE-SHADOWED-PAIRS2 A32)
;;           :induct t
;;           :in-theory (disable
;; ;                      (:induction remove-shadowed-pairs2)
;;                       )
;;           :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (remove-shadowed-pairs2 (my-compose-alists a32 a21))
;;         (my-compose-alists (remove-shadowed-pairs2 a32) a21))
;;  :hints (("Goal" :expand (REMOVE-SHADOWED-PAIRS2 A32)
;;           :induct t
;;           :in-theory (disable
;;                       remove-shadowed-pairs2
;; ;(:induction remove-shadowed-pairs2)
;;                       )
;;           :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (equal (my-compose-alists (remove-shadowed-pairs2 a32) a21)
;;         (remove-shadowed-pairs2 (my-compose-alists a32 a21)))
;;  :hints (("Goal" :in-theory (disable
;;                              ;(:induction remove-shadowed-pairs2)
;;                              )
;;           :do-not '(generalize eliminate-destructors))))



;; (thm
;;  (equal (remove-shadowed-pairs2 (my-compose-alists a32 a21))
;;         (my-compose-alists (remove-shadowed-pairs2 a32) (remove-shadowed-pairs2 a21)))
;;  :hints (("Goal" :in-theory (disable
;;                              ;(:induction remove-shadowed-pairs2)
;;                              )
;;           :do-not '(generalize eliminate-destructors))))





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

;; (thm
;;  (implies (
;;  (equal (GP-LIST paths (SP p v r))


;; ;not true! consider when a little guy precedes a big guy.
;; (thm
;;  (implies (no-shadowed-pairs alist)
;;           (equal (gp-list (keys alist)
;;                           (mp alist r1 r2))
;;                  (gp-list (vals alist)
;;                           r1)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (gp-list

;;                              )
;;                           (;(:induction remove-shadowed-pairs2)
;;                            )))))

;; ;not true! consider when a little guy precedes a big guy.
;; (thm
;;  (equal (gp-list (keys (remove-shadowed-pairs2 alist))
;;                  (mp alist r1 r2))
;;         (gp-list (vals (remove-shadowed-pairs2 alist))
;;                  r1))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (gp-list

;;                              )
;;                           (;(:induction remove-shadowed-pairs2)
;;                            )))))

;; (thm
;;  (implies (no-shadowed-pairs alist)
;;           (equal (gp-list plist (mp alist r1 r2))

;;                  (mp (effect-on-spot p alist) r1 (gp p r2))

;; ;look at resti                 gp-of-mp




;; ;not true! consider when a little guy precedes a big guy.
;; (thm
;;  (equal (equal (mp alist r1 r2) r3)
;;         (and (equal (clrp-list (keys (remove-shadowed-pairs2 alist)) r2)
;;                     (clrp-list (keys (remove-shadowed-pairs2 alist)) r3))
;;              (equal (gp-list (keys (remove-shadowed-pairs2 alist)) r3)
;;                     (gp-list (range alist) r1)))))





;; (defun all-pairs-dominated-somehow (alist1 alist2)
;;   (if (endp alist1)
;;       t
;;     (and (dominated-by-some (caar alist1) (keys alist2))
;;          (all-pairs-dominated-somehow (cdr alist1) alist2))))

;; (thm
;;  (implies (all-pairs-dominated-somehow alist2 alist1)
;;           (equal (mp alist1 v1 (mp alist2 v2 r))
;;                  (mp alist1 v1 r)))
;;  :hints (("Goal" :in-theory (disable (:induction mp))))
;;  )



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


;; (thm
;;  (equal (gp p (mp a32 (mp a21 r1 r2) r3))
;;         (gp p (mp (my-compose-alists a32 a21) r1 (mp a32 r2 r3))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))





;; (thm
;;  (implies (dominated-by-some p (keys alist1))
;;           (equal (effect-on-spot p (append alist1 alist2))
;;                  (effect-on-spot p alist1)))
;;  :hints (("Goal" :induct t
;;           :in-theory (enable append)
;;           :expand ((EFFECT-ON-SPOT P (APPEND ALIST1 ALIST2))))))

;; (thm
;;  (equal (effect-on-spot p (append alist1 alist2))
;;         (if (dominated-by-some p (keys alist1))
;;             (effect-on-spot p alist1)
;;           (append (effect-on-spot p alist1)
;;                   (effect-on-spot p alist2)))))


;; (thm
;;  (implies (dominated-by-some p (keys alist))
;;           (equal (effect-on-spot p alist)
;;                  (


;; (thm
;;  (implies (not (dominates-some p (keys alist)))
;;           (equal (effect-on-spot p (my-compose-alists alist alist2))
;;                  (if (diverges-from-all p (keys alist))
;;                      nil
;;                    (let ((fd (first-dominator p (keys alist))))
;;                      (let ((tail (nthcdr (len fd) p)))
;;                        (cons (cons nil (append (cdr (assoc fd alist)) tail)
;;                                    )
;;                              nil)))))))


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




;; (thm
;;  (equal (sp p val (mp alist r1 r2))
;;         ;(mp (remove-pairs-dominated-by p alist) r1 (s p val r2))
;;         )
;;  :hints (("Goal" :induct t)))




;; (thm
;;  (equal (equal (gp p r) r)
;;         (or (equal r nil)
;;             (not (consp p))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable gp))))





;;            (dominates domp p)
;;                (list::memberp domp (keys (remove-shadowed-pairs alist)))




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

;; (encapsulate
;;  ()
;;  (local (defthm mp-of-s-1-memberp-case-helper
;;           (implies (and (bag::unique (keys alist))
;;                         (list::memberp a (range alist)))
;;                    (equal (mp alist (s a v r1) r2)
;;                           (s-list (pre-image a alist) (repeat (num-keys-for a alist) v) (mp alist r1 r2))))
;;           :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;                    :in-theory (e/d (mp s-list)
;;                                    ())))))

;; ;Since one spot in r1 can provide a value for many spots in r2, setting A in r1 may require us to set many things in r2.
;; ;( if many spots in r2 are getting the value from spot A in r1).
;;  (defthm mp-of-s-1-memberp-case
;;    (implies (list::memberp a (range alist))
;;             (equal (mp alist (s a v r1) r2)
;;                    (s-list (pre-image a alist) (repeat (num-keys-for a alist) v) (mp alist r1 r2))))
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :in-theory (disable mp-of-s-1-memberp-case-helper)
;;             :use (:instance mp-of-s-1-memberp-case-helper (alist (remove-shadowed-pairs alist)))))))

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

;; (theory-invariant (incompatible (:rewrite s-of-mp-non-memberp-case)
;;                                 (:rewrite mp-of-s-2-memberp-case)))

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

;; (encapsulate
;;  ()
;;  (local (defthm mp-associative-helper
;;           (implies (and (bag::unique (keys a32))
;;                         (bag::unique (keys a21)))
;;                    (equal (mp a32 (mp a21 r1 r2) r3)
;;                           (mp (compose-alists-aux a32 a21) r1 (mp a32 r2 r3))))
;;           :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;                    :in-theory (enable mp)))))

;;  (defthm mp-associative
;;    (equal (mp a32 (mp a21 r1 r2) r3)
;;           (mp (compose-alists a32 a21) r1 (mp a32 r2 r3)))
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :use (:instance  mp-associative-helper ( a21 (remove-shadowed-pairs a21))  ( a32 (remove-shadowed-pairs a32)))
;;             :in-theory (disable mp-associative-helper)))))

;; (defthm mp-commutativity-2
;;   (equal (mp a31 r1 (mp a32 r2 r3))
;;          (mp (alist-diff a32 a31) r2 (mp a31 r1 r3)))
;;   :hints (("Goal" :in-theory (enable mp))))





;; ;;get rid of pp and pp-list?
;; ;;decide what to name functions like diverge, etc.
;; ;;add guards to all of these functions



;; ;; =========================================================================

;; ;; This file extends the ACL2 "records" interface, providing two functions, gp
;; ;; and sp, that have properties that mimic the properties we normally get with
;; ;; g and s, yet with a richer address semantics (paths).

;; ;; =========================================================================


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


;; ;; (thm
;; ;;  (not (list::memberp (car (pp path)) (cdr (pp path))))
;; ;;  :hints (("Goal" :in-theory (enable bag::MEMBERP-OF-CONS))))


;; (defthm unique-pp
;;   (bag::unique (pp path))
;;   ;:rule-classes nil
;;   :hints (("Goal" :in-theory (enable pp
;;                                      bag::unique
;;                                      bag::UNIQUE-OF-CONS)))
;;   )





;; ;make case for when a doesn't match what gets prefixed
;; (encapsulate
;;  ()

;;  (local (defthm memberp-of-cons-and-prelist-fix-one
;;           (implies (list::memberp (cons a x) (prelist-fix a yy))
;;                    (list::memberp x yy))
;;           :hints (("Goal" :in-theory (enable prelist-fix)))))

;;  (local (defthm memberp-of-cons-and-prelist-fix-two
;;           (implies (list::memberp x yy)
;;                    (list::memberp (cons a x) (prelist-fix a yy)))
;;           :hints (("Goal" :in-theory (enable prelist-fix)))))

;;  (defthm memberp-of-cons-and-prelist-fix
;;    (equal (list::memberp (cons a x) (prelist-fix a yy))
;;           (list::memberp x yy))))

;; ;bzo move also rename params on the rule
;; (theory-invariant (incompatible (:rewrite bag::CONS-CAR-ONTO-REMOVE-1-OF-CDR) (:definition bag::remove-1)))

;; (defthm remove-1-of-cons-and-prelist-fix
;;   (equal (bag::remove-1 (cons a x) (prelist-fix a yy))
;;          (prelist-fix a (bag::remove-1 x yy)))
;;   :hints (("Goal" :in-theory (e/d (prelist-fix bag::remove-1
;;                                      ) ( bag::CONS-CAR-ONTO-REMOVE-1-OF-CDR)))))

;; (defthm subbagp-of-prelist-fix-and-prelist-fix
;;   (equal (bag::subbagp (prelist-fix a x)
;;                        (prelist-fix a y))
;;          (bag::subbagp x y))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (prelist-fix
;;                             bag::SUBBAGP-IMPLIES-MEMBERSHIP
;;                             (:induction bag::SUBBAGP)
;;                             bag::SUBBAGP ;drop?
;;                             )
;;                            (bag::SUBBAGP-CDR-REMOVE-1-REWRITE)))))

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






;; ;;
;; ;; List generalizations of gp/sp I'm torn between using two separate lists
;; ;; (for address and values) and using a single alist .. for now we use two
;; ;; lists.
;; ;;


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


;; (thm
;;  (implies (NOT (CONSP MAP))
;;           (equal (ACL2->RCD MAP)
;;                  nil))
;;  :hints (("Goal" :in-theory (enable ACL2->RCD))))









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

;; ;; The holy grail ..

;; ;; Consider the composition of the following maps (A.B) and (C.D):
;; ;;
;; ;;                   C        D
;; ;;                 +---+    +---+
;; ;;                 | u |    | 0 |
;; ;;    A        B   | v |    | 1 |
;; ;;  +---+    +---+ |   | -> |   |
;; ;;  | a |    | w | | w |    | 2 |
;; ;;  | b |    | x | | x |    | 3 |
;; ;;  |   | -> |   | +---+    +---+
;; ;;  | c |    | y |
;; ;;  | d |    | z |
;; ;;  +---+    +---+

;; ;; we need a function that computes the effect of this composition in order to
;; ;; normalize expressions involving mp-list (see mp-list-normalization below).

;; ; (split-map '((a . w) (b . x) (c . y) (d . z)) '((u . 0) (v . 1) (w . 2) (x . 3))) =
;; ; `(((A . 2) (B . 3)) ((U . 0) (V . 1)))

;; ;;
;; ;; Question: how hard is it to write meta-split-map? What hyps are needed?
;; ;;
;; ;; Note, too, that logical inequality of two paths does not give
;; ;; us any real useful information.  The only useful information
;; ;; is (not (dominates p1 p2)) or (disjoint (pp p1) (pp p2)).
;; ;;
;; ;; Since our maps are constructed of using paths as elements,
;; ;; any theorems about disjointness of maps will need to be
;; ;; phrased using something like (pp-list (use map)) ..

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

;; ;; It would be nice if mp-list nests could be represented using some macro
;; ;; like m* :
;; ;;
;; ;; (m* (a b)
;; ;;     (c d)
;; ;;     (e f)
;; ;;     (g h)
;; ;;     rz)
;; ;;
;; ;; of course, acl2 only allows binary macros. (dang!)

;; ;; Define mp-list to take two arguments:
;; ;;
;; ;; (mp-list (cons map r1) r2)

;; ;; (m* (cons (du x) r1) r2)

;; ;; (= (m* (du x) (m* (du y) ra rb) rc)
;; ;;    (met ((mac mbc) (split-map (du x) (du y)))
;; ;;      (m* (v0 pair) ra (m* (v1 pair) rb rc))))

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

;; ;; Below we see a template for the data structure substrate.  This template is
;; ;; much simpler than the one used in the AAMP7 proofs.  Which raises the
;; ;; question: is it just as/more useful?

;; #+joe
;; (
;;  (:type  . type)
;;  (:base  . base)
;;  (:value . (
;;             (:index {..})
;;             ..
;;             ))
;;  )


;; ;; Can you model pointer manipulation transparently using this representation?
;; ;; I think the answer is yes if we allow the "base" field to be the pointer
;; ;; location of the structure. (Changing structure location at the abstract
;; ;; level would be the same as changing a pointer in the implementation)

;; ;; Or, perhaps the "location" stored in the base field should be the set of
;; ;; addresses implementing the body of the structure??  Or even the map from
;; ;; the implementation to the structure??

;; ;; This brings up the question: what _can_ be modeled transparently using this
;; ;; representation??  Can arbitrary manipulations of arbitrary abstract data
;; ;; structures be modeled efficiently?

;; ;; Perhaps a "differential" analysis would produce a suitable mapping
;; ;; function?  If we knew how the pointers changed under the abstract function,
;; ;; we could then map those changes into the implementation ??

;; ;; So, if we can characterize some function as a mapping in the
;; ;; abstract space from A1 to A2:
;; ;;
;; ;; <A1.A2>
;; ;;
;; ;; And we have an abstraction that maps I0 to A0:
;; ;;
;; ;; <I0.A0>
;; ;;
;; ;; Then the implementation effect of the abstract function can be modeled by
;; ;; reflecting the abstract mapping <A1.A2> back into the implementation. (?)

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

;; ;;
;; ;; An example, challenge problem
;; ;;

;; ;; Define a function that operates on a simple list data structure in memory.
;; ;; Have the function insert an element into the list.

;; ;; Can you show that that function maps to an abstract representation
;; ;; of the same functionality?

;;

;; ;; How about a little object-orientation ..

;; (defstructure zed
;;   a
;;   b
;;   :extends (foo
;;             :pred foo-p
;;             :keys foo-keys))


;; (update-zed zed
;;             :x v
;;             :y q
;;             :a 3)

;; = (update-zed (update-foo :x v :y q) :a 3)


;; (defun zed-keys
;;   (append (foo-keys)
;;           (list a b)))

;; (defun zed-p (st)
;;   (and (foo-p st)
;;        (integerp (a-val st))
;;        (listp (b-val st))))

;; (defarray fred
;;   :size 10
;;   :type foop
;;   :default value)

;;



;;
;; (thm
;;    (implies (diverge p1 p2)
;;             (equal (sp p1 val (mp (remove-pairs-dominated-by p2 alist) r1 r2))
;;                    (sp p1 val (mp alist r1 r2))))
;;    :hints (("Goal" :in-theory (enable diverge))))


;; (thm
;;  (IMPLIES (AND (NOT (DOMINATES P1 P2))
;;                (NOT (DOMINATES P2 P1)))
;;           (EQUAL (SP P1 NIL
;;                      (MP (REMOVE-PAIRS-DOMINATED-BY P2 ALIST)
;;                               R1 R2))
;;                  (SP P1 NIL (MP ALIST R1 R2)))))



;; (thm
;;  (implies (not (dominates p2 p1))
;;           (equal (sp p1 val (mp (remove-pairs-dominated-by p2 alist) r1 r2))
;;                  (sp p1 val (mp alist r1 r2))))
;;  :hints (("Goal" :in-theory (enable diverge)
;;           :cases ((diverge p1 p2)))))

;; ;remove-pairs-dominated-by
;;                              ))))





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

(theory-invariant (incompatible (:rewrite sp-to-clrp) (:definition clrp)))

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

;; jcd - added this congruence
(defcong list::equiv equal (clrp-list paths r) 1
  :hints(("Goal" :in-theory (enable clrp-list)
          :induct (list::len-len-induction paths paths-equiv))))

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

(theory-invariant (incompatible (:rewrite clrp-of-clrp-list)
                                (:rewrite clrp-list-of-clrp)))

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

(theory-invariant (incompatible (:rewrite sp==r) (:definition clrp))) ;bzo is this what we want?

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


;;
;;
;; meta rules
;;
;;

;; These rules are very similar to the rules in bags/eric-meta.lisp.
;; See the documentation in that file.  A lot more could be done here.
;; For instance, we don't really follow chains of domination now.

;; These rules make use of some similarites between the path functions
;; and the bag functions.  Here are some pairs of similar functions:

;; (diverge a b) ~ (not (equal a b))
;; (unique x) ~ (all-diverge x)
;; (disjoint x y) ~ (all-diverge-from-all x y)
;; (memberp a x) ~ (dominates-some a x), (dominated-by-some a x)



;This evaluator extends the syntax-ev evaluator, so we can lift the
;theorems about syntax-ev to theorems about this evaluator.

;bzo get rid of some of this stuff from this

(syn::defevaluator path-syntax-ev path-syntax-ev-list
  (
   (hide x)
   (bag::hide-unique list)
   (bag::hide-subbagp x y)
   (bag::hide-disjoint x y)
   (bag::hide-memberp a x)
   (bag::perm x y)
   (bag::unique list)
;   (implies-if a term)
   (if a b c)
   (consp x)
   (true-listp x)
   (binary-append x y)
   (cons a b)
   (bag::meta-subbagp list1 list2)
   (bag::remove-bag x list)
   (bag::meta-remove-bag x list)
   (bag::remove-1 x list)
;   (meta-remove-1 x list)
   (bag::unique-subbagps x y list)
   (bag::unique-memberps x y list)
   (bag::subbagp-pair x1 x2 list1 list2)
   (bag::meta-memberp x list)
   (bag::any-subbagp x list) ;remove this?
   (list::finalcdr x)
   (acl2::true-list-fix x)
   (bag::subbagp x y)
   (bag::memberp a x)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
   (acl2::member-equal a x)
   (bag::disjoint x y)
;   (synp vars form term)
   (equal x y)
   (diverge a b)
   (all-diverge x)
   (all-diverge-from-all x y)
   ))

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

;; Ways to show (diverge a b):
;;   Find (all-diverge BLAH), and then show (unique-memberps a b BLAH).
;;   Find (all-diverge-from-all BLAH1 BLAH2), and then show (memberp a BLAH1) and (memberp b BLAH2).
;;   Find (all-diverge-from-all BLAH1 BLAH2), and then show (memberp a BLAH2) and (memberp b BLAH1).

(defignored show-diverge-from-type-alist bag::a (a b n type-alist whole-type-alist)
  (declare (type t a b type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
;           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp a) ;drop?
                              (pseudo-termp b)
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))

  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'all-diverge)
                        (bag::ts-non-nil (cadr entry))
                        (bag::show-unique-memberps-from-type-alist a b (cadr fact) n whole-type-alist n whole-type-alist 1)
                        (equal nil (cddr fact)))
                   (and (equal (car fact) 'all-diverge-from-all)
                        (bag::ts-non-nil (cadr entry))
                        (or (and (bag::show-memberp-from-type-alist a (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (bag::show-memberp-from-type-alist b (caddr fact) n whole-type-alist whole-type-alist 1))
                            (and (bag::show-memberp-from-type-alist a (caddr fact) n whole-type-alist whole-type-alist 1)
                                 (bag::show-memberp-from-type-alist b (cadr fact) n whole-type-alist whole-type-alist 1)))
                        (equal nil (cdddr fact)))))
          (show-diverge-from-type-alist a b n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-diverge-from-type-alist 1 bag::a (a b n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-diverge-from-type-alist
                              bag::hyp-for-show-memberp-from-type-alist-irrelevant
                              bag::hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-diverge-from-type-alist bag::a (a b n type-alist whole-type-alist)
  (declare (type t a b type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
;           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp a) ;drop?
                              (pseudo-termp b)
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'all-diverge)
                        (bag::ts-non-nil (cadr entry))
                        (equal nil (cddr fact))
                        (bag::conjoin-fact-and-hyp
                         fact (bag::hyp-for-show-unique-memberps-from-type-alist
                               a b (cadr fact) n whole-type-alist n whole-type-alist 1)))
                   (and (equal (car fact) 'all-diverge-from-all)
                        (bag::ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (or (bag::conjoin-fact-and-two-hyps
                             fact (bag::hyp-for-show-memberp-from-type-alist
                                   a (cadr fact) n whole-type-alist whole-type-alist 1)
                             (bag::hyp-for-show-memberp-from-type-alist
                              b (caddr fact) n whole-type-alist whole-type-alist 1))
                            (bag::conjoin-fact-and-two-hyps
                             fact (bag::hyp-for-show-memberp-from-type-alist
                                   a (caddr fact) n whole-type-alist whole-type-alist 1)
                             (bag::hyp-for-show-memberp-from-type-alist
                              b (cadr fact) n whole-type-alist whole-type-alist 1))))))
          (hyp-for-show-diverge-from-type-alist a b n (cdr type-alist) whole-type-alist)))))


(defirrelevant hyp-for-show-diverge-from-type-alist 1 bag::a (a b n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-diverge-from-type-alist
                              bag::hyp-for-show-memberp-from-type-alist-irrelevant
                              bag::hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))

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


(set-state-ok t)

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


;;tests:

(encapsulate
 ()
 (local (defthm tester0
          (implies (and (all-diverge (append x y z))
                        (bag::subbagp x- x)
                        (bag::subbagp x-- x-)
                        (list::memberp a x--)
                        (bag::subbagp (append y- blah) y)
                        (list::memberp b y-))
                   (diverge a b))
          :hints (("Goal" :in-theory '(meta-rule-to-show-diverge))))))


(encapsulate
 ()
 (local (defthm tester1
          (implies (and (all-diverge-from-all (append x z) (cons aa y))
                        (bag::subbagp x- x)
                        (bag::subbagp x-- x-)
                        (list::memberp a x--)
                        (bag::subbagp (append y- blah) y)
                        (list::memberp b y-))
                   (diverge a b))
          :hints (("Goal" :in-theory '(meta-rule-to-show-diverge))))))

;;
;;
;; :meta rule for all-diverge
;;
;;

;; Ways to show (all-diverge x):
;;   Find (all-diverge BLAH), and the show (subbag x BLAH).

(defignored show-all-diverge-from-type-alist bag::a (x n type-alist whole-type-alist)
  (declare (type t type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
;           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x) ;drop?
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (and (equal (car fact) 'all-diverge)
                    (bag::ts-non-nil (cadr entry))
                    (bag::show-subbagp-from-type-alist x (cadr fact) n whole-type-alist whole-type-alist 1)
                    (equal nil (cddr fact))))
          (show-all-diverge-from-type-alist x n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-all-diverge-from-type-alist 1 bag::a (x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-all-diverge-from-type-alist
                              bag::hyp-for-show-subbagp-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-all-diverge-from-type-alist bag::a (x n type-alist whole-type-alist)
  (declare (type t type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (and (equal (car fact) 'all-diverge)
                    (bag::ts-non-nil (cadr entry))
                    (equal nil (cddr fact))
                    (bag::conjoin-fact-and-hyp
                     fact  (bag::hyp-for-show-subbagp-from-type-alist
                            x (cadr fact) n whole-type-alist whole-type-alist 1))
                    ))
          (hyp-for-show-all-diverge-from-type-alist x n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-all-diverge-from-type-alist 1 bag::a (x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-all-diverge-from-type-alist
                              bag::hyp-for-show-subbagp-from-type-alist-irrelevant
                              ))))


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

(syn::defevaluator meta-twins-ev meta-twins-ev-list
  ((all-diverge a)
   (cons a b)))

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


(encapsulate
 ()
 (local (defthm tester0
          (implies (and (all-diverge (append x z (cons aa y)))
                        (bag::subbagp x- x)
                        (bag::subbagp (append x-- hoooo) x-)
                        (bag::subbagp foo x--))
                   (all-diverge foo))
          :hints (("Goal" :in-theory '(meta-rule-to-show-all-diverge))))))

(encapsulate
 ()
 (local (defthm tester1
          (implies (and (all-diverge (append x z (cons aa y)))
                        (bag::subbagp x- x)
                        (bag::subbagp (append x-- hoooo) x-)
                        (bag::subbagp (append foo foo3 foo2) x--))
                   (all-diverge (append foo foo2)))
          :hints (("Goal" :in-theory '(meta-rule-to-show-all-diverge))))))


;;
;;
;; all-diverge-from-all
;;
;;

;; Ways to show (all-diverge-from-all x y):
;;   Find (all-diverge BLAH), and then show (unique-subbagps x y BLAH).
;;   Find (all-diverge-from-all BLAH1 BLAH2), and then show (subbagp x BLAH1) and (subbagp y BLAH2).
;;   Find (all-diverge-from-all BLAH1 BLAH2), and then show (subbagp x BLAH2) and (subbagp y BLAH1).

(defignored show-all-diverge-from-all-from-type-alist bag::a (x y n type-alist whole-type-alist)
  (declare (type t type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x) ;drop?
                              (pseudo-termp y) ;drop?
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'all-diverge)
                        (bag::ts-non-nil (cadr entry))
                        (bag::show-unique-subbagps-from-type-alist x y (cadr fact) n whole-type-alist whole-type-alist 1)
                        (equal nil (cddr fact)))
                   (and (equal (car fact) 'all-diverge-from-all)
                        (bag::ts-non-nil (cadr entry))
                        (or (and (bag::show-subbagp-from-type-alist x (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (bag::show-subbagp-from-type-alist y (caddr fact) n whole-type-alist whole-type-alist 1))
                            (and (bag::show-subbagp-from-type-alist x (caddr fact) n whole-type-alist whole-type-alist 1)
                                 (bag::show-subbagp-from-type-alist y (cadr fact) n whole-type-alist whole-type-alist 1)))
                        (equal nil (cdddr fact)))))
          (show-all-diverge-from-all-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-all-diverge-from-all-from-type-alist 1 bag::a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-all-diverge-from-all-from-type-alist
                              bag::hyp-for-show-subbagp-from-type-alist-irrelevant
                              bag::hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-all-diverge-from-all-from-type-alist bag::a (x y n type-alist whole-type-alist)
  (declare (type t type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x) ;drop?
                              (pseudo-termp y) ;drop?
                              (equal n (bag::usb16-fix (len whole-type-alist)))
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'all-diverge)
                        (bag::ts-non-nil (cadr entry))
                        (equal nil (cddr fact))
                        (bag::conjoin-fact-and-hyp
                         fact (bag::hyp-for-show-unique-subbagps-from-type-alist
                               x y (cadr fact) n whole-type-alist whole-type-alist 1))
                        )
                   (and (equal (car fact) 'all-diverge-from-all)
                        (bag::ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (or (bag::conjoin-fact-and-two-hyps
                             fact (bag::hyp-for-show-subbagp-from-type-alist
                                   x (cadr fact) n whole-type-alist whole-type-alist 1)
                             (bag::hyp-for-show-subbagp-from-type-alist
                              y (caddr fact) n whole-type-alist whole-type-alist 1))
                            (bag::conjoin-fact-and-two-hyps
                             fact (bag::hyp-for-show-subbagp-from-type-alist
                                   x (caddr fact) n whole-type-alist whole-type-alist 1)
                             (bag::hyp-for-show-subbagp-from-type-alist
                              y (cadr fact) n whole-type-alist whole-type-alist 1))))))
          (hyp-for-show-all-diverge-from-all-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-all-diverge-from-all-from-type-alist 1 bag::a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-all-diverge-from-all-from-type-alist
                              bag::hyp-for-show-subbagp-from-type-alist-irrelevant
                              bag::hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              ))))

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


(encapsulate
 ()
 (local (defthm tester0
          (implies (and (all-diverge (append x z (cons aa y) (append w www)))
                        (bag::subbagp x- x)
                        (bag::subbagp x-- x-)
                        (bag::subbagp foo x--)
                        (bag::subbagp w- w)
                        (bag::subbagp bar w))
                   (all-diverge-from-all foo bar))
          :hints (("Goal" :in-theory '(meta-rule-to-show-all-diverge-from-all))))))


(encapsulate
 ()
 (local (defthm tester1
          (implies (and (all-diverge-from-all (append x z (cons aa y)) (append w www))
                        (bag::subbagp x- (cons aa y))
                        (bag::subbagp x-- x-)
                        (bag::subbagp foo x--)
                        (bag::subbagp w- w) ;extra
                        (bag::subbagp (append bar strongbag) w))
                   (all-diverge-from-all foo bar))
          :hints (("Goal" :in-theory '(meta-rule-to-show-all-diverge-from-all))))))


;; meta rule stuff:

;; ;maybe we need a syntax-car and syntax-cdr and a syntax-consp?

;; (syntax-diverge '(cons 'a x) '(cons 'b y))
;; (syntax-diverge '(cons 'a x) '(cons 'b y))
;; (syntax-diverge '(cons a (cons 'b x)) '(append (cons a2 '(not-b)) z))

;; ;x and y are terms (nests of conses and appends).
;; ;this function determines whether we know synatctically that x and y diverge (because x any y have different constants at corresponding locations...)
;; (defun syntax-diverge (x y)
;;   (if (and (equal (car x) 'quote)  ;call syntax-consp?
;;            (not (consp (cadr x))))
;;       nil
;;     (if (and (equal (car y) 'quote)
;;              (not (consp (cadr y))))
;;         nil
;;       (if (equal (car x) 'cons)
;;           (or (syntax-not-equal (cadr x) (syntax-car y))
;;               (syntax-diverge



;; (syntax-dominates 'x '(append x y))
;; (syntax-dominates ''(a) '(append (cons 'a b) y)) ; hmmm.... maybe we do want append and cons normalization on.  we would have to have it for bags if we used the bag constructors for those.  paths really are built of cons and append...

;; (defun syntax-dominates (x y)

;; ;will DIVERGE-OF-CONS-AND-CONS be too expensive too keep enabled? it can do a lot of the work...
;; ;but we need syntax diverge for our rules?

;; (thm
;;  (diverge (cons 'a x) (cons 'b y)))

;; ;depends on list normalization...
;; (thm
;;  (diverge (cons 'a x) (append (cons 'b y) z)))

;; ;we know they diverge because their second arguments differ
;; (thm
;;  (diverge (cons a (cons 'b x)) (append (cons a2 '(not-b)) z)))


;; (thm
;;  (implies (and (dominates '(a b) q) ;what if this was (dominates (cons 'a (cons 'b x)) q)?
;;                (dominates q p)
;;                (dominates '(c) q2)
;;                (dominates q2 r2)
;;                (dominates r2 p2) ;what if this was (dominates (append r2 r22) p2)
;;                )
;;           (diverge p p2)))


;; ;possible todos:
;; ;add a syntax-diverge test?
;; ;   Find (all-diverge-from-all BLAH1 BLAH2) and show (dominated-by-some p BLAH1) and (dominated-by-some q BLAH2).
;; ;   Find (all-diverge-from-all BLAH1 BLAH2) and show (dominated-by-some q BLAH1) and (dominated-by-some p BLAH2).
;; ;   Easy case: Discover that (syntax-divegre p q)




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

;; (thm
;;  (IMPLIES (AND (CONSP A31)
;;                (not (ALL-DOMINATED-BY-SOME paths (cdr paths2)))
;;                (ALL-DOMINATED-BY-SOME paths path2))
;;           blah)
;;  :hints (("Goal" :induct t)))


(defthm keys-of-cdr
  (equal (keys (cdr alist))
         (cdr (keys alist))))

(defthmd cdr-of-keys
  (equal (cdr (keys alist))
         (keys (cdr alist))))

(in-theory (disable keys))

(theory-invariant (incompatible (:rewrite keys-of-cdr) (:rewrite cdr-of-keys)))
(theory-invariant (incompatible (:rewrite keys-of-cdr) (:definition keys)))

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

;(defcong bag::perm equal (clrp-list alist r2) 1 :hints (("Goal" :in-theory (enable clrp-list))))

;; (thm
;;  (equal (CLRP p (MP ALIST R1 R2))
;;         blah))

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


;; (thm
;;  (implies (acl2::dominates x (append y z))
;;           (and (acl2::dominates x y)
;;                (acl2::dominates (nthcdr (len y) x) z)))
;;  :hints (("Goal" :in-theory (enable acl2::dominates))))


;; (thm
;;  (implies (<= (len y) (len x))
;;           (implies (dominates x (append y z))
;;                    (and (list::equiv (acl2::firstn (len y) x) y)
;;                         (dominates (nthcdr (len y) x) z))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable dominates
;;                              ;append
;;                              acl2::firstn
;;                              nthcdr
;;                              ))))


;untrue
;; (thm
;;  (implies (not (dominates x y))
;;           (not (DOMINATES x (APPEND Y Y2)))))


;bzo take pains to make sure firstn and nthcdr don't appear the user's proofs?
;He doesn't want to see them?


;; (thm
;;  (IMPLIES (AND (NOT (EQUAL N1 N2))
;;                (integerp n1)
;;                (integerp n2)
;;                (<= 0 n1)
;;                (<= 0 n2)
;;                (EQUAL (list::FIRSTN N1 X)
;;                       (list::FIRSTN N2 X))
;;                (< N1 N2))
;;           (<= (LEN X) N1))
;;  :hints (("Goal" :in-theory (enable not-equal-from-len-not-equal))))


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

(encapsulate
 ()
 (local (defthm fw
          (implies (and (<= (len x) n)
                        (integerp n)
                        (not (dominates x (list::firstn n y))))
                   (not (dominates x y)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable dominates list::firstn)))))

 (local (defthm bk
          (IMPLIES (AND (<= (LEN X) N)
                        (INTEGERP N)
                        (DOMINATES X (list::FIRSTN N Y)))
                   (DOMINATES X Y))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable dominates list::firstn)))))

 (defthm dominates-of-firstn-two
   (equal (dominates x (list::firstn n y))
          (if (and (integerp n)
                   (<= (len x) n))
              (dominates x y)
            (not (consp x))))
   :hints (("Goal" :use (bk fw
                            (:instance not-dominates-from-<-of-len-and-len (y  (list::FIRSTN N Y)))) :in-theory (disable bk fw)))))




;; (thm dominates-of-firstn-one
;;   (equal (dominates (list::firstn n y) x)
;;          (if (and (integerp n)
;;                   (<= (len x) n))
;;              (dominates x y)
;;            (not (consp x))))
;;   :hints (("Goal" :use (:instance not-dominates-from-<-of-len-and-len (y  (list::FIRSTN N Y))))))


;; (thm
;;  (implies (and (diverge x y)
;;                (<= (len x) (len y))
;; ;               (<= (len x) n)
;;                )
;;           (diverge x (list::firstn n y)))
;;  :hints (("Goal" :in-theory (enable list::firstn
;;                                     diverge))))

;turn off most rules about diverges,etc. here?


(in-theory (disable all-diverge-of-cons)) ;this is analogous to how we disabled many of the basic theorems about bags

;characterize effect-on-spot of pair-with-selves

;These should be disabled!
(in-theory (disable bag::NOT-SUBBAGP-OF-CONS-FROM-NOT-SUBBAGP
                    bag::SUBBAGP-OF-CONS
                    DOMINATES-FROM-equiv-hack
                    UNIQUE-MEMBERPS-OF-CONS))

;; (defun number-of-divergers (p paths)
;;   (if (endp paths)


;; (thm
;;  (equal (effect-on-spot p (pair-with-selves vars))
;;         (acl2::repeat ;(len vars) should be the number of divergers
;;                       (cons nil p)))
;;  :hints (("Goal" :in-theory (enable effect-on-spot pair-with-selves acl2::repeat ;len
;;                                     ))))

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



;handle this?
;;   (ALL-DIVERGE (LIST THEDRIVER THEITEM LEFTNODE NIL UPNODE
;;                            (GP '(:UPOFFSET) (GP THEDRIVER ST))
;;                            (GP '(:UPOFFSET) (GP THEDRIVER ST))
;;                            (GP '(:UPOFFSET) (GP THEDRIVER ST))))

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
(theory-invariant (incompatible (:rewrite MP-OF-APPEND)
                                (:rewrite mp-collect)))

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


;;
;;
;;meta rule for not equal, from all diverge
;;
;;


(defignored show-not-equal-from-type-alist-path-version bag::a (x y n type-alist whole-type-alist)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (equal n (bag::usb16-fix (len whole-type-alist))))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :guard-hints (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (and (equal 'all-diverge (car fact))
                    (bag::ts-non-nil (cadr entry))
                    (bag::show-unique-memberps-from-type-alist x y (cadr fact) n whole-type-alist n whole-type-alist 1)
                    (equal nil (cdddr fact))))
          (show-not-equal-from-type-alist-path-version x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-not-equal-from-type-alist-path-version 1 bag::a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-not-equal-from-type-alist-path-version
                              bag::hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-not-equal-from-type-alist-path-version bag::a (x y n type-alist whole-type-alist)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (equal n (bag::usb16-fix (len whole-type-alist))))
                  :guard-hints (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(preprocess generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (and (equal 'all-diverge (car fact))
                    (bag::ts-non-nil (cadr entry))
                    (equal nil (cdddr fact))
                    (bag::conjoin-fact-and-hyp
                     fact (bag::hyp-for-show-unique-memberps-from-type-alist
                           x y (cadr fact) n whole-type-alist n whole-type-alist 1))
                     ))
          (hyp-for-show-not-equal-from-type-alist-path-version x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-not-equal-from-type-alist-path-version 1 bag::a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-not-equal-from-type-alist-path-version
                              bag::hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))


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


(in-theory (disable GP-OF-APPEND
                    DOMINATED-BY-SOME-OF-CONS
                    DIVERGES-FROM-ALL-WHEN-DIVERGES-FROM-ALL-OF-CDR))


(in-theory (disable SP-EQUAL-REWRITE)) ;this should stay disabled


;;
;; All of our reasoning should be done using gp/sp
;;

(in-theory (disable gp sp clrp-list))

(theory-invariant (incompatible (:rewrite g-to-gp) (:definition gp)))

(theory-invariant (incompatible (:rewrite g-to-gp) (:rewrite open-gp)))

(theory-invariant (incompatible (:rewrite s-to-sp) (:definition sp)))

(theory-invariant (incompatible (:rewrite clrp-to-clrp-list) (:definition clrp-list)))

;; This is causing problems.

(defmacro path-representation-theory ()
  `(e/d (DIVERGES-FROM-ALL clrp-to-clrp-list sp==r)
        (gp sp clrp-list)))

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

(defequiv pperm)

(defcong pperm pperm (cons a x) 2)
(defcong pperm pperm (append x y) 1)
(defcong pperm pperm (append x y) 2)

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

(defcong pperm equal (clrp-list plist r) 1
  :hints (("goal" :in-theory (enable perm-clp-list))))

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

(theory-invariant (incompatible (:rewrite s-to-sp) (:rewrite open-sp)))

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

(theory-invariant (incompatible (:rewrite clrp-singleton-becomes-clr) (:rewrite clr-becomes-clrp-singleton)))

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

(theory-invariant (incompatible (:rewrite sp-to-clrp)
                                (:rewrite clrp-of-cons)
                                ))

(defthm diverge-of-non-consp-one-cheap
  (implies (not (consp x))
           (equal (diverge x y) nil))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))
