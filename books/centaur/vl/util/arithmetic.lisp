; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")

; BOZO Lib.  This book should only be locally included, and because of that you
; should never define a function here.  Instead, widely useful functions should
; generally be defined in defs.lisp.  Eventually, these lemmas should be moved
; into more other libraries.

(deflabel pre-arithmetic)

(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/bitops/integer-length" :dir :system)
(include-book "cutil/deflist" :dir :system)
(include-book "cutil/defrule" :dir :system)


;; BOZO how much of this is still needed, given the new Tau system?
(defrule rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

(defrule integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defrule natp-when-posp
  (implies (posp x)
           (natp x)))

(defrule negative-when-natp
  (implies (natp x)
           (equal (< x 0)
                  nil)))

(defrule natp-of-one-plus
  (implies (natp x)
           (natp (+ 1 x))))

(defrule integerp-of-plus
  (implies (and (integerp a)
                (integerp b))
           (integerp (+ a b))))

(def-ruleset basic-arithmetic-rules
  (set-difference-equal (current-theory :here)
                        (current-theory 'pre-arithmetic)))

(add-to-ruleset basic-arithmetic-rules
                '(acl2::rationalp-implies-acl2-numberp
                  default-+-1
                  default-+-2
                  default-<-1
                  default-<-2
                  default-unary-minus
                  default-*-1
                  default-*-2))

(include-book "subsetp-equal")

;; BOZO question: how much of this do we really need?
(include-book "data-structures/list-defthms" :dir :system)

(include-book "misc/hons-help" :dir :system)

(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/ks/explode-atom" :dir :system)


(defun dec-dec-induct (k n)
  (if (zp k)
      nil
    (if (zp n)
        nil
      (dec-dec-induct (- k 1) (- n 1)))))


(in-theory (disable
            ;; I've had performance problems with these:
            (:type-prescription acl2::consp-append . 1)
            (:type-prescription acl2::consp-append . 2)
            ;; This seems like a lousy rule and causes performance problems:
            acl2::remove-equal-non-member-equal
            ;; My nomination for worst rule in the history of ACL2.  Causes
            ;; terrible goal blowup whenever state is involved in proofs that
            ;; have forcing round and just generally is a terrible idea.
            state-p1-forward
            ;; These just ought to be disabled
            o<
            o-p
            acl2-count
            explode-atom
            string-append
            string-append-lst
            subseq
            subseq-list
            intersectp-equal
            intersection-equal
            no-duplicatesp-equal
            set-difference-equal

            ;; now disabled due to std/alists/top
            ;; pairlis$
            ;; alistp
            ;; strip-cars
            ;; strip-cdrs

            ;; Now disabled due to std/lists/top
            ;append
            ;make-character-list
            ;acl2::take-redefinition
            ;nthcdr

            true-listp
            string-listp
            symbol-listp
            character-listp

            assoc-equal

            hons-shrink-alist
            make-fal))


(defsection true-listp

  (local (in-theory (enable true-listp)))

  (defrule true-listp-when-not-consp
    (implies (not (consp x))
             (equal (true-listp x)
                    (not x))))

  (defrule true-listp-of-cons
    (equal (true-listp (cons a x))
           (true-listp x)))

  (defrule consp-under-iff-when-true-listp
    (implies (true-listp x)
             (iff (consp x)
                  x))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection acl2-count

  (local (in-theory (enable acl2-count o< o-p)))

  (defrule acl2-count-positive-when-consp
    (implies (consp x)
             (< 0 (acl2-count x)))
    :rule-classes ((:type-prescription) (:linear)))

  (defrule acl2-count-of-cons
    (equal (acl2-count (cons a x))
           (+ 1 (acl2-count a) (acl2-count x))))

  (defrule acl2-count-of-cdr
    (and (implies (consp x)
                  (< (acl2-count (cdr x))
                     (acl2-count x)))
         (<= (acl2-count (cdr x))
             (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-car
    (and (implies (consp x)
                  (< (acl2-count (car x))
                     (acl2-count x)))
         (<= (acl2-count (car x))
             (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-cdr-same-fc
    (implies (equal (acl2-count (cdr x))
                    (acl2-count x))
             (not (consp x)))
    :rule-classes :forward-chaining)

  (defrule acl2-count-zero-when-true-listp
    (implies (true-listp x)
             (equal (equal 0 (acl2-count x))
                    (not x))))

  (defrule acl2-count-zero-when-stringp
    (implies (stringp x)
             (equal (equal 0 (acl2-count x))
                    (equal x ""))))

  (defrule o<-when-natps
    (implies (and (natp x)
                  (natp y))
             (equal (o< x y)
                    (< x y))))

  (defrule o-p-when-natp
    (implies (natp x)
             (o-p x)))

  (defrule acl2-count-of-list-fix-weak
    (<= (acl2-count (list-fix x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-append
    (equal (acl2-count (append x y))
           (+ (acl2-count (list-fix x))
              (acl2-count y)))
    :enable append))



(defsection nthcdr

  (local (in-theory (enable nthcdr)))

  (defrule nthcdr-of-increment
    ;; Goofy rule which may be useful when nthcdr is used in recursive
    ;; definitions.  This may be unsuitable for std/lists.
    (implies (natp n)
             (equal (nthcdr (+ 1 n) x)
                    (cdr (nthcdr n x)))))

  (defrule acl2-count-of-nthcdr
    ;; BOZO eventually move to std/lists?
    (equal (acl2-count (nthcdr n x))
           (if (<= (nfix n) (len x))
               (- (acl2-count x)
                  (acl2-count (take n x)))
             0))))



(defsection nth

  (local (in-theory (enable nth)))

  (defrule nth-of-atom
    (implies (not (consp x))
             (equal (nth n x)
                    nil)))

  (defrule nth-of-cons
    (equal (nth n (cons a x))
           (if (zp n)
               a
             (nth (- n 1) x))))

  (defrule nth-when-zp
    (implies (zp n)
             (equal (nth n x)
                    (car x))))

  (defrule nth-when-too-big
    (implies (<= (len x) (nfix n))
             (equal (nth n x)
                    nil))))


(defsection last

  (local (in-theory (enable last)))

  (defrule last-when-atom
    (implies (atom x)
             (equal (last x)
                    x)))

  (defrule last-of-cons
    (equal (last (cons a x))
           (if (atom x)
               (cons a x)
             (last x))))

  (defrule last-under-iff
    (iff (last x)
         x))

  (defrule consp-of-last
    (equal (consp (last x))
           (consp x)))

  (defrule acl2-count-of-last-weak
    (<= (acl2-count (last x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-last-strong
    (implies (consp (cdr x))
             (< (acl2-count (last x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-last-same
    (equal (equal (acl2-count x) (acl2-count (last x)))
           (atom (cdr x)))))



(defrule butlast-under-iff
  ;; Hypothesis was changed for ACL2 Version 5.1 from (force (integerp n)) by
  ;; Matt Kaufmann, because a change to butlast made this fail, e.g., under the
  ;; bindings ((n -1) (x nil)).
  (implies (force (natp n))
           (iff (butlast x n)
                (< n (len x))))
  :enable butlast)



(defsection prefixp

  (local (in-theory (enable prefixp)))

  (defrule prefixp-impossible-by-len
    ;; not sure whether this is a good rule that should go into std/lists since
    ;; we have len-when-prefixp...
    (implies (< (len x) (len p))
             (equal (prefixp p x)
                    nil))))


(encapsulate
  ()
  (local (in-theory (enable alistp)))

  (defrule alistp-of-insert
    (implies (and (alistp x)
                  (consp a))
             (alistp (sets::insert a x)))
    :enable sets::primitive-rules)

  (defrule alistp-of-mergesort
    (implies (alistp x)
             (alistp (sets::mergesort x)))))



(defsection hons-assoc-equal

  (local (in-theory (enable hons-assoc-equal)))

  (defrule hons-assoc-equal-when-atom
    (implies (atom alist)
             (equal (hons-assoc-equal a alist)
                    nil)))

  (defrule hons-assoc-equal-of-cons
    (equal (hons-assoc-equal key (cons entry map))
           (if (and (consp entry)
                    (equal key (car entry)))
               entry
             (hons-assoc-equal key map))))

  (defrule hons-assoc-equal-of-hons-acons
    (equal (hons-assoc-equal key (hons-acons key2 val map))
           (if (equal key key2)
               (cons key val)
             (hons-assoc-equal key map))))

  (defrule consp-of-hons-assoc-equal
    (equal (consp (hons-assoc-equal x alist))
           (if (hons-assoc-equal x alist)
               t
             nil)))

  (defrule car-of-hons-assoc-equal
    (equal (car (hons-assoc-equal key alist))
           (if (hons-assoc-equal key alist)
               key
             nil)))

  (defrule assoc-equal-elim
    (implies (force (alistp alist))
             (equal (assoc-equal key alist)
                    (hons-assoc-equal key alist)))
    :enable assoc-equal))



(defrule hons-assoc-equal-of-make-fal
  (equal (hons-assoc-equal a (make-fal x y))
         (or (hons-assoc-equal a x)
             (hons-assoc-equal a y)))
  :enable make-fal)



(defsection hons-shrink-alist

  (local (in-theory (enable hons-shrink-alist)))

  (defrule hons-shrink-alist-when-not-consp
    (implies (atom x)
             (equal (hons-shrink-alist x y)
                    y)))

  (defrule hons-shrink-alist-of-cons
    (equal (hons-shrink-alist (cons a x) y)
           (cond ((atom a)
                  (hons-shrink-alist x y))
                 ((hons-assoc-equal (car a) y)
                  (hons-shrink-alist x y))
                 (t
                  (hons-shrink-alist x (cons a y))))))

  (defrule alistp-of-hons-shrink-alist
    (implies (alistp ans)
             (alistp (hons-shrink-alist x ans))))

  (defrule assoc-equal-of-hons-shrink-alist
    (equal (hons-assoc-equal a (hons-shrink-alist x ans))
           (or (hons-assoc-equal a ans)
               (hons-assoc-equal a x))))

  ;; BOZO probably want to redo this stuff with alist-keys instead of strip-cars

  (local (defrule l0
           (implies (alistp x)
                    (iff (hons-assoc-equal a x)
                         (member-equal a (strip-cars x))))))

  (local (defrule l1
           (implies (and (alistp x)
                         (alistp y))
                    (iff (member-equal a (strip-cars (hons-shrink-alist x y)))
                         (or (member-equal a (strip-cars x))
                             (member-equal a (strip-cars y)))))))

  (defrule strip-cars-of-hons-shrink-alist-under-set-equiv
    (implies (and (alistp x)
                  (alistp y))
             (set-equiv (strip-cars (hons-shrink-alist x y))
                         (strip-cars (append x y))))
    :hints((set-reasoning)))

  (local (defrule l2
           (implies (and (not (member-equal a (strip-cars x)))
                         (not (member-equal a (strip-cars y))))
                    (not (member-equal a (strip-cars (hons-shrink-alist x y)))))))

  (defrule subsetp-equal-of-strip-cars-of-hons-shrink-alist
    (subsetp-equal (strip-cars (hons-shrink-alist x nil))
                   (strip-cars x))
    :hints((set-reasoning))))



(defsection intersectp-equal

  (local (in-theory (enable intersectp-equal)))

;; We used to have lots of stuff here, but it was all redundant with other ACL2
;; libraries, especially data-structures/no-duplicates and misc/equal-sets.

  ;; Our -of-cons-right rule is stronger
  (in-theory (disable ACL2::INTERSECTP-EQUAL-CONS-SECOND))

  (defrule intersectp-equal-of-cons-right
    (equal (intersectp-equal x (cons a y))
           (if (member-equal a x)
               t
             (intersectp-equal x y))))

  (defrule intersect-equal-of-cons-left
    (equal (intersectp-equal (cons a x) y)
           (if (member-equal a y)
               t
             (intersectp-equal x y)))))


(defsection uniqueness-of-append

  (defrule no-duplicatesp-equal-of-append
    (equal (no-duplicatesp-equal (append x y))
           (and (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (not (intersectp-equal x y))))
    :induct (len x))

  (defrule subsetp-equal-of-append-when-empty-intersect-left
    (implies (not (intersectp-equal a b))
             (equal (subsetp-equal a (append b c))
                    (subsetp-equal a c)))
    :enable subsetp-equal)

  (defrule subsetp-equal-of-append-when-empty-intersect-right
    (implies (not (intersectp-equal a c))
             (equal (subsetp-equal a (append b c))
                    (subsetp-equal a b)))
    :enable subsetp-equal))


(defsection intersection-equal

  (local (in-theory (enable intersection-equal)))

  (defrule intersection-equal-when-atom
    (implies (atom x)
             (equal (intersection-equal x y)
                    nil)))

  (defrule intersection-equal-of-cons
    (equal (intersection-equal (cons a x) y)
           (if (member-equal a y)
               (cons a (intersection-equal x y))
             (intersection-equal x y))))

  (defrule subsetp-equal-of-intersection-equal-1
    ;; BOZO consider moving to equal-sets
    (subsetp-equal (intersection-equal x y) x)
    :hints((set-reasoning)))

  (defrule subsetp-equal-of-intersection-equal-2
    ;; BOZO consider moving to equal-sets
    (subsetp-equal (intersection-equal x y) y)
    :hints((set-reasoning))))



(defsection set-difference-equal

  (local (in-theory (enable set-difference-equal)))

  (defrule set-difference-equal-when-atom
    (implies (atom x)
             (equal (set-difference-equal x y)
                    nil)))

  (defrule set-difference-equal-of-cons
    (equal (set-difference-equal (cons a x) y)
           (if (member-equal a y)
               (set-difference-equal x y)
             (cons a (set-difference-equal x y)))))

  (defrule set-difference-equal-when-subsetp-equal
    (implies (subsetp-equal x y)
             (equal (set-difference-equal x y)
                    nil)))

  (defrule set-difference-equal-of-self
    (equal (set-difference-equal x x)
           nil))

  (defrule empty-intersect-with-difference-of-self
    (not (intersectp-equal a (set-difference-equal b a)))))



(defsection character-listp

  (local (in-theory (enable character-listp)))

  (defrule character-listp-when-not-consp
    (implies (not (consp x))
             (equal (character-listp x)
                    (not x))))

  (defrule character-listp-of-cons
    (equal (character-listp (cons a x))
           (and (characterp a)
                (character-listp x))))

  (defrule true-listp-when-character-listp
    (implies (character-listp x)
             (true-listp x)))

  (defrule characterp-of-car-when-character-listp
    (implies (character-listp x)
             (equal (characterp (car x))
                    (consp x))))

  (defrule character-listp-of-cdr-when-character-listp
    (implies (character-listp x)
             (character-listp (cdr x))))

  (defrule character-listp-of-make-list-ac
    (implies (and (force (character-listp ac))
                  (force (characterp x)))
             (character-listp (make-list-ac n x ac))))

  (defrule character-listp-of-repeat
    (equal (character-listp (repeat a n))
           (or (zp n)
               (characterp a)))
    :enable repeat)

  (defrule character-listp-of-take
    (implies (and (character-listp x)
                  (force (<= (nfix n) (len x))))
             (character-listp (take n x)))
    :enable acl2::take-redefinition)

  (defrule character-listp-of-butlast
    (implies (and (character-listp x)
                  (force (natp n))
                  (force (<= n (len x))))
             (character-listp (butlast x n)))
    :enable butlast)

  (defrule character-listp-of-last
    (implies (character-listp x)
             (character-listp (last x))))

  (defrule character-listp-of-nthcdr
    (implies (character-listp x)
             (character-listp (nthcdr n x)))))



#!ACL2
(cutil::deflist string-listp (x)
  (stringp x)
  :true-listp t
  :elementp-of-nil nil
  :already-definedp t)

#!ACL2
(cutil::deflist symbol-listp (x)
  (symbolp x)
  :true-listp t
  :elementp-of-nil t
  :already-definedp t)


(defsection string-listp

  ;;(local (in-theory (enable string-listp)))

  (defrule true-listp-when-string-listp
    ;; Having the rewrite rule seems nice; otherwise type prescriptions
    ;; sometimes don't go through, etc.
    (implies (string-listp x)
             (true-listp x))
    :rule-classes ( ;;(:compound-recognizer)
                   (:rewrite :backchain-limit-lst 1)))

  (defrule string-listp-of-intersection-equal
    (implies (and (force (string-listp x))
                  (force (string-listp y)))
             (string-listp (intersection-equal x y))))

  (defrule string-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (string-listp x)
             (string-listp (remove-equal a x))))

  (defrule string-listp-of-strip-cdrs-of-pairlis$
    ;; BOZO what nonsense is this?
    (implies (and (string-listp cdrs)
                  (force (equal (len cars) (len cdrs))))
             (string-listp (strip-cdrs (pairlis$ cars cdrs))))))



(defsection symbol-listp

  (defrule true-listp-when-symbol-listp
    ;; Having the rewrite rule seems nice; otherwise type prescriptions
    ;; sometimes don't go through, etc.
    (implies (symbol-listp x)
             (true-listp x))
    :rule-classes ( ;;(:compound-recognizer)
                   (:rewrite :backchain-limit-lst 1)))

  (defrule eqlable-listp-when-symbol-listp
    (implies (symbol-listp x)
             (eqlable-listp x)))

  (defrule symbolp-of-cdr-hons-assoc-equal-when-symbol-listp-of-strip-cdrs
    (implies (symbol-listp (strip-cdrs alist))
             (symbolp (cdr (hons-assoc-equal a alist))))))




;; BOZO uncategorized rules

(defrule characterp-of-char
  (implies (and (force (< (nfix n) (length x)))
                (force (stringp x)))
           (characterp (char x n)))
  :enable char)

(defrule stringp-when-true-listp
  (implies (true-listp x)
           (equal (stringp x)
                  nil)))

(defrule eqlablep-when-characterp
  ; BOZO why do we need this rule when there is eqlablep-recog?
  (implies (characterp x)
           (eqlablep x)))

(defrule string-append-lst-when-not-consp
  (implies (not (consp x))
           (equal (string-append-lst x)
                  ""))
  :enable string-append-lst)

(defrule string-append-lst-of-cons
  (equal (string-append-lst (cons a x))
         (string-append a (string-append-lst x)))
  :enable string-append-lst)


(defrule true-listp-of-explode-nonnegative-integer
  (implies (true-listp acc)
           (true-listp (explode-nonnegative-integer x n acc)))
  :rule-classes :type-prescription)

(defrule true-listp-of-explode-atom
  (true-listp (explode-atom x n))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (e/d (explode-atom)))))


(defrule plist-worldp-of-w
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :enable (state-p1 w))


(defrule alistp-of-make-fal
  (equal (alistp (make-fal x y))
         (alistp y))
  :enable make-fal)


(defsection characterp-of-nth

  (local (defrule l0
           (implies (and (< (nfix n) (len x))
                         (character-listp x))
                    (characterp (nth n x)))
           :enable nth))

  (defrule characterp-of-nth
    (implies (character-listp x)
             (equal (characterp (nth n x))
                    (< (nfix n) (len x))))
    :hints(("Goal" :use ((:instance l0))))))



