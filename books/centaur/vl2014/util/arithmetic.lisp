; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")

; BOZO Lib.  This book should only be locally included, and because of that you
; should never define a function here.  Instead, widely useful functions should
; generally be defined in defs.lisp.  Eventually, these lemmas should be moved
; into more other libraries.


;; Note (Sol) -- Including these before the pre-arithmetic label so that when
;; we disable basic-arithmetic-rules it doesn't turn off things that should
;; basically always be enabled, e.g., the definition of lifix.
(include-book "std/basic/defs" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)


(deflabel pre-arithmetic)

(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/bitops/integer-length" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "default-hints")


;; assumes this book will only be locally included
(in-theory (enable set::definitions
                   set::expensive-rules))

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
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/explode-atom" :dir :system)


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
            assoc-equal
            hons-shrink-alist
            make-fal
            print-base-p))



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
             (alistp (set::insert a x)))
    :enable set::primitive-rules)

  (defrule alistp-of-mergesort
    (implies (alistp x)
             (alistp (set::mergesort x)))))



(defrule assoc-equal-elim
  (implies (force (alistp alist))
           (equal (assoc-equal key alist)
                  (hons-assoc-equal key alist)))
  :enable assoc-equal)

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


  ;; BOZO probably want to redo this stuff with alist-keys instead of strip-cars

  (local (defrule l0
           (implies (alistp x)
                    (iff (hons-assoc-equal a x)
                         (member-equal a (strip-cars x))))
           :enable strip-cars))

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





(defrule string-listp-of-strip-cdrs-of-pairlis$
  ;; BOZO what nonsense is this?
  (implies (and (string-listp cdrs)
                (force (equal (len cars) (len cdrs))))
           (string-listp (strip-cdrs (pairlis$ cars cdrs)))))

(defrule symbolp-of-cdr-hons-assoc-equal-when-symbol-listp-of-strip-cdrs
  (implies (symbol-listp (strip-cdrs alist))
           (symbolp (cdr (hons-assoc-equal a alist))))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))




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



(defthm stringp-of-subseq
  (equal (stringp (subseq x start end))
         (stringp x))
  :hints(("Goal" :in-theory (enable subseq))))

(defthm true-listp-of-subseq
  (equal (true-listp (subseq x start end))
         (not (stringp x)))
  :hints(("Goal" :in-theory (enable subseq))))


(encapsulate
  ()
  (local (defthmd l0
           (equal (< (+ a x) (+ a y))
                  (< x y))))

  (defthm |(< c2 (+ c1 a))|
    (implies (and (syntaxp (quotep c2))
                  (syntaxp (quotep c1)))
             (equal (< c2 (+ c1 a))
                    (< (- c2 c1) a)))
    :hints(("Goal" :use ((:instance l0 (a (- c1)) (x c2) (y (+ c1 a))))))))


(defsection characterp-of-nth-of-explode

  (local (defthm l0
           (implies (and (character-listp x)
                         (< (nfix n) (len x)))
                    (characterp (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm l1
           (implies (and (character-listp x)
                         (not (< (nfix n) (len x))))
                    (equal (nth n x)
                           nil))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm l2
           (implies (character-listp x)
                    (equal (characterp (nth n x))
                           (< (nfix n) (len x))))
           :hints(("Goal" :use ((:instance l0)
                                (:instance l1))))))

  (defthm characterp-of-nth-of-explode
    (equal (characterp (nth n (explode x)))
           (< (nfix n) (len (explode x))))))

(defthm nth-of-explode-when-char-fix-known
  (implies (equal (char-fix (nth n (explode x))) c)
           (equal (nth n (explode x))
                  (and (< (nfix n) (len (explode x)))
                       c)))
  :hints(("Goal"
          :in-theory (disable nth characterp-of-nth-of-explode)
          :use ((:instance characterp-of-nth-of-explode)))))


(encapsulate ()
  (local (defthm l0
           (iff (member a (alist-keys (hons-shrink-alist x y)))
                (or (member a (alist-keys x))
                    (member a (alist-keys y))))
           :hints(("Goal" :in-theory (enable hons-shrink-alist)))))

  (defthm alist-keys-of-hons-shrink-alist
    (set-equiv (alist-keys (hons-shrink-alist x y))
               (append (alist-keys x)
                       (alist-keys y)))
    :hints((set-reasoning))))

(defcong acl2::nat-equiv equal (str::nat-to-dec-chars n) 1
  :event-name nat-to-dec-chars-preserves-nat-equiv
  :hints(("Goal" :in-theory (enable str::nat-to-dec-chars))))

(defcong acl2::nat-equiv equal (natstr n) 1
  :event-name natstr-preserves-nat-equiv)

(defthm natstr-when-zp
  (implies (zp n)
           (equal (natstr n) "0"))
  :hints(("Goal"
          ;; This is fucking terrible.
          :in-theory (disable natstr-preserves-nat-equiv)
          :use ((:instance natstr-preserves-nat-equiv
                 (n 0)
                 (acl2::n-equiv n))))))


(defthm len-of-cdr-strong
  (implies (consp x)
           (< (len (cdr x))
              (len x)))
  :rule-classes ((:rewrite) (:linear)))
