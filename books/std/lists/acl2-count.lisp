; acl2-count of lists
; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
;
; These theorems are proved so often that I don't think there's any sense
; copyrighting them.

; Not sure if it's best to put theorems about acl2-count of other list-related
; stuff here or in the books for the various list functions, e.g., there's some
; stuff about acl2-count of nthcdr in the nthcdr book.  For now here are some
; lemmas about car and cdr that are all over the place.

; It looks like there aren't any exact name clashes -- some overlap in
; centaur/vl/util/arithmetic, but in the VL package.

(in-package "ACL2")

;; These are strictly weaker than acl2-count-of-sum, below (at least, together
;; with (:type-prescription acl2-count)).
(defthmd acl2-count-of-car
  (and (implies (consp x)
                (< (acl2-count (car x))
                   (acl2-count x)))
       (<= (acl2-count (car x))
           (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count)))
  :rule-classes :linear)

(defthmd acl2-count-of-cdr
  (and (implies (consp x)
                (< (acl2-count (cdr x))
                   (acl2-count x)))
       (<= (acl2-count (cdr x))
           (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count)))
  :rule-classes :linear)

(defthm acl2-count-of-sum
  (and (implies (consp x)
                (< (+ (acl2-count (car x))
                      (acl2-count (cdr x)))
                   (acl2-count x)))
       (<= (+ (acl2-count (car x))
              (acl2-count (cdr x)))
           (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count)))
  :rule-classes :linear)


(defthm acl2-count-of-consp-positive
  (implies (consp x)
           (< 0 (acl2-count x)))
  :rule-classes (:type-prescription :linear))

(defthm acl2-count-of-cons-greater
  ;; [Jared] renamed this form acl2-count-of-cons for compatibility with
  ;; coi/lists/acl2-count
  (> (acl2-count (cons a b))
     (+ (acl2-count a) (acl2-count b)))
  :rule-classes :linear)
