; ESIM Symbolic Hardware Simulator
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


; local-theory.lisp -- general lemmas used in the esim proofs, this book should
; only be locally included!
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/lists/rev" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "std/lists/remove-duplicates" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))



(defthm remove-duplicates-equal-of-append
  (equal (remove-duplicates-equal (append a b))
         (append (set-difference-equal (remove-duplicates-equal a) b)
                 (remove-duplicates-equal b)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-append
  (equal (set-difference-equal (append a b) c)
         (append (set-difference-equal a c)
                 (set-difference-equal b c)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-remove-inside-set-difference
  (implies (member-equal k keys)
           (equal (set-difference-equal
                   (set-difference-equal a (list k))
                   keys)
                  (set-difference-equal a keys)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))


(defthm set-difference-equal-nil
  (equal (set-difference-equal x nil)
         (append x nil))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

;; (defthm hons-remove-duplicates1-is-remove-duplicates
;;   (equal (hons-remove-duplicates1 lst tab)
;;          (rev (set-difference-equal
;;                (remove-duplicates-equal (rev lst))
;;                (alist-keys tab))))
;;   :hints(("Goal" :in-theory (enable rev set-difference-equal))))

;; (defthm hons-remove-duplicates-is-remove-duplicates
;;   (equal (hons-remove-duplicates lst)
;;          (rev (remove-duplicates-equal (rev lst)))))

(in-theory (enable hons-remove-duplicates))

(defthm hons-dups-p1-when-table-member
  (implies (and (member-equal x lst)
                (hons-assoc-equal x tab))
           (hons-dups-p1 lst tab)))

(defthm hons-dups-p1-is-no-duplicatesp
  (iff (hons-dups-p1 lst tab)
       (or (not (no-duplicatesp-equal lst))
           (intersectp-equal lst (alist-keys tab)))))

(defthm hons-dups-p-is-no-duplicatesp
  (iff (hons-dups-p lst)
       (not (no-duplicatesp-equal lst))))

(defthm member-equal-rev
  (iff (member-equal k (rev x))
       (member-equal k x))
  :hints(("Goal" :in-theory (enable rev))))

(defthm set-equiv-rev
  (set-equiv (rev x) x)
  :hints ((witness)))

(defthm alist-keys-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b))))

(defthm true-listp-append-iff
  (iff (true-listp (append a b))
       (true-listp b)))

