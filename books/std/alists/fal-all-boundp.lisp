; Standard Association Lists Library
; Copyright (C) 2013-2014 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "alist-equiv")
(include-book "worth-hashing")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "hons-assoc-equal"))

(define fal-all-boundp-fast (keys alist)
  :parents (fal-all-boundp)
  (if (atom keys)
      t
    (and (hons-get (car keys) alist)
         (fal-all-boundp-fast (cdr keys) alist))))

(define fal-all-boundp-slow (keys alist)
  :parents (fal-all-boundp)
  (if (atom keys)
      t
    (and (hons-assoc-equal (car keys) alist)
         (fal-all-boundp-slow (cdr keys) alist))))

(define fal-all-boundp (keys alist)
  :parents (std/alists)
  :short "@(call fal-all-boundp) determines if every key in @('keys') is bound
in the alist @('alist')."
  :long "<p>The @('alist') need not be fast.  If it is not fast, it may be made
temporarily fast, depending on its length.</p>"
  :returns bool
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (atom keys)
           t
         (and (hons-assoc-equal (car keys) alist)
              (fal-all-boundp (cdr keys) alist)))
       :exec
       (if (atom keys)
           t
         (if (and (worth-hashing keys)
                  (worth-hashing alist))
             (with-fast-alist alist
               (fal-all-boundp-fast keys alist))
           (fal-all-boundp-slow keys alist))))
  ///
  (defthm fal-all-boundp-fast-removal
    (equal (fal-all-boundp-fast keys alist)
           (fal-all-boundp keys alist))
    :hints(("Goal" :in-theory (enable fal-all-boundp-fast))))

  (defthm fal-all-boundp-slow-removal
    (equal (fal-all-boundp-slow keys alist)
           (fal-all-boundp keys alist))
    :hints(("Goal" :in-theory (enable fal-all-boundp-slow))))

  (verify-guards fal-all-boundp)

  (defthm fal-all-boundp-when-atom
    (implies (atom keys)
             (equal (fal-all-boundp keys alist)
                    t)))

  (defthm fal-all-boundp-of-cons
    (equal (fal-all-boundp (cons a keys) alist)
           (and (hons-get a alist)
                (fal-all-boundp keys alist))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (and (fal-all-boundp y alist)
                           (member-equal a y))
                      (hons-assoc-equal a alist))))

    (local (defthm l1
             (implies (and (fal-all-boundp y alist)
                           (subsetp-equal x y))
                      (fal-all-boundp x alist))
             :hints(("Goal" :induct (len x)))))

    (defcong set-equiv equal (fal-all-boundp x alist) 1
      :hints(("Goal" :in-theory (e/d (set-equiv)
                                     (l1))
              :use ((:instance l1 (x x) (y x-equiv))
                    (:instance l1 (x x-equiv) (y x)))))))

  (defcong alist-equiv equal (fal-all-boundp x alist) 2)

  (defthm fal-all-boundp-of-list-fix
    ;; BOZO silly to prove this?  Just a consequence of the set-equiv
    (equal (fal-all-boundp (list-fix x) alist)
           (fal-all-boundp x alist)))

  (defthm fal-all-boundp-of-rev
    ;; BOZO silly to prove this?  Just a consequence of the set-equiv
    (equal (fal-all-boundp (rev x) alist)
           (fal-all-boundp x alist)))

  (defthm fal-all-boundp-of-append
    (equal (fal-all-boundp (append x y) alist)
           (and (fal-all-boundp x alist)
                (fal-all-boundp y alist))))

  (defthm fal-all-boundp-of-revappend
    ;; BOZO silly to prove this?  Trivial via the set-equiv and append rules
    (equal (fal-all-boundp (revappend x y) alist)
           (and (fal-all-boundp x alist)
                (fal-all-boundp y alist)))))