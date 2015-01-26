; Standard Association Lists Library
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "../lists/list-defuns")
(local (include-book "alist-equiv"))
(local (include-book "append-alist-keys"))
(local (include-book "append-alist-vals"))

(defund alist-keys (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-keys (cdr x)))
        (t
         (cons (caar x) (alist-keys (cdr x))))))

(defund alist-vals (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-vals (cdr x)))
        (t
         (cons (cdar x) (alist-vals (cdr x))))))

(defund hons-rassoc-equal (val alist)
  (declare (xargs :guard t))
  (cond ((atom alist)
         nil)
        ((and (consp (car alist))
              (equal val (cdar alist)))
         (car alist))
        (t
         (hons-rassoc-equal val (cdr alist)))))

(defund alists-agree (keys al1 al2)
  "Do AL1 and AL2 agree on the value of every KEY in KEYS?"
  (declare (xargs :guard t))
  (or (atom keys)
      (and (equal (hons-get (car keys) al1)
                  (hons-get (car keys) al2))
           (alists-agree (cdr keys) al1 al2))))

(defund sub-alistp (a b)
  "Is every key bound in A also bound to the same value in B?"
  (declare (xargs :guard t))
  (mbe :logic (alists-agree (alist-keys a) a b)
       :exec
       (with-fast-alist a
         (with-fast-alist b
           (alists-agree (alist-keys a) a b)))))

(defund alist-equiv (a b)
  "Do A and B agree on the values of every key?"
  (declare (xargs :guard t))
  (mbe :logic (and (sub-alistp a b)
                   (sub-alistp b a))
       :exec
       ;; Silly, make them both fast once instead of twice.
       (with-fast-alist a
         (with-fast-alist b
           (and (sub-alistp a b)
                (sub-alistp b a))))))

(defequiv alist-equiv
  ;; We include this, even though this book isn't really meant to include
  ;; theorems, in order to avoid subtle errors that can arise in different
  ;; books.  Without this, in book A we could just load ALIST-DEFUNS and then
  ;; prove a theorem that concluded (ALIST-EQUIV X Y).  If then in book B we
  ;; load alists/alist-equiv.lisp first and then include book A, this is no
  ;; longer a valid rewrite rule and we get a horrible error!
  )

(defund fal-extract1 (keys al)
  "Assumes AL is fast"
  (declare (xargs :guard t))
  (b* (((when (atom keys))
        nil)
       (look (hons-get (car keys) al))
       ((when look)
        (cons look (fal-extract1 (cdr keys) al))))
    (fal-extract1 (cdr keys) al)))

(defund fal-extract (keys al)
  "Makes AL fast if necessary"
  (declare (xargs :guard t
                  :guard-hints(("Goal" :in-theory (enable fal-extract fal-extract1)))))
  (mbe :logic
       (b* (((when (atom keys))
             nil)
            (look (hons-get (car keys) al))
            ((when look)
             (cons look (fal-extract (cdr keys) al))))
         (fal-extract (cdr keys) al))
       :exec
       (with-fast-alist al
         (fal-extract1 keys al))))

(defund fal-extract-vals1 (keys al)
  "Assumes AL is fast"
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (cons (cdr (hons-get (car keys) al))
          (fal-extract-vals1 (cdr keys) al))))

(defund fal-extract-vals (keys al)
  "Makes AL fast if necessary"
  (declare (xargs :guard t
                  :guard-hints(("Goal" :in-theory (enable fal-extract-vals fal-extract-vals1)))))
  (mbe :logic
       (if (atom keys)
           nil
         (cons (cdr (hons-get (car keys) al))
               (fal-extract-vals (cdr keys) al)))
       :exec
       (with-fast-alist al
         (fal-extract-vals1 keys al))))

(defund append-alist-vals-exec (x acc)
  (declare (xargs :guard t))
  (mbe :logic
       (if (atom x)
           acc
         (append-alist-vals-exec (cdr x)
                                 (revappend (cdar x) acc)))
       :exec
       (cond ((atom x)
              acc)
             ((atom (car x))
              (append-alist-vals-exec (cdr x) acc))
             (t
              (append-alist-vals-exec (cdr x)
                                      (revappend-without-guard (cdar x) acc))))))

(defund append-alist-vals (x)
  (declare (xargs :guard t))
  (mbe :logic
       (if (atom x)
           nil
         (append (cdar x) (append-alist-vals (cdr x))))
       :exec
       (reverse (append-alist-vals-exec x nil))))

(defund append-alist-keys-exec (x acc)
  (declare (xargs :guard t))
  (mbe :logic
       (if (atom x)
           acc
         (append-alist-keys-exec (cdr x)
                                 (revappend (caar x) acc)))
       :exec
       (cond ((atom x)
              acc)
             ((atom (car x))
              (append-alist-keys-exec (cdr x) acc))
             (t
              (append-alist-keys-exec (cdr x)
                                      (revappend-without-guard (caar x) acc))))))

(defund append-alist-keys (x)
  (declare (xargs :guard t))
  (mbe :logic
       (if (atom x)
           nil
         (append (caar x) (append-alist-keys (cdr x))))
       :exec
       (reverse (append-alist-keys-exec x nil))))


(define worth-hashing1 (x n)
  (declare (type (unsigned-byte 8) n)
           (xargs :guard t))
  (mbe :logic (>= (len x) n)
       :exec
       (cond ((eql n 0) t)
             ((atom x) nil)
             (t (worth-hashing1 (cdr x) (the (unsigned-byte 8) (1- n)))))))

(local (in-theory (enable worth-hashing1)))

(define worth-hashing (x)
  :returns bool
  :inline t
  (mbe :logic (>= (len x) 18)
       :exec (and (consp x)
                  (worth-hashing1 (cdr x) 17))))

(define fal-all-boundp-fast (keys alist)
  (if (atom keys)
      t
    (and (hons-get (car keys) alist)
         (fal-all-boundp-fast (cdr keys) alist))))

(define fal-all-boundp-slow (keys alist)
  (if (atom keys)
      t
    (and (hons-assoc-equal (car keys) alist)
         (fal-all-boundp-slow (cdr keys) alist))))

(define fal-all-boundp (keys alist)
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
           (fal-all-boundp-slow keys alist)))))

(encapsulate
  ()
  (local (in-theory (enable fal-all-boundp)))

  (defthm fal-all-boundp-fast-removal
    (equal (fal-all-boundp-fast keys alist)
           (fal-all-boundp keys alist))
    :hints(("Goal" :in-theory (enable fal-all-boundp-fast))))

  (defthm fal-all-boundp-slow-removal
    (equal (fal-all-boundp-slow keys alist)
           (fal-all-boundp keys alist))
    :hints(("Goal" :in-theory (enable fal-all-boundp-slow))))

  (verify-guards fal-all-boundp))


