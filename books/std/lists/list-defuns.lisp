; Definitions of List Functions
; Copyright (C) 2008-2014 Centaur Technology
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
; Additional copyright notice for list-defuns.lisp.  This file was originally
; part of the Unicode library.  It has since then been extended with additional
; definitions, e.g., from Centaur libraries.

(in-package "ACL2")

; This book is intended to be a rather bare-minimum set of list definitions.
; Historically it included most of the books in the std/lists library and then
; just redundantly introduced the logic-mode, guard-verified definitions.
; However, to really optimize things and avoid having lots of dependencies, we
; now prove the bare-minimum theorems inline and avoid including the other
; books.

; Mihir M. mod: list-fix-exec and list-fix were defined here earlier, but after
; the migration of these definitions to the sources, we just have macros.
(defmacro list-fix-exec (x) `(true-list-fix-exec ,x))

(table macro-aliases-table 'list-fix-exec 'true-list-fix-exec)

(in-theory (disable list-fix-exec))

(defmacro list-fix (x) `(true-list-fix ,x))

(table macro-aliases-table 'list-fix 'true-list-fix)

(in-theory (disable list-fix))

(encapsulate
  ()
  (local (in-theory (enable list-fix list-fix-exec)))

  (defthm list-fix-exec-removal
    (equal (list-fix-exec x)
           (list-fix x)))

  (local (defthm list-fix-when-true-listp
           (implies (true-listp x)
                    (equal (list-fix x) x))))

  (defun-inline llist-fix (x)
    (declare (xargs :guard (true-listp x)))
    (mbe :logic (list-fix x)
         :exec x)))

(defund fast-list-equiv (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (fast-list-equiv (cdr x) (cdr y)))
    (atom y)))

(defund list-equiv (x y)
  (declare (xargs :guard t
                  :guard-hints(("Goal" :in-theory (enable fast-list-equiv
                                                          list-fix)))))
  (mbe :logic (equal (list-fix x) (list-fix y))
       :exec (fast-list-equiv x y)))

(defequiv list-equiv
  ;; We include this, even though this book isn't really meant to include
  ;; theorems, in order to avoid subtle errors that can arise in different
  ;; books.  Without this, in book A we could just load LIST-DEFUNS and then
  ;; prove a theorem that concluded (LIST-EQUIV X Y).  If then in book B we
  ;; load list/equiv.lisp first and then include book A, this is no longer a
  ;; valid rewrite rule and we get a horrible error!
  :hints(("Goal" :in-theory (enable list-equiv))))


(defun set-equiv (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(encapsulate
  ()
  ;; We prove these for the same reason as we show (defequiv list-equiv).
  (local (defthm l0
           (implies (subsetp x (cdr y))
                    (subsetp x y))))

  (local (defthm l1
           (subsetp x x)))

  (local (defthm l2
           (implies (and (member a x)
                         (subsetp x y))
                    (member a y))))

  (local (defthm l3
           (implies (and (subsetp x y)
                         (subsetp y z))
                    (subsetp x z))))

  (defequiv set-equiv)


  ;; It seems basically reasonable to also prove the fundamental refinement
  ;; relation.
  (local (defthm r0
           (equal (subsetp-equal (list-fix x) y)
                  (subsetp-equal x y))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (local (defthm r1
           (iff (member-equal a (list-fix x))
                (member-equal a x))
           :hints(("Goal" :in-theory (enable list-fix)))))

  (local (defthm r2
           (equal (subsetp-equal x (list-fix y))
                  (subsetp-equal x y))))

  (local (defthm r3
           (equal (set-equiv (list-fix x) y)
                  (set-equiv x y))))

  (local (defthm r4
           (equal (set-equiv x (list-fix y))
                  (set-equiv x y))))

  (defrefinement list-equiv set-equiv
    :hints(("Goal"
            :in-theory (e/d (list-equiv) (set-equiv r4))
            :use ((:instance r4 (y x))
                  (:instance r4 (x y)))))))

(defun binary-append-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (append x y)
       :exec
       (if (consp x)
           (cons (car x)
                 (binary-append-without-guard (cdr x) y))
         y)))

(defmacro append-without-guard (x y &rest rst)
  (xxxjoin 'binary-append-without-guard (list* x y rst)))

(add-macro-alias append-without-guard binary-append-without-guard)

(defun revappend-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic (revappend x y)
       :exec  (if (consp x)
                  (revappend-without-guard (cdr x)
                                           (cons (car x) y))
                y)))

(defund rcons (a x)
  (declare (xargs :guard t))
  (append-without-guard x (list a)))

(defund rev (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp x)
                  (append (rev (cdr x))
                          (list (car x)))
                nil)
       :exec (revappend-without-guard x nil)))

(encapsulate
  ()
  (local (defthm l1
           (equal (append (append rv (list x1)) y)
                  (append rv (cons x1 y)))))

  (local (defthm l2
           (equal (revappend x y)
                  (append (rev x) y))
           :hints(("Goal" :in-theory (enable rev)))))

  (verify-guards rev
    :hints(("Goal" :in-theory (enable rev)))))


(defund prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(defund suffixp (x y)
  (declare (xargs :guard t))
  (or (equal x y)
      (and (consp y)
           (suffixp x (cdr y)))))

(defund flatten (x)
  (declare (xargs :guard t))
  (if (consp x)
      (append-without-guard (car x)
                            (flatten (cdr x)))
    nil))

(defund repeat (n x)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat (- n 1) x)))
       :exec (make-list n :initial-element x)))

(defmacro replicate (n x)
  `(repeat ,n ,x))

(add-macro-alias replicate repeat)

(local
 (encapsulate
   ()
   (local (defthm l0
            (equal (append (replicate n x) (cons x acc))
                   (cons x (append (replicate n x) acc)))
            :hints(("Goal" :in-theory (enable replicate)))))

   (defthm make-list-ac-redef
     (equal (make-list-ac n x acc)
            (append (replicate n x)
                    acc))
     :hints(("Goal" :in-theory (enable repeat))))))

(verify-guards repeat
  :hints(("Goal" :in-theory (enable repeat))))


(encapsulate
  ()
  (local (in-theory (enable repeat list-fix)))

  (defun all-equalp (a x)
    (declare (xargs :guard t :verify-guards nil))
    (let ((__function__ 'all-equalp))
      (declare (ignorable __function__))
      (mbe :logic
           (equal (list-fix x) (repeat (len x) a))
           :exec
           (if (consp x)
               (and (equal a (car x))
                    (all-equalp a (cdr x)))
             t))))

  (verify-guards all-equalp))

(defund final-cdr (x)
  (declare (xargs :guard t))
  (if (atom x)
      x
    (final-cdr (cdr x))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil)
                nil)))

(defun rest-n (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (nthcdr n x)
       :exec
       (cond ((zp n)
              x)
             ((atom x)
              nil)
             (t
              (rest-n (- n 1) (cdr x))))))

(defun first-n (n x)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (mbe :logic (take n x)
       :exec
       (cond ((zp n)
              nil)
             ((atom x)
              (make-list n))
             (t
              (cons (car x)
                    (first-n (- n 1) (cdr x)))))))

(encapsulate
  ()

  (local (defthm take-when-atom
           (implies (atom x)
                    (equal (take n x)
                           (replicate n nil)))
           :hints(("Goal"
                   :in-theory (enable replicate)))))

  (verify-guards first-n
    :hints(("Goal" :in-theory (enable replicate)))))

(defun same-lengthp (x y)
  (declare (xargs :guard t))
  (mbe :logic (equal (len x) (len y))
       :exec (if (consp x)
                 (and (consp y)
                      (same-lengthp (cdr x) (cdr y)))
               (not (consp y)))))

(defund sublistp (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y) t)
        ((atom y)      nil)
        (t             (sublistp x (cdr y)))))

(defund listpos (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y)
         0)
        ((atom y)
         nil)
        (t
         (let ((pos-in-cdr (listpos x (cdr y))))
           (and pos-in-cdr
                (+ 1 pos-in-cdr))))))

(defund duplicity-exec (a x n)
  (declare (xargs :guard (natp n)))
  (if (atom x)
      n
    (duplicity-exec a (cdr x)
                    (if (equal (car x) a)
                        (+ 1 n)
                      n))))

(defund duplicity (a x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cond ((atom x)
                     0)
                    ((equal (car x) a)
                     (+ 1 (duplicity a (cdr x))))
                    (t
                     (duplicity a (cdr x))))
       :exec (duplicity-exec a x 0)))

(local (defthm duplicity-exec-removal
         (implies (natp n)
                  (equal (duplicity-exec a x n)
                         (+ (duplicity a x) n)))
         :hints(("Goal" :in-theory (enable duplicity duplicity-exec)))))

(verify-guards duplicity
  :hints(("Goal" :in-theory (enable duplicity))))
