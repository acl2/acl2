; A utility to check whether all values in a list are greater than a given value
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also all-less.lisp.
;; TODO: Synchronize this book with that one.

(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(defund all-> (x bound)
  (declare (xargs :guard (and (rational-listp x)
                              (rationalp bound))))
  (if (atom x)
      t
      (and (> (first x) bound)
           (all-> (rest x) bound))))

(defthm all->-of-cons
  (equal (all-> (cons a x) bound)
         (and (> a bound)
              (all-> x bound)))
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-nil
  (all-> nil bound)
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-cdr
  (implies (all-> x bound)
           (all-> (cdr x) bound))
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-append
  (equal (all-> (append x y) bound)
         (and (all-> x bound)
              (all-> y bound)))
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-revappend
  (equal (all-> (revappend x y) bound)
         (and (all-> x bound)
              (all-> y bound)))
  :hints (("Goal" :in-theory (enable all-> revappend-becomes-append-of-reverse-list))))

;; (defthm all->-of-reverse-list
;;   (equal (all-> (reverse-list x) bound)
;;          (all-> x bound))
;;   :hints (("Goal" :in-theory (enable all-> reverse-list))))
