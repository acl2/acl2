; A functiont to get the last element of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that the built-in function LAST returns the last cons of a list, not
;; the last element.

(defund last-elem (x)
  (declare (xargs :guard (listp x))) ;todo: try consp as a guard
  (car (last x)))

;; (defthm last-elem-of-singleton
;;   (equal (last-elem (list x))
;;          x)
;;   :hints (("Goal" :in-theory (enable last-elem))))

(defthm last-elem-of-cons
  (equal (last-elem (cons a x))
         (if (consp x)
             (last-elem x)
           a))
  :hints (("Goal" :in-theory (enable last-elem))))

(defthm last-elem-of-append
  (equal (last-elem (append x y))
         (if (endp y)
             (last-elem x)
           (last-elem y)))
  :hints (("Goal" :in-theory (enable last-elem))))

(defthm <-of-acl2-count-of-last-elem-when-consp
  (implies (consp x)
           (< (acl2-count (last-elem x))
              (acl2-count x)))
  :rule-classes (:rewrite :linear))

(defthm <=-of-acl2-count-of-last-elem
  (<= (acl2-count (last-elem x))
      (acl2-count x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable last-elem))))

(defthmd last-elem-when-not-consp
  (implies (not (consp x))
           (equal (last-elem x)
                  nil))
  :hints (("Goal" :in-theory (enable last-elem))))

(defthm last-elem-when-not-consp-cheap
  (implies (not (consp x))
           (equal (last-elem x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable last-elem))))
