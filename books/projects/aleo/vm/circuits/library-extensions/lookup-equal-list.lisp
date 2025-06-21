; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lift lookup-equal to lists of keys

(define lookup-equal-list (keys alist)
  :guard (and (true-listp keys) (alistp alist))
  :returns vals
  (cond ((endp keys) nil)
        (t (cons (lookup-equal (car keys) alist)
                 (lookup-equal-list (cdr keys) alist))))
  ///

  (defret len-of-lookup-equal-list
    (equal (len vals)
           (len keys)))

  (defret consp-of-lookup-equal-list
    (equal (consp vals)
           (consp keys)))

  (defruled lookup-equal-list-of-cdr
    (equal (lookup-equal-list (cdr keys) alist)
           (cdr (lookup-equal-list keys alist))))

  (defruled lookup-equal-list-of-cons
    (equal (lookup-equal-list (cons key keys) alist)
           (cons (lookup-equal key alist)
                 (lookup-equal-list keys alist))))

  (defruled lookup-equal-list-of-append
    (equal (lookup-equal-list (append keys1 keys2) alist)
           (append (lookup-equal-list keys1 alist)
                   (lookup-equal-list keys2 alist))))

  (defruled lookup-equal-list-of-rev
    (equal (lookup-equal-list (rev keys) alist)
           (rev (lookup-equal-list keys alist)))
    :enable lookup-equal-list-of-append)

  (defruled lookup-equal-list-of-nthcdr
    (equal (lookup-equal-list (nthcdr i keys) alist)
           (nthcdr i (lookup-equal-list keys alist))))

  (defruled lookup-equal-list-of-repeat
    (equal (lookup-equal-list (repeat n key) alist)
           (repeat n (lookup-equal key alist)))
    :enable repeat)

  (defruled lookup-equal-list-of-take
    (implies (< i (len keys))
             (equal (lookup-equal-list (take i keys) alist)
                    (take i (lookup-equal-list keys alist)))))

  (defruled lookup-equal-list-of-last
    (equal (lookup-equal-list (last keys) alist)
           (last (lookup-equal-list keys alist)))
    :enable lookup-equal-list)

  (defruled last-of-lookup-equal-list
    (equal (last (lookup-equal-list keys alist))
           (lookup-equal-list (last keys) alist))
    :enable lookup-equal-list)

  (theory-invariant (incompatible (:rewrite lookup-equal-list-of-last)
                                  (:rewrite last-of-lookup-equal-list)))

  (defruled lookup-equal-of-car
    (implies (consp keys)
             (equal (lookup-equal (car keys) alist)
                    (car (lookup-equal-list keys alist))))
    :enable lookup-equal-list)

  (defruled car-of-lookup-equal-list
    (implies (consp keys)
             (equal (car (lookup-equal-list keys alist))
                    (lookup-equal (car keys) alist)))
    :enable lookup-equal-list)

  (theory-invariant (incompatible (:rewrite lookup-equal-of-car)
                                  (:rewrite car-of-lookup-equal-list))))
