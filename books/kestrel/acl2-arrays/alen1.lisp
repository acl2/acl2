; A more abstract idiom for getting the length of an array1
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;dup
(local
 (defthm equal-of-assoc-equal-same
  (implies key
           (iff (equal key (car (assoc-equal key array)))
                (assoc-equal key array)))
  :hints (("Goal" :in-theory (enable assoc-equal)))))

;; Get the length of a 1-d array.  We prefer this to (car (dimensions ...))
;; because car in many cases get rewritten to a call of nth.
(defund alen1 (name l)
  (declare (xargs :guard (array1p name l)))
  (car (dimensions name l)))

(defthmd normalize-alen1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (alen1 name l)
                  (alen1 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (alen1) ()))))

;; Introduce alen1
(defthm alen1-intro
  (equal (car (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (enable alen1))))

(theory-invariant (incompatible (:rewrite alen1-intro) (:definition alen1)))

;; Introduce alen1
;; (car (dimensions ..)) can arise from the guard of aref1 and can then be turned into (nth 0 (dimensions ...))
(defthm alen1-intro2
  (equal (nth 0 (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro)))))

(theory-invariant (incompatible (:rewrite alen1-intro2) (:definition alen1)))

(defthm alen1-of-compress1
  (equal (alen1 array-name (compress1 array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro alen1-intro2)))))
