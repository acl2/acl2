; A term to make tuples
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;make-tuple : this is a scheme for taking a term that represents a list ("tuple") value and making it into an equivalent, explicit cons nest

(defun make-tuple (n len x)
  (declare (xargs :measure (nfix (+ 1 (- len n)))))
  (if (or (<= len n)
          (not (natp n))
          (not (natp len)))
      nil
    (cons (nth n x)
          (make-tuple (+ 1 n) len x))))

(defthmd make-tuple-dropper-helper
  (implies (and (equal len (len x))
                (true-listp x)
                (natp n))
           (equal (make-tuple n len x)
                  (nthcdr n x)))
  :hints (("Goal" :in-theory (enable cdr-of-nthcdr))))

(defthmd make-tuple-dropper
  (implies (and (equal len (len x))
                (true-listp x))
           (equal (make-tuple 0 len x)
                  x))
  :hints (("Goal" :in-theory (enable make-tuple-dropper-helper))))

(defthmd make-tuple-opener
  (implies (and (< n len)
                (natp n)
                (natp len))
           (equal (make-tuple n len x)
                  (cons (nth n x)
                        (make-tuple (+ 1 n) len x)))))

(defthm make-tuple-base
  (equal (make-tuple len len x)
         nil)
  :hints (("Goal" :expand ((make-tuple len len x)))))

;; ;example rule to expose the components of foo's x argument (which we expect to be of length 5)
;; (defthm foo-make-tuple
;;  (implies (and (axe-syntaxp (not (equal 'cons (car x))))
;;                (equal 5 (len x))
;;                (true-listp x))
;;           (equal (foo x)
;;                  (foo (make-tuple 0 5 x)))))
