; A lightweight book about the built-in function ash
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a few theorems about the built-in function ASH
;; (arithmetic shift).

(local (include-book "floor"))
(local (include-book "expt"))
(local (include-book "divides"))
(local (include-book "times-and-divides"))
(local (include-book "times"))

(defthm ash-of-0
  (equal (ash i 0)
         (ifix i))
  :hints (("Goal" :in-theory (enable ash))))

(defthm integerp-of-ash
  (integerp (ash i c)))

;;todo: combine with other rules?
;; avoids name clash
(defthm unsigned-byte-p-of-ash-alt
  (implies (and (natp c) ;; positive count means a left shift
                (unsigned-byte-p (- size c) i)
                (natp size))
           (unsigned-byte-p size (ash i c)))
  :hints (("Goal"
           :use (:instance <-of-*-and-*-cancel
                           (x1 i)
                           (x2 (* (/ (expt 2 c)) (expt 2 size)))
                           (y (expt 2 c)))
           :in-theory (e/d (ash expt-of-+)
                           (<-of-*-and-*-cancel)))))
