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

(defthm <=-of-0-and-ash
  (implies (<= 0 i)
           (<= 0 (ash i c)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm <=-of-0-and-ash-type
  (implies (<= 0 i)
           (<= 0 (ash i c)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ash))))

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

;; could make a version restricted to constant c and k
;; works for both positive and negative shifts
(defthmd <-of-ash-arg1
  (implies (and (rationalp k)
                (integerp c))
           (equal (< (ash i c) k)
                  (if (integerp k)
                      (< (ifix i)
                         (/ k (expt 2 c)))
                    (< (ifix i)
                       ;; round k up to an integer:
                       (/ (+ 1 (floor k 1)) (expt 2 c))))))
  :hints (("Goal" :in-theory (enable ash <-of-floor-arg1-gen))))

(defthmd <-of-ash-arg2
  (implies (and (rationalp k)
                (integerp c))
           (equal (< k (ash i c))
                  (<= (+ 1 (floor k 1)) ; round k up (or add 1 if an integer)
                      (* (ifix i) (expt 2 c)))))
  :hints (("Goal" :in-theory (enable ash <-of-floor-arg2-gen))))

(defthmd <=-of-ash-when-<=-free-linear
  (implies (and (<= i free)
                (integerp i)
                (integerp c))
           (<= (ash i c) (* free (expt 2 c))))
  :rule-classes ((:linear :trigger-terms ((ash i c))))
  :hints (("Goal" :in-theory (enable ash))))

(defthm <-of-ash-linear-when-<-free-linear
  (implies (and (< i free)
                (integerp i)
                (integerp c))
           (< (ash i c) (* free (expt 2 c))))
  :rule-classes ((:linear :trigger-terms ((ash i c))))
  :hints (("Goal" :in-theory (enable ash))))

;; (defthm <-of-ash-and-*-of-expt
;;   (implies (and (< i free)
;;                 (integerp i)
;;                 (natp c))
;;            (< (ash i c) (* free (expt 2 c))))
;;   :hints (("Goal" :in-theory (enable ash))))

;; (defthm <-of-ash-and-*-of-expt-alt
;;   (implies (and (< i free)
;;                 (integerp i)
;;                 (natp c))
;;            (< (ash i c) (* (expt 2 c) free)))
;;   :hints (("Goal" :in-theory (enable ash))))

;; (defthm <=-of-ash-and-*-of-expt-arg1
;;   (implies (and (<= i free)
;;                 (integerp i)
;;                 (natp c))
;;            (<= (ash i c) (* (expt 2 c) free)))
;;   :hints (("Goal" :in-theory (enable ash))))

;; (defthm <=-of-ash-and-*-of-expt-arg2
;;   (implies (and (<= i free)
;;                 (integerp i)
;;                 (natp c))
;;            (<= (ash i c) (* free (expt 2 c))))
;;   :hints (("Goal" :in-theory (enable ash))))

;; (defthm <=-of-ash-and-*-of-expt-alt
;;   (implies (and (< i free)
;;                 (integerp i)
;;                 (integerp free)
;;                 (natp c))
;;            (<= (ash i c) (* (expt 2 c) (+ -1 free))))
;;   :hints (("Goal" :use (:instance <=-of-ash-and-*-of-expt-arg1
;;                                   (free (+ -1 free)))
;;            :in-theory (disable <=-of-ash-and-*-of-expt-arg1))))

;; (defthm <=-of-ash-and-*-of-expt-alt-linear
;;   (implies (and (< i free)
;;                 (integerp i)
;;                 (integerp free)
;;                 (natp c))
;;            (<= (ash i c) (* (expt 2 c) (+ -1 free))))
;;   :rule-classes ((:linear :trigger-terms ((ash i c))))
;;   :hints (("Goal" :use (:instance <=-of-ash-and-*-of-expt-arg1
;;                                   (free (+ -1 free)))
;;            :in-theory (disable <=-of-ash-and-*-of-expt-arg1))))
