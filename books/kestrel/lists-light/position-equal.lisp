; A lightweight book about the built-in-function position-equal
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "position-equal-ac"))

;; Note that position-equal handles both strings and lists.

(in-theory (disable position-equal))

(defthm integerp-of-position-equal
  (equal (integerp (position-equal x seq))
         (if (position-equal x seq) t nil))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm natp-of-position-equal
  (equal (natp (position-equal x seq))
         (if (position-equal x seq) t nil))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm rationalp-of-position-equal
  (equal (rationalp (position-equal x seq))
         (if (position-equal x seq) t nil))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm acl2-numberp-of-position-equal
  (equal (acl2-numberp (position-equal x seq))
         (if (position-equal x seq) t nil))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm position-equal-under-iff
  (iff (position-equal x seq)
       (if (stringp seq)
           (member-equal x (coerce seq 'list))
         (member-equal x seq)))
  :hints (("Goal" :in-theory (enable position-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For when SEQ is a string.
(defthm <-of-position-equal-and-length-linear
  (implies (and (stringp seq)
                (position-equal x seq) ; rephrase?
                )
           (< (position-equal x seq) (length seq)))
  :rule-classes ((:linear :trigger-terms ((position-equal x seq))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (item x) (lst (coerce seq 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when SEQ is a string.
(defthm <-of-position-equal-and-length
  (implies (stringp seq)
           (equal (< (position-equal x seq) (length seq))
                  (if (position-equal x seq) ; rephrase?
                      t
                    (< 0 (length seq)) ; or (not (equal "" seq))
                    )))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (item x) (lst (coerce seq 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For when SEQ is a list.
(defthm <-of-position-equal-and-len-linear
  (implies (and (not (stringp seq))
                (member-equal x seq))
           (< (position-equal x seq) (len seq)))
  :rule-classes ((:linear :trigger-terms ((position-equal x seq))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (item x) (lst seq))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when SEQ is a list.
(defthm <-of-position-equal-and-len
  (implies (not (stringp seq))
           (equal (< (position-equal x seq) (len seq))
                  (if (member-equal x seq)
                      t
                    (consp seq))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (item x) (lst seq))
           :expand (len seq)
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when SEQ is a list
(defthm position-equal-when-not-member-equal
  (implies (and (not (stringp seq))
                (not (member-equal x seq)))
           (equal (position-equal x seq)
                  nil))
  :hints (("Goal" :in-theory (enable position-equal))))

;; For when SEQ is a list
(defthm position-equal-of-car-same
  (implies (not (stringp seq))
           (equal (position-equal (car seq) seq)
                  (if (consp seq) 0 nil)))
  :hints (("Goal" :in-theory (enable position-equal))))

;; For when SEQ is a list, but happens to be true when SEQ is a string.
(defthm nth-of-position-equal-same
  (equal (nth (position-equal x seq) seq)
         (if (member-equal x seq)
             x
           (car seq) ; unusual case
           ))
  :hints (("Goal" :in-theory (enable position-equal))))
