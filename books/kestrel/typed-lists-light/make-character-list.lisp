; A lightweight book about the built-in function make-character-list
;
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable make-character-list))

(defthm character-listp-of-make-character-list
  (character-listp (make-character-list x))
  :hints (("Goal" :in-theory (enable make-character-list))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x))
         (len x))
  :hints (("Goal" :in-theory (enable make-character-list))))

(defthm make-character-list-iff
  (iff (make-character-list x)
       (consp x))
  :hints (("Goal" :in-theory (enable make-character-list))))

(defthm consp-of-make-character-list
  (equal (consp (make-character-list x))
         (consp x))
  :hints (("Goal" :in-theory (enable make-character-list))))

(defthm car-of-make-character-list
  (equal (car (make-character-list x))
         (if (not (consp x))
             nil
           (let ((car (first x)))
             (if (characterp car)
                 car
               *null-char*))))
  :hints (("Goal" :in-theory (enable make-character-list))))

(defthm nth-of-make-character-list
  (equal (nth n (make-character-list x))
         (if (<= (len x) (nfix n))
             nil
           (let ((char (nth n x)))
             (if (characterp char)
                 char
               *null-char*))))
  :hints (("Goal" :in-theory (enable make-character-list (:i nth)))))
