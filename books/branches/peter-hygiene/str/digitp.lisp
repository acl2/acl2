; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")
(include-book "eqv")
(local (include-book "arithmetic"))



(defund digitp (x)

  ":Doc-Section Str
  Recognizer for characters #\0 through #\9.~/

  ACL2 provides ~il[digit-char-p] which is more flexible and can recognize
  characters in other bases.  STR::digitp only recognizes base-10 digits, 
  but is roughly twice as fast as digit-char-p, at least on CCL.~/

  Here is an experiment you can run in raw lisp, with times reported in CCL
  on Lisp2.

  (defconstant *chars* 
    (loop for i from 0 to 256 collect (code-char i)))

  ;; 21.876 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digit-char-p c))))

  ;; 10.819 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (STR::digitp c))))"

  (declare (type character x))

  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\0) code)
                     (<= code (char-code #\9))))
       :exec (let ((code (the (unsigned-byte 8) (char-code (the character x)))))
               (declare (type (unsigned-byte 8) code))
               (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                    (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57))))))

(defcong chareqv equal (digitp x) 1
  :hints(("Goal" :in-theory (enable digitp))))




(defund digit-val (x)

  ":Doc-Section Str
  Coerces a digitp character into an integer. ~/

  For instance, the digit-val of #\3 is 3.  For any non-digitp, 0 is returned. ~/
  "

  (declare (type character x)
           (xargs :guard (digitp x)
                  :guard-hints (("Goal" :in-theory (enable digitp)))))

  (mbe :logic 
       (if (digitp x)
           (- (char-code (char-fix x))
              (char-code #\0))
         0)
       :exec 
       (the (unsigned-byte 8)
         (- (the (unsigned-byte 8) (char-code (the character x)))
            (the (unsigned-byte 8) 48)))))

(defcong chareqv equal (digit-val x) 1
  :hints(("Goal" :in-theory (enable digit-val))))

(defthm natp-of-digit-val
  (and (integerp (digit-val x))
       (<= 0 (digit-val x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable digit-val digitp))))

(defthm digit-val-upper-bound
  (< (digit-val x) 10)
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable digit-val digitp))))

(defthm equal-of-digit-val-and-digit-val
  (implies (and (digitp x)
                (digitp y))
           (equal (equal (digit-val x) 
                         (digit-val y))
                  (equal x y)))
  :hints(("Goal" :in-theory (enable digit-val digitp char-fix))))



(defund digit-listp (x)

  ":Doc-Section Str
  Recognizes lists of digitp characters.~/~/
  " 

  (declare (xargs :guard (character-listp x)
                  :guard-hints (("Goal" :in-theory (enable digitp)))))

  (if (consp x)
      (and (mbe :logic (digitp (car x))
                :exec (let ((code (the (unsigned-byte 8) (char-code (the character (car x))))))
                        (declare (type (unsigned-byte 8) code))
                        (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                             (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57)))))
           (digit-listp (cdr x)))
    t))

(defthm digit-listp-when-not-consp
  (implies (not (consp x))
           (digit-listp x))
  :hints(("Goal" :in-theory (enable digit-listp))))

(defthm digit-listp-of-cons
  (equal (digit-listp (cons a x))
         (and (digitp a)
              (digit-listp x)))
  :hints(("Goal" :in-theory (enable digit-listp))))

(defcong charlisteqv equal (digit-listp x) 1
  :hints(("Goal" :in-theory (enable charlisteqv))))



(defund digit-list-value1 (x val)

  (declare (type integer val)
           (xargs :guard (and (character-listp x)
                              (digit-listp x)
                              (natp val))
                  :guard-hints (("Goal" :in-theory (enable digit-val
                                                           digitp)))))

  (mbe :logic (if (consp x)
                  (digit-list-value1 (cdr x)
                                     (+ (digit-val (car x))
                                        (* 10 (nfix val))))
                (nfix val))
       :exec (if (consp x)
                 (digit-list-value1 (cdr x)
                                    (the integer 
                                      (+ (the (unsigned-byte 8)
                                           (- (the (unsigned-byte 8) (char-code (the character (car x))))
                                              (the (unsigned-byte 8) 48)))
                                         (* (the integer 10)
                                            (the integer val)))))
               (the integer val))))

(defund digit-list-value (x)

  ":Doc-Section Str
  Coerces a list of digits into a natural number.~/

  For instance, the digit-list-value of '(#\1 #\0 #\3) is 103.~/
  "

  (declare (xargs :guard (and (character-listp x)
                              (digit-listp x))
                  :verify-guards nil))
  (mbe :logic (if (consp x)
                  (+ (* (expt 10 (1- (len x)))
                        (digit-val (car x)))
                     (digit-list-value (cdr x)))
                0)
       :exec (digit-list-value1 x (the integer 0))))

(defcong charlisteqv equal (digit-list-value x) 1
  :hints(("Goal" :in-theory (enable digit-list-value
                                    charlisteqv))))
      
(defthm natp-of-digit-list-value
  (natp (digit-list-value x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable digit-list-value))))

(encapsulate
 ()
 (set-non-linearp t) ;; implicitly local
 (defthm digit-list-value-upper-bound
   (< (digit-list-value x)
      (expt 10 (len x)))
   :hints(("Goal" 
           :in-theory (enable digit-list-value)
           :do-not '(generalize fertilize)))))

(defthm digit-list-value-upper-bound-free
  (implies (equal n (len x))
           (< (digit-list-value x) (expt 10 n))))


(defthm digit-list-value1-removal
  (equal (digit-list-value1 x val)
         (+ (digit-list-value x) 
            (* (nfix val) (expt 10 (len x)))))
  :hints(("Goal"
          :in-theory (enable digit-list-value1 digit-list-value)
          :induct (digit-list-value1 x val))))

(verify-guards digit-list-value
               :hints(("Goal" :in-theory (enable digit-list-value))))


(defund skip-leading-digits (x)
  (declare (xargs :guard (character-listp x)
                  :guard-hints (("Goal" :in-theory (enable digitp)))))
  (if (consp x)
      (if (mbe :logic (digitp (car x))
               :exec (let ((code (the (unsigned-byte 8) (char-code (the character (car x))))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                            (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57)))))
          (skip-leading-digits (cdr x))
        x)
    nil))

(defcong charlisteqv charlisteqv (skip-leading-digits x) 1
  :hints(("Goal" :in-theory (enable skip-leading-digits
                                    charlisteqv))))

(defthm len-of-skip-leading-digits
  (implies (digitp (car x))
           (< (len (skip-leading-digits x))
              (len x)))
  :hints(("Goal" :in-theory (enable skip-leading-digits))))

(defthm character-listp-of-skip-leading-digits
  (implies (character-listp x)
           (character-listp (skip-leading-digits x)))
  :hints(("Goal" :in-theory (enable skip-leading-digits))))



(defund take-leading-digits (x)

  (declare (xargs :guard (character-listp x)
                  :guard-hints (("Goal" :in-theory (enable digitp)))))
      
  (if (consp x)
      (if (mbe :logic (digitp (car x))
               :exec (let ((code (the (unsigned-byte 8) (char-code (the character (car x))))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                            (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57)))))
          (cons (car x) (take-leading-digits (cdr x)))
        nil)
    nil))
 
(defcong charlisteqv equal (take-leading-digits x) 1
  :hints(("Goal" :in-theory (enable take-leading-digits
                                    charlisteqv
                                    ;; Gross, but gets us equal.
                                    digitp
                                    chareqv
                                    char-fix))))

(defthm character-listp-of-take-leading-digits
  (character-listp (take-leading-digits x))
  :hints(("Goal" :in-theory (enable take-leading-digits
                                    digitp))))

(defthm digit-listp-of-take-leading-digits
  (digit-listp (take-leading-digits x))
  :hints(("Goal" :in-theory (enable take-leading-digits))))

(defthm bound-of-len-of-take-leading-digits
  (<= (len (take-leading-digits x)) (len x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable take-leading-digits))))
