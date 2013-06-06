; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

; stringify.lisp
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STR")

(include-book "natstr")

(defun stringify-integer (x)
  (declare (Xargs :guard (integerp x)))
  (if (and (integerp x) (< x 0))
      (concatenate 'string "-" (natstr (- x)))
    (natstr x)))


(encapsulate
  nil
  (local (defthm natchars-of-non-natp
           (implies (not (natp x))
                    (equal (natchars x) '(#\0)))
           :hints(("Goal" :in-theory (enable natchars)))))

  (defthmd natstr-of-non-natp
    (implies (not (natp x))
             (equal (natstr x) "0"))
    :hints(("Goal" :in-theory (enable natstr)))))



(local (defthmd switch-coerce-list
         (implies (and (character-listp x) (stringp y))
                  (equal (equal x (coerce y 'list))
                         (equal (coerce x 'string) y)))))

(local (defthmd switch-coerce-string
         (implies (and (character-listp y) (stringp x))
                  (equal (equal x (coerce y 'string))
                         (equal (coerce x 'list) y)))))

(local (defthm equal-coerce-list
         (implies (and (stringp y) (stringp x))
                  (equal (Equal (coerce x 'list) (coerce y 'list))
                         (equal x y)))
         :hints(("Goal" :in-theory (enable switch-coerce-list)))))

(encapsulate
  nil

  (local (defthm not-member-minus-char-digit-listp
           (implies (digit-listp x)
                    (not (member-equal #\- x)))))

  (local (defthm not-equal-cons-when-not-member-equal
           (implies (not (member-equal a b))
                    (not (equal b (cons a c))))))

  (local (defthm switch-coerce-cons-string
           (implies (and (syntaxp (not (quotep b)))
                         (characterp a)
                         (character-listp b)
                         (stringp c))
                    (and (equal (Equal (coerce (cons a b) 'string) c)
                                (equal (cons a b) (coerce c 'list)))
                         (equal (Equal c (coerce (cons a b) 'string))
                                (equal (cons a b) (coerce c 'list)))))))

  (local (in-theory (disable switch-coerce-string)))

  (defthm stringify-integer-one-to-one
    (equal (equal (stringify-integer x)
                  (stringify-integer y))
           (equal (ifix x) (ifix y)))
    :hints (("goal" :use ((:instance not-member-minus-char-digit-listp
                           (x (coerce (natstr x) 'list)))
                          (:instance not-member-minus-char-digit-listp
                           (x (coerce (natstr y) 'list)))
                          (:instance natstr-one-to-one
                           (n x) (m 0))
                          (:instance natstr-one-to-one
                           (n y) (m 0)))
             :in-theory (disable not-member-minus-char-digit-listp)))))

(defthm stringify-integer-of-non-integer
  (implies (not (integerp x))
           (equal (stringify-integer x) "0"))
  :hints(("Goal" :in-theory (enable natstr-of-non-natp))))

(encapsulate nil
  (local (defthm not-member-slash-char-digit-listp
           (implies (digit-listp x)
                    (not (member-equal #\/ x)))))

  (defthm not-member-/-stringify-integer
    (not (member-equal #\/ (coerce (stringify-integer i) 'list))))

  (defthm not-member-/-natstr
    (not (member-equal #\/ (coerce (natstr i) 'list)))))

(in-theory (disable stringify-integer))

(defun stringify-rational (x)
  (declare (xargs :guard (rationalp x)))
  (if (or (integerp x) (mbe :logic (not (rationalp x)) :exec nil))
      (stringify-integer x)
    (concatenate 'string (stringify-integer (numerator x))
                 "/" (natstr (denominator x)))))


(local (defthm member-equal-append
         (iff (member-equal k (append a b))
              (or (member-equal k a)
                  (member-equal k b)))))


(local (defun cdr-both-equal (a b)
         (if (or (atom a) (atom b))
             nil
           (and (and (consp a) (consp b)
                     (equal (car a) (car b)))
                (cdr-both-equal (cdr a) (cdr b))))))

(local (defthm equal-appends-with-nonmembers-implies-components-equal
         (implies (and (not (member-equal x a))
                       (not (member-equal x b))
                       (not (member-equal x c))
                       (not (member-equal x d))
                       (true-listp a)
                       (true-listp c))
                  (equal (equal (append a (cons x b))
                                (append c (cons x d)))
                         (and (equal a c) (equal b d))))
         :hints ((and stable-under-simplificationp
                      `(:induct (cdr-both-equal a c)
                        :expand ((append a (cons x b))
                                 (append c (cons x d))))))
         :otf-flg t))

(encapsulate
  nil
  
  (local (defthm switch-coerce-append-string
           (implies (and (character-listp a)
                         (character-listp b)
                         (stringp c))
                    (and (equal (Equal (coerce (append a b) 'string) c)
                                (equal (append a b) (coerce c 'list)))
                         (equal (Equal c (coerce (append a b) 'string))
                                (equal (append a b) (coerce c 'list)))))))

  (local (defthm not-equal-if-not-members-append-cons
           (implies (not (member-equal a c))
                    (not (equal (append b (cons a d)) c)))))

  (defthm stringify-rational-one-to-one
    (equal (equal (stringify-rational x)
                  (stringify-rational y))
           (equal (rfix x) (rfix y)))
    :hints (("goal" :use ((:instance not-member-/-stringify-integer
                           (i x))
                          (:instance not-member-/-stringify-integer
                           (i y))
                          (:instance not-member-/-stringify-integer
                           (i (numerator x)))
                          (:instance not-member-/-stringify-integer
                           (i (numerator y)))
                          (:instance stringify-integer-one-to-one
                           (x y) (y 0))
                          (:instance stringify-integer-one-to-one
                           (x x) (y 0))
                          (:instance rational-implies2)
                          (:instance rational-implies2 (x y)))
             :in-theory (disable not-member-/-stringify-integer
                                 rational-implies2)))))

(encapsulate nil
  (local (defthm not-member-sharp-char-digit-listp
           (implies (digit-listp x)
                    (not (member-equal #\# x)))))

  (defthm not-member-sharp-natstr
    (not (member-equal #\# (coerce (natstr i) 'list))))

  (defthm not-member-sharp-stringify-integer
    (not (member-equal #\# (coerce (stringify-integer i) 'list)))
    :hints(("Goal" :in-theory (enable stringify-integer))))

  (defthm not-member-sharp-stringify-rational
    (not (member-equal #\# (coerce (stringify-rational r) 'list)))))

(encapsulate nil
  (local (defthm not-member-space-char-digit-listp
           (implies (digit-listp x)
                    (not (member-equal #\Space x)))))

  (defthm not-member-space-natstr
    (not (member-equal #\Space (coerce (natstr i) 'list))))

  (defthm not-member-space-stringify-integer
    (not (member-equal #\Space (coerce (stringify-integer i) 'list)))
    :hints(("Goal" :in-theory (enable stringify-integer))))

  (defthm not-member-space-stringify-rational
    (not (member-equal #\Space (coerce (stringify-rational r) 'list)))))

(in-theory (disable stringify-rational))

(defun stringify-number (x)
  (declare (xargs :guard (acl2-numberp x)))
  (if (or (rationalp x) (mbe :logic (not (acl2-numberp x)) :exec nil))
      (stringify-rational x)
    (concatenate 'string
                 "#C(" (stringify-rational (realpart x))
                 " " (stringify-rational (imagpart x)) ")")))

(encapsulate
  nil
  
  (local (defthm switch-coerce-list*-append-string
           (implies (and (character-listp a)
                         (character-listp b)
                         (characterp e)
                         (characterp f)
                         (characterp g)
                         (stringp c))
                    (and (equal (Equal (coerce (list* e f g (append a b)) 'string) c)
                                (equal (list* e f g (append a b)) (coerce c 'list)))
                         (equal (Equal c (coerce (list* e f g (append a b)) 'string))
                                (equal (list* e f g (append a b)) (coerce c 'list)))))))

  (local (defthmd not-equal-by-len
           (implies (not (equal (len x) (len y)))
                    (not (Equal x y)))))

  (local (defthm len-append-linear
           (<= (len x) (len (append z x)))
           :rule-classes :linear))

  (local (defthm not-equal-x-cons-y-append-z-x
           (not (equal x (cons y (append z x))))
           :hints (("goal" :in-theory (enable not-equal-by-len)))))

  (local (defthm equal-append-to-tail
           (implies (and (true-listp a) (true-listp b))
                    (equal (equal (append a c) (append b c))
                           (equal a b)))
           :hints (("goal" :induct (cdr-both-equal a b)
                    :expand ((append a c) (append b c))))))

  (defthm stringify-number-one-to-one
    (equal (equal (stringify-number x)
                  (stringify-number y))
           (equal (fix x) (fix y)))
    :hints (("goal" :use ((:instance not-member-space-stringify-rational
                           (r x))
                          (:instance not-member-space-stringify-rational
                           (r y))
                          (:instance not-member-space-stringify-rational
                           (r (realpart x)))
                          (:instance not-member-space-stringify-rational
                           (r (realpart y)))
                          (:instance not-member-space-stringify-rational
                           (r (imagpart x)))
                          (:instance not-member-space-stringify-rational
                           (r (imagpart y)))
                          (:instance stringify-rational-one-to-one
                           (x y) (y 0))
                          (:instance stringify-rational-one-to-one
                           (x x) (y 0))
                          (:instance realpart-imagpart-elim)
                          (:instance realpart-imagpart-elim (x y)))
             :in-theory (disable not-member-space-stringify-rational
                                 realpart-imagpart-elim)))))

(defun upper-casep (x)
  (declare (type character x))
  (mbe :logic (let ((code (char-code (char-fix x))))
                   (and (<= (char-code #\A) code)
                        (<= code (char-code #\Z))))
       :exec (let ((code (the (unsigned-byte 8)
                              (char-code (the character x)))))
                  (declare (type (unsigned-byte 8) code))
                  (and (<= (the (unsigned-byte 8) 65)
                           (the (unsigned-byte 8) code))
                       (<= (the (unsigned-byte 8) code)
                           (the (unsigned-byte 8) 90))))))

(defun upper-case-or-digit-listp (x)
  (declare (xargs :guard (character-listp x)))
  (if (atom x)
      t
    (and (or (upper-casep (car X)) (digitp (car x)))
         (upper-case-or-digit-listp (cdr x)))))

(in-theory (disable upper-case-or-digit-listp upper-casep))

(local (defthm characterp-car-of-character-listp
         (implies (and (character-listp x)
                       (consp x))
                  (characterp (car x)))))

(local (defthm character-listp-cdr-of-character-listp
         (implies (character-listp x)
                  (character-listp (cdr x)))))

;; Like may-need-slashes-fn, but hard-coded base 10.  Mainly we just need to be
;; able to show that we can't confuse this with a character, number, or string,
;; for which it's enough to show that it can't start with #, ", -, or a digit.
;; Then we'll also want to use bars for anything lower-case.  We can afford to
;; be a bit more conservative than may-need-slashes-fn in order to ease the
;; logic, but we still don't want to use vertical bars for absolutely
;; everything.
;; We'll allow the first letter to be only an upper-case letter, and the rest
;; to be either upper-case or digits.
(defun escape-free-symnamep (x)
  (declare (xargs :guard (stringp x)))
  (let ((lst (coerce x 'list)))
    (and (consp lst) ;; not the empty string
         (upper-casep (car lst))
         (upper-case-or-digit-listp (cdr lst)))))

(local (defthm assoc-append
         (equal (append (append a b) c)
                (append a b c))))

(local (defthm fold-constants-append
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (append a b c)
                         (append (append a b) c)))))


;; This may perform somewhat poorly due to the coerce to list in the
;; escape-free-symname check.
(defun stringify-symbol (x)
  (declare (type symbol x))
  (let ((name (symbol-name x))
        (pkg (symbol-package-name x)))
    (mbe :logic
         (if (symbolp x)
             (let ((pkg-string
                    (if (equal pkg "ACL2")
                        ""
                      (if (escape-free-symnamep pkg)
                          (concatenate 'string pkg "::")
                        (concatenate 'string "|" pkg "|::"))))
                   (name-string
                    (if (escape-free-symnamep name)
                        name
                      (concatenate 'string "|" name "|"))))
               (concatenate 'string pkg-string name-string))
           "COMMON-LISP::NIL")
         :exec
         (if (equal pkg "ACL2")
             (if (escape-free-symnamep name)
                 name
               (concatenate 'string "|" name "|"))
           (if (escape-free-symnamep pkg)
               (if (escape-free-symnamep name)
                   (concatenate 'string pkg "::" name)
                 (concatenate 'string pkg "::|" name "|"))
             (if (escape-free-symnamep name)
                 (concatenate 'string "|" pkg "|::" name)
               (concatenate 'string "|" pkg "|::|" name "|")))))))

(in-theory (disable escape-free-symnamep))


;; Maybe someday we can prove this and go on with the rest of the proof --
;; seems pretty tedious though.
;; (defthm stringify-symbol-unique
;;   (equal (equal (stringify-symbol x)
;;                 (stringify-symbol y))
;;          (equal (and (symbolp x) x)
;;                 (and (symbolp y) y)))
;;   :hints ((and stable-under-simplificationp
;;                (equal (caar (last clause)) 'not)
;;                (symbolp (cadar (last clause)))
;;                `(:use ((:instance symbol-equality
;;                         (acl2::s1 ,(cadar (last clause))) (acl2::s2 nil)))))))


       
(defun stringify-atom (x)
  (declare (Xargs :guard (not (consp x))))
  (cond ((symbolp x) (stringify-symbol x))
        ((stringp x) (concatenate 'string "\"" x "\""))
        ((acl2-numberp x) (stringify-number x))
        ((characterp x)
         (concatenate 'string "#\\" (coerce (list x) 'string)))
        (t "##**BAD-ATOM**##")))
         
