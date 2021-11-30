; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; stringify.lisp
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STR")
(include-book "cat")
(include-book "decimal")

; cert_param: (non-acl2r)

(defun stringify-integer (x)
  (declare (Xargs :guard (integerp x)))
  (if (and (mbt (integerp x))
           (< x 0))
      (cat "-" (nat-to-dec-string (- x)))
    (nat-to-dec-string x)))

(encapsulate
  nil
  (local (defthm nat-to-dec-chars-of-non-natp
           (implies (not (natp x))
                    (equal (nat-to-dec-chars x) '(#\0)))
           :hints(("Goal" :in-theory (enable nat-to-dec-chars)))))

  (defthmd nat-to-dec-string-of-non-natp
    (implies (not (natp x))
             (equal (nat-to-dec-string x) "0"))
    :hints(("Goal" :in-theory (enable nat-to-dec-string)))))


(encapsulate
  nil
  (local (defthm not-member-minus-char-dec-digit-char-listp
           (implies (dec-digit-char-listp x)
                    (not (member-equal #\- x)))))

  (local (defthm not-equal-cons-when-not-member-equal
           (implies (not (member-equal a b))
                    (not (equal b (cons a c))))))

  (local (defthm switch-coerce-cons-string
           (implies (and (syntaxp (not (quotep b)))
                         (characterp a)
                         (character-listp b)
                         (stringp c))
                    (and (equal (Equal (implode (cons a b)) c)
                                (equal (cons a b) (explode c)))
                         (equal (Equal c (implode (cons a b)))
                                (equal (cons a b) (explode c)))))))

  (defthm stringify-integer-one-to-one
    (equal (equal (stringify-integer x)
                  (stringify-integer y))
           (equal (ifix x) (ifix y)))
    :hints (("goal" :use ((:instance not-member-minus-char-dec-digit-char-listp
                                     (x (coerce (nat-to-dec-string x) 'list)))
                          (:instance not-member-minus-char-dec-digit-char-listp
                                     (x (coerce (nat-to-dec-string y) 'list)))
                          (:instance nat-to-dec-string-one-to-one
                                     (n x) (m 0))
                          (:instance nat-to-dec-string-one-to-one
                                     (n y) (m 0)))
             :in-theory (disable not-member-minus-char-dec-digit-char-listp)))))


(defthm stringify-integer-of-non-integer
  (implies (not (integerp x))
           (equal (stringify-integer x) "0"))
  :hints(("Goal" :in-theory (enable nat-to-dec-string-of-non-natp))))

(encapsulate nil
  (local (defthm not-member-slash-char-dec-digit-char-listp
           (implies (dec-digit-char-listp x)
                    (not (member-equal #\/ x)))))

  (defthm not-member-/-stringify-integer
    (not (member-equal #\/ (explode (stringify-integer i)))))

  (defthm not-member-/-nat-to-dec-string
    (not (member-equal #\/ (explode (nat-to-dec-string i))))))

(in-theory (disable stringify-integer))

(defun stringify-rational (x)
  (declare (xargs :guard (rationalp x)))
  (if (or (integerp x)
          (mbe :logic (not (rationalp x))
               :exec nil))
      (stringify-integer x)
    (cat (stringify-integer (numerator x))
         "/"
         (nat-to-dec-string (denominator x)))))

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
                    (and (equal (Equal (implode (append a b)) c)
                                (equal (append a b) (explode c)))
                         (equal (Equal c (implode (append a b)))
                                (equal (append a b) (explode c)))))))

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
  (local (defthm not-member-sharp-char-dec-digit-char-listp
           (implies (dec-digit-char-listp x)
                    (not (member-equal #\# x)))))

  (defthm not-member-sharp-nat-to-dec-string
    (not (member-equal #\# (explode (nat-to-dec-string i)))))

  (defthm not-member-sharp-stringify-integer
    (not (member-equal #\# (explode (stringify-integer i))))
    :hints(("Goal" :in-theory (enable stringify-integer))))

  (defthm not-member-sharp-stringify-rational
    (not (member-equal #\# (explode (stringify-rational r))))))

(encapsulate nil
  (local (defthm not-member-space-char-dec-digit-char-listp
           (implies (dec-digit-char-listp x)
                    (not (member-equal #\Space x)))))

  (defthm not-member-space-nat-to-dec-string
    (not (member-equal #\Space (explode (nat-to-dec-string i)))))

  (defthm not-member-space-stringify-integer
    (not (member-equal #\Space (explode (stringify-integer i))))
    :hints(("Goal" :in-theory (enable stringify-integer))))

  (defthm not-member-space-stringify-rational
    (not (member-equal #\Space (explode (stringify-rational r))))))

(in-theory (disable stringify-rational))

(defun stringify-number (x)
  (declare (xargs :guard (acl2-numberp x)))
  (if (or (rationalp x)
          (mbe :logic (not (acl2-numberp x))
               :exec nil))
      (stringify-rational x)
    (cat "#C(" (stringify-rational (realpart x))
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
                    (and (equal (Equal (implode (list* e f g (append a b))) c)
                                (equal (list* e f g (append a b)) (explode c)))
                         (equal (Equal c (implode (list* e f g (append a b))))
                                (equal (list* e f g (append a b)) (explode c)))))))

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


(defun upper-case-or-dec-digit-char-listp (x)
  (declare (xargs :guard (character-listp x)))
  (if (atom x)
      t
    (and (or (up-alpha-p (car X)) (dec-digit-char-p (car x)))
         (upper-case-or-dec-digit-char-listp (cdr x)))))

(in-theory (disable upper-case-or-dec-digit-char-listp up-alpha-p))

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
  (let ((lst (explode x)))
    (and (consp lst) ;; not the empty string
         (up-alpha-p (car lst))
         (upper-case-or-dec-digit-char-listp (cdr lst)))))

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
        (pkg  (symbol-package-name x)))
    (mbe :logic
         (if (symbolp x)
             (let ((pkg-string
                    (if (equal pkg "ACL2")
                        ""
                      (if (escape-free-symnamep pkg)
                          (cat pkg "::")
                        (cat "|" pkg "|::"))))
                   (name-string
                    (if (escape-free-symnamep name)
                        name
                      (cat "|" name "|"))))
               (cat pkg-string name-string))
           "COMMON-LISP::NIL")
         :exec
         (if (equal pkg "ACL2")
             (if (escape-free-symnamep name)
                 name
               (cat "|" name "|"))
           (if (escape-free-symnamep pkg)
               (if (escape-free-symnamep name)
                   (cat pkg "::" name)
                 (cat pkg "::|" name "|"))
             (if (escape-free-symnamep name)
                 (cat "|" pkg "|::" name)
               (cat "|" pkg "|::|" name "|")))))))

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
  ;; BOZO escaping of strings, proper escaping of characters, ...
  (declare (xargs :guard (atom x)))
  (cond ((symbolp x)      (stringify-symbol x))
        ((stringp x)      (cat "\"" x "\""))
        ((acl2-numberp x) (stringify-number x))
        ((characterp x)   (cat "#\\" (implode (list x))))
        (t                "##**BAD-ATOM**##")))
