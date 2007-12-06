;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(defund base10-digit-charp (x)
  (if (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
      t
    nil))
  
(defthm characterp-when-base10-digit-charp
  (implies (base10-digit-charp x)
           (characterp x))
  :hints(("Goal" :in-theory (enable base10-digit-charp))))


(defund base10-digit-char-listp (x)
  (if (consp x)
      (and (base10-digit-charp (car x))
           (base10-digit-char-listp (cdr x)))
    (eq x nil)))

(defthm base10-digit-char-listp-when-not-consp
  (implies (not (consp x))
           (equal (base10-digit-char-listp x)
                  (not x)))
  :hints(("Goal" :in-theory (enable base10-digit-char-listp))))

(defthm base10-digit-char-listp-of-cons
  (equal (base10-digit-char-listp (cons a x))
         (and (base10-digit-charp a)
              (base10-digit-char-listp x)))
  :hints(("Goal" :in-theory (enable base10-digit-char-listp))))

(defthm character-listp-when-base10-digit-char-listp
  (implies (base10-digit-char-listp x)
           (character-listp x))
  :hints(("Goal" :induct (len x))))

(defthm base10-digit-char-listp-of-revappend
  (implies (and (base10-digit-char-listp x)
                (base10-digit-char-listp acc))
           (base10-digit-char-listp (revappend x acc))))



(in-theory (disable digit-to-char))

(defthm base10-digit-charp-of-digit-to-char
  (implies (and (natp n)
                (< n 10))
           (base10-digit-charp (digit-to-char n)))
  :hints(("Goal" :in-theory (enable digit-to-char
                                    base10-digit-charp))))

(defthm equal-of-digit-to-chars
  (implies (and (natp i) (< i 10)
                (natp j) (< j 10))
           (equal (equal (digit-to-char i)
                         (digit-to-char j))
                  (equal i j)))
  :hints(("Goal" :in-theory (enable digit-to-char))))


