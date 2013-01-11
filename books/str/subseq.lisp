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


; subseq.lisp
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(local (include-book "arithmetic"))
(local (include-book "misc/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/coerce" :dir :system))

;; NOTE: These get globally disabled by including this book!  This is probably
;; how things ought to be.

(in-theory (disable subseq subseq-list))

(local (in-theory (enable subseq subseq-list)))

(defthm len-of-subseq-list
  (equal (len (subseq-list x start end))
         (nfix (- end start))))

(defthm true-listp-subseq-list
  (true-listp (subseq-list x start end))
  :rule-classes :type-prescription)

(defthm stringp-of-subseq
  (equal (stringp (subseq x start end))
         (stringp x)))

(defthm length-of-subseq
  (equal (length (subseq x start end))
         (nfix (- (or end (length x)) start))))

(defthm len-of-subseq
  (equal (len (subseq x start end))
         (if (stringp x)
             0
           (nfix (- (or end (len x)) start)))))
