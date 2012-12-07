; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "CUTIL")
(include-book "defprojection")
(local (include-book "misc/assert" :dir :system))

(local
 (encapsulate
  ()

  (defund square (x)
    (declare (xargs :guard (integerp x)))
    (* x x))

  (defprojection slow-square-list (x)
    (square x)
    :guard (integer-listp x)
    :optimize nil)

  (defprojection square-list (x)
    (square x)
    :guard (integer-listp x))

  (defprojection program-square-list (x)
    (square x)
    :guard (integer-listp x)
    :mode :program)

  (assert! (let ((x '(1 2 3 4 5 6 7 8 9 10)))
             (and (equal (square-list x)
                         (slow-square-list x))
                  (equal (square-list x)
                         (program-square-list x)))))

  (defthm integerp-of-square
    (implies (integerp x)
             (integerp (square x)))
    :hints(("Goal" :in-theory (enable square))))

  (defprojection slow-square-list-with-result-type (x)
    (square x)
    :guard (integer-listp x)
    :result-type integer-listp
    :optimize nil)

  (defprojection slow-square-list-with-result-type-and-parallelism (x)
    (square x)
    :guard (integer-listp x)
    :result-type integer-listp
    :optimize nil
    :parallelize t)


  ;; Some tests with constants...

  (defprojection add1-list (x)
    (+ 1 x)
    :guard (integer-listp x)
    :parents (foo)
    :rest
    ((defthm add1-list-integer-list
       (implies (integer-listp x)
                (integer-listp (add1-list x))))))

  (defprojection symbol-<-foo-list (x)
    (symbol-< :foo x)
    :guard (symbol-listp x))

  (defprojection symbol-<-bar-list (x)
    (symbol-< 'bar x)
    :guard (symbol-listp x))

  ))







#||

;; Test for includeed book.  (Unlocalize the encapsulate above, first.)  It
;; seems to work just fine.

(in-package "VL")
(include-book ;; fool dependency scanner
 "util-defprojection")
:q

(defparameter *test* (loop for i from 1 to 1000 collect i))

(equal (vl::square-list *test*)
       (vl::slow-square-list *test*))

;; .76 seconds, 320 MB
(progn
    (gc$)
    (time (loop for i from 1 to 10000
                do
                (consp (vl::slow-square-list *test*)))))

;; .43 seconds, 160 MB
(progn
    (gc$)
    (time (loop for i from 1 to 10000
                do
                (consp (vl::square-list *test*)))))

;; .43 seconds, 160 MB
(progn
    (gc$)
    (time (loop for i from 1 to 10000
                do
                (consp (vl::program-square-list *test*)))))



  ))

||#