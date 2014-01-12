; Centaur Miscellaneous Books
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
; load-stobj-tests.lisp -- automation for loading lists into STOBJ arrays.
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "load-stobj")
(include-book "std/util/defconsts" :dir :system)
(include-book "misc/assert" :dir :system)

; These are basic tests of DEF-LOAD-STOBJ-ARRAY.

(defstobj demo$
  (arr :type (array t (0))
       :initially nil
       :resizable t)

  (arr2 :type (array t (0))
       :initially nil
       :resizable t)

  (arr3 :type (array integer (0))
        :initially 0
        :resizable t)

  (arr4 :type (array (unsigned-byte 32) (17))
        :initially 23
        :resizable t))

(def-load-stobj-array load-demo-arr
  :stobj demo$
  :stobjp demo$p
  :index *arri*
  :arrp arrp
  :elemp nil
  :default nil
  :update-arri update-arri
  :resize-arr resize-arr
  :arr-length arr-length)

(defconsts demo$
  (load-demo-arr '(a b c d e) demo$))

(assert! (equal (arri 0 demo$) 'a))
(assert! (equal (arri 1 demo$) 'b))
(assert! (equal (arri 2 demo$) 'c))
(assert! (equal (arri 3 demo$) 'd))
(assert! (equal (arri 4 demo$) 'e))
(assert! (equal (arr-length demo$) 5))


(def-load-stobj-array load-demo-arr2
  :stobj demo$
  :stobjp demo$p
  :index *arr2i*
  :arrp arr2p
  :elemp nil
  :default nil
  :update-arri update-arr2i
  :resize-arr resize-arr2
  :arr-length arr2-length)

(defconsts demo$
  (load-demo-arr2 '(foo bar) demo$))

(assert! (equal (arr2i 0 demo$) 'foo))
(assert! (equal (arr2i 1 demo$) 'bar))
(assert! (equal (arr2-length demo$) 2))


(def-load-stobj-array load-demo-arr3
  :stobj demo$
  :stobjp demo$p
  :index *arr3i*
  :arrp arr3p
  :elemp (integerp x)
  :default 0
  :update-arri update-arr3i
  :resize-arr resize-arr3
  :arr-length arr3-length)

(defconsts demo$
  (load-demo-arr3 '(9 8 7) demo$))

(assert! (equal (arr3i 0 demo$) 9))
(assert! (equal (arr3i 1 demo$) 8))
(assert! (equal (arr3i 2 demo$) 7))
(assert! (equal (arr3-length demo$) 3))


(def-load-stobj-array load-demo-arr4
  :stobj demo$
  :stobjp demo$p
  :index *arr4i*
  :arrp arr4p
  :elemp (unsigned-byte-p 32 x)
  :default 23
  :update-arri update-arr4i
  :resize-arr resize-arr4
  :arr-length arr4-length)


(defconsts demo$
  (load-demo-arr4 '(11 18 17) demo$))

(assert! (equal (arr4i 0 demo$) 11))
(assert! (equal (arr4i 1 demo$) 18))
(assert! (equal (arr4i 2 demo$) 17))
(assert! (equal (arr4-length demo$) 3))

