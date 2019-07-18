; BV Library: 32-bit operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defs-bitwise")
(include-book "bvplus")

(defmacro and32 (x y)
  `(bvand 32 ,x ,y))

(defmacro plus32 (x y)
  `(bvplus 32 ,x ,y))

(defmacro or32 (x y)
  `(bvor 32 ,x ,y))

(defmacro xor32 (x y)
  `(bvxor 32 ,x ,y))

(defmacro not32 (x)
  `(bvnot 32 ,x))
