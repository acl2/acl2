; BV Library: 64-bit operations
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

(defmacro and64 (x y)
  `(bvand 64 ,x ,y))

(defmacro plus64 (x y)
  `(bvplus 64 ,x ,y))

(defmacro or64 (x y)
  `(bvor 64 ,x ,y))

(defmacro xor64 (x y)
  `(bvxor 64 ,x ,y))

(defmacro not64 (x)
  `(bvnot 64 ,x))
