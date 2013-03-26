; watch.lisp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; This file was originally part of the HONS version of ACL2.  The original
; version of ACL2(h) was contributed by Bob Boyer and Warren A. Hunt, Jr.  The
; design of this system of Hash CONS, function memoization, and fast
; association lists (applicative hash tables) was initially implemented by
; Boyer and Hunt.

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)

; [Jared]: I pulled the WATCH related functionality out of ACL2(h) and into
; this ttag-based book.  In the process I ripped out the previous if-profiling
; stuff, which made it much easier to disentangle watch from memoize.

; WARNING: We never use WATCH anymore.  We do not know if or how it works.  It
; is very likely that this code will not work correctly.

(defttag :watch)
(include-raw "output-raw.lsp")
(include-raw "watch-raw.lsp")

