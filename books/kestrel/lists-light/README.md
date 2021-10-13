; A lightweight library about lists.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

This directory contains a lightweight library about lists.  Generally
speaking, each file deals with a single function.

This directory follows a lightweight or minimalist design.  We aim to
have each book contain as few non-local include-books and
function/macro definitions as possible (ideally, none).  This gives
the user of these books maximum flexibility; a user who includes our
book about append is not forced to also include, say, our book about
nthcdr, or any other irrelevant material.
