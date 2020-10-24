; The BV (bit vector) library.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-syntax")

(include-book "bvchop-def")
(include-book "bvchop")
(include-book "unsigned-byte-p")
(include-book "unsigned-byte-p-forced")
(include-book "lognot")
(include-book "logand")
(include-book "logand2")
(include-book "logior")
(include-book "logior-b")
(include-book "logorc1")
(include-book "logeqv")
(include-book "logxor")
(include-book "logxor-b")
(include-book "logapp")
(include-book "logtail")
(include-book "bvcat-def")
(include-book "bvcat2")
(include-book "getbit-def")
(include-book "getbit")
(include-book "slice-def")
(include-book "slice")
(include-book "slice2")
(include-book "bvcat")
(include-book "bvxor")
(include-book "bitxor")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvuminus")
(include-book "defs-bitwise")
(include-book "defs-shifts")
(include-book "leftrotate")
(include-book "rightrotate")
(include-book "ops32")
(include-book "ops64")
(include-book "putbits")

(include-book "bvshl")
(include-book "bvshr")
