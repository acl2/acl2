; A lightweight book about the built-in function write-byte$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/io/base" :dir :system)) ;for reasoning support

(defthm state-p1-of-write-byte$-alt
  (implies (and (state-p state)
                (symbolp channel)
                (open-output-channel-p channel :byte state)
                (unsigned-byte-p 8 byte) ;this is what's different
                )
           (state-p1 (write-byte$ byte channel state)))
  :hints (("Goal" :use (:instance state-p1-of-write-byte$)
           :in-theory (e/d (open-output-channel-p)
                           (state-p1-of-write-byte$)))))
