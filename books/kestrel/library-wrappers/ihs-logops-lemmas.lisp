; Disable some things from ihs/logops-lemmas.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; NOTE: This book should probably only be used if you also include our books
;; that replace the things from IHS that are disabled here (see comments below).

(include-book "ihs/logops-lemmas" :dir :system)

;; Disable things for which we have better versions in our bv/logapp.lisp book.
(in-theory (disable logapp-<-0 ;we have <-of-logapp-and-0
                    logapp-0
                    associativity-of-logapp
                    unsigned-byte-p-logapp
                    logtail-0-i
                    logtail-logapp
                    logtail-logtail))
