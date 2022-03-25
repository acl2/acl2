; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This little book does three things.
; - Include xdoc/top, so that the :doc command invokes xdoc.
; - Eliminate the noisy initialization produced by the first use of xdoc.
;   (Instead the noise occurs when including this book.)
; - Defer ttag notes (see :DOC set-deferred-ttag-notes) to reduce that noise.
; The last of these, deferring ttag notes, has nothing in particular to do with
; xdoc, other than reducing noise when including the present book.  But it
; seems a desirable feature in general.  Anyone is welcome to remove the use of
; set-deferred-ttag-notes from init.acl2 as far as I'm concerned.

(in-package "ACL2")

(include-book "top")

; We could use "depends-on", but we might as well simply include the books that
; xdoc::colon-xdoc-init will be including.

(include-book "xdoc/defxdoc-raw" :dir :system :ttags :all)
(include-book "xdoc/topics" :dir :system)
(include-book "system/doc/acl2-doc-wrap" :dir :system)
(include-book "xdoc/display" :dir :system :ttags :all)

(xdoc::colon-xdoc-init)
