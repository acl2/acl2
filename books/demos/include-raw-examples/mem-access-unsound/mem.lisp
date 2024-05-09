; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; When using books/build/cert.pl, the following forces recertification when
; mem-raw.lsp has changed.
; (depends-on "mem-raw.lsp"

; See :DOC stobj for relevant background.  This book introduces a stobj, mem,
; with a single resizable array field, ar.  It provides a small example to
; illustrate the use of raw Lisp for doing special reads and writes by
; modifying the array primitives directly.

; WARNING: THIS IS UNSOUND!  In particular, one can imagine proving the usual
; read-over-write theorem but then, by execution (perhaps using
; with-local-stobj), proving its negation in a special case.  For an alternate
; approach that is sound, see ../mem-access-sound/mem.lisp; but in place of the
; usual read-over-write lemma that is proved here, below, there is a weaker
; version.

; The following log shows how this works, where 8 is not a special address and
; 10 is a special address.  You can ignore that last part about raw mode, but
; if you're curious, look at mem-raw.lsp.

; This assumes that we have evaluated (include-book "mem").
#|
ACL2 !>(ari 8 mem)
0
ACL2 !>(update-ari 8 20 mem)
<mem>
ACL2 !>(ari 8 mem)
20
ACL2 !>(ari 10 mem)
NOTE: Returning result for read at special address 10.

11
ACL2 !>(update-ari 10 100 mem)
NOTE: Calling update-ari on special address 10.

<mem>
ACL2 !>(ari 10 mem)
NOTE: Returning result for read at special address 10.

11
ACL2 !>(set-raw-mode-on!)

TTAG NOTE: Adding ttag :RAW-MODE-HACK from the top level loop.
ACL2 P>(funcall *old-ari* 10 mem)
100
ACL2 P>
|#

(in-package "ACL2")

(defstobj mem
  (ar :type (array (unsigned-byte 8) (1024))
      :resizable t ; optional
      :initially 0)
; The use of :inline nil here is just for emphasis, since it's the default.  It
; is critical not to inline functions that we will smash in raw Lisp.
  :inline nil
  :non-memoizable t ; optional
  )

; The following is provable but is not true -- hence, this approach is unsound!
; -- after we smash ari and update-ari by loading mem-raw.lsp (below).
(defthm read-over-write
  (implies (and (natp addr1)
                (natp addr2))
           (equal (ari addr1 (update-ari addr2 val mem))
                  (if (equal addr1 addr2)
                      val
                    (ari addr1 mem)))))

(include-book "tools/include-raw" :dir :system)

(defttag :mem-special) ; required before calling include-raw

(include-raw "mem-raw.lsp")
