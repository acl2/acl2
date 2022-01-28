; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.  We also thank Kestrel.

; This book provides theorems to support reasoning about loop$.  Note that it
; includes the book projects/apply/apply, since loop$ uses apply$.

; When this book is included, three theories are defined:
; apply-book-theory  -- all the introduced by the book apply.lisp
; loop-book-theory   -- all the introduced by the book loop.lisp
;                       (which includes apply-book-theory)
; loop-rules-theory  -- the rules introduced by the book loop.lisp
;                       not including those introduced by apply.lisp

; Notice that loop-book-theory = apply-book-theory + loop-rules-theory.

; The apply-book-theory is thought to be pretty innocuous during proof attempts
; that do not involve apply$ primitives at all.  We see little reason to mess
; with that theory.  But the loop-rules-theory contains some rules which may
; fire (or attempt to fire) even when not in the presence of loop$ primitives.
; These rules are, however, necessary when, say, proving guard conjectures for
; loop$s.

; Here is a secenario in which you might want to use these theories.

; Suppose you have an application book that uses loop$ occasionally, perhaps
; uses apply$ occasionally, but is dominated by events not involving apply$ or
; loop$.  Then you might wish to

; (include-book "projects/apply/loop" :dir :system)
; (in-theory (disable loop-rules-theory))

; Then, embed in the following form each event, <ev>, in your book that
; mentions loop$:

; (encapsulate nil
;   (local (in-theory (enable loop-rules-theory)))
;   <ev>)

; Thus, theorems in your book not involving loop$ are not affected by the
; presence of the loop$ rules but still have the apply$ rules available for
; conjectures that involve apply$ or scions of apply$.

; To shut off all the rules included by this book:

; (in-theory (disable loop-book-theory))

; We have seen a slight speedup with this approach in some Community Books,
; using kestrel/c/atc/generation.lisp as our benchmark.  Generation.lisp has
; five events that mention loop$, makes no other use of apply$, and contains
; many theorems that do not mention loop$.  We produced one version of
; generation.lisp, here called ``version 1,'' in which loop.lisp was locally
; included and the all the rules were left enabled throughout all the proofs.
; In two other versions of generation.lisp the loop-book-theory was immediately
; locally disabled after the local inclusion of loop.lisp and then temporarily
; enabled for each of the five events in generation.lisp that mention loop$.
; We tried two different ways of temporarily enabling.  One of those ways,
; called ``version 2,'' consisted of embedding each event mentioning loop$ in
; this form:

; (encapsulate nil
;  (local (in-theory (enable acl2::loop-book-theory)))
;  <ev>>)

; In the other, called ``version 3,'' we preceded each such event with
; (local (in-theory (enable acl2::loop-book-theory)))
; and followed the event with
; (local (in-theory (disable acl2::loop-book-theory))).

; The certification times of the three versions of generation.lisp on a MacBook
; Pro were

;             seconds
; version 1:  50.253
; version 2:  47.920
; version 3:  48.106

; However, repeated runs show that the time difference between versions 2 and 3
; is insignificant.

(in-package "ACL2")

(deflabel beginning-of-loop-book)

(include-book "apply")
(include-book "loop-lemmas")
(include-book "definductor")
(include-book "relink-fancy-scion")

(make-event
 (let ((world (w state)))
   `(deftheory loop-book-theory
      ',(set-difference-equal (current-theory :here)
                              (current-theory 'beginning-of-loop-book)))))

(make-event
 (let ((world (w state)))
   `(deftheory loop-rules-theory
      ',(set-difference-equal (theory 'loop-book-theory)
                              (theory 'apply-book-theory)))))

