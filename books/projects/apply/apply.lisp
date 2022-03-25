; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.  We also thank Kestrel.

; This book contains lemmas that are helpful when reasoning about apply$ and
; user-defined apply$ scions.  However, if loop$ is being used we recommend
; using the book loop.lisp on this directory instead of this book.  (The loop$
; book includes this book but has many lemmas designed to help proving guard
; conjectures about loop$s.)

; This book also defines a theory, (theory 'apply-book-theory), consisting of
; all the rules introduced by this book.  If you include this book and then
; (in-theory (disable apply-book-theory)) the enabled rules will be as though
; this book were not included.  Practically speaking we see no reason to do
; this since the rules introduced here all concern apply$ primitives and won't
; be tried unless those primitives are in the goal conjecture.  However, see
; the comment in the book projects/apply/loop.lisp.

(in-package "ACL2")

(deflabel beginning-of-apply-book)
(include-book "base")
(make-event
 (let ((world (w state)))
   `(deftheory apply-book-theory
      ',(set-difference-equal (current-theory :here)
                              (current-theory 'beginning-of-apply-book)))))
