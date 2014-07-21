; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Warning: If you change this book, consider changing the documentation in
; with-supporters.lisp, which refers to this book.

(in-package "ACL2")

(include-book "with-supporters")

(deflabel my-start)

(local
 (progn
   (defun f1 (x)
     (declare (xargs :guard t))
     x)

   (defun f2 (x)
     (declare (xargs :guard (f1 x)))
     x)

   (defun f3 (x)
     (f2 x))))

(with-supporters-after
 my-start ; add redundant events for all those after the event, MY-START (above)
 (defun h1 (x)
   (f3 x)))

; Expansion of the above:

#||
(PROGN (STD::DEFREDUNDANT F1 F2 F3)
       (DEFUN H1 (X) (F3 X)))
||#

(with-supporters

; We generate an (encapsulate () ...) with suitable events (all redundant on
; the first pass) generated for supporters of the events after the first.  The
; first event is generally local.  :Names is generally required when macro
; definitions are also needed; the "suitable events .. for supporters" don't
; include macros or supporters of macros.  However, macro-aliases for
; generated supporting functions are included, as are their suitable
; supporters.

 (local (include-book "with-supporters-test-sub"))
 :names (mac1 mac1-fn) ; don't need to specify mac2, a macro-alias for g2
 (defun h2 (x)
   (g3 x)))

; Expansion of the above:

#||
(ENCAPSULATE NIL
              (LOCAL (INCLUDE-BOOK "with-supporters-test-sub"))
              (DEFUN MAC1-FN (X) X)
              (DEFMACRO MAC1 (X) (MAC1-FN X))
              (STD::DEFREDUNDANT G1 MAC2-FN-B MAC2-FN MAC2 G2 G3)
              (DEFUN H2 (X) (G3 X)))
||#
