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
; first event is generally local.  :Names is required when macro definitions
; are also needed; the "suitable events .. for supporters" don't include
; macros or supporters of macros.

 (local (include-book "with-supporters-test-sub"))
 :names (mac1 mac2-fn mac2)
 (defun h2 (x)
   (g3 x)))

; Expansion of the above:

#||
(ENCAPSULATE
 ()
 (LOCAL (INCLUDE-BOOK "with-supporters-test-sub"))
 (DEFMACRO MAC1 (X) X)
 (DEFUN MAC2-FN (X) X)
 (DEFMACRO MAC2 (X) (MAC2-FN X))
 (STD::DEFREDUNDANT G1 G2 G3)
 (DEFUN H2 (X) (G3 X)))
||#
