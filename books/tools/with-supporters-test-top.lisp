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

   (defund f2 (x)
     (declare (xargs :guard (f1 x)))
     (if (and (consp x) (consp (cdr x)))
         (f2 (cdr x))
       x))

   (defun f3 (x)
     (f2 x))))

(with-supporters-after
 my-start ; add redundant events for all those after the event, MY-START (above)
 (in-theory (enable (:d f2)))
 (defun h1 (x)
   (f3 x)))

(assert-event (equal (disabledp 'f2)
                     '((:INDUCTION F2)))
              :on-skip-proofs t)

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

; Test use of :names without any events.

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (g5))

(assert-event (equal (disabledp 'g4)
                     '((:DEFINITION G4)))
              :on-skip-proofs t)

(assert-event (equal (g5 '(4 5 6)) 4)
              :on-skip-proofs t)

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 (defun h3 (st)
   (declare (xargs :stobjs st))
   (fld st)))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (stub2))

(assert-event (and (equal (stub1 3) '(3 . 3))
                   (equal (stub2 3) '(3 3)))
              :on-skip-proofs t)

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 (defun h4 (st)
   (declare (xargs :stobjs st))
   (update-fld 3 st)))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (stub1 stub3))

(assert-event (and (equal (stub1 3) '(3 . 3))
                   (equal (stub2 3) '(3 3))
                   (equal (stub3 '(a b c d)) 4))
              :on-skip-proofs t)

(assert-event (equal (disabledp 'g8)
                     nil)
              :on-skip-proofs t)

(assert-event (equal (disabledp 'g9)
                     '((:DEFINITION G9)))
              :on-skip-proofs t)

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (g11 g13)

; Somewhat strangely, the line "Expansion of with-supporters call:" in
; with-supporters-test-top.cert.out shows G13 occurring before G10.  That's
; because G13 was actually introduced in a previous event of this book

 :show :only)

(assert-event (not (function-symbolp 'g10 (w state))))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (g11 g13)
; See comment above.
 :show t)

(assert-event (function-symbolp 'g10 (w state)))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (mac))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :tables (my-tbl))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :with-output (:on :all)
 :tables :all)

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (e1))

(with-supporters
 (local (include-book "with-supporters-test-sub"))
 :names (g16))
