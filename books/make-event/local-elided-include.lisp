; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book checks that expansions are stored as expected.  The constant below
; is what we expect to find for the :expansion-alist field of
; local-elided.cert.  The last form in this file shows how we can do useful
; file IO on behalf of a make-event.

(in-package "ACL2")

; Here is the expected :expansion-alist from local-elided.cert when provisional
; certification was not used.
(defconst *local-elided-expansion-alist*
  '((1 LOCAL (VALUE-TRIPLE :ELIDED))
    (2 LOCAL (VALUE-TRIPLE :ELIDED))
    (3 LOCAL (VALUE-TRIPLE :ELIDED))
    (5
     PROGN
     (LOCAL (VALUE-TRIPLE :ELIDED))
     (LOCAL (VALUE-TRIPLE :ELIDED))
     (ENCAPSULATE ((BAR2 (X) T))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (DEFTHM BAR2-PRESERVES-CONSP
         (IMPLIES (CONSP X)
                  (CONSP (BAR2 X))))))
    (6
     ENCAPSULATE ((BAR2 (X) T))
     (LOCAL (VALUE-TRIPLE :ELIDED))
     (DEFTHM BAR2-PRESERVES-CONSP
       (IMPLIES (CONSP X) (CONSP (BAR2 X)))))
    (7 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (8 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (9 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (10 DEFUN FOO-3 (X) X)
    (12 ENCAPSULATE
        NIL (MY-LOCAL (DEFUN G3 (X) X))
        (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))
        (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))
        (MY-LOCAL (DEFUN G4 (X) X))
        (RECORD-EXPANSION
         (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X)))))
         (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                (LOCAL (VALUE-TRIPLE :ELIDED)))))))

; Here is the expected :expansion-alist from local-elided.cert when provisional
; certification was used.
(defconst *local-elided-expansion-alist-pcert*
  '((1 LOCAL (VALUE-TRIPLE :ELIDED))
    (2 LOCAL (VALUE-TRIPLE :ELIDED))
    (3 LOCAL (VALUE-TRIPLE :ELIDED))
    (5 PROGN (LOCAL (VALUE-TRIPLE :ELIDED))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (ENCAPSULATE ((BAR2 (X) T))
         (LOCAL (VALUE-TRIPLE :ELIDED))
         (DEFTHM BAR2-PRESERVES-CONSP
           (IMPLIES (CONSP X) (CONSP (BAR2 X))))))
    (6 ENCAPSULATE ((BAR2 (X) T))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (DEFTHM BAR2-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR2 X)))))
    (7 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (8 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (9 ENCAPSULATE ((BAR3 (X) T))
       (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                         (LOCAL (VALUE-TRIPLE :ELIDED)))
       (DEFTHM BAR3-PRESERVES-CONSP
         (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
    (10 DEFUN FOO-3 (X) X)
    (12 ENCAPSULATE
        NIL (MY-LOCAL (DEFUN G3 (X) X))
        (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))
        (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))
        (MY-LOCAL (DEFUN G4 (X) X))
        (RECORD-EXPANSION
         (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X)))))
         (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                (LOCAL (VALUE-TRIPLE :ELIDED)))))))

; Include the book whose certificate we want to check.
(include-book "local-elided")

(include-book "std/testing/must-succeed" :dir :system)

; Define read-list (used below).
(include-book "misc/file-io" :dir :system)

; Check that the above constant is equal to the :expansion-alist field of the
; certificate of the "local-elided" book.
(must-succeed
 (mv-let (erp val state)
   (read-list "local-elided.pcert0" 'top state)
   (declare (ignore val))
   (er-let* ((forms (read-list "local-elided.cert" 'top state)))
            (let ((erp (not (equal (cadr (member-eq :expansion-alist forms))
                                   (if erp ; no .pcert0 file
                                       *local-elided-expansion-alist*
                                     *local-elided-expansion-alist-pcert*)))))
              (mv erp nil state)))))
