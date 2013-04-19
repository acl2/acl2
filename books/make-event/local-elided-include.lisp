; This book checks that expansions are stored as expected.  The constant below
; is what we expect to find for the :expansion-alist field of
; local-elided.cert.  The last form in this file shows how we can do useful
; file IO on behalf of a make-event.

(in-package "ACL2")

; Here is the expected :expansion-alist from local-elided.cert when provisional
; certification was not used.
(defconst *local-elided-expansion-alist*
  '((1 RECORD-EXPANSION
       (LOCAL (MAKE-EVENT '(DEFUN FOO (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (2 RECORD-EXPANSION
       (MAKE-EVENT '(LOCAL (DEFUN FOO (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (3 RECORD-EXPANSION
       (MAKE-EVENT '(LOCAL (DEFUN FOO-2 (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (5
     RECORD-EXPANSION
     (PROGN
      (MAKE-EVENT '(LOCAL (DEFUN G (X) X)))
      (LOCAL (DEFUN G2 (X) X))
      (MAKE-EVENT (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                                       (LOCAL (DEFUN BAR2 (X) (FOO X)))
                                       (DEFTHM BAR2-PRESERVES-CONSP
                                         (IMPLIES (CONSP X)
                                                  (CONSP (BAR2 X))))))))
     (PROGN
      (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN G (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED)))
      (LOCAL (VALUE-TRIPLE :ELIDED))
      (RECORD-EXPANSION
       (MAKE-EVENT
        (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                             (LOCAL (DEFUN BAR2 (X) (FOO X)))
                             (DEFTHM BAR2-PRESERVES-CONSP
                               (IMPLIES (CONSP X) (CONSP (BAR2 X)))))))
       (ENCAPSULATE ((BAR2 (X) T))
                    (LOCAL (DEFUN BAR2 (X) (FOO X)))
                    (DEFTHM BAR2-PRESERVES-CONSP
                      (IMPLIES (CONSP X)
                               (CONSP (BAR2 X))))))))
    (6
     RECORD-EXPANSION
     (MAKE-EVENT
      (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                           (LOCAL (DEFUN BAR2 (X) (FOO X)))
                           (DEFTHM BAR2-PRESERVES-CONSP
                             (IMPLIES (CONSP X) (CONSP (BAR2 X)))))))
     (ENCAPSULATE ((BAR2 (X) T))
                  (LOCAL (DEFUN BAR2 (X) (FOO X)))
                  (DEFTHM BAR2-PRESERVES-CONSP
                    (IMPLIES (CONSP X) (CONSP (BAR2 X))))))
    (7
     RECORD-EXPANSION
     (MAKE-EVENT
      (VALUE '(ENCAPSULATE ((BAR3 (X) T))
                           (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                           (DEFTHM BAR3-PRESERVES-CONSP
                             (IMPLIES (CONSP X) (CONSP (BAR3 X)))))))
     (ENCAPSULATE
      ((BAR3 (X) T))
      (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                        (LOCAL (VALUE-TRIPLE :ELIDED)))
      (DEFTHM BAR3-PRESERVES-CONSP
        (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
    (8 RECORD-EXPANSION
       (ENCAPSULATE ((BAR3 (X) T))
                    (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                    (DEFTHM BAR3-PRESERVES-CONSP
                      (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
       (ENCAPSULATE
        ((BAR3 (X) T))
        (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))
        (DEFTHM BAR3-PRESERVES-CONSP
          (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
    (10 RECORD-EXPANSION
        (MUST-FAIL (ENCAPSULATE ((BAR3 (X) T))
                                (LOCAL (DEFUN BAR3 (X) (FOO X)))
                                (DEFTHM BAR3-PRESERVES-CONSP
                                  (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
        (VALUE-TRIPLE 'T))
    (11 RECORD-EXPANSION
        (MAKE-EVENT '(DEFUN FOO-3 (X) X))
        (DEFUN FOO-3 (X) X))
    (13
     RECORD-EXPANSION
     (ENCAPSULATE NIL (MY-LOCAL (DEFUN G3 (X) X))
                  (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                  (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                  (MY-LOCAL (DEFUN G4 (X) X))
                  (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                         (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X))))))
     (ENCAPSULATE
      NIL (MY-LOCAL (DEFUN G3 (X) X))
      (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED)))
      (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED)))
      (MY-LOCAL (DEFUN G4 (X) X))
      (RECORD-EXPANSION
       (PROGN (MY-LOCAL (DEFUN G5 (X) X))
              (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X)))))
       (PROGN
        (MY-LOCAL (DEFUN G5 (X) X))
        (RECORD-EXPANSION (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X))))
                          (LOCAL (VALUE-TRIPLE :ELIDED)))))))))

; Here is the expected :expansion-alist from local-elided.cert when provisional
; certification was used.
(defconst *local-elided-expansion-alist-pcert*
  '((1 RECORD-EXPANSION
       (LOCAL (MAKE-EVENT '(DEFUN FOO (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (2 RECORD-EXPANSION
       (MAKE-EVENT '(LOCAL (DEFUN FOO (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (3 RECORD-EXPANSION
       (MAKE-EVENT '(LOCAL (DEFUN FOO-2 (X) X)))
       (LOCAL (VALUE-TRIPLE :ELIDED)))
    (5
     RECORD-EXPANSION
     (PROGN
      (MAKE-EVENT '(LOCAL (DEFUN G (X) X)))
      (LOCAL (DEFUN G2 (X) X))
      (MAKE-EVENT (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                                       (LOCAL (DEFUN BAR2 (X) (FOO X)))
                                       (DEFTHM BAR2-PRESERVES-CONSP
                                         (IMPLIES (CONSP X)
                                                  (CONSP (BAR2 X))))))))
     (PROGN
      (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN G (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED)))
      (LOCAL (VALUE-TRIPLE :ELIDED))
      (RECORD-EXPANSION
       (MAKE-EVENT
        (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                             (LOCAL (DEFUN BAR2 (X) (FOO X)))
                             (DEFTHM BAR2-PRESERVES-CONSP
                               (IMPLIES (CONSP X) (CONSP (BAR2 X)))))))
       (ENCAPSULATE ((BAR2 (X) T))
                    (LOCAL (VALUE-TRIPLE :ELIDED)) ; eliding was optional
                    (DEFTHM BAR2-PRESERVES-CONSP
                      (IMPLIES (CONSP X)
                               (CONSP (BAR2 X))))))))
    (6
     RECORD-EXPANSION
     (MAKE-EVENT
      (VALUE '(ENCAPSULATE ((BAR2 (X) T))
                           (LOCAL (DEFUN BAR2 (X) (FOO X)))
                           (DEFTHM BAR2-PRESERVES-CONSP
                             (IMPLIES (CONSP X) (CONSP (BAR2 X)))))))
     (ENCAPSULATE ((BAR2 (X) T))
                  (LOCAL (VALUE-TRIPLE :ELIDED)) ; eliding was optional
                  (DEFTHM BAR2-PRESERVES-CONSP
                    (IMPLIES (CONSP X) (CONSP (BAR2 X))))))
    (7
     RECORD-EXPANSION
     (MAKE-EVENT
      (VALUE '(ENCAPSULATE ((BAR3 (X) T))
                           (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                           (DEFTHM BAR3-PRESERVES-CONSP
                             (IMPLIES (CONSP X) (CONSP (BAR3 X)))))))
     (ENCAPSULATE
      ((BAR3 (X) T))
      (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                        (LOCAL (VALUE-TRIPLE :ELIDED))) ; eliding was optional
      (DEFTHM BAR3-PRESERVES-CONSP
        (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
    (8 RECORD-EXPANSION
       (ENCAPSULATE ((BAR3 (X) T))
                    (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                    (DEFTHM BAR3-PRESERVES-CONSP
                      (IMPLIES (CONSP X) (CONSP (BAR3 X)))))
       (ENCAPSULATE
        ((BAR3 (X) T))
        (RECORD-EXPANSION (MAKE-EVENT '(LOCAL (DEFUN BAR3 (X) (FOO X))))
                          (LOCAL (VALUE-TRIPLE :ELIDED))) ; eliding was optional
        (DEFTHM BAR3-PRESERVES-CONSP
          (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
    (10 RECORD-EXPANSION
        (MUST-FAIL (ENCAPSULATE ((BAR3 (X) T))
                                (LOCAL (DEFUN BAR3 (X) (FOO X)))
                                (DEFTHM BAR3-PRESERVES-CONSP
                                  (IMPLIES (CONSP X) (CONSP (BAR3 X))))))
        (VALUE-TRIPLE 'T))
    (11 RECORD-EXPANSION
        (MAKE-EVENT '(DEFUN FOO-3 (X) X))
        (DEFUN FOO-3 (X) X))
    (13
     RECORD-EXPANSION
     (ENCAPSULATE NIL (MY-LOCAL (DEFUN G3 (X) X))
                  (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                  (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                  (MY-LOCAL (DEFUN G4 (X) X))
                  (PROGN (MY-LOCAL (DEFUN G5 (X) X))
                         (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X))))))
     (ENCAPSULATE
      NIL (MY-LOCAL (DEFUN G3 (X) X))
      (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G3 (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED))) ; eliding was optional
      (RECORD-EXPANSION (MAKE-EVENT '(MY-LOCAL (DEFUN G4 (X) X)))
                        (LOCAL (VALUE-TRIPLE :ELIDED))) ; eliding was optional
      (MY-LOCAL (DEFUN G4 (X) X))
      (RECORD-EXPANSION
       (PROGN (MY-LOCAL (DEFUN G5 (X) X))
              (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X)))))
       (PROGN
        (MY-LOCAL (DEFUN G5 (X) X))
        (RECORD-EXPANSION (MY-LOCAL (MAKE-EVENT (VALUE '(DEFUN G6 (X) X))))
                          (LOCAL (VALUE-TRIPLE :ELIDED))))))))) ; eliding was optional

; Include the book whose certificate we want to check.
(include-book "local-elided")

; Define must-succeed (used below).
(include-book "misc/eval" :dir :system)

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
