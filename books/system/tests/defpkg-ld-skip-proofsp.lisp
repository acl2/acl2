; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.  For a corresponding proof of nil, see community book
; system/tests/empty-pkg-nil.lisp.

; Finding 45: chk-acceptable-defpkg (other-events.lisp:1468-1470) skips its
; ENTIRE name-legality cond when (ld-skip-proofsp state) is 'include-book:
;
;    (cond ((or package-entry
;               (eq (ld-skip-proofsp state) 'include-book))
;           (value nil))                 ; <<< everything below is skipped
;          ((not (stringp name)) ...)
;          ((equal name "") ...)         ; <<< the Version 2.8 check
;
; The comment just below, at :1479-1492, contains the worked proof of NIL that
; the "" check exists to prevent.  A portcullis containing
;    (set-ld-skip-proofsp 'include-book state) (defpkg "" nil)
; therefore certifies a book whose world proves NIL, with (ttags-seen),
; skip-proofs-seen, the 82-axiom count and the .cert all clean --
; set-ld-skip-proofsp leaves no command landmark.
;
; A portcullis cannot be expressed in this suite's one-book-per-test form, so
; this test targets the CHECK rather than the exploit: each form below asks
; ACL2 to accept an illegal package name with the flag set, and must-fail
; requires it to be refused.  All three go green when the bypass at :1470 is
; made unconditional, which is the recommended fix.  The end-to-end portcullis
; witness is in the report bundle under 15-defpkg-ld-skip-proofsp/.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; The empty package name -- the Version 2.8 unsoundness.
(must-fail
 (make-event
  (er-progn (set-ld-skip-proofsp 'include-book state)
            (defpkg "" nil)
            (set-ld-skip-proofsp nil state)
            (value '(value-triple :accepted)))))

; A lower-case package name.
(must-fail
 (make-event
  (er-progn (set-ld-skip-proofsp 'include-book state)
            (defpkg "lower" nil)
            (set-ld-skip-proofsp nil state)
            (value '(value-triple :accepted)))))

; The ACL2_*1*_ prefix, which carries executable counterparts.
(must-fail
 (make-event
  (er-progn (set-ld-skip-proofsp 'include-book state)
            (defpkg "ACL2_*1*_FOO" nil)
            (set-ld-skip-proofsp nil state)
            (value '(value-triple :accepted)))))

; N228, merged in v2.30: the fourth bypassed clause, "LISP" (other-events.lisp
; :1501), added for note-2-9.3 because "LISP" is a nickname of the host
; COMMON-LISP package in some Common Lisp implementations.  Measured on
; eb770dc1ae / SBCL 2.2.9: with the flag set, MARK name="LISP" erp=NIL
; present=T; without the flag, refused with "...is used under the hood in some
; Common Lisp implementations."  Goes green with the other three when the
; bypass at :1470 is made unconditional.
(must-fail
 (make-event
  (er-progn (set-ld-skip-proofsp 'include-book state)
            (defpkg "LISP" nil)
            (set-ld-skip-proofsp nil state)
            (value '(value-triple :accepted)))))
