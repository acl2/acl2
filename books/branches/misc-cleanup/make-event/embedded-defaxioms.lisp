; This book illustrates the idea of using make-event to check that books do NOT
; certify.

; We do some testing of the interaction of defaxiom with books and
; encapsulate.  But we do so in an interesting way, using make-event
; (specifically, macros must-succeed and must-fail) to do our checking.  We
; lucked out a little, since calling certify-book while inside certify-book
; seems a bit odd; but it seems to work.

; Notice that the set-cbd calls are protected -- that is, the cbd reverts to
; its top-level value after each make-event expansion is complete.

(in-package "ACL2")

; Portcullis command:
; (include-book "make-event/eval" :dir :system)

(defttag :writes-okp)

(remove-untouchable writes-okp nil)

(defttag nil)

(defmacro succeed-certify-book (&rest args)
  `(make-event '(must-succeed
                 (progn (defttag :writes-okp)
                        (progn! (set-cbd "embedded-defaxioms")
                                (assign writes-okp t)
                                (defttag nil)
                                (certify-book ,@args
                                              :ttags (:writes-okp)))))))

(succeed-certify-book "bar" 1 nil :defaxioms-okp t :ttags (:writes-okp))

(succeed-certify-book "baruser" 1 nil :defaxioms-okp t :ttags (:writes-okp))

(defmacro fail-certify-book (&rest args)
  `(make-event '(must-fail
                 (progn (defttag :writes-okp)
                        (progn! (set-cbd "embedded-defaxioms")
                                (assign writes-okp t)
                                (defttag nil)
                                (certify-book ,@args
                                              :ttags (:writes-okp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The rest of these should all fail.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(a1) - this should fail directly because of local defaxiom
(fail-certify-book "foo-a1" 1 nil :defaxioms-okp t)

;(a21) - this should fail because of macro expanding to local defaxiom
(fail-certify-book "foo-a21" 1 nil :defaxioms-okp t)

;(b1) - this fails because "bar" contains a defaxiom and when we do
;      the chk-embedded-event-form on the forms in "bar" we know
;      in-local-flg.
(fail-certify-book "foo-b1" 1 nil :defaxioms-okp t)

;(b2) - as with (b1) but with macro for local
(fail-certify-book "foo-b2" 1 nil :defaxioms-okp t)

;(b3) - as with (b1) but with two levels of include-book
(fail-certify-book "foo-b3" 1 nil :defaxioms-okp t)

;(c1) - this fails because we don't permit local include-books with
;      defaxiom, just as with (b1)
(fail-certify-book "foo-c1" 1 nil :defaxioms-okp t)

;(c2) - like (c1) but with macro for local
(fail-certify-book "foo-c2" 1 nil :defaxioms-okp t)

;(d) - this fails because we don't permit local defaxioms inside encapsulate
(fail-certify-book "foo-d" 1 nil :defaxioms-okp t)

;(e) - this fails because don't permit defaxioms in encapsulates
(fail-certify-book "foo-e" 1 nil :defaxioms-okp t)

;(f) - this fails because of non-local include-book in an encapsulate
(fail-certify-book "foo-f" 1 nil :defaxioms-okp t)

; The following fails because of a local defaxiom.  But notice that it's not
; directly a local defaxiom; rather, it's a local make-event, where the
; make-event generates a defaxiom.  We need to be sure this doesn't certify!
(fail-certify-book "local-defaxiom-1" 1 nil :defaxioms-okp t)

; Similar, but more obviously a local defaxiom:
(fail-certify-book "local-defaxiom-2" 1 nil :defaxioms-okp t)

; From :doc note-2-9-5:
(must-fail
 (encapsulate
  ()
  (local
   (encapsulate
    ()
    (local (progn (program))) ; or, (local (with-output :off summary (program)))
    (set-irrelevant-formals-ok t)
    (defun foo (x)
      (declare (xargs :measure (acl2-count x)))
      (1+ (foo x)))))
  (defthm inconsistent
    nil
    :hints (("Goal" :use foo))
    :rule-classes nil)))
