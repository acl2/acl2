(in-package "ACL2")

; See comment below for check-hons-enabled.

(defmacro check-state (form error-msg &key ctx check-expansion)
  `(with-output :stack :push
                :off (error summary)
                (make-event (if ,form
                                (value '(value-triple :CHECK-STATE-PASSED))
                              (with-output
                               :stack :pop
                               (er soft ,(or ctx 'check-state)
                                   "~@0"
                                   ,error-msg)))
                            :check-expansion ,check-expansion)))

(defmacro check-hons-enabled (ctx &optional check-expansion)

; Typical usage is at the top of a book that requires ACL2(h) (say, because it
; includes GL and takes too long to certify in ACL2):

; (check-hons-enabled (:book "my-book.lisp"))

; Notice that the string is just the book name.  In the error message, ACL2
; will automatically prepend the directory path.

; Use check-expansion = t if you want this check executed at include-book time,
; not just certify-book time, as this uses :check-expansion t for the
; underlying make-event form.  Otherwise, you might want to make both your
; include-book and check-hons-enabled forms local, e.g.:

; (local (include-book "misc/check-state" :dir :system))
; (local (check-hons-enabled (:book "my-book.lisp")))

  (declare (xargs :guard (booleanp check-expansion)))
  `(check-state (hons-enabledp state)
                "The current context requires the use of ACL2(h).~%See ~
                        :DOC hons-and-memoization."
                :ctx ,(cond ((and (consp ctx)
                                  (consp (cdr ctx))
                                  (eq (car ctx) :book)
                                  (stringp (cadr ctx)))
                             `(msg "processing book~%~s0~s1"
                                   (@ connected-book-directory)
                                   ,(cadr ctx)))
                            (ctx)
                            (t ''check-hons-enabled))
                :check-expansion ,check-expansion))
