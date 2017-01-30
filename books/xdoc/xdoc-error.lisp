; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file provides utilities pertaining to "xdoc error", "Markup error", and
; perhaps other syntactic problems with xdoc source.  Historically (as of this
; writing in January, 2017), those messages have not caused an error.  This
; file provides a very simple mechanism for moving to a mode where such
; "errors" are recorded so that at a future time, chosen by the user, and
; actual error occurs if any such "errors" have been noted.  The hope is that
; it will be easy to modify this mechanism if a more sophisticated capability
; is desired, for example, printing an ACL2 warning that lists the offending
; topic names.  We'll use "xdoc-error" in function names so that it is easy to
; search for these utilities.

(in-package "XDOC")

(defun initialize-xdoc-errors (flg)

; The wormhole-data for the 'xdoc-errors wormhole is either nil, indicating
; that we are not tracking errors, or a natural number n, indicating that n
; errors have been encountered since last initialized.  Flg says to track
; errors: it is t, nil, or :same, meaning (respectively) to turn tracking on,
; turn it off, or leave tracking as it was except that we set n back to 0 if
; tracking was (and is to be) on.

; If this function has never been called, then calling it with flg = nil is
; essentially a no-op.  Quoting :doc wormhole: "Upon the first call of wormhole
; or wormhole-eval on a name, the status of that name is nil."  Since
; wormhole-data returns the cdr of the status, it is also initially nil.

  (declare (xargs :guard (member-eq flg '(t nil :same))))
  (cond ((eq flg :same)
         (wormhole-eval 'xdoc-errors
                        '(lambda (whs)
                           (let* ((old (wormhole-data whs))
                                  (new (if old 0 nil)))
                             (set-wormhole-data whs new)))
                        nil))
        (flg
         (wormhole-eval 'xdoc-errors
                        '(lambda (whs)
                           (set-wormhole-data whs 0))
                        nil))
        (t
         (wormhole-eval 'xdoc-errors
                        '(lambda (whs)
                           (set-wormhole-data whs nil))
                        nil))))

(defun show-xdoc-errors () ; mainly for debugging
  (wormhole-eval 'xdoc-errors
                 '(lambda (whs)
                    (prog2$ (cw "Value of xdoc-errors: ~x0~%"
                                (wormhole-data whs))
                            whs))
                 nil))

(defun report-xdoc-errors (ctx)
  (declare (xargs :guard t))
  (prog2$
   (wormhole-eval 'xdoc-errors
                  '(lambda (whs)
                     (let* ((old (wormhole-data whs))
                            (new (cond ((natp old) (- old))

; The resetting done just below is probably not important, since we expect only
; to call report-xdoc-errors after some sort of manual-saving that starts by
; calling initialize-xdoc-errors (e.g., in xdoc::save).

                                       ((integerp old) 0)
                                       (t nil))))
                       (set-wormhole-data whs new)))
                  nil)
   (wormhole-eval 'xdoc-errors
                  '(lambda (whs)
                     (let* ((data (wormhole-data whs))
                            (count (if (integerp data) ; then data <= 0
                                       (- data)
                                     0)))
                       (cond
                        ((> count 0)

; We formerly reported the number of errors, as follows (notice #+skip):

                         #+skip
                         (er acl2::hard? ctx
                             "~n0 error~#1~[ was~/s were~] encountered by ~
                              XDOC (noted with \"xdoc error\")."
                             count
                             (if (= count 1) 0 1))

; However, for reasons I don't yet understand, the manual build seems to go
; through the topics twice, without an intervening error message from this
; function, but apparently with re-initialization because the reported count is
; only half of the number of "xdoc error" occurrences; that is, each such error
; is reported twice.

                         (er acl2::hard? ctx
                             "at least one syntax error was encountered by ~
                              XDOC; search above for \"xdoc error\" (but the ~
                              same error may be reported more than once)."))
                        (t whs))))
                  count)))

(defun note-xdoc-error ()
  (declare (xargs :guard t))
  (wormhole-eval 'xdoc-errors
                 '(lambda (whs)
                    (let ((count (wormhole-data whs)))
                      (and count
                           (set-wormhole-data whs (1+ (nfix count))))))
                 nil))

(defmacro xdoc-error (str ctx &rest args)
  (declare (xargs :guard (stringp str)))
  `(prog2$ (note-xdoc-error)
           (cw ,(concatenate 'string "; xdoc error in ~x0: " str "~%")
               ,ctx
               ,@args)))
