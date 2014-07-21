
(defun cw-unformatted (x)
  (let ((stream (get-output-stream-from-channel *standard-co*)))
    (write-string x stream)

; [Jared] We added finish-output to make this work better with file streams
; that we were wanting to monitor.  Unfortunately this turned out to be
; horribly slow when writing to an NFS-mounted file system.  (Which can happen,
; for instance, if you are running ACL2 and redirecting output to a file from
; the shell, or using with-stdout, or similar.)  It seems that using
; force-output is much, much faster, and at least tries to accomplish something
; similar, so now we'll just use it.

    (force-output stream))
  nil)
