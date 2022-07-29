;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-

; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HTCLIENT")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post (url data state)
  (b* (((unless (live-state-p state))
        (error "POSTLS can only be called on a live state.")
        (mv "ERROR" nil state))
       ((unless (stringp url))
        (error "POST called on a non-stringp url")
        (mv "ERROR" nil state)))

    (handler-case
      (mv-let (reply-string response-code hashtable uri something)
          (dex:post url :content data)
        (if (equal response-code 200)
            (mv nil reply-string state)
          ;; For now, we make any reply code except 200 be returned as the error code
          (mv response-code reply-string state)))

      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (mv (msg "~s0: error listing ~s1: ~s2."
                        'ls path condition-str)
                   nil state))))))
