;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-

; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022-2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HTCLIENT")

;; This book is just a variant of post.lisp, with the function renamed to post-light.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-light (url data state kwds)
  ;; kwds is a doublet-list mapping keyword args to values
  ;; The keyword args must be valid for dex:post (see https://quickdocs.org/dexador)
  ;; E.g., (post-light "https:..." <data> state '((:connect-timeout 30) (:read-timeout 30)))
  (if (not (live-state-p state))
      (prog2$ (error "POSTLS can only be called on a live state.")
              (mv "ERROR" nil state))
    (if (not (stringp url))
        (prog2$ (error "POST-LIGHT called on a non-stringp url")
                (mv "ERROR" nil state))
      (handler-case
       (mv-let (reply-string response-code hashtable uri something)
         (apply 'dex:post url :content data (reduce 'append kwds))
         (if (equal response-code 200)
             (mv nil reply-string state)
           ;; For now, we make any reply code except 200 be returned as the error code
           (mv response-code reply-string state)))

       (error (condition)
              (let ((condition-str (format nil "~a" condition)))
                (mv (msg "~s0: error from ~s1: ~s2."
                         'post url condition-str)
                    nil state)))))))
