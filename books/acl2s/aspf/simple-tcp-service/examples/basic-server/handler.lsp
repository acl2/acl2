;; SPDX-FileCopyrightText: Copyright (c) 2021 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :server)

;; This function takes in a string corresponding to the message sent
;; to the server, and should return a string that will be encoded and
;; sent back to the requester.
;; If this function signals an error, the server will respond with the
;; stringified version of the error, plus a flag indicating that the
;; request resulted in an error in the handler.
;; If this function signals a condition of class
;; handler-shutdown-request, the server will shutdown.
(defun handle-request (str)
  (let ((command (char str 0))
        (contents (subseq str 1 (length str)))) ;; TODO: possibly inefficient to do this because creates a copy
    ;; This will throw an error if command doesn't match any of the
    ;; provided cases.
    (ecase command
           ;; The E and Q commands are required by the provided Python
           ;; interface, but feel free to add, remove, or modify any
           ;; other cases.
           (#\E ;; Echo the contents of the recieved request.
            contents)
           (#\Q ;; Tell the server to shutdown.
            (signal 'handler-shutdown-request))
           (#\R ;; Do a thing!  In this case, call one of ACL2s'
            ;; enumerators with a random seed value.
            (acl2s::nth-string (random (expt 2 63)))))))
