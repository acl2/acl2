; A tool to parse a file containing a JSON object
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-json")
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-character-list" :dir :system)
(include-book "kestrel/typed-lists-light/map-char-code" :dir :system)
(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)


;; Returns (mv parsed-value maybe-sha256 state).
;; If the json was successfully parsed, then if compute-hash? is non-null,
;; this calls sha256-bytes on the bytes of the file and
;; returns as the second return value a list of 32 bytes that is the sha256 hash of the file.
;; If compute-hash? is null (or if there was any error, or if the file has more
;; than sha2::*sha-256-max-message-bytes* (currently 2305843009213693951) bytes),
;; then the hash is not computed and nil is returned as the second return value.
;; If the first return value is T then there was an error.
(defund parse-file-as-json-aux (filename compute-hash? state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-file-as-json "JSON file does not exist: ~x0." filename)
                (mv t nil state)))
       (chars ; not that state is not returned!
        (read-file-into-character-list filename state))
       ((when (not (consp chars))) ;I've seen this be a string error message
        (prog2$ (er hard? 'parse-file-as-json "Failed to read any character from file: ~x0.  Result: ~x1" filename chars)
                (mv t nil state)))
       ;; Parse the characters read:
       ((mv erp parsed-json)
        (parse-json chars))
       ((when erp)
        (prog2$ (er hard? 'parse-file-as-json "ERROR (~x0) parsing JSON in ~x1" erp filename)
                (mv t nil state)))
       (sha256
        (if (and compute-hash?
                 (<= (len chars) sha2::*sha-256-max-message-bytes*))
            (sha2::sha-256-bytes (map-char-code chars))
          nil)))
    (mv parsed-json sha256 state)))


;; The purpose of the following function is to hash the same bytes that were parsed
;; so that you have a way to detect if a file was changed after it was parsed.

;; The sha-256-bytes function on the file's bytes yields the same result as
;; the linux sha256sum command.
;; To see that, do:
;;   (include-book "kestrel/utilities/strings/hexstrings" :dir :system)
;;   (ubyte8s=>hexstring (sha2::sha-256-bytes (map-char-code (read-file-into-character-list <FILENAME> state))))

;; Returns (mv erp parsed-value sha256-bytes state).
;; If there is any error the first return value is T and the second is NIL.
;; Example call: (parse-file-as-json-and-sha256 "example.json" state)
;; [ Note, The ERP return value is there solely because without it there were
;;   3 values ending in state (parsed-value, sha-256-bytes, state)
;;   and the top-level interface interpreted it as an error triple
;;   and didn't print it, which was annoying. ]
(defund parse-file-as-json-and-sha256 (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (if (not (stringp filename))
      (mv t t nil state)
    (mv-let (parsed-json sha256-bytes state)
        (parse-file-as-json-aux filename t state)
      (if (or (eq parsed-json t) (eq sha256-bytes nil))
          (mv t parsed-json sha256-bytes state)
        (mv nil parsed-json sha256-bytes state)))))

;; Returns (mv parsed-value state).
;; If there is any error the first return value is T.
;; Example call: (parse-file-as-json "example.json" state)
(defund parse-file-as-json (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (if (not (stringp filename))
      (mv t state)
    (mv-let (parsed-json ignoreme state)
        (parse-file-as-json-aux filename nil state)
      (declare (ignore ignoreme))
      (mv parsed-json state))))
