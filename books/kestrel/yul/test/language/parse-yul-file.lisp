; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "std/io/read-file-lines-no-newlines" :dir :system)

(include-book "../../language/parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; returns an error triple
(defund parse-yul-file (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (acl2::file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-yul-file "File does not exist: ~x0." filename)
                (mv `(:file-does-not-exist ,filename) nil state)))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list filename state))
       ((when (or erp (not (consp bytes))))
        (prog2$ (er hard? 'parse-yul-file "Failed to read bytes from file: ~x0." filename)
                (mv `(:failed-to-read-from-file ,filename) nil state)))
       ((unless (acl2::nat-listp bytes))
        (mv t nil state))
       ;; Parse the bytes read:
       (yul-or-err (parse-yul-bytes bytes)))
    (if (resulterrp yul-or-err)
        (mv `(:parse-error ,filename) yul-or-err state)
      (mv nil yul-or-err state))))

;; (parse-yul-file "test/yulOptimizerTests/disambiguator/for_statement.yul" state)

;; a non-error-triple equivalent of parse-yul-file
(define parse-yul-fileX ((filename stringp) state)
  :returns (mv (yul-prog block-resultp) state)
  (b* (((mv existsp state)
        (acl2::file-existsp filename state))
       ((when (not existsp))
        (mv (err `(:file-does-not-exist ,filename)) state))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list filename state))
       ((when (or erp (not (consp bytes))))
        (mv (err `(:failed-to-read-from-file ,filename)) state))
       ((unless (acl2::nat-listp bytes))
        ;; can't happen, but helps guard checks
        (mv (err `(:bytes-in-file-are-not-nats ,filename)) state))
       ;; Parse the bytes read:
       (yul-or-err (parse-yul-bytes bytes)))
    (if (resulterrp yul-or-err)
        (mv (err `(:parse-error ,filename yul-or-err)) state)
      (mv yul-or-err state))))

;; (parse-yul-fileX "test/yulOptimizerTests/disambiguator/for_statement.yul" state)

(defund parse-yul-files (filenames state)
  (declare (xargs :stobjs state
                  :guard (string-listp filenames)))
  (if (endp filenames)
      (mv nil nil state)
    (b* (((mv erp yul-or-err state)
          (parse-yul-file (car filenames) state))
         ((mv rest-erp rest-yul-or-err state)
          (parse-yul-files (cdr filenames) state)))
      (mv (or erp rest-erp)
          (cons yul-or-err rest-yul-or-err)
          state))))

;; Usually there is an empty string at the end.
;; Might as well remove any empty lines as well
(define remove-empty-strings ((strings string-listp))
  :returns (ret-strings string-listp)
  (if (endp strings)
      nil
    (if (not (mbt (and (stringp (car strings))
                       (string-listp (cdr strings)))))
        nil
      (let ((rest-nonempty-strings (remove-empty-strings (cdr strings))))
        (if (equal (car strings) "")
            rest-nonempty-strings
          (cons (car strings)
                rest-nonempty-strings))))))

;; For iterating over a bunch
(defund parse-yul-files-from-list (filenames-file state)
  (declare (xargs :stobjs state
                  :guard (stringp filenames-file)))
  (mv-let (filenames state)
      (acl2::read-file-lines-no-newlines filenames-file state)
    (if (string-listp filenames)
        (let ((nonempty-filenames (remove-empty-strings filenames)))
          (parse-yul-files nonempty-filenames state))
      (mv t nil state) ; should never happen
      )))

;; $ ls -1 /path/to/tests/*/*.{yul,yul.expected} > /tmp/yul-file-list
;; $ cd books/kestrel/yul ; $ACL2
;; YUL !> (include-book "parse-yul-file")  ; this book
;; YUL !> (include-book "std/util/defconsts")
;; YUL !> (defconsts (*yul-progs-err* *yul-progs* state) (parse-yul-files-from-list "/tmp/yul-file-list" state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; in and out refer to the yul optimizer
(define parse-yul-optimizer-pair ((in-filename stringp) (out-filename stringp) state)
  :returns (mv (in-prog block-resultp) (out-prog block-resultp) state)
  (b* (((mv result1 state)
        (parse-yul-fileX in-filename state))
       ((mv result2 state)
        (parse-yul-fileX out-filename state)))
    (mv result1 result2 state)))

;; (parse-yul-optimizer-pair "test/yulOptimizerTests/disambiguator/for_statement.yul" "test/yulOptimizerTests/disambiguator/for_statement.yul.expected" state)
