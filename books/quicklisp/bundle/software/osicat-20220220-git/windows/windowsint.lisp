;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; windowsint.lisp --- Grovel definitions for Windows functions
;;;
;;; Copyright (C) 2021, Eric Timmons <eric@timmons.dev>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

;;; Definitions in this file should match POSIX 1003.1 or some such.
;;; In practice, though, we place here whatever is supported by the
;;; wimpiest of the POSIX systems, Windows.

(include "windows.h")

(in-package #:osicat-windows)

(constant (+max-path+ "MAX_PATH"))
(constant (+invalid-handle-value+ "INVALID_HANDLE_VALUE"))
(constant (+cp-utf-8+ "CP_UTF8"))

(constant (+error-success+ "ERROR_SUCCESS"))
(constant (+error-file-not-found+ "ERROR_FILE_NOT_FOUND"))
(constant (+error-no-more-files+ "ERROR_NO_MORE_FILES"))

(constant (+generic-all+ "GENERIC_ALL"))
(constant (+generic-execute+ "GENERIC_EXECUTE"))
(constant (+generic-read+ "GENERIC_READ"))
(constant (+generic-write+ "GENERIC_WRITE"))

(bitfield format-message-flags
          ((:allocate-buffer "FORMAT_MESSAGE_ALLOCATE_BUFFER"))
          ((:argument-array "FORMAT_MESSAGE_ARGUMENT_ARRAY"))
          ((:from-hmodule "FORMAT_MESSAGE_FROM_HMODULE"))
          ((:from-string "FORMAT_MESSAGE_FROM_STRING"))
          ((:from-system "FORMAT_MESSAGE_FROM_SYSTEM"))
          ((:ignore-inserts "FORMAT_MESSAGE_IGNORE_INSERTS")))

(progn
  (bitfield file-attributes
            . #1=(((:attribute-archive "FILE_ATTRIBUTE_ARCHIVE"))
                  ((:attribute-compressed "FILE_ATTRIBUTE_COMPRESSED"))
                  ((:attribute-device "FILE_ATTRIBUTE_DEVICE"))
                  ((:attribute-directory "FILE_ATTRIBUTE_DIRECTORY"))
                  ((:attribute-encrypted "FILE_ATTRIBUTE_ENCRYPTED"))
                  ((:attribute-hidden "FILE_ATTRIBUTE_HIDDEN"))
                  ((:attribute-integrity-stream "FILE_ATTRIBUTE_INTEGRITY_STREAM")
                   :optional t)
                  ((:attribute-normal "FILE_ATTRIBUTE_NORMAL"))
                  ((:attribute-not-content-indexed "FILE_ATTRIBUTE_NOT_CONTENT_INDEXED"))
                  ((:attribute-no-scrub-data "FILE_ATTRIBUTE_NO_SCRUB_DATA")
                   :optional t)
                  ((:attribute-offline "FILE_ATTRIBUTE_OFFLINE"))
                  ((:attribute-readonly "FILE_ATTRIBUTE_READONLY"))
                  ((:attribute-recall-on-data-access "FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS")
                   :optional t)
                  ((:attribute-recall-on-open "FILE_ATTRIBUTE_RECALL_ON_OPEN")
                   :optional t)
                  ((:attribute-reparse-point "FILE_ATTRIBUTE_REPARSE_POINT"))
                  ((:attribute-sparse-file "FILE_ATTRIBUTE_SPARSE_FILE"))
                  ((:attribute-system "FILE_ATTRIBUTE_SYSTEM"))
                  ((:attribute-temporary "FILE_ATTRIBUTE_TEMPORARY"))
                  ((:attribute-virtual "FILE_ATTRIBUTE_VIRTUAL"))))

  (bitfield file-flags
            . #2=(((:flag-backup-semantics "FILE_FLAG_BACKUP_SEMANTICS"))
                  ((:flag-delete-on-close "FILE_FLAG_DELETE_ON_CLOSE"))
                  ((:flag-no-buffering "FILE_FLAG_NO_BUFFERING"))
                  ((:flag-open-no-recall "FILE_FLAG_OPEN_NO_RECALL"))
                  ((:flag-open-reparse-point "FILE_FLAG_OPEN_REPARSE_POINT"))
                  ((:flag-overlapped "FILE_FLAG_OVERLAPPED"))
                  ((:flag-posix-semantics "FILE_FLAG_POSIX_SEMANTICS"))
                  ((:flag-random-access "FILE_FLAG_RANDOM_ACCESS"))
                  ((:flag-session-aware "FILE_FLAG_SESSION_AWARE"))
                  ((:flag-sequential-scan "FILE_FLAG_SEQUENTIAL_SCAN"))
                  ((:flag-write-through "FILE_FLAG_WRITE_THROUGH"))))

  (bitfield file-attributes-and-flags
            . #.(append '#1# '#2#)))

(cstruct file-time "struct _FILETIME"
         (low-date-time "dwLowDateTime" :type dword)
         (high-date-time "dwHighDateTime" :type dword))

(cstruct find-data "struct _WIN32_FIND_DATAW"
         (file-attributes "dwFileAttributes" :type file-attributes)
         (creation-time "ftCreationTime" :type (:struct file-time))
         (last-access-time "ftLastAccessTime" :type (:struct file-time))
         (last-write-time "ftLastWriteTime" :type (:struct file-time))
         (file-size-high "nFileSizeHigh" :type dword)
         (file-size-low "nFileSizeLow" :type dword)
         (reserved-0 "dwReserved0" :type dword)
         (reserved-1 "dwReserved1" :type dword)
         (file-name "cFileName" :type wide-string :count :auto)
         (alternate-file-name "cAlternateFileName" :type wide-string :count 14)
         ;; The Windows documentation mentions the following three fields, but
         ;; the compiler doesn't seem to know about them.
         ;;
         ;; (file-type "dwFileType" :type dword)
         ;; (creator-type "dwCreatorType" :type dword)
         ;; (finder-flags "wFinderFlags" :type :uint16)
         )

(cstruct by-handle-file-information "struct _BY_HANDLE_FILE_INFORMATION"
         (file-attributes "dwFileAttributes" :type file-attributes)
         (creation-time "ftCreationTime" :type (:struct file-time))
         (last-access-time "ftLastAccessTime" :type (:struct file-time))
         (last-write-time "ftLastWriteTime" :type (:struct file-time))
         (volume-serial-number "dwVolumeSerialNumber" :type dword)
         (file-size-high "nFileSizeHigh" :type dword)
         (file-size-low "nFileSizeLow" :type dword)
         (number-of-links "nNumberOfLinks" :type dword)
         (file-index-high "nFileIndexHigh" :type dword)
         (file-index-low "nFileIndexLow" :type dword))

(bitfield symbolic-link-flags
          ((:directory "SYMBOLIC_LINK_FLAG_DIRECTORY"))
          ((:allow-unprivileged-create "SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE")))

(bitfield share-mode-flags
          ((:delete "FILE_SHARE_DELETE"))
          ((:read "FILE_SHARE_READ"))
          ((:write "FILE_SHARE_WRITE")))

(cenum creation-disposition
       ((:create-always "CREATE_ALWAYS"))
       ((:create-new "CREATE_NEW"))
       ((:open-always "OPEN_ALWAYS"))
       ((:open-existing "OPEN_EXISTING"))
       ((:truncate-existing "TRUNCATE_EXISTING")))

(cenum file-type
       ((:char "FILE_TYPE_CHAR"))
       ((:disk "FILE_TYPE_DISK"))
       ((:pipe "FILE_TYPE_PIPE"))
       ((:remote "FILE_TYPE_REMOTE"))
       ((:unknown "FILE_TYPE_UNKNOWN")))

(cenum device-io-control-code
       ((:fsctl-get-reparse-point "FSCTL_GET_REPARSE_POINT")))

(cenum (io-reparse-tag :base-type :ulong)
       ((:symlink "IO_REPARSE_TAG_SYMLINK")))
