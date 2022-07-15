;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; windows.lisp --- Low-level interface to the windows API.
;;;
;;; Copyright (c) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;; Copyright (c) 2021, Eric Timmons   <eric@timmons.dev>
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

(in-package #:osicat-windows)

(load-foreign-library "Kernel32.dll")

;;; Error Handling

(defrawwinapi ("GetLastError" get-last-error) dword)

(defwinapi ("FormatMessageW" %format-message-w) dword
  (flags format-message-flags)
  (source :pointer)
  (message-id dword)
  (language-id dword)
  (buffer :pointer)
  (size dword)
  &rest)

(defun get-error-message (error-code)
  (with-foreign-object (buffer-pointer :uint16 (* 64 1024))
    (%format-message-w '(:ignore-inserts :from-system)
                       (null-pointer)
                       error-code
                       0
                       buffer-pointer
                       (* 64 1024))
    (wstring-to-string buffer-pointer)))

;;; Performance Counter

(defwinapi ("QueryPerformanceCounter" %query-perf-counter) bool
  (count (:pointer large-integer)))

(defun query-performance-counter ()
  (with-foreign-object (ptr 'large-integer)
    (assert (%query-perf-counter ptr))
    (mem-ref ptr 'large-integer)))

;;; Wide string translation.
;;;
;;; Many windows functions have an ASCII version and a Unicode/Wide String
;;; version. We typically want to use the Unicode versions because they have
;;; fewer restrictions. Unfortunately, Windows has standardized on UTF-16 using
;;; :uint32s instead of :chars. To also guard against any other shenanigans,
;;; just use Windows' built in functionality to create wide strings.

(defwinapi ("WideCharToMultiByte" wide-char-to-multi-byte) :int
  (code-page :uint)
  (flags dword)
  (wide-char-str :pointer)
  (wide-char :int)
  (multi-byte-str :pointer)
  (multi-byte :int)
  (default-char :pointer)
  (used-default-char :pointer))

(defwinapi ("MultiByteToWideChar" multi-byte-to-wide-char) :int
  (code-page :uint)
  (flags dword)
  (multi-byte-str :pointer)
  (multi-byte :int)
  (wide-char-str :pointer)
  (wide-char :int))

(defun string-to-wstring (string)
  "Convert a Lisp string to a Windows wide string. Returns a pointer to the
newly allocated string."
  (with-foreign-string (foreign-string string :encoding :utf-8)
    ;; Compute the size needed to hold the wide string, then actually do the
    ;; conversion.
    (let* ((num-chars (multi-byte-to-wide-char +cp-utf-8+ 0 foreign-string -1 (null-pointer) 0))
           (wide-string (foreign-alloc :uint16 :count num-chars)))
      (multi-byte-to-wide-char +cp-utf-8+ 0 foreign-string -1 wide-string num-chars)
      wide-string)))

(defun wstring-to-string (wstring &optional length)
  "Given a pointer to a Windows wide string, return a Lisp string with its contents.

If LENGTH is provided, it is how many characters to read from the wide
string. If it is not provided, the wide string must be null terminated.
"
  (let ((num-bytes (wide-char-to-multi-byte +cp-utf-8+ 0
                                            wstring (or length -1)
                                            (null-pointer) 0
                                            (null-pointer) (null-pointer))))
    (with-foreign-object (foreign-string :uchar num-bytes)
      (wide-char-to-multi-byte +cp-utf-8+ 0
                               wstring (or length -1)
                               foreign-string num-bytes
                               (null-pointer) (null-pointer))
      (foreign-string-to-lisp foreign-string :encoding :utf-8
                                             :count (unless (null length) num-bytes)))))

(defmethod translate-to-foreign (string (type wide-string))
  (string-to-wstring string))

(defmethod translate-from-foreign (pointer (type wide-string))
  (wstring-to-string pointer))

(defmethod free-translated-object (pointer (type wide-string) param)
  (declare (ignore param))
  (foreign-free pointer))

(defmethod translate-to-foreign ((filename string) (type wide-filename))
  (string-to-wstring filename))

(defmethod translate-to-foreign ((filename pathname) (type wide-filename))
  (when (wild-pathname-p filename)
    (system-error "Pathname is wild: ~S." filename))
  (string-to-wstring (native-namestring (translate-logical-pathname filename))))

(defmethod free-translated-object (pointer (type wide-filename) param)
  (declare (ignore param))
  (foreign-free pointer))

;;; readdir/opendir equivalents

(defwinapi ("FindFirstFileW" find-first-file-w) search-handle
  (file-name wide-string)
  (find-file-data :pointer))

(defwinapi ("FindNextFileW" find-next-file-w) bool
  (find-file search-handle)
  (find-file-data :pointer))

(defwinapi ("FindClose" find-close) bool
  (find-file search-handle))

(define-c-struct-wrapper find-data ())

(defmethod print-object ((object find-data) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (format stream "~S ~S" (find-data-file-name object) (find-data-file-attributes object))))

(defun find-first-file (path)
  "Calls FindFirstFileW with the PATH. Returns one or two VALUES.

If there are no matches for PATH, then NIL is returned as the only value.

If there are matches, a FIND-DATA instance containing the first match is the
first value and a handle for subsequent use with FIND-NEXT-FILE is the second
value.

When finished, the handle must be passed to FIND-CLOSE."
  (with-foreign-object (buf '(:struct find-data))
    (handler-bind ((win32-error (lambda (c)
                                  (when (= (system-error-code c) +error-file-not-found+)
                                    (return-from find-first-file nil)))))
      (let ((handle (find-first-file-w path buf)))
        (values (make-instance 'find-data :pointer buf) handle)))))

(defun find-next-file (handle)
  "Calls FindNextFileW to continue the search represented by HANDLE. Returns a
FIND-DATA instance or NIL."
  (with-foreign-object (buf '(:struct find-data))
    (handler-bind ((win32-error (lambda (c)
                                  (when (= (system-error-code c) +error-no-more-files+)
                                    (return-from find-next-file nil)))))
      (find-next-file-w handle buf)
      (make-instance 'find-data :pointer buf))))

;;; Symbolic links

(defwinapi ("CreateSymbolicLinkW" create-symbolic-link) bool
  (symlink-file-name wide-filename)
  (target-file-name wide-filename)
  (flags symbolic-link-flags))

;;; Hard links

(defwinapi ("CreateHardLinkW" create-hard-link) bool
  (file-name wide-filename)
  (existing-file-name wide-filename)
  (security-attributes :pointer))

;;; File handle creation

(defwinapi ("CreateFileW" create-file-w) handle
  (file-name wide-filename)
  (desired-access dword)
  (share-mode share-mode-flags)
  (security-attributes :pointer)
  (creation-disposition creation-disposition)
  (flags-and-attributes file-attributes-and-flags)
  (template-file :pointer))

(defun create-file (file-name desired-access share-mode security-attributes
                    creation-disposition flags-and-attributes
                    &key (template-file (null-pointer)))
  (create-file-w file-name desired-access share-mode security-attributes creation-disposition
                 flags-and-attributes template-file))

(defun call-with-create-file (thunk file-name desired-access share-mode security-attributes
                              creation-disposition flags-and-attributes
                              &key (template-file (null-pointer)))
  (let ((handle (create-file file-name desired-access share-mode security-attributes
                             creation-disposition flags-and-attributes
                             :template-file template-file)))
    (unwind-protect
         (funcall thunk handle)
      (close-handle handle))))

(defmacro with-create-file ((handle-name
                             file-name desired-access share-mode security-attributes
                             creation-disposition flags-and-attributes
                             &key (template-file '(null-pointer)))
                            &body body)
  `(call-with-create-file (lambda (,handle-name) ,@body)
                          ,file-name ,desired-access ,share-mode ,security-attributes
                          ,creation-disposition ,flags-and-attributes
                          :template-file ,template-file))

(defwinapi ("CloseHandle" close-handle) bool
  (object handle))

(defwinapi ("GetFinalPathNameByHandleW" %get-final-path-name-by-handle-w) dword
  (file handle)
  (file-path :pointer)
  (file-path-size dword)
  (flags dword))

(defun get-final-path-name-by-handle (handle)
  (with-foreign-object (wstring :uint16 +max-path+)
    (%get-final-path-name-by-handle-w handle wstring +max-path+ 0)
    (wstring-to-string wstring)))

;; this function has funky error semantics.
(defrawwinapi ("GetFileType" %get-file-type) file-type
  (file handle))

(defun get-file-type (file)
  (let ((result (%get-file-type file)))
    (when (eql result :unknown)
      (let ((error-code (get-last-error)))
        (unless (= error-code +error-success+)
          (win32-error error-code 'get-file-type))))
    result))

(defwinapi ("GetFileInformationByHandle" %get-file-information-by-handle) bool
  (file handle)
  (file-information :pointer))

(define-c-struct-wrapper by-handle-file-information ())

(defun get-file-information-by-handle (handle)
  (with-foreign-object (buff '(:struct by-handle-file-information))
    (%get-file-information-by-handle handle buff)
    (make-instance 'by-handle-file-information :pointer buff)))

(defun filetime-to-int (filetime)
  "Returns the number of 100-nanosecond intervals since January 1, 1601 (UTC)."
  (+ (ash (getf filetime 'high-date-time) (* 8 (foreign-type-size 'dword)))
     (getf filetime 'low-date-time)))

(defun file-information-creation-time (file-information)
  (filetime-to-int (slot-value file-information 'creation-time)))

(defun file-information-last-access-time (file-information)
  (filetime-to-int (slot-value file-information 'last-access-time)))

(defun file-information-last-write-time (file-information)
  (filetime-to-int (slot-value file-information 'last-write-time)))

(defun file-information-volume-serial-number (file-information)
  (slot-value file-information 'volume-serial-number))

(defun file-information-number-of-links (file-information)
  (slot-value file-information 'number-of-links))

(defun file-information-file-index (file-information)
  (logior (ash (slot-value file-information 'file-index-high) (* 8 (foreign-type-size 'dword)))
          (slot-value file-information 'file-index-low)))

(defun file-information-file-attributes (file-information)
  (slot-value file-information 'file-attributes))

;;; IO Control

(defun reparse-data-buffer-is-symbolic-link-p (buffer)
  (let ((reparse-tag (foreign-slot-value buffer '(:struct reparse-data-buffer) 'reparse-tag)))
    (= reparse-tag (foreign-enum-value 'io-reparse-tag :symlink))))

(defun handle-is-symbolic-link-p (handle)
  (and (member :attribute-reparse-point
               (file-information-file-attributes (get-file-information-by-handle handle)))
       (with-foreign-object (buffer '(:struct reparse-data-buffer))
         (device-io-control handle :fsctl-get-reparse-point
                            (null-pointer) 0
                            buffer (foreign-type-size '(:struct reparse-data-buffer))
                            (null-pointer) (null-pointer))
         (reparse-data-buffer-is-symbolic-link-p buffer))))

(defun get-symbolic-link-target-by-handle (handle)
  "Given the handle to a symlink (must be opened with
:FLAG-OPEN-REPARSE-POINT), return the target."
  ;; win32 API provides no nice way to do this, so we use an ioctl.
  (assert (member :attribute-reparse-point
                  (file-information-file-attributes (get-file-information-by-handle handle))))
  (with-foreign-object (buffer '(:struct reparse-data-buffer))
    (device-io-control handle :fsctl-get-reparse-point
                       (null-pointer) 0
                       buffer (foreign-type-size '(:struct reparse-data-buffer))
                       (null-pointer) (null-pointer))
    (assert (reparse-data-buffer-is-symbolic-link-p buffer))
    (let* ((buffer-pointer (foreign-slot-pointer buffer '(:struct reparse-data-buffer) 'buffer))
           (path-buffer-pointer (foreign-slot-pointer buffer-pointer
                                                      '(:struct symbolic-link-reparse-buffer)
                                                      'path-buffer))
           (name-offset (foreign-slot-value buffer-pointer '(:struct symbolic-link-reparse-buffer)
                                            'substitute-name-offset))
           (name-length (foreign-slot-value buffer-pointer '(:struct symbolic-link-reparse-buffer)
                                            'substitute-name-length))
           (raw-target (wstring-to-string (mem-aptr path-buffer-pointer 'wchar
                                                    (/ name-offset (foreign-type-size 'wchar)))
                                          (/ name-length (foreign-type-size 'wchar)))))
      ;; If the target is absolute, it may start with \??\. If that exists,
      ;; strip it off.
      (when (and (>= (length raw-target) 4)
                 (string= "\\??\\" (subseq raw-target 0 4)))
          (setf raw-target (subseq raw-target 4)))
      ;; Furthermore, the target may start with \\?\ if the pathname is very
      ;; long. Strip that off as well.
      (when (and (>= (length raw-target) 4)
                 (string= "\\\\?\\" (subseq raw-target 0 4)))
        (setf raw-target (subseq raw-target 4)))
      raw-target)))
