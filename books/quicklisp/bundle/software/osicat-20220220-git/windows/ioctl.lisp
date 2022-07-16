;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; ioctl.lisp --- ioctl definitions.
;;;
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

;; These structs are difficult to grovel for. The required headers seem to be
;; difficult to access. Besides, the size of REPARSE-DATA-BUFFER is likely to
;; be "wrong" in the headers, at least based on the definitions the Win32 API
;; docs give.

(defcstruct symbolic-link-reparse-buffer
  (substitute-name-offset :ushort)
  (substitute-name-length :ushort)
  (print-name-offset :ushort)
  (print-name-length :ushort)
  (flags :ulong)
  (path-buffer wchar :count 1))

(defcstruct mount-point-reparse-buffer
  (substitute-name-offset :ushort)
  (substitute-name-length :ushort)
  (print-name-offset :ushort)
  (print-name-length :ushort)
  (path-buffer wchar :count 1))

(defcstruct generic-reparse-buffer
  (databuffer :uchar :count 1))

(defcunion reparse-data-buffer-dummy-union
  (symbolic-link-reparse-buffer (:struct symbolic-link-reparse-buffer))
  (mount-point-reparse-buffer (:struct mount-point-reparse-buffer))
  (generic-reparse-buffer (:struct generic-reparse-buffer)))

;; Size gotten from
;; <https://docs.microsoft.com/en-us/windows/win32/fileio/reparse-points>
(defcstruct (reparse-data-buffer :size #.(* 16 1024))
  (reparse-tag :ulong)
  (reparse-data-length :ushort)
  (reserved :ushort)
  (buffer (:union reparse-data-buffer-dummy-union)))

(defwinapi ("DeviceIoControl" device-io-control) bool
  (device handle)
  (io-control-code device-io-control-code)
  (in-buffer :pointer)
  (in-buffer-size dword)
  (out-buffer :pointer)
  (out-buffer-size dword)
  (bytes-returned :pointer)
  (overlapped :pointer))
