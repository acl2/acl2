;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; packages.lisp --- Package definitions.
;;;
;;; Copyright (C) 2003, 2004 Nikodemus Siivola <nikodemus@random-state.net>
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

(in-package #:cl-user)

(defpackage #:osicat
  (:use #:common-lisp #:osicat-sys #:cffi #:alexandria)
  (:documentation
   "Osicat is a lightweight operating system interface for Common
Lisp on Unix-platforms.  It is not a POSIX-style API, but rather
a simple lispy accompaniment to the standard ANSI facilities.

Osicat homepage:

  http://www.common-lisp.net/project/osicat/

Concepts:

Designated directory

  When a relative pathname designator is used as a directory
  designator it is first resolved against
  *DEFAULT-PATHNAME-DEFAULT*, and then against the current
  directory. (With MERGE-PATHNAMES in both cases.)")
  (:export
   ;; Conditions
   #:system-error
   #:system-error-code
   #:system-error-identifier
   #:system-error-message

   ;; Evironment
   #:environment
   #:environment-variable
   #:makunbound-environment-variable

   ;; Directories
   #:current-directory
   #:delete-directory
   #:delete-directory-and-files
   #:directory-exists-p
   #:list-directory
   #:mapdir
   #:walk-directory
   #:with-directory-iterator

   ;; Files
   #:file-exists-p
   #:good-symlink-exists-p
   #:regular-file-exists-p
   #:file-kind

   ;; Symlinks
   #:read-link
   #:make-link

   ;; Permissions
   #:file-permissions

   ;; Temporary files
   #:open-temporary-file
   #:with-temporary-file

   ;; Password entries
   #:user-info

   ;; Pathname utilities
   #:absolute-pathname
   #:absolute-pathname-p
   #:directory-pathname-p
   #:native-namestring
   #:pathname-as-directory
   #:pathname-as-file
   #:pathname-directory-pathname
   #:relative-pathname-p
   #:unmerge-pathnames

   ;; Time
   #:get-monotonic-time

   ;; Specials
   #:*temporary-directory*
   ))
