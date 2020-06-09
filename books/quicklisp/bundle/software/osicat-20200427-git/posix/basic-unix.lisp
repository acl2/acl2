;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; basic-unix.lisp --- CL-POSIX bindings.
;;;
;;; Copyright (C) 2005-2006, Matthew Backes  <lucca@accela.net>
;;; Copyright (C) 2005-2006, Dan Knapp  <dankna@accela.net> and
;;; Copyright (C) 2007, Stelian Ionescu  <stelian.ionescu-zeus@poste.it>
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

(in-package #:osicat-posix)

#+windows (load-foreign-library "msvcrt.dll")

;;;; POSIX-ERROR

#+windows
(defcfun "strerror" :string
  "Look up the error message string for ERRNO. (reentrant)"
  (errnum :int))

;;; TODO: accept keywords too?
#-windows
(defun strerror (&optional (err (get-errno)))
  "Look up the error message string for ERRNO. (reentrant)"
  (let ((errno (if (keywordp err)
                   (foreign-enum-value 'errno-values err)
                   err)))
    #-linux ; XSI-compliant strerror_r() always stores the error
            ; message in the user-supplied buffer.
    (with-foreign-pointer-as-string ((buf bufsiz) 1024)
      (strerror-r errno buf bufsiz))
    #+linux ; GNU strerror_r() doesn't always store the error message
            ; in the user-supplied buffer, but it returns a string
            ; instead of an int.
    (with-foreign-pointer (buf 1024 bufsiz)
      (strerror-r errno buf bufsiz))))

(defmethod print-object ((posix-error posix-error) stream)
 (print-unreadable-object (posix-error stream :type t :identity nil)
   (let ((code (system-error-code posix-error))
         (identifier (system-error-identifier posix-error))
         (syscall (posix-error-syscall posix-error)))
     (format stream "~s ~s ~s ~s"
             (or syscall "[No syscall name]")
             (or code "[No code]") identifier
             (or (strerror code) "[Can't get error string.]")))))

;;;; string.h

(defcfun "memset" :pointer
  (buffer :pointer)
  (value  :int)
  (length size))

(defun bzero (buffer length)
  (memset buffer 0 length))

(defcfun "memcpy" :pointer
  (dest   :pointer)
  (src    :pointer)
  (length size))

(defcfun "memmove" :pointer
  (dest   :pointer)
  (src    :pointer)
  (length size))

;;;; unistd.h

;;; I/O

(defsyscall "read" ssize
  "Read at most COUNT bytes from FD into the foreign area BUF."
  (fd    file-descriptor-designator)
  (buf   :pointer)
  (count size))

(defsyscall "write" ssize
  "Write at most COUNT bytes to FD from the foreign area BUF."
  (fd    file-descriptor-designator)
  (buf   :pointer)
  (count size))

;;; directories

(defsyscall "chdir" :int
  "Changes the current working directory"
  (path filename-designator))

(defsyscall ("getcwd" %getcwd) :string
  (buf :pointer)
  (size size))

(defun getcwd ()
  "Returns the current working directory as a string."
  (with-foreign-pointer (buf path-max size)
    (%getcwd buf size)))

(defsyscall "rmdir" :int
  (path filename-designator))

;;; files

(defsyscall ("open" %open) :int
  (pathname filename-designator)
  (flags    :int)
  (mode     mode))

(defvar *default-open-mode* #o666)

(defun open (pathname flags &optional (mode *default-open-mode*))
  ;; Let's just use O_BINARY always unless there's a good reason not to.
  #+windows (setq flags (logior flags o-binary))
  (cond
    ((integerp mode) (%open pathname flags mode))
    (t (error "Wrong mode: ~S" mode))))

(defsyscall "creat" :int
  (pathname filename-designator)
  (mode     mode))

(defsyscall ("pipe" %pipe) :int
  (filedes :pointer))

(defun pipe ()
  "Create pipe, returns two values with the new FDs."
  (with-foreign-object (filedes :int 2)
    (%pipe filedes)
    (values (mem-aref filedes :int 0)
            (mem-aref filedes :int 1))))

(defcsyscall "rename" :int
  "Rename a file."
  (old filename-designator)
  (new filename-designator))

(defsyscall "close" :int
  "Close an open file descriptor."
  (fd file-descriptor-designator))

(defsyscall "unlink" :int
  (path filename-designator))

(defsyscall "access" :int
  (path  filename-designator)
  (amode :int))

(defsyscall "dup" :int
  (fildes file-descriptor-designator))

(defsyscall "dup2" :int
  (fildes1 file-descriptor-designator)
  (fildes2 file-descriptor-designator))

(defsyscall "chmod" :int
  (path filename-designator)
  (mode mode))

;;; environment

(defcvar ("environ" :read-only t) (:pointer :string))

(defcfun "getenv" :string
  "Returns the value of an environment variable"
  (name :string))

;;; time

(defsyscall "sleep" :unsigned-int
  (seconds :unsigned-int))

;;;; sys/time.h

(defcsyscall ("time" %time) time
  (tloc :pointer))

(defun time ()
  (%time (null-pointer)))

;;;; sys/stat.h

(define-c-struct-wrapper stat ())

;;; If necessary for performance reasons, we can add an optional
;;; argument to this function and use that to reuse a wrapper object.
(defun funcall-stat (fn arg)
  (with-foreign-object (buf '(:struct stat))
    (funcall fn arg buf)
    (make-instance 'stat :pointer buf)))

(defun stat (path)
  "Get information about a file."
  (funcall-stat #'%stat path))

(defun fstat (fd)
  "Get information about a file descriptor"
  (funcall-stat #'%fstat fd))

(defsyscall "umask" mode
  "Sets the umask and returns the old one"
  (new-mode mode))

(defsyscall "mkdir" :int
  "Create a directory."
  (path filename-designator)
  (mode mode))

(defsyscall ("realpath" %realpath) :string
  "Returns the canonicalized absolute pathname"  
  (path filename-designator)
  (resolved-name :string))

(defun realpath (path)
  "Returns the canonicalized absolute pathname"
  (with-foreign-pointer (resolved-name path-max)
    (%realpath path resolved-name)))

