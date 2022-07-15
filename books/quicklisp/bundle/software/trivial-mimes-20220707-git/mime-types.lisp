#|
 This file is a part of Trivial-Mimes
 (c) 2014 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defpackage #:trivial-mimes
  (:nicknames #:mimes #:org.tymoonnext.trivial-mimes)
  (:use #:cl)
  (:export
   #:*mime-db*

   #:find-mime.types
   #:mime-probe
   #:mime-lookup
   #:mime
   #:mime-file-type))
(in-package #:org.tymoonnext.trivial-mimes)


(defun find-mime.types ()
  "Attempts to find a usable MIME.TYPES file.
If none can be found, an error is signalled."
  (or (loop for file in (list #p"/etc/mime.types"
                              #+asdf (merge-pathnames "mime.types" (asdf:system-source-directory :trivial-mimes)))
            thereis (probe-file file))
      (error "No MIME.TYPES file found anywhere!")))

(defvar *mime-db* (make-hash-table :test 'equalp)
  "An EQUALP hash-table with file-extensions as keys and the mime-types as values.")
(defvar *reverse-mime-db* (make-hash-table :test 'equalp)
  "An EQUALP hash-table with mime-types as keys and the file-extensions as values.")

(defun whitespace-p (char)
  (find char '(#\Space #\Newline #\Backspace #\Tab #\Linefeed #\Page #\Return #\Rubout)))

(defun %read-tokens (line)
  (let ((tokens)
        (start))
    (dotimes (i (length line))
      (let ((char (aref line i)))
        (cond
          ((and start (whitespace-p char))
           (push (subseq line start i) tokens)
           (setf start NIL))
          ((not (or start (whitespace-p char)))
           (setf start i)))))
    (when start (push (subseq line start) tokens))
    (nreverse tokens)))

(defun valid-name-p (name)
  "According to RFC6838 type names MUST start with an alphanumeric character
This also conveniently skips comments"
  (and name (alphanumericp (elt name 0))))

(defun build-mime-db (&optional (file (find-mime.types)))
  "Populates the *MIME-DB* with data gathered from the file.
The file should have the following structure:

MIME-TYPE FILE-EXTENSION*"
  (with-open-file (stream file :direction :input)
    (loop for line = (read-line stream NIL)
          while line
          for tokens = (%read-tokens line)
          when (valid-name-p (first tokens))
          do (dolist (ending (cdr tokens))
               (setf (gethash ending *mime-db*) (car tokens)))
             (setf (gethash (first tokens) *reverse-mime-db*) (second tokens)))))
(build-mime-db)

(defun mime-probe (pathname)
  "Attempts to get the mime-type through a call to the FILE shell utility.
If the file does not exist or the platform is not unix, NIL is returned."
  #+unix
  (when (probe-file pathname)
    (let ((output (uiop:run-program (list "file" #+darwin "-bI" #-darwin "-bi"
                                                 (uiop:native-namestring pathname))
                                    :output :string)))
      (with-output-to-string (mime)
        (loop for c across output
              for char = (char-downcase c)
              ;; Allowed characters as per RFC6383
              while (find char "abcdefghijklmnopqrstuvwxyz0123456789!#$&-^_.+/")
              do (write-char char mime)))))
  #-unix
  NIL)

(defun mime-lookup (pathname)
  "Attempts to get the mime-type by file extension comparison.
If none can be found, NIL is returned."
  (gethash (pathname-type pathname) *mime-db*))

(defun mime (pathname &optional (default "application/octet-stream"))
  "Attempts to detect the mime-type of the given pathname.
First uses MIME-LOOKUP, then MIME-PROBE and lastly returns the DEFAULT if both fail."
  (or (mime-lookup pathname)
      (mime-probe pathname)
      default))

(defun mime-file-type (mime-type)
  "Returns a matching file-extension for the given mime-type.
If the given mime-type cannot be found, NIL is returned."
  (gethash mime-type *reverse-mime-db*))
