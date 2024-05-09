(defpackage #:trivial-mimes
  (:nicknames #:mimes #:org.tymoonnext.trivial-mimes)
  (:use #:cl)
  (:export
   #:*mime-db*

   #:find-mime.types
   #:mime-add
   #:mime-probe
   #:mime-lookup
   #:mime
   #:mime-file-type
   #:mime-equal
   #:mime-case))
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

(defun mime-add (mime &rest file-extensions)
  "Add MIME and FILE-EXTENSIONS associations to *MIME-DB* and *REVERSE-MIME-DB*.
Makes the provided MIME and FILE-EXTENSIONS properly look-up-able with
MIME, MIME-PROBE and other trivial-mimes functions."
  (dolist (extension file-extensions)
    (setf (gethash extension *mime-db*) mime))
  (setf (gethash mime *reverse-mime-db*) (first file-extensions)))

(defun build-mime-db (&optional (file (find-mime.types)))
  "Populates the *MIME-DB* with data gathered from the file.
The file should have the following structure:

MIME-TYPE FILE-EXTENSION*"
  (with-open-file (stream file :direction :input)
    (loop for line = (read-line stream NIL)
          while line
          for tokens = (%read-tokens line)
          when (valid-name-p (first tokens))
            do (apply #'mime-add tokens))))
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

(defun mime-equal (m1 m2)
  "Checks whether M1 and M2 are matching.

In particular, checks the match of type and subtype (any of which can
be asterisks), discarding any parameters there might be.

\(mime-equal \"text/*\" \"text/html\")
T

\(mime-equal \"text/html\" \"text/html;charset=utf8\")
T

\(mime-equal \"*/*\" \"application/octet-stream\")
T

\(mime-equal \"text/*\" \"application/octet-stream\")
NIL"
  (or (equal "*" m1)
      (equal "*" m2)
      (equal "*/*" m1)
      (equal "*/*" m2)
      (destructuring-bind (type1 subtype1 &rest parameters1)
          (uiop:split-string m1 :separator '(#\/ #\;))
        (declare (ignorable parameters1))
        (destructuring-bind (type2 subtype2 &rest parameters2)
            (uiop:split-string m2 :separator '(#\/ #\;))
          (declare (ignorable parameters2))
          (cond
            ((or (equal "*" subtype1)
                 (equal "*" subtype2)
                 (equal "" subtype1)
                 (equal "" subtype2))
             (string-equal type1 type2))
            ((string-equal type1 type2)
             (string-equal subtype1 subtype2))
            (t nil))))))

(defmacro mime-case (file &body cases)
  "A case-like macro that works with MIME type of FILE.

Otherwise clause is the last clause that starts with T or OTHERWISE,.

Example:
\(mime-case #p\"~/CHANGES.txt\"
  ((\"application/json\" \"application/*\") \"Something opaque...\")
  (\"text/plain\" \"That's a plaintext file :D\")
  (t \"I don't know this type!\"))"
  (let ((mime (gensym "mime")))
    `(let ((,mime (mime ,file)))
       (cond
         ,@(loop for ((mimes . body) . rest) on cases
                 when (member mimes '(T OTHERWISE))
                   collect `(t ,@body) into clauses
                   and do (if rest
                              (warn "Clauses after T and OTHERWISE are not reachable.")
                              (return clauses))
                 collect `((member ,mime (list ,@(uiop:ensure-list mimes)) :test #'mime-equal)
                           ,@body)
                   into clauses
                 finally (return clauses))))))
