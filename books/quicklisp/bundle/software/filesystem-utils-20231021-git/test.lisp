(in-package #:cl-user)
(defpackage #:filesystem-utils-test
  (:nicknames #:org.shirakumo.filesystem-utils.test)
  (:use #:cl #:parachute)
  (:local-nicknames
   (#:fs #:org.shirakumo.filesystem-utils)
   (#:pu #:org.shirakumo.pathname-utils)))
(in-package #:org.shirakumo.filesystem-utils.test)

(defvar *here* #.(make-pathname :name NIL :type NIL :defaults (or *compile-file-pathname* *load-pathname*)))

(define-test filesystem-utils)

(defun create-file (file &optional (contents "a"))
  (with-open-file (stream file
                          :direction :output
                          :if-exists :error)
    (write-string contents stream)))

(defun file-contents (file)
  (with-open-file (stream file)
    (with-output-to-string (out)
      (loop with buf = (make-string 4096)
            for read = (read-sequence buf stream)
            while (< 0 read)
            do (write-sequence buf out :end read)))))

(define-test directories
  :parent filesystem-utils
  (true (pu:directory-p (fs:runtime-directory)))
  (true (pu:absolute-p (fs:runtime-directory)))
  (true (pu:directory-p (fs:temporary-directory)))
  (true (pu:absolute-p (fs:temporary-directory)))
  (true (pu:directory-p (fs:current-directory)))
  (true (pu:absolute-p (fs:current-directory)))
  (let* ((current (fs:current-directory))
         (new (pu:to-root current)))
    (fs:with-current-directory (new)
      (is pu:pathname= new (fs:current-directory)))
    (is pu:pathname= current (fs:current-directory))))

(define-test tempfile
  :parent filesystem-utils
  (true (pu:file-p (fs:make-temporary-file)))
  (is string= "abc" (pathname-name (fs:make-temporary-file :name "abc")))
  (is string= "abc" (pathname-type (fs:make-temporary-file :type "abc")))
  (isnt pu:pathname= (fs:make-temporary-file) (fs:make-temporary-file))
  (let (file)
    (fs:with-temporary-file (tempfile)
      (setf file tempfile)
      (finish (create-file tempfile)))
    (false (fs:file-exists-p file))))

(define-test files
  :parent filesystem-utils
  (false (fs:ensure-deleted (fs:make-temporary-file)))
  (true (fs:file-exists-p (user-homedir-pathname)))
  (let ((file (fs:make-temporary-file)))
    (finish (create-file file))
    (true (fs:file-exists-p file))
    (true (fs:ensure-deleted file))
    (false (fs:file-exists-p file))))

(define-test attributes
  :parent filesystem-utils
  (true (fs:directory-p (user-homedir-pathname)))
  (true (fs:directory-p (make-pathname :name (pu:directory-name (user-homedir-pathname))
                                       :defaults (pu:parent (user-homedir-pathname)))))
  (false (fs:file-p (user-homedir-pathname)))
  (false (fs:file-p (make-pathname :name (pu:directory-name (user-homedir-pathname))
                                   :defaults (pu:parent (user-homedir-pathname)))))
  (fs:with-temporary-file (file)
    (finish (create-file file))
    (true (fs:file-p file))
    (false (fs:symbolic-link-p file)))
  (false (fs:symbolic-link-p (user-homedir-pathname))))

(define-test contents
  :parent filesystem-utils
  (true (find "docs" (fs:list-contents *here*) :key #'pu:directory-name :test #'string=))
  (true (find "docs" (fs:list-directories *here*) :key #'pu:directory-name :test #'string=))
  (false (find "test.lisp" (fs:list-directories *here*) :key #'pu:file-name :test #'string=))
  (true (find "test.lisp" (fs:list-contents *here*) :key #'pu:file-name :test #'string=))
  (true (find "test.lisp" (fs:list-files *here*) :key #'pu:file-name :test #'string=))
  (false (find "docs" (fs:list-files *here*) :key #'pu:directory-name :test #'string=)))

(define-test devices
  :parent filesystem-utils
  (true (not (null (fs:list-hosts))))
  (skip-on (:unix) "Unix does not have devices."
    (true (find "C" (fs:list-devices) :test #'string-equal))))

(define-test symbolic-links
  :parent filesystem-utils
  (skip-on ((not :sbcl)) "Can't test symbolic-link functions as we have no way of establishing them."
    (fs:with-temporary-file (file)
      (let ((target (make-pathname :name "test" :type "lisp" :defaults *here*)))
        (finish (fs:create-symbolic-link file target))
        (false (find target (fs:directory* (merge-pathnames pu:*wild-file* (fs:temporary-directory))) :test #'pu:pathname=))
        (false (fs:symbolic-link-p target))
        (true (fs:symbolic-link-p file))
        (is pu:pathname= target (fs:resolve-symbolic-links file))))))

(define-test rename
  :parent filesystem-utils
  (fs:with-temporary-file (a)
    (finish (create-file a "a"))
    (true (fs:file-exists-p a))
    (fs:with-temporary-file (b)
      (finish (create-file b "b"))
      (true (fs:file-exists-p b))
      (finish (fs:rename-file* a b))
      (true (fs:file-exists-p b))
      (false (fs:file-exists-p a))
      (is string= "a" (file-contents b)))))

(define-test copy
  :parent filesystem-utils)
