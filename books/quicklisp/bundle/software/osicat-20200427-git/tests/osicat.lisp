;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; osicat.lisp --- Tests for Osicat's high-level interface.
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

(in-package #:osicat/tests)

(deftest current-directory.1
    (let ((old (current-directory)))
      (unwind-protect
           (progn
             (setf (current-directory) "/tmp/")
             (equal (native-namestring (current-directory))
                    (native-namestring (truename "/tmp/"))))
        (setf (current-directory) old)))
  t)

(deftest delete-directory.1
    (let ((dir (merge-pathnames "delete-directory/" *test-directory*)))
      (ensure-directories-exist dir)
      (and (eq :directory (file-kind dir))
           (delete-directory dir)
           (null (file-kind dir))))
  t)

(deftest delete-directory.2
    (let* ((dir (merge-pathnames "delete-directory/" *test-directory*))
           (file (merge-pathnames "file" dir)))
      (ensure-directories-exist dir)
      (ensure-file file)
      (unwind-protect
           (and (eq :regular-file (file-kind file))
                (eq :directory (file-kind dir))
                (eq :error (handler-case (delete-directory dir)
                             (error () :error))))
        (osicat-posix:unlink file)))
  t)

;;; FIXME: (user-homedir-pathname) is "home:" under CMUCL, so this
;;; test will fail.
;;;        CLISP's probe-file doesn't work with directories
#-(or cmu clisp)
(deftest environment.1
    (namestring (probe-file (cdr (assoc "HOME" (environment)
                                        :test #'equal))))
  #.(namestring (user-homedir-pathname)))

(deftest environment.2
    (unwind-protect
         (progn
           (setf (environment-variable "TEST-VARIABLE") "TEST-VALUE")
           (assoc "TEST-VARIABLE" (environment) :test #'equal))
      (makunbound-environment-variable 'test-variable))
  ("TEST-VARIABLE" . "TEST-VALUE"))

;;; No-op test to ensure setf environment actually works.
(deftest environment.3
    (let ((old-env (environment)))
      (prog1 (setf (environment) nil)
        (setf (environment) old-env)))
  nil)

(deftest environment-variable.1
    (environment-variable 'test-variable)
  nil)

(deftest environment-variable.2
    (unwind-protect
         (progn
           (setf (environment-variable "TEST-VARIABLE") "TEST-VALUE")
           (environment-variable "TEST-VARIABLE"))
      (makunbound-environment-variable "TEST-VARIABLE"))
  "TEST-VALUE")

(deftest environment-variable.3
    (unwind-protect
         (progn
           (setf (environment-variable "test-variable") "test-value")
           (environment-variable "TEST-VARIABLE"))
      (makunbound-environment-variable "test-variable"))
  nil)

(deftest environment-variable.4
    (unwind-protect
         (progn
           (setf (environment-variable "test-variable") "test-value")
           (environment-variable "test-variable"))
      (makunbound-environment-variable "test-variable"))
  "test-value")

(deftest file-kind.1
    (file-kind *test-directory*)
  :directory)

(deftest file-kind.2
    (file-kind (make-pathname :name "does-not-exist"
                              :defaults *test-directory*))
  nil)

(deftest file-kind.3
    (let* ((file (ensure-file "tmp-file"))
           (link (ensure-link "tmp-link" :target file)))
      (unwind-protect
           (file-kind link)
        (osicat-posix:unlink link)
        (osicat-posix:unlink file)))
  :symbolic-link)

(deftest file-kind.4
    (let ((file (ensure-file "tmp-file")))
      (unwind-protect
           (file-kind file)
        (osicat-posix:unlink file)))
  :regular-file)

(deftest file-permissions.1
    (and (member :other-read (file-permissions "/tmp/"))
         t)
  t)

(deftest file-permissions.2
    (let ((file (ensure-file "tmp-exec")))
      (unwind-protect
           (and (not (member :user-exec (file-permissions file)))
                (push :user-exec (file-permissions file))
                (member :user-exec (file-permissions file))
                t)
        (osicat-posix:unlink file)))
  t)

(deftest make-link.1
    (let ((link (merge-pathnames "make-link-test-link" *test-directory*))
          (file (ensure-file "tmp-file")))
      (unwind-protect
           (progn
             (make-link link :target file)
             (namestring (read-link link)))
        (osicat-posix:unlink link)
        (osicat-posix:unlink file)))
  #.(namestring (merge-pathnames "tmp-file" *test-directory*)))

(deftest make-link.2
    (let ((link (merge-pathnames "make-link-test-link" *test-directory*))
          (file (ensure-file "tmp-file")))
      (unwind-protect
           (progn
             (make-link link :target file)
             (file-kind link))
        (osicat-posix:unlink file)
        (osicat-posix:unlink link)))
  :symbolic-link)

;;; Test the case of reading a link to a directory.
(deftest read-link.1
    (let ((link (merge-pathnames "read-link-test-link" *test-directory*)))
      (unwind-protect
           (progn
             (make-link link :target *test-directory*)
             (namestring (read-link link)))
        (osicat-posix:unlink link)))
  #.(namestring *test-directory*))

;;; Test the case of reading a link with a very long name.
(deftest read-link.2
    (let ((link (merge-pathnames "make-link-test-link" *test-directory*))
          (file (ensure-file "a-very-long-tmp-file-name-explicitly-for-the-purpose-of-testing-a-certain-condition-in-read-link-please-ignore-thanks")))
      (unwind-protect
           (progn
             (make-link link :target file)
             (equal (native-namestring (merge-pathnames file *test-directory*))
                    (native-namestring (read-link link))))
        (osicat-posix:unlink link)
        (osicat-posix:unlink file)))
  t)

(deftest makunbound-environment-variable.1
    (let ((old (environment-variable :path)))
      (unwind-protect
           (and old
                (makunbound-environment-variable :path)
                (null (environment-variable :path))
                t)
        (setf (environment-variable :path) old)))
  t)

(deftest mapdir.1
    (let* ((dir (ensure-directories-exist
                 (merge-pathnames "mapdir-test/" *test-directory*)))
           (file1 (ensure-file "file1" dir))
           (file2 (ensure-file "file2.txt" dir))
           (subdir (ensure-directories-exist
                    (merge-pathnames "subdir/" dir))))
      (unwind-protect
           (let ((result (remove-if #'null (mapdir #'pathname-name dir))))
             (sort result #'string<))
        (osicat-posix:unlink file1)
        (osicat-posix:unlink file2)
        (delete-directory subdir)
        (delete-directory dir)))
  ("file1" "file2"))

(deftest mapdir.2
    (let* ((dir (ensure-directories-exist
                 (merge-pathnames "mapdir-test/" *test-directory*)))
           (file1 (ensure-file "file1" dir))
           (file2 (ensure-file "file2.txt" dir))
           (subdir (ensure-directories-exist
                    (merge-pathnames "subdir/" dir))))
      (unwind-protect
           (let ((result (mapdir #'namestring dir)))
             (sort result #'string<))
        (osicat-posix:unlink file1)
        (osicat-posix:unlink file2)
        (delete-directory subdir)
        (delete-directory dir)))
  ("file1" "file2.txt" "subdir/"))

(deftest mapdir.3
    (let* ((dir (ensure-directories-exist
                 (merge-pathnames "mapdir-test/" *test-directory*)))
           (file (ensure-file "foo" dir)))
      (unwind-protect
           (let ((*default-directory-defaults* (truename "/tmp/")))
             (mapdir (lambda (x)
                       (pathname-directory (merge-pathnames x)))
                     dir))
        (osicat-posix:unlink file)
        (delete-directory dir)))
  (#.(pathname-directory (merge-pathnames "mapdir-test/" *test-directory*))))

;;; Test that directories of form foo.bar/ don't become foo/bar/.
(deftest mapdir.4
    (let* ((dir (ensure-directories-exist
                 (merge-pathnames "mapdir-test.type/" *test-directory*))))
      (unwind-protect
           (dolist (list (remove-if
                          #'null
                          (osicat:mapdir
                           (lambda (x) (pathname-directory x))
                           *test-directory*)))
             (when (/= (length list) 2)
               (error "too many path elements.")))
        (delete-directory dir)))
  nil)

;;; Be careful with this test.  It deletes directories recursively.
(deftest with-directory-iterator.1
    (let ((dirs (list "wdi-test-1/" ".wdi-test.2/" ".wdi.test.3../")))
      (ensure-directories-exist (reduce (lambda (x y) (merge-pathnames y x))
                                        (cons *test-directory* dirs)))
      (labels ((rm-r (dir)
                 (with-directory-iterator (next dir)
                   (loop for file = (next)
                         while file
                         when (and (eql (file-kind file) :directory)
                                   (member (namestring file) dirs
                                           :test #'string=))
                         do (progn (rm-r file)
                                   (delete-directory file))))))
        (rm-r *test-directory*)))
  nil)

;;; Test iteration over a variety of objects.
(deftest with-directory-iterator.2
    (let ((playground '(:directory "wdi-test-2/"
                        (:directory "wdi-test-2-2/"
                         (:symbolic-link "bar" "foo")
                         (:directory "baz/"
                          (:file "quux"))
                         (:file "foo")))))
      (labels
          ((create-playground (x base-dir)
             (case (car x)
               (:file (ensure-file (cadr x) base-dir))
               (:symbolic-link
                (handler-case
                    (make-link (merge-pathnames (cadr x) base-dir)
                               :target (merge-pathnames (caddr x) base-dir))
                  ;; FIXME?
                  (nix:eexist ())))
               (:directory (ensure-directories-exist (merge-pathnames
                                                      (cadr x) base-dir))
                           (dolist (y (cddr x))
                             (create-playground y (merge-pathnames
                                                   (cadr x) base-dir))))))
           (walk (dir)
             (with-directory-iterator (next dir)
               (loop for file = (next)
                     while file
                     collect (case (file-kind file)
                               (:directory
                                (append (list :directory (namestring file))
                                        (sort (walk file)
                                              (lambda (a b)
                                                (string<= (cadr a) (cadr b))))))
                               (:symbolic-link
                                (list :symbolic-link (namestring file)
                                      (pathname-name (namestring
                                                      (read-link file)))))
                               (t (list :file (namestring file))))))))
        (create-playground playground *test-directory*)
        (equal (walk (merge-pathnames (cadr playground) *test-directory*))
               (cddr playground))))
  t)

;;; Test behavior in the case of an obviously incorrect username.
(deftest user-info.1
    (user-info "definitely_not_a_user!")
  nil)

;;; Does this test still work in the case of su/sudo?  It should, I
;;; think.
(deftest user-info.2
    (let* ((uid (our-getuid))
           (user-info (user-info uid)))
      (equal (cdr (assoc :user-id user-info)) uid))
  t)

;;; Just get our home directory, and see if it exists.  I don't
;;; think this will work 100% of the time, but it should for most
;;; people testing the package; given that, would it be even better
;;; to compare the value to (user-homedir-pathname)?
(deftest user-info.3
    (let* ((uid (our-getuid))
           (user-info (user-info uid)))
      (file-kind (cdr (assoc :home user-info))))
  :directory)

;;; We'll go out on a limb and assume that not only does the root
;;; account exist, but its home directory exists, as well.  Note
;;; that this is unfortunately not always true.
(deftest user-info.4
    (let ((home (cdr (assoc :home (user-info "root")))))
      (file-kind home))
  :directory)

(deftest temporary-file.1
    (with-temporary-file (stream)
      (print 'foo stream)
      (let ((pos (file-position stream)))
        (print 'bar stream)
        (print 'baz stream)
        (file-position stream pos)
        (eql (read stream) 'bar)))
  t)

(defun call-with-temporary-nofile-rlimit (limit function)
  #-unix (declare (ignore limit))
  #+unix
  (multiple-value-bind (soft hard)
      (nix:getrlimit nix:rlimit-nofile)
    (nix:setrlimit nix:rlimit-nofile limit hard)
    (unwind-protect
         (funcall function)
      (nix:setrlimit nix:rlimit-nofile soft hard)))
  #-unix
  (funcall function))

(defmacro with-temporary-nofile-rlimit (limit &body body)
  `(call-with-temporary-nofile-rlimit ,limit (lambda () ,@body)))

;;; Test failure condition of OPEN-TEMPORARY-FILE.  So far, opening too
;;; many fds is all I can determine as a way to do this.
(deftest temporary-file.2
    (let ((fds))
      (handler-case
          (unwind-protect
               (with-temporary-nofile-rlimit 512
                 (do ((ctr 1024 (1- ctr)))
                     ((zerop ctr))
                   (push (open-temporary-file) fds)))
            (mapcar #'close fds))
        (file-error () t)))
  t)
