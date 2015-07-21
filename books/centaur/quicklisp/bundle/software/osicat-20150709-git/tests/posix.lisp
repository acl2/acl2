;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; posix.lisp --- OSICAT-POSIX test suite.
;;;
;;; Copyright (C) 2007, Luis Oliveira  <loliveira@common-lisp.net>
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

;;; This test suite is adapted from SBCL's contrib module SB-POSIX
;;; which unfortunately lacks any copyright information.  We're
;;; assuming it was either public domain or MIT-licensed.

(in-package #:osicat-tests)

;;;; Preliminaries

;;; Handle undefined/unsupported functions as passed tests in order to
;;; better simulate the POSIX compliance certification process. :-D
;;; That is how Windows got to be POSIX compliant, right?
(defmacro define-posix-test (name form &rest values)
  `(deftest ,name
      (handler-case ,form
        (osicat-sys:unsupported-function ()
          (values ,@(mapcar (lambda (v) `',v) values))))
    ,@values))

(defmacro define-eacces-test (name form &rest values)
  `(define-posix-test ,name
       (block ,name
         (when (= (nix:geteuid) 0)
           (return-from ,name (values ,@(mapcar (lambda (v) `',v) values))))
         ,form)
     ,@values))

(defvar *this-file* (or *load-truename* *compile-file-truename*))

;; because CMUCL and CLISP set *default-pathname-defaults* to #p""
(defvar *current-directory* (pathname (nix:getcwd)))

(defconstant +mode-rwx-all+
  (logior nix:s-irusr nix:s-iwusr nix:s-ixusr
          #-windows
          (logior nix:s-irgrp nix:s-iwgrp nix:s-ixgrp
                  nix:s-iroth nix:s-iwoth nix:s-ixoth)))

(defun test-dir (name)
  (merge-pathnames (make-pathname :directory (list :relative name))
                   *test-directory*))

;;;; Tests

(define-posix-test chdir.1
    (nix:chdir *test-directory*)
  0)

(define-posix-test chdir.2
    (nix:chdir (native-namestring *test-directory*))
  0)

(define-posix-test chdir.3
    (nix:chdir "/")
  0)

(define-posix-test chdir.4
    (nix:chdir #p"/")
  0)

(define-posix-test chdir.5
    (nix:chdir *current-directory*)
  0)

(define-posix-test chdir.6
    (nix:chdir "/../")
  0)

;;; other lisps don't seem to like this pathname
#+sbcl
(define-posix-test chdir.7
    (nix:chdir #p"/../")
  0)

(define-posix-test chdir.8
    (nix:chdir (make-pathname :directory '(:absolute)))
  0)

(define-posix-test chdir.error.1
    (handler-case
        (nix:chdir (test-dir "chdir.does-not-exist"))
      (nix:enoent () 'failed))
  failed)

(define-posix-test chdir.error.2
    (handler-case
        (nix:chdir *this-file*)
      (#+windows nix:einval
       #-windows nix:enotdir () 'failed))
  failed)

(define-posix-test mkdir.1
    (let ((dne (test-dir "mkdir.does-not-exist.1")))
      (unwind-protect
           (nix:mkdir dne 0)
        ;; FIXME: no delete-directory in CL, but using our own operators
        ;; is probably not ideal
        (ignore-errors (nix:rmdir dne))))
  0)

(define-posix-test mkdir.2
    (let ((dne (test-dir "mkdir.does-not-exist.2")))
      (unwind-protect
           (nix:mkdir (native-namestring dne) 0)
        (ignore-errors (nix:rmdir dne))))
  0)

(define-posix-test mkdir.error.1
    (handler-case
        (nix:mkdir *test-directory* 0)
      (nix:eexist () 'failed))
  failed)

(define-posix-test mkdir.error.2
    (handler-case
        (nix:mkdir "/" 0)
      (#+(or darwin openbsd) nix:eisdir
       #+windows nix:eacces
       #-(or darwin windows openbsd) nix:eexist () 'failed))
  failed)

(define-eacces-test mkdir.error.3
    (let* ((dir (test-dir "mkdir.error.3"))
           (dir2 (merge-pathnames
                  (make-pathname :directory '(:relative "does-not-exist"))
                  dir)))
      (nix:mkdir dir 0)
      (handler-case
          (nix:mkdir dir2 0)
        (nix:eacces ()
          (nix:rmdir dir)
          'failed)
        (:no-error (result)
          (nix:rmdir dir2)
          (nix:rmdir dir)
          result)))
  failed)

(define-posix-test rmdir.1
    (let ((dne (test-dir "rmdir.does-not-exist.1")))
      (ensure-directories-exist dne)
      (nix:rmdir dne))
  0)

(define-posix-test rmdir.2
  (let ((dne (test-dir "rmdir.does-not-exist.2")))
    (ensure-directories-exist dne)
    (nix:rmdir (native-namestring dne)))
  0)

(define-posix-test rmdir.error.1
    (handler-case
        (nix:rmdir (test-dir "rmdir.dne.error.1"))
      (nix:enoent () 'failed))
  failed)

(define-posix-test rmdir.error.2
    (handler-case
        (nix:rmdir *this-file*)
      (#+windows nix:einval
       #-windows nix:enotdir () 'failed))
  failed)

(define-posix-test rmdir.error.3
    (handler-case
        (nix:rmdir "/")
      (#+(or darwin openbsd) nix:eisdir
       #+windows nix:eacces
       #-(or darwin windows openbsd) nix:ebusy () 'failed))
  failed)

(define-posix-test rmdir.error.4
    (let* ((dir (ensure-directories-exist (test-dir "rmdir.error.4")))
           (file (make-pathname :name "foo" :defaults dir)))
      (with-open-file (s file :direction :output :if-exists nil)
        (write "" :stream s))
      (handler-case
          (nix:rmdir dir)
        (system-error (c)
          (delete-file file)
          (nix:rmdir dir)
          ;; documented by POSIX
          (not (null (member (system-error-identifier c)
                             '(:eexist :enotempty #+(or darwin openbsd) :enonet
                               #+windows :enosr)))))))
  t)

(define-eacces-test rmdir.error.5
    (let* ((dir (test-dir "rmdir.error.5"))
           (dir2 (merge-pathnames
                  (make-pathname :directory '(:relative "unremovable"))
                  dir)))
      (nix:mkdir dir +mode-rwx-all+)
      (nix:mkdir dir2 +mode-rwx-all+)
      (nix:chmod dir 0)
      (handler-case
          (nix:rmdir dir2)
        (nix:eacces (c)
          (nix:chmod dir (logior nix:s-iread nix:s-iwrite nix:s-iexec))
          (nix:rmdir dir2)
          (nix:rmdir dir)
          'failed)
        (:no-error (result)
          (nix:chmod dir (logior nix:s-iread nix:s-iwrite nix:s-iexec))
          (nix:rmdir dir)
          result)))
  failed)

(define-posix-test stat.1
    (logand (nix:stat-mode (nix:stat *test-directory*))
            (logior nix:s-iread nix:s-iwrite nix:s-iexec))
  #.(logior nix:s-iread nix:s-iwrite nix:s-iexec))

#-windows
(define-posix-test stat.2
    ;; it's logically possible for / to be writeable by others... but
    ;; if it is, either someone is playing with strange security
    ;; modules or they want to know about it anyway.
    (logand (nix:stat-mode (nix:stat "/")) nix:s-iwoth)
  0)

(define-posix-test stat.3
    (let* ((now (get-universal-time))
           ;; FIXME: (encode-universal-time 00 00 00 01 01 1970)
           (unix-now (- now 2208988800)))
      ;; FIXME: breaks if mounted noatime :-(
      (< (- (nix:stat-atime (nix:stat *test-directory*)) unix-now) 10))
  t)

#-windows
(define-posix-test stat.4
    ;; it's logically possible for / to be writeable by others... but
    ;; if it is, either someone is playing with strange security
    ;; modules or they want to know about it anyway.
    (logand (nix:stat-mode
             (nix:stat (make-pathname :directory '(:absolute))))
            nix:s-iwoth)
  0)

;;; FIXME: add tests for carrying a stat structure around in the
;;; optional argument to NIX:STAT

;;; FIXME: This test fails.  Why doesn't it signal ENOENT?
(define-posix-test stat.error.1
    (handler-case (nix:stat "")
      (nix:enoent () 'failed))
  failed)

(define-eacces-test stat.error.2
    (let* ((dir (test-dir "stat.error.2"))
           (file (merge-pathnames (make-pathname :name "unstatable") dir)))
      (nix:mkdir dir +mode-rwx-all+)
      (with-open-file (s file :direction :output)
        (write "" :stream s))
      (nix:chmod dir 0)
      (handler-case
          (nix:stat file)
        (nix:eacces ()
          (nix:chmod dir (logior nix:s-iread nix:s-iwrite nix:s-iexec))
          (nix:unlink file)
          (nix:rmdir dir)
          'failed)
        (:no-error (&rest result)
          (nix:chmod dir (logior nix:s-iread nix:s-iwrite nix:s-iexec))
          (nix:unlink file)
          (nix:rmdir dir)
          result)))
  failed)

;;; stat-mode tests
(defmacro with-stat-mode ((mode pathname) &body body)
  `(let ((,mode (nix:stat-mode (nix:stat ,pathname))))
     ,@body))

(defmacro with-lstat-mode ((mode pathname) &body body)
  `(let ((,mode (nix:stat-mode (nix:lstat ,pathname))))
     ,@body))

(define-posix-test stat-mode.1
    (with-stat-mode (mode *test-directory*)
      (nix:s-isreg mode))
  nil)

(define-posix-test stat-mode.2
    (with-stat-mode (mode *test-directory*)
      (nix:s-isdir mode))
  t)

(define-posix-test stat-mode.3
    (with-stat-mode (mode *test-directory*)
      (nix:s-ischr mode))
  nil)

(define-posix-test stat-mode.4
    (with-stat-mode (mode *test-directory*)
      (nix:s-isblk mode))
  nil)

(define-posix-test stat-mode.5
    (with-stat-mode (mode *test-directory*)
      (nix:s-isfifo mode))
  nil)

(define-posix-test stat-mode.6
    (with-stat-mode (mode *test-directory*)
      (nix:s-issock mode))
  nil)

(define-posix-test stat-mode.7
    (let ((link-pathname (make-pathname :name "stat-mode" :type "7"
                                        :defaults *test-directory*)))
      (unwind-protect
           (progn
             (nix:symlink *test-directory* link-pathname)
             (with-lstat-mode (mode link-pathname)
               (nix:s-islnk mode)))
        (ignore-errors (nix:unlink link-pathname))))
  t)

(define-posix-test stat-mode.8
    (let ((pathname (make-pathname :name "stat-mode" :type "8"
                                   :defaults *test-directory*)))
      (unwind-protect
           (progn
             (with-open-file (out pathname :direction :output)
               (write-line "test" out))
             (with-stat-mode (mode pathname)
               (nix:s-isreg mode)))
        (ignore-errors (delete-file pathname))))
  t)

;; FIXME: this fails on CMUCL because CMUCL treats filenames that begin
;; with [ specially: #p"[foo].txt" unparses to "\\[foo].txt"
;; we need a better native-namestring
#-cmu
(define-posix-test filename-designator.1
    (let ((file (format nil "~A/[foo].txt"
                        (native-namestring *test-directory*))))
      ;; creat() with a string as argument
      (nix:creat file nix:s-iwrite)
      ;; if this test fails, it will probably be with
      ;; "System call error 2 (No such file or directory)"
      (let ((*default-pathname-defaults* *test-directory*))
        (handler-case (nix:unlink (car (directory (merge-pathnames "*.txt"))))
          #+windows (nix:eacces () 0))))
  0)

(define-posix-test open.1
    (let ((name (merge-pathnames "open-test.txt" *test-directory*)))
      (unwind-protect
           (progn
             (nix:close
              (nix:creat name (logior nix:s-iwrite
                                           nix:s-iread)))
             (let ((fd (nix:open name nix:o-rdonly)))
               (ignore-errors (nix:close fd))
               (< fd 0)))
        (ignore-errors (nix:unlink name))))
  nil)

(define-posix-test open.error.1
    (handler-case (nix:open *test-directory* nix:o-wronly)
      (#+windows nix:eacces
       #-windows nix:eisdir () 'failed))
  failed)

#-(or (and x86-64 linux) windows)
(define-posix-test fcntl.1
    (let ((fd (nix:open "/dev/null" nix:o-nonblock)))
      (= (nix:fcntl fd nix:f-getfl) nix:o-nonblock))
  t)

;;; On AMD64/Linux O_LARGEFILE is always set, even though the whole
;;; flag makes no sense.
#+(and x86-64 linux)
(define-posix-test fcntl.1
    (let ((fd (nix:open "/dev/null" nix:o-nonblock)))
      (/= 0 (logand (nix:fcntl fd nix:f-getfl)
                    nix:o-nonblock)))
  t)

(define-posix-test opendir.1
    (let ((dir (nix:opendir "/")))
      (unwind-protect (cffi:null-pointer-p dir)
        (unless (cffi:null-pointer-p dir)
          (nix:closedir dir))))
  nil)

(define-posix-test readdir.1
    (let ((dir (nix:opendir "/")))
      (unwind-protect
           (block dir-loop
             (loop for dirent-name = (nix:readdir dir)
                   until (null dirent-name)
                   when (not (stringp dirent-name))
                   do (return-from dir-loop nil)
                   finally (return t)))
        (nix:closedir dir)))
  t)

;;; This test is buggy since LIST-CURRENT-DIR doesn't list symlinks
;;; for some reason.  Hopefully TEST-DIR doesn't contain any.
;;; Also, CLISP's directory doesn't list directories
#+nil
(define-posix-test readdir.dirent-name
    (let ((test-dir (pathname-directory-pathname
                     (truename
                      (asdf:system-definition-pathname
                       (asdf:find-system 'osicat))))))
      (flet ((list-current-dir ()
               (mapcar (lambda (p)
                         (let ((string (enough-namestring p test-dir)))
                           (if (pathname-name p)
                               string
                               (subseq string 0 (1- (length string))))))
                       (directory (make-pathname
                                   :name :wild
                                   :type :wild
                                   :defaults test-dir)))))
        (let ((dir (nix:opendir test-dir)))
          (unwind-protect
               (equal (sort (loop for name = (nix:readdir dir)
                                  until (null name) collect name)
                            #'string<)
                      (sort (append '("." "..") (list-current-dir))
                            #'string<))
            (nix:closedir dir)))))
  t)

(define-posix-test pwent.1
    ;; make sure that we found something
    (not (nix:getpwuid 0))
  nil)

(define-posix-test pwent.2
    ;; make sure that we found something
    (not (nix:getpwnam "root"))
  nil)

#-(and)
;;; Requires root or special group + plus a sensible thing on the port
(define-posix-test cfget.setispeed.1
    (with-open-file (s "/dev/ttyS0")
      (let* ((termios (nix:tcgetattr s))
             (old (nix:cfgetispeed termios))
             (new (if (= old nix:b2400)
                      nix:b9600
                      nix:b2400)))
        (nix:cfsetispeed new termios)
        (nix:tcsetattr 0 nix:tcsadrain termios)
        (setf termios (nix:tcgetattr s))
        (= new (nix:cfgetispeed termios))))
  t)

#-(and)
;; Requires root or special group + a sensible thing on the port
(define-posix-test cfget.setospeed.1
    (with-open-file (s "/dev/ttyS0" :direction :output :if-exists :append)
      (let* ((termios (nix:tcgetattr s))
             (old (nix:cfgetospeed termios))
             (new (if (= old nix:b2400)
                      nix:b9600
                      nix:b2400)))
        (nix:cfsetospeed new termios)
        (nix:tcsetattr 0 nix:tcsadrain termios)
        (setf termios (nix:tcgetattr 0))
        (= new (nix:cfgetospeed termios))))
  t)

(define-posix-test time.1
    (plusp (nix:time))
  t)

;;; TODO: not implemented in NIX yet
#-(and)
(define-posix-test utimes.1
    (let ((file (merge-pathnames #p"utimes.1" *test-directory*))
          (atime (random (1- (expt 2 31))))
          (mtime (random (1- (expt 2 31)))))
      (with-open-file (stream file :direction :output
                              :if-exists :supersede
                              :if-does-not-exist :create)
        (princ "Hello, utimes" stream))
      (nix:utime file atime mtime)
      (let* ((stat (nix:stat file)))
        (delete-file file)
        (list (= (nix:stat-atime stat) atime)
              (= (nix:stat-mtime stat) mtime))))
  (t t))

;;; readlink tests.

(define-posix-test readlink.1
    (let ((link-pathname (make-pathname :name "readlink" :type "1"
                                        :defaults *test-directory*)))
      (nix:symlink "/" link-pathname)
      (unwind-protect
           (nix:readlink link-pathname)
        (ignore-errors (nix:unlink link-pathname))))
  "/")

;;; Same thing, but with a very long link target (which doesn't have
;;; to exist).  This tests the array adjustment in the wrapper,
;;; provided that the target's length is long enough.
(define-posix-test readlink.2
    (let ((target-pathname (make-pathname
                            :name (make-string 255 :initial-element #\a)
                            :directory '(:absolute)))
          (link-pathname (make-pathname :name "readlink" :type "2"
                                        :defaults *test-directory*)))
      (nix:symlink target-pathname link-pathname)
      (unwind-protect
           (nix:readlink link-pathname)
        (ignore-errors (nix:unlink link-pathname))))
  #.(concatenate 'string "/" (make-string 255 :initial-element #\a)))

;;; The error tests are in the order of exposition from SUSv3.
#-windows
(define-posix-test readlink.error.1
    (let* ((subdir-pathname (test-dir "readlink.error.1"))
           (link-pathname (make-pathname :name "readlink.error" :type "1"
                                         :defaults subdir-pathname)))
      (nix:mkdir subdir-pathname #o777)
      (nix:symlink "/" link-pathname)
      (nix:chmod subdir-pathname 0)
      (unwind-protect
           (handler-case (nix:readlink link-pathname)
             (nix:eacces () 'failed))
        (ignore-errors
          (nix:chmod subdir-pathname #o777)
          (nix:unlink link-pathname)
          (nix:rmdir subdir-pathname))))
  failed)

(define-posix-test readlink.error.2
    (let* ((non-link-pathname (make-pathname :name "readlink.error" :type "2"
                                             :defaults *test-directory*))
           (fd (nix:open non-link-pathname nix:o-creat)))
      (unwind-protect
           (handler-case (nix:readlink non-link-pathname)
             (nix:einval () 'failed))
        (ignore-errors
          (nix:close fd)
          (nix:unlink non-link-pathname))))
  failed)

;;; Skipping EIO, ELOOP
(define-posix-test readlink.error.3
    (let* ((link-pathname (make-pathname :name "readlink.error" :type "3"
                                         :defaults *test-directory*))
           (bogus-pathname (merge-pathnames
                            (make-pathname
                             :name "bogus"
                             :directory '(:relative "readlink.error.3"))
                            *test-directory*)))
      (nix:symlink link-pathname link-pathname)
      (unwind-protect
           (handler-case (nix:readlink bogus-pathname)
             (nix:eloop () 'failed))
        (ignore-errors (nix:unlink link-pathname))))
  failed)

;;; Note: PATH_MAX and NAME_MAX need not be defined, and may vary, so
;;; failure of this test is not too meaningful.
(define-posix-test readlink.error.4
    (let ((pathname (make-pathname
                     :name (make-string 257 ; NAME_MAX plus some, maybe
                                        :initial-element #\a))))
      (handler-case (nix:readlink pathname)
        (nix:enametoolong () 'failed)))
  failed)

(define-posix-test readlink.error.5
    (let ((string (format nil "~v{/A~}" 2049 ; PATH_MAX/2 plus some, maybe
                          '(x))))
      (handler-case (nix:readlink string)
        (nix:enametoolong (c) 'failed)))
  failed)

(define-posix-test readlink.error.6
    (let ((no-such-pathname (make-pathname :name "readlink.error" :type "6"
                                           :defaults *test-directory*)))
      (handler-case (nix:readlink no-such-pathname)
        (nix:enoent (c) 'failed)))
  failed)

(define-posix-test readlink.error.7
    (let* ((non-link-pathname (make-pathname :name "readlink.error" :type "7"
                                             :defaults *test-directory*))
           (impossible-pathname (merge-pathnames
                                 (make-pathname
                                  :directory
                                  '(:relative "readlink.error.7")
                                  :name "readlink.error" :type "7")
                                 *test-directory*))
           (fd (nix:open non-link-pathname nix:o-creat)))
      (unwind-protect
           (handler-case (nix:readlink impossible-pathname)
             (nix:enotdir () 'failed))
        (ignore-errors
          (nix:close fd)
          (nix:unlink non-link-pathname))))
  failed)

(define-posix-test posix-error-syscall
    (handler-case (nix:mkdir "/" 0)
      (nix:posix-error (c)
        (nix:posix-error-syscall c)))
  nix:mkdir)

(define-posix-test isatty.1
    (let (fd)
      (unwind-protect
           (progn
             (setf fd (nix:open "/tmp/isatty.test" nix:o-creat))
             (nix:isatty fd))
        (when fd
          (nix:close fd))))
  0)

(define-posix-test isatty.2
    (let (fd)
      (unwind-protect
           (progn
             (setf fd (ignore-errors (nix:open "/dev/tty" nix:o-rdwr)))
             (if fd
                 (nix:isatty fd)
                 ;; FIXME: add pty stuff for proper testing
                 "could not open /dev/tty for testing isatty"))
        (when fd
          (nix:close fd))))
  1)
