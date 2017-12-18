;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; wrappers.lisp --- Grovel wrapper definitions.
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

(in-package #:osicat-posix)

(c "#if defined(__linux__)")
(define "_XOPEN_SOURCE" 600)
(define "_LARGEFILE_SOURCE")
(define "_LARGEFILE64_SOURCE")
(define "_FILE_OFFSET_BITS" 64)
(define "_GNU_SOURCE")
(c "#endif")

(include "string.h" "errno.h"  "sys/types.h" "sys/stat.h"
         "fcntl.h" "unistd.h" "dirent.h"  "sys/time.h")

#-windows
(include "syslog.h" "sys/mman.h" "sys/resource.h" "sys/statvfs.h" "sys/wait.h")

;;;; Large-file support

;;; FIXME: this is only necessary on Linux right?

(defwrapper "lseek" ("off_t" (errno-wrapper off))
  (fildes ("int" file-descriptor-designator))
  (offset ("off_t" off))
  (whence :int))

#-windows
(defwrapper "truncate" ("int" (errno-wrapper :int))
  (path ("const char*" filename-designator))
  (length ("off_t" off)))

(defwrapper "ftruncate" ("int" (errno-wrapper :int))
  (fd ("int" file-descriptor-designator))
  (length ("off_t" off)))

#-windows
(defwrapper "mmap" ("void*" (errno-wrapper
                             :pointer
                             :error-predicate (lambda (p) (pointer-eq p *map-failed-pointer*))))
  (start :pointer)
  (length ("size_t" size))
  (prot :int)
  (flags :int)
  (fd ("int" file-descriptor-designator))
  (offset ("off_t" off)))

#+linux
(defwrapper "mremap" ("void*" (errno-wrapper
                               :pointer
                               :error-predicate (lambda (p) (pointer-eq p *map-failed-pointer*))))
  (old-address :pointer)
  (old-size ("size_t" size))
  (new-size ("size_t" size))
  (flags :int))

(defwrapper ("stat" %stat) ("int" (errno-wrapper :int))
  (file-name ("const char*" filename-designator))
  (buf ("struct stat*" :pointer)))

(defwrapper ("fstat" %fstat) ("int" (errno-wrapper :int))
  (filedes ("int" file-descriptor-designator))
  (buf ("struct stat*" :pointer)))

#-windows
(defwrapper ("lstat" %lstat) ("int" (errno-wrapper :int))
  (file-name ("const char*" filename-designator))
  (buf ("struct stat*" :pointer)))

#-windows
(defwrapper "pread" ("ssize_t" (errno-wrapper ssize))
  (fd ("int" file-descriptor-designator))
  (buf :pointer)
  (count ("size_t" size))
  (offset ("off_t" off)))

#-windows
(defwrapper "pwrite" ("ssize_t" (errno-wrapper ssize))
  (fd ("int" file-descriptor-designator))
  (buf ("const void*" :pointer))
  (count ("size_t" size))
  (offset ("off_t" off)))

#-windows
(defwrapper ("readdir_r" %readdir-r) ("int" (errno-wrapper :int))
  (dirp ("DIR*" :pointer))
  (entry ("struct dirent*" :pointer))
  (result ("struct dirent**" :pointer)))

#-windows
(defwrapper ("getrlimit" %getrlimit) ("int" (errno-wrapper :int))
  (resource :int)
  (rlim ("struct rlimit*" :pointer)))

#-windows
(defwrapper ("setrlimit" %setrlimit) ("int" (errno-wrapper :int))
  (resource :int)
  (rlim ("const struct rlimit*" :pointer)))

#-windows
(defwrapper ("statvfs" %statvfs) ("int" (errno-wrapper :int))
  (path ("const char*" filename-designator))
  (buf ("struct statvfs*" :pointer)))

#-windows
(defwrapper ("fstatvfs" %fstatvfs) ("int" (errno-wrapper :int))
  (fd ("int" file-descriptor-designator))
  (buf ("struct statvfs*" :pointer)))

#-windows
(defwrapper* "fcntl_without_arg" ("int" (errno-wrapper :int))
    ((fd ("int" file-descriptor-designator)) (cmd :int))
  "return fcntl(fd, cmd);")

;;; FIXME: Linux/glibc says ARG's type is long, POSIX says it's int.
;;; Is this an issue?
#-windows
(defwrapper* "fcntl_with_int_arg" ("int" (errno-wrapper :int))
  ((fd ("int" file-descriptor-designator)) (cmd :int) (arg :int))
  "return fcntl(fd, cmd, arg);")

#-windows
(defwrapper* "fcntl_with_pointer_arg" ("int" (errno-wrapper :int))
    ((fd ("int" file-descriptor-designator)) (cmd :int) (arg :pointer))
  "return fcntl(fd, cmd, arg);")

#+linux
(defwrapper "posix_fallocate" ("int" (errno-wrapper :int
                                                    :error-predicate (lambda (r) (not (zerop r)))
                                                    :error-generator syscall-signal-posix-error-via-return-value))
  (fd ("int" file-descriptor-designator))
  (offset ("off_t" off))
  (length ("off_t" off)))

;;;; Miscellaneous

(defwrapper* "get_errno" :int ()
  "return errno;")

(defwrapper* "set_errno" :int ((value :int))
  "errno = value;"
  "return errno;")

;; Note: since we define _GNU_SOURCE on Linux (to get at mremap()), we
;; get the GNU version of strerror_r() which doesn't always store the
;; result in `buf'.
#-windows
(defwrapper "strerror_r" #+linux :string #-linux :int
  (errnum :int)
  (buf :string)
  (buflen ("size_t" size)))

#-windows
(defwrapper* "log_mask" :int ((priority :int))
  "return LOG_MASK(priority);")

#-windows
(defwrapper* "log_upto" :int ((priority :int))
  "return LOG_UPTO(priority);")

;;; Create a special or an ordinary file.
#-windows
(defwrapper "mknod" :int
  (path ("const char*" filename-designator))
  (mode ("mode_t" mode))
  (dev ("dev_t" dev)))

;;; dirfd() is a macro on BSDs
;;;
;;; Returns the file descriptor of a directory.
#-windows
(defwrapper "dirfd" :int
  (dir ("DIR*" :pointer)))

(defwrapper* "s_isreg" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISREG(mode);")

(defwrapper* "s_isdir" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISDIR(mode);")

(defwrapper* "s_ischr" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISCHR(mode);")

(defwrapper* "s_isblk" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISBLK(mode);")

(defwrapper* "s_isfifo" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISFIFO(mode);")

#-windows
(defwrapper* "s_islnk" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISLNK(mode);")

#-windows
(defwrapper* "s_issock" ("int" :boolean) ((mode ("mode_t" mode)))
  "return S_ISSOCK(mode);")

;; (defwrapper* "fileno" :int ((fp ("FILE *" :pointer)))
;;   "return fileno(fp);")



;; wrap C macros that decode wait/waitpid return value
#-windows
(defwrapper* "wifexited" ("int" :boolean) ((status :int))
  "return WIFEXITED(status);")

#-windows
(defwrapper* "wifsignaled" ("int" :boolean) ((status :int))
  "return WIFEXITED(status);")

#-windows
(defwrapper* "wcoredump" ("int" :boolean) ((status :int))
  "
#ifdef WCOREDUMP
  return WCOREDUMP(status);
#else
  return 0;
#endif
")

#-windows
(defwrapper* "wifcontinued" ("int" :boolean) ((status :int))
  "
#ifdef WIFCONTINUED
  return WIFCONTINUED(status);
#else
  return 0;
#endif
")

#-windows
(defwrapper* "wifstopped" ("int" :boolean) ((status :int))
  "return WIFSTOPPED(status);")


#-windows
(defwrapper* "wexitstatus" :int ((status :int))
  "return WEXITSTATUS(status);")

#-windows
(defwrapper* "wtermsig" :int ((status :int))
  "return WTERMSIG(status);")

#-windows
(defwrapper* "wstopsig" :int ((status :int))
  "return WSTOPSIG(status);")
