;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; windows.lisp --- List of functions unsupported by Windows.
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

(define-unsupported-functions
  clock-getres clock-gettime clock-settime closedir closelog dirfd fchdir
  fchmod fcntl fork fstatvfs fsync getdomainname getegid geteuid getgid
  getgrgid getgrnam getpagesize getpgid getpgrp getpid getppid getpriority
  getpwnam getpwuid getrlimit getrusage gettimeofday getuid ioctl link lockf
  lstat mkdtemp mkfifo mknod mkstemp mlock mlockall mmap mprotect msync munlock
  munlockall munmap nice opendir openlog pread pwrite readdir readlink readv
  rewinddir seekdir select setegid setenv seteuid setgid setlogmask setpgid
  setpgrp setpriority setregid setreuid setrlimit setsid setuid statvfs symlink
  sync sysconf syslog telldir truncate uname unsetenv usleep writev s-issock
  s-islnk gethostname)
