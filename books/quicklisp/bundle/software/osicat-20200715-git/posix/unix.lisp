;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; unix.lisp --- CL-POSIX bindings.
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

;;; Needed for clock_gettime() and friends.
(define-foreign-library librt
  (:linux (:or "librt.so.1" "librt.so")))
(use-foreign-library librt)

;;;; stdlib.h

(defsyscall ("mktemp" %mktemp) :string
  (template :pointer))

(defun mktemp (&optional (template ""))
  (let ((template (concatenate 'string template "XXXXXX")))
    (with-foreign-string (ptr (filename template))
      (%mktemp ptr))))

(defsyscall ("mkstemp" %mkstemp) :int
  (template :pointer))

(defun mkstemp (&optional (template ""))
  (let ((template (concatenate 'string template "XXXXXX")))
    (with-foreign-string (ptr (filename template))
      (values (%mkstemp ptr) (foreign-string-to-lisp ptr)))))

(defsyscall ("mkdtemp" %mkdtemp) :string
  (template filename-designator))

(defun mkdtemp (&optional (template ""))
  (%mkdtemp (concatenate 'string template "XXXXXX")))

;;;; unistd.h

;;; directories

(defsyscall "fchdir" :int
  (fildes :int))

(defsyscall "link" :int
  (path1 filename-designator)
  (path2 filename-designator))

(defsyscall "isatty" :int
  (fd file-descriptor-designator))

;;; files

(defsyscall ("readlink" %readlink) ssize
  (path    filename-designator)
  (buf     :pointer)
  (bufsize size))

(defun readlink (path)
  "Read value of a symbolic link."
  (with-foreign-pointer (buf 4096 bufsize)
    (let ((count (%readlink path buf bufsize)))
      (values (foreign-string-to-lisp buf :count count)))))

(defsyscall "symlink" :int
  "Creates a symbolic link"
  (name1 filename-designator)
  (name2 filename-designator))

(defsyscall "chown" :int
  "Change ownership of a file."
  (path  filename-designator)
  (owner uid)
  (group uid))

(defsyscall "fchown" :int
  "Change ownership of an open file."
  (fd    file-descriptor-designator)
  (owner uid)
  (group uid))

(defsyscall "lchown" :int
  "Change ownership of a file or symlink."
  (path  filename-designator)
  (owner uid)
  (group uid))

(defsyscall "fchmod" :int
  (fd   file-descriptor-designator)
  (mode mode))

(defsyscall "sync" :void
  "Schedule all file system buffers to be written to disk.")

(defsyscall "fsync" :int
  (fildes file-descriptor-designator))

(defsyscall "lockf" :int
  "Apply, test or remove a POSIX lock on an open file."
  (fd  file-descriptor-designator)
  (cmd :int)
  (len off))

;;; processes

(defcfun ("nice" %nice) :int
  (increment :int))

(defun nice (increment)
  "Change process priority."
  (set-errno 0)
  (let ((r (%nice increment)))
    (if (and (= r -1) (/= (get-errno) 0))
        (posix-error)
        r)))

(defsyscall "fork" pid
  "Create a child process.")

(defsyscall "exit" :int
  "Exit a process immediately."
  (code :int))

(defcfun ("wait" %wait) pid
  (stat-loc :pointer))

(defun wait ()
  "Wait for any child process to terminate."
  (with-foreign-object (stat-loc :int)
    (let ((result (%wait stat-loc)))
      (values result (mem-ref stat-loc :int)))))

(defcfun ("waitpid" %waitpid) pid
  (pid pid)
  (stat-loc :pointer)
  (options :int))

(defun waitpid (pid &key (no-hang nil) (untraced nil))
  "Wait for a specific child process to terminate"
  (with-foreign-object (stat-loc :int)
    (let ((result (%waitpid pid stat-loc (logior (if no-hang wnohang 0)
                                                 (if untraced wuntraced 0)))))
      (values result (mem-ref stat-loc :int)))))

(defsyscall "getegid" gid
  "Get effective group id of the current process.")

(defsyscall "geteuid" uid
  "Get effective user id of the current process.")

(defsyscall "getgid" gid
  "Get real group id of the current process.")

(defsyscall "getpgid" pid
  "Get process group id of a process."
  (pid pid))

(defsyscall "getpgrp" pid
  "Get process group id of the current process.")

(defsyscall "getpid" pid
  "Returns the process id of the current process")

(defsyscall "getppid" pid
  "Returns the process id of the current process's parent")

(defsyscall "getuid" uid
  "Get real user id of the current process.")

(defsyscall "setegid" :int
  "Set effective group id of the current process."
  (gid gid))

(defsyscall "seteuid" :int
  "Set effective user id of the current process."
  (uid uid))

(defsyscall "setgid" :int
  "Get real group id of the current process."
  (gid gid))

(defsyscall "setpgid" :int
  "Set process group id of a process."
  (pid  pid)
  (pgid pid))

(defsyscall "setpgrp" pid
  "Set process group id of the current process.")

(defsyscall "setregid" :int
  "Set real and effective group id of the current process."
  (rgid gid)
  (egid gid))

(defsyscall "setreuid" :int
  "Set real and effective user id of the current process."
  (ruid uid)
  (euid uid))

(defsyscall "setsid" pid
  "Create session and set process group id of the current process.")

(defsyscall "setuid" :int
  "Set real user id of the current process."
  (uid uid))

;;; environment

(defsyscall "setenv" :int
  "Changes the value of an environment variable"
  (name  :string)
  (value :string))

(defsyscall "unsetenv" :int
  "Removes the binding of an environment variable"
  (name :string))

;;; time

(defsyscall "usleep" :int
  (useconds useconds))

;;; misc

(defsyscall ("gethostname" %gethostname) :int
  (name    :pointer)
  (namelen size))

(defun gethostname ()
  (with-foreign-pointer-as-string ((cstr size) 256)
    (%gethostname cstr size)))

(defsyscall ("getdomainname" %getdomainname) :int
  (name    :pointer)
  (namelen size))

(defun getdomainname ()
  (with-foreign-pointer-as-string ((cstr size) 256)
    (%getdomainname cstr size)))

(defsyscall ("sysconf" %sysconf) :long
  (name :int))

(defun sysconf (name)
  "Get value of configurable system variables."
  (set-errno 0)
  (let ((r (%sysconf name)))
    (if (and (= r -1) (/= (get-errno) 0))
        (posix-error)
        r)))

(defun getpagesize ()
  "Get memory page size."
  (sysconf sc-pagesize))

;;;; fcntl.h

(defun fcntl (fd cmd &optional (arg nil argp))
  (cond
    ((not argp) (fcntl-without-arg fd cmd))
    ((integerp arg) (fcntl-with-int-arg fd cmd arg))
    ((pointerp arg) (fcntl-with-pointer-arg fd cmd arg))
    (t (error "Wrong argument to fcntl: ~S" arg))))

;;;; ioctl.h

(defsyscall ("ioctl" %ioctl-without-arg) :int
  (fd      file-descriptor-designator)
  (request :int))

(defsyscall ("ioctl" %ioctl-with-arg) :int
 (fd      file-descriptor-designator)
 (request :int)
 (arg     :pointer))

(defun ioctl (fd request &optional (arg nil argp))
  "Control device."
  (cond
    ((not argp) (%ioctl-without-arg fd request))
    ((pointerp arg) (%ioctl-with-arg fd request arg))
    (t (error "Wrong argument to ioctl: ~S" arg))))

;;;; signal.h

(defsyscall "kill" :int
  "Send signal to a process."
  (pid pid)
  (sig :int))

;;;; sys/mman.h

(defsyscall "mlock" :int
  "Lock a range of process address space."
  (addr :pointer)
  (len  size))

(defsyscall "munlock" :int
  "Unlock a range of process address space."
  (addr :pointer)
  (len  size))

(defsyscall "mlockall" :int
  "Lock the address space of a process."
  (flags :int))

(defsyscall "munlockall" :int)

(defsyscall "munmap" :int
  "Unmap pages of memory."
  (addr :pointer)
  (len  size))

(defsyscall "msync" :int
  "Synchronize memory with physical storage."
  (addr  :pointer)
  (len   size)
  (flags :int))

(defsyscall "mprotect" :int
  "Set protection of memory mapping."
  (addr  :pointer)
  (len   size)
  (flags :int))

;;;; sys/time.h

(defsyscall ("gettimeofday" %gettimeofday) :int
  (tp  :pointer)
  (tzp :pointer))

(defun gettimeofday ()
  "Return the time in seconds and microseconds."
  (with-foreign-object (tv '(:struct timeval))
    (with-foreign-slots ((sec usec) tv (:struct timeval))
      (%gettimeofday tv (null-pointer))
      (values sec usec))))

;;; FIXME: or we can implement this through the MACH functions.
#+darwin
(progn
  (unsupported-function clock-getres)
  (unsupported-function clock-gettime)
  (unsupported-function clock-settime))

#-darwin
(progn
  (defsyscall ("clock_getres" %clock-getres) :int
    "Returns the resolution of the clock CLOCKID."
    (clockid clockid)
    (res     :pointer))

  (defun clock-getres (clock-id)
    (with-foreign-object (ts '(:struct timespec))
      (with-foreign-slots ((sec nsec) ts (:struct timespec))
        (%clock-getres clock-id ts)
        (values sec nsec))))

  (defsyscall ("clock_gettime" %clock-gettime) :int
    (clockid clockid)
    (tp      :pointer))

  (defun clock-gettime (clock-id)
    "Returns the time of the clock CLOCKID."
    (with-foreign-object (ts '(:struct timespec))
      (with-foreign-slots ((sec nsec) ts (:struct timespec))
        (%clock-gettime clock-id ts)
        (values sec nsec))))

  (defsyscall ("clock_settime" %clock-settime) :int
    (clockid clockid)
    (tp      :pointer))

  (defun clock-settime (clock-id)
    "Sets the time of the clock CLOCKID."
    (with-foreign-object (ts '(:struct timespec))
      (with-foreign-slots ((sec nsec) ts (:struct timespec))
        (%clock-settime clock-id ts)
        (values sec nsec)))))

#-(or darwin openbsd)
(progn
  (defsyscall ("timer_create" %timer-create) :int
    (clockid clockid)
    (sigevent :pointer)
    (timer :pointer))

  (defun timer-create (clock-id notify-method
                       &key signal notify-value function attributes
                            #+linux thread-id)
    "Creates a new per-process interval timer."
    (with-foreign-object (se '(:struct sigevent))
      (with-foreign-slots ((notify signo value
                            notify-function notify-attributes
                            #+linux notify-thread-id)
                           se (:struct sigevent))
        (with-foreign-slots ((int) value (:union sigval))
          (setf notify notify-method)
          (cond ((= notify-method sigev-none))
                ((= notify-method sigev-signal)
                 (setf signo signal
                       int notify-value))
                #+linux
                ((= notify-method (logior sigev-signal sigev-thread-id))
                 (setf signo signal
                       notify-thread-id thread-id
                       int notify-value))
                ((= notify-method sigev-thread)
                 (setf notify-function function
                       notify-attributes attributes
                       int notify-value))
                (t (error "bad timer notification method")))
          (with-foreign-object (timer 'timer)
            (%timer-create clock-id se timer)
            (mem-ref timer :int))))))

  (defsyscall ("timer_delete" timer-delete) :int
    "Deletes the timer identified by TIMER-ID."
    (timer-id timer))

  (defsyscall ("timer_getoverrun" timer-getoverrun) :int
    "Returns the overrun count for the timer identified by TIMER-ID."
    (timer-id timer))

  (defsyscall ("timer_gettime" %timer-gettime) :int
    (timer timer)
    (itimerspec :pointer))

  (defun deconstruct-itimerspec (its)
    (with-foreign-slots ((interval value) its (:struct itimerspec))
      (with-foreign-slots ((sec nsec) interval (:struct timespec))
        (let ((interval-sec sec)
              (interval-nsec nsec))
          (with-foreign-slots ((sec nsec) value (:struct timespec))
            (values interval-sec interval-nsec sec nsec))))))

  (defun timer-gettime (timer-id)
    "Returns the interval and the time until next expiration for the
timer specified by TIMER-ID.  Both the interval and the time are returned
as seconds and nanoseconds, so four values are returned."
    (with-foreign-object (its '(:struct itimerspec))
      (%timer-gettime timer-id its)
      (values-list (multiple-value-list (deconstruct-itimerspec its)))))

  (defsyscall ("timer_settime" %timer-settime) :int
    (timer timer)
    (flags :int)
    (new :pointer)
    (old :pointer))

  (defun timer-settime (timer-id flags interval-sec interval-nsec
                        initial-sec initial-nsec
                        &optional return-previous-p)
    "Arms or disarms the timer identified by TIMER-ID."
    (with-foreign-object (new '(:struct itimerspec))
      (with-foreign-slots ((interval value) new (:struct itimerspec))
        (with-foreign-slots ((sec nsec) interval (:struct timespec))
          (setf sec interval-sec
                nsec interval-nsec)
          (with-foreign-slots ((sec nsec) value (:struct timespec))
            (setf sec initial-sec
                  nsec initial-nsec)
            (with-foreign-object (old '(:struct itimerspec))
              (let ((result (%timer-settime timer-id flags new old)))
                (if return-previous-p
                    (values-list (multiple-value-list (deconstruct-itimerspec old)))
                    result)))))))))

;;;; sys/stat.h

(defun lstat (path)
  "Get information about a file or symlink."
  (funcall-stat #'%lstat path))

(defsyscall "mkfifo" :int
  "Create a FIFO (named pipe)."
  (path filename-designator)
  (mode mode))

;;;; syslog.h

(defvar *syslog-identity* nil)

(defsyscall ("openlog" %openlog) :void
  (ident    :string)
  (option   :int)
  (facility syslog-facilities))

;;; not my BUG: on Linux openlog() keeps a pointer to the "ident"
;;; string which syslog() then uses when logging, therefore
;;; we need to keep the foreign string around.
;;;
;;; FIXME: this workaround seems broken to me. --luis
(defun openlog (name options &optional (facility :user))
  "Open system log."
  (when *syslog-identity*
    (foreign-string-free *syslog-identity*)
    (setf *syslog-identity* nil))
  (setf *syslog-identity* (foreign-string-alloc name))
  (%openlog *syslog-identity* options facility))

(defsyscall ("syslog" %syslog) :void
  (priority syslog-priorities)
  (format   :string)
  (message  :string))

(defun syslog (priority format &rest args)
  "Send a message to the syslog facility, with severity level
PRIORITY.  The message will be formatted by CL:FORMAT (rather
than C's printf) with format string FORMAT and arguments ARGS."
  (%syslog priority "%s" (format nil "~?" format args)))

(defsyscall ("closelog" %closelog) :void)

(defun closelog ()
  "Close system log."
  (%closelog)
  (when *syslog-identity*
    (foreign-string-free *syslog-identity*)
    (setf *syslog-identity* nil)))

(defsyscall "setlogmask" :int
  (mask :int))

;;;; sys/resource.h

(defun getrlimit (resource)
  (with-foreign-object (rl '(:struct rlimit))
    (with-foreign-slots ((cur max) rl (:struct rlimit))
      (%getrlimit resource rl)
      (values cur max))))

(defun setrlimit (resource soft-limit hard-limit)
  (with-foreign-object (rl '(:struct rlimit))
    (with-foreign-slots ((cur max) rl (:struct rlimit))
      (setf cur soft-limit
            max hard-limit)
      (%setrlimit resource rl))))

(defsyscall ("getrusage" %getrusage) :int
  (who   :int)
  (usage :pointer))

;;; TODO: it might be more convenient to return a wrapper object here
;;; instead like we do in STAT.
(defun getrusage (who)
  (with-foreign-object (ru '(:struct rusage))
    (%getrusage who ru)
    (with-foreign-slots ((maxrss ixrss idrss isrss minflt majflt nswap inblock
                          oublock msgsnd msgrcv nsignals nvcsw nivcsw)
                         ru (:struct rusage))
      (values (foreign-slot-value
               (foreign-slot-pointer ru '(:struct rusage) 'utime)
               '(:struct timeval) 'sec)
              (foreign-slot-value
               (foreign-slot-pointer ru '(:struct rusage) 'utime)
               '(:struct timeval) 'usec)
              (foreign-slot-value
               (foreign-slot-pointer ru '(:struct rusage) 'stime)
               '(:struct timeval) 'sec)
              (foreign-slot-value
               (foreign-slot-pointer ru '(:struct rusage) 'stime)
               '(:struct timeval) 'usec)
              maxrss ixrss idrss isrss minflt majflt
              nswap inblock oublock msgsnd
              msgrcv nsignals nvcsw nivcsw))))

(defsyscall "getpriority" :int
  (which :int)
  (who   :int))

(defsyscall "setpriority" :int
  (which :int)
  (who   :int)
  (value :int))

;;;; sys/utsname.h

(defsyscall ("uname" %uname) :int
  (buf :pointer))

(defun uname ()
  "Get name and information about current kernel."
  (with-foreign-object (buf '(:struct utsname))
    (bzero buf size-of-utsname)
    (%uname buf)
    (macrolet ((utsname-slot (name)
                 `(foreign-string-to-lisp
                   (foreign-slot-pointer buf '(:struct utsname) ',name))))
      (values (utsname-slot sysname)
              (utsname-slot nodename)
              (utsname-slot release)
              (utsname-slot version)
              (utsname-slot machine)))))

;;;; sys/statvfs.h

(defun funcall-statvfs (fn arg)
  (with-foreign-object (buf '(:struct statvfs))
    (funcall fn arg buf)
    (with-foreign-slots ((bsize frsize blocks bfree bavail files
                          ffree favail fsig flag namemax)
                         buf (:struct statvfs))
      (values bsize frsize blocks bfree bavail files
              ffree favail fsig flag namemax))))

(defun statvfs (path)
  "Retrieve file system information."
  (funcall-statvfs #'%statvfs path))

(defun fstatvfs (fd)
  "Retrieve file system information."
  (funcall-statvfs #'%fstatvfs fd))

;;;; pwd.h

;;; Should actually be
;;;   (errno-wrapper :int :error-predicate (lambda (x) (not (zerop x))))
;;; but see explanation below.
(defcfun ("getpwuid_r" %getpwuid-r)
    :int
  (uid     uid)
  (pwd     :pointer)
  (buffer  :pointer)
  (bufsize size)
  (result  :pointer))

(defcfun ("getpwnam_r" %getpwnam-r)
    :int
  (name    :string)
  (pwd     :pointer)
  (buffer  :pointer)
  (bufsize size)
  (result  :pointer))

(defun funcall-getpw (fn arg)
  ;; http://pubs.opengroup.org/onlinepubs/009695399/functions/getpwnam.html
  ;; "Applications wishing to check for error situations should set
  ;; errno to 0 before calling getpwnam(). If getpwnam() returns null
  ;; pointer and errno is non-zero, an error occured.
  (set-errno 0)
  (with-foreign-objects ((pw '(:struct passwd)) (pwp :pointer))
    (with-foreign-pointer (buf 4096 bufsize)
      (with-foreign-slots ((name passwd uid gid gecos dir shell) pw (:struct passwd))
        (let ((ret (funcall fn arg pw buf bufsize pwp)))
          (cond ((and (null-pointer-p (mem-ref pwp :pointer))
                      (not (zerop (get-errno))))
                 (posix-error ret))
                ((and (null-pointer-p (mem-ref pwp :pointer))
                      (zerop (get-errno)))
                 nil)
                (t (values name passwd uid gid gecos dir shell))))))))

(defun getpwuid (uid)
  "Gets the password-entry of a user, by user id."
  (funcall-getpw #'%getpwuid-r uid))

(defun getpwnam (name)
  "Gets the password-entry of a user, by username."
  (funcall-getpw #'%getpwnam-r name))

;;;; grp.h

(defsyscall ("getgrgid_r" %getgrgid-r) :int
  (uid     uid)
  (grp     :pointer)
  (buffer  :pointer)
  (bufsize size)
  (result  :pointer))

(defsyscall ("getgrnam_r" %getgrnam-r) :int
  (name    :string)
  (grp     :pointer)
  (buffer  :pointer)
  (bufsize size)
  (result  :pointer))

(defun funcall-getgr (fn arg)
  (with-foreign-objects ((gr '(:struct group)) (grp :pointer))
    (with-foreign-pointer (buf 4096 bufsize)
      (with-foreign-slots ((name passwd gid) gr (:struct group))
        (if (and (zerop (funcall fn arg gr buf bufsize grp))
                 (null-pointer-p (mem-ref grp :pointer)))
            (values)
            (values name passwd gid))))))

(defun getgrgid (gid)
  "Gets a group-entry, by group id. (reentrant)"
  (funcall-getgr #'%getgrgid-r gid))

(defun getgrnam (name)
  "Gets a group-entry, by group name. (reentrant)"
  (funcall-getgr #'%getgrnam-r name))

;;;; dirent.h

(defsyscall "opendir" :pointer
  "Opens a directory for listing of its contents"
  (filename filename-designator))

(defsyscall "closedir" :int
  "Closes a directory when done listing its contents"
  (dir :pointer))

(defun readdir (dir)
  "Reads an item from the listing of a directory (reentrant)"
  (with-foreign-objects ((entry '(:struct dirent)) (result :pointer))
    (%readdir-r dir entry result)
    (if (null-pointer-p (mem-ref result :pointer))
        nil
        (with-foreign-slots ((name #-sunos type #-sunos fileno) entry (:struct dirent))
          (values (foreign-string-to-lisp name) #-sunos type #-sunos fileno)))))

(defsyscall "rewinddir" :void
  "Rewinds a directory."
  (dir :pointer))

(defsyscall "seekdir" :void
  "Seeks a directory."
  (dir :pointer)
  (pos :long))

;;; FIXME: According to POSIX docs "no errors are defined" for
;;; telldir() but Linux manpages specify a possible EBADF.
(defsyscall "telldir" off
  "Returns the current location in a directory"
  (dir :pointer))

;;;; sys/uio.h

(defsyscall "readv" ssize
  (fd    file-descriptor-designator)
  (iov   :pointer)
  (count size))

(defsyscall "writev" ssize
  (fd    file-descriptor-designator)
  (iov   :pointer)
  (count size))

;; termios.h

(defsyscall "tcgetattr" :int
  (fd      file-descriptor-designator)
  (termios :pointer))

(defsyscall "tcsetattr" :int
  (fd      file-descriptor-designator)
  (mode    :int)
  (termios :pointer))
