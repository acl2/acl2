;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; unixint.lisp --- Grovel definitions for OSICAT.
;;;
;;; Copyright (C) 2005-2006, Matthew Backes  <lucca@accela.net>
;;; Copyright (C) 2005-2006, Dan Knapp  <dankna@accela.net>
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

#+linux
(define "_GNU_SOURCE")

;;; largefile support on linux
;;; TODO: check if these flags are required on solaris too
#+linux
(progn
  (define "_XOPEN_SOURCE" 600)
  (define "_LARGEFILE_SOURCE")
  (define "_LARGEFILE64_SOURCE")
  (define "_FILE_OFFSET_BITS" 64))

(include "sys/types.h" "sys/stat.h" "sys/mman.h" "sys/wait.h" "fcntl.h"
         "errno.h" "signal.h" "unistd.h" "termios.h" "sys/ioctl.h" "limits.h"
         "sys/uio.h"  "time.h" "dirent.h" "pwd.h" "grp.h" "syslog.h"
         "sys/resource.h" "stdlib.h" "sys/utsname.h" "sys/statvfs.h"
         #+linux "sys/syscall.h")

(in-package #:osicat-posix)

(constant (sighup "SIGHUP") :documentation "terminal line hangup.")
(constant (sigquit "SIGQUIT") :documentation "quit program.")
(constant (sigtrap "SIGTRAP") :documentation "trace trap.")
#-linux
(constant (sigemt "SIGEMT") :documentation "emulate instruction executed.")
(constant (sigkill "SIGKILL") :documentation "kill program.")
(constant (sigbus "SIGBUS") :documentation "bus error.")
(constant (sigsys "SIGSYS") :documentation "non-existent system call invoked.")
(constant (sigpipe "SIGPIPE") :documentation "write on a pipe with no reader.")
(constant (sigalrm "SIGALRM") :documentation "real-timeimer expired.")
(constant (sigurg "SIGURG")
          :documentation "urgent condition present on socket.")
(constant (sigstop "SIGSTOP")
          :documentation "stop (cannot be caught or ignored).")
(constant (sigtstp "SIGTSTP")
          :documentation "stop signal generated from keyboard.")
(constant (sigcont "SIGCONT") :documentation "continue after stop.")
(constant (sigchld "SIGCHLD") :documentation "child status has changed.")
(constant (sigttin "SIGTTIN")
          :documentation "background read attempted from control terminal.")
(constant (sigttou "SIGTTOU")
          :documentation "background write attempted from control terminal.")
(constant (sigio "SIGIO")
          :documentation "I/O is possible on a descriptor (see fcntl(2)).")
(constant (sigxcpu "SIGXCPU")
          :documentation "cpuime limit exceeded (see setrlimit(2)).")
(constant (sigxfsz "SIGXFSZ")
          :documentation "file size limit exceeded (see setrlimit(2)).")
(constant (sigvtalrm "SIGVTALRM")
          :documentation "virtualime alarm (see setitimer(2)).")
(constant (sigprof "SIGPROF")
          :documentation "profilingimer alarm (see setitimer(2)).")
(constant (sigwinch "SIGWINCH") :documentation "Window size change.")
#-linux
(constant (siginfo "SIGINFO") :documentation "status request from keyboard.")
(constant (sigusr1 "SIGUSR1") :documentation "User defined signal 1.")
(constant (sigusr2 "SIGUSR2") :documentation "User defined signal 2.")

#+linux
(progn
  (constant (sigrtmin "SIGRTMIN")
            :documentation "Smallest real-time signal number.")
  (constant (sigrtmax "SIGRTMAX")
            :documentation "Largest real-time signal number."))

(constant (sigev-none "SIGEV_NONE")
          :documentation "No notification when the event occurs.")
(constant (sigev-signal "SIGEV_SIGNAL")
          :documentation "Generate a signal when the event occurs.")
(constant (sigev-thread "SIGEV_THREAD")
          :documentation "Call a function when the event occurs.")
#+linux
(constant (sigev-thread-id "SIGEV_THREAD_ID")
          :documentation
          "Send a signal to a specific thread when the event occurs.")

(cunion sigval "union sigval"
  (int "sival_int" :type :int)
  (ptr "sival_ptr" :type :pointer))

#-openbsd
(cstruct sigevent "struct sigevent"
  (notify            "sigev_notify"            :type :int)
  (signo             "sigev_signo"             :type :int)
  (value             "sigev_value"             :type sigval)
  (notify-function   "sigev_notify_function"   :type :pointer)
  (notify-attributes "sigev_notify_attributes" :type :pointer)
  #+linux
  (notify-thread-id  "_sigev_un._tid"          :type pid))

;;;; fcntl()

(constant (f-dupfd "F_DUPFD"))
(constant (f-getfd "F_GETFD"))
(constant (f-setfd "F_SETFD"))
(constant (f-getfl "F_GETFL"))
(constant (f-setfl "F_SETFL"))
(constant (f-getlk "F_GETLK"))
(constant (f-setlk "F_SETLK"))
(constant (f-setlkw "F_SETLKW"))
(constant (f-getown "F_GETOWN"))
(constant (f-setown "F_SETOWN"))
(constant (f-rdlck "F_RDLCK"))
(constant (f-wrlck "F_WRLCK"))
(constant (f-unlck "F_UNLCK"))

#+linux
(progn
  (constant (f-getsig "F_GETSIG"))
  (constant (f-setsig "F_SETSIG"))
  (constant (f-setlease "F_SETLEASE"))
  (constant (f-getlease "F_GETLEASE")))

;;; lockf()
(constant (f-lock  "F_LOCK"))
(constant (f-tlock "F_TLOCK"))
(constant (f-ulock "F_ULOCK"))
(constant (f-test  "F_TEST"))

;;; mmap()
(constant (prot-none   "PROT_NONE")   :documentation "mmap: no protection")
(constant (prot-read   "PROT_READ")   :documentation "mmap: read protection")
(constant (prot-write  "PROT_WRITE")  :documentation "mmap: write protection")
(constant (prot-exec   "PROT_EXEC")   :documentation "mmap: execute protection")
(constant (map-shared  "MAP_SHARED")  :documentation "mmap: shared memory")
(constant (map-private "MAP_PRIVATE") :documentation "mmap: private mapping")
(constant (map-fixed   "MAP_FIXED")   :documentation "mmap: map at location")
(constant (map-failed  "MAP_FAILED")  :documentation "mmap: failure")

#+linux
(progn
  (constant (map-noreserve "MAP_NORESERVE"))
  (constant (map-locked "MAP_LOCKED"))
  (constant (map-growsdown "MAP_GROWSDOWN"))
  (constant (map-anon "MAP_ANON"))
  (constant (map-anonymous "MAP_ANONYMOUS"))
  (constant (map-populate "MAP_POPULATE"))
  (constant (map-nonblock "MAP_NONBLOCK")))

#+freebsd
(progn
  (constant (map-anon "MAP_ANON"))
  (constant (map-hassemaphore "MAP_HASSEMAPHORE"))
  (constant (map-inherit "MAP_INHERIT"))
  (constant (map-nocore "MAP_NOCORE"))
  (constant (map-nosync "MAP_NOSYNC"))
  (constant (map-stack "MAP_STACK")))

;;; mremap()
#+linux
(progn
  (constant (mremap-maymove "MREMAP_MAYMOVE"))
  (constant (mremap-fixed "MREMAP_FIXED")))

;;; msync()
(constant (ms-async "MS_ASYNC") :documentation "msync: return immediately")
(constant (ms-sync "MS_SYNC")
          :documentation "msync: perform synchronous writes")
(constant (ms-invalidate "MS_INVALIDATE")
          :documentation "msync: invalidate all data")

;;; mlockall()
(constant (mcl-current "MCL_CURRENT")
          :documentation "mlockall: lock currently mapped pages.")
(constant (mcl-future "MCL_FUTURE")
          :documentation "mlockall: lock pages that become mapped.")

;;;; sysconf constants

(constant (sc-aio-listio-max "_SC_AIO_LISTIO_MAX"))
(constant (sc-aio-max "_SC_AIO_MAX"))
(constant (sc-aio-prio-delta-max "_SC_AIO_PRIO_DELTA_MAX"))
(constant (sc-arg-max "_SC_ARG_MAX"))
(constant (sc-atexit-max "_SC_ATEXIT_MAX"))
(constant (sc-bc-base-max "_SC_BC_BASE_MAX"))
(constant (sc-bc-dim-max "_SC_BC_DIM_MAX"))
(constant (sc-bc-scale-max "_SC_BC_SCALE_MAX"))
(constant (sc-bc-string-max "_SC_BC_STRING_MAX"))
(constant (sc-child-max "_SC_CHILD_MAX"))
(constant (sc-clk-tck "_SC_CLK_TCK"))
(constant (sc-coll-weights-max "_SC_COLL_WEIGHTS_MAX"))
(constant (sc-delaytimer-max "_SC_DELAYTIMER_MAX"))
(constant (sc-expr-nest-max "_SC_EXPR_NEST_MAX"))
(constant (sc-host-name-max "_SC_HOST_NAME_MAX"))
(constant (sc-iov-max "_SC_IOV_MAX"))
(constant (sc-line-max "_SC_LINE_MAX"))
(constant (sc-login-name-max "_SC_LOGIN_NAME_MAX"))
(constant (sc-ngroups-max "_SC_NGROUPS_MAX"))
(constant (sc-getgr-r-size-max "_SC_GETGR_R_SIZE_MAX"))
(constant (sc-getpw-r-size-max "_SC_GETPW_R_SIZE_MAX"))
(constant (sc-mq-open-max "_SC_MQ_OPEN_MAX"))
(constant (sc-mq-prio-max "_SC_MQ_PRIO_MAX"))
(constant (sc-open-max "_SC_OPEN_MAX"))
(constant (sc-advisory-info "_SC_ADVISORY_INFO"))
(constant (sc-barriers "_SC_BARRIERS"))
(constant (sc-asynchronous-io "_SC_ASYNCHRONOUS_IO"))
(constant (sc-clock-selection "_SC_CLOCK_SELECTION"))
(constant (sc-cputime "_SC_CPUTIME"))
(constant (sc-file-locking "_SC_FILE_LOCKING"))
(constant (sc-fsync "_SC_FSYNC"))
(constant (sc-ipv6 "_SC_IPV6"))
(constant (sc-job-control "_SC_JOB_CONTROL"))
(constant (sc-mapped-files "_SC_MAPPED_FILES"))
(constant (sc-memlock "_SC_MEMLOCK"))
(constant (sc-memlock-range "_SC_MEMLOCK_RANGE"))
(constant (sc-memory-protection "_SC_MEMORY_PROTECTION"))
(constant (sc-message-passing "_SC_MESSAGE_PASSING"))
(constant (sc-monotonic-clock "_SC_MONOTONIC_CLOCK"))
#-darwin (constant (sc-multi-process "_SC_MULTI_PROCESS"))
(constant (sc-prioritized-io "_SC_PRIORITIZED_IO"))
(constant (sc-priority-scheduling "_SC_PRIORITY_SCHEDULING"))
(constant (sc-raw-sockets "_SC_RAW_SOCKETS"))
(constant (sc-reader-writer-locks "_SC_READER_WRITER_LOCKS"))
(constant (sc-realtime-signals "_SC_REALTIME_SIGNALS"))
(constant (sc-regexp "_SC_REGEXP"))
(constant (sc-saved-ids "_SC_SAVED_IDS"))
(constant (sc-semaphores "_SC_SEMAPHORES"))
(constant (sc-shared-memory-objects "_SC_SHARED_MEMORY_OBJECTS"))
(constant (sc-shell "_SC_SHELL"))
(constant (sc-spawn "_SC_SPAWN"))
(constant (sc-spin-locks "_SC_SPIN_LOCKS"))
(constant (sc-sporadic-server "_SC_SPORADIC_SERVER"))
(constant (sc-symloop-max "_SC_SYMLOOP_MAX"))
(constant (sc-synchronized-io "_SC_SYNCHRONIZED_IO"))
(constant (sc-thread-attr-stackaddr "_SC_THREAD_ATTR_STACKADDR"))
(constant (sc-thread-attr-stacksize "_SC_THREAD_ATTR_STACKSIZE"))
(constant (sc-thread-cputime "_SC_THREAD_CPUTIME"))
(constant (sc-thread-prio-inherit "_SC_THREAD_PRIO_INHERIT"))
(constant (sc-thread-prio-protect "_SC_THREAD_PRIO_PROTECT"))
(constant (sc-thread-priority-scheduling "_SC_THREAD_PRIORITY_SCHEDULING"))
(constant (sc-thread-process-shared "_SC_THREAD_PROCESS_SHARED"))
(constant (sc-thread-safe-functions "_SC_THREAD_SAFE_FUNCTIONS"))
(constant (sc-thread-sporadic-server "_SC_THREAD_SPORADIC_SERVER"))
(constant (sc-threads "_SC_THREADS"))
(constant (sc-timeouts "_SC_TIMEOUTS"))
(constant (sc-timers "_SC_TIMERS"))
(constant (sc-trace "_SC_TRACE"))
(constant (sc-trace-event-filter "_SC_TRACE_EVENT_FILTER"))
(constant (sc-trace-inherit "_SC_TRACE_INHERIT"))
(constant (sc-trace-log "_SC_TRACE_LOG"))
(constant (sc-typed-memory-objects "_SC_TYPED_MEMORY_OBJECTS"))
(constant (sc-version "_SC_VERSION"))
(constant (sc-v6-ilp32-off32 "_SC_V6_ILP32_OFF32"))
(constant (sc-v6-ilp32-offbig "_SC_V6_ILP32_OFFBIG"))
(constant (sc-v6-lp64-off64 "_SC_V6_LP64_OFF64"))
(constant (sc-v6-lpbig-offbig "_SC_V6_LPBIG_OFFBIG"))
(constant (sc-2-c-bind "_SC_2_C_BIND"))
(constant (sc-2-c-dev "_SC_2_C_DEV"))
#-darwin (constant (sc-2-c-version "_SC_2_C_VERSION"))
(constant (sc-2-char-term "_SC_2_CHAR_TERM"))
(constant (sc-2-fort-dev "_SC_2_FORT_DEV"))
(constant (sc-2-fort-run "_SC_2_FORT_RUN"))
(constant (sc-2-localedef "_SC_2_LOCALEDEF"))
(constant (sc-2-pbs "_SC_2_PBS"))
(constant (sc-2-pbs-accounting "_SC_2_PBS_ACCOUNTING"))
(constant (sc-2-pbs-checkpoint "_SC_2_PBS_CHECKPOINT"))
(constant (sc-2-pbs-locate "_SC_2_PBS_LOCATE"))
(constant (sc-2-pbs-message "_SC_2_PBS_MESSAGE"))
(constant (sc-2-pbs-track "_SC_2_PBS_TRACK"))
(constant (sc-2-sw-dev "_SC_2_SW_DEV"))
(constant (sc-2-upe "_SC_2_UPE"))
(constant (sc-2-version "_SC_2_VERSION"))
#-darwin (constant (sc-regex-version "_SC_REGEX_VERSION"))
(constant (sc-page-size "_SC_PAGE_SIZE"))
(constant (sc-pagesize "_SC_PAGESIZE"))
(constant (sc-thread-destructor-iterations "_SC_THREAD_DESTRUCTOR_ITERATIONS"))
(constant (sc-thread-keys-max "_SC_THREAD_KEYS_MAX"))
(constant (sc-thread-stack-min "_SC_THREAD_STACK_MIN"))
(constant (sc-thread-threads-max "_SC_THREAD_THREADS_MAX"))
(constant (sc-re-dup-max "_SC_RE_DUP_MAX"))
(constant (sc-rtsig-max "_SC_RTSIG_MAX"))
(constant (sc-sem-nsems-max "_SC_SEM_NSEMS_MAX"))
(constant (sc-sem-value-max "_SC_SEM_VALUE_MAX"))
(constant (sc-sigqueue-max "_SC_SIGQUEUE_MAX"))
(constant (sc-stream-max "_SC_STREAM_MAX"))
(constant (sc-symloop-max "_SC_SYMLOOP_MAX"))
(constant (sc-timer-max "_SC_TIMER_MAX"))
(constant (sc-tty-name-max "_SC_TTY_NAME_MAX"))
(constant (sc-tzname-max "_SC_TZNAME_MAX"))
(constant (sc-xbs5-ilp32-off32 "_SC_XBS5_ILP32_OFF32"))
(constant (sc-xbs5-ilp32-offbig "_SC_XBS5_ILP32_OFFBIG"))
(constant (sc-xbs5-lp64-off64 "_SC_XBS5_LP64_OFF64"))
(constant (sc-xbs5-lpbig-offbig "_SC_XBS5_LPBIG_OFFBIG"))
(constant (sc-xopen-crypt "_SC_XOPEN_CRYPT"))
(constant (sc-xopen-enh-i18n "_SC_XOPEN_ENH_I18N"))
(constant (sc-xopen-legacy "_SC_XOPEN_LEGACY"))
(constant (sc-xopen-realtime "_SC_XOPEN_REALTIME"))
(constant (sc-xopen-realtime-threads "_SC_XOPEN_REALTIME_THREADS"))
(constant (sc-xopen-shm "_SC_XOPEN_SHM"))
(constant (sc-xopen-unix "_SC_XOPEN_UNIX"))
(constant (sc-xopen-version "_SC_XOPEN_VERSION"))
(constant (sc-xopen-xcu-version "_SC_XOPEN_XCU_VERSION"))

;;;; from sys/uio.h

(cstruct iovec "struct iovec"
  (base "iov_base" :type :pointer)
  (len  "iov_len"  :type size))

(constant (iov-max #+bsd "IOV_MAX" #+linux "UIO_MAXIOV"))

;;;; from time.h

(ctype suseconds "suseconds_t")

#-darwin
(progn
  (ctype clockid "clockid_t")
  (ctype timer "timer_t")
  (constant (clock-monotonic "CLOCK_MONOTONIC"))
  (constant (clock-realtime "CLOCK_REALTIME"))
  (constant (clock-process-cputime-id "CLOCK_PROCESS_CPUTIME_ID"))
  (constant (clock-thread-cputime-id "CLOCK_THREAD_CPUTIME_ID"))
  (constant (timer-abstime "TIMER_ABSTIME")))

(cstruct timespec "struct timespec"
  "UNIX time specification in seconds and nanoseconds."
  (sec  "tv_sec"  :type time)
  (nsec "tv_nsec" :type :long))

#-darwin
(cstruct itimerspec "struct itimerspec"
  "UNIX timer interval and initial expiration."
  (interval "it_interval" :type timespec)
  (value    "it_value"    :type timespec))

;;;; from sys/select.h

(cstruct timeval "struct timeval"
  "UNIX time specification in seconds and microseconds."
  (sec  "tv_sec"  :type time)
  (usec "tv_usec" :type suseconds))

;;;; from syslog.h

;;; options
(constant (log-cons "LOG_CONS"))
(constant (log-ndelay "LOG_NDELAY"))
(constant (log-perror "LOG_PERROR"))
(constant (log-pid "LOG_PID"))

;;; priority
(constantenum syslog-priorities
  ((:emerg "LOG_EMERG"))
  ((:alert "LOG_ALERT"))
  ((:crit "LOG_CRIT"))
  ((:err "LOG_ERR"))
  ((:warning "LOG_WARNING"))
  ((:notice "LOG_NOTICE"))
  ((:info "LOG_INFO"))
  ((:debug "LOG_DEBUG")))

;;; facilities
(constantenum syslog-facilities
  ((:auth "LOG_AUTH"))
  ((:authpriv "LOG_AUTHPRIV"))
  ((:cron "LOG_CRON"))
  ((:daemon "LOG_DAEMON"))
  ((:ftp "LOG_FTP"))
  ((:kern "LOG_KERN"))
  ((:lpr "LOG_LPR"))
  ((:mail "LOG_MAIL"))
  ((:news "LOG_NEWS"))
  ((:security "LOG_SECURITY") :optional t)       ; freebsd
  ((:syslog "LOG_SYSLOG"))
  ((:user "LOG_USER"))
  ((:uucp "LOG_UUCP"))
  ((:local0 "LOG_LOCAL0"))
  ((:local1 "LOG_LOCAL1"))
  ((:local2 "LOG_LOCAL2"))
  ((:local3 "LOG_LOCAL3"))
  ((:local4 "LOG_LOCAL4"))
  ((:local5 "LOG_LOCAL5"))
  ((:local6 "LOG_LOCAL6"))
  ((:local7 "LOG_LOCAL7")))

;;;; from sys/resource.h

(ctype rlim "rlim_t")
(ctype id "id_t")

(cstruct rlimit "struct rlimit"
  (cur "rlim_cur" :type rlim)
  (max "rlim_max" :type rlim))

(cstruct rusage "struct rusage"
  (utime    "ru_utime"    :type timeval)
  (stime    "ru_stime"    :type timeval)
  (maxrss   "ru_maxrss"   :type :long)
  (ixrss    "ru_ixrss"    :type :long)
  (idrss    "ru_idrss"    :type :long)
  (isrss    "ru_isrss"    :type :long)
  (minflt   "ru_minflt"   :type :long)
  (majflt   "ru_majflt"   :type :long)
  (nswap    "ru_nswap"    :type :long)
  (inblock  "ru_inblock"  :type :long)
  (oublock  "ru_oublock"  :type :long)
  (msgsnd   "ru_msgsnd"   :type :long)
  (msgrcv   "ru_msgrcv"   :type :long)
  (nsignals "ru_nsignals" :type :long)
  (nvcsw    "ru_nvcsw"    :type :long)
  (nivcsw   "ru_nivcsw"   :type :long))

(constant (prio-process "PRIO_PROCESS"))
(constant (prio-pgrp "PRIO_PGRP"))
(constant (prio-user "PRIO_USER"))
(constant (rlim-infinity "RLIM_INFINITY"))
(constant (rusage-self "RUSAGE_SELF"))
(constant (rusage-children "RUSAGE_CHILDREN"))
(constant (rlimit-as "RLIMIT_AS"))
(constant (rlimit-core "RLIMIT_CORE"))
(constant (rlimit-cpu "RLIMIT_CPU"))
(constant (rlimit-data "RLIMIT_DATA"))
(constant (rlimit-fsize "RLIMIT_FSIZE"))
(constant (rlimit-memlock "RLIMIT_MEMLOCK"))
(constant (rlimit-nofile "RLIMIT_NOFILE"))
(constant (rlimit-nproc "RLIMIT_NPROC"))
(constant (rlimit-rss "RLIMIT_RSS"))
(constant (rlimit-stack "RLIMIT_STACK"))

#+linux
(progn
  (constant (rlim-saved-max "RLIM_SAVED_MAX"))
  (constant (rlim-saved-cur "RLIM_SAVED_CUR"))
  (constant (rlimit-locks "RLIMIT_LOCKS"))
  (constant (rlimit-msgqueue "RLIMIT_MSGQUEUE"))
  (constant (rlimit-nlimits "RLIMIT_NLIMITS"))
  (constant (rlimit-nice "RLIMIT_NICE"))
  (constant (rlimit-rtprio "RLIMIT_RTPRIO"))
  (constant (rlimit-sigpending "RLIMIT_SIGPENDING")))

#+freebsd
(constant (rlimit-sbsize "RLIMIT_SBSIZE"))

;;;; from sys/utsname.h

(cstruct utsname "struct utsname"
  (sysname  "sysname"  :type :char)
  (nodename "nodename" :type :char)
  (release  "release"  :type :char)
  (version  "version"  :type :char)
  (machine  "machine"  :type :char))

;;;; from sys/statvfs.h

(ctype fsblkcnt "fsblkcnt_t")
(ctype fsfilcnt "fsfilcnt_t")

(cstruct statvfs "struct statvfs"
  (bsize   "f_bsize"   :type :unsigned-long)
  (frsize  "f_frsize"  :type :unsigned-long)
  (blocks  "f_blocks"  :type fsblkcnt)
  (bfree   "f_bfree"   :type fsblkcnt)
  (bavail  "f_bavail"  :type fsblkcnt)
  (files   "f_files"   :type fsfilcnt)
  (ffree   "f_ffree"   :type fsfilcnt)
  (favail  "f_favail"  :type fsfilcnt)
  (fsig    "f_fsid"    :type :unsigned-long)
  (flag    "f_flag"    :type :unsigned-long)
  (namemax "f_namemax" :type :unsigned-long))

(constant (st-rdonly "ST_RDONLY"))
(constant (st-nosuid "ST_NOSUID"))

#+linux
(progn
  (constant (st-nodev "ST_NODEV"))
  (constant (st-noexec "ST_NOEXEC"))
  (constant (st-synchronous "ST_SYNCHRONOUS"))
  (constant (st-mandlock "ST_MANDLOCK"))
  (constant (st-write "ST_WRITE"))
  (constant (st-append "ST_APPEND"))
  (constant (st-immutable "ST_IMMUTABLE"))
  (constant (st-noatime "ST_NOATIME"))
  (constant (st-nodiratime "ST_NODIRATIME")))

;;;; from unistd.h

(ctype useconds "useconds_t")

(constant (posix-vdisable "_POSIX_VDISABLE"))

;;;; from pwd.h

(cstruct passwd "struct passwd"
  (name   "pw_name"   :type :string)
  (passwd "pw_passwd" :type :string)
  (uid    "pw_uid"    :type uid)
  (gid    "pw_gid"    :type gid)
  (gecos  "pw_gecos"  :type :string)
  (dir    "pw_dir"    :type :string)
  (shell  "pw_shell"  :type :string))

;;;; from grp.h

;;; FIXME What about gr_mem?  Kinda the whole point?
(cstruct group "struct group"
  (name   "gr_name"   :type :string)
  (passwd "gr_passwd" :type :string)
  (gid    "gr_gid"    :type gid))

;;;; from dirent.h

;;; Apparently POSIX 1003.1-2001 (according to linux manpages) only
;;; requires d_name.  Sigh.  I guess we should assemble some decent
;;; wrapper functions.  No, struct members can't be optional at this
;;; point.
(cstruct dirent "struct dirent"
  ;; POSIX actually requires this to be d_ino
  (fileno "d_fileno" :type #-freebsd ino #+freebsd :uint32)
  (type   "d_type"   :type :uint8)
  (name   "d_name"   :type :uint8 :count :auto))

;;; filetypes set in d_type slot of struct dirent
(constant (dt-unknown "DT_UNKNOWN"))
(constant (dt-fifo "DT_FIFO"))
(constant (dt-chr "DT_CHR"))
(constant (dt-dir "DT_DIR"))
(constant (dt-blk "DT_BLK"))
(constant (dt-reg "DT_REG"))
(constant (dt-lnk "DT_LNK"))
(constant (dt-sock "DT_SOCK"))
(constant (dt-wht "DT_WHT"))

;;;; from ioctl.h

(cstruct winsize "struct winsize"
  (row "ws_row" :type :uint16)
  (col "ws_col" :type :uint16)
  (xpixel "ws_xpixel" :type :uint16)
  (ypixel "ws_ypixel" :type :uint16))

#+(or linux bsd)
(progn
  ;; FIXME: Others too probaly exist on BSD hosts as well.
  (constant (tiocgwinsz "TIOCGWINSZ"))
  (constant (tiocswinsz "TIOCSWINSZ"))
  (constant (tiocnotty "TIOCNOTTY")))

;;;; from termios.h

(cstruct termios "struct termios"
  (iflag "c_iflag" :type :uint32)
  (oflag "c_oflag" :type :uint32)
  (cflag "c_cflag" :type :uint32)
  (lflag "c_lflag" :type :uint32)
  (cc "c_cc" :type :uint8 :count :auto))

(constant (cflag-VINTR "VINTR"))
(constant (cflag-VQUIT "VQUIT"))
(constant (cflag-VERASE "VERASE"))
(constant (cflag-VKILL "VKILL"))
(constant (cflag-VEOF "VEOF"))
(constant (cflag-VTIME "VTIME"))
(constant (cflag-VMIN "VMIN"))
(constant (cflag-VSWTC "VSWTC"))
(constant (cflag-VSTART "VSTART"))
(constant (cflag-VSTOP "VSTOP"))
(constant (cflag-VDSUSP "VDSUSP"))
(constant (cflag-VSUSP "VSUSP"))
(constant (cflag-VEOL "VEOL"))
(constant (cflag-VREPRINT "VREPRINT"))
(constant (cflag-VDISCARD "VDISCARD"))
(constant (cflag-VWERASE "VWERASE"))
(constant (cflag-VLNEXT "VLNEXT"))
(constant (cflag-VEOL2 "VEOL2"))
(constant (cflag-VSTATUS "VSTATUS"))

(constant (TCSANOW "TCSANOW"))
(constant (TCSADRAIN "TCSADRAIN"))
(constant (TCSAFLUSH "TCSAFLUSH"))

(constant (tty-IGNBRK "IGNBRK"))
(constant (tty-BRKINT "BRKINT"))
(constant (tty-IGNPAR "IGNPAR"))
(constant (tty-PARMRK "PARMRK"))
(constant (tty-INPCK "INPCK"))
(constant (tty-ISTRIP "ISTRIP"))
(constant (tty-INLCR "INLCR"))
(constant (tty-IGNCR "IGNCR"))
(constant (tty-ICRNL "ICRNL"))
(constant (tty-IUCLC "IUCLC"))
(constant (tty-IXON "IXON"))
(constant (tty-IXANY "IXANY"))
(constant (tty-IXOFF "IXOFF"))
(constant (tty-IMAXBEL "IMAXBEL"))
(constant (tty-IUTF8 "IUTF8"))

(constant (tty-OPOST "OPOST"))
(constant (tty-OLCUC "OLCUC"))
(constant (tty-ONLCR "ONLCR"))
(constant (tty-OCRNL "OCRNL"))
(constant (tty-ONOCR "ONOCR"))
(constant (tty-ONLRET "ONLRET"))
(constant (tty-OFILL "OFILL"))
(constant (tty-OFDEL "OFDEL"))


(constant (tty-ISIG "ISIG"))
(constant (tty-ICANON "ICANON"))
(constant (tty-ECHO "ECHO"))
(constant (tty-ECHOE "ECHOE"))
(constant (tty-ECHOK "ECHOK"))
(constant (tty-ECHONL "ECHONL"))
(constant (tty-NOFLSH "NOFLSH"))
(constant (tty-TOSTOP "TOSTOP"))



;;;; Linux ioctls from sys/ioctl.h

#+linux
(progn
  (constant (siocgifname "SIOCGIFNAME"))
  (constant (siocsiflink "SIOCSIFLINK"))
  (constant (siocgifconf "SIOCGIFCONF"))
  (constant (siocgifflags "SIOCGIFFLAGS"))
  (constant (siocsifflags "SIOCSIFFLAGS"))
  (constant (siocgifaddr "SIOCGIFADDR"))
  (constant (siocsifaddr "SIOCSIFADDR"))
  (constant (siocgifdstaddr "SIOCGIFDSTADDR"))
  (constant (siocsifdstaddr "SIOCSIFDSTADDR"))
  (constant (siocgifbrdaddr "SIOCGIFBRDADDR"))
  (constant (siocsifbrdaddr "SIOCSIFBRDADDR"))
  (constant (siocgifnetmask "SIOCGIFNETMASK"))
  (constant (siocsifnetmask "SIOCSIFNETMASK"))
  (constant (siocgifmetric "SIOCGIFMETRIC"))
  (constant (siocsifmetric "SIOCSIFMETRIC"))
  (constant (siocgifmem "SIOCGIFMEM"))
  (constant (siocsifmem "SIOCSIFMEM"))
  (constant (siocgifmtu "SIOCGIFMTU"))
  (constant (siocsifmtu "SIOCSIFMTU"))
  (constant (siocsifname "SIOCSIFNAME"))
  (constant (siocsifhwaddr "SIOCSIFHWADDR"))
  (constant (siocgifencap "SIOCGIFENCAP"))
  (constant (siocsifencap "SIOCSIFENCAP"))
  (constant (siocgifhwaddr "SIOCGIFHWADDR"))
  (constant (siocgifslave "SIOCGIFSLAVE"))
  (constant (siocsifslave "SIOCSIFSLAVE"))
  (constant (siocaddmulti "SIOCADDMULTI"))
  (constant (siocdelmulti "SIOCDELMULTI"))
  (constant (siocgifindex "SIOCGIFINDEX"))
  (constant (siogifindex "SIOGIFINDEX"))
  (constant (siocsifpflags "SIOCSIFPFLAGS"))
  (constant (siocgifpflags "SIOCGIFPFLAGS"))
  (constant (siocdifaddr "SIOCDIFADDR"))
  (constant (siocsifhwbroadcast "SIOCSIFHWBROADCAST"))
  (constant (siocgifcount "SIOCGIFCOUNT"))

  (constant (siocgifbr "SIOCGIFBR"))
  (constant (siocsifbr "SIOCSIFBR"))

  (constant (siocgiftxqlen "SIOCGIFTXQLEN"))
  (constant (siocsiftxqlen "SIOCSIFTXQLEN"))

  (constant (siocdarp "SIOCDARP"))
  (constant (siocgarp "SIOCGARP"))
  (constant (siocsarp "SIOCSARP"))

  (constant (siocdrarp "SIOCDRARP"))
  (constant (siocgrarp "SIOCGRARP"))
  (constant (siocsrarp "SIOCSRARP"))

  (constant (siocgifmap "SIOCGIFMAP"))
  (constant (siocsifmap "SIOCSIFMAP"))

  (constant (siocadddlci "SIOCADDDLCI"))
  (constant (siocdeldlci "SIOCDELDLCI"))

  (constant (siocdevprivate "SIOCDEVPRIVATE"))

  (constant (siocprotoprivate "SIOCPROTOPRIVATE"))

  (constant (tcgets "TCGETS"))
  (constant (tcsets "TCSETS"))
  (constant (tcsetsw "TCSETSW"))
  (constant (tcsetsf "TCSETSF"))
  (constant (tcgeta "TCGETA"))
  (constant (tcseta "TCSETA"))
  (constant (tcsetaw "TCSETAW"))
  (constant (tcsetaf "TCSETAF"))
  (constant (tcsbrk "TCSBRK"))
  (constant (tcxonc "TCXONC"))
  (constant (tcflsh "TCFLSH"))
  (constant (tiocexcl "TIOCEXCL"))
  (constant (tiocnxcl "TIOCNXCL"))
  (constant (tiocsctty "TIOCSCTTY"))
  (constant (tiocgpgrp "TIOCGPGRP"))
  (constant (tiocspgrp "TIOCSPGRP"))
  (constant (tiocoutq "TIOCOUTQ"))
  (constant (tiocsti "TIOCSTI"))
  (constant (tiocmget "TIOCMGET"))
  (constant (tiocmbis "TIOCMBIS"))
  (constant (tiocmbic "TIOCMBIC"))
  (constant (tiocmset "TIOCMSET"))
  (constant (tiocgsoftcar "TIOCGSOFTCAR"))
  (constant (tiocssoftcar "TIOCSSOFTCAR"))
  (constant (fionread "FIONREAD"))
  (constant (tiocinq "TIOCINQ"))
  (constant (tioclinux "TIOCLINUX"))
  (constant (tioccons "TIOCCONS"))
  (constant (tiocgserial "TIOCGSERIAL"))
  (constant (tiocsserial "TIOCSSERIAL"))
  (constant (tiocpkt "TIOCPKT"))
  (constant (fionbio "FIONBIO"))
  (constant (tiocsetd "TIOCSETD"))
  (constant (tiocgetd "TIOCGETD"))
  (constant (tcsbrkp "TCSBRKP"))
  (constant (tiocsbrk "TIOCSBRK"))
  (constant (tioccbrk "TIOCCBRK"))
  (constant (tiocgsid "TIOCGSID"))
  (constant (tiocgptn "TIOCGPTN"))
  (constant (tiocsptlck "TIOCSPTLCK"))

  (constant (fionclex "FIONCLEX"))
  (constant (fioclex "FIOCLEX"))
  (constant (fioasync "FIOASYNC"))
  (constant (tiocserconfig "TIOCSERCONFIG"))
  (constant (tiocsergwild "TIOCSERGWILD"))
  (constant (tiocserswild "TIOCSERSWILD"))
  (constant (tiocglcktrmios "TIOCGLCKTRMIOS"))
  (constant (tiocslcktrmios "TIOCSLCKTRMIOS"))
  (constant (tiocsergstruct "TIOCSERGSTRUCT"))
  (constant (tiocsergetlsr "TIOCSERGETLSR"))
  (constant (tiocsergetmulti "TIOCSERGETMULTI"))
  (constant (tiocsersetmulti "TIOCSERSETMULTI"))

  (constant (tiocmiwait "TIOCMIWAIT"))
  (constant (tiocgicount "TIOCGICOUNT"))
  (constant (tiocghayesesp "TIOCGHAYESESP"))
  (constant (tiocshayesesp "TIOCSHAYESESP"))
  (constant (fioqsize "FIOQSIZE")))

;;;; from wait.h

(constant (wnohang "WNOHANG"))
(constant (wuntraced "WUNTRACED"))

;;;; from sys/syscall.h

#+linux
(constant (sys-gettid "SYS_gettid"))
