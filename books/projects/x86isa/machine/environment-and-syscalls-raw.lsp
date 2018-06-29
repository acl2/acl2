; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Soumava Ghosh       <soumava@cs.utexas.edu>

(in-package "X86ISA")

(CCL::open-shared-library *shared-syscall-dir-path*)

;; ======================================================================

;; Environment-Related Definitons:

(defun env-read$notinline (x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::env-read$notinline
      (X86ISA::env-read-logic x86)))
  (er hard! 'env-read
      "Ill-advised attempt to call env-read during top-level ~
       evaluation."))

(defun env-write$notinline (env x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::env-write$notinline
      (X86ISA::env-write-logic env x86)))
  (er hard! 'env-write
      "Ill-advised attempt to call env-write during top-level ~
       evaluation."))

(defun read-x86-file-des$notinline (id x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::read-x86-file-des$notinline
      (X86ISA::read-x86-file-des-logic id x86)))
  (er hard! 'read-x86-file-des
      "Ill-advised attempt to call read-x86-file-des during top-level ~
       evaluation."))

(defun read-x86-file-contents$notinline (name x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::read-x86-file-contents$notinline
      (X86ISA::read-x86-file-contents-logic name x86)))
  (er hard! 'read-x86-file-contents
      "Ill-advised attempt to call read-x86-file-contents during top-level ~
       evaluation."))

(defun write-x86-file-des$notinline (fd fd-field x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::write-x86-file-des$notinline
      (X86ISA::write-x86-file-des-logic fd fd-field x86)))
  (er hard! 'write-x86-file-des
      "Ill-advised attempt to call write-x86-file-des during top-level ~
       evaluation."))

(defun delete-x86-file-des$notinline (fd x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::delete-x86-file-des$notinline
      (X86ISA::delete-x86-file-des-logic fd x86)))
  (er hard! 'delete-x86-file-des
      "Ill-advised attempt to call delete-x86-file-des during top-level ~
       evaluation."))

(defun write-x86-file-contents$notinline (name contents-field x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::write-x86-file-contents$notinline
      (X86ISA::write-x86-file-contents-logic name contents-field x86)))
  (er hard! 'write-x86-file-contents
      "Ill-advised attempt to call write-x86-file-contents during top-level ~
       evaluation."))

(defun delete-x86-file-contents$notinline (name x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::delete-x86-file-contents$notinline
      (X86ISA::delete-x86-file-contents-logic name x86)))
  (er hard! 'delete-x86-file-contents
      "Ill-advised attempt to call delete-x86-file-contents during top-level ~
       evaluation."))

(defun pop-x86-oracle$notinline (x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global
		    'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::pop-x86-oracle$notinline
      (X86ISA::pop-x86-oracle-logic x86)))
  (er hard! 'pop-x86-oracle
      "Ill-advised attempt to call pop-x86-oracle during top-level ~
       evaluation."))

;; ======================================================================

;; Syscall Definitions:

(defun syscall-read$notinline (fd *buf count x86)
  ;; ssize_t read(int fd, void *buf, size_t count);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd *buf count x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-read$notinline
      (X86ISA::syscall-read-logic fd *buf count x86)))
  (multiple-value-bind
      (_str ptr)
      ;; Note that ptr stands in for *buf.
      (ccl::make-heap-ivector count '(unsigned-byte 8))
    (declare (ignorable _str))
    (b* ( ;; (- (cw "syscall-read$notinline: Entering.~%"))
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (fd (n32 fd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_read-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int fd
				  :address ptr
				  :unsigned-int count
				  :signed-int))
	 ;; (- (cw "syscall-read$notinline: Ret: ~x0~%" ret))
	 ;; (- (cw "syscall-read$notinline: Fd: ~x0~%" fd))
	 ;; (- (cw "syscall-read$notinline: Count: ~x0~%" count))
	 (retStr (ccl::%str-from-ptr ptr ret))
	 ;; (- (cw "syscall-read$notinline: RetStr: ~x0~%" retStr))
	 (retBytes (X86ISA::string-to-bytes retStr))
	 ;; (- (cw "syscall-read$notinline: RetBytes: ~x0~%" retBytes))
	 ((mv flg x86)
	  (if (and (<= (- #.X86ISA::*2^47*) *buf)
		   (<= (+ (len retBytes) *buf)
		       #.X86ISA::*2^47*))
	      (b* (((mv flg x86)
		    (X86ISA::write-bytes-to-memory
		     *buf retBytes X86ISA::*the-live-x86*)))
		  (mv flg x86))
	    (mv t x86)))
	 (- (if flg
		(cw "syscall-read$notinline: Execution Error: Insufficient memory.~%")
	      nil))
	 (ret (if flg -1 ret))
	 ;; (- (cw "syscall-read$notinline: Exiting.~%"))
	 )
	(ccl::dispose-heap-ivector ptr)
	(mv ret x86))))


(defun syscall-write$notinline (fd *buf count x86)
  ;; ssize_t write(int fd, const void *buf, size_t count);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd *buf count x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-write$notinline
      (X86ISA::syscall-write-logic fd *buf count x86)))
  (b* ( ;; (- (cw "syscall-write$notinline: Entering.~%"))
       ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
       ;; apparently does and CCL doesn't.
       (fd (n32 fd))
       ((mv flg *buf-string x86)
	(X86ISA::read-string-from-memory *buf count X86ISA::*the-live-x86*))
       ;; (- (cw "syscall-write$notinline: *buf-string: ~x0~%" *buf-string))
       (ptr  (ccl::make-cstring *buf-string))
       (ret  (ccl::external-call "syscall"
				 :unsigned-int (X86ISA::sys_write-raw-idx X86ISA::*the-live-x86*)
				 :unsigned-int fd
				 :address ptr
				 :unsigned-int count
				 :unsigned-int))
       ;; (- (cw "syscall-write$notinline: Ret: ~x0~%" ret))
       ;; (- (cw "syscall-write$notinline: Fd: ~x0~%" fd))
       ;; (- (cw "syscall-write$notinline: Count: ~x0~%" count))
       ;; (- (cw "syscall-write$notinline: Exiting.~%"))
       )
      (ccl::dispose-heap-ivector ptr)
      (mv ret x86)))

(defun syscall-open$notinline (pathname oflags mode x86)
  ;; int open(const char *pathname, int flags);
  ;; int open(const char *pathname, int flags, mode_t mode);
  ;; int creat(const char *pathname, mode_t mode);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable pathname oflags mode x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-open$notinline
      (X86ISA::syscall-open-logic pathname oflags mode x86)))
  (b* ( ;; (- (cw "syscall-open$notinline: Entering.~%"))
       (ptr (ccl::make-cstring pathname))
       (ret (ccl::external-call "syscall"
				:unsigned-int (X86ISA::sys_open-raw-idx X86ISA::*the-live-x86*)
				:address ptr

				:unsigned-int oflags
				:unsigned-int mode
				:signed-int))
       ;; (- (cw "syscall-open$notinline: Ret: ~x0~%" ret))
       ;; (- (cw "syscall-open$notinline: Pathname: ~x0~%" pathname))
       ;; (- (cw "syscall-open$notinline: Oflags: ~x0~%" oflags))
       ;; (- (cw "syscall-open$notinline: Mode: ~x0~%" mode))
       ;; (- (cw "syscall-open$notinline: Exiting.~%"))
       )
      (mv ret x86)))


(defun syscall-close$notinline (fd x86)
  ;; int close(int fd);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-close$notinline
      (X86ISA::syscall-close-logic fd x86)))
  (b* ( ;; (- (cw "syscall-close$notinline: Entering.~%"))
       ;; ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
       ;; ;; apparently does and CCL doesn't.
       ;; (fd (n32 fd))
       ;; (ret  (ccl::external-call "syscall"
       ;;                           :unsigned-int #.X86ISA::*SYS_close-raw*
       ;;                           :unsigned-int fd
       ;;                           :signed-int))
       ;; (- (cw "syscall-close$notinline: Ret: ~x0~%" ret))
       ;; (- (cw "syscall-close$notinline: Fd: ~x0~%" fd))
       ;; (- (cw "syscall-close$notinline: Exiting.~%"))
       )
      (mv ret x86)))

(defun syscall-lseek$notinline (fd offset whence x86)
  ;; off_t lseek(int fd, off_t offset, int whence);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd offset whence x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-lseek$notinline
      (X86ISA::syscall-lseek-logic fd offset whence x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (fd (n32 fd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_lseek-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int fd
				  :signed-int offset
				  :signed-int whence
				  :signed-int)))
    (mv ret x86)))

(defun syscall-fadvise64$notinline (fd offset len advice x86)
  ;; int fadvise64(int fd, off_t offset, off_t len, int advice);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd offset len advice x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-fadvise64$notinline
      (X86ISA::syscall-fadvise64-logic fd offset len advice x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (fd (n32 fd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_fadvise64-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int fd
				  :signed-int offset
				  :signed-int len
				  :signed-int advice
				  :signed-int)))
    (mv ret x86)))

(defun syscall-link$notinline (oldpath newpath x86)
  ;; int link(const char* oldpath, const char* newpath);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable oldpath newpath x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-link$notinline
      (X86ISA::syscall-link-logic oldpath newpath x86)))
  (let* ((oldptr (ccl::make-cstring oldpath))
	 (newptr (ccl::make-cstring newpath))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_link-raw-idx X86ISA::*the-live-x86*)
				  :address oldptr
				  :address newptr
				  :signed-int)))
    (mv ret x86)))

(defun syscall-unlink$notinline (path x86)
  ;; int unlink(const char* path);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable path x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-unlink$notinline
      (X86ISA::syscall-unlink-logic path x86)))
  (let* ((ptr (ccl::make-cstring path))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_unlink-raw-idx X86ISA::*the-live-x86*)
				  :address ptr
				  :signed-int)))
    (mv ret x86)))


(defun syscall-dup$notinline (oldfd x86)
  ;; int dup(int oldfd);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable oldfd x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-dup$notinline
      (X86ISA::syscall-dup-logic oldfd x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate oldfd because the OS
	 ;; apparently does and CCL doesn't.
	 (oldfd (n32 oldfd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_dup-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int oldfd
				  :signed-int)))
    (mv ret x86)))

(defun syscall-dup2$notinline (oldfd newfd x86)
  ;; int dup2(int oldfd, int newfd);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable oldfd newfd x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-dup2$notinline
      (X86ISA::syscall-dup2-logic oldfd newfd x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (oldfd (n32 oldfd))
	 (newfd (n32 newfd))

	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_dup2-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int oldfd
				  :unsigned-int newfd
				  :signed-int)))
    (mv ret x86)))

(defun syscall-dup3$notinline (oldfd newfd flags x86)
  ;; int dup3(int oldfd, int newfd, int flags);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable oldfd newfd flags x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-dup3$notinline
      (X86ISA::syscall-dup3-logic oldfd newfd flags x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (oldfd (n32 oldfd))
	 (newfd (n32 newfd))

	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_dup3-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int oldfd
				  :unsigned-int newfd
				  :signed-int flags
				  :signed-int)))
    (mv ret x86)))

(defun syscall-fcntl$notinline (fd cmd arg x86)
  ;; int fcntl(int fd, int cmd, long arg);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd cmd arg x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-fcntl$notinline
      (X86ISA::syscall-fcntl-logic fd cmd arg x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (fd (n32 fd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_fcntl-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int fd
				  :unsigned-int cmd
				  :unsigned-long arg
				  :signed-int)))
    (mv ret x86)))

(defun syscall-truncate$notinline (path len x86)
  ;; int truncate(const char* path, long len);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable path len x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-truncate$notinline
      (X86ISA::syscall-truncate-logic path len x86)))
  (let* ((ptr (ccl::make-cstring path))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_truncate-raw-idx X86ISA::*the-live-x86*)
				  :address ptr
				  :unsigned-long len
				  :signed-int)))
    (mv ret x86)))

(defun syscall-ftruncate$notinline (fd len x86)
  ;; int ftruncate(int fd, unsigned long len);
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd len x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg
				 ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-ftruncate$notinline
      (X86ISA::syscall-ftruncate-logic fd len x86)))
  (let* (
	 ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
	 ;; apparently does and CCL doesn't.
	 (fd (n32 fd))
	 (ret (ccl::external-call "syscall"
				  :unsigned-int (X86ISA::sys_ftruncate-raw-idx X86ISA::*the-live-x86*)
				  :unsigned-int fd
				  :unsigned-long len
				  :signed-int)))
    (mv ret x86)))

;; A helper function for the *stat syscalls:

(defun get-bytelist-from-ptr (ptr index size)
  ;; This function is used to retrieve a list of unsigned bytes from
  ;; the location pointed to by the pointer ptr upto a maximum of
  ;; size, with index being the current index.
  (declare (xargs :mode :program
		  :guard (and (natp index)
			      (natp size)
			      (<= index size))))
  (if (equal index size)
      nil
    (b* ((byte (ccl::%get-unsigned-byte ptr index)))
	(append (cons byte nil)
		(get-bytelist-from-ptr ptr
				       (+ index 1)
				       size)))))


(defun syscall-stat$notinline (path buf x86)
  ;; int stat(const char* path, struct stat* buf)
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable path buf x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-stat$notinline
      (X86ISA::syscall-stat-logic path buf x86)))
  (b* ((size (ccl::external-call "get_struct_size"
				 :unsigned-int #.X86ISA::*STRUCT_STAT*
				 :signed-int))
       (- (cw "syscall-stat$notinline: size: ~x0~%" size))
       (pathPtr (ccl::make-cstring path))
       ((mv ?_statbuf ptr) (ccl::make-heap-ivector size '(unsigned-byte 8)))
       (- (cw "syscall-stat$notinline: path: ~x0~%" path))
       (ret (ccl::external-call "syscall"
				:unsigned-int (X86ISA::sys_stat-raw-idx X86ISA::*the-live-x86*)
				:address pathPtr
				:address ptr
				:signed-int))
       (- (cw "syscall-stat$notinline: ret: ~x0~%" ret)))
      (if (equal 0 ret)
	  (b* ((byteList (get-bytelist-from-ptr ptr 0 size))
	       (- (cw "syscall-stat$notinline: byteList: ~x0~%" byteList))
	       ((mv flg x86)
		(if (and (<= (- #.X86ISA::*2^47*) buf)
			 (<= (+ (len byteList) buf)
			     #.X86ISA::*2^47*))
		    (b* (((mv flg x86)
			  (X86ISA::write-bytes-to-memory
			   buf byteList X86ISA::*the-live-x86*))
			 (- (cw "syscall-stat$notinline: writing bytelist to: ~x0~%" buf)))
			(mv flg x86))
		  (mv t x86)))
	       (- (if flg
		      (cw "syscall-stat$notinline: Execution Error: Insufficient memory.~%")
		    nil))
	       (ret (if flg -1 ret)))
	      ;; (- (cw "syscall-stat$notinline: Exiting.~%"))
	      (ccl::dispose-heap-ivector ptr)
	      (mv ret x86)))
      (ccl::dispose-heap-ivector ptr)
      (mv ret x86)))


(defun syscall-fstat$notinline (fd buf x86)
  ;; int fstat(int fd, struct stat* buf)
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable fd buf x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-fstat$notinline
      (X86ISA::syscall-fstat-logic fd buf x86)))
  (b* (
       ;; TO-DO@Shilpi: Bah! Have to truncate fd because the OS
       ;; apparently does and CCL doesn't.
       (fd (n32 fd))
       (size (ccl::external-call "get_struct_size"
				 :unsigned-int #.X86ISA::*STRUCT_STAT*
				 :signed-int))
       (- (cw "syscall-fstat$notinline: size: ~x0~%" size))
       ((mv ?_statbuf ptr) (ccl::make-heap-ivector size '(unsigned-byte 8)))
       (- (cw "syscall-fstat$notinline: fd: ~x0~%" fd))
       (ret (ccl::external-call "syscall"
				:unsigned-int (X86ISA::sys_fstat-raw-idx X86ISA::*the-live-x86*)
				:unsigned-int fd
				:address ptr
				:signed-int))
       (- (cw "syscall-fstat$notinline: ret: ~x0~%" ret)))
      (if (equal 0 ret)
	  (b* ((byteList (get-bytelist-from-ptr ptr 0 size))
	       (- (cw "syscall-fstat$notinline: byteList: ~x0~%" byteList))
	       ((mv flg x86)
		(if (and (<= (- #.X86ISA::*2^47*) buf)
			 (<= (+ (len byteList) buf)
			     #.X86ISA::*2^47*))
		    (b* (((mv flg x86)
			  (X86ISA::write-bytes-to-memory
			   buf byteList X86ISA::*the-live-x86*))
			 (- (cw "syscall-stat$notinline: writing bytelist to: ~x0~%" buf)))
			(mv flg x86))
		  (mv t x86)))
	       (- (if flg
		      (cw "syscall-fstat$notinline: Execution Error: Insufficient memory.~%")
		    nil))
	       (ret (if flg -1 ret)))
	      ;; (- (cw "syscall-fstat$notinline: Exiting.~%"))
	      (ccl::dispose-heap-ivector ptr)
	      (mv ret x86)))
      (ccl::dispose-heap-ivector ptr)
      (mv ret x86)))

(defun syscall-lstat$notinline (path buf x86)
  ;; int lstat(const char* path, struct stat* buf)
  (declare (xargs :mode :program :stobjs x86)
	   (ignorable path buf x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
		   t)
	    (equal (f-get-global 'in-verify-flg ACL2::*the-live-state*)
		   t))
    (return-from X86ISA::syscall-lstat$notinline
      (X86ISA::syscall-lstat-logic path buf x86)))
  (b* ((size (ccl::external-call "get_struct_size"
				 :unsigned-int #.X86ISA::*STRUCT_STAT*
				 :signed-int))
       (- (cw "syscall-lstat$notinline: size: ~x0~%" size))
       (pathPtr (ccl::make-cstring path))
       ((mv ?_statbuf ptr) (ccl::make-heap-ivector size '(unsigned-byte 8)))
       (- (cw "syscall-lstat$notinline: path: ~x0~%" path))
       (ret (ccl::external-call "syscall"
				:unsigned-int (X86ISA::sys_lstat-raw-idx X86ISA::*the-live-x86*)
				:address pathPtr
				:address ptr
				:signed-int))
       (- (cw "syscall-lstat$notinline: ret: ~x0~%" ret)))
      (if (equal 0 ret)
	  (b* ((byteList (get-bytelist-from-ptr ptr 0 size))
	       (- (cw "syscall-lstat$notinline: byteList: ~x0~%" byteList))
	       ((mv flg x86)
		(if (and (<= (- #.X86ISA::*2^47*) buf)
			 (<= (+ (len byteList) buf)
			     #.X86ISA::*2^47*))
		    (b* (((mv flg x86)
			  (X86ISA::write-bytes-to-memory
			   buf byteList X86ISA::*the-live-x86*))
			 (- (cw "syscall-stat$notinline: writing bytelist to: ~x0~%" buf)))
			(mv flg x86))
		  (mv t x86)))
	       (- (if flg
		      (cw "syscall-lstat$notinline: Execution Error: Insufficient memory.~%")
		    nil))
	       (ret (if flg -1 ret)))
	      ;; (- (cw "syscall-lstat$notinline: Exiting.~%"))
	      (ccl::dispose-heap-ivector ptr)
	      (mv ret x86)))
      (ccl::dispose-heap-ivector ptr)
      (mv ret x86)))

;; ======================================================================
