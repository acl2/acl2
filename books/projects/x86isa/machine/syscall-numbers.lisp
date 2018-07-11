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

(in-package "X86ISA")

(include-book "abstract-state")

;; ======================================================================

;; For Linux systems: See /usr/include/x86_64-linux-gnu/asm/unistd_64.h
;; For Darwin systems: See /usr/include/sys/syscall.h
;; For FreeBSD systems: See sys/kern/syscalls.master

(defsection syscall-numbers
  :parents (syscalls)
  :short "OS-specific system call numbers"

  :long "<p>System call numbers differ among different operating
  systems.  For example, on Linux machines, the read syscall number is
  @('0') but on Darwin machines, it is @('3').  The x86 model
  currently supports syscall numbers for Linux and Darwin operating
  systems only.</p>

<p>For the x86isa model, we define the syscall numbers based on the
contents of the @('os-info') field of the x86 state. Currently
supported values of this field are @(':linux') and @(':darwin'), with
@(':linux') being the default value. Note that the field @('os-info')
is meaningful only in the @(see app-view).</p>"

  )

(local (xdoc::set-default-parents syscall-numbers))

;; ======================================================================

;; Definitions of syscall numbers in logic mode:

(define sys_read-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  0)
         ((equal os :darwin) #x2000003)
         ((equal os :freebsd) 3)
         (t -1)))
    nil))

(define sys_write-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  1)
         ((equal os :darwin) #x2000004)
         ((equal os :freebsd) 4)
         (t -1)))
    nil))

(define sys_open-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  2)
         ((equal os :darwin) #x2000005)
         ((equal os :freebsd) 5)
         (t -1)))
    nil))

(define sys_close-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  3)
         ((equal os :darwin) #x2000006)
         ((equal os :freebsd) 6)
         (t -1)))
    nil))

(define sys_stat-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  4)
         ((equal os :darwin) #x20000BC)
         (t -1)))
    nil))

(define sys_fstat-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  5)
         ((equal os :darwin) #x20000BD)
         (t -1)))
    nil))

(define sys_lstat-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  6)
         ((equal os :darwin) #x20000BE)
         (t -1)))
    nil))

(define sys_lseek-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  8)
         ((equal os :darwin) #x20000C7)
         (t -1)))
    nil))

(define sys_dup-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  32)
         ((equal os :darwin) #x200001B)
         (t -1)))
    nil))

(define sys_dup2-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  33)
         ((equal os :darwin) #x200005A)
         (t -1)))
    nil))

(define sys_fcntl-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  72)
         ((equal os :darwin) #x200005C)
         (t -1)))
    nil))

(define sys_truncate-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  76)
         ((equal os :darwin) #x20000C8)
         (t -1)))
    nil))

(define sys_ftruncate-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  77)
         ((equal os :darwin) #x20000C9)
         (t -1)))
    nil))

(define sys_link-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  86)
         ((equal os :darwin) #x2000009)
         (t -1)))
    nil))

(define sys_unlink-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  87)
         ((equal os :darwin) #x200000A)
         (t -1)))
    nil))

(define sys_fadvise64-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  221)
         ;; Not supported on Darwin.
         (t -1)))
    nil))

(define sys_dup3-idx ((x86))
  :enabled t
  (if (app-view x86)
      (let ((os (os-info x86)))
        (cond
         ((equal os :linux)  292)
         ;; Not supported on Darwin.
         (t -1)))
    nil))

;; ======================================================================

;; Definitions of syscall numbers in raw Lisp (because CCL uses these
;; numbers for its FFI):

(define sys_read-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  0)
     ((equal os :darwin) 3)
     (t -1))))

(define sys_write-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  1)
     ((equal os :darwin) 4)
     (t -1))))

(define sys_open-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  2)
     ((equal os :darwin) 5)
     (t -1))))

(define sys_close-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  3)
     ((equal os :darwin) 6)
     (t -1))))

(define sys_stat-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  4)
     ((equal os :darwin) #xBC)
     (t -1))))

(define sys_fstat-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  5)
     ((equal os :darwin) #xBD)
     (t -1))))

(define sys_lstat-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  6)
     ((equal os :darwin) #xBE)
     (t -1))))

(define sys_lseek-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  8)
     ((equal os :darwin) #xC7)
     (t -1))))

(define sys_dup-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  32)
     ((equal os :darwin) #x1B)
     (t -1))))

(define sys_dup2-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  33)
     ((equal os :darwin) #x5A)
     (t -1))))

(define sys_fcntl-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  72)
     ((equal os :darwin) #x5C)
     (t -1))))

(define sys_truncate-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  76)
     ((equal os :darwin) #xC8)
     (t -1))))

(define sys_ftruncate-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  77)
     ((equal os :darwin) #xC9)
     (t -1))))

(define sys_link-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  86)
     ((equal os :darwin) #x9)
     (t -1))))

(define sys_unlink-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  87)
     ((equal os :darwin) #xA)
     (t -1))))

(define sys_fadvise64-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  221)
     ;; Not supported on Darwin.
     (t -1))))

(define sys_dup3-raw-idx ((x86))
  :enabled t
  (let ((os (os-info x86)))
    (cond
     ((equal os :linux)  292)
     ;; Not suppported on Darwin.
     (t -1))))

;; For raw functions requesting the size of a structure
(defconst       *STRUCT_STAT*        1)

;; ======================================================================
