; cert.pl build system
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; NOTE: This file is not part of the standard ACL2 books build process; it is
; part of an experimental build system.  The ACL2 developers do not maintain
; this file.

(in-package "ACL2")

(mv-let (channel state)
  (open-output-channel "Makefile-features" :character state)
  (if (not channel)
      (progn$
       (er hard? '|Makefile-features| "Error opening Makefile-features?")
       state)
    (let* ((state (princ$ "export ACL2_FEATURES_DETECTED := 1" channel state))
           (state (newline channel state))
           (state (princ$ #+hons "export ACL2_HAS_HONS := 1"
                          #-hons "export ACL2_HAS_HONS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_HONS" channel state))
           (state (newline channel state))
           (state (princ$ #-(and gcl (not ansi-cl)) "export ACL2_HAS_ANSI := 1"
                          #+(and gcl (not ansi-cl)) "export ACL2_HAS_ANSI := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_ANSI" channel state))
           (state (newline channel state))
           (state (princ$ #+acl2-par "export ACL2_HAS_PARALLEL := 1"
                          #-acl2-par "export ACL2_HAS_PARALLEL := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_PARALLEL" channel state))
           (state (newline channel state))
           (state (princ$ #+non-standard-analysis "export ACL2_HAS_REALS := 1"
                          #-non-standard-analysis "export ACL2_HAS_REALS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_REALS" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_COMP_EXT := " channel state))
           (state (princ$ (@ compiled-file-extension) channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_COMP_EXT" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_HOST_LISP := " channel state))
           (host-lisp (symbol-name (@ host-lisp)))
           (state (princ$ host-lisp channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HOST_LISP" channel state))
           (state (newline channel state))
           (state (princ$ "export USE_QUICKLISP ?= " channel state))
           (state (princ$ (if (equal host-lisp "GCL") "0" "1") channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += USE_QUICKLISP" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_THINKS_BOOK_DIR_IS := " channel state))
           (state (princ$ (f-get-global 'system-books-dir state) channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_THINKS_BOOK_DIR_IS" channel state))
           (state (newline channel state))
           (state (close-output-channel channel state)))
      state)))

(defun write-file-if-obj-differs (filename object state)
  ;; Reads the given file and checks whether the first object it contains
  ;; equals the given object.  If not, overwrites that file with the given
  ;; object.
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (mv-let (need-to-write-file-p state)
      (if channel
          (mv-let (eof val state)
            (read-object channel state)
            (let ((state (close-input-channel channel state)))
              (if (and (not eof) (equal val object))
                  ;; File was read and object matches.
                  (mv nil state)
                ;; No object in the file or didn't match.
                (mv t state))))
        ;; File didn't exist.
        (mv t state))
      
      (if need-to-write-file-p
          (mv-let (channel state)
            (open-output-channel filename :object state)
            (if channel
                (let* ((state (print-object$ object channel state)))
                  (prog2$ (cw "Wrote ~s0~%" filename)
                          (close-output-channel channel state)))
              (prog2$ (cw "Error writing to ~s0~%" filename)
                      state)))
        (prog2$ (cw "No need to write ~s0~%" filename)
                state)))))

(write-file-if-obj-differs "first-order-like-terms-and-out-arities.certdep"
                           *first-order-like-terms-and-out-arities*
                           state)

(write-file-if-obj-differs "acl2-exports.certdep"
                           *acl2-exports*
                           state)

(write-file-if-obj-differs "acl2-version.certdep"
                           (f-get-global 'acl2-version state)
                           state)

(write-file-if-obj-differs "ground-zero-theory.certdep"
                           (let ((world (w state))) (current-theory 'acl2::ground-zero))
                           state)

(good-bye 0)
