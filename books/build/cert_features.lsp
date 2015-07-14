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
    (let* ((state (princ$ "ACL2_FEATURES_DETECTED := 1" channel state))
           (state (newline channel state))
           (state (princ$ #+hons "ACL2_HAS_HONS := 1"
                          #-hons "ACL2_HAS_HONS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #-(and gcl (not ansi-cl)) "ACL2_HAS_ANSI := 1"
                          #+(and gcl (not ansi-cl)) "ACL2_HAS_ANSI := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #+acl2-par "ACL2_HAS_PARALLEL := 1"
                          #-acl2-par "ACL2_HAS_PARALLEL := "
                          channel state))
           (state (newline channel state))
           (state (princ$ #+non-standard-analysis "ACL2_HAS_REALS := 1"
                          #-non-standard-analysis "ACL2_HAS_REALS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "ACL2_COMP_EXT := " channel state))
           (state (princ$ (@ compiled-file-extension) channel state))
           (state (newline channel state))
           (state (princ$ "ACL2_HOST_LISP := " channel state))
           (state (princ$ (symbol-name (@ host-lisp)) channel state))
           (state (newline channel state))
           (state (princ$ "ACL2_THINKS_BOOK_DIR_IS := " channel state))
           (state (princ$ (f-get-global 'system-books-dir state) channel state))
           (state (newline channel state))
           (state (close-output-channel channel state)))
      state)))

(good-bye 0)
