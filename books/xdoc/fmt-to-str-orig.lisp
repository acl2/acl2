; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "std/util/bstar" :dir :system)
(set-state-ok t)
(program)

; fmt-to-str-orig.lisp
;
; This file is merely a bootstrapping hack.
;
; We implement a bare-bones pretty printer, similar to ACL2's fmt-to-string or
; str::pretty.  Unlike ACL2's fmt-to-string, we use narrower margins and print
; with downcased symbols.
;
; This function was historically used throughout XDOC in the pretty-printing of
; terms, e.g., to handle things like @(def ...).  Today, XDOC's preprocessor
; instead uses str::pretty, which allows us to avoid nasty problems with using
; ACL2's formatting functions to print outside of the loop, e.g., for use with
; the ACL2 Sidekick.
;
; Why do we still need this file, then?  Well, macros such as DEFINE and
; DEFAGGREGATE, which are used in the definition of str::pretty, have their own
; documentation-generation functionality.  Historically these documentation
; producing routines made use of fmt-to-string.  This leads to circular
; dependencies such as fmt-to-str -> str::pretty -> define -> fmt-to-str!
;
; To break this circularity, we keep the original implementation of fmt-to-str,
; renaming it to fmt-to-str-orig.  We use the orig version in macros such as
; DEFINE to minimize dependencies and avoid these loops.  When these macros
; call fmt-to-str-orig, they're running in the real ACL2 loop, so we don't have
; these outside-the-loop problems.  Meanwhile, we avoid the fmt functions in
; the real preprocessor code.

(defun fmt-to-str-orig-aux (string alist base-pkg state)
  ;; Use ACL2's fancy new string-printing stuff to do pretty-printing
  (b* ((hard-right-margin   (f-get-global 'acl2::fmt-hard-right-margin state))
       (soft-right-margin   (f-get-global 'acl2::fmt-soft-right-margin state))
       (print-case          (f-get-global 'acl2::print-case state))
       (pkg                 (current-package state))
       (base-pkg-name       (symbol-package-name base-pkg))
       ((mv er ?val state)  (acl2::in-package-fn base-pkg-name state))
       ((when er)
        (er hard? 'fmt-to-str-orig-aux "Error switching to package ~x0" base-pkg-name)
        (mv "" state))
       (state               (set-fmt-hard-right-margin 68 state))
       (state               (set-fmt-soft-right-margin 62 state))
       (state               (set-print-case :downcase state))
       ((mv channel state)  (open-output-channel :string :character state))
       ((mv ?col state)     (fmt1 string alist 0 channel state nil))
       ((mv er1 str state)  (get-output-stream-string$ channel state))
       ((mv er2 ?val state) (acl2::in-package-fn pkg state))
       (state               (set-fmt-hard-right-margin hard-right-margin state))
       (state               (set-fmt-soft-right-margin soft-right-margin state))
       (state               (set-print-case print-case state))
       ((when er1)
        (er hard? 'fmt-to-str-orig-aux "Error with get-output-stream-string$?")
        (mv "" state))
       ((when er2)
        (er hard? 'fmt-to-str-orig-aux "Error switching back to package ~x0" pkg)
        (mv "" state)))
    (mv str state)))

(defun fmt-to-str-orig (x base-pkg state)
  ;; Basic formatting of sexprs, no encoding or autolinking
  (fmt-to-str-orig-aux "~x0" (list (cons #\0 x)) base-pkg state))
