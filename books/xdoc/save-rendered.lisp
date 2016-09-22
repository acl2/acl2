; XDOC Documentation System for ACL2
; Copyright (C) 2009-2016 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com> (but see next comment)

; This book was created by Matt Kaufmann to define function save-rendered,
; essentially using code that was formerly in community book
; books/doc/top.lisp, with original author Jared Davis.

(in-package "XDOC")

(include-book "defxdoc-raw")
(include-book "save")
(include-book "system/doc/render-doc-base" :dir :system)
(include-book "alter")

(set-state-ok t)
(program)

(defttag :open-output-channel!)

(defun save-rendered (outfile
                      header
                      force-missing-parents-p
                      maybe-add-top-topic-p
                      state)

; This code was originally invoked with force-missing-parents-p and
; maybe-add-top-topic-p both true.  Perhaps that's always best.

; Example of outfile:
;   (acl2::extend-pathname (cbd)
;                           "../system/doc/rendered-doc-combined.lsp"
;                           state))

  (state-global-let*
   ((current-package "ACL2" set-current-package-state))
   (b* (((mv ? all-topics0 state)
         (all-xdoc-topics state))
        (all-topics
         (time$
          (let* ((all-topics1 (normalize-parents-list ; Should we clean-topics?
                               all-topics0))
                 (all-topics2 (if maybe-add-top-topic-p
                                  (maybe-add-top-topic all-topics1)
                                all-topics1))
                 (all-topics3 (if force-missing-parents-p
                                  (force-missing-parents all-topics2)
                                all-topics2)))
            all-topics3)))
        ((mv rendered state)
         (time$ (render-topics all-topics all-topics state)))
        (rendered (time$ (split-acl2-topics rendered nil nil nil)))
        (- (cw "Writing ~s0~%" outfile))
        ((mv channel state) (open-output-channel! outfile :character state))
        ((unless channel)
         (cw "can't open ~s0 for output." outfile)
         (acl2::silent-error state))
        (state (princ$ header channel state))
        (state (time$ (fms! "~x0"
                            (list (cons #\0 rendered))
                            channel state nil)))
        (state (fms! ")" nil channel state nil))
        (state (newline channel state))
        (state (close-output-channel channel state)))
     (value '(value-triple :ok)))))
