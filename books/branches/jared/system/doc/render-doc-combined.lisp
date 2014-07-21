; Converter From ACL2 System Documentation to Text
; Copyright (C) 2013 Centaur Technology
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
; 10/29/2013: Mods made by Matt Kaufmann to support Emacs-based ACL2-Doc browser

(in-package "XDOC")
(set-state-ok t)
(include-book "render-doc-base")
(program)

(include-book "doc/top" :dir :system)
(include-book "doc/top-topic" :dir :system)

(value-triple (len (get-xdoc-table (w state))))

(defttag :open-output-channel!)

(acl2::defconsts
 (& & state)
 (state-global-let*
  ((current-package "ACL2" set-current-package-state))
  (b* ((all-topics (force-root-parents
                    (maybe-add-top-topic
                     (normalize-parents-list ; Should we clean-topics?
                      (get-xdoc-table (w state))))))
       ((mv rendered state)
        (render-topics all-topics all-topics state))
       (rendered (split-acl2-topics rendered nil nil nil))
       (- (cw "Writing rendered-doc-combined.lsp~%"))
       ((mv channel state) (open-output-channel! "rendered-doc-combined.lsp"
                                                 :character state))
       ((unless channel)
        (cw "can't open rendered-doc-combined.lsp for output.")
        (acl2::silent-error state))
       (state (princ$ "; Documentation for acl2+books
; WARNING: GENERATED FILE, DO NOT HAND EDIT!
; The contents of this file are derived from the full acl2+books
; documentation.  For license and copyright information, see community book
; xdoc/fancy/LICENSE.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

(in-package \"ACL2\")

(defconst *acl2+books-documentation* '"
                      channel state))
       (state (fms! "~x0"
                    (list (cons #\0 rendered))
                    channel state nil))
       (state (fms! ")" nil channel state nil))
       (state (newline channel state))
       (state (close-output-channel channel state)))
      (value nil))))
