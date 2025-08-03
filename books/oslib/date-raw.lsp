; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
; Contributing author: Grant Jurgensen <grant@kestrel.edu>

(in-package "OSLIB")

(defun get-decoded-time$ (state)

   (unless (live-state-p state)
     (er hard? 'get-decoded-time$ "Get-decoded-time$ can only be called on a live state.")
     (mv 0 0 0 1 1 0 0 nil 0 state))

   (multiple-value-bind
    (second minute hour date month year day daylight-p zone)
    (get-decoded-time)
    (mv second minute hour date month year day daylight-p zone state)))


(defun universal-time-fn (state)

   (unless (live-state-p state)
     (er hard? 'universal-time "Universal-time can only be called on a live state.")
     (mv 0 state))

   (let ((ans (get-universal-time)))
     (unless (natp ans)
       (er hard? 'universal-time "Common Lisp's get-universal-time returned a non-natural: ~x0." ans))
     (mv ans state)))
