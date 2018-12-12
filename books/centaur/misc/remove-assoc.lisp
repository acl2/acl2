; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; REMOVE-ASSOC-EQUAL is like REMOVE1-ASSOC-EQUAL, but removes all occurrences of
; the key from the alist instead of just removing the first occurrence.

; Virtually all of this file has been moved to ACL2 source file axioms.lisp,
; after checking with Sol Swords and not getting an objection.  Note that
; modifications to earlier versions were made anyhow by Matt Kaufmann,
; 5/19/2014, to support changes in let-mbe that provide better guard-checking;
; indeed, the results were completely analogous to ACL2 source functions and
; macros delete-assoc*, renamed 12/2018 remove1-assoc*.

(defthm assoc-of-remove-assoc-split
  (equal (assoc j (remove-assoc k a))
         (if (equal j k)
             nil
           (assoc j a))))

