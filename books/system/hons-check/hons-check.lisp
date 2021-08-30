; Hons Sanity Checking
; Copyright (C) 2010 Centaur Technology
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

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
; (depends-on "hons-check-raw.lsp")

(defun unsound-normedp (x)
  (declare (xargs :guard t)
           (ignorable x))
  (er hard? 'unsound-normedp "Under the hood definition not installed."))

(defun unsound-falp (x)
  (declare (xargs :guard t)
           (ignorable x))
  (er hard? 'unsound-falp "Under the hood definition not installed."))

(defttag unsound-normedp)

(progn!
 (set-raw-mode t)
 (defun unsound-normedp (x)
   (hl-hspace-normedp x *default-hs*))

 (defun unsound-falp (x)
   (let* ((faltable (hl-hspace-faltable *default-hs*))
          (table    (hl-faltable-table faltable))
          (slot1    (hl-faltable-slot1 faltable))
          (slot2    (hl-faltable-slot2 faltable)))
     (if (or (gethash x table)
             (and x
                  (or (eq (hl-falslot-key slot1) x)
                      (eq (hl-falslot-key slot2) x))))
         t
       nil))))

(defttag nil)


(defsection hons-check
  :parents (hons-and-memoization)
  :short "Run sanity checks on the Hons Space."

  :long "<p>This is a potentially expensive run-time check that can be useful
when debugging the Hons implementation.</p>

<p>In the logic, it simply returns @('nil').</p>

<p>Under the hood, it checks that the Hons Space satisfies many invariants, and
causes an error if any invariants are violated.</p>"

  (defun hons-check ()
    "Has an under-the-hood implementation"
    (declare (xargs :guard t))
    nil))

(defttag hons-check)

(include-raw "hons-check-raw.lsp")
