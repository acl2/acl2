; Copyright (C) 2021 Centaur Technology and ForrestHunt, Inc.
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
; Original author:  Sol Swords <sswords@gmail.com>
; Additional author: Matt Kaufmann <kaufmann@cs.utexas.edu>

(in-package "ACL2")

(include-book "std/stobjs/stobj-table" :dir :system)

(in-theory (disable nth update-nth))

(defstobj foo (foo-fld))

(defthm foo-fld-of-update-foo-fld
  (equal (foo-fld (update-foo-fld val foo))
         val))

(in-theory (disable foop foo-fld update-foo-fld))

(defund do-something-complicated-with-foo (in foo)
  (declare (xargs :stobjs foo))
  (update-foo-fld in foo))

(defthm foo-fld-of-do-something-complicated
  (equal (foo-fld (do-something-complicated-with-foo in foo)) in)
  :hints(("Goal" :in-theory (enable do-something-complicated-with-foo))))

; The following defun and defthm show a successful 

(defun test1 (stobj-table)

; Read the foo-fld of foo in stobj-table.

  (declare (xargs :stobjs (stobj-table)))
  (stobj-let ((foo (tbl-get 'foo stobj-table (create-foo))))
             (fld)
             (foo-fld foo)
             fld))

(defthm test1-of-do-sompething-complicated

; Read-over-write: read (the field of) foo from stobj-table after writing a
; "complicated" foo to stobj-table.

  (let* ((foo1 (do-something-complicated-with-foo in foo))
         (stobj-table (tbl-put 'foo foo1 stobj-table))) ; write
    (equal (test1 stobj-table) ; read
           in)))

; Now we see that if we fix foo after extracting it from stobj-table, that
; ruins our ability to prove the theorem above.

(defun-nx foo-fixer (foo)
  (if (foop foo) foo (create-foo)))

(defun-nx test2 (stobj-table)
  (let* ((foo (foo-fixer (tbl-get 'foo stobj-table (create-foo))))
         (fld (foo-fld foo)))
    fld))

(make-event

; This make-event form is essentially an application of must-fail to the
; indicated thm form.  But we want to see the checkpoint, and must-fail hides
; that.

 (mv-let (erp val state)

; The proof that formerly succeeded using test1 now fails using test2.  The
; checkpoint shows that we need to know (at least when in is non-nil) that
; (foop (do-something-complicated-with-foo in foo)) holds.

   (with-output
     :on summary
     (thm
      (let* ((foo1 (do-something-complicated-with-foo in foo))
             (stobj-table (tbl-put 'foo foo1 stobj-table))) ; write
        (equal (test2 stobj-table)                          ; read
               in))))
   (declare (ignore val))
   (if erp
       (value '(value-triple :failed-as-expected))
     (er soft 'top-level
         "Theorem unexpectedly succeeded!"))))
