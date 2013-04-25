(in-package "ACL2")

; One may wish to modify state when defining constants inside a book.  This is
; particularly useful when such modification of state empowers one to do things
; like read from a file.  This example doesn't even modify state, but since foo
; returns the ACL2 state, foo could do so.  Thus, it demonstrates the idea.

; Note that this file has nothing to do with trust tags, which was my original
; intention.  The user that is interested in permitting trust tags during the
; first pass of certification but not the second pass should see ACL2
; documentation topic "set-write-acl2x" and book
; "make-event/double-cert-test-1.lisp".

(include-book "tools/defconsts" :dir :system)

(defun foo (state)
  (declare (xargs :stobjs (state)
                  :verify-guards nil))
  (progn$ (cw "==========================================================~%")
          (cw "Running foo.~%")
          (cw "This should only print during certification.~%")
          (cw "==========================================================~%")
          (mv (f-get-global 'waterfall-parallelism state) state)))

(defconsts (*foo* state)
  (foo state))
