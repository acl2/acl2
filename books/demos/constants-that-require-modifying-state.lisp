(in-package "ACL2")

(include-book "tools/defconsts" :dir :system)

(defun foo (state)
  (declare (xargs :stobjs (state)
                  :verify-guards nil))
  (progn$ (cw "==========================================================~%")
          (cw "Running foo.~%")
          (cw "This should only print during first pass of certification.~%")
          (cw "==========================================================~%")
          (mv (f-get-global 'waterfall-parallelism state) state)))

(defconsts (*foo* state)
  (foo state))
