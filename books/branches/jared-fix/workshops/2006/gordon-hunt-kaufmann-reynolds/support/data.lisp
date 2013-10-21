(in-package "ACL2")

(defconst *write-increment* 13)

(defconst *read-increment* 17)

(defconst *max-addr* 100)

(set-compile-fns t)

; For guard verification:
(local
 (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun make-instrs (read-start write-start flag n acc)
  (declare (xargs :measure (acl2-count n)
                  :guard (and (natp n) (natp read-start) (natp write-start))))
  (if (zp n)
      acc
    (if flag
        (make-instrs read-start
                     (mod (+ write-start *write-increment*) *max-addr*)
                     (not flag)
                     (1- n)
                     (cons (list 'write write-start n) acc))
      (make-instrs (mod (+ read-start *read-increment*) *max-addr*)
                   write-start
                   (not flag)
                   (1- n)
                   (cons (list 'read read-start) acc)))))
