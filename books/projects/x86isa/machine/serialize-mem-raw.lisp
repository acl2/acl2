(in-package "X86ISA")

(defun serialize-mem (x86)
  (let* ((arr (make-array '(#x20000000))))
    (loop for i from 0 below #x20000000
          do (setf (aref arr i) (memi i x86)))
    arr))
