(in-package "X86ISA")

(defun serialize-mem (x86)
    (stobj-let ((bigmem::mem (mem$c x86)))
               (obj)
               (bigmem::serialize-mem bigmem::mem)
               obj))

(defun deserialize-mem (obj x86)
  (stobj-let ((bigmem::mem (mem$c x86)))
               (bigmem::mem)
               (bigmem::deserialize-mem obj bigmem::mem)
               x86))

(defun save-x86 (filename x86)
  (let ((*print-readably* t))
    (with-open-file (str filename
                         :direction :output
                         :if-exists :supersede)
      (print (serialize-x86 x86) str)
      (terpri str))
    nil))

(defun restore-x86 (filename x86)
  (with-open-file (str filename
                       :direction :input)
    (deserialize-x86 (read str) x86)))
