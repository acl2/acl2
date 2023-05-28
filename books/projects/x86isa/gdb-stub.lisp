(in-package "X86ISA")

(include-book "machine/x86")
(include-book "tools/include-raw" :dir :system)

;; Function defined to be smashed later
(defun gdb-stub (x86)
  (declare (xargs :stobjs (x86)))
  x86)

(defttag :include-raw)
(include-raw "gdb-stub-raw.lsp")
