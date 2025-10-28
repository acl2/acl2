; Tests of the material from decoder.lisp
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "decoder")
(include-book "std/testing/must-be-redundant" :dir :system)

(must-be-redundant
  (defun add-register-argsp (args)
  (declare (xargs :guard (symbol-alistp args)))
  (and (unsigned-byte-p 4 (lookup-eq 'cond args))
       (unsigned-byte-p 1 (lookup-eq 's args))
       (unsigned-byte-p 4 (lookup-eq 'rn args))
       (unsigned-byte-p 4 (lookup-eq 'rd args))
       (unsigned-byte-p 5 (lookup-eq 'imm5 args))
       (unsigned-byte-p 2 (lookup-eq 'type args))
       (unsigned-byte-p 4 (lookup-eq 'rm args)))))
