; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(load "load-toothbrush.lsp")

(in-package "ACL2")

(let ((syms nil)
      (*package* (find-package "ACL2")))
  (do-symbols (sym (find-package "ACL2"))
              (when (and (not (equal (symbol-package-name sym)
                                     "COMMON-LISP"))
                         (fboundp sym))
                (push sym syms)))
  (with-open-file
   (str "defined-syms.lsp"
        :direction :output
        :if-exists :supersede)
   (loop for form in
         `((in-package "ACL2")
           (f-put-global
            'program-fns-with-raw-code
            (cons 'cl-defined-p
                  (f-get-global 'program-fns-with-raw-code *the-live-state*))
            *the-live-state*)
           (defparameter *cl-defined-p-ht* (make-hash-table :test 'eq))
           (loop for sym in ',syms
                 do
                 (setf (gethash sym *cl-defined-p-ht*)
                       t))
           (defun cl-defined-p (x)
             (if (equal (symbol-package-name x) "COMMON-LISP")
                 (fboundp x)
               (gethash x *cl-defined-p-ht*))))
         do (pprint form str))
   (terpri str)))
