; Standard System Library
;
; Copyright (C) 2020 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-suffix-to-fn-or-const ((name (and (symbolp name)
                                              (not (keywordp name))))
                                   (suffix stringp))
  :returns (new-name symbolp)
  :parents (std/system)
  :short "Add a suffix to a function or constant name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is related to the built-in functions
     @(tsee add-suffix) and @(tsee add-suffix-to-fn).
     If the argument symbol starts and ends with @('*'),
     it is considered a constant name
     and the suffix is added just before the ending @('*'),
     so that the resulting symbol is still a constant name.
     Otherwise, the argument symbol is considered a function name
     and @(tsee add-suffix-to-fn) is used."))
  (let* ((s (symbol-name name))
         (len (length s)))
    (cond
     ;; The following test is essentially from legal-variable-or-constant-namep.
     ;; We could simply call legal-variable-or-constant-namep,
     ;; but this is a bit more efficient.
     ((and (not (= len 0))
           (eql (char s 0) #\*)
           (eql (char s (1- len)) #\*))
      (if (equal (symbol-package-name name)
                 *main-lisp-package-name*)
          (intern (concatenate 'string (subseq s 0 (1- len)) suffix "*")
                  "ACL2")
        (intern-in-package-of-symbol
         (concatenate 'string (subseq s 0 (1- len)) suffix "*")
         name)))
     (t (add-suffix-to-fn name suffix)))))
