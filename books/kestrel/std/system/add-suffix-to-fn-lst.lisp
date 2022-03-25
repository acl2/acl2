; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-suffix-to-fn-lst ((syms symbol-listp) (suffix stringp))
  :returns (new-syms symbol-listp)
  :parents (std/system)
  :short "Apply @(tsee add-suffix-to-fn) to a list of symbols,
          all with the same suffix."
  (cond ((endp syms) nil)
        (t (cons (add-suffix-to-fn (car syms) suffix)
                 (add-suffix-to-fn-lst (cdr syms) suffix))))
  ///

  (defret len-of-add-suffix-to-fn-lst
    (equal (len new-syms)
           (len syms))))
