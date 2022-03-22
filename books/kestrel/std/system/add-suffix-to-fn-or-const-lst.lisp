; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "add-suffix-to-fn-or-const")

(include-book "kestrel/std/basic/nonkeyword-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-suffix-to-fn-or-const-lst ((syms symbol-listp) (suffix stringp))
  :guard (nonkeyword-listp syms)
  :returns (new-syms symbol-listp)
  :parents (std/system)
  :short "Apply @(tsee add-suffix-to-fn-or-const) to a list of symbols,
          all with the same suffix."
  (cond ((endp syms) nil)
        (t (cons (add-suffix-to-fn-or-const (car syms) suffix)
                 (add-suffix-to-fn-or-const-lst (cdr syms) suffix))))
  :prepwork ((local (in-theory (disable keywordp))))
  ///

  (defret len-of-add-suffix-to-fn-or-const-lst
    (equal (len new-syms)
           (len syms))))
