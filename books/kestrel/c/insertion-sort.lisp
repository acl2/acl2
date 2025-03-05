; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "misc/total-order" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insertion-sort ((list true-listp))
  :parents (c)
  :short "A generic insert sort based on ACL2's total order of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be moved to a more general library."))
  :returns (sorted-list true-listp
                        :hyp :guard
                        :rule-classes (:rewrite :type-prescription))
  (cond ((endp list) nil)
        (t (insertion-sort-insert (car list)
                                  (insertion-sort (cdr list)))))
  :prepwork
  ((define insertion-sort-insert (elem (list true-listp))
     :returns (list-with-elem true-listp
                              :hyp :guard
                              :rule-classes (:rewrite :type-prescription))
     (cond ((endp list) (list elem))
           ((<< elem (car list)) (cons elem list))
           (t (cons (car list)
                    (insertion-sort-insert elem (cdr list))))))))
