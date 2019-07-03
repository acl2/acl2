; Keyword-Value Lists
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/rev" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-value-list-to-alist ((kvlist keyword-value-listp))
  :returns (alist alistp)
  :parents (kestrel-utilities)
  :short "Turn a true list of even length
          with keywords at its even-numbered positions (counting from 0),
          into the corresponding alist."
  :long
  (xdoc::topstring-p
   "The alist associates each of the keywords at the even positions
    with the immediately following element in the list.
    The keywords in the alist are in the same order as in the original list.")
  (mbe :logic (if (endp kvlist)
                  nil
                (cons (cons (car kvlist) (cadr kvlist))
                      (keyword-value-list-to-alist (cddr kvlist))))
       :exec (keyword-value-list-to-alist-aux kvlist nil))
  :verify-guards nil ; done below

  :prepwork
  ((define keyword-value-list-to-alist-aux ((kvlist keyword-value-listp)
                                            (rev-alist alistp))
     (if (endp kvlist)
         (rev rev-alist)
       (keyword-value-list-to-alist-aux (cddr kvlist)
                                        (cons (cons (car kvlist) (cadr kvlist))
                                              rev-alist)))
     :enabled t))

  ///

  (local
   (defrule verify-guards-lemma
     (equal (keyword-value-list-to-alist-aux kvlist rev-alist)
            (revappend rev-alist (keyword-value-list-to-alist kvlist)))))

  (verify-guards keyword-value-list-to-alist)

  (more-returns
   (alist symbol-alistp
          :hyp (keyword-value-listp kvlist)
          :name symbol-alistp-of-keyword-value-list-to-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-keyword-value-list-from-keys-and-value ((keys keyword-listp)
                                                     val)
  :returns (kvlist keyword-value-listp
                   :hyp :guard)
  :parents (kestrel-utilities)
  :short "Make a list satisfying @(tsee keyword-value-listp) by associating
          each member of a true-list of keywords list of keywords with a
          given value."
  :long
  (xdoc::topstring-p
   "The keywords in the result are in the same order as in the input keys.")
  (cond
   ((endp keys) nil)
   (t (list* (car keys) val
             (make-keyword-value-list-from-keys-and-value (cdr keys) val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
