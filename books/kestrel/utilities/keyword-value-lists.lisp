; Keyword-Value Lists
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/rev" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-value-list-to-alist ((kvlist keyword-value-listp))
  :returns (alist alistp)
  :parents (kestrel-utilities system-utilities)
  :short "Turn a @('nil')-terminated list of even length
          with keywords at its even-numbered positions (counting from 0),
          into the corresponding alist."
  :long
  "<p>
   The alist associates each of the keywords at the even positions
   with the immediately following element in the list.
   The keywords in the alist are in the same order as in the original list.
   </p>"
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

  (verify-guards keyword-value-list-to-alist))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strip-keywords ((kvlist keyword-value-listp))
  :returns (keywords symbol-listp
                     :hyp :guard
                     :hints (("Goal"
                              :in-theory (enable keyword-value-list-to-alist))))
  :parents (kestrel-utilities system-utilities)
  :short "Extract the list of keywords from
          a @('nil')-terminated list of even length
          with keywords at its even-numbered positions (counting from 0),
          into the corresponding alist."
  :long
  "<p>
   The returned keywords are in the same order as in the starting list.
   </p>"
  (strip-cars (keyword-value-list-to-alist kvlist)))
