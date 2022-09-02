; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "defobject")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-object-tables
  :parents (atc-event-and-code-generation)
  :short "Tables of @(tsee defobjects)s, and operations on these tables."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-obj-info
  :short "Fixtype of information associated to
          an ACL2 @(tsee defobject) symbol translated to a C external object."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this is just a wrapper of @(tsee defobject-info),
     but we may extend it with more ATC-specific information in the future."))
  ((defobject defobject-info))
  :pred atc-obj-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-string-objinfo-alist
  :short "Fixtype of alists from strings to object information."
  :key-type string
  :val-type atc-obj-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred atc-string-objinfo-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-objinfo-alist-to-recognizers
  ((prec-objs atc-string-objinfo-alistp))
  :returns (recognizers symbol-listp)
  :short "Project the recognizers
          out of an external object information alist."
  (b* (((when (endp prec-objs)) nil)
       (info (cdar prec-objs))
       (recognizer (defobject-info->recognizer (atc-obj-info->defobject info)))
       (more-recognizers
        (atc-string-objinfo-alist-to-recognizers (cdr prec-objs))))
    (cons recognizer more-recognizers)))
