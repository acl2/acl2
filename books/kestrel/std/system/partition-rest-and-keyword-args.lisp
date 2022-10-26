; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the community-books file 3BSD-mod.txt.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/partition-rest-and-keyword-args
  :parents (std/system)
  :short "Theorems about @(tsee partition-rest-and-keyword-args)."

  (local
   (defthm partition-rest-and-keyword-args1-results
     (implies (true-listp x)
              (mv-let (rest keypart)
                  (partition-rest-and-keyword-args1 x)
                (and (true-listp rest)
                     (true-listp keypart))))))

  (local
   (defthm partition-rest-and-keyword-arg2-results
     (implies (symbol-alistp alist)
              (let ((alist1
                     (partition-rest-and-keyword-args2 keypart keys alist)))
                (implies (not (equal alist1 t))
                         (symbol-alistp alist1))))))

  (defthm true-listp-of-partition-rest-and-keyword.rest
    (implies (true-listp x)
             (mv-let (erp rest keypart)
                 (partition-rest-and-keyword-args x keys)
               (declare (ignore keypart))
               (implies (not erp)
                        (true-listp rest))))
    :rule-classes (:rewrite :type-prescription))

  (defthm symbol-alistp-of-partition-rest-and-keyword.keypart
    (implies (true-listp x)
             (mv-let (erp rest keypart)
                 (partition-rest-and-keyword-args x keys)
               (declare (ignore rest))
               (implies (not erp)
                        (symbol-alistp keypart))))))

(in-theory (disable partition-rest-and-keyword-args))
