; Utilities for making keywords into symbols in the ACL2 package
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun keyword-to-acl2-package (keyword)
  (declare (xargs :guard (keywordp keyword)))
  (intern-in-package-of-symbol (symbol-name keyword)
                               'defthm))

(defun keywords-to-acl2-package-aux (keywords acc)
  (declare (xargs :guard (acl2::keyword-listp keywords)))
  (if (endp keywords)
      acc
    (keywords-to-acl2-package-aux (rest keywords)
                                  (cons (keyword-to-acl2-package (first keywords))
                                        acc))))

(defthm len-of-keywords-to-acl2-package-aux
  (equal (len (keywords-to-acl2-package-aux keywords acc))
         (+ (len keywords) (len acc))))

(defthm symbol-listp-of-keywords-to-acl2-package-aux
  (equal (symbol-listp (keywords-to-acl2-package-aux keywords acc))
         (symbol-listp acc)))

(defthm true-listp-of-keywords-to-acl2-package-aux
  (equal (true-listp (keywords-to-acl2-package-aux keywords acc))
         (true-listp acc)))

(defun keywords-to-acl2-package (keywords)
  (declare (xargs :guard (acl2::keyword-listp keywords)))
  (keywords-to-acl2-package-aux keywords nil))

(defthm len-of-keywords-to-acl2-package
  (equal (len (keywords-to-acl2-package keywords))
         (len keywords)))

(defthm symbol-listp-of-keywords-to-acl2-package
  (symbol-listp (keywords-to-acl2-package keywords)))
