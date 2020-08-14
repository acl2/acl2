; A utility to make a legal variable name
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "legal-variablep")
(local (include-book "coerce"))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(local (in-theory (disable char append)))

;;add $ to make the name legal, at front if starts with &
;; Always uses the acl2 package.  TODO: Generalize.
(defund make-legal-var-in-acl2-package (desired-name)
  (declare (xargs :guard (symbolp desired-name)))
  (let ((str (symbol-name desired-name)))
    (if (equal "" str)
        'acl2::|| ;; empty name is allowed!  should it be?
        (if (equal #\& (char str 0))
            ;; If the name starts with &, we add a $ to the beginning:
            (intern (concatenate 'string "$" str) "ACL2")
          (if (and (equal (char str 0) #\*)
                   (equal (char str (1- (length str))) #\*))
              ;; If the name starts and ends with *, we add a $ to the end:
              (intern (concatenate 'string "$" str) "ACL2")
            (if (member-equal str (names-of-common-lisp-specials-and-constants))
                ;; If the name is one of the disallowed ones, we add a $ to the end:
                (intern (concatenate 'string "$" str) "ACL2")
              ;; No need to add a $
              (intern str "ACL2")))))))

(defthm legal-variablep-of-make-legal-var-in-acl2-package
  (legal-variablep (make-legal-var-in-acl2-package desired-name))
  :hints (("Goal" :in-theory (enable legal-variable-name-in-acl2-packagep
                                     make-legal-var-in-acl2-package
                                     member-equal-of-cons ;many cases
                                     char
                                     (names-of-common-lisp-specials-and-constants)))))
