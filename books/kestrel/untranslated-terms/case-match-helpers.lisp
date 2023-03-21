; Helper functions for manipulating calls of case-match
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Extract the bodies of the items.  These are the untranslated terms that need to be handled.
;; TODO: What about a decl of (type (satisfies foo)) where perhaps FOO is a function to replace?
(defun extract-terms-from-case-match-cases (cases ;each is either (<pat> <body>) or (<pat> <dcl> <body>).
                                            )
  (declare (xargs :guard (true-list-listp cases)))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (second case) (extract-terms-from-case-match-cases (rest cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (third case) (extract-terms-from-case-match-cases (rest cases)))))))

;; Whenever there is a term in the cases, use the corresponding term from new-terms-from-cases.
(defun recreate-case-match-cases (cases new-terms-from-cases)
  (declare (xargs :guard (and (true-list-listp cases)
                              (true-listp new-terms-from-cases))))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (list (first case) (first new-terms-from-cases))
                (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (list (first case) (second case) (first new-terms-from-cases))
              (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))))))
