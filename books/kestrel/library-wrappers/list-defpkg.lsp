; Portcullis file for list-defpkg.lisp
;
; Copyright (C) 2016-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cherry pick just the LIST package from books/coi/lists/package.lsp, so that
;; we don't get all the extra stuff that that file brings in.  This needs to be
;; kept in sync with the defpkg in books/coi/lists/package.lsp.
(defpkg "LIST"
  (set-difference-eq
;;   (remove-duplicates-eql ;no longer necessary due to change in ACL2
    `(,@*acl2-exports*
      ,@*common-lisp-symbols-from-main-lisp-package*

      a b c d e f g h i j k l m n o p q r s u v w x y z

      ;; Leave this here, becuase we want our version of firstn to be
      ;; the same one as used in some of the books, e.g.,
      ;; data-structures.
      firstn

      ;; bzo - this was originally in the ACL2 package and some code
      ;; may still rely on that.  But, we should remove this eventually.
      repeat

      ;; bzo - remove me eventually if Matt adds me to *acl2-exports*
      update-nth-array

      )
    ;)
    '(fix)))
