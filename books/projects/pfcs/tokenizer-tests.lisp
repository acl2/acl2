; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "tokenizer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun subtoken-treep (tree)
  (or (is-tree-rulename? tree "identifier")
      (is-tree-rulename? tree "integer")
      (is-tree-rulename? tree "operator")
      (is-tree-rulename? tree "separator")))

(defun subtoken-tree-listp (tl)
  (if (endp tl)
      t
    (and (subtoken-treep (car tl))
         (subtoken-tree-listp (cdr tl)))))

(assert-event
 (let ((subtoken-trees
(tokenize-pfcs "boolean_and(x,y,z) := {
  x * y == z
}
boolean_and(w0, w1, w2)")))
  (and (not (reserrp subtoken-trees))
       (subtoken-tree-listp subtoken-trees))))
