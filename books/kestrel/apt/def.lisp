; A utility to apply a transformation, supplying the new name as the first arg
;
; Copyright (C) 2016-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Def simplify wraps a call of a transformation, supplying the given name as
;; the :new-name argument.  Def can help make clear where a given name was
;; created, rather than allowing the transformation to create the new name
;; implicitly (implicitly created names will not appear at their points of
;; creation and so will be hard to search for).

;; Example call, to create foo.2 from foo by applying rename-params:
;; (def foo.2 (rename-params foo ((x y))))

;; TODO: Think about how to support mutual-recursion.

;; We could have this book include all of the transformations that it might
;; invoke, but I'd prefer to avoid those dependencies (so that we can have
;; individual derivations depend on just the transformations they need, to
;; avoid unnecessary rebuilding when other transformations change).

;; TODO Try to give a nicer error if the :new-name keyword is already supplied, but
;; that might require knowing how to interpret the args of the transformation.
(defun def-fn (name form)
  (let* ((transformation-name (car form))
         (transformation-args (cdr form)))
    `(,transformation-name ,@transformation-args
                           :new-name ,name)))

;; Creates a new function named NEW-NAME by applying the transformation given in FORM
(defmacro def (new-name form)
  (def-fn new-name form))
