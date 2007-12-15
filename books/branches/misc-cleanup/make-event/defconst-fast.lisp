; This macro, defconst-fast, is based on a conversation with Warren Hunt.  A
; defconst in a book has the unfortunate property that its form is evaluated
; not only when that book is certified, but also (again) when that book is
; included.  Defconst-fast is more efficient because it generates a defconst
; that uses the result of the evaluation.  See defconst-fast-examples.lisp.

(in-package "ACL2")

(defmacro defconst-fast (name form &optional (doc '"" doc-p))
  `(make-event
    (let ((val ,form))
      (list* 'defconst ',name (list 'quote val)
             ,(and doc-p (list 'list doc))))))
