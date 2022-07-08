;; The ONCE-ONLY macro is hard to explain, hard to understand, hard to
;; write, hard to modify, and hard to live without once you figure out
;; how to use it. It's used in macros to guard against multiple
;; evaluation of arguments. My version is longer than most, but it
;; does some error checking and it gives gensym'd variables more
;; meaningful names than usual.

(in-package :cl-utilities)

(defun %check-once-only-names (names)
  "Check that all of the NAMES are symbols. If not, raise an error."
  ;; This only raises an error for the first non-symbol argument
  ;; found. While this won't report multiple errors, it is probably
  ;; more convenient to only report one.
  (let ((bad-name (find-if-not #'symbolp names)))
    (when bad-name
      (error "ONCE-ONLY expected a symbol but got ~S" bad-name))))

(defmacro once-only (names &body body)
  ;; Check the NAMES list for validity.
  (%check-once-only-names names)
  ;; Do not touch this code unless you really know what you're doing.
  (let ((gensyms (loop for name in names collect (gensym (string name)))))
    `(let (,@(loop for g in gensyms
                   for name in names
                   collect `(,g (gensym ,(string name)))))
       `(let (,,@(loop for g in gensyms for n in names
                       collect ``(,,g ,,n)))
          ,(let (,@(loop for n in names for g in gensyms
                         collect `(,n ,g)))
             ,@body)))))