; Basic utilities on forms that look like function calls.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Simple utilities for manipulating forms.

;; For a form that looks like a function call, extract its arguments (the
;; numbering is 1-based).
;; TODO: Consider calling these arg1, etc.  Matt suggests that it's bad style
;; to call fargn on something that's not a translated term (and these are like
;; fargn).

(defmacro farg1 (form) `(car (cdr ,form)))
(defmacro farg2 (form) `(car (cdr (cdr ,form))))
(defmacro farg3 (form) `(car (cdr (cdr (cdr ,form)))))
(defmacro farg4 (form) `(car (cdr (cdr (cdr (cdr ,form))))))
(defmacro farg5 (form) `(car (cdr (cdr (cdr (cdr (cdr ,form)))))))
(defmacro farg6 (form) `(car (cdr (cdr (cdr (cdr (cdr (cdr ,form))))))))

;; Test whether FORM looks like a call of the function FN.  This requires FN to
;; be a symbol (not a lambda).  See also ffn-symb-p, but that is for
;; pseudo-terms.
(defabbrev call-of (fn form)
  (and (consp form)
       (eq fn (car form))))
