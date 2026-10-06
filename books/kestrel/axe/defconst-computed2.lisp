; A variant of defconst-computed that uses result-array-stobj
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defconst-computed" :dir :system) ; for make-defconst-form
(include-book "result-array-stobj")

(defun defconst-computed2-fn (name form)
  `(mv-let (erp result state result-array-stobj)
     ,form
     (mv erp
         (make-defconst-form ',name result)
         state result-array-stobj)))

;this one takes a form that returns (mv erp result state result-array-stobj)
(defmacro defconst-computed2 (name form)
  `(make-event ,(defconst-computed2-fn name form)))

;; test: (defconst-computed2 *bar* (mv nil '3 state result-array-stobj))
