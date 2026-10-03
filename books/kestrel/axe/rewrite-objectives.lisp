; Objectives for rewriting (prove, disprove, or either)
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

;Recognizes a rewrite-objective: t, nil, or ?
(defund rewrite-objectivep (obj)
  (declare (xargs :guard t))
  (or (eq t obj)   ; trying to prove the thing is true
      (eq nil obj) ; trying to prove the thing is false
      ;; todo: use :?
      (eq '? obj)  ; not targeting true or false
      ))

(defund-inline flip-objective (obj)
  (declare (xargs :guard (rewrite-objectivep obj)))
  (if (eq t obj)
      nil
    (if (eq nil obj)
        t
      ;; must be '?:
      obj)))

(defconst *all-rewrite-objectives* '(? t nil))
