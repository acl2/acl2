; Test whether a DAG's corresponding term is present in another DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/merge-dag-into-dag-quick" :dir :system)

;todo: what should happen if dag1 is a quotep?
;this assumes that dag2 is reduced (otherwise irrelevant nodes in it might lead to wrong results here)
(defun subdagp (dag1 dag2)
  (mv-let (erp nodenum-or-quotep-for-dag1 extended-dag2)
    (merge-dag-into-dag-quick dag1 dag2)
    (declare (ignore extended-dag2))
    (if erp
        nil ;todo: pass back the error?
      (if (quotep nodenum-or-quotep-for-dag1)
          (hard-error 'subdagp "didn't expect a quotep." nil)
        (<= nodenum-or-quotep-for-dag1 (top-nodenum dag2))))))

(defun subdag-of-somep (dag dags)
  (if (endp dags)
      nil
    (or (subdagp dag (first dags))
        (subdag-of-somep dag (rest dags)))))
