; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "internal/subbag-defs")
(include-book "bag-defs")
(include-book "count-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "subbag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; As in treeset's subset-defs: std::defredundant cannot reproduce a
;; guard-verified define-sk, so the quantified form is stated here with its
;; guards verified separately.

(defun-sk subbag-sk (sub sup)
  (declare (xargs :verify-guards nil))
  (declare (xargs :guard t))
  (forall (elem)
          (non-exec (<= (count elem sub) (count elem sup))))
  :rewrite
  (implies (subbag-sk sub sup)
           (non-exec (<= (count elem sub) (count elem sup))))
  :skolem-name subbag-sk-witness
  :thm-name subbag-sk-necc)

(verify-guards subbag-sk)

(std::defredundant
  :names (subbag
          subbag-sk-witness
          subbag-sk
          ))
