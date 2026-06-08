; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "process-rpc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; looks up a member by name in a member-list, returns nil if not found
(defun find-member-value (name members)
  (declare (xargs :guard (and (stringp name)
                              (member-listp members))
                  :mode :program))
  (cond ((endp members) nil)
        ((equal (member->name (car members)) name)
         (member->value (car members)))
        (t (find-member-value name (cdr members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subtract ((params structuredp) state)
  :short "Subtract two numbers. Accepts array [minuend, subtrahend] or
          object {\"minuend\": ..., \"subtrahend\": ...}."
  :mode :program
  :stobjs state
  (b* (((mv x y)
        (if (equal (structured-kind params) :array)
            (b* ((elems (structured-array->elements params)))
              (if (= (len elems) 2)
                  (mv (first elems) (second elems))
                (mv nil nil)))
          (b* ((members (structured-object->members params))
               (x (find-member-value "minuend" members))
               (y (find-member-value "subtrahend" members)))
            (mv x y))))
       ((unless (and x y))
        (mv (make-invalid-params-error
             "params must be [minuend, subtrahend] or {\"minuend\":...,\"subtrahend\":...}")
            (value-null)
            state))
       ((unless (equal (value-kind x) :number))
        (mv (make-invalid-params-error "minuend must be a number")
            (value-null)
            state))
       ((unless (equal (value-kind y) :number))
        (mv (make-invalid-params-error "subtrahend must be a number")
            (value-null)
            state))
       (result (- (value-number->get x) (value-number->get y))))
    (mv nil (make-value-number :get result) state)))

#|

(process-json-rpc-file "json-request.txt"
                       "json-response.txt"
                       state)

|#
