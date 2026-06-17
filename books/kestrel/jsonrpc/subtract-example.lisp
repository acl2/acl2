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
(include-book "socket")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-member-value ((name stringp) (members member-listp))
  :returns (val valuep)
  (cond ((endp members) (value-null))
        ((equal (member->name (car members)) name)
         (member->value (car members)))
        (t (find-member-value name (cdr members)))))

(define member-exists-p ((name stringp) (members member-listp))
  :returns (exists booleanp)
  (cond ((endp members) nil)
        ((equal (member->name (car members)) name) t)
        (t (member-exists-p name (cdr members)))))

(define subtract ((params structuredp) state)
  :returns (mv erp (res valuep) state)
  :stobjs state
  (if (equal (structured-kind params) :array)
      ; Case 1: params is array
      (b* ((elems (structured-array->elements params))
           ((unless (= (len elems) 2))
            (mv (make-invalid-params-error
                 "Array params must have exactly 2 elements: [minuend, subtrahend]")
                (value-null) state))
           (x (first elems))
           (y (second elems))
           ((unless (equal (value-kind x) :number))
            (mv (make-invalid-params-error "minuend must be a number")
                (value-null) state))
           ((unless (equal (value-kind y) :number))
            (mv (make-invalid-params-error "subtrahend must be a number")
                (value-null) state))
           (result (- (value-number->get x) (value-number->get y))))
        (mv nil (value-number result) state))
    ; Case 2: params is object
    (b* ((members (structured-object->members params))
         ((unless (= (len members) 2))
          (mv (make-invalid-params-error
               "Object params must have exactly 2 fields: minuend and subtrahend")
              (value-null) state))
         ((unless (member-exists-p "minuend" members))
          (mv (make-invalid-params-error "Missing field: minuend")
              (value-null) state))
         ((unless (member-exists-p "subtrahend" members))
          (mv (make-invalid-params-error "Missing field: subtrahend")
              (value-null) state))
         (x (find-member-value "minuend" members))
         (y (find-member-value "subtrahend" members))
         ((unless (equal (value-kind x) :number))
          (mv (make-invalid-params-error "minuend must be a number")
              (value-null) state))
         ((unless (equal (value-kind y) :number))
          (mv (make-invalid-params-error "subtrahend must be a number")
              (value-null) state))
         (result (- (value-number->get x) (value-number->get y))))
      (mv nil (value-number result) state))))

#|

(process-json-rpc-file "json-request.txt"
                       "json-response.txt"
                       '(subtract)
                       state)

(run-jsonrpc-server 7070 nil '(subtract) state)

|#
