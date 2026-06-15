; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Socket server test.
;
; Load this file, then start the server:
;
;   (include-book "kestrel/jsonrpc/socket-tests" :dir :system)
;   (run-jsonrpc-server 7070 state)
;
; Then paste the nc commands from the block comment below into a terminal.

(in-package "JSONRPC")

(include-book "socket")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; looks up a member by name in a member-list, returns nil if not found
(define find-member-value ((name stringp) (members member-listp))
  :returns (val valuep)
  (cond ((endp members) (value-null))
        ((equal (member->name (car members)) name)
         (member->value (car members)))
        (t (find-member-value name (cdr members)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subtract ((params structuredp) state)
  :returns (mv erp (res valuep) state)
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
             "Params must be [minuend, subtrahend] or
             {\"minuend\":...,\"subtrahend\":...}")
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
    (mv nil (value-number result) state)))

#|

(run-jsonrpc-server 7070 state)

nc localhost 7070 < json-request.txt > json-response.txt

|#
