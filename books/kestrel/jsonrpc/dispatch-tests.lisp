; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "process-rpc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of dispatching to method functions of various signatures.

(defun process-json-rpc-string (msg state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((mv - alist) (parse-json-rpc msg))
       ((mv erp responses state)
        (process-all alist :any 'process-json-rpc-string state)))
    (mv erp (value-to-json-string (car responses)) state)))

(defmacro assert-response (request response)
  `(make-event
    (er-let* ((str (process-json-rpc-string ,request state)))
      (if (equal str ,response)
          (value '(value-triple :success))
        (er soft 'assert-response
            "Expected the response~%~s0~%but got~%~s1"
            ,response
            str)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj counter
  (total :type (integer 0 *) :initially 0))

;; A user stobj and params, in the opposite of the usual order.
(define bump (counter (params structuredp))
  :stobjs counter
  :returns (mv erp (res valuep) counter)
  (b* (((unless (structured-case params :array))
        (mv (make-invalid-params-error "Expected an array.") (value-null) counter))
       (elems (structured-array->elements params))
       ((unless (and (consp elems)
                     (value-case (car elems) :number)
                     (natp (value-number->get (car elems)))))
        (mv (make-invalid-params-error "Expected a natural number.")
            (value-null)
            counter))
       (counter (update-total (+ (value-number->get (car elems))
                                 (total counter))
                              counter)))
    (mv nil (value-number (total counter)) counter)))

;; A user stobj that is read but not returned, and no params.
(define get-count (counter)
  :stobjs counter
  :returns (mv erp (res valuep))
  (mv nil (value-number (total counter))))

;; Two stobjs, and no params.
(define reset (counter state)
  :stobjs (counter state)
  :returns (mv erp (res valuep) counter state)
  (b* ((counter (update-total 0 counter)))
    (mv nil (value-null) counter state)))

;; No stobjs.
(define pure ((params structuredp))
  (declare (ignorable params))
  :returns (mv erp (res valuep))
  (mv nil (value-true)))

;; Two ordinary inputs, which is unsupported.
(define two-inputs ((params structuredp) x)
  (declare (ignorable params x))
  :returns (mv erp (res valuep))
  (mv nil (value-true)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; User stobj updates persist across requests.

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"bump\",\"params\":[5],\"id\":1}"
 "{\"jsonrpc\":\"2.0\",\"result\":5,\"id\":1}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"bump\",\"params\":[2],\"id\":2}"
 "{\"jsonrpc\":\"2.0\",\"result\":7,\"id\":2}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"get-count\",\"id\":3}"
 "{\"jsonrpc\":\"2.0\",\"result\":7,\"id\":3}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"reset\",\"id\":4}"
 "{\"jsonrpc\":\"2.0\",\"result\":null,\"id\":4}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"get-count\",\"id\":5}"
 "{\"jsonrpc\":\"2.0\",\"result\":0,\"id\":5}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"pure\",\"params\":[],\"id\":6}"
 "{\"jsonrpc\":\"2.0\",\"result\":true,\"id\":6}")

;; Params must be present exactly when the method has an ordinary input.

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"bump\",\"id\":7}"
 "{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Method requires params: bump\"},\"id\":7}")

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"get-count\",\"params\":[],\"id\":8}"
 "{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Method takes no params: get-count\"},\"id\":8}")

;; Unsupported signatures are rejected before evaluation.

(assert-response
 "{\"jsonrpc\":\"2.0\",\"method\":\"two-inputs\",\"params\":[],\"id\":9}"
 "{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32603,\"message\":\"Method has an unsupported signature: two-inputs\"},\"id\":9}")
