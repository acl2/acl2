(in-package "JSONRPC")

(include-book "temp")

(defun subtract (x y state)
  (declare (xargs :guard (and (json::valuep x)
                              (json::valuep y))
                  :mode :program
                  :stobjs state))
  (b* (((unless (equal (value-kind x) :number))
        (mv (make-invalid-params-error
             "Invalid first argument")
            (value-null)
            state))
       ((unless (equal (value-kind y) :number))
        (mv (make-invalid-params-error
             "Invalid second argument")
            (value-null)
            state))
       (x-val (value-number->get x))
       (y-val (value-number->get y))
       (res-val (- x-val y-val))
       (res (make-value-number :get res-val)))
    ;; put error in erp
    (mv nil res state)))

#|

(process-json-rpc-file "json-request.txt"
                       "json-response.txt"
                       state)

|#
