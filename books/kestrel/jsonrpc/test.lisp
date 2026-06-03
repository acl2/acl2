(in-package "JSONRPC")

(include-book "temp")

(defun subtract (x y)
  (declare (xargs :guard (and (json::valuep x)
                              (json::valuep y))))
  (b* (((unless (equal (json::value-kind x) 'number))
        (mv t (json::value-null)))
       (x-val (json::value-number->get x))
       (y-val (json::value-number->get y))
       (res-val (- x-val y-val))
       (res (json::make-value-number res-val)))
    (mv nil res)))

(process-json-rpc-file "json-request.txt"
                       "json-response.txt"
                       (w state))
