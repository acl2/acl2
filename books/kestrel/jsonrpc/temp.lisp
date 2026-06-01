; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; id: MUST contain either a string, a number, or a null value
(fty::deftagsum id
  (:string ((get string)))
  (:number ((get rational)))
  (:null ())
  :pred idp)

(defirrelevant irr-id
  :type idp
  :body (id-null))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; request:
;  - method: the name of the method to be invoked
;  - params-presentp: whether the params are present
;  - params: MUST either be a JSON array or object, MAY be ommitted
;    + params-arr?: true if params is a JSON array
;    + params-arr: used when params-arr? is true
;    + params-obj: used when params-arr? is false
;  - notificationp: true if no id provided
;  - id: the request id 
(fty::defprod request
  ((method string)
   (params-presentp bool)
   (params-is-arr bool)
   (params-arr json::value-list)
   (params-obj json::member-list)
   (notificationp bool)
   (id id))
  :pred requestp)

; error
;  - code: error code
;    + -32700: Parse error
;    + -32600: Invalid request
;    + -32601: Method not found
;    + -32602: Invalid params
;    + -32603: Internal error
;    + -32000 to -32099: Server error
;  - message: the message string
;  - data: additional info, MAY be ommitted
(fty::defprod error2 ; change name (error and error1 both taken)
  ((code int)
   (message string)
   (data json::value-option))
  :pred error2p)

; request+error: contains a request and an error
(fty::deftagsum request+error
  (:request ((get request)))
  (:error ((get error2)))
  :pred request+errorp)

; id-request+error-alist: mapping ids to request-errors
(fty::defalist id-request+error-alist
    :key-type id
    :val-type request+error
    :true-listp t
    :pred id-request+error-alistp)

(defirrelevant irr-request
  :type requestp
  :body (make-request :method ""
                      :params-presentp nil
                      :params-is-arr t
                      :params-arr nil
                      :params-obj nil
                      :notificationp nil
                      :id (irr-id)))

(defirrelevant irr-error
  :type error2p
  :body (make-error2 :code 0 :message "" :data nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-parse-error ((msg stringp))
  :returns (err error2p)
  (make-error2 :code -32700 :message msg :data nil))

(define make-invalid-request-error ((msg stringp))
  :returns (err error2p)
  (make-error2 :code -32600 :message msg :data nil))

; takes in a JSON object and extracts its "id" field
; returns:
;  - id?: true if the "id" field is present
;  - valid?: true if either the "id" field is not present or it is present and
; of the correct type
(define parse-rpc-id ((obj json::valuep))
  :guard (json::value-case obj :object)
  :returns (mv (has-id booleanp) (is-valid booleanp) (id idp))
  (b* ((id-val? (json::object-member-value? "id" obj))
       ((unless id-val?)
        (mv nil t (id-null)))
       (id-val id-val?)
       ((when (json::value-case id-val :string))
        (mv t t (id-string (json::value-string->get id-val))))
       ((when (and (json::value-case id-val :number)
                   (rationalp (json::value-number->get id-val))))
        (mv t t (id-number (json::value-number->get id-val))))
       ((when (json::value-case id-val :null))
        (mv t t (id-null))))
    (mv t nil (id-null))))

; takes in a JSON value and tries to parse it into a request+error
(define parse-rpc-request ((val json::valuep))
  :returns (mv (id idp) (req-err request+errorp))
  (b* (((unless (json::value-case val :object))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "Request must be a JSON object"))))
       (jsonrpc-val? (json::object-member-value? "jsonrpc" val))
       ((unless (and jsonrpc-val?
                     (json::value-case jsonrpc-val? :string)
                     (equal (json::value-string->get jsonrpc-val?) "2.0")))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "Missing or invalid \"jsonrpc\" field; must be \"2.0\""))))
       (method-val? (json::object-member-value? "method" val))
       ((unless (and method-val?
                     (json::value-case method-val? :string)))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "Missing or invalid \"method\" field; must be a string"))))
       (method (json::value-string->get method-val?))
       (params-presentp (json::object-has-member-p "params" val))
       (params-val? (and params-presentp (json::object-member-value? "params" val)))
       ((when (and params-val?
                   (not (json::value-case params-val? :array))
                   (not (json::value-case params-val? :object))))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "\"params\" must be an array or object"))))
       (params-is-arr (and params-val? (json::value-case params-val? :array)))
       (params-arr (if params-is-arr params-val? (json::value-null)))
       (params-obj (if params-is-arr (json::value-null) params-val?))
       ((mv has-id is-valid id-val) (parse-rpc-id val))
       ((unless is-valid)
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Invalid \"id\" field; must either be a number, string, or null"))))
       (notificationp (not has-id)))
    (mv id-val
        (request+error-request
         (make-request :method method
                       :params-presentp params-presentp
                       :params-is-arr params-is-arr
                       :params-arr params-arr
                       :params-obj params-obj
                       :notificationp notificationp
                       :id id-val))))
  :verify-guards :after-returns)

(define parse-rpc-elements ((elems json::value-listp))
  (if (endp elems)
      nil
    (cons (parse-rpc-element (car elems))
          (parse-rpc-elements (cdr elems)))))

(define parse-json-rpc ((msg stringp))
  (b* (((mv erp parsed) (parse-string-as-json msg))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to parse JSON")))))
       ((mv erp value) (json::parsed-to-value parsed))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to convert parsed JSON")))))
       ((when (json::value-case value :array))
        (b* ((elems (json::value-array->elements value))
             ((when (endp elems))
              (list (cons (id-null)
                          (request+error-error
                           (make-invalid-request-error "Batch request array must not be empty"))))))
          (parse-rpc-elements elems)))
       ((when (json::value-case value :object))
        (list (parse-rpc-element value))))
    (list (cons (id-null)
                (request+error-error
                 (make-invalid-request-error "Top-level JSON value must be an object or array"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-escape-char ((ch characterp))
  :returns (s stringp)
  (case ch
    (#\" "\\\"")
    (#\\ "\\\\")
    (#\Newline "\\n")
    (#\Return "\\r")
    (#\Tab "\\t")
    (otherwise (string ch))))

(define json-escape-string-chars ((chars character-listp))
  :returns (s stringp)
  (if (endp chars)
      ""
    (string-append (json-escape-char (car chars))
                   (json-escape-string-chars (cdr chars)))))

(define json-escape-string ((s stringp))
  :returns (escaped stringp)
  (json-escape-string-chars (coerce s 'list)))

(define rational-to-json-string ((r rationalp))
  :returns (s stringp)
  (if (integerp r)
      (coerce (explode-atom r 10) 'string)
    (string-append (coerce (explode-atom (numerator r) 10) 'string)
                   (string-append "e-"
                                  (coerce (explode-atom (denominator r) 10) 'string)))))

(defines value-to-json-string

  (define value-to-json-string ((val json::valuep))
    :returns (s stringp)
    :measure (two-nats-measure (acl2-count val) 0)
    (json::value-case val
      :null    "null"
      :true    "true"
      :false   "false"
      :number  (rational-to-json-string val.get)
      :string  (string-append "\"" (string-append (json-escape-string val.get) "\""))
      :array   (string-append "[" (string-append (value-list-to-json-string val.elements) "]"))
      :object  (string-append "{" (string-append (member-list-to-json-string val.members) "}"))))

  (define value-list-to-json-string ((vals json::value-listp))
    :returns (s stringp)
    :measure (two-nats-measure (acl2-count vals) 0)
    (cond ((endp vals) "")
          ((endp (cdr vals)) (value-to-json-string (car vals)))
          (t (string-append (value-to-json-string (car vals))
                            (string-append "," (value-list-to-json-string (cdr vals)))))))

  (define member-list-to-json-string ((members json::member-listp))
    :returns (s stringp)
    :measure (two-nats-measure (acl2-count members) 0)
    (if (endp members)
        ""
      (b* ((m (car members))
           (entry (string-append
                   (string-append "\"" (string-append (json-escape-string (json::member->name m)) "\""))
                   (string-append ":" (value-to-json-string (json::member->value m))))))
        (if (endp (cdr members))
            entry
          (string-append entry (string-append "," (member-list-to-json-string (cdr members)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-to-json-value ((id idp))
  :returns (val json::valuep)
  (id-case id
    :string  (json::value-string id.get)
    :integer (json::value-number id.get)
    :null    (json::value-null)))

(define make-success-response ((id idp) (result json::valuep))
  :returns (val json::valuep)
  (json::value-object
   (list (json::make-member :name "jsonrpc" :value (json::value-string "2.0"))
         (json::make-member :name "result"  :value result)
         (json::make-member :name "id"      :value (id-to-json-value id)))))

(define make-error-response ((id idp) (err errorp))
  :returns (val json::valuep)
  (b* ((error-obj-members
        (append (list (json::make-member :name "code"
                                        :value (json::value-number (error->code err)))
                      (json::make-member :name "message"
                                        :value (json::value-string (error->message err))))
                (if (error->data err)
                    (list (json::make-member :name "data"
                                            :value (error->data err)))
                  nil))))
    (json::value-object
     (list (json::make-member :name "jsonrpc" :value (json::value-string "2.0"))
           (json::make-member :name "error"   :value (json::value-object error-obj-members))
           (json::make-member :name "id"      :value (id-to-json-value id))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dispatch-request ((req requestp) ctx state)
  :mode :program
  :stobjs state
  (b* ((method-sym (intern (string-upcase (request->method req)) "JSONRPC"))
       (form `(,method-sym
               ',(request->params-presentp req)
               ',(request->params req)
               ',(request->notificationp req)
               ',(request->id req)
               state)))
    (trans-eval-error-triple form ctx state)))

(define process-one (pair ctx state)
  :mode :program
  :stobjs state
  (b* ((id  (car pair))
       (val (cdr pair)))
    (request+error-case val
      :error
      (mv (make-error-response id val.get) state)
      :request
      (b* ((req val.get)
           ((when (request->notificationp req))
            (mv nil state))
           ((mv erp result state)
            (dispatch-request req ctx state))
           ((when erp)
            (mv (make-error-response
                 id
                 (make-error :code -32603
                             :message "Internal error"
                             :data (json::value-string (fmt-to-string "~@0" (list (cons #\0 erp))))))
                state)))
        (mv (make-success-response id result) state)))))

(define process-all (pairs ctx state)
  :mode :program
  :stobjs state
  (if (endp pairs)
      (mv nil state)
    (b* (((mv resp state) (process-one (car pairs) ctx state))
         ((mv rest state) (process-all (cdr pairs) ctx state)))
      (mv (if resp (cons resp rest) rest) state))))

(define write-string-to-file ((filename stringp) (str stringp) state)
  :mode :program
  :stobjs state
  (mv-let (chan state)
    (open-output-channel filename :character state)
    (if (null chan)
        (progn$ (er hard? 'write-string-to-file "Could not open output file: ~x0" filename)
                state)
      (let ((state (princ$ str chan state)))
        (close-output-channel chan state)))))

(define process-json-rpc-file ((input-file stringp) (output-file stringp) state)
  :mode :program
  :stobjs state
  (b* (((mv chars state) (read-file-into-character-list-safe input-file state))
       (msg (coerce chars 'string))
       (alist (parse-json-rpc msg))
       (batchp (> (len alist) 1))
       ((mv responses state) (process-all alist 'process-json-rpc-file state))
       (response-val
        (cond ((endp responses) nil)
              (batchp (json::value-array responses))
              (t (car responses))))
       (state
        (if response-val
            (write-string-to-file output-file (value-to-json-string response-val) state)
          state)))
    (mv nil state)))

