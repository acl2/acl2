; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file" :dir :system)

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

(fty::deftagsum structured
  (:array ((elements value-list)))
  (:object ((members member-list)))
  :pred structuredp)

(defirrelevant irr-structured
  :type structuredp
  :body (make-structured-array :elements nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; request:
;  - method: the name of the method to be invoked
;  - params-presentp: whether the params are present
;  - params: a structured JSON value (array or object)
;  - notificationp: true if no id provided
;  - id: the request id 
(fty::defprod request
  ((method string)
   (params-presentp bool)
   (params structured)
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
(fty::defprod error ; change name (error and error1 both taken)
  ((code int)
   (message string)
   (data value-option))
  :pred errorp)

; request+error: contains a request and an error
(fty::deftagsum request+error
  (:request ((get request)))
  (:error ((get error)))
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
                      :params (irr-structured)
                      :notificationp nil
                      :id (irr-id)))

(defirrelevant irr-error
  :type errorp
  :body (make-error :code 0 :message "" :data nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-parse-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32700 :message msg :data nil))

(define make-invalid-request-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32600 :message msg :data nil))

(define make-method-not-found-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32601 :message msg :data nil))

(define make-invalid-params-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32602 :message msg :data nil))

(define make-internal-error ((msg stringp))
  :returns (err errorp)
  (make-error :code -32603 :message msg :data nil))

; takes in a JSON object and extracts its "id" field
; returns:
;  - has-id: true if the "id" field is present
;  - is-valid: true if either the "id" field is not present or it is present and
; of the correct type
;  - id: the id
(define parse-rpc-id ((obj valuep))
  :guard (value-case obj :object)
  :returns (mv (has-id booleanp) (is-valid booleanp) (id idp))
  (b* ((id-val? (object-member-value? "id" obj))
       ((unless id-val?)
        (mv nil t (id-null)))
       (id-val id-val?)
       ((when (value-case id-val :string))
        (mv t t (id-string (value-string->get id-val))))
       ((when (and (value-case id-val :number)
                   (rationalp (value-number->get id-val))))
        (mv t t (id-number (value-number->get id-val))))
       ((when (value-case id-val :null))
        (mv t t (id-null))))
    (mv t nil (id-null))))

; takes in a JSON value and tries to parse it into a request+error
(define parse-rpc-request ((val valuep))
  :returns (mv (id idp) (req+err request+errorp))
  (b* (((unless (value-case val :object))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error "Request must be a JSON object"))))
       (jsonrpc-val? (object-member-value? "jsonrpc" val))
       ((unless (and jsonrpc-val?
                     (value-case jsonrpc-val? :string)
                     (equal (value-string->get jsonrpc-val?) "2.0")))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Missing or invalid \"jsonrpc\" field; must be \"2.0\""))))
       (method-val? (object-member-value? "method" val))
       ((unless (and method-val?
                     (value-case method-val? :string)))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Missing or invalid \"method\" field; must be a string"))))
       (method (value-string->get method-val?))
       (params-presentp (object-has-member-p "params" val))
       (params-val? (and params-presentp 
                         (object-member-value? "params" val)))
       ((when (and params-val?
                   (not (value-case params-val? :array))
                   (not (value-case params-val? :object))))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "\"params\" must be an array or object"))))
       (params (if params-val?
                   (if (equal (value-kind params-val?)
                              :array)
                       (make-structured-array
                        :elements
                        (value-array->elements params-val?))
                     (make-structured-object
                      :members
                      (value-object->members params-val?)))
                 (irr-structured)))
       ((mv has-id is-valid id-val) (parse-rpc-id val))
       ((unless is-valid)
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "\"id\" must either be a number, string, or null"))))
       (notificationp (not has-id)))
    (mv id-val
        (request+error-request
         (make-request :method method
                       :params-presentp params-presentp
                       :params params
                       :notificationp notificationp
                       :id id-val)))))

; takes in a JSON array and tries to parse it into an id-request+error-alist
(define parse-rpc-requests ((vals value-listp))
  :returns (id-req+err-alist id-request+error-alistp)
  (b* (((when (endp vals)) nil)
       ((mv id req+err) (parse-rpc-request (car vals))))
    (cons (cons id req+err)
          (parse-rpc-requests (cdr vals)))))

; takes in a string and tries to parse it into an id-request-error-alist
(define parse-json-rpc ((msg stringp))
  :returns (id-req+err-alist id-request+error-alistp)
  (b* (((mv erp parsed) (parse-string-as-json msg))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to parse JSON")))))
       ((mv erp value) (parsed-to-value parsed))
       ((when erp)
        (list (cons (id-null)
                    (request+error-error
                     (make-parse-error "Failed to convert parsed JSON")))))
       ((when (value-case value :array))
        (b* ((elems (value-array->elements value))
             ((when (endp elems))
              (list (cons (id-null)
                          (request+error-error
                           (make-invalid-request-error 
                            "Batch request array must not be empty"))))))
          (parse-rpc-requests elems)))
       ((when (value-case value :object))
        (b* (((mv id req+err) (parse-rpc-request value)))
          (list (cons id req+err)))))
    (list (cons (id-null)
                (request+error-error
                 (make-invalid-request-error 
                  "Top-level JSON value must be an object or array"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section deals with converting an ACL2 JSON value to a JSON string

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
    (concatenate 'string 
                 (json-escape-char (car chars))
                 (json-escape-string-chars (cdr chars)))))

(define json-escape-string ((s stringp))
  :returns (escaped stringp)
  (json-escape-string-chars (coerce s 'list)))

(define rational-to-json-string ((r rationalp))
  :returns (s stringp)
  (if (integerp r)
      (if (< r 0)
          (string-append "-" (nat-to-string (- r)))
        (nat-to-string r))
    (concatenate 'string 
                 (if (< (numerator r) 0) "-" "")
                 (nat-to-string (abs (numerator r)))
                 "/" 
                 (nat-to-string (denominator r)))))

(defines value-to-json-string

  (define value-to-json-string ((val valuep))
    :returns (s stringp)
    :measure (value-count val)
    (value-case val
      :null "null"
      :true "true"
      :false "false"
      :number (rational-to-json-string val.get)
      :string (concatenate 'string 
                           "\"" 
                           (json-escape-string val.get) 
                           "\"")
      :array (concatenate 'string 
                          "[" 
                          (value-list-to-json-string val.elements)
                          "]")
      :object (concatenate 'string 
                           "{" 
                           (member-list-to-json-string val.members)
                           "}")))

  (define value-list-to-json-string ((vals value-listp))
    :returns (s stringp)
    :measure (value-list-count vals)
    (cond ((endp vals) "")
          ((endp (cdr vals)) (value-to-json-string (car vals)))
          (t 
           (concatenate 'string
                        (value-to-json-string (car vals))
                        "," 
                        (value-list-to-json-string (cdr vals))))))

  (define member-list-to-json-string ((members member-listp))
    :returns (s stringp)
    :measure (member-list-count members)
    (if (endp members)
        ""
      (b* ((m (car members))
           (entry (concatenate 'string
                               "\""
                               (json-escape-string (member->name m))
                               "\":"
                               (value-to-json-string (member->value m)))))
        (if (endp (cdr members))
            entry
          (concatenate 'string 
                       entry 
                       "," 
                       (member-list-to-json-string (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section deals with building responses

(define id-to-json-value ((id idp))
  :returns (val valuep)
  (id-case id
    :string  (value-string id.get)
    :number (value-number id.get)
    :null    (value-null)))

(define make-success-response ((id idp) (result valuep))
  :returns (val valuep)
  (value-object
   (list (make-member :name "jsonrpc" :value (value-string "2.0"))
         (make-member :name "result"  :value result)
         (make-member :name "id"      :value (id-to-json-value id)))))

(define make-error-response ((id idp) (err errorp))
  :returns (val valuep)
  (b* ((error-obj-members
        (append (list (make-member :name "code"
                                         :value (value-number
                                                 (error->code err)))
                      (make-member :name "message"
                                         :value (value-string
                                                 (error->message err))))
                (if (error->data err)
                    (list (make-member :name "data"
                                             :value (error->data err)))
                  nil))))
    (value-object
     (list (make-member :name "jsonrpc"
                              :value (value-string "2.0"))
           (make-member :name "error"
                              :value (value-object error-obj-members))
           (make-member :name "id"
                              :value (id-to-json-value id))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(defines json-value-to-lisp-value

  (define json-value-to-lisp-value ((val json::valuep))
    :measure (json::value-count val)
    (json::value-case val
      :null   nil
      :true   t
      :false  nil
      :number val.get
      :string val.get
      :array  (json-value-list-to-lisp-values val.elements)
      :object (json-member-list-to-lisp-values val.members)))

  (define json-value-list-to-lisp-values ((vals json::value-listp))
    :returns (lisp-vals true-listp)
    :measure (json::value-list-count vals)
    (if (endp vals)
        nil
      (cons (json-value-to-lisp-value (car vals))
            (json-value-list-to-lisp-values (cdr vals)))))

  (define json-member-list-to-lisp-values ((members json::member-listp))
    :returns (lisp-vals alistp)
    :measure (json::member-list-count members)
    (if (endp members)
        nil
      (b* ((m (car members))
           (key (json::member->name m))
           (val (json-value-to-lisp-value (json::member->value m)))
           (rest (json-member-list-to-lisp-values (cdr members))))
        (cons (cons key val) rest)))))

|#

; converts a member list into a keyword-argument list
(define json-member-list-to-lisp-params ((members member-listp))
  :returns (params true-listp)
  (if (endp members)
      nil
    (b* ((m (car members))
         (key (intern (string-upcase (member->name m)) "KEYWORD"))
         (val (member->value m))
         (rest (json-member-list-to-lisp-params (cdr members))))
      (cons key (cons val rest)))))

; converts the json params to an appropriate params list
(define json-params-to-lisp-params ((params structuredp))
  :returns (lisp-params true-listp)
  (if (equal (structured-kind params) :array)
      (structured-array->elements params)
    (json-member-list-to-lisp-params (structured-object->members params))))

(define dispatch-request ((req requestp) ctx state)
  :mode :program
  :stobjs state
  (b* ((method-sym
        (intern-in-package-of-symbol (string-upcase (request->method req))
                                     (pkg-witness "JSONRPC")))
       (form (if (not (request->params-presentp req))
                 `(,method-sym state)
               `(,method-sym ,@(kwote-lst (json-params-to-lisp-params
                                           (request->params req)))
                             state)))
       ((mv erp result state)
        (trans-eval-error-triple form ctx state)))
    (mv erp result state)))


;; NOTE: should process-one and process-all attach the state to its outputs?
(define process-one ((id idp) (val request+errorp) ctx state)
  :mode :program
  :stobjs state
  (request+error-case val
    :error (mv (make-error-response id val.get) state)
    :request
    (b* ((req val.get)
         ((when (request->notificationp req)) 
          (mv nil state))
         ((mv erp output state)
          (dispatch-request req ctx state))
         (error-val (and erp
                         (if (errorp erp)
                             erp
                           (make-internal-error "Internal error"))))
         ((when erp)
          (mv (make-error-response id error-val) state)))
      (mv (make-success-response id output) state))))

(define process-all ((pairs id-request+error-alistp) ctx state)
  :mode :program
  :stobjs state
  (if (endp pairs)
      (mv nil state)
    (b* (((mv resp state) (process-one (caar pairs) (cdar pairs) ctx state))
         ((mv rest state) (process-all (cdr pairs) ctx state)))
      (if resp 
          (mv (cons resp rest) state) 
        (mv rest state)))))

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
              (batchp (value-array responses))
              (t (car responses))))
       ((when response-val)
        (b* ((response (list (value-to-json-string response-val)))
             ((mv erp state)
              (write-strings-to-file response 
                                     output-file
                                     'process-json-rpc-file
                                     state))
             ((when erp)
              (mv t "[ERROR] error when writing response to file" state)))
          (mv erp "[SUCCESS] response written to output file" state))))
    (mv nil "[NOTICE] no responses were generated" state)))

