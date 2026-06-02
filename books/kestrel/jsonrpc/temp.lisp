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
  :returns (mv (id idp) (req+err request+errorp))
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
             (make-invalid-request-error 
              "Missing or invalid \"jsonrpc\" field; must be \"2.0\""))))
       (method-val? (json::object-member-value? "method" val))
       ((unless (and method-val?
                     (json::value-case method-val? :string)))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "Missing or invalid \"method\" field; must be a string"))))
       (method (json::value-string->get method-val?))
       (params-presentp (json::object-has-member-p "params" val))
       (params-val? (and params-presentp 
                         (json::object-member-value? "params" val)))
       ((when (and params-val?
                   (not (json::value-case params-val? :array))
                   (not (json::value-case params-val? :object))))
        (mv (id-null)
            (request+error-error
             (make-invalid-request-error 
              "\"params\" must be an array or object"))))
       (params-is-arr (and params-val? (json::value-case params-val? :array)))
       (params-arr (and params-val? params-is-arr 
                        (json::value-array->elements params-val?)))
       (params-obj (and params-val? (not params-is-arr) 
                        (json::value-object->members params-val?)))
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
                       :params-is-arr params-is-arr
                       :params-arr params-arr
                       :params-obj params-obj
                       :notificationp notificationp
                       :id id-val)))))

; takes in a JSON array and tries to parse it into an id-request+error-alist
(define parse-rpc-requests ((vals json::value-listp))
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
                           (make-invalid-request-error 
                            "Batch request array must not be empty"))))))
          (parse-rpc-requests elems)))
       ((when (json::value-case value :object))
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

  (define value-to-json-string ((val json::valuep))
    :returns (s stringp)
    :measure (json::value-count val)
    (json::value-case val
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

  (define value-list-to-json-string ((vals json::value-listp))
    :returns (s stringp)
    :measure (json::value-list-count vals)
    (cond ((endp vals) "")
          ((endp (cdr vals)) (value-to-json-string (car vals)))
          (t 
           (concatenate 'string
                        (value-to-json-string (car vals))
                        "," 
                        (value-list-to-json-string (cdr vals))))))

  (define member-list-to-json-string ((members json::member-listp))
    :returns (s stringp)
    :measure (json::member-list-count members)
    (if (endp members)
        ""
      (b* ((m (car members))
           (entry (concatenate 'string
                               "\""
                               (json-escape-string (json::member->name m))
                               "\":"
                               (value-to-json-string (json::member->value m)))))
        (if (endp (cdr members))
            entry
          (concatenate 'string 
                       entry 
                       "," 
                       (member-list-to-json-string (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section deals with building responses

(define id-to-json-value ((id idp))
  :returns (val json::valuep)
  (id-case id
    :string  (json::value-string id.get)
    :number (json::value-number id.get)
    :null    (json::value-null)))

(define make-success-response ((id idp) (result json::valuep))
  :returns (val json::valuep)
  (json::value-object
   (list (json::make-member :name "jsonrpc" :value (json::value-string "2.0"))
         (json::make-member :name "result"  :value result)
         (json::make-member :name "id"      :value (id-to-json-value id)))))

(define make-error-response ((id idp) (err error2p))
  :returns (val json::valuep)
  (b* ((error-obj-members
        (append (list (json::make-member :name "code"
                                        :value (json::value-number (error2->code err)))
                      (json::make-member :name "message"
                                        :value (json::value-string (error2->message err))))
                (if (error2->data err)
                    (list (json::make-member :name "data"
                                            :value (error2->data err)))
                  nil))))
    (json::value-object
     (list (json::make-member :name "jsonrpc" :value (json::value-string "2.0"))
           (json::make-member :name "error"   :value (json::value-object error-obj-members))
           (json::make-member :name "id"      :value (id-to-json-value id))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define json-value-list-to-lisp-params ((vals json::value-listp))
  :returns (params true-listp)
  (json-value-list-to-lisp-values vals))

(define json-member-list-to-lisp-params ((members json::member-listp))
  :returns (params true-listp)
  (if (endp members)
      nil
    (b* ((m (car members))
         (key (intern (string-upcase (json::member->name m)) "KEYWORD"))
         (val (json-value-to-lisp-value (json::member->value m)))
         (rest (json-member-list-to-lisp-params (cdr members))))
      (cons key (cons val rest)))))

;; NOTE: right now, dispatch is sending the raw result from the method function
;; to make-success-response, which requires a JSON value. There are a few
;; issues with this. If we want to convert lisp value to JSON value, there's a
;; lot of subtleties, one of which is settling what nil is (null, false, empty
;; list). Another way is to limit requests to functions defined inside the
;; jsonrpc package; we can then enforce that any function has to return a JSON
;; value. Will circle back

(define dispatch-request ((req requestp) ctx state)
  :mode :program
  :stobjs state
  (b* (;; NOTE: not sure what the convention is here. This would probably be a
       ;; local function so don't know if type checking is necessary
;       ((unless (requestp req)) (raise "The REQ input must be a request"))
       (method-sym (intern (string-upcase (request->method req)) "ACL2"))
       (form (cond
              ((not (request->params-presentp req))
               `(,method-sym))
              ((request->params-is-arr req)
               `(,method-sym ,@(kwote-lst (json-value-list-to-lisp-params
                                           (request->params-arr req)))))
              (t
               `(,method-sym ,@(kwote-lst (json-member-list-to-lisp-params
                                           (request->params-obj req))))))))
    (trans-eval form ctx state t)))


;; NOTE: shoulde process-one and process-all attach the state to its outputs
(define process-one ((id idp) (val request+errorp) ctx state)
  :mode :program
  :stobjs state
  (request+error-case val
    :error (mv (make-error-response id val.get) state)
    :request (b* (;; NOTE: same comments as the previous function
;                  ((unless (idp id)) (raise "The ID input must be an id"))
;                  ((unless (request+errorp req+err))
;                   (raise "The REQ+ERR input must be a request+error"))
                  (req val.get)
                  ((when (request->notificationp req)) 
                   (mv nil state))
                  ;; NOTE: trans-eval returns an error triple where the value
                  ;; component is (stobjs . value), so we need to extract the
                  ;; result by using (cdr result)
                  ((mv erp result state)
                   (dispatch-request req ctx state))
                  ((when erp)
                   (mv (make-error-response
                        id
                        (make-error2 :code -32603
                                :message "Internal error"
                                :data nil)) ; TODO: return better error messages
                       state)))
               (mv (make-success-response id (cdr result)) state))))

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
              (batchp (json::value-array responses))
              (t (car responses))))
       ;; NOTE: very ugly here, need to fix the below case
       ((mv & state)
        (if response-val
            (write-strings-to-file (list (value-to-json-string response-val)) 
                                   output-file
                                   'process-json-rpc-file
                                   state)
          (mv nil state))))
    (mv nil state)))

