; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json-to-string
  :parents (jsonrpc)
  :short "Serializing JSON values to strings."
  :long "<p>These functions serialize @(see valuep) objects to JSON strings
  suitable for writing to files or sending over a transport. The main function
  is @(see value-to-json-string). String values are properly escaped per
  RFC 4627. Rational numbers that are integers are printed without a decimal
  point; non-integer rationals are printed as @('numerator/denominator').</p>"
  :order-subtopics t
  :default-parent t)

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
