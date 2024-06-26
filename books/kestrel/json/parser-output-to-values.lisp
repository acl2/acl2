; JSON Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-output-to-values
  :parents (json)
  :short "A translator
          from the JSON parser's output to our model of JSON values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The JSON parser in @('kestrel/json-parser/')
     produces output that is slightly different from the "
    (xdoc::seetopic "values" "the JSON values")
    " formalized in this JSON library;
     in particular, the parser's output is not a fixtype.")
   (xdoc::p
    "Thus, here we provide a translator
     from the parser's output to the JSON values.
     Since at the time that this translator was first written
     the parser did not include a type (i.e. recognizer) for its output,
     the translator is defined over all possible ACL2 values,
     but it returns an error if given something
     that does not belong to the parser's implicit output type.
     After that, recognizers have been added in @('kestrel/json-parser/'),
     so we plan to improve this translator to take them into account."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines parsed-to-value
  :short "Translate the JSON values generated by the parser
          to the corresponding fixtype JSON values."

  (define parsed-to-value (x)
    :returns (mv (erp booleanp)
                 (value valuep))
    (cond ((eq x :null) (mv nil (value-null)))
          ((eq x :true) (mv nil (value-true)))
          ((eq x :false) (mv nil (value-false)))
          ((stringp x) (mv nil (value-string x)))
          ((rationalp x) (mv nil (value-number x)))
          ((consp x)
           (cond ((and (eq (car x) :object)
                       (consp (cdr x))
                       (null (cddr x)))
                  (b* (((mv erp members) (parsed-to-member-list (cadr x))))
                    (if erp
                        (mv erp (irr-value))
                      (mv nil (value-object members)))))
                 ((and (eq (car x) :array)
                       (consp (cdr x))
                       (null (cddr x)))
                  (b* (((mv erp values) (parsed-to-value-list (cadr x))))
                    (if erp
                        (mv erp (irr-value))
                      (mv nil (value-array values)))))
                 (t (mv t (irr-value)))))
          (t (mv t (irr-value)))))

  (define parsed-to-value-list (x)
    :returns (mv (erp booleanp)
                 (values value-listp))
    (b* (((when (atom x)) (if (null x)
                              (mv nil nil)
                            (mv t nil)))
         ((mv erp value) (parsed-to-value (car x)))
         ((when erp) (mv erp nil))
         ((mv erp values) (parsed-to-value-list (cdr x)))
         ((when erp) (mv erp nil)))
      (mv nil (cons value values))))

  (define parsed-to-member (x)
    :returns (mv (erp booleanp)
                 (member memberp))
    (if (and (consp x)
             (stringp (car x)))
        (b* (((mv erp value) (parsed-to-value (cdr x))))
          (if erp
              (mv erp (irr-member))
            (mv nil (member (car x) value))))
      (mv t (irr-member))))

  (define parsed-to-member-list (x)
    :returns (mv (erp booleanp)
                 (members member-listp))
    (b* (((when (atom x)) (if (null x)
                              (mv nil nil)
                            (mv t nil)))
         ((mv erp member) (parsed-to-member (car x)))
         ((when erp) (mv erp nil))
         ((mv erp members) (parsed-to-member-list (cdr x)))
         ((when erp) (mv erp nil)))
      (mv nil (cons member members))))

  :verify-guards nil ; done below
  ///
  (verify-guards parsed-to-value))
