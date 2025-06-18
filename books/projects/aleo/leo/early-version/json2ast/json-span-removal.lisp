; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../definition/abstract-syntax")

(include-book "std/basic/two-nats-measure" :dir :system)

;; fixtypes for representing JSON structures
(include-book "kestrel/json/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json2ast
  :parents (early-version)
  :short "Build Leo abstract syntax trees from Leo AST JSON files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo abstract syntax trees are represented in many forms.  Here we discuss
  the steps in which they are translated from JSON files to ACL2 fixtypes.
  We usually omit the term \"Leo abstract syntax trees\" for brevity.")
   (xdoc::p
    "Currently we call @('jsonfile-to-formal') as the entry point.
     It calls @('jsonfile-to-spanfree'), which handles the first few steps,
     followed by @('j2f-file'), which handles the last step.")
   (xdoc::p
    "A JSON file is parsed into an ACL2 JSON list structure using
  @('acl2::parse-file-as-json').  All further processing is done in ACL2,
  so we will omit that term.")
   (xdoc::p
    "Then the JSON list structure is translated to a
     <see topic='@(url json::abstract-syntax)'>JSON abstract syntax</see>
    structure using @(tsee json::parsed-to-value).
  By a <it>JSON abstract syntax structure</it> we mean a value of type @('json::value') that
  represents the JSON that was seen in the file.  At this point ACL2 does not
  know anything about the meaning of this value as a Leo program.")
   (xdoc::p
    "Operating on the JSON abstract syntax, we remove span objects using
  @(tsee json-remove-spans-in-value).
  For more details see @(tsee json-fixtype-span-removal).")
   (xdoc::p
    "Finally, the spanfree JSON abstract syntax is translated to
     <see topic='@(url abstract-syntax)'>Leo abstract syntax</see>
     using @('j2f-file').")
   (xdoc::p
    "The result is a Leo abstract syntax tree represented as an ACL2 value
     of type @(tsee file)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Nomenclature note:
;; the lexical elements of JSON are called value, array, object, member, number, etc.
;; When referring to these in documentation, we call them "JSON value", etc,
;; or leave off "JSON" if it is obvious.

(define json-value-is-core-span-object-p ((value (json::valuep value)))
  :returns (yes/no booleanp)
  :short "Checks if this json value looks like a span object."
  :long
  (xdoc::topstring
   (xdoc::p
    "A span object is an artifact added by a parser to an AST node that
     describes the location and contents of the text parsed to create
     that AST node.")
   (xdoc::p
    "Currently, we observe span objects have exactly two members,
     with names @('lo') and @('hi').")
;     with names @('line_start'), @('line_stop'), @('col_start'), @('col_stop'),
;     and @('path').
   (xdoc::p "The positions are indices into the file named by
     the path when the file was parsed---so there is an dependency
     on the file contents.
     As long as these members are present, this predicate will be true.
     Additional members are allowed, to allow for the possibility that
     the parser is extended."))
  (and (json::valuep value)
       (equal (json::value-kind value) :object)
;       (json::object-has-member-p "line_start" value)
;       (json::object-has-member-p "col_start" value)
;       (json::object-has-member-p "line_stop" value)
;       (json::object-has-member-p "col_stop" value)
;       (json::object-has-member-p "path" value)
       (json::object-has-member-p "lo" value)
       (json::object-has-member-p "hi" value)
       ))

(define json-member-is-span-p ((member json::memberp))
  :returns (yes/no booleanp)
  :short "Checks if this json object member looks like a span."
  :long
  (xdoc::topstring
   (xdoc::p
    "We are defining a JSON member as a span if the member name is
     \"span\" and the member value is a JSON value satisfying
     @(tsee json-value-is-core-span-object-p)."))
  (and (json::memberp member)
       (equal "span" (json::member->name member))
       (let ((val (json::member->value member)))
         (and (equal :object (json::value-kind val))
              (json-value-is-core-span-object-p val)))))

(define json-value-is-span-object-p ((value (json::valuep value)))
  :returns (yes/no booleanp)
  :short "Checks if this json value looks like either a span object or a wrapped span object."
  :long
  (xdoc::topstring
   (xdoc::p
    "A span object is an artifact added by a parser to an AST node that
     describes the location and contents of the text parsed to create
     that AST node.")
   (xdoc::p
    "See @(tsee json-value-is-core-span-object-p) for the definition of a span object.")
   (xdoc::p
    "Originally, we observed that the Leo parser added span objects in two places:")
   (xdoc::ol
    (xdoc::li "at the end of a JSON array of values, and")
    (xdoc::li "at the end of a JSON object list of members, in which case
               the span object is wrapped with a single-member object whose
               member name is @('span') and whose member value is the span object"))
   (xdoc::p
    "Subsequently, span removal was added to the Leo compiler.
  There are a few steps to span removal.  It appears the step of regularizing
  span objects @('{\"line_start\": .., ..}') to add a wrapper span object
  @('{\"span\": {\"line_start\": .., ..} }') now happens before the output from the
  @('parser') executable.  We now also recognize such wrapped spans as span
  objects in any context, not just as a member of an object.")
   (xdoc::p
    "See @(tsee json-fixtype-span-removal) for details on how spans are removed."))
  (or (json-value-is-core-span-object-p value)
      (and (json::valuep value)
           (equal (json::value-kind value) :object)
           (let ((object-member-list (json::value-object->members value)))
             (and (equal (len object-member-list) 1)
                  (json-member-is-span-p (first object-member-list)))))))

(defines json-fixtype-span-removal
  :short "Removes spans recursively in a parsed JSON fixtype."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although we have observed a span showing up in a typed AST only
     at the end of an array's values or at the end of an object's members
     (see @(tsee json-value-is-span-object-p)),
     we also remove spans that are not at the end, in case they arise.")
   (xdoc::p
    "In general, we return a similar structure with the spans spliced out.
     However, if the span object is the second value of a JSON array of
     length 2, and if the first value is not a span object, then
     the first value (with substructure spans removed) is lifted up to
     replace the JSON array.
     The rationale for this is that the JSON array was probably created by
     the parser solely to attach the span to the first value and does not carry
     any other meaning."))

  :prepwork
  ((defrule termination-lemma
     (implies (and (json::valuep value)
                   (equal (json::value-kind value) :array))
              (< (json::value-list-count (json::value-array->elements value))
                 (json::value-count value)))
     :rule-classes :linear
     :local t))
  :hints (("Goal" :use termination-lemma))

  (define json-remove-spans-in-value ((value json::valuep))
    :returns (spanfree-json json::valuep)
    :short "Removes span decorations from a JSON value representing an AST."
    (let ((v (json::value-fix value))) ; helps the return type theorems
      (json::value-case v
        :object (json::make-value-object
                 :members (json-remove-spans-in-member-list v.members))
        :array (json-remove-spans-in-array v)
        :number v
        :string v
        :true v
        :false v
        :null v))
    ;; Note on two-nats-measure: 2nd nat must be greater than that for json-remove-spans-in-array
    :measure (two-nats-measure (json::value-count value) 1))

  (define json-remove-spans-in-member-list ((members json::member-listp))
    :returns (spanfree-members json::member-listp)
    :short "Removes spans in a list of object members."
    :long
    (xdoc::topstring
     (xdoc::p
      "Returns a new list of members.  Members that are spans are omitted,
     and members whose member value is an array or object will have spans
     removed from their member value, recursively.  Members whose member
     value is a primitive type will be retained unchanged."))
    (if (endp members)
        nil
      (let ((first-member (first members)))
        (if (json-member-is-span-p first-member)
            (json-remove-spans-in-member-list (rest members))
          (cons (json-remove-spans-in-member first-member)
                (json-remove-spans-in-member-list (rest members))))))
    :measure (two-nats-measure (json::member-list-count members) 0))

  (define json-remove-spans-in-member ((member json::memberp))
    :returns (spanfree-member-value json::memberp)
    :short "If the member value is a composite, returns a new member with the same name but with spans removed from the value."
    ;; NOTE: this should probably not be called when the name is "span" but we should clarify this.
    ;; What if the name is "span" but the value is a different kind of object, or if the names in the object
    ;; differ slightly from the json-member-is-span-p predicate?
    (if (not (json::memberp member))
        (json::member-fix member)
      (json::member (json::member->name member)
                    (json-remove-spans-in-value (json::member->value member))))
    ;; Tip on two-nats-measure: member->value needs to decrease,
    ;; so the 2nd index needs to be greater than any other value
    :measure (two-nats-measure (json::member-count member) 2))

  (define json-remove-spans-in-array ((value (and (json::valuep value)
                                                  (equal (json::value-kind value) :array))))
    :returns (spanfree-new-value json::valuep)
    :short "Returns a new JSON value replacing the JSON array, with any spans spliced out."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each value of the array has its spans removed, and the array is returned.
     If a value is a span, it is removed from the array.
     If, by removing a span value, the array is left with a single value,
     that means the array itself was constructed around the value solely
     to group it with the span, so the array itself is not likely to be
     meaningful for the AST, so the value is returned in place of the array.")
     (xdoc::p
      "See @(tsee json-fixtype-span-removal)."))

    ;; Need to make sure value is an array before calling json::value-array->elements,
    ;; so that the measure conjecture can be proved.
    ;; We just repeat the guard and if not satisified, return an empty array.
    ;; This will not actually get returned but it enables the measure proof.
    (if (not (and (json::valuep value)
                  (equal (json::value-kind value) :array)))
        (json::make-value-array :elements nil)

      (let ((array-element-list (json::value-array->elements value)))
        (if (and (equal (len array-element-list) 2)
                 (not (json-value-is-span-object-p (first array-element-list)))
                 (json-value-is-span-object-p (second array-element-list)))
            ;; return the result of removing spans from the first value
            (json-remove-spans-in-value (first array-element-list))
          (json::make-value-array
           :elements (json-remove-spans-in-value-list array-element-list))))
      )
    :measure (two-nats-measure (json::value-count value) 0))

  (define json-remove-spans-in-value-list ((value-list json::value-listp))
    :returns (spanfree-value-list json::value-listp)
    :short "Removes span decorations from a list of JSON values."
    (if (endp value-list)
        nil
      (if (json-value-is-span-object-p (first value-list))
          (json-remove-spans-in-value-list (rest value-list))
        (cons (json-remove-spans-in-value (first value-list))
              (json-remove-spans-in-value-list (rest value-list))))
      )
    :measure (two-nats-measure (json::value-list-count value-list) 0))

  :verify-guards nil ; done below

  ///
  (verify-guards json-remove-spans-in-value)
  )
