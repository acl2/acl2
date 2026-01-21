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

;; fixtypes for representing JSON structures
(include-book "kestrel/json/top" :dir :system)

;; Spans need to be removed before the code here is applied,
;; but how we organize that code is TBD.
;; (Note, JSON file to s-exp parsing falls in the same category)
;; This include-book is not needed specifically for certification of this book,
;; but it does define the xdoc json2ast so to get a good manual we need it here.
(include-book "json-span-removal")

;; Leo formal AST definition
(include-book "../definition/abstract-syntax")
;; Consider removing this and the currently unused calls to leo-early::make-format-string in this file:
(include-book "../definition/format-strings")

(include-book "std/strings/decimal" :dir :system) ; for str::strval
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/strtok-bang" :dir :system)

;; For UTF-8 to UTF-32
(include-book "unicode/utf8-decode" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporarily put this file in program mode, due to performance problem with certifying it.
;; EM 2021-08-29
(acl2::program)
;; The only other change needed to put this file into program mode is:
;; * In :returns type declarations that are in a define form that are in a
;;   defines mutual-recursion, the types need to be put in string quotes.
;; Other things that we thought we might need but were not needed:
;; * comment out (verify-guards ..) calls
;; * (acl2::set-bogus-mutual-recursion-ok t)
;; * (acl2::set-bogus-measure-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The parent is defined in json-span-removal.lisp
;; NOTE: set-default-parents doesn't seem to work in my use case (EM);
;; therefore explicit parents are set on documented items below.
;; The documentation is a work in progress and will be restructured.
(local (xdoc::set-default-parents json2ast))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (enable json::value-kind
                   ;; all the light-ast-check functions used by json::pattern
                   json::jnullp json::jtruep json::jfalsep
                   json::jstringp json::jnumberp
                   json::top-jarrayp json::top-jobjectp
                   json::top-jmemberp json::top-jmember-listp))

;; These are disabled for performance.  Can be re-enabled if needed.
;; These were found by accumulated persistence.
;; These are the top 11 that had zero "useful" usages when loading this file.
(local (in-theory (disable ACL2::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP
                           TRUE-LIST-LISTP
                           SET::SETS-ARE-TRUE-LISTS-CHEAP
                           ACL2::TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP
                           DEFAULT-CDR
                           SET::SETP-TYPE
                           leo-early::SETP-WHEN-TYPE-OPTION-SETP
                           OMAP::SETP-WHEN-MAPP
                           SETP-WHEN-IDENTIFIER-SETP
                           SET::NONEMPTY-MEANS-SET
                           ACL2::TRUE-LIST-LISTP-WHEN-NOT-CONSP)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JSON fty AST to Formal AST

;; Structure of file:
;; * Define small detectors and helpers outside the defines.
;; * Main mutual recursion
;; * Top-level function (program).


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define small detectors and helpers outside the defines.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; b* binders to lessen the verbosity of code that walks the JSON tree

;; Note: if we put these into the JSON abstract syntax model,
;; we might also want to grab Eric M's explanation of it
;; from his aleo-notes/explain-bstar-binders.txt

(acl2::def-b*-binder require-json-member-with-name ; args are (j name errobj)
  :body
  (cond ((and (eql (len acl2::args) 3)
              (null acl2::forms))
         `(cond ((or (not (json::memberp ,(car acl2::args)))
                     (not (equal ,(cadr acl2::args) (json::member->name ,(car acl2::args)))))
                 (mv t ,(caddr acl2::args)))
                (t ,acl2::rest-expr)))
        (t (er hard? 'require-json-member-with-name "bad arguments"))))

(acl2::def-b*-binder require-json-object-with-single-member  ; args are (j errobj)
  :body
  (cond ((and (eql (len acl2::args) 2)
              (null acl2::forms))
         `(cond ((or (not (json::valuep ,(car acl2::args)))
                     (not (json::value-case ,(car acl2::args) :object))
                     ;; These next two work better than (= 1 (len ..))
                     (not (consp (json::value-object->members ,(car acl2::args))))
                     (not (endp (cdr (json::value-object->members ,(car acl2::args))))))
                 (mv t ,(cadr acl2::args)))
                (t ,acl2::rest-expr)))
        (t (er hard? 'require-json-object-with-single-member "bad arguments"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities

;; We could potentially call this in json-span-removal.lisp instead.
(define extract-identifier-name ((id-with-span stringp))
  :returns (shorter-id stringp)
  ;; id-with-span might not have a span-like wrapper, in which case it is returned unchanged.
  ;; If the id-with-span starts with "{\"name\":\""
  ;; then we presume the remaining characters up to the next #\"
  ;; are the actual identifier name.
  ;; If there is no next #\" or if the name is the empty string,
  ;; the entire id-with-span is returned.
  ;; Warning: this sort of change could potentially lose information,
  ;; but so far we don't see anything in id-with-span other than the span of
  ;; the identifier reference.  There is no linking information.
  (b* (((unless (stringp id-with-span)) "") ; duplicate guard
       (prefix "{\"name\":\"")
       ((unless (str::strprefixp prefix id-with-span)) id-with-span)
       ;; This next thing is duplicative, but it helps the guard proof of the call to subseq,
       ;; since we don't need to prove anything about when strprefixp returns true.
       ((unless (< (length prefix) (length id-with-span))) id-with-span)
       (rest-of-id-with-span (subseq id-with-span (length prefix) (length id-with-span)))
       (next-double-quote (str::strpos "\"" rest-of-id-with-span))
       ((when (null next-double-quote)) id-with-span)
       ((when (equal next-double-quote 0)) id-with-span))
    (subseq rest-of-id-with-span 0 next-double-quote)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Error objects.

;; These could be turned into constructors that carry information
;; about the error.

;; general error identifier that doesn't say where it came from
(defconst *error-identifier*
  (leo-early::make-identifier :name "ERROR_constructing_Identifier"))

;(defconst *error-funinput*
;  (make-funinput :name (leo-early::make-identifier :name "ERROR_constructing_FunctionInput")
;                 :type (leo-early::make-type-unsigned :size (leo-early::make-bitsize-8))))

(defconst *error-funparam*
  (leo-early::make-funparam :name (leo-early::make-identifier :name "ERROR_constructing_funparam")
                 :sort (leo-early::make-var/const-sort-const)
                 :type (leo-early::make-type-unsigned :size (leo-early::make-bitsize-8))))

(defconst *error-expression*
  (leo-early::make-expression-var/const :name (leo-early::make-identifier :name "erroneous_expression_from_json")))

;; An error in a parent object can use this as a sub.
(defconst *error-dummy-expression*
  (leo-early::make-expression-var/const :name (leo-early::make-identifier :name "dummy_expression")))

;(defconst *error-arrinelem-expression*
;  (make-arrinelem-expression :spreadp nil
;                             :expression *error-dummy-expression*))

;(defconst *error-circinmem-expression*
;  (make-circinmem-expression
;   :name (leo-early::make-identifier :name "ERROR_circinmem_expression_name")
;   :init (leo-early::make-expression-var/const :name (leo-early::make-identifier :name "ERROR_circinmem_expression_init_name"))))

(defconst *error-cond*
  (leo-early::make-expression-cond
   :test *error-expression*
   :then *error-expression*
   :else *error-expression*))

(defconst *error-binop*
  (leo-early::make-expression-binary
   :op (leo-early::make-binop-pow)
   :arg1 *error-expression*
   :arg2 *error-expression*))

(defconst *error-unary-op*
  (leo-early::make-expression-unary
   :op (leo-early::make-unop-not)
   :arg *error-expression*))

;;; There is not really any good error type declaration.
;;; Maybe a tuple with zero elements is likely to be erroneous.
;(defconst *error-type-decl*
;  (leo-early::make-type-tuple :elements nil))

;;; There is not really any good error type declaration.
;;; Just use i128 since maybe it is the least likely in other contexts.
;;; No caller counts on these being unobtainable, they are just for help when debugging.
(defconst *error-type-decl*
  (leo-early::make-type-signed :size (leo-early::make-bitsize-128)))

(defconst *error-vardecl*
  (leo-early::make-vardecl :name *error-identifier*
                :type *error-type-decl*
                :init *error-expression*))

(defconst *error-constdecl*
  (leo-early::make-constdecl :name *error-identifier*
                  :type *error-type-decl*
                  :init *error-expression*))

(defconst *error-let-statement*
  (leo-early::make-statement-let
   :get *error-vardecl*))

(defconst *error-const-statement*
  (leo-early::make-statement-const
   :get *error-constdecl*))

(defconst *error-assign-statement*
  (leo-early::make-statement-assign :op (leo-early::make-asgop-asg)
                         :left *error-expression*
                         :right *error-expression*))

(defconst *error-iteration-statement*
  (leo-early::make-statement-for :name (leo-early::make-identifier :name "ERROR_constructing_For_statement")
                      :type *error-type-decl*
                      :from *error-dummy-expression*
                      :to *error-dummy-expression*
                      :inclusivep nil
                      :body nil))

;; 2022-03-25 conditional no longer allows empty list of branches
(defconst *error-branch*
  (leo-early::make-branch :test *error-expression*
               :body nil))

;; we use the shortcut of zero branches to indicate an error conditional
;; 2022-03-25 no longer allows empty list of branches
(defconst *error-conditional-statement*
  (leo-early::make-statement-if :branches (list *error-branch*)
                     :else nil))

;(defconst *error-expression-statement*
;  (leo-early::make-statement-expr :get *error-expression*))

(defconst *error-block-statement*
  ;; It doesn't much matter what the sub-statement is, but an error expression
  ;; statement looks like the least likely to crop up as a singleton in a Block.
  (leo-early::make-statement-block :get (list *error-assign-statement*)))

;; Maybe there should be an :ERROR alternative in deftagsum statement
;; to handle the error statements.
(defconst *error-return-statement*
  (leo-early::make-statement-return :value *error-expression*))

;; EM 2022-03-26: no more print-args; now it is just a char-list
;; Not bothering right now to figure out outer-console vs console.
;; Also, debug went away.

;; Used to represent an error in a console statement where we
;; don't really know what console function it should be,
;; but we have to choose one of them, so make it the console.error
;; with an appropriate message.
(defconst *error-outer-console-error*
  (b* (
       (empty-fmt-string '()) ; char-list
       (msg "ERROR_constructing_console_statement_unknown_console_function")
       (msg-expr (leo-early::make-expression-var/const :name (leo-early::make-identifier :name msg))))
;    (leo-early::make-console-error :arg? (make-print-args :string empty-fmt-string :params (list msg-expr)))
    (leo-early::make-console-error :string empty-fmt-string :exprs (list msg-expr))
    ))

(defconst *error-console-error*
  (b* (
       (empty-fmt-string  '()) ; char-list
       (msg "ERROR_constructing_console_error_function_call")
       (msg-expr (leo-early::make-expression-var/const :name (leo-early::make-identifier :name msg))))
;    (leo-early::make-console-error :arg? (make-print-args :string empty-fmt-string :params (list msg-expr)))
    (leo-early::make-console-error :string empty-fmt-string :exprs (list msg-expr))
    ))

(defconst *error-console-assert*
  (leo-early::make-console-assert :arg *error-expression*))

;(defconst *error-console-debug*
;  (b* (
;       (empty-fmt-string  '()) ; char-list
;       (msg "ERROR_constructing_console_debug_function_call")
;       (msg-expr (leo-early::make-expression-var/const :name (leo-early::make-identifier :name msg))))
;;    (leo-early::make-console-debug :arg? (make-print-args :string empty-fmt-string :params (list msg-expr)))
;    (leo-early::make-console-error :string empty-fmt-string :exprs (list msg-expr))
;    ))

;; currently unused, but might be later.  See format-string.
(defconst *error-format-string*
  (leo-early::make-format-string :elements nil))

(defconst *error-console-log*
  (b* (
       (empty-fmt-string '()) ; char-list
       (msg "ERROR_constructing_console_log_function_call")
       (msg-expr (leo-early::make-expression-var/const :name (leo-early::make-identifier :name msg))))
;    (leo-early::make-console-log :arg? (make-print-args :string empty-fmt-string :params (list msg-expr)))
    (leo-early::make-console-error :string empty-fmt-string :exprs (list msg-expr))
    ))

(defconst *error-console-statement*
  (leo-early::make-statement-console :get *error-outer-console-error*))

;; Need to expand the definition of literal.
;; For now, make it untyped 34404.
(defconst *error-literal*
  (leo-early::make-literal-string :get (list (leo-early::make-char :codepoint #x10EEEE))))

(defconst *error-literal-expression*
  (leo-early::make-expression-literal :get *error-literal*))

(defconst *error-literal-group-coordinate*
  (leo-early::make-coordinate-explicit :get 34404))

(defconst *error-var-expression*
  (leo-early::make-expression-var/const :name (leo-early::identifier "ERRORVAR")))

(defconst *error-fundecl*
  (leo-early::make-fundecl :annotations nil
                :sort (leo-early::fun-sort-standard)
                :name (leo-early::identifier "ERROR")
;               :self (selfinput-none)
                :inputs nil
                :output *error-type-decl*
                :body nil
                :finalizer nil
;               :constp nil
                    ))

(defconst *error-definition*
  (leo-early::make-topdecl-function :get *error-fundecl*))

(defconst *error-program*
  (leo-early::make-programdecl :id (leo-early::make-programid :name (leo-early::identifier "error")
                                        :network (leo-early::identifier "error"))
                    :items nil))

(defconst *error-file*
  (leo-early::make-file :imports nil :program *error-program*))

;(defconst *error-pkgpath*
;  (make-pkgpath-symbol :name *error-identifier* :alias? *error-identifier*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Detectors
;; (TODO: not used much, yet.. see what patterns we want as things grow)


;; Each jsonast-looks-like-XXX-p must be passed a json::valuep,
;; which is an object or array (but that should be checked).

;;;;;;;;;;;;;;;;
;; File object detector

(define jsonast-looks-like-file-p ((thing json::valuep))
  :returns (yes/no booleanp)
  :short "Checks if THING is a JSON AST file object."
  :parents (json2ast)
  (and (equal :object (json::value-kind thing))
       (json::object-has-member-p "name" thing)
       (json::object-has-member-p "expected_input" thing)
;       (json::object-has-member-p "import_statements" thing)
       (json::object-has-member-p "structs" thing)
       (json::object-has-member-p "functions" thing)
       ;(json::object-has-member-p "tests" thing) ; EM 2021-03-16 was folded in to "functions"
       ))


;;;;;;;;;;;;;;;;
;; Function definition member detector

;; EM 2021-01: add 2nd argument, which carries the outer mangled name.
;;   For test functions, the outer mangled name is the name of the test,
;;   and (json::member->name thing) is "function".
;;   For non-test functions, the outer mangled name should be the same
;;   as (json::member->name thing).
;;   In both cases, we now ignore (json::member->name thing).
;; EM 2020-12-08 additional "block" layer added above "statements"
;; EM 2020-11-21: "returns" changed to "output"
;;
(define jsonast-looks-like-function-definition-p ((thing json::memberp)
                                                  (outer-mangled-name stringp))
  :returns (yes/no booleanp)
  :short "Checks if THING is a JSON AST function definition object member."
  :parents (json2ast)
  (and (json::memberp thing)
    (let ((inner-fn-val (json::member->value thing)))
      (and (json::valuep inner-fn-val)
         (equal :object (json::value-kind inner-fn-val))
         (json::object-has-member-p "identifier" inner-fn-val)
         ;; This identifier is a json::value of kind :string
         (json::valuep (json::object-member-value "identifier" inner-fn-val))
         (equal :string (json::value-kind (json::object-member-value "identifier" inner-fn-val)))
         (equal outer-mangled-name (json::value-string->get (json::object-member-value "identifier" inner-fn-val)))
         (json::object-has-member-p  "input" inner-fn-val)
         (json::object-has-member-p  "output" inner-fn-val)
         (json::object-has-member-p  "block" inner-fn-val)
         (b* ((block-val (json::object-member-value "block" inner-fn-val))
              ((json::pattern (:object (:member "statements" json-array-of-statements)))
               block-val))
           (and json::match?
                (equal :array (json::value-kind json-array-of-statements))))
         ))))


(define jsonast-looks-like-struct-declaration-p ((thing json::memberp))
  :returns (yes/no booleanp)
  :short "Checks if THING is a JSON AST outer struct declaration object member, including the duplicate name."
  :parents (json2ast)
  (b* (((unless (json::memberp thing))
        nil)
       (outer-struct-mangled-name (json::member->name thing))
       (inner-struct-val (json::member->value thing))
       ((json::pattern (:object (:member "identifier"
                                         (:string inner-struct-mangled-name))
                                ;; EM 2022-07-30 "circuit_name" --> "identifier"
                                ;; EM 2021-08-30 New core_mapping json object member.
                                ;;   Don't yet know what it is for.
                                ;;   All instances seen so far are :NULL.
                                ;;   TODO: figure out what core_mapping is and handle it.
                                ;; EM 2021-12-13 ...and core_mapping has disappeared!
                                ;;   Commenting it out.
                                ;(:member "core_mapping" _)
                                (:member "members"
                                         (:array *..))
                                (:member "is_record" true-or-false)))  ; TODO
        inner-struct-val))
    (and json::match?
         (equal outer-struct-mangled-name inner-struct-mangled-name))))




;;;;;;;;;;;;;;;;
;; Return statement detector

(define jsonast-looks-like-return-statement-p ((thing json::valuep))
  :returns (yes/no booleanp)
  (and (equal :object (json::value-kind thing))
       (equal 1 (length (json::value-object->members thing)))
       (json::object-has-member-p "Return" thing)))

;; This should only be called once we know thing is a return statement
(define jsonast-return-statement-expression ((thing json::valuep))
  :guard (and (json::value-case thing :object)
               (jsonast-looks-like-return-statement-p thing))
  :returns (the-expression json::valuep)
  (json::object-member-value "Return" thing))

;;;;;;;;;;;;;;;;
;; Binop detector

; Not currently used.  See j2f-binop-name-to-binop
;(defconst *binop-names*  '("And" "Or" "Eq" "Ne" "Ge" "Gt" "Le"
;                           "Lt" "Add" "Sub" "Mul" "Div" "Pow"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; literal integers, untyped and typed

;; Note that the typed ast gives us integers as strings.
;; Presumably they have already been parsed, but when they are
;; serialized, they are turned into strings in the AST,
;; probably because the signed and unsigned integers need the iN or uN suffixes
;; and that is not legal syntax for JSON integers.

;; Looking at ~/leo/input/src/leo-input.pest
;; it looks like leading zeros are not forbidden in value_number.
;; So if the original input strings are returned in the AST
;; (which they probably are not),
;; we might as well just parse the regex -?[0-9]+


;; This is used for group and field literals.
;; TODO: Probably those places should be changed to use
;;       j2f-poss-negated-integer, and j2f-poss-negated-integer-string
;;       should be augmented to handle those additional literal types.
(define parse-leo-untyped-integer ((the-string stringp))
  :returns (maybe-untyped-int (or (null maybe-untyped-int)
                                  (integerp maybe-untyped-int)))
  (and (stringp the-string)
       (> (length the-string) 0)
       (let ((first-char (acl2::char the-string 0)))
         (if (equal #\- first-char)
             (and (> (length the-string) 1)
                  (let ((abs (str::strval (subseq the-string 1 (length the-string)))))
                    (and (natp abs)
                         (- abs))))
           (str::strval the-string)))))


;; leo-integer-type is passed down through the calls unchanged so it can
;; create the right ast node at the leaf.
;; If leo-integer-type is NIL, it represents an untyped integer
;; (the ast contains "Implicit").
(define j2f-poss-negated-integer-string ((s stringp)
                                         (i natp)
                                         (leo-integer-type leo-early::type-optionp))
  :returns (mv (erp booleanp) (leo-poss-negated-integer expressionp))
  (b* (((when (or (not (mbt (natp i)))
                  (>= i (length s))))
        (mv t *error-literal-expression*))
       ((unless (equal (acl2::char s i) #\-))
        ;; the rest must be digits
        (b* (((mv val len) (str::parse-nat-from-string s 0 0 i (length s)))
             ((when (= len 0))
              (mv t *error-literal-expression*))
             (leo-literal
              (if (null leo-integer-type)
                  *error-literal* ;(leo-early::make-literal-untyped :val val)
                (leo-early::type-case leo-integer-type
                           :signed (leo-early::make-literal-signed :val val
                                                        :size (leo-early::type-signed->size leo-integer-type))
                           :unsigned (leo-early::make-literal-unsigned :val val
                                                            :size (leo-early::type-unsigned->size leo-integer-type))
                           :otherwise *error-literal*)))
             ((when (equal leo-literal *error-literal*))
              (mv t *error-literal-expression*)))
          (mv nil
              (leo-early::make-expression-literal :get leo-literal))))
       ;; Now we know the first char is a minus sign
       ((mv suberp sub)
        (j2f-poss-negated-integer-string s (+ i 1) leo-integer-type))
       ((when suberp)
        (mv t *error-literal-expression*))
       ;; sub is either an expression-lit or an expression-unary
       ((unless (leo-early::expression-case sub ; :lit t
                                 :unary t :otherwise nil))
        (mv t *error-literal-expression*)))
    (mv nil
        (leo-early::make-expression-unary :op (leo-early::make-unop-neg)
                               :arg sub)))
  :measure (nfix (- (length s) i))
  :verify-guards nil
  ///
  (verify-guards j2f-poss-negated-integer-string))


(define j2f-poss-negated-integer ((thing json::valuep) (leo-integer-type leo-early::type-optionp))
  :returns (mv (erp booleanp) (leo-poss-negated-integer expressionp))
  (b* (((unless (equal :string (json::value-kind thing)))
        (mv t *error-literal-expression*))
       (poss-negated-int-string (json::value-string->get thing))
       ((unless (stringp poss-negated-int-string))
        (mv t *error-literal-expression*)))
    (j2f-poss-negated-integer-string poss-negated-int-string 0 leo-integer-type)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variable declarations


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types

;; Note, we could share a single object for each type, or we could
;; have multiple copies.  Multiple copies is more flexible later,
;; so let's leave them unshared for now.

;; A type is usually the member->value val of a json-member that
;; looks like this: (:MEMBER "type_" val)
;; but it can also occur in a 2-element :ARRAY (see below).

;; Types we have seen:
;;   (:NULL)  - e.g., no type decl on a let var
;;   (:STRING "Boolean")
;;   (:OBJECT (:MEMBER "IntegerType" (:STRING "U32")))
;;   (:OBJECT (:MEMBER "Array" (:ARRAY elemtype (:ARRAY (:NUMBER howmany)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define j2f-type-string ((type-string stringp))
  :returns (mv (erp booleanp) (leo-type typep))
  (cond ((equal type-string "U8")
         (mv nil (leo-early::make-type-unsigned :size (leo-early::make-bitsize-8))))
        ((equal type-string "U16")
         (mv nil (leo-early::make-type-unsigned :size (leo-early::make-bitsize-16))))
        ((equal type-string "U32")
         (mv nil (leo-early::make-type-unsigned :size (leo-early::make-bitsize-32))))
        ((equal type-string "U64")
         (mv nil (leo-early::make-type-unsigned :size (leo-early::make-bitsize-64))))
        ((equal type-string "U128")
         (mv nil (leo-early::make-type-unsigned :size (leo-early::make-bitsize-128))))
        ((equal type-string "I8")
         (mv nil (leo-early::make-type-signed :size (leo-early::make-bitsize-8))))
        ((equal type-string "I16")
         (mv nil (leo-early::make-type-signed :size (leo-early::make-bitsize-16))))
        ((equal type-string "I32")
         (mv nil (leo-early::make-type-signed :size (leo-early::make-bitsize-32))))
        ((equal type-string "I64")
         (mv nil (leo-early::make-type-signed :size (leo-early::make-bitsize-64))))
        ((equal type-string "I128")
         (mv nil (leo-early::make-type-signed :size (leo-early::make-bitsize-128))))
        (t (mv t (leo-early::make-type-signed :size (leo-early::make-bitsize-128)))))) ; error indicator

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type declarations without component types.
;; Keep it outside the mutual recursion.

;; NOTE: this definition introduces a few error objects that are not in
;; *error-xxx* constants.
;;
;; NOTE: this definition is used in a number of places,
;;    some of which are not json-members with name "IntegerType".
;;    E.g., a literal integer can have a type decoration.
(define j2f-integer-type ((json-integer-type json::valuep))
  :returns (mv (erp booleanp) (leo-type typep))
  (b* (((unless (and (json::valuep json-integer-type)
                     (json::value-case json-integer-type :string)))
        (mv t (leo-early::make-type-unsigned :size (leo-early::make-bitsize-32))))
       (type-string (json::value-string->get json-integer-type))
       ((unless (stringp type-string))
        (mv t (leo-early::make-type-unsigned :size (leo-early::make-bitsize-64)))))
    (j2f-type-string type-string)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; EM 2022-07-20 At least some types have simplified.
;; For the type of a let var statement, was:
;;            "type_": {
;;              "IntegerType": "U32"
;;            },
;; Now:
;;             "type_": "U32",

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; named type is just an identifier with span
;; In before-testnet3 this used to be called struct-or-alias-type.
(define j2f-named-type ((json-type-id json::valuep))
  :returns (mv (erp booleanp) (leo-type typep))
  (b* (((unless (json::valuep json-type-id))
        (mv t *error-type-decl*))
       ((json::pattern (:string type-name-w-span)) json-type-id)
       ((unless (and json::match?
                     (stringp type-name-w-span)))
        (mv t *error-type-decl*))
       (type-name (extract-identifier-name type-name-w-span))
       ((unless (leo-early::identifier-string-p type-name)) (mv t *error-type-decl*)))
    (mv nil
        ;; TODO: handle all the kinds of internal/external types and recordp
        (leo-early::make-type-internal-named :get (leo-early::make-identifier :name type-name)
                                  :recordp nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursive type declarations

(set-bogus-mutual-recursion-ok t)

(defines json2ast-mutual-recursion-types
  :short "Convert Leo types from JSON to formal AST."
  :parents (json2ast)

  (define j2f-type-list ((json-types json::value-listp))
    :returns (mv (erp booleanp) (leo-types type-listp))
    (b* (((when (endp json-types))
          (mv nil nil))
         ((mv first-erp first-type) (j2f-type (car json-types)))
         ((mv rest-erp rest-types) (j2f-type-list (cdr json-types))))
      (mv (or first-erp rest-erp)
          (cons first-type rest-types)))
    :measure (two-nats-measure (json::value-list-count json-types) 0))

  (define j2f-type ((json-type json::valuep))
    :returns (mv (erp booleanp) (leo-type typep))
    :short "Converts a json-type into a leo::type."
    :parents (json2ast)

    ;; First handle the types that are not json-objects
    ;; (so far, all :string, but I see there are some null type_ markers
    ;; in the json files, so that will need to be handled eventually).
    (b* (((json::pattern (:string simple-type-name)) json-type))

      (if json::match?
          (cond ((equal "Boolean" simple-type-name)
                 (mv nil (leo-early::make-type-bool)))
;                ((equal "Char" simple-type-name)
;                 (mv nil (leo-early::make-type-char)))
                ((equal "Field" simple-type-name)
                 (mv nil (leo-early::make-type-field)))
                ((equal "Group" simple-type-name)
                 (mv nil (leo-early::make-type-group)))
                ((equal "Address" simple-type-name)
                 (mv nil (leo-early::make-type-address)))
                ((equal "Scalar" simple-type-name)
                 (mv nil (leo-early::make-type-scalar)))
                ;; EM 2022-07-20 integer types now handled here
                (t
                 (b* (((mv not-int-type? leo-type)
                       (j2f-type-string simple-type-name))
                      ((when not-int-type?)
                       (mv t *error-type-decl*)))
                   (mv nil leo-type))))

        ;; Now the objects
        (b* (((unless (and (json::valuep json-type)
                           (json::value-case json-type :object)))
              (mv t *error-type-decl*))
             (json-type-members (json::value-object->members json-type))
             ((unless (and (= 1 (len json-type-members))
                           ;; these next conjuncts are redundant, but helpful for the prover
                           (consp json-type-members)
                           (endp (cdr json-type-members))))
              (mv t *error-type-decl*))
             (json-member (first json-type-members))
             (json-type-name (json::member->name json-member))
             ((unless (stringp json-type-name))
              (mv t *error-type-decl*)))

;          (if (equal "Tuple" json-type-name)
;              (j2f-tuple-type json-member)
;            (if (equal "Array" json-type-name)
;                (j2f-array-type json-member)
              (if (equal "IntegerType" json-type-name)
                  ;; since j2f-integer-type is used elsewhere just as the json-value part,
                  ;; we dereference it here
                  (j2f-integer-type (json::member->value json-member))
                (if (equal "Identifier" json-type-name)
                    ;; EM 2021-08-30: this was changed from "Circuit" to "CircuitOrAlias"
                    ;; EM 2021-09-09: this was changed from "CircuitOrAlias" to "Identifier"
                    ;; EM 2022-07-30: changed from j2f-circuit-or-alias-type to j2f-named-type
                    (j2f-named-type (json::member->value json-member))

                  ;; Other type names go here:
                  ;;   ...
                  ;; If none of them match, return an error:
                  (prog2$ (cw "ERROR: unknown type declaration ~x0~%" json-type)
                          (mv t *error-type-decl*))
;                  )
              ))
;              ))
      )))
    :measure (two-nats-measure (json::value-count json-type) 0))

  ;; for the defines
  :verify-guards nil ; done below
  ///
  (verify-guards j2f-type)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; funinput

;; A funinput has a name (an identifier object), a mode, and type.

;; If a JSON-member's name is "Variable", this function is called on the member's value.
(define j2f-funinput ((json-functioninput-value json::valuep))
  :returns (mv (erp booleanp) (leo-funinput funinputp))
  (if (not (json::valuep json-functioninput-value))
      (mv t *error-funparam*)

    (if (json::value-case json-functioninput-value :string)
      ;; TODO: test the "input" case
      (let ((the-string (json::value-string->get json-functioninput-value)))
        (if (and (stringp the-string) (equal the-string "input"))
            (mv t *error-funparam*)
          (mv t *error-funparam*)))

      (if (json::value-case json-functioninput-value :object)
          (b* (
               ;; EM 2022-05-18 No longer support "const_", but now there is "mode".
               ;; EM: 2021-08-23  Added "const_".  I also see there is a member
               ;; with name "mutable".  Would it always be opposite "const_"?
               ;; Right now we ignore it.
               ;; WAS: There should be 2 members with names: "identifier", "type_"
               ((unless (and (json::object-has-member-p "identifier" json-functioninput-value)
                             (json::object-has-member-p "mode" json-functioninput-value)
                             ;(json::object-has-member-p "const_" json-functioninput-value)
                             (json::object-has-member-p "type_" json-functioninput-value)))
                (mv t *error-funparam*))

               (id-value (json::object-member-value "identifier" json-functioninput-value))
               ((unless (and (json::valuep id-value)
                             (json::value-case id-value :string)))
                (mv t *error-funparam*))
               ;; remove span from id
               (cleaned-id-value (extract-identifier-name (json::value-string->get id-value)))
               ((unless (leo-early::identifier-string-p cleaned-id-value)) (mv t *error-funparam*))
               (leo-id (leo-early::make-identifier :name cleaned-id-value))

;               (const-value (json::object-member-value "const_" json-functioninput-value))
;               (leo-const (json::value-case const-value :true t :false nil :otherwise :error))
;               ((when (eq leo-const :error))
;                (mv t *error-funparam*))

               ;; mode: Private, Public, or Constant
               (mode-value (json::object-member-value "mode" json-functioninput-value))
               ((unless (equal :string (json::value-kind mode-value)))
                (mv t *error-funparam*))
               (mode-value-string (json::value-string->get mode-value))
               ((unless (member-equal mode-value-string
                                      '("Private" "Public" "Const" "Constant")))
                (mv t *error-funparam*))
               (type-value (json::object-member-value "type_" json-functioninput-value))
               ((mv erp leo-type) (j2f-type type-value))
               ((when erp) (mv t *error-funparam*))) ; we ignore the inner error object for now

            (mv nil (leo-early::make-funparam :name leo-id
                                   ; it would be good to factor out j2f-param-mode
                                   :sort (cond ((equal mode-value-string "Private")
                                                (leo-early::make-var/const-sort-private))
                                               ((equal mode-value-string "Public")
                                                (leo-early::make-var/const-sort-public))
                                               ((equal mode-value-string "Const")
                                                (leo-early::make-var/const-sort-const))
                                               ((equal mode-value-string "Constant")
                                                (leo-early::make-var/const-sort-constant)))
;                                   (if leo-const
;                                       (leo-early::make-var/const-sort-const)
;                                     (leo-early::make-var/const-sort-public))
                                   :type leo-type)))

        ;; the value-kind is neither :string nor :object
        (mv t *error-funparam*)))
    ))

;; TODO: how about "registers"?
;; I see it is documented in https://developer.aleo.org/developer/programming_model/model/
;; but the test compiler/tests/field/output_register.leo
;; gets an error when I do "leo_ast output_register.leo".
;;
;; This should be called on an object with a single member whose name is "FunctionInput".
;; The idea is to abstract out this layer in case other input specs are needed.
(define j2f-outer-funinput ((json-outer-funinput json::valuep))
  :returns (mv (erp booleanp) (leo-funinput funinputp))
  (b* (((unless (and (json::valuep json-outer-funinput)
                     (equal :object (json::value-kind json-outer-funinput))))
        (mv t *error-funparam*))
       ((json::pattern (:object (:member "InputKeyword"
                                         (:string input-with-span))))
        json-outer-funinput)
       ;; handle keyword "input"
       ((when json::match?)
        (let ((input-string (and (stringp input-with-span)
                                 (extract-identifier-name input-with-span))))
          (if (not (equal "input" input-string))
              (mv t *error-funparam*)
            (mv t *error-funparam*))))
       ((json::pattern (:object (:member "Variable"
                                         funinput-value)))
        json-outer-funinput)
       ((unless json::match?)
        (mv t *error-funparam*)))
    (j2f-funinput funinput-value)))


(define j2f-funinputs  ((json-fn-inputs json::value-listp))
  :returns (mv (erp booleanp) (leo-inputs funinput-listp))
  :short "Converts a list of json fn input parameters to a leo::funinput-list."
  :parents (json2ast)
  (b* (((when (endp json-fn-inputs))
        (mv nil nil))
       (inp (first json-fn-inputs))
       ((mv erp leo-fn-input) (j2f-outer-funinput inp))
       ((when erp) (mv t nil))
       ((mv erp rest-leo-fn-inputs) (j2f-funinputs (rest json-fn-inputs)))
       ((when erp) (mv t nil)))
    (mv nil (cons leo-fn-input rest-leo-fn-inputs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Leaf expressions

;; Here is are expression-creating functions that don't need to go into the mutual recursion.

;; This seems to be used for array repeat counts, so we restrict it to nats.
(define j2f-value-expression ((json-value-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-nat-expression expressionp))
  (b* (((unless (and (json::memberp json-value-expression)
                     (equal "value" (json::member->name json-value-expression))))
        (mv t *error-literal-expression*))
       ((json::pattern (:string decimal-digit-string))
        (json::member->value json-value-expression))
       ((unless (and json::match?
                     (stringp decimal-digit-string)
                     (str::dec-digit-string-p decimal-digit-string)))
        (mv t *error-literal-expression*))
       (value-nat (str::strval decimal-digit-string))
       ((unless (natp value-nat))
        (mv t *error-literal-expression*)))
    ;; TODO: This is probably wrong.. maybe the abstract syntax needs to change
    (mv nil
        ; EM 2022-03-25: took out untyped literals for pre-testnet3
        ;(leo-early::make-expression-literal :get (leo-early::make-literal-untyped :val value-nat))
        *error-literal-expression*
        )))

(define j2f-implicit-expression ((json-implicit-expression json::memberp))
  ;; We call the parameter json-implicit-expression because "Implicit" is the member name.
  ;; We call the return parameter "leo-untyped-literal-expression" because
  ;; it is an expression of kind :lit with a literal of kind :untyped in it.
  :returns (mv (erp booleanp) (leo-untyped-literal-expression expressionp))
  (b* (((unless (and (json::memberp json-implicit-expression)
                     (equal "Implicit" (json::member->name json-implicit-expression))
                     (json::valuep (json::member->value json-implicit-expression))
                     (equal :string (json::value-kind (json::member->value json-implicit-expression)))))
        (mv t *error-literal-expression*)))
    (j2f-poss-negated-integer (json::member->value json-implicit-expression) nil)))

;; NOTE 2020-11-03: I am now seeing some "Implicit" expressions
;; now wrapped with an extra layer of "Expression".
;; I don't know what else can be wrapped with "Expression".
;; NOTE 2020-11-17:  I am now seeing the index i in self.parameters[i]
;; wrapped in an expression.  Not sure why, but we unwrap that here as well.
;; FURTHER NOTE: it might be possible to just unwrap this and call j2f-expression
;; on the inner part.  If this crops up in more places, bring it up to see
;; if that makes sense.
(define j2f-expression-expression ((json-expression-expression json::memberp))
  :returns (mv (erp booleanp) (leo-untyped-literal-expression expressionp))
  (b* (((unless (and (json::memberp json-expression-expression)
                     (equal "Expression" (json::member->name
                                          json-expression-expression))))
        (mv t *error-expression*))
       ((json::pattern (:object (:member "Implicit" (:string int-val-string))))
        (json::member->value json-expression-expression))
       ((when (and json::match?
                   (stringp int-val-string)))
        ;; handle the "Implicit" case here
        (j2f-poss-negated-integer (json::member->value json-expression-expression) nil))
       ;; now try the Identifier wrapped in expression
       ((json::pattern (:object (:member "Identifier" (:string index-var-w-span))))
        (json::member->value json-expression-expression))
       ((unless (and json::match?
                     (stringp index-var-w-span)))
        (mv t *error-expression*))
       (index-var (extract-identifier-name index-var-w-span))
       ((unless (leo-early::identifier-string-p index-var))
        (mv t *error-expression*)))
    (mv nil
        (leo-early::make-expression-var/const :name (leo-early::make-identifier :name index-var)))))

(define j2f-var-or-self-expression ((json-identifier-expression json::memberp))
  :returns (mv (erp booleanp) (leo-var expressionp))
  (b* (((unless (and (json::memberp json-identifier-expression)
                     (equal "Identifier" (json::member->name json-identifier-expression))
                     (json::valuep (json::member->value json-identifier-expression))
                     (equal :string (json::value-kind (json::member->value json-identifier-expression)))))
        (mv t *error-var-expression*))
       (leo-var-name-with-span (json::value-string->get (json::member->value json-identifier-expression)))
       ((unless (stringp leo-var-name-with-span))
        (mv t *error-var-expression*))
       (leo-var-name (extract-identifier-name leo-var-name-with-span))
       ;; We see "self" in the pedersen mock test, circuit member expression self.parameters[i]
       ;; TODO: does "Self" also show up here, and if so, what does it mean?
       ;; EM 2020-11-22: now seeing "input" show up here.  Adding as a separate case.
       ((unless (or ;(equal "self" leo-var-name)
                    ;(equal "input" leo-var-name)
                    (leo-early::identifier-string-p leo-var-name)))
        (mv t *error-var-expression*)))
    (mv nil
        (leo-early::make-expression-var/const :name (leo-early::make-identifier :name leo-var-name))
;        (if (equal "self" leo-var-name)
;            (leo-early::make-expression-self)
;          (if (equal "input" leo-var-name)
;              (leo-early::make-expression-input)
;            (leo-early::make-expression-var/const :name (leo-early::make-identifier :name leo-var-name))))
        )))

;; Temporary, to see what changed in 2020-11-21.
;; For now, we ignore the new (:member :accesses (:array *..))
(define j2f-var-or-self-expression-2 ((json-identifier-expression json::memberp))
  :returns (mv (erp booleanp) (leo-var expressionp))
  (b* (((unless (and (json::memberp json-identifier-expression)
                     (equal "identifier" (json::member->name json-identifier-expression))
                     (json::valuep (json::member->value json-identifier-expression))
                     (equal :string (json::value-kind (json::member->value json-identifier-expression)))))
        (mv t *error-var-expression*))
       (leo-var-name-with-span (json::value-string->get (json::member->value json-identifier-expression)))
       ((unless (stringp leo-var-name-with-span))
        (mv t *error-var-expression*))
       (leo-var-name (extract-identifier-name leo-var-name-with-span))
       ;; We see "self" in the pedersen mock test, circuit member expression self.parameters[i]
       ;; TODO: does "Self" also show up here, and if so, what does it mean?
       ((unless (or ;(equal "self" leo-var-name)
                    (leo-early::identifier-string-p leo-var-name)
                    ))
        (mv t *error-var-expression*)))
    (mv nil
;        (if (equal "self" leo-var-name)
;            (leo-early::make-expression-self)
          (leo-early::make-expression-var/const :name (leo-early::make-identifier :name leo-var-name))
;          )
    )))

;; If the integer were untyped, it would be in a member with name "Implicit", handled elsewhere.
;; This is in a member with name "Integer".
(define j2f-integer-literal-expression ((json-literal-integer-expression json::memberp))
  :returns (mv (erp booleanp) (leo-integer-literal-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-integer-expression)
                     (equal "Integer" (json::member->name json-literal-integer-expression))
                     (json::valuep (json::member->value json-literal-integer-expression))
                     (equal :array (json::value-kind (json::member->value json-literal-integer-expression)))))
        (mv t *error-literal-expression*))
       (literal-int-json-array-elements (json::value-array->elements (json::member->value json-literal-integer-expression)))
       ;; exactly 2 elements
       ((unless (and (consp literal-int-json-array-elements)
                     (consp (cdr literal-int-json-array-elements))
                     (endp (cddr literal-int-json-array-elements))))
        (mv t *error-literal-expression*))
       (literal-int-type-specifier (first literal-int-json-array-elements))
       (literal-int-value-specifier (second literal-int-json-array-elements))
       ;(- (cw "literal-int-type-specifier: ~x0~%" literal-int-type-specifier))
       ;(- (cw "literal-int-value-specifier: ~x0~%" literal-int-value-specifier))
       ;; first the type.  j2f-integer-type does its own checking; as long as it is json::valuep
       ((mv erp leo-integer-type) (j2f-integer-type literal-int-type-specifier))
       ;(- (cw "leo-integer-type: ~x0~%" leo-integer-type))
       ((when erp) (mv t *error-literal-expression*)))

    ;; 2022-03-13 EM: At the moment, the value string can start with any
    ;; number of hyphens that should be translated to unary negations.
    (j2f-poss-negated-integer literal-int-value-specifier leo-integer-type)))

;; EM 2022-07-20 Simplified version that hopefully replaces above
;; after AST changes.
(define j2f-literal-integer ((typestring stringp) (intstring stringp))
  :returns (mv (erp booleanp) (leo-integer-literal-expression expressionp))
  (b* (((mv erp leo-type) (j2f-type-string typestring))
       ((when erp)
        (mv t *error-literal-expression*)))
    (j2f-poss-negated-integer-string intstring 0 leo-type)))

(define j2f-boolean-literal-expression ((json-literal-boolean-expression json::memberp))
  :returns (mv (erp booleanp) (leo-boolean-literal-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-boolean-expression)
                     (equal "Boolean" (json::member->name json-literal-boolean-expression))
                     (json::valuep (json::member->value json-literal-boolean-expression))
                     (equal :string (json::value-kind (json::member->value json-literal-boolean-expression)))))
        (mv t *error-literal-expression*))
       (literal-boolean-value (json::member->value json-literal-boolean-expression))
       ((json::pattern (:string true-or-false)) literal-boolean-value)
       ((unless (and json::match?
                     (member-equal true-or-false '("true" "false"))))
        (mv t *error-literal-expression*)))
    (mv nil (leo-early::make-expression-literal :get (leo-early::make-literal-bool
                                       :val (equal true-or-false "true"))))))

;; The field number is in a string, similar to j2f-implicit-expression.
;; NOTE: currently supports negative number literals, since the parser
;; permits those, even though the Aleo Developer Doc forbids them.
(define j2f-field-literal-expression ((json-literal-field-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-field-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-field-expression)
                     (equal "Field" (json::member->name json-literal-field-expression))
                     (json::valuep (json::member->value json-literal-field-expression))
                     (equal :string (json::value-kind (json::member->value json-literal-field-expression)))))
        (mv t *error-literal-expression*))
       (literal-field-value (json::member->value json-literal-field-expression))
       ((json::pattern (:string field-val-string)) literal-field-value)
       ((unless (and json::match?
                     (stringp field-val-string)))
        (mv t *error-literal-expression*))
       (parsed (parse-leo-untyped-integer field-val-string))
       ((unless (integerp parsed))
        (mv t *error-literal-expression*)))
    (mv nil (leo-early::make-expression-literal :get (leo-early::make-literal-field
                                       :val parsed)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Group literals.
;; Below "Group", there is either "Single" (like 1group) or "Tuple" (like (0,1)group).

(define j2f-group-coordinate ((json-literal-group-coordinate json::valuep))
  :returns (mv (erp booleanp) (leo-literal-group-coordinate coordinatep))
  (b* (((unless (json::valuep json-literal-group-coordinate))
        (mv t *error-literal-group-coordinate*))

       ((json::pattern (:string "SignHigh")) json-literal-group-coordinate)
       ((when json::match?)
        (mv nil (leo-early::make-coordinate-sign-high)))
       ((json::pattern (:string "SignLow")) json-literal-group-coordinate)
       ((when json::match?)
        (mv nil (leo-early::make-coordinate-sign-low)))
       ((json::pattern (:string "Inferred")) json-literal-group-coordinate)
       ((when json::match?)
        (mv nil (leo-early::make-coordinate-inferred)))

       ((json::pattern (:object (:member "Number" (:string coord-val-string))))
        json-literal-group-coordinate)
       ((unless (and json::match?
                     (stringp coord-val-string)))
        (mv t *error-literal-group-coordinate*))
       (parsed (parse-leo-untyped-integer coord-val-string))
       ((unless (integerp parsed))
        (mv t *error-literal-group-coordinate*)))
    (mv nil (leo-early::make-coordinate-explicit :get parsed))))


(define j2f-group-literal-expression ((json-literal-group-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-group-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-group-expression)
                     (equal "Group" (json::member->name json-literal-group-expression))))
        (mv t *error-literal-expression*))

       ;; First try "Single"
       ((json::pattern (:object (:member "Single" (:string group-val-string))))
        (json::member->value json-literal-group-expression))
       (parsed (and json::match?
                    (stringp group-val-string)
                    (parse-leo-untyped-integer group-val-string)))
       ((when (integerp parsed))
        (mv nil (leo-early::make-expression-literal
                 :get (leo-early::make-literal-group
                       :get (leo-early::make-group-literal-product :factor parsed)))))

       ;; The other known arrangement is "Tuple"
       ((json::pattern (:object (:member "Tuple"
                                         (:object (:member "x" x-coord)
                                                  (:member "y" y-coord)))))
        (json::member->value json-literal-group-expression))
       ((unless json::match?)
        (mv t *error-literal-expression*))
       ((mv erp-x leo-x)
        (j2f-group-coordinate x-coord))
       ((mv erp-y leo-y)
        (j2f-group-coordinate y-coord))
       ((when (or erp-x erp-y))
        (mv t *error-literal-expression*)))
    (mv nil
        (leo-early::make-expression-literal
         :get (leo-early::make-literal-group
               :get (leo-early::make-group-literal-affine
                     :x leo-x :y leo-y))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Address literals.

;; The address is in a string, similar to j2f-implicit-expression and to field literals.
;; NOTE: leo-early::address-string-p checks that the address is a well-formed string.
;; It would be good to report more detailed errors if not, though.
;;
(define j2f-address-literal-expression ((json-literal-address-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-address-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-address-expression)
                     (equal "Address" (json::member->name json-literal-address-expression))))
        (mv t *error-literal-expression*))
       ((json::pattern (:string address-string))
        (json::member->value json-literal-address-expression))
       ((unless (and json::match?
                     (leo-early::address-string-p address-string)))
        (mv t *error-literal-expression*)))
    (mv nil
        (leo-early::make-expression-literal :get (leo-early::make-literal-address
                                   :get (leo-early::make-address :name address-string))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Character literals and String literals

;; In Leo abstract syntax (not JSON):
;; No char literals now: NOT:* Individual character literals are of type expression-lit containing a literal-char.
;; * String literals are a type-expression-lit containing a literal-string,
;;   where the literal-string has a list of char directly, with no intermediate
;;   expression or literal-char.
;; Note that a literal array, which is what a literal string will be canonicalized into,
;; has an extra arrinelem-expression wrapped around each expression-lit,
;; to allow for spreads.

;(defconst *error-literal-char-expr*
;  (leo-early::make-expression-literal :get (leo-early::make-literal-char :get (leo-early::make-char :codepoint 33)))) ; '!'

;(define j2f-literal-char ((json-literal-char json::valuep))
;  :returns (mv (erp booleanp) (leo-literal-char-expr expressionp))
;  (b* (((unless (and (json::valuep json-literal-char)
;                     (json::value-case json-literal-char :object)))
;        (mv t *error-literal-char-expr*))
;       ((json::pattern (:object (:member scalar-or-non-scalar
;                                         (:number char-code))))
;        json-literal-char)
;       ((unless (and json::match?
;                     (stringp scalar-or-non-scalar)
;                     ;; we could check the exact string here
;                     (natp char-code)
;                     (<= char-code #x10FFFF)))
;        (mv t *error-literal-char-expr*)))
;    (mv nil (leo-early::make-expression-literal :get (leo-early::make-literal-char :get (leo-early::make-char :codepoint char-code))))))

(defconst *error-char*
  (leo-early::make-char :codepoint 33))

;; This has the same main body as j2f-literal-char does except for the make- fn,
;; but we do not combine them since it is possible they could differ in the future.
(define j2f-literal-string-char ((json-literal-char json::valuep))
  :returns (mv (erp booleanp) (leo-literal-char charp))
  (b* (((unless (and (json::valuep json-literal-char)
                     (json::value-case json-literal-char :object)))
        (mv t *error-char*))
       ((json::pattern (:object (:member scalar-or-non-scalar
                                         (:number char-code))))
        json-literal-char)
       ((unless (and json::match?
                     (stringp scalar-or-non-scalar)
                     ;; we could check the exact string here
                     (natp char-code)
                     (<= char-code #x10FFFF)))
        (mv t *error-char*)))
    (mv nil (leo-early::make-char :codepoint char-code))))

;; Used for literal strings.
;; Testing for nonempty not done here; if needed, it should be done in the caller,
;; or possibly check later during compilation.
(define j2f-literal-string-char-list ((json-literal-chars json::value-listp))
  :returns (mv (erp booleanp) (leo-literal-char-list char-listp))
  (b* (((when (endp json-literal-chars))
        (mv nil nil))
       ((mv first-erp first-char)
        (j2f-literal-string-char (first json-literal-chars)))
       ((when first-erp)
        (mv t nil))
       ((mv rest-erp rest-chars)
        (j2f-literal-string-char-list (rest json-literal-chars)))
       ((when rest-erp)
        (mv t nil)))
    (mv nil (cons first-char rest-chars))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define j2f-literal-scalar ((json-literal-scalar-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-scalar-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-scalar-expression)
                     (equal "Scalar" (json::member->name json-literal-scalar-expression))
                     (json::valuep (json::member->value json-literal-scalar-expression))
                     (equal :string (json::value-kind (json::member->value json-literal-scalar-expression)))))
        (mv t *error-literal-expression*))
       (literal-scalar-value (json::member->value json-literal-scalar-expression))
       ((json::pattern (:string scalar-val-string)) literal-scalar-value)
       ((unless (and json::match?
                     (stringp scalar-val-string)))
        (mv t *error-literal-expression*))
       (parsed (parse-leo-untyped-integer scalar-val-string))
       ((unless (integerp parsed))
        (mv t *error-literal-expression*)))
    (mv nil (leo-early::make-expression-literal :get (leo-early::make-literal-scalar
                                           :val parsed)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; EM 2022-07-20 integer value pattern changed from (after removing span):
;;                          "Literal": {
;;                            "Integer": [ "U32","5" ]
;;                          }
;; to (after removing span and then eliminating the resulting extra :array around the "5"):
;;                          "Literal": {
;;                            "U32": "5"
;;                          }

;; EM 2022-06-04 the JSON string "Value" changed to "literal".
;;   Also a new pattern for "Scalar"
;; EM 2021 New "Value" wrapper for atomic literal values.
;; There are currently 3 literal value patterns.
;; 1. "Integer" value is (:array (:string typestring) (:string integerstring))
;; 2. "Group" value is (:object (:member "Tuple" ...))
;; 3. "Implicit", "Boolean", "Address", and "Field" all have a value string
;;    that must be parsed.

(define j2f-value-wrapper-expression ((json-literal-value-expression json::memberp))
  :returns (mv (erp booleanp) (leo-literal-expression expressionp))
  (b* (((unless (and (json::memberp json-literal-value-expression)
                     (equal "Literal" (json::member->name json-literal-value-expression))))
        (mv t *error-literal-expression*))

       ;; Bind the single member of the object that is the value of
       ;; json-literal-value-expression.
       ;; This helps the legacy callees because they expect the member,
       ;; not the components of the member.
       ;; Consider removing this when the callees are updated to be less verbose.
       ;; Note, I want to expand json::pattern so I can do this:
       ;;  ((json::pattern (:object the-member))
       ;;   (json::member->value json-literal-value-expression))
       ;; Currently I have to open up the member just to check that there is a single member.
       ((json::pattern (:object (:member value-json-type
                                         value-json-expr)))
        (json::member->value json-literal-value-expression))
       ((unless json::match?)
        (mv t *error-literal-expression*))

       ;; 2022-07-20 New pattern for integers, without "Integer" name
       ((json::pattern (:object (:member typestring (:string intstring))))
        (json::member->value json-literal-value-expression))
       ((when (and json::match?
                   (member-equal typestring '("U8" "U16" "U32" "U64" "U128"
                                              "I8" "I16" "I32" "I64" "I128"))
                   (stringp intstring)))
        (j2f-literal-integer typestring intstring))

       ;; 2022-07-20 New pattern for boolean
       ((json::pattern (:object (:member "Boolean" true-or-false)))
        (json::member->value json-literal-value-expression))
       ((when (and json::match?
                   (json::valuep true-or-false)
                   (json::value-case true-or-false
                     :true t :false t :otherwise nil)))
        (mv nil (leo-early::make-expression-literal
                 :get (leo-early::make-literal-bool
                       :val (json::value-case true-or-false :true)))))

       ;; handle Literal (was "Value") being literal integer
       ((json::pattern (:object (:member "Integer"
                                         (:array (:string typestring)
                                                 (:string intstring)))))
        (json::member->value json-literal-value-expression))
       ((when (and json::match?
                   (stringp typestring) (stringp intstring)))
        (j2f-integer-literal-expression (first (json::value-object->members
                                                (json::member->value json-literal-value-expression))))
        ;; j2f-integer-literal-expression does some extra work.  Could be replaced by
        ;; a new function (j2f-literal-integer typestring intstring)
        )

;       ;; handle Value being literal character
;       ((json::pattern (:object (:member "Char"
;                                         (:object (:member "character"
;                                                           json-inner-char)))))
;        (json::member->value json-literal-value-expression))
;       ((when json::match?)
;        (j2f-literal-char json-inner-char))

       ;; handle Value being literal string
       ((json::pattern (:object (:member "String"
                                         (:array literalchars..))))
        (json::member->value json-literal-value-expression))
       ((when (and json::match?
                   (json::value-listp literalchars..)
                   ;; empty literal string not supported, but a later phase detects this now,
                   ;; so we took out the consp check
                   ;; (consp literalchars..)
                   ))
        (b* (((mv erp leo-chars)
              (j2f-literal-string-char-list literalchars..))
             ((when erp)
              (mv t *error-literal-expression*)))
          (mv nil
              (leo-early::make-expression-literal :get (leo-early::make-literal-string :get leo-chars))
              )))

       ;; handle Value being literal group
       ((json::pattern (:object (:member "Group"
                                         group-object)))
        ;; group-object can be (:object (:member "Single" (:string generator-multiple)))
        ;; or (:object (:member "Tuple"
        ;;                      (:object (:member "x" x-part)
        ;;                               (:member "y" y-part))))
        (json::member->value json-literal-value-expression))
       ;; x-part and y-part can be things like (:string "SignHigh")
       ;; or like (:object (:member "Number" (:string intstring))).
       ((when json::match?)
        (j2f-group-literal-expression
         (first (json::value-object->members
                 (json::member->value json-literal-value-expression)))))

       ;; handle Value being some other literal
       ((json::pattern (:object (:member value-type-name
                                         (:string value-string))))
        (json::member->value json-literal-value-expression))
       ((unless (and json::match?
                     (stringp value-type-name)
                     (stringp value-string)))
        (mv t *error-literal-expression*)))

    (if (equal value-type-name "Implicit")
        ;; j2f-implicit-expression does some extra work.  Could be replaced by
        ;; a new function (j2f-literal-implicit value-string).
        (j2f-implicit-expression (first (json::value-object->members
                                         (json::member->value json-literal-value-expression))))
      (if (equal value-type-name "Boolean")
        ;; j2f-boolean-literal-expression does some extra work.  Could be replaced by
        ;; a new function (j2f-literal-boolean value-string).
          (j2f-boolean-literal-expression (first (json::value-object->members
                                                  (json::member->value json-literal-value-expression))))
        (if (equal value-type-name "Address")
            ;; j2f-address-literal-expression does some extra work.  Could be replaced by
            ;; a new function (j2f-literal-address value-string).
            (j2f-address-literal-expression (first (json::value-object->members
                                                    (json::member->value json-literal-value-expression))))
          (if (equal value-type-name "Field")
              ;; j2f-field-literal-expression does some extra work.  Could be replaced by
              ;; a new function (j2f-literal-field value-string)
              (j2f-field-literal-expression (first (json::value-object->members
                                                    (json::member->value json-literal-value-expression))))
            (if (equal value-type-name "Scalar")
                (j2f-literal-scalar (first (json::value-object->members
                                            (json::member->value json-literal-value-expression))))
              (mv t *error-literal-expression*))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper function for binops.

(define j2f-binop-name-to-binop ((binop-name stringp))
  :returns (leo-binop binopp)
  (cond ((equal binop-name "And") (leo-early::make-binop-and))
        ((equal binop-name "Or") (leo-early::make-binop-or))
        ((equal binop-name "Eq") (leo-early::make-binop-eq))
        ((equal binop-name "Neq") (leo-early::make-binop-ne)) ; originally was "Ne"
        ((equal binop-name "Gte") (leo-early::make-binop-ge)) ; originally was "Ge"
        ((equal binop-name "Gt") (leo-early::make-binop-gt))
        ((equal binop-name "Lte") (leo-early::make-binop-le)) ; originally was "Le"
        ((equal binop-name "Lt") (leo-early::make-binop-lt))
        ((equal binop-name "Add") (leo-early::make-binop-add))
        ((equal binop-name "Sub") (leo-early::make-binop-sub))
        ((equal binop-name "Mul") (leo-early::make-binop-mul))
        ((equal binop-name "Div") (leo-early::make-binop-div))
        ((equal binop-name "Pow") (leo-early::make-binop-pow))
        ;; recently added before 2022-06-04
        ((equal binop-name "BitwiseAnd") (leo-early::make-binop-bitand))
        ((equal binop-name "BitwiseOr") (leo-early::make-binop-bitior))
        ((equal binop-name "Xor") (leo-early::make-binop-bitxor))
        ((equal binop-name "Shr") (leo-early::make-binop-shr))
        ((equal binop-name "Shl") (leo-early::make-binop-shl))

        ((equal binop-name "ShrWrapped") (leo-early::make-binop-shr-wrapped))
        ((equal binop-name "ShlWrapped") (leo-early::make-binop-shl-wrapped))

        ((equal binop-name "SubWrapped") (leo-early::make-binop-sub-wrapped))
        ((equal binop-name "AddWrapped") (leo-early::make-binop-add-wrapped))
        ((equal binop-name "DivWrapped") (leo-early::make-binop-div-wrapped))
        ((equal binop-name "MulWrapped") (leo-early::make-binop-mul-wrapped))
        ((equal binop-name "PowWrapped") (leo-early::make-binop-pow-wrapped))

        ((equal binop-name "Nand") (leo-early::make-binop-nand))
        ((equal binop-name "Nor") (leo-early::make-binop-nor))

        ((equal binop-name "Rem") (leo-early::make-binop-rem))
        ((equal binop-name "RemWrapped") (leo-early::make-binop-rem-wrapped))

        ;; TODO: temporarily relax hardness of error, just write a message,
        ;; until the number of binary ops has stabilized
        (t (prog2$ ;(er hard? 'top-level "Unknown binop name")
                   (cw "~%Unknown binary op name ~x0~%" binop-name)
                   (leo-early::make-binop-pow)))))

;; Helper function for unops

(define j2f-unary-op-name-to-unop ((unary-op-name stringp))
  :returns (leo-unop unopp)
  (cond ((equal unary-op-name "Abs") (leo-early::make-unop-abs))
        ((equal unary-op-name "AbsWrapped") (leo-early::make-unop-abs-wrapped))
        ((equal unary-op-name "Double") (leo-early::make-unop-double))
        ((equal unary-op-name "Inverse") (leo-early::make-unop-inv))
        ((equal unary-op-name "Negate") (leo-early::make-unop-neg))
        ((equal unary-op-name "Not") (leo-early::make-unop-not))
        ((equal unary-op-name "Square") (leo-early::make-unop-square))
        ((equal unary-op-name "SquareRoot") (leo-early::make-unop-square-root))
        ;; TODO: temporarily relax hardness of error, just write a message,
        ;; until the number of unary ops has stabilized
        (t (prog2$ ;(er hard? 'top-level ...)
                   (cw "~%Unknown unary op name ~x0~%" unary-op-name)
                   (leo-early::make-unop-not)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main mutual recursion for expressions

;; Q:
;; How to apply fty::defoption to a fty::deflist?
;; Can't seem to.  I think it is because nil is a legal fty::deflist.
;; But the error message is useless.

;; This is a reason to eschew a fty::deflist,
;; when one might want a fty::defoption around it.

(defines json2ast-mutual-recursion-expressions
  :short "Converts a Leo expression from JSON AST to fixtype AST."
  :parents (json2ast)

  ;; EM 2021-01: "IfElse" --> "Conditional" --> "Ternary".
  ;; I decided to rename j2f-cond-expression to j2f-ternary-expression
  (define j2f-ternary-expression ((json-ifelse-expression json::memberp))
    :returns (mv (erp booleanp) (leo-cond-expression expressionp))
    (b* (((unless (and (json::memberp json-ifelse-expression)
                       (equal "Ternary" (json::member->name json-ifelse-expression))))
          (mv t *error-cond*))
         ;; EM 2021-01: this changed from (:array ...) to an object with 3 members
         ((json::pattern (:object (:member "condition" test-expr)
                                  (:member "if_true" then-expr)
                                  (:member "if_false" else-expr)))
          (json::member->value json-ifelse-expression))
         ((unless json::match?)
          (mv t *error-cond*))
         ((mv erp-test leo-test)
          (j2f-expression test-expr))
         ((mv erp-then leo-then)
          (j2f-expression then-expr))
         ((mv erp-else leo-else)
          (j2f-expression else-expr))
         ((when (or erp-test erp-then erp-else))
          (mv t *error-cond*)))
      (mv nil
          (leo-early::make-expression-cond :test leo-test
                                :then leo-then
                                :else leo-else)))
    :measure (two-nats-measure (json::member-count json-ifelse-expression) 2))

  (define j2f-binop-expression ((json-binop-expression json::memberp))
    :returns (mv (erp booleanp) (leo-binop-expression expressionp))
    (b* (((unless (and (json::memberp json-binop-expression)
                       (equal "Binary" (json::member->name json-binop-expression))
                       (json::valuep (json::member->value json-binop-expression))
                       (equal :object (json::value-kind (json::member->value json-binop-expression)))))
          (mv t *error-binop*))
         ((json::pattern (:object (:member "left" left_operand)
                                  (:member "right" right_operand)
                                  (:member "op" (:string opname))))
          (json::member->value json-binop-expression))
         ((unless json::match?)
          (mv t *error-binop*))
         ((mv erp expression1) (j2f-expression left_operand))
         ((when erp) (mv t *error-binop*))
         ((mv erp expression2) (j2f-expression right_operand))
         ((when erp) (mv t *error-binop*)))
      (mv nil
          (leo-early::make-expression-binary
           :op (j2f-binop-name-to-binop opname)
           :arg1 expression1
           :arg2 expression2)))
    :measure (two-nats-measure (json::member-count json-binop-expression) 2))

  (define j2f-unary-expression ((json-unary-expression json::memberp))
    :returns (mv (erp booleanp) (leo-unary-expression expressionp))
    (b* (((unless (and (json::memberp json-unary-expression)
                       (equal "Unary" (json::member->name json-unary-expression))
                       (json::valuep (json::member->value json-unary-expression))
                       (equal :object (json::value-kind (json::member->value json-unary-expression)))))
          (mv t *error-unary-op*))
         ;; EM 2022-07-06 "inner" changed to "receiver"
         ((json::pattern (:object (:member "receiver" operand)
                                  (:member "op" (:string opname))))
          (json::member->value json-unary-expression))
         ((unless json::match?)
          (mv t *error-unary-op*))
         ((mv erp expression) (j2f-expression operand))
         ((when erp) (mv t *error-unary-op*)))
      (mv nil
          (leo-early::make-expression-unary
           :op (j2f-unary-op-name-to-unop opname)
           :arg expression)))
    :measure (two-nats-measure (json::member-count json-unary-expression) 2))

;;;;;;;;;;;;;;;;;;;;

  ;; Function call

  ;; This section handles "FunctionCall", which can be either
  ;; * an expression-call-top, which has an identifier for the function name, or
  ;; * an expression-call-static (struct)
  ;; * an expression-call-instance (member function of a struct)

  (define j2f-function-call-expression-top ((ident-w-span stringp)
                                            (json-array-of-arg-exprs json::valuep))
    :returns (mv (erp booleanp) (leo-funcall-top-expression expressionp))
    (b* (((unless (and (stringp ident-w-span)
                       (json::valuep json-array-of-arg-exprs)
                       (eq :ARRAY (json::value-kind json-array-of-arg-exprs))))
          (mv t *error-expression*))
         (cleaned-id-value (extract-identifier-name ident-w-span))
         ((unless (leo-early::identifier-string-p cleaned-id-value))
          (mv t *error-expression*))
         ((mv erp arg-exprs)
          (j2f-expression-list (json::value-array->elements json-array-of-arg-exprs)))
         ((when erp)
          (mv t *error-expression*)))
      (mv nil
          (leo-early::make-expression-internal-call
           :fun (leo-early::make-identifier :name cleaned-id-value)
           :args arg-exprs)))
    :measure (two-nats-measure (json::value-count json-array-of-arg-exprs) 1))

    (define j2f-function-call-expression ((json-funcall-expression json::memberp))
      :returns (mv (erp booleanp) (leo-funcall-expression expressionp))
      (b* (((unless (and (json::memberp json-funcall-expression)
                         (equal "Call" (json::member->name
                                        json-funcall-expression))))
            (mv t *error-expression*))

           ;; EM 2021-01: This has changed from an array to an object with two members
           ((json::pattern (:object (:member "function"
                                             (:object (:member "Identifier"
                                                               (:string ident-w-span))))
                                    (:member "arguments"
                                             json-array-of-arg-exprs)))
            (json::member->value json-funcall-expression))
           #|| Was:
           ((json::pattern (:array (:object (:member "Identifier"
                                                     (:string ident-w-span)))
                                   json-array-of-arg-exprs))
            (json::member->value json-funcall-expression))
           ||#
           ((when (and json::match?
                       (stringp ident-w-span)
                       (json::valuep json-array-of-arg-exprs)))
            (j2f-function-call-expression-top ident-w-span json-array-of-arg-exprs))

           )
        (mv t *error-expression*))
      :measure (two-nats-measure (json::member-count json-funcall-expression) 2))

;;;;;;;;;;;;;;;;;;;;;

  (define j2f-expression-list ((json-expressions json::value-listp))
    :returns (mv (erp booleanp) (leo-expressions expression-listp))
    (b* (((when (endp json-expressions))
          (mv nil nil))
        ((mv first-erp first-expr) (j2f-expression (car json-expressions)))
        ((mv rest-erp rest-exprs) (j2f-expression-list (cdr json-expressions))))
      (mv (or first-erp rest-erp)
          (cons first-expr rest-exprs)))
    :measure (two-nats-measure (json::value-list-count json-expressions) 0))

  (define j2f-expression ((json-expression json::valuep))
    ;; We don't know if all json expressions will come through as json-objects.
    ;; Some might be json-arrays.  Let's keep that possibility open for now.
    :returns (mv (erp booleanp) (leo-expression expressionp))

    (if (equal :object (json::value-kind json-expression))
        (if (and (= 1 (len (json::value-object->members json-expression)))
                 ;; this second conjunct is redundant, but helpful for the prover
                 (consp (json::value-object->members json-expression)))
            (let ((json-member (first (json::value-object->members json-expression))))

              ;; Handle all the json-expressions with one member here:
              ;; EM 2021-01: Appears to have changed from "FunctionCall" to "Call".
              (if (equal "Call" (json::member->name json-member))
                  (j2f-function-call-expression json-member)

                ;; EM 2021-01: "IfElse" --> "Conditional" --> "Ternary"
                (if (equal "Ternary" (json::member->name json-member))
                    (j2f-ternary-expression json-member)

                  (if (equal "Binary" (json::member->name json-member))
                      ;EM 2021: was (member (json::member->name json-member) *binop-names*)

                      (j2f-binop-expression json-member)

                    (if (equal "Unary" (json::member->name json-member))
                        (j2f-unary-expression json-member)

                    (if (equal "Literal" (json::member->name json-member))
                        ;EM 2022-06-04 Changed from "Value" to "Literal"
                        ;EM 2021 New "Value" wrapper for literals:
                        ;Address, Boolean, Field, Group, Implicit, Integer
                        (j2f-value-wrapper-expression json-member)

                          ;; EM 2020-11-21 This is a new expression.
                          ;; Grepping showed that the member-value is always a string with a nat in it.
                          (if (equal "value" (json::member->name json-member))
                              (j2f-value-expression json-member)

                          (if (equal "Implicit" (json::member->name json-member))
                              (j2f-implicit-expression json-member)
                            ;; NOTE EM 2020-11-03: I am now seeing "Implicit" expressions
                            ;; now wrapped with an extra layer of "Expression".
                            (if (equal "Expression" (json::member->name json-member))
                                (j2f-expression-expression json-member)

                                (if (equal "Identifier" (json::member->name json-member))
                                    (j2f-var-or-self-expression json-member)
                                  (if (equal "Integer" (json::member->name json-member))
                                      (j2f-integer-literal-expression json-member)
                                    (if (equal "Boolean" (json::member->name json-member))
                                        (j2f-boolean-literal-expression json-member)
                                      (if (equal "Field" (json::member->name json-member))
                                          (j2f-field-literal-expression json-member)
                                        (if (equal "Group" (json::member->name json-member))
                                            (j2f-group-literal-expression json-member)
                                          (if (equal "Address" (json::member->name json-member))
                                              (j2f-address-literal-expression json-member)

                                            ;; EM 2021-12-20  In the leo "staging" branch (not yet in "master")
                                            ;; it looks like "TupleAccess", "ArrayAccess",
                                            ;; "ArrayRangeAccess", and "CircuitMemberAccess"
                                            ;; have been renamed and split into two levels.
                                            ;; The outer level is just "Access", and then inside that there
                                            ;; is either "Tuple", "Array", "ArrayRange", and "Member", respectively.
                                            ;; So this check replaced the previous four checks.
;                                            (if (equal "Access" (json::member->name json-member))
;                                                (j2f-access-expression json-member)

;                                              (if (equal "TupleInit" (json::member->name json-member))
;                                                  (j2f-tuple-expression json-member)
;                                                (if (equal "Array" (json::member->name json-member))
;                                                    (j2f-array-expression json-member)
;                                                  (if (equal "ArrayInline" (json::member->name json-member))
;                                                      (j2f-array-expression-2 json-member)
;                                                    (if (equal "ArrayInit" (json::member->name json-member))
;                                                        (j2f-array-initializer-expression json-member)

;                                                      (if (equal "CircuitInit" (json::member->name json-member))
;                                                          (j2f-circuit-inline-expression json-member)

                                                        ;; Remove this when staging-testnet2 is merged to master.
;                                                        (if (equal "LengthOf" (json::member->name json-member))
;                                                            (j2f-lengthof-expression json-member)

                                                          ;; add more expressions with one member here
                                                          ;;   ..
                                                          ;; if it is not any of those, return error
                                                          ;; Make a fake error expression.
                                                          (mv t *error-expression*)
;                                                          )))))))
                                                          )))))))))))))))

          ;; Handle the json-expressions with 0 members or more than 1 member here:

          ;; NOTE EM 2020-11-21 I am now seeing lowercase
          ;; "identifier", with an extra "accesses" json-member.
          ;; First try is to make it a copy of j2f-var-or-self-expression.
          (let ((json-members (json::value-object->members json-expression)))
            (if (and (< 1 (len json-members))
                     (equal "identifier" (json::member->name (first json-members))))
                (j2f-var-or-self-expression-2 (first json-members))
              (mv t *error-expression*))))

      ;; Handle the json-expressions that are not of kind :object here:
      ;;  ...
      ;; (Right now we don't have any of those.)
      (mv t *error-expression*))
    :measure (two-nats-measure (json::value-count json-expression) 1))

  ;; for the defines
  :verify-guards nil ; done below
  ///
  (verify-guards j2f-expression)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statements
;; (currently above mutual recursion, but they might get brought in,
;; or get their own mutual recursion)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let/Const statements and support

;; A let or const statement does not establish a new block of statements
;; in the AST,
;; it is just a statement that introduces a new var.


;; EM 2022-07-20
;; This JSON structure:
;;              "variable_names": [
;;                {
;;                  "mutable": true,
;;                  "identifier": "{\"name\":\"y\",\"span\":\"{\\\"lo\\\":112,\\\"hi\\\":113}\"}",
;;                  "span": {
;;                    "lo": 112,
;;                    "hi": 113
;;                  }
;;                }
;;              ],
;; changed to:
;;
;;               "variable_name": "{\"name\":\"y\",\"span\":\"{\\\"lo\\\":112,\\\"hi\\\":113}\"}",
;; Besides the plural to singular change,
;; it lost the identifier level.

(define j2f-let-var ((j-var json::valuep))
  :returns (formal-var identifierp)
  (b* (
; EM 2022-07-20 was:
;       ((json::pattern (:object (:member "identifier" (:string varname))))
;        j-var)
       ((json::pattern (:string varname))
        j-var)
       ((when (and json::match? (stringp varname)))
        (let ((spanfree-varname (extract-identifier-name varname)))
          (if (and (stringp spanfree-varname)
                   (leo-early::identifier-string-p spanfree-varname))
              (leo-early::make-identifier :name spanfree-varname)
            *error-identifier*)))
       ;; EM 2022-07-20 leave this in for now, but take out when it is clearly dead
       ;; Now try a pattern with "mutable": true
       ((json::pattern (:object (:member "mutable" (:true))
                                (:member "identifier" (:string varname))))
        j-var)
       ((unless (and json::match?
                     (stringp varname)))
        *error-identifier*)
       (spanfree-varname (extract-identifier-name varname))
       ((unless (and (stringp spanfree-varname)
                     (leo-early::identifier-string-p spanfree-varname)))
        *error-identifier*))
    (leo-early::make-identifier :name spanfree-varname)))

(define j2f-let-vars ((j-vars json::value-listp))
  :returns (formal-vars identifier-listp)
  (if (endp j-vars)
      nil
    (cons (j2f-let-var (car j-vars))
          (j2f-let-vars (cdr j-vars)))))

;; 2020-11-03: At first I was not seeing any "mutable" member, but now
;; I see (:member "mutable (:false)).  So let's support both.
(define j2f-const-var ((j-var json::valuep))
  :returns (formal-var identifierp)
  (b* (
; EM 2022-07-20 was:
;       ((json::pattern (:object (:member "identifier" (:string varname)))) j-var)
       ((json::pattern (:string varname))
        j-var)
       ((when (and json::match? (stringp varname)))
        (let ((spanfree-varname (extract-identifier-name varname)))
          (if (and (stringp spanfree-varname)
                   (leo-early::identifier-string-p spanfree-varname))
              (leo-early::make-identifier :name spanfree-varname)
            *error-identifier*)))
       ;; EM 2022-07-20 leave this in for now, but take out when it is clearly dead
       ;; Now try the new pattern
       ((json::pattern (:object (:member "mutable" (:false))
                                (:member "identifier" (:string varname)))) j-var)
        ((unless (and json::match?
                      (stringp varname)))
         *error-identifier*)
        (spanfree-varname (extract-identifier-name varname))
        ((unless (and (stringp spanfree-varname)
                      (leo-early::identifier-string-p spanfree-varname)))
         *error-identifier*))
    (leo-early::make-identifier :name spanfree-varname)))

(define j2f-const-vars ((j-vars json::value-listp))
  :returns (formal-vars identifier-listp)
  (if (endp j-vars)
      nil
    (cons (j2f-const-var (car j-vars))
          (j2f-const-vars (cdr j-vars)))))

;; Currently the same for let and const
(define j2f-let-type ((j-let-type json::valuep))
  :returns (mv (erp booleanp) (formal-type leo-early::type-optionp))
  ;; often the type specifier is left off the let-binding
  (json::value-case j-let-type
      :null (mv nil nil)
      :otherwise
      (j2f-type j-let-type)))

;; Currently the same for let and const
(define j2f-let-init ((j-let-init json::valuep))
  :returns (formal-init expressionp)
  (mv-let (erp val)
      (j2f-expression j-let-init)
    (if erp
        *error-expression*
      val)))

#||
  ;; I need member patvars.
  (b* (((unless (and (json::valuep j-let-init)
                     (eq :object (json::value-kind j-let-init))
                     (consp (json::value-object->members j-let-init))
                     (json::memberp (car (json::value-object->members j-let-init)))
                     ;; so far only seen a single member
                     (null (cdr (json::value-object->members j-let-init)))))
        *error-expression*))
)) ||#


(define j2f-let-body ((def-member-val json::valuep))
  :returns (mv (erp booleanp) (leo-vardecl vardeclp))
  ;; Note: this returns an error object if "declaration_type" is not "Let"
  (b* (((json::pattern (:object (:member "declaration_type" (:string let-or-const))
                                ;; EM 2022-07-20 changed from "variable_names"
                                ;; to "variable_name"
                                ;; (:array of jvars changed to single :string)
                                (:member "variable_name" jvars)
                                (:member "type_" vartype)
                                (:member "value" jexpr)))
        def-member-val)
       ((unless (and json::match?
                     (equal let-or-const "Let")
                     (json::valuep jvars) (json::valuep vartype) (json::valuep jexpr)
                     (eq :string (json::value-kind jvars))
                     (json::valuep jexpr)
                     (eq :object (json::value-kind jexpr))))
        (mv t *error-vardecl*))

       ;; If there is more than one var, we have
       ;; * a list of N vars
       ;; * ?? types ?? - right now I just have (:null)
       ;; * one tuple expression with N subexpressions
       ;; EM 2022-07-20 Just one var now, so put a list around it.

       ;; first compute the :vars, :type, and :init
       ;(let-vars (j2f-let-vars (json::value-array->elements jvars)))
       (let-vars (j2f-let-vars (list jvars)))
       ((mv erp type) (j2f-let-type vartype))
       ((when erp) (mv t *error-vardecl*))
       (init (j2f-let-init jexpr))

       ;; If we see an error in the let, return an error statement.
       ((when (or (and (consp let-vars) (member-equal *error-identifier* let-vars))
                  ;(equal type *error-type*) we don't have an error type yet,
                  ; so it does an er hard?
                  (equal init *error-expression*)))
        (mv t *error-vardecl*)))

;    (mv nil (leo-early::make-vardecl :names let-vars :type? type :init init))
    (mv nil (leo-early::make-vardecl :name (car let-vars) :type type :init init))
    ))

(define j2f-const-body ((def-member-val json::valuep))
  :returns (mv (erp booleanp) (leo-constdecl constdeclp))
  ;; Note: this returns an error object if "declaration_type" is not "Const"
  (b* (((json::pattern (:object (:member "declaration_type" (:string let-or-const))
                                ;; EM 2022-07-20 changed from "variable_names"
                                ;; to "variable_name"
                                ;; (:array of jvars changed to single :string)
                                (:member "variable_name" jvars)
                                (:member "type_" vartype)
                                (:member "value" jexpr)))
        def-member-val)
       ((unless (and json::match?
                     (equal let-or-const "Const")
                     (json::valuep jvars) (json::valuep vartype) (json::valuep jexpr)
                     (eq :string (json::value-kind jvars))
                     (json::valuep jexpr)
                     (eq :object (json::value-kind jexpr))))
        (mv t *error-constdecl*))

       ;; If there is more than one var, we have
       ;; * a list of N vars
       ;; * ?? types ?? - right now I just have (:null)
       ;; * one tuple expression with N subexpressions
       ;; EM 2022-07-20 Just one var now, so put a list around it.

       ;; first compute the :vars, :type, and :init
       ;(const-vars (j2f-const-vars (json::value-array->elements jvars)))
       (const-vars (j2f-const-vars (list jvars)))
       ((mv erp type) (j2f-let-type vartype)) ; also works for const type
       ((when erp) (mv t *error-constdecl*))
       (init (j2f-let-init jexpr))

       ;; If we see an error in the let, return an error statement.
       ((when (or (and (consp const-vars)
                       ; *error-identifier* functions both as a let-var error
                       ; and a const-var error
                       (member-equal *error-identifier* const-vars))
                  ;(equal type *error-type*) we don't have an error type yet,
                  ; so it does an er hard?
                  (equal init *error-expression*)))
        (mv t *error-constdecl*)))

;    (mv nil (leo-early::make-constdecl :names const-vars :type? type :init init))
    (mv nil (leo-early::make-constdecl :name (car const-vars) :type type :init init))
    ))

(define j2f-let-statement ((def-member-val json::valuep))
  :returns (mv (erp booleanp) (leo-let-statment statementp))

  (b* (((unless (json::valuep def-member-val))
        (mv t *error-let-statement*))
       ((mv erp vardecl) (j2f-let-body def-member-val))
       ((when erp) (mv t *error-let-statement*)))
    (mv nil (leo-early::make-statement-let :get vardecl))))

(define j2f-const-statement ((def-member-val json::valuep))
  :returns (mv (erp booleanp) (leo-const-statment statementp))

  (b* (((unless (json::valuep def-member-val))
        (mv t *error-let-statement*))
       ((mv erp constdecl) (j2f-const-body def-member-val))
       ((when erp) (mv t *error-const-statement*)))
    (mv nil (leo-early::make-statement-const :get constdecl))))

(define j2f-let-or-const-statement ((json-let-or-const-statement json::memberp))
  :returns (mv (erp booleanp) (leo-let-or-const-statement statementp))
  :short "Converts a json-member let statement to a leo::statmement of kind :let."
  :parents (json2ast)

  (b* (((unless (and (json::memberp json-let-or-const-statement)
                     (equal "Definition" (json::member->name json-let-or-const-statement))))
        (mv t *error-let-statement*))
       (def-member-val (json::member->value json-let-or-const-statement))

       ;; dispatch to let or const here, so they can differ later
       ;; (they don't differ now, but they might in the future,
       ;; and this lets us reuse the body code for global consts)
       ((json::pattern (:object (:member "declaration_type" (:string let-or-const))
                                *..))
        def-member-val)
       ((unless (and json::match?
                     (member-equal let-or-const '("Let" "Const"))))
        (mv t *error-let-statement*)))
    (if (equal let-or-const "Let")
        (j2f-let-statement def-member-val)
      (j2f-const-statement def-member-val))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Left-hand-side expression of assignment statement

;; The left-hand-side is the value of the "assignee" member.
;; It contains an identifier and an array of "accesses".
;; The "accesses" can be
;;   simple identifier,
;;   array indexing,
;;   array range indexing,
;;   tuple indexing, and
;;   circuit member access.
;; (Those are all EM knows of right now.)
;; We turn the json left-hand-side into the same acl2 ast as it would be
;; if it were on the rhs.

;(define j2f-wrap-lhs-access ((leo-expr-so-far expressionp) (json-lhs-accessor json::valuep))
;  :returns (mv (erp booleanp) (leo-lhs-expression expressionp))
;  (b* (((unless (and (expressionp leo-expr-so-far)
;                     (json::valuep json-lhs-accessor)
;                     (json::value-case json-lhs-accessor :object)))
;        (mv t *error-expression*))

;       ;; array access
;       ((json::pattern (:object (:member "ArrayIndex" json-index))) json-lhs-accessor)
;       ((when (and json::match?
;                   (json::valuep json-index)))
;        (b* (((mv erp leo-accessor) (j2f-expression json-index)))
;          (if erp
;              (mv t *error-expression*)
;            (mv nil (leo-early::make-expression-array-element :array leo-expr-so-far
;                                                   :index leo-accessor)))))

;       ;; array access
;       ((json::pattern (:object (:member "ArrayRange"
;                                         (:array lb ub))))
;        json-lhs-accessor)
;       ((when (and json::match?
;                   (json::valuep lb)
;                   (json::valuep ub)))
;        (b* (;; array ranges on the lhs of an assignment are not currently supported,
;             ;; but we should build the ast and let static checking catch it
;             (left-omitted? (json::value-case lb :null))
;             (right-omitted? (json::value-case ub :null))

;             ;; The only other kind of value should be :object
;             (left-valuep? (json::value-case lb :object))
;             (right-valuep? (json::value-case ub :object))
;             ((unless (or left-omitted? left-valuep?))
;              (mv t *error-expression*))
;             ((unless (or right-omitted? right-valuep?))
;              (mv t *error-expression*))

;             ((mv erp-lb leo-lb) (if left-omitted?
;                                     (mv nil nil)
;                                   (j2f-expression lb)))
;             ((mv erp-ub leo-ub) (if right-omitted?
;                                     (mv nil nil)
;                                   (j2f-expression ub))))
;          (if erp-lb
;              (mv t *error-expression*)
;            (if erp-ub
;              (mv t *error-expression*)
;            (mv nil (leo-early::make-expression-array-range :array leo-expr-so-far
;                                                 :from? leo-lb
;                                                 :to? leo-ub)))))
;        )

;       ;; tuple access
;       ((json::pattern (:object (:member "Tuple" json-tuple-index))) json-lhs-accessor)
;       ((when (and json::match?
;                   (json::valuep json-tuple-index)))
;        (b* (((mv erp leo-accessor) (j2f-expression json-tuple-index)))
;          (if (or erp
;                  (not (expressionp leo-accessor))
;                  (not (eq :LIT (expression-kind leo-accessor)))
;                  (not (literalp (expression-lit->get leo-accessor)))
;                  (not (eq :UNTYPED (literal-kind (expression-lit->get leo-accessor))))
;                  (not (natp (literal-untyped->val (expression-lit->get leo-accessor)))))
;              (mv t *error-expression*)
;            (mv nil (leo-early::make-expression-tuple-element
;                     :tuple leo-expr-so-far
;                     ;; TODO: revist if abstract syntax changes.  This gets a nat.
;                     :index (literal-untyped->val (expression-lit->get leo-accessor)))))))

;       ;; circuit member access
;       ((json::pattern (:object (:member "Member"
;                                         (:string memberdef-name-w-span))))
;        json-lhs-accessor)
;       ((when (and json::match?
;                   (stringp memberdef-name-w-span)))
;        (b* ((memberdef-name (extract-identifier-name memberdef-name-w-span))
;             ((unless (leo-early::identifier-string-p memberdef-name))
;              (mv t *error-expression*)))
;          (mv nil (leo-early::make-expression-circuit-member
;                   :circuit leo-expr-so-far
;                   :member (leo-early::make-identifier :name memberdef-name)))))

;       ;; New kinds of lhs accessors can go here
;       )

;    ;; If none of those match, return an error
;    (mv t *error-expression*)))

;(define j2f-wrap-lhs-accesses ((leo-expr-so-far expressionp) (json-lhs-remaining json::value-listp))
;  :returns (mv (erp booleanp) (leo-lhs-expression expressionp))
;  (if (or (not (expressionp leo-expr-so-far))
;          (not (json::value-listp json-lhs-remaining)))
;      (mv t *error-expression*)
;    (if (endp json-lhs-remaining)
;        (mv nil leo-expr-so-far)
;      (b* ((json-first-accessor (first json-lhs-remaining))
;           ((mv erp leo-wrapped-first-accessor)
;            (j2f-wrap-lhs-access leo-expr-so-far json-first-accessor))
;           ((when erp)
;            (mv t *error-expression*)))
;        (j2f-wrap-lhs-accesses leo-wrapped-first-accessor (cdr json-lhs-remaining)))))
;  :measure (acl2-count json-lhs-remaining))

(define j2f-lhs-expression ((json-assignee json::valuep))
  :returns (mv (erp booleanp) (leo-lhs-expression expressionp))
  (b* (((unless (json::value-case json-assignee :object))
        (mv t *error-expression*))
       ((json::pattern (:object ; EM 2022-07-30 "identifier" -> "Identifier"
                                (:member "Identifier" (:string id-with-span))
                                ; EM 2022-05-18 "accesses" is still in the AST
                                ; although it had better be an empty array now.
                                ; EM 2022-07-30 "accesses" is now gone in
                                ; observed examples.
                                ;(:member "accesses" (:array json-lhs-accesses..))
                                ))
        json-assignee)
       ((unless (and json::match?
                     (stringp id-with-span)
                     ;(null json-lhs-accesses..) ; EM 2022-05-18
                     ;(json::value-listp json-lhs-accesses..)
                     ))
        (mv t *error-expression*))
       (ident (extract-identifier-name id-with-span))
       ((unless (or (equal ident "self")
                    (leo-early::identifier-string-p ident)))
        (mv t *error-expression*))
       (leo-id-ref-expression
;        (if (equal ident "self" )
;            (leo-early::make-expression-self)
          (leo-early::make-expression-var/const
           :name (leo-early::make-identifier :name ident))
;          )
       ))
    ;(j2f-wrap-lhs-accesses leo-id-ref-expression json-lhs-accesses..)
    (mv nil leo-id-ref-expression)
    ))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assign statement

;(defconst *assignment-kind-string-to-op3*
;  `(("Assign" . ,(leo-early::make-asgop-asg))
;    ("Add" . ,(leo-early::make-asgop-asg-add))
;    ("Sub" . ,(leo-early::make-asgop-asg-sub))
;    ("Mul" . ,(leo-early::make-asgop-asg-mul))
;    ("Div" . ,(leo-early::make-asgop-asg-div))
;    ("Pow" . ,(leo-early::make-asgop-asg-pow))))

(define j2f-assign-statement ((json-assign-statement json::memberp))
  :returns (mv (erp booleanp) (leo-assign-statement statementp))
  :short "Converts a json-member Assign statement to a leo::statement of kind :assign"
  :parents (json2ast)

  (b* (((unless (and (json::memberp json-assign-statement)
                     (equal "Assign" (json::member->name json-assign-statement))))
        (mv t *error-assign-statement*))
       ;; The member value is a json-array with two expressions in it
       (lhs-and-rhs (json::member->value json-assign-statement))
       ;; EM 2021-01: this changed from (:array lhs-expr rhs-expr).
       ;;   Besides that, now "operation" indicates the kind of assignment.
       ;;   Regular assignment is "Assign";
       ;;   compound assignment operators such as x += 3 are
       ;;   (according to statements/assign/mod.rs):
       ;;   "Add", "Sub", "Mul", "Div", and "Pow".

        ;; EM 2022-07-30 observed "assignee" -> "place"
        ((json::pattern (:object (:member "operation" (:string assignment-kind))
                                (:member "place" lhs-stuff)
                                (:member "value" rhs-expr)))
        lhs-and-rhs)
       ((unless (and json::match?
                     (stringp assignment-kind)
                     (eq :object (json::value-kind lhs-stuff))
                     (eq :object (json::value-kind rhs-expr))))
        (mv t *error-assign-statement*))

;       (assignment-kind-op (cdr (assoc-equal assignment-kind *assignment-kind-string-to-op3*)))
;       ((unless (asgopp assignment-kind-op))
;        ;; Unknown assignment kind string
;        (mv t *error-assign-statement*))

       ((mv erp leo-lhs-expression) (j2f-lhs-expression lhs-stuff))
       ((when erp)
        (mv t *error-assign-statement*))

       #|| from version prior to 2021-01:
       ((mv lhs-erp leo-lhs) (if array-assignee?
                                 (j2f-array-assignee-expression (car lhs-members))
                               (j2f-expression lhs-expr)))
       ||#
       ((mv rhs-erp leo-rhs) (j2f-expression rhs-expr))
       ((when rhs-erp)
        (mv t *error-assign-statement*)))
    (mv nil
        (leo-early::make-statement-assign ;:op assignment-kind-op
                               :left leo-lhs-expression
                               :right leo-rhs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return statement

(define j2f-return-statement ((json-return-statement json::memberp))
  :returns (mv (erp booleanp) (leo-return-statement statementp))
  :short "Converts a json-member return statement to a leo::statement of kind :return."
  :parents (json2ast)

  (b* (((unless (and (json::memberp json-return-statement)
                     (equal "Return" (json::member->name json-return-statement))))
        (mv t *error-return-statement*))

       ;; EM 2021-01: There is a new member wrapper with member-name "expression"
       ((json::pattern (:object (:member "expression" json-return-statement-expression)))
        (json::member->value json-return-statement))
       ((unless json::match?)
        (mv t *error-return-statement*))
       #|| was:
       (json-return-statement-expression (json::member->value json-return-statement))
       ((unless (and (json::valuep json-return-statement-expression)
                     (json::value-case json-return-statement-expression :object)))
        (mv t *error-return-statement*))
       ||#
       ((mv erp leo-return-expression) (j2f-expression json-return-statement-expression)))
    (mv erp (leo-early::make-statement-return :value leo-return-expression))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Console statements

(define j2f-console-assert ((json-console-assert json::memberp))
  :returns (mv (erp booleanp) (leo-console-assert consolep))
  :short "Converts a json-member console assert statement to a leo::statement of kind :console"
  :parents (json2ast)

  (b* (((require-json-member-with-name json-console-assert "Assert" *error-console-assert*))
       (jc-assert-value (json::member->value json-console-assert))
       ;; the value must be the expression.  Checking the type of json value
       ;; and the contents of the object members is done in j2f-expression.
       ((mv erp leo-console-assert-expression) (j2f-expression jc-assert-value)))
    (mv erp
        (leo-early::make-console-assert :arg leo-console-assert-expression))))

;;; 2021-07-22 EM: The Leo AST no longer contains a parsed, structured format string,
;;; so this code is currently unused.
;;; We may want to reuse this code later.
(define char-list-to-char/container-list ((char-list character-listp))
  :returns (elements leo-early::char/container-listp)
  (if (endp char-list)
      nil
    (cons (leo-early::make-char/container-char :get (leo-early::make-char :codepoint (char-code (first char-list))))
          (char-list-to-char/container-list (rest char-list)))))

;;; 2021-07-22 EM: The Leo AST no longer contains a parsed, structured format string,
;;; so this code is currently unused.
;;; We may want to reuse this code later.
(define string-to-char/container-list ((str stringp))
  :returns (elements leo-early::char/container-listp)
  (char-list-to-char/container-list (acl2::explode str)))

;;; 2021-07-22 EM: The Leo AST no longer contains a parsed, structured format string,
;;; so this code is currently unused.
;;; We may want to reuse this code later.
(define j2f-format-string-item ((json-format-string-part json::valuep))
  :returns (mv (erp booleanp) (elements leo-early::char/container-listp))
  (b* (((json::pattern (:object (:member "Const" (:string the-string))))
        json-format-string-part)
       ((when json::match?)
        (mv nil (string-to-char/container-list the-string)))
       ((json::pattern "Container")
        json-format-string-part)
       ((when json::match?)
        (mv nil (list (leo-early::make-char/container-container)))))
    (mv t nil)))

;;; 2021-07-22 EM: The Leo AST no longer contains a parsed, structured format string,
;;; so this code is currently unused.
;;; We may want to reuse this code later.
(define j2f-format-string-items ((json-format-string-parts json::value-listp))
  :returns (mv (erp booleanp) (elements leo-early::char/container-listp))
  (b* (((when (endp json-format-string-parts))
        (mv nil nil))
       ((mv erp elements-from-first-item)
        (j2f-format-string-item (first json-format-string-parts)))
       ((when erp)
        (mv t nil))
       ((mv erp elements-from-rest-items)
        (j2f-format-string-items (rest json-format-string-parts)))
       ((when erp)
        (mv t nil))
       ;; both lists are clearly leo-early::char/container-listp, but
       ;; the prover is having trouble with
       ;; DEFTHM LEO-EARLY::CHAR/CONTAINER-LISTP-OF-J2F-FORMAT-STRING-ITEMS.ELEMENTS
       ;; so check again here.
       ((unless (leo-early::char/container-listp elements-from-first-item))
        (mv t nil))
       ((unless (leo-early::char/container-listp elements-from-rest-items))
        (mv t nil))
       ;; also append them here.  Somehow the prover doesn't know
       ;; that when two leo-early::char/container-listp items are appended, the result
       ;; is also leo-early::char/container-listp.
       (appended-elements
        (append elements-from-first-item elements-from-rest-items))
       ((unless (leo-early::char/container-listp appended-elements))
        (mv t nil))
       )
    (mv nil
        appended-elements)))

;;; 2021-07-22 EM: The Leo AST no longer contains a parsed, structured format string,
;;; so this code is currently unused.
;;; We may want to reuse this code later.
(define j2f-format-string ((json-format-string-parts json::value-listp))
  :returns (mv (erp booleanp) (leo-format-string format-stringp))
  (b* (((mv erp leo-format-string-elements) (j2f-format-string-items json-format-string-parts))
       ((when erp)
        (mv t *error-format-string*)))
    (mv nil (leo-early::make-format-string :elements leo-format-string-elements))))

(define j2f-console-log ((json-console-log json::memberp))
  :returns (mv (erp booleanp) (leo-console-log consolep))
  :short "Converts a json-member console log statement to a leo::statement of kind :console"
  :parents (json2ast)

  (b* (((require-json-member-with-name json-console-log "Log" *error-console-log*))
       ((json::pattern (:object (:member "string"
                                         ;; EM 2022-07-30 changed from :array to :string
                                         ;(:array literalchars..)
                                         (:string litstring))
                                (:member "parameters" (:array formatting-string-parameters..))))
        (json::member->value json-console-log))
;; 2021-07-22 EM: pattern was like this:
;;       ((json::pattern (:object (:member "parts" (:array formatting-string-parts..))
;;                                (:member "parameters" (:array formatting-string-parameters..))))
;;        (json::member->value json-console-log))
       ((unless (and json::match?
                     (stringp litstring)
                     ;(json::value-listp literalchars..)
                     ))
        (mv t *error-console-log*))
;;       ((mv erp leo-format-string)
;;        (j2f-format-string formatting-string-parts..))
;       ((mv erp leo-chars)
;        (j2f-literal-string-char-list literalchars..))
;       ((when erp)
;        (mv t *error-console-log*))
       ((mv erp leo-params)
        (j2f-expression-list formatting-string-parameters..))
       ((when erp)
        (mv t *error-console-log*))
       )
    (mv nil
        (leo-early::make-console-log
         :string (acl2::explode litstring) ;leo-chars
         :exprs leo-params))))

(define j2f-console-error ((json-console-error json::memberp))
  :returns (mv (erp booleanp) (leo-console-error-statement consolep))
  :short "Converts a json-member console error statement to a leo::statement of kind :console"
  :parents (json2ast)

  (b* (((require-json-member-with-name json-console-error "Error" *error-console-error*))
       ((json::pattern (:object (:member "string"
                                         ;; EM 2022-07-30 changed from :array to :string
                                         ;(:array literalchars..)
                                         (:string litstring))
                                (:member "parameters" (:array formatting-string-parameters..))))
        (json::member->value json-console-error))
       ((unless (and json::match?
                     (stringp litstring)
                     ;(json::value-listp literalchars..)
                     ))
        (mv t *error-console-error*))
;;       ((mv erp leo-format-string)
;;        (j2f-format-string formatting-string-parts..))
;       ((mv erp leo-chars)
;        (j2f-literal-string-char-list literalchars..))
;       ((when erp)
;        (mv t *error-console-error*))
       ((mv erp leo-params)
        (j2f-expression-list formatting-string-parameters..))
       ((when erp)
        (mv t *error-console-error*))
       )
    (mv nil
        (leo-early::make-console-error
         :string (acl2::explode litstring) ;leo-chars
         :exprs leo-params))))

(define j2f-console-statement ((json-console-statement json::memberp))
  :returns (mv (erp booleanp) (leo-console-statement statementp))
  :short "Converts a json-member console statement to a leo::statement of kind :console"
  :parents (json2ast)

  (b* (((require-json-member-with-name json-console-statement "Console" *error-console-statement*))
       ;; The json-member console statement has a value that is
       ;; a JSON-object with a single member, with name "function"
       ;; and with value being the rest of the statement.
       (jcs-value (json::member->value json-console-statement))
       ;(- (cw "jcs-value: ~x0~%" jcs-value))
       ((require-json-object-with-single-member jcs-value *error-console-statement*))
       (jcs-function (first (json::value-object->members jcs-value)))
       ;(- (cw "jcs-function: ~x0~%" jcs-function))

       ((require-json-member-with-name jcs-function "function" *error-console-statement*))
       (jcs-function-value (json::member->value jcs-function))
       ;(- (cw "jcs-function-value: ~x0~%" jcs-function-value))
       ((require-json-object-with-single-member jcs-function-value *error-console-statement*))
       (jcs-specific-function (first (json::value-object->members jcs-function-value)))
       ;(- (cw "jcs-specific-function: ~x0~%" jcs-specific-function))

       ;; jcs-specific-function is a JSON-member
       ;; whose name is in the set {"Assert", "Log", "Debug", "Error"}
       (jcs-specific-function-name (json::member->name jcs-specific-function))
       ;(- (cw "jcs-specific-function-name: ~x0~%" jcs-specific-function-name))
       ((mv erp console-function)
        (cond ((equal jcs-specific-function-name "Assert")
               (j2f-console-assert jcs-specific-function))
              ((equal jcs-specific-function-name "Log")
               (j2f-console-log jcs-specific-function))
;              ((equal jcs-specific-function-name "Debug")
;               (j2f-console-debug jcs-specific-function))
              ((equal jcs-specific-function-name "Error")
               (j2f-console-error jcs-specific-function))
              ;; if none of those four, use a special console-error object to indicate that
              (t (mv t *error-outer-console-error*)))))
    (mv erp (leo-early::make-statement-console :get console-function))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Statements Mutual Recursion

;; Control statements
;; that can contain other statements.
;;
;; The abstract syntax shows the following recursive types for Leo statements:
;;   statement statement-list branch branch-list
;;
;; For j2f, we need to know what kinds of statements are in the recursion.
;; That would be:
;;   :for and :if
;; So the j2f functions in the recursion are:
;;   j2f-statement, j2f-statements,
;;   j2f-iteration-statement, j2f-if-statement,
;;   j2f-branch (?), j2f-branches (?)
;;
;; All the other statements are leaves.
;; Fortunately, you can't have a statement under an expression.
;; We should try to keep it that way.

(defines json2ast-mutual-recursion-statements
  :short "Converts a Leo statement from JSON AST to fixtype AST."
  :parents (json2ast)

  (define j2f-iteration-statement ((json-iteration-statement json::memberp))
    :returns (mv (erp booleanp) (leo-for-statement statementp))
    :short "Converts a json-member Iteration statement to a leo::statement of kind :for"
    :parents (json2ast)
    (b* (((unless (and (json::memberp json-iteration-statement)
                       (equal "Iteration" (json::member->name json-iteration-statement))))
          (mv t *error-iteration-statement*))
         ;; EM 2021-01 changed again.  What was (:array _ (:array lb ub) stmts)
         ;; is now an object with 4 members: "variable", "start", "stop", and "block".
         ;; EM 2020-12-10 this changed.  the 3rd thing was a :array but now the array
         ;;   has (:object (member "statements") ..) wrapped around it.
         ;; EM 2020-11-21 this changed. #2 and #3 have been combined into an array.
         ;; Was:
         ;; ;; I'm seeing the member value being an array with 4 things:
         ;; ;; 1. :string name (with span to be removed)
         ;; ;; 2. :object expression for lower bound
         ;; ;; 3. :object expression for upper bound
         ;; ;; 4. :array with body statements.  This and the :if construct need
         ;; ;;    to be in a mutual recursion.
         ;; Now:
         ;; I'm seeing the member value being an array with 4 things:
         ;; 1. :string name (with span to be removed)
         ;; 2. :array with two items: :object expression for lower bound
         ;;                           :object expression for upper bound
         ;; 4. :array with body statements.  This and the :if construct need
         ;;    to be in a mutual recursion.
         (contents (json::member->value json-iteration-statement))
         ((json::pattern (:object (:member "variable" (:string itervar))
                                  (:member "type_" iter-type)
                                  (:member "start" lb-expr)
                                  (:member "stop" ub-expr)
                                  (:member "inclusive" true-or-false)
                                  (:member "block" (:object (:member "statements"
                                                                     block-statements-array)))))
          contents)
         ((unless (and json::match?
                       ; EM 2022-07-30 ast of type has changed.
                       ; E.g., this is not an :object : (JSON::VALUE :STRING "U32")
                       ;(eq :object (json::value-kind iter-type))
                       (eq :object (json::value-kind lb-expr))
                       (eq :object (json::value-kind ub-expr))
                       (json::value-case true-or-false :true t :false t :otherwise nil)
                       (eq :array (json::value-kind block-statements-array))))
          (mv t *error-iteration-statement*))
         (cleaned-id-value (extract-identifier-name itervar))
         ((unless (leo-early::identifier-string-p cleaned-id-value))
          (mv t *error-iteration-statement*))
         (itervar-identifier (leo-early::make-identifier :name cleaned-id-value))
         ((mv type-erp leo-type) (j2f-type iter-type))
         ((mv lb-erp leo-lb) (j2f-expression lb-expr))
         ((mv ub-erp leo-ub) (j2f-expression ub-expr))
         ((when (or lb-erp ub-erp type-erp))
          (mv t *error-iteration-statement*))
         ((mv erp leo-statements)
          (j2f-statements (json::value-array->elements block-statements-array)))
         ((when erp)
          (mv t *error-iteration-statement*)))
      (mv nil
          (leo-early::make-statement-for :name itervar-identifier
                              :type leo-type
                              :from leo-lb
                              :to leo-ub
                              :inclusivep nil
;                              :inclusive (json::value-case true-or-false
;                                           :true t :false nil
;                                           :otherwise
;                                           (er hard? 'top-level "bad value of statement-for->inclusive"))
                              :body leo-statements)))
     :measure (two-nats-measure (json::member-count json-iteration-statement) 2))

  ;; TODO: when we have an error alternative in deftagsum statement,
  ;; change the *error-return-statement* occurrences below.

  (define j2f-statement ((json-statement json::valuep))
    :returns (mv (erp booleanp) (leo-stmt statementp))
    :short "Converts a json-statement to a leo::statement."
    :parents (json2ast)
    (b* (((unless (and (json::valuep json-statement)
                       (json::value-case json-statement :object)))
          (mv t *error-return-statement*))
         (json-stmt-object-members (json::value-object->members json-statement))
         ((unless (and (= 1 (len json-stmt-object-members))
                       ;; these next conjuncts are redundant, but helpful for the prover
                       (consp json-stmt-object-members)
                       (endp (cdr json-stmt-object-members))))
          (mv t *error-return-statement*))
         (json-member (first json-stmt-object-members))
         (json-statement-type (json::member->name json-member))
         ((unless (stringp json-statement-type))
          (mv t *error-return-statement*)))
      (if (equal "Return" json-statement-type)
          ;; To maintain consistency with the other statements,
          ;; we pass the object member including the "Return" name.
          (j2f-return-statement json-member)
        (if (equal "Console" json-statement-type)
            (j2f-console-statement json-member)
          (if (equal "Definition" json-statement-type) ; let or const statement
              (j2f-let-or-const-statement json-member)
            (if (equal "Assign" json-statement-type)
                (j2f-assign-statement json-member)
              (if (equal "Iteration" json-statement-type)
                  (j2f-iteration-statement json-member)
                (if (equal "Conditional" json-statement-type)
                    (j2f-if-statement json-member)
;                  (if (equal "Expression" json-statement-type)
;                      (j2f-expression-statement json-member)
                    (if (equal "Block" json-statement-type)
                        (j2f-block-statement json-member)
                      ;; Other statement types go here:
                      ;;   ...
                      ;; If none of them match, return an error:
                      (prog2$ (cw "ERROR: unknown statement type ~x0~%" json-statement-type)
                              (mv t *error-return-statement*))
                    ))))))))
     :measure (two-nats-measure (json::value-count json-statement) 1))

  ;; statement-list occurs in the abstract-syntax as
  ;; the body of a for, branch, and functiondef

  ;; We should already have seen past the member <"statements", [..]>
  ;; and the param should be the array elements that are the statements.
  (define j2f-statements ((json-statements json::value-listp))
    :returns (mv (erp booleanp) (leo-statements statement-listp))
    :short "Converts a list of json-statement to a leo::statement-list."
    :parents (json2ast)
    (b* (((when (endp json-statements))
          (mv nil nil))
         (stmt (first json-statements))
         ((mv erp leo-stmt) (j2f-statement stmt))
         ((when erp) (mv t nil))
         ((mv erp rest-leo-stmts) (j2f-statements (rest json-statements)))
         ((when erp) (mv t nil)))
      (mv nil (cons leo-stmt rest-leo-stmts)))
     :measure (two-nats-measure (json::value-list-count json-statements) 0))

  (define j2f-block-statement ((json-block-statement json::memberp))
    :returns (mv (erp booleanp)
                 (leo-block-statement statementp))
    :short "Converts a JSON block statement into a leo::statement of kind :block."
    :parents (json2ast)
    (b* (((unless (and (json::memberp json-block-statement)
                       (equal "Block" (json::member->name json-block-statement))))
          (mv t *error-block-statement*))
         ((json::pattern (:object (:member "statements" (:array inner-statements..))))
          (json::member->value json-block-statement))
         ((unless (and json::match?
                       (json::value-listp inner-statements..)))
          (mv t *error-block-statement*))
         ((mv erp leo-statements)
          (j2f-statements inner-statements..))
         ((when erp)
          (mv t *error-block-statement*)))
      (mv nil (leo-early::make-statement-block :get leo-statements)))
    :measure (two-nats-measure (json::member-count json-block-statement) 2))

  ;; EM: changed to have "block" around "statements".
  (define j2f-if-statement ((json-conditional-statement json::memberp))
    :returns (mv (erp booleanp) (leo-if-statement statementp))
    :short "Converts a JSON if statement into a leo::statement of kind :if."
    :parents (json2ast)
    (b* (((unless (and (json::memberp json-conditional-statement)
                       (equal "Conditional" (json::member->name json-conditional-statement))))
          (mv t *error-conditional-statement*))
         ;; EM 2022-07-30 observed "block" -> "then" and "next" -> "otherwise".
         ;; The JSON always shows "otherwise" as the else clause,
         ;; and its value is JSON-null if there was no else clause.
         ((json::pattern (:object (:member "condition" branch-1-condition-expr)
                                  (:member "then" (:object (:member "statements" branch-1-statements)))
                                  (:member "otherwise" remaining-branches-and-last-else)))
          (json::member->value json-conditional-statement))
         ((unless (and json::match?
                       (eq :object (json::value-kind branch-1-condition-expr))
                       (eq :array (json::value-kind branch-1-statements))))
          (mv t *error-conditional-statement*))

         ((mv erp leo-b1-condition) (j2f-expression branch-1-condition-expr))
         ((when erp) (mv t *error-conditional-statement*))
         ((mv erp leo-b1-statements) (j2f-statements (json::value-array->elements branch-1-statements)))
         ((when erp) (mv t *error-conditional-statement*))
         (leo-first-branch (leo-early::make-branch :test leo-b1-condition
                                        :body leo-b1-statements))

         ((mv erp remaining-branches last-else-statements)
          (j2f-if-statement-tail remaining-branches-and-last-else))
         ((when erp) (mv t *error-conditional-statement*)))

      (mv nil
          (leo-early::make-statement-if :branches (cons leo-first-branch remaining-branches)
                             :else last-else-statements)))
     :measure (two-nats-measure (json::member-count json-conditional-statement) 2))

  (define j2f-if-statement-tail ((json-conditional-next-value json::valuep))
    :returns (mv (erp booleanp)
                 (branches branch-listp)
                 (last-else-statements statement-listp))
    :short "Converts a JSON if statement's 'otherwise' object into a \
            leo::branch-list and a final else leo::statement-list."
    :parents (json2ast)
    (b* (((unless (json::valuep json-conditional-next-value))
          (mv t nil nil))

         ;; "next" value of :null means there are no more "else if" branches
         ;; and no final "else"
         ((when (eq :null (json::value-kind json-conditional-next-value)))
          (mv nil nil nil))

         ;; EM 2021-01 This changed from:
         ;;   "next" value of (:object (:member "End" _)) means there are no more
         ;;   "else if" branches on this conditional, but there is a final else.
         ;; to:
         ;;   "next" value of (:object (:member "Block" _)) means there are no more
         ;;   "else if" branches on this conditional, but htere is a final else
         ((json::pattern (:object (:member "Block" (:object (:member "statements" last-else-statements)))))
          ;; EM 2020-12-10 added this (:object (:member "statements" ..)) layer to match AST change
          json-conditional-next-value)
         ((when json::match?)
          (if (eq :ARRAY (json::value-kind last-else-statements))
              (mv-let (erp statement-list)
                  (j2f-statements
                   (json::value-array->elements last-else-statements))
                (if erp
                    (mv t nil nil)
                  (mv nil nil statement-list)))
            (mv t nil nil)))

         ;; EM 2022-07-30 observed "block" -> "then" and "next" -> "otherwise".
         ;; EM 2021-01 This changed from:
         ;;   "next" value of (:object (:member "Nested" _)) means there is
         ;;   at least one more "else if" branch.
         ;;   Under "Nested" we see an object with the same 3 members
         ;;   as you see at the top level of the if statement.
         ;; to:
         ;;   "next" value of (:object (:member "Conditional" _)) means there is
         ;;   at least one more else if" branch.
         ;;   Under "Conditional" we see an object with the same 3 members
         ;;   as you see at the top level of the if statement.
         ((json::pattern (:object (:member "Conditional"
                                           (:object (:member "condition" c)
                                                    ;; EM 2020-12-10: added "block layer to match AST change
                                                    (:member "then" (:object (:member "statements" s)))
                                                    (:member "otherwise" n)))))
          json-conditional-next-value)
         ((unless (and json::match?
                       (eq :object (json::value-kind c))
                       (eq :array (json::value-kind s))))
          (mv t nil nil))

         ;; convert the condition and statements, as in j2f-if-statement
         ((mv erp leo-condition) (j2f-expression c))
         ((when erp) (mv t nil nil))
         ((mv erp leo-statements) (j2f-statements (json::value-array->elements s)))
         ((when erp) (mv t nil nil))
         (leo-this-branch (leo-early::make-branch :test leo-condition
                                       :body leo-statements))

         ;; get n's remaining branches and then assemble the result
         ((mv erp remaining-branches last-else-stmts)
          (j2f-if-statement-tail n))
         ((when erp)
          (mv t nil nil)))
      (mv nil
          (cons leo-this-branch remaining-branches)
          last-else-stmts))
     :measure (two-nats-measure (json::value-count json-conditional-next-value) 1))

  ;; for the defines
  :verify-guards nil ; done below
  ///
  (verify-guards j2f-statement)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function Definitions


(define j2f-fundecl ((inner-fn-val json::valuep))
  :returns (mv (erp booleanp) (leo-functiondef fundeclp))
  (b* (;; input (assume required field; TODO: is it, or can it be omitted when fn is nullary?)
         ((unless (and (json::valuep inner-fn-val)
                       (eq :object (json::value-kind inner-fn-val))))
          (mv t *error-fundecl*))

         ;; For regular functiondefs, we have already checked the inner against
         ;; the outer function name.  But for functiondefs as circuit members,
         ;; we need to grab the inner name.  So just do it again for regular
         ;; functiondefs
         ((unless (json::object-has-member-p "identifier" inner-fn-val))
          (mv t *error-fundecl*))
         (fn-name-val (json::object-member-value "identifier" inner-fn-val))
         ;; This identifier is a json::value of kind :string
         ((unless (and (json::valuep fn-name-val)
                       (eq :string (json::value-kind fn-name-val))))
          (mv t *error-fundecl*))
         (fn-name-w-span (json::value-string->get fn-name-val))
         (fn-name (extract-identifier-name fn-name-w-span))
         ((unless (leo-early::identifier-string-p fn-name))
          (mv t *error-fundecl*))

         ;; EM 2021-03-16 now the annotations are here, instead of in a separate
         ;; top level test functions section.
;         ((mv erp leo-annotations)
;          (j2f-annotations (json::object-member-value? "annotations" inner-fn-val)))
;         ((when erp)
;          (mv t *error-functiondef*))

         (array-of-inputs (json::object-member-value "input" inner-fn-val))
         ((unless (and (json::valuep array-of-inputs)
                       (equal :array (json::value-kind array-of-inputs))))
          (mv t *error-fundecl*))
         (json-inputs (json::value-array->elements array-of-inputs))

         ((mv erp leo-fn-inputs) ;(if (selfinput-case leo-self :none)
                                     (j2f-funinputs json-inputs)
                                 ;    (j2f-funinputs (cdr json-inputs)))
                                     )
         ((when erp)  ;; ignore the error inputs for now, if any
          (mv t *error-fundecl*))

         ;; Return type.
         ;; The Leo formal AST return type is in (fundecl->output ..) of type leo-early::type-option.
         ;; The JSON return type is either:
         ;;   If the return type is not specified, the JSON-object-member looks like "output": null.
         ;;   In this case we make the leo fundecl with :output nil.
         ;;   If it is specified, it looks like "output": { "IntegerType": "U8" }
         ;;   In this case we make the leo fundecl with :output (j2f-type ..)
         (json-return-type (json::object-member-value "output" inner-fn-val))

         ((mv erp leo-return-maybe-type) (json::value-case json-return-type
                                           :null (mv nil nil)
                                           ;; both :string and :object are handled in j2f-type
                                           :string (j2f-type json-return-type)
                                           :object (j2f-type json-return-type)
                                           :otherwise (mv t nil)))
         ((when erp) (mv t *error-fundecl*)) ; more error info would be good

         ;; statements
         ;; EM 2020-12-08: now there is a new "block" layer.  We check its existence in
         ;; jsonast-looks-like-function-definition-p.
         (block-val (json::object-member-value "block" inner-fn-val))
         ((json::pattern (:object (:member "statements" array-of-statements)))
          block-val)
         ((unless (and json::match?
                       (equal :array (json::value-kind array-of-statements))))
          (mv t *error-fundecl*))
         (json-statements (json::value-array->elements array-of-statements))
         ((mv erp leo-statements) (j2f-statements json-statements))
         ((when erp)
          (mv t *error-fundecl*)))
    (mv nil
        (leo-early::make-fundecl :name (leo-early::make-identifier :name fn-name)
;                          :self leo-self
                          :inputs leo-fn-inputs
                          :output leo-return-maybe-type
                          :body leo-statements
;                          :annotations leo-annotations
                          ))))

;; A function is a kind of definition.
;; Input:
;; The functions object under the file is a json-object, each member of which
;;   defines a function that maps
;;   a big constructed name with span (currently, 2020-08-24)
;;   to a value which is a json-object that has member names
;;   "identifier", "input" "output" and "statements".
;;   This takes as input one of the outer members.
;; Output: returns a leo::definition of kind :function.
(define j2f-function-definition ((json-fn json::memberp)
                                 (outer-mangled-name stringp))
  :returns (mv (erp booleanp) (leo-function-definition definitionp))
  :short "Converts a single member of the functions of a file to a leo::definition."
  :parents (json2ast)
  (if (not (and (json::memberp json-fn)
                (jsonast-looks-like-function-definition-p json-fn outer-mangled-name)))
      (mv t *error-definition*)
    (b* (;; Currently, the function name in the json ast has the span
         ;; serialized into it.
         ;; For now, we will pick out the real function name.
         (fn-name-with-span outer-mangled-name)
         (fn-name (extract-identifier-name fn-name-with-span))
         ((unless (leo-early::identifier-string-p fn-name)) (mv t *error-definition*))

         ;; The inner-fn-val is the same structure as appears in a fundecl
         ;; under a circuit memberdef.  TODO: factor this code.
         (inner-fn-val (json::member->value json-fn))
         ((unless (equal :object (json::value-kind inner-fn-val)))
          (mv t *error-definition*))

         ((mv erp leo-functiondef) (j2f-fundecl inner-fn-val))
         ((when erp)
          (mv t *error-definition*)))
      (mv nil
          (leo-early::make-topdecl-function :get leo-functiondef))))
  :verify-guards nil
  ///
  (verify-guards j2f-function-definition
    :hints (("Goal" :in-theory (enable jsonast-looks-like-function-definition-p))))
  )

;; EM TODO: it looks like the following is no longer correct.  The @test
;; annotation no longer affects this part of the structure.
;;
;; functions that do not have the @test annotation have the outer-fn-name
;; as the json::member->name of the json::member.  Explicate that in the
;; 2nd argument to j2f-function-definition.
(define j2f-function-definition-not-test ((json-fn json::memberp))
  :returns (mv (erp booleanp) (leo-function-definition definitionp))
  (j2f-function-definition json-fn (json::member->name json-fn)))

;; A list of the previous.
(define j2f-function-definitions ((json-fns json::member-listp))
  :returns (mv (erp booleanp) (leo-function-definitions definition-listp))
  :short "Converts list of json-members, all of which are supposed to be functions, to a list of leo::definitions."
  :parents (json2ast)
  (if (endp json-fns)
      (mv nil nil)
    (b* ((first-json-fn (first json-fns))
         ((mv erp first-leo-fn) (j2f-function-definition-not-test first-json-fn))
         ((when erp) (mv erp (list first-leo-fn)))
         (rest-json-fns (rest json-fns))
         ((mv erp rest-leo-fns) (j2f-function-definitions rest-json-fns))
         ((when erp) (mv erp rest-leo-fns)))
      (mv nil (cons first-leo-fn rest-leo-fns)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Struct member definitions

(defconst *error-struct-component-declaration*
  (leo-early::make-compdecl :name (leo-early::make-identifier :name "ERROR_constructing_struct_component_declaration")
                 :type (leo-early::make-type-unsigned :size (leo-early::make-bitsize-8))))

;; EM 2020-12-11 Mutable flag is now gone.  Took out first argument.
(define j2f-struct-component-declaration ((json-component-decl json::valuep))
  :returns (mv (erp booleanp) (leo-struct-component-declaration compdeclp))
  (b* (((json::pattern (:object (:member "StructVariable" (:array (:string var-with-span)
                                                                   type-object))))
        json-component-decl)
       ((unless (and json::match?
                     (stringp var-with-span)
                     (json::valuep type-object)))
        (mv t *error-struct-component-declaration*))
       (var (extract-identifier-name var-with-span))
       ((unless (leo-early::identifier-string-p var))
        (mv t *error-struct-component-declaration*))
       ((mv erp leo-type) (j2f-type type-object))
       ((when erp)
        (mv t *error-struct-component-declaration*)))
    (mv nil
        (leo-early::make-compdecl :name (leo-early::make-identifier :name var)
                                    :type leo-type))))

;; As of 2022-07-30 the only direct members are component declarations.
(define j2f-struct-members ((json-component-declarations json::value-listp))
  :returns (mv (erp booleanp) (leo-component-declarations compdecl-listp))
  :short "Converts a list of json struct members to a leo::compdecl-list."
  :parents (json2ast)
  (b* (((when (endp json-component-declarations))
        (mv nil nil))
       (cdecl (first json-component-declarations))
       ((mv erp leo-cdecl) (j2f-struct-component-declaration cdecl))
       ((when erp) (mv t nil))
       ((mv erp rest-leo-cdecls) (j2f-struct-members (rest json-component-declarations)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons leo-cdecl rest-leo-cdecls))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simplified Struct declarations.
;; (testnet3 version)

(define j2f-struct-declaration ((json-struct json::memberp))
  :returns (mv (erp booleanp) (leo-top-struct-declaration topdeclp))
  :short "Converts a single member of the structs of a file to a leo::topdecl-struct."
  :parents (json2ast)
  (if (not (and (json::memberp json-struct)
                (jsonast-looks-like-struct-declaration-p json-struct)))
      (mv t *error-definition*)
    (b* ((struct-name-with-span (json::member->name json-struct))
         (struct-name (extract-identifier-name struct-name-with-span))
         ((unless (leo-early::identifier-string-p struct-name)) (mv t *error-definition*))
         (inner-struct-val (json::member->value json-struct))
         ((unless (equal :object (json::value-kind inner-struct-val)))
          (mv t *error-definition*))

         ;; members, which are now (2022-07-30) StructVariable objects
         (array-of-struct-members (json::object-member-value "members" inner-struct-val))
         ((unless (equal :array (json::value-kind array-of-struct-members)))
          (mv t *error-definition*))
         (json-struct-members (json::value-array->elements array-of-struct-members))
         ((mv erp leo-members) (j2f-struct-members json-struct-members))
         ((when erp)
          (mv t
              (leo-early::make-topdecl-struct
               :get (leo-early::make-structdecl :name (leo-early::make-identifier :name "ERROR_in_members")
                                     :components leo-members))))
         (leo-struct (leo-early::make-structdecl :name (leo-early::make-identifier :name struct-name)
                                       :components leo-members)))
      (mv nil (leo-early::make-topdecl-struct
               :get leo-struct))))

  :verify-guards nil
  ///
  (verify-guards j2f-struct-definition
    :hints (("Goal" :in-theory (enable jsonast-looks-like-struct-definition-p))))
  )

;; A list of the previous.
(define j2f-struct-declarations ((json-structs json::member-listp))
  :returns (mv (erp booleanp) (leo-top-struct-declarations topdecl-listp))
  :short "Converts list of members, all of which are supposed to be struct declarations,
          to a list of leo::topdecl."
  :parents (json2ast)
  (if (endp json-structs)
      (mv nil nil)
    (b* ((first-json-struct (first json-structs))
         ((mv erp first-leo-struct) (j2f-struct-declaration first-json-struct))
         ((when erp) (mv erp (list first-leo-struct)))
         (rest-json-structs (rest json-structs))
         ((mv erp rest-leo-structs) (j2f-struct-declarations rest-json-structs))
         ((when erp) (mv erp rest-leo-structs)))
      (mv nil (cons first-leo-struct rest-leo-structs)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; File

;; On input:
;; The functions object under the file is a json-object, each member of which
;;   defines a function that maps
;;   a big constructed name with span (currently, 2020-08-24)
;;   to a value which is a json-object that has member names
;;   "identifier", "input" "output" and "statements".
;; On output:
;;   A leo::function is a defprod with "identifier", etc.
;;   A leo::definition is a deftagsum, with :function kind having a field leo::get that gets the function.
;;   A leo::file is a defprod with the field leo::defs that is a definition-list.

;; It would be good if we always return a formal file along with an
;; informational object.  The informational object would be like ERP
;; except not just a single bit.  It would have information about what pieces
;; were not recognized and any error messages.  Hopefully in a form that
;; enables quick fixes.

;; Top-level call can be outside the mutual recursion since
;; a file is currently only at the top level.

(define j2f-file ((value json::valuep))
  :returns (mv (erp booleanp)  ; TODO: impove error reporting
               (ret-file file))
  (b* (((when (not (and (json::valuep value)
                        (jsonast-looks-like-file-p value))))
        (mv t *error-file*))
       ;; For now the formal AST doesn't know about name or expected_input, or imports.
       ;; This will all change, but let's use what we have for now.

       (fns-object (json::object-member-value "functions" value))
       ;; fns-object is currently a json-object mapping a function name to another json-object
       ;; that has all the information of the function.
       ;; Note that object-member-value can raise an exception... we probably
       ;; want a different version, and then we check the error condition.
       ((unless (and (json::valuep fns-object)
                     (equal :object (json::value-kind fns-object))))
        (mv t *error-file*))

       (structs-object (json::object-member-value "structs" value))
       ((unless (and (json::valuep structs-object)
                     (equal :object (json::value-kind structs-object))))
        (mv t *error-file*))
       ;; If there are no structs, we still get an object, but it has no members.

       ;; EM 2021-03-16 "tests" have been folded in to "functions" with annotations
;       (tests-object (json::object-member-value "tests" value))
;       ((unless (and (json::valuep tests-object)
;                     (equal :object (json::value-kind tests-object))))
;        (mv t *error-file*))
;       ;; If there are no tests, we still get an object, but it has no members.

       ;; Now fns-object should map names to the actual fn objects
       ;; Currently (2020-08-24) the name is duplicated in the fn object as
       ;; the value of "identifier".  We don't check that yet, since it
       ;; might change.  (If we did check this, it would be in j2f-function-definitions.)
       ((mv erp-fns fns) (j2f-function-definitions (json::value-object->members fns-object)))

       ;; structs
       ((mv erp-structs structs) (j2f-struct-declarations (json::value-object->members structs-object)))
       )

    (mv (or erp-fns
            erp-structs
            ;erp-consts
            ;erp-aliases
            ;erp-imports
            ) ;erp-tests
        ;; for now, we combine all the defs into a single list in this order:
        (leo-early::make-file :imports nil ; TODO: fix
                   :program (leo-early::make-programdecl :id (leo-early::programid
                                                   (leo-early::identifier "fix")
                                                   (leo-early::identifier "me"))
                                              :items
                                              (append ;imports
                                               ;global-consts
                                               ;type-aliases
                                               structs
                                               fns))))) ; test-structs test-fns
  :verify-guards nil
  ///
  (verify-guards j2f-file
    :hints (("Goal" :in-theory (enable jsonast-looks-like-file-p)))))
