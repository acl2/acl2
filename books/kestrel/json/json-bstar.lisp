; JSON Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "std/strings/suffixp" :dir :system)

(include-book "abstract-syntax")
(include-book "light-ast-check")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; b* binder that uses a pattern to match a JSON FTY structure
;; and to bind variables to parts of that structure.

;; Example:
;;   (b* ((json::pattern (:array "uno" _ tres (:string "quatro") *..)) x)
;;     ..
;; If x is a JSON array with at least 4 elements,
;; and if the first and fourth are JSON literal strings "uno" and "quatro",
;; then tres will be bound to the third element (it could be any json value),
;; and the remaining b* forms will be evaluated.
;; If the match fails, the b* returns NIL.

;; x can be any expression, but it will be duplicated in each match requirement
;; so it shouldn't be too big.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Background

;; For more information on JSON, see
;; http://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf

;; For a JSON parser in ACL2, see
;;   books/kestrel/json-parser/parse-json.lisp

;; For the JSON Fixtype definitions we are using here, see
;;   books/kestrel/json/abstract-syntax.lisp

#||
Here is a simplified ABNF for JSON without pattern matching:

value = "true" / "false" / "null" / string / number / array / object
array = "[" [ element *( "," element ) ] "]"
element = value
object = "{" [ member *( "," member ) ] "}"
member = name ":" value
name = string

string means a literal string that is delimited by double-quotes (").
We omit the details on whitespace, numbers, strings, and symbols.

Although the JSON Fixtype we are using is implemented as an s-expression,
it is organized in a similar way as above.  An analogous simplified ABNF
for our JSON pattern language would be:

value-pattern = "true" / "false" / "null" / string-pattern / number-pattern /
                array-pattern / object-pattern /
                literal-string / literal-number / patvar
array-pattern = "[" [ element-pattern *( "," element-pattern ) ] [ "*.." / literal-symbol.. ] "]"
element-pattern = value-pattern
object-pattern = "{" [ member-pattern *( "," member-pattern ) ] [ "*.." / literal-symbol.. ] "}"
member-pattern = name-pattern ":" value-pattern
name-pattern = literal-string / patvar
patvar = _ / literal-symbol

literal-symbol.. is a symbol whose symbol-name ends in "..".
literal-symbol is a symbol whose symbol-name does not end in "..".

The preceding grammar is a short way to show the structure of the patterns.
The next section describes the actual JSON pattern S-expression structure
and the details on the pattern variables.
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; JSON pattern S-expression syntax

;; JSON null, true, and false patterns are the same as our JSON AST
;; representation:
;;   (:NULL)
;;   (:TRUE)
;;   (:FALSE)
;; JSON string pattern can have a pattern variable:
;;   (:STRING string) or (:STRING patvar-single)
;; patvar-single is a symbol.
;;   * To avoid confusion,
;;     the special symbols T and NIL (whose home package is COMMON-LISP)
;;     and any symbol whose name is "" are disallowed as patvars.
;;     Additionally, it does not make sense to use symbols in the KEYWORD package.
;;     This list could be augmented later if other symbols are problematic.
;;   * If the symbol-name is "_" it means match but don't
;;     bind any value when pattern matching.
;;     See also *JPAT-ANY-VALUE*.
;;   * A symbol named "*.." is disallowed (reserved for patvar-multiple).
;;     See also *JPAT-ANY-TAIL*.
;;   * Any symbol ending in ".." is disallowed (used in patvar-multiple).
;;   * any other symbol means it names a variable that is bound to the
;;     matched JSON structure
;; (:ARRAY . array-elements)
;;   * array-elements is a list of zero or more array element patterns,
;;     and is the cdr of the array pattern.
;;     Note, this is a different shape from the JSON AST representation,
;;     where the array element list is the cadr of the array object.
;;   * array-elements is 0 or more elements, the last of which can be
;;     an optional patvar-multiple.
;;   * an array element is a value-pattern.
;; (:OBJECT . object-members)
;;   * object-members is a list of zero or more member patterns,
;;     the last of which can be an optional patvar-multiple
;;   * Note, this is a different shape from the JSON AST representation.
;;   * IMPORTANT NOTE: the member patterns are matched against the
;;     form in the same order.  Even though JSON objects are usually
;;     used as dictionaries with unordered keys, there does exist an order,
;;     and this binder does not attempt to find a matching permutation.
;; patvar-multiple is a symbol whose symbol-name ends in "..".  It can only
;;   occur at the end of array-elements or object-members.
;;   If the symbol name is "*..", it means match the tail but don't bind
;;   any value when pattern matching.  Any other symbol ending in ".."
;;   will be bound to the tail when pattern matching.
;;   See also *JPAT-ANY-TAIL*.
;; (:MEMBER name/patvar-single value-pattern/patvar-single)
;;   * Note, this is a different shape from the JSON AST representation.
;;   * name is a literal string.  It matches a literal string in the form
;;     (not a value of kind :STRING).
;;
;; A value pattern is any of the preceding except member or *..
;; or any symbol whose symbol name ends in "..".

;; Other notes: in the whole pattern, symbols named "_" or "*.." could
;; occur multiple times (in the correct contexts).
;; However, There must not be more than one occurrence of any other
;; pattern variable symbol in the whole pattern,
;; or it is an ill-formed pattern.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Possible enhancements:
;; * consider when patvar matches (:STRING literal-string), perhaps it should
;;   turn into (let ((patvar literal-string)) ..) rather than binding it
;;   to the JSON string, and similarly with numbers.
;;   However, that would complicate the type of patvar.
;; * allow patvar-single (including _) in place of a member
;; * allow *.. in more places


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define constants for the wildcard pattern variables.

;; Any symbol with this symbol-name is a pattern variable that
;; matches any json value but does not bind a variable to the match.
(defconst *jpat-any-value* "_")

;; Any symbol with this symbol-name is a pattern variable that
;; matches any tail of json array elements or json object members.
;; I.e., it can only occur at the very end of those lists.
;; It does not bind any variable to the match.
(defconst *jpat-any-tail* "*..")

;; Note:
;; *jpat-any-tail* is "*.." but it could be "..*" or "0..*"
;;   or various other things.  ".." does not work.

;; Any symbol ending in ".." will match a list of things.
;; Such a symbol may only be in a context that is legal for "*..",
;; i.e., object members or array elements.
(defconst *jpat-match-multiple-suffix* "..")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specific disallowed pattern variable names.

;; JSON::MATCH? is reserved for indicating whether the whole pattern matched
(defconst *jpat-disallowed-symbols* '(T NIL MATCH?))

(defconst *jpat-disallowed-symbol-names* '(""))

(defconst *jpat-disallowed-package-names* '("KEYWORD"))

;; This tells you if S might be a valid pattern var.
;; However, different vars are valid in different contexts,
;; and this predicate does not tell you that.
(define valid-jpat-varp ((s symbolp))
  (and (not (member-eq s *jpat-disallowed-symbols*))
       (not (member-equal (symbol-name s) *jpat-disallowed-symbol-names*))
       (not (member-equal (symbol-package-name s) *jpat-disallowed-package-names*))))

;; A list valued pattern variable must also end in "..".
(define list-valued-jpat-varp ((s symbolp))
  (and (valid-jpat-varp s)
       (str::strsuffixp *jpat-match-multiple-suffix* (symbol-name s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define json pattern predicates.

;; We collect the pattern variables (other than those with names "_" or "*..")
;; so that we can check for duplication at the top level.

;; For those predicates that do not need to return pattern variables,
;; we call them xxx-patternp.

;; For the "predicates" that also collect the pattern variables and return them
;; in another mv value, we call them xxx-patternp-with-vars.

;; Then each xxx-patternp-with-vars function gets a single-valued predicate
;; equivalent xxx-patternp.

;; Note, it would be good to define and use a json-patternp fixtype using
;; defflexsum.  Then guard verification of callers of these functions
;; would be easier.

;; First start with the leaf cases.

;; null, true, and false are expressed the same in json and json-pattern.

(define null-patternp (p)
  (jnullp p))
(define true-patternp (p)
  (jtruep p))
(define false-patternp (p)
  (jfalsep p))

(define string-patternp-with-vars (p)
  :returns (mv (true/false booleanp) (patvars symbol-listp))
  (b* (((unless (and (consp p)
                     (eq :string (car p))
                     (consp (cdr p))
                     (or (symbolp (cadr p))
                         (stringp (cadr p)))
                     (null (cddr p))))
        (mv nil nil))
       ((when (stringp (cadr p)))
        (mv t nil))
       ;; certain symbols not allowed as patvars
       ((when (and (symbolp (cadr p))
                   (not (valid-jpat-varp (cadr p)))))
        (mv nil nil))
       ;; *.. not allowed in this context
       ((when (and (symbolp (cadr p))
                   (equal (symbol-name (cadr p)) *jpat-any-tail*)))
        (mv nil nil))
       ;; *jpat-any-value* is a wildcard
       ((when (and (symbolp (cadr p))
                   (equal (symbol-name (cadr p)) *jpat-any-value*)))
        (mv t nil)))
    ;; Now we know it is a symbol and not "*.." or "_",
    ;; so it is a pattern variable.
    (mv t (list (cadr p)))))

(define number-patternp-with-vars (p)
  :returns (mv (true/false booleanp) (patvars symbol-listp))
  (b* (((unless (and (consp p)
                     (eq :number (car p))
                     (consp (cdr p))
                     (or (symbolp (cadr p))
                         (rationalp (cadr p)))
                     (null (cddr p))))
        (mv nil nil))
       ((when (rationalp (cadr p)))
        (mv t nil))
       ;; certain symbols not allowed as patvars
       ((when (and (symbolp (cadr p))
                   (not (valid-jpat-varp (cadr p)))))
        (mv nil nil))
       ;; *.. not allowed in this context
       ((when (and (symbolp (cadr p))
                   (equal (symbol-name (cadr p)) *jpat-any-tail*)))
        (mv nil nil))
       ;; *jpat-any-value* is a wildcard
       ((when (and (symbolp (cadr p))
                   (equal (symbol-name (cadr p)) *jpat-any-value*)))
        (mv t nil)))
    ;; Now we know it is a symbol and not "*.." or "_",
    ;; so it is a pattern variable.
    (mv t (list (cadr p)))))

(defines pattern-checkers
  :verify-guards nil ; done below

  (define value-patternp-with-vars (p)
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 1)
    (b* (;; This is an alias for (:STRING p)
         ((when (stringp p))
          (mv t nil))
	 ;; This is an alias for (:NUMBER p)
         ((when (rationalp p))
          (mv t nil))
         ;; certain symbols not allowed as patvars
         ((when (and (symbolp p)
                     (not (valid-jpat-varp p))))
          (mv nil nil))
         ;; *.. and SYMBOL.. not allowed in this context
         ((when (and (symbolp p)
                     (list-valued-jpat-varp p)))
          (mv nil nil))
         ;; *jpat-any-value* is a wildcard
         ((when (and (symbolp p)
                     (equal (symbol-name p) *jpat-any-value*)))
          (mv t nil))
         ;; any other symbol is a patvar
         ((when (symbolp p))
          (mv t (list p)))
         ;; That is it for atoms.
         ((when (atom p))
          (mv nil nil))
         ;; null, true, and false patterns cannot have patvars inside
         ((when (or (null-patternp p) (true-patternp p) (false-patternp p)))
          (mv t nil))
         ;; string, array, and object patterns are all lists that start with
         ;; their tag.  If the tag is known, but the recognizer fails,
         ;; then we should not check the other recognizers.
         ((mv string-pattern? vars) (string-patternp-with-vars p))
         ;; Exit when the tag is :STRING.
         ((when (eq (car p) :STRING))
          (mv string-pattern? (and string-pattern? vars)))

	 ((mv number-pattern? vars) (number-patternp-with-vars p))
         ;; Exit when the tag is :NUMBER
         ((when (eq (car p) :NUMBER))
          (mv number-pattern? (and number-pattern? vars)))

         ((mv array-pattern? vars) (array-patternp-with-vars p))
         ((when (eq (car p) :ARRAY))
          (mv array-pattern? (and array-pattern? vars)))

         ((mv object-pattern? vars) (object-patternp-with-vars p))
         ((when (eq :OBJECT (car p)))
          (mv object-pattern? (and object-pattern? vars))))
      ;; if it is none of those, return nil
      (mv nil nil)))

  (define array-patternp-with-vars (p)
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 0)
    (if (not (and (true-listp p)
                  (eq :ARRAY (car p))))
        (mv nil nil)
      (array-elements-patternp-with-vars (cdr p))))

  (define array-elements-patternp-with-vars ((p true-listp))
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 0)
    (b* (((when (null p))
          (mv t nil))
         ((when (atom p)) ; helps proofs, I think
          (mv nil nil))
         ;; *.. is allowed at the end of a value list
         ((when (and (null (cdr p))
                     (symbolp (car p))
                     (equal (symbol-name (car p)) *jpat-any-tail*)))
          (mv t nil))
         ;; SYMBOL.. is allowed at the end of a value list
         ;; Note, the entire symbol including the ".." is the variable name.
         ((when (and (null (cdr p))
                     (symbolp (car p))
                     (list-valued-jpat-varp (car p))))
          (mv t (list (car p))))
         ;; Now we can use value-patternp-with-vars for the car,
         ;; and join it with a recursive call on the cdr.
         ((mv car-is-pattern? car-vars)
          (value-patternp-with-vars (car p)))
         ((unless car-is-pattern?)
          (mv nil nil))
         ((mv cdr-is-pattern? cdr-vars)
          (array-elements-patternp-with-vars (cdr p)))
         ((unless cdr-is-pattern?)
          (mv nil nil)))
      (mv t (append car-vars cdr-vars))))

  (define object-patternp-with-vars (p)
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 0)
    (if (not (and (consp p)
                  (eq :OBJECT (car p))
                  (true-listp (cdr p))))
        (mv nil nil)
      (object-members-patternp-with-vars (cdr p))))

  (define object-members-patternp-with-vars ((p true-listp))
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 0)
    (b* (((when (null p))
          (mv t nil))
         ((when (atom p)) ; helps proofs, I think
          (mv nil nil))
         ;; *.. is allowed at the end of a member list
         ((when (and (null (cdr p))
                     (symbolp (car p))
                     (equal (symbol-name (car p)) *jpat-any-tail*)))
          (mv t nil))
         ;; SYMBOL.. is allowed at the end of a member list
         ;; Note, the entire symbol including the ".." is the variable name.
         ((when (and (null (cdr p))
                     (symbolp (car p))
                     (list-valued-jpat-varp (car p))))
          (mv t (list (car p))))
         ;; Now we can use member-patternp-with-vars for the car,
         ;; and join it with a recursive call on the cdr.
         ((mv car-is-pattern? car-vars)
          (member-patternp-with-vars (car p)))
         ((unless car-is-pattern?)
          (mv nil nil))
         ((mv cdr-is-pattern? cdr-vars)
          (object-members-patternp-with-vars (cdr p)))
         ((unless cdr-is-pattern?)
          (mv nil nil)))
      (mv t (append car-vars cdr-vars))))

  ;; At first, we don't allow pattern variables at the member level.
  ;; Consider: try allowing pattern vars at this level to see how it goes.
  (define member-patternp-with-vars (p)
    :returns (mv (true/false booleanp) (patvars symbol-listp))
    :measure (two-nats-measure (acl2-count p) 0)
    (b* (((unless (and (consp p)
                       (eq :MEMBER (car p))
                       (true-listp (cdr p))
                       (= 2 (len (cdr p)))))
          (mv nil nil))
         (name-component (second p))
         (value-component (third p))
         ;; The name component must be a literal string or a patvar
         ;; If the name is neither a string nor a symbol,
         ;; then p is not a valid member pattern.
         ((unless (or (stringp name-component)
                      (symbolp name-component)))
          (mv nil nil))
         ;; certain symbols not allowed as patvars
         ((when (and (symbolp name-component)
                     (not (valid-jpat-varp name-component))))
          (mv nil nil))
         ;; If the name is a patvar named *jpat-any-tail*, then p is
         ;; not a valid member pattern.
         ((when (and (symbolp name-component)
                     (equal *jpat-any-tail* (symbol-name name-component))))
          (mv nil nil))
         ;; remember name-patvars for later combination with any
         ;; patvars from the value component
         (name-patvars (if (and (symbolp name-component)
                                (not (equal *jpat-any-value* (symbol-name name-component))))
                           (list name-component)
                         '()))
         ((mv value-pattern? value-patvars)
          (value-patternp-with-vars value-component))
         ((unless value-pattern?)
          (mv nil nil)))
      (mv t (append name-patvars value-patvars))))

  ///
  (verify-guards value-patternp-with-vars))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predicates for top-level pattern checking

;; At top level, the structure can be any value-patternp-with-vars
;; (not a member-patternp-with-vars).
;; Further, it must not have any duplicate patvars.
;;
(define value-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (value-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

;; We define json-patternp as an alias for value-patternp,
;; since it is standard json to allow any value at the top level.
(define json-patternp (p)
  :returns (true/false booleanp)
  (value-patternp p))

(define array-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (array-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

(define array-elements-patternp ((p true-listp))
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (array-elements-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

(define object-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (object-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

(define object-members-patternp ((p true-listp))
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (object-members-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

(define member-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (member-patternp-with-vars p)
    (and pattern?
         (no-duplicatesp-eq patvars))))

;; Since there is a max of one var, we can discard it if we
;; are calling this at the top level.
(define string-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? vars)
      (string-patternp-with-vars p)
    (declare (ignore vars))
    pattern?))

(define number-patternp (p)
  :returns (true/false booleanp)
  (mv-let (pattern? vars)
      (number-patternp-with-vars p)
    (declare (ignore vars))
    pattern?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; non-top-level single-valued pattern predicates

;; These can be used as guards in places where you don't need to check
;; whether there are duplicate vars.

(define value-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (value-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

(define array-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (array-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

(define array-elements-patternp-dups-ok ((p true-listp))
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (array-elements-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

(define object-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (object-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

(define object-members-patternp-dups-ok ((p true-listp))
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (object-members-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

(define member-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (mv-let (pattern? patvars) (member-patternp-with-vars p)
    (declare (ignore patvars))
    pattern?))

;; Since string-patternp can't have dups, we are just defining an alias here.
(define string-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (string-patternp p))

;; Since number-patternp can't have dups, we are just defining an alias here.
(define number-patternp-dups-ok (p)
  :returns (true/false booleanp)
  (number-patternp p))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Collecting match requirements.

;; Collect conjuncts that must all be met in order for the JSON pattern to match.
;; Along the way, also collects pattern variables and expressions that can be used
;; to compute their values.
;; The b* macro will construct those into the b*-binding expansion.
;;
;; form is a variable or an expression that, when evaluated, picks out a part
;;    of a json structure that is to be matched against jpat
;;

;; Leaf functions

;; Handles the <something> in (:STRING <something>)
(define jpat-collect-match-requirements--string ((jpat-inner-string atom) form-to-string)
  :returns (mv (match-reqts true-listp) (var-bindings true-listp))
  ;; literal string pattern case
  (cond ((stringp jpat-inner-string)
         (mv (list `(equal ,jpat-inner-string ,form-to-string))
             nil))
        ((and (symbolp jpat-inner-string)
              (equal *jpat-any-value* (symbol-name jpat-inner-string)))
         (mv nil nil))
        ;; symbol with name *jpat-any-tail* should not appear here since value-patternp would not allow that
        ((symbolp jpat-inner-string)
         (mv nil (list (list jpat-inner-string form-to-string))))
        (t
         (mv (er hard? 'top-level "Unforseen case in jpat-collect-match-requirements--string") nil))))

;; Handles the <something> in (:NUMBER <something>)
(define jpat-collect-match-requirements--number ((jpat-inner-number atom) form-to-number)
  :returns (mv (match-reqts true-listp) (var-bindings true-listp))
  ;; literal integer / rational number pattern case
  (cond ((rationalp jpat-inner-number)
         (mv (list `(equal ,jpat-inner-number ,form-to-number))
             nil))
        ((and (symbolp jpat-inner-number)
              (equal *jpat-any-value* (symbol-name jpat-inner-number)))
         (mv nil nil))
        ;; symbol with name *jpat-any-tail* should not appear here since value-patternp would not allow that
        ((symbolp jpat-inner-number)
         (mv nil (list (list jpat-inner-number form-to-number))))
        (t
         (mv (er hard? 'top-level "Unforseen case in jpat-collect-match-requirements--number") nil))))

(define jpat-collect-match-requirements--member-name ((jpat atom) form)
  :returns (mv (match-reqts true-listp) (var-bindings true-listp))
  (cond ((stringp jpat)
         (mv (list `(equal ,jpat ,form))
             nil))
        ((and (symbolp jpat)
              (equal *jpat-any-value* (symbol-name jpat)))
         (mv nil nil))
        ((symbolp jpat)
         (mv nil
             (list (list jpat form))))
        (t ;; just in case
         (mv (er hard? 'top-level "problem in jpat-collect-match-requirements--member-name") nil))))

(defines jpat-collect-match-requirements--recur
  :verify-guards nil ; done below

  (define jpat-collect-match-requirements--value ((jpat value-patternp-dups-ok) form)
    :returns (mv (match-reqts true-listp) (var-bindings true-listp))
    :measure (two-nats-measure (acl2-count jpat) 1)
    (cond
     ;; Since jpat has already been validated as a json-patternp,
     ;; if jpat is a symbol,
     ;; we can be sure valid-jpat-varp is already true, so we don't check it.
     ;;
     ;; _ can match any value and no patvars are bound
     ((and (symbolp jpat) (equal *jpat-any-value* (symbol-name jpat)))
      (mv nil nil))
     ;; We will have have already validated that jpat is a json-patternp *.. is not allowed at a json-value location
     ;; So a symbol named *jpat-any-tail* can not occur here.
     ((symbolp jpat)
      (mv nil (list (list jpat form))))
     ;; a literal string in the pattern (in a json-value location)
     ;; is shorthand for a json-string pattern with a literal string
     ((stringp jpat)
      (mv (list `(jstringp ,form)
                `(equal ,jpat (value-string->get ,form)))
          nil))
     ;; a literal integer in the pattern (in a json-value location)
     ;; is shorthand for a json-number pattern with a literal integer
     ((integerp jpat)
      (mv (list `(jnumberp ,form)
                `(equal ,jpat (value-number->get ,form)))
          nil))
     ;; There should not be any other atoms here; help the prover out
     ;; by saying so.
     ((atom jpat)
      (mv (er hard? 'top-level "jpat-collect-match-requirements--value: unexpected atom ~x0 as pattern~%" jpat) nil))
     ((and (consp jpat)
           (eq :number (car jpat)))
      (let ((new-match-requirement `(jnumberp ,form))) ; checks value-kind and that the get is rationalp
        (mv-let (inner-match-requirements inner-var-bind-forms)
            (jpat-collect-match-requirements--number (cadr jpat) `(value-number->get ,form))
          (mv (cons new-match-requirement inner-match-requirements)
              inner-var-bind-forms))))
     ;; string pattern
     ((and (consp jpat)
           (eq :string (car jpat)))
      (let ((new-match-requirement `(jstringp ,form))) ; checks value-kind and that the get is stringp
        (mv-let (inner-match-requirements inner-var-bind-forms)
            (jpat-collect-match-requirements--string (cadr jpat) `(value-string->get ,form))
          (mv (cons new-match-requirement inner-match-requirements)
              inner-var-bind-forms))))
     ;; null pattern
     ((jnullp jpat)
      (mv (list `(jnullp ,form))
          nil))
     ;; true pattern
     ((jtruep jpat)
      (mv (list `(jtruep ,form))
          nil))
     ;; false pattern
     ((jfalsep jpat)
      (mv (list `(jfalsep ,form))
          nil))
     ;; number pattern
     ((jnumberp jpat)
      (mv (er hard? 'top-level "number patterns not yet handled") nil))
     ;; array pattern
     ((and (consp jpat)
           (eq :array (car jpat)))
      (let ((new-match-requirement `(top-jarrayp ,form))) ;`(eq :ARRAY (car ,form))
        (mv-let (inner-match-requirements inner-var-bind-forms)
            (jpat-collect-match-requirements--array-elements (cdr jpat) `(value-array->elements ,form))
          (mv (cons new-match-requirement inner-match-requirements)
              inner-var-bind-forms))))
     ;; object pattern
     ((and (consp jpat)
           (eq :object (car jpat)))
      (let ((new-match-requirement `(top-jobjectp ,form))) ;`(eq :OBJECT (car ,form))
        (mv-let (inner-match-requirements inner-var-bind-forms)
            (jpat-collect-match-requirements--object-members (cdr jpat) `(value-object->members ,form))
          (mv (cons new-match-requirement inner-match-requirements)
              inner-var-bind-forms))))
     (t (mv (er hard? 'top-level "Unforseen case in jpat-collect-match-requirements--value") nil))))

  (define jpat-collect-match-requirements--array-elements
            ((rest-of-jpat (and (true-listp rest-of-jpat)
                                (array-elements-patternp-dups-ok rest-of-jpat)))
             form)
    :returns (mv (match-reqts true-listp) (var-bindings true-listp))
    :measure (two-nats-measure (acl2-count rest-of-jpat) 0)
    (cond
     ;; extra guard check
     ((not (array-elements-patternp-dups-ok rest-of-jpat))
      (mv nil nil))

     ;; if no more elements in jpat, then collect a requirement that form be null
     ((null rest-of-jpat) ; @@@ I did have atom, but that didn't work, so i give
      ;; rest-of-jpat will be null, but make it obvious that if this is false then rest-of-jpat is a cons
      (mv (list `(null ,form))
          nil))

     ;; extra error check
     ((atom rest-of-jpat)
      (mv (er hard? 'top-level "unexpected condition") nil))

     ;; *..
     ((and (consp rest-of-jpat)
           (symbolp (car rest-of-jpat))
           (equal *jpat-any-tail* (symbol-name (car rest-of-jpat))))
      (mv nil nil))

     ;; SYMBOL.. (meaning a symbol whose symbol name ends in "..")
     ((and (consp rest-of-jpat)
           (symbolp (car rest-of-jpat))
           (list-valued-jpat-varp (car rest-of-jpat)))
      (mv nil
          (list (list (car rest-of-jpat) form))))

     ;; now any other pattern cons is a value pattern and requires that form be a cons;
     ;; we combine the results of recurring on the car and the cdr
     (t (b* (((mv car-match-requirements car-var-bind-forms)
              (jpat-collect-match-requirements--value (car rest-of-jpat) `(car ,form)))
             ((mv cdr-match-requirements cdr-var-bind-forms)
              (jpat-collect-match-requirements--array-elements (cdr rest-of-jpat) `(cdr ,form))))
          (mv (cons `(consp ,form)
                    (append car-match-requirements cdr-match-requirements))
              (append car-var-bind-forms cdr-var-bind-forms))))))

  (define jpat-collect-match-requirements--object-members
            ((rest-of-jpat (and (true-listp rest-of-jpat)
                                (object-members-patternp-dups-ok rest-of-jpat)))
             form)
    :measure (two-nats-measure (acl2-count rest-of-jpat) 0)
    :returns (mv (match-reqts true-listp) (var-bindings true-listp))
    (cond
     ;; extra guard check
     ((not (object-members-patternp-dups-ok rest-of-jpat))
      (mv nil nil))

     ;; if no more members in jpat, then collect a requirement that form be null
     ((null rest-of-jpat) ;@@@ see comment above
      ;; rest-of-jpat will be null, but make it obvious that if this is false then rest-of-jpat is a cons
      (mv (list `(null ,form))
          nil))

     ;; extra error check
     ((atom rest-of-jpat)
      (mv (er hard? 'top-level "unexpected condition") nil))

     ;; *..
     ((and (consp rest-of-jpat)
           (symbolp (car rest-of-jpat))
           (equal *jpat-any-tail* (symbol-name (car rest-of-jpat))))
      (mv nil nil))

     ;; SYMBOL.. (meaning a symbol whose symbol name ends in "..")
     ((and (consp rest-of-jpat)
           (symbolp (car rest-of-jpat))
           (list-valued-jpat-varp (car rest-of-jpat)))
      (mv nil
          (list (list (car rest-of-jpat) form))))

     ;; (car jpat) will be a member pattern but let's have an extra check
     ((not (member-patternp-dups-ok (car rest-of-jpat)))
      (mv (er hard? 'top-level "problem in jpat-collect-match-requirements--object-members") nil))

     ;; now any other pattern cons is a member pattern and requires that form be a cons;
     ;; we combine the results of recurring on the car and the cdr
     (t (b* (((mv car-match-requirements car-var-bind-forms)
              (jpat-collect-match-requirements--member (car rest-of-jpat) `(car ,form)))
             ((mv cdr-match-requirements cdr-var-bind-forms)
              (jpat-collect-match-requirements--object-members (cdr rest-of-jpat) `(cdr ,form))))
          (mv (cons `(consp ,form)
                    (append car-match-requirements cdr-match-requirements))
              (append car-var-bind-forms cdr-var-bind-forms))))))

  (define jpat-collect-match-requirements--member ((jpat member-patternp-dups-ok) form)
    :returns (mv (match-reqts true-listp) (var-bindings true-listp))
    :measure (two-nats-measure (acl2-count jpat) 0)
     ;; (cond
     ;; right now, we don't allow patvars at the member level
     ;; ;; _ can match any value and no patvars are bound
     ;; ((and (symbolp jpat) (equal *jpat-any-value* (symbol-name jpat)))
     ;;  (mv nil nil))
     ;; ;; We will have have already validated that jpat is a json-patternp *.. is not allowed at a json-member location
     ;; ;; So a symbol named *jpat-any-tail* can not occur here.
     ;; ((symbolp jpat)
     ;;  (mv nil (list (list jpat form))))
     ;;  ... )

;    (if (mbe :logic (member-patternp jpat) :exec t)
    (if (and (member-patternp-dups-ok jpat) (true-listp jpat) (= 3 (len jpat)))
        (b* ((reqt `(memberp ,form)) ; memberp reqt probably not needed because we are in a list of object members, but it doesn't hurt much
             ((mv name-match-requirements name-var-bind-forms)
              (jpat-collect-match-requirements--member-name (second jpat) `(member->name ,form)))
             ((mv value-match-requirements value-var-bind-forms)
              (jpat-collect-match-requirements--value (third jpat) `(member->value ,form))))
          (mv (cons reqt (append name-match-requirements value-match-requirements))
              (append name-var-bind-forms value-var-bind-forms)))
      (mv (er hard? 'top-level "unusual situation") nil)))

  ///
  ;; Note: this verify-guards would be made simpler if we had a fixtype for JSON patterns.
  ;; As it is now, verifying guards needs to enable up most of these functions.
  ;; See the section above titled "Define json pattern predicates."
  (verify-guards jpat-collect-match-requirements--value
    :hints (("Goal" :do-not-induct t :expand (VALUE-PATTERNP-DUPS-OK jpat)
	     :in-theory  (enable VALUE-PATTERNP-DUPS-OK
				 ARRAY-ELEMENTS-PATTERNP-DUPS-OK
				 OBJECT-MEMBERS-PATTERNP-DUPS-OK
				 MEMBER-PATTERNP-DUPS-OK

				 VALUE-PATTERNP-WITH-VARS
				 STRING-PATTERNP-WITH-VARS
				 NUMBER-PATTERNP-WITH-VARS
				 ARRAY-PATTERNP-WITH-VARS
				 ARRAY-ELEMENTS-PATTERNP-WITH-VARS
				 OBJECT-PATTERNP-WITH-VARS
				 OBJECT-MEMBERS-PATTERNP-WITH-VARS
				 MEMBER-PATTERNP-WITH-VARS

				 JNUMBERP
				 TRUE-PATTERNP JTRUEP
				 NULL-PATTERNP JNULLP
				 FALSE-PATTERNP JFALSEP))))
  )


;; If there was no global match then the pattern variables are
;; bound to :nomatch!
;; This is done as a postprocessing step, but we could
;; do this at gathering time in an api function that
;; adds a form to a list of var-bind-forms, and then
;; make all the gatherers go through that api function.
(define add-match-check-to-var-bind-forms ((pairs acl2::doublet-listp))
  :returns (retpairs acl2::doublet-listp)
  (if (atom pairs) nil
    (let ((patvar (first (first pairs)))
	  (form (second (first pairs))))
      (cons (list patvar
		  `(if match? ,form :nomatch!))
	    (add-match-check-to-var-bind-forms (rest pairs))))))


;; Top-level function gathering top-level match requirements
;; and patvar-binding forms.
(define jpat-collect-match-requirements (jpat form)
  :returns (mv (match-reqts true-listp) (var-bindings true-listp))
  :verify-guards nil
  (if (json-patternp jpat)
      (mv-let (match-requirements var-bind-forms)
          (jpat-collect-match-requirements--value jpat form)
        (mv (cons `(valuep ,form)
                  match-requirements)
	    (add-match-check-to-var-bind-forms var-bind-forms)))
    (mv (er hard? 'top-level "jpat must be json-patternp") nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The b* binder

(def-b*-binder pattern
  :parents (json acl2::b*-binders)
  :short "b* binder for JSON pattern matching."
  :long
  (xdoc::topstring
   (xdoc::p
    "Binds @('json::match?') based on whether a JSON FTY structure matches a
     pattern.  If matched, the pattern variables in the pattern are bound
     to the corresponding JSON substructures.  If not matched, the pattern
     variables are bound to the symbol @(':nomatch!')"))
  :body
  (if (or (not (= (len acl2::args) 1)) (not (= (len acl2::forms) 1)))
      (er hard? 'top-level "bad json::pattern b* binder")
    (mv-let (match-reqts var-bindings)
	(jpat-collect-match-requirements (first acl2::args) (first acl2::forms))
      `(let ((match? (and ,@match-reqts)))
	 (declare (ignorable match?))
	 ;; The var-bindings expressions check match? and if it is false,
	 ;; each pattern var will be bound to :nomatch!
	 (let ,var-bindings
	   (declare (ignorable ,@(strip-cars var-bindings)))
	   ,acl2::rest-expr)))))
