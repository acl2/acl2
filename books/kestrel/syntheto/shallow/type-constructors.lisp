; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shallow Type Specs
;; i.e., type constructors.

;; * Forms that describe types, for use in the shallow embedding.
;;   Not named type definitions, but types for things like function parameters.

;; * Recognizers of valid type constructor trees.

;; * code to convert a shallow type spec into a single name
;;   that is then used as the ACL2 Fixtype (FTY) name.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "../syndef-package-utilities")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unnamed composite types vs named composite types

;; Discussion
;; Unnamed types are those formed with
;;   (s-type-set ..)
;;   (s-type-sequence ..),
;;   (s-type-map .., ..)
;;   (s-type-option ..).
;; and with named types as leaves.
;; For any such type seen, we create a symbol to name it and we generate
;; an fty::def.. form.
;; (But not in this file... see "types.lisp"(

;; (s-type-ref ") ; a reference to a named type

;; See also the discussion about symbols in package.lsp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Predefined base types

;; See xdoc basetypes for the full list of possible predefined base types.
;; Currently we support 4 of them.

(defmacro s-type-boolean () 'BOOL)
(defmacro s-type-integer () 'INT)
(defmacro s-type-character () 'CHARACTER)
(defmacro s-type-string () 'STRING)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reference to a Named type.

(defmacro s-type-ref (type-string)
  (intern-syndef type-string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unnamed Composite types

;; The type constructors we currently support are
;; set, sequence, map, and option.


#||
ABNF for type forms

type-form = leaf-type-form / tree-type-form

leaf-type-construct = type-ref-construct / nullary-type-construct
type-ref-construct = "(s-type-ref " literal-string ")"
nullary-type-construct = "(s-type-boolean)" / "(s-type-integer)" / "(s-type-character)" / "(s-type-string)"

tree-type-form = unary-type-construct / binary-type-construct
unary-type-construct = set-type-construct / sequence-type-construct / option-type-construct
set-type-construct = "(s-type-set " type-form ")"
sequence-type-construct = "(s-type-sequence " type-form ")"
option-type-construct = "(s-type-option " type-form ")"
binary-type-construct = map-type-construct
map-type-construct = "(s-type-map " domain-type-form "," range-type-form ")"
domain-type-form = type-form
range-type-form = type-form

||#

;; Note, there are examples below.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type constructor names and recogizers

(defconst *nullary-type-constructors*
  '(s-type-boolean s-type-integer s-type-character s-type-string))

;; a type form will look like (s-type-boolean), (s-type-integer), ..
(defun nullary-type-constructor-p (type-form)
  (declare (xargs :guard t))
  (and (consp type-form)
       (null (cdr type-form))
       (member-eq (car type-form) *nullary-type-constructors*)
       T)) ; return a boolean rather than a member suffix list

;; We don't bother with a separate constant for s-type-ref.

(defun type-ref-constructor-p (type-form)
  (declare (xargs :guard t))
  (and (true-listp type-form)
       (= 2 (len type-form))
       (eq (first type-form) 's-type-ref)
       (stringp (second type-form))))

(defthm stringp-of-second-type-ref-constructor-p
  (implies (type-ref-constructor-p type-form)
           (stringp (second type-form))))

(defthm type-ref-constructor-p-implies-consp
  (implies (type-ref-constructor-p type-form)
           (consp type-form)))

(defthm consp-cdr-if-type-ref-constructor-p
  (implies (type-ref-constructor-p type-form)
           (consp (cdr type-form))))

;; s-type-ref is also a unary type constructor, but its argument
;; must be a literal string, so it doesn't participate in the mutual
;; recursion.  As a leaf-type construct we omit it from *unary-type-constructors*
(defconst *unary-type-constructors*
  '(s-type-set s-type-sequence s-type-option))

(defun unary-type-constructor-p (type-form)
  (declare (xargs :guard t))
  (and (true-listp type-form)
       (= 2 (len type-form))
       (member-eq (car type-form) *unary-type-constructors*)
       T))

(defthm acl2-count-when-unary-type-constructor-p
  (implies (unary-type-constructor-p type-form)
           (< (acl2-count (cadr type-form))
              (acl2-count type-form))))

(defthm unary-type-constructor-p-implies-consp
  (implies (unary-type-constructor-p type-form)
           (consp type-form)))

(defthm unary-type-constructor-p-implies-consp-cdr
  (implies (unary-type-constructor-p type-form)
           (consp (cdr type-form))))

(defconst *binary-type-constructors*
  '(s-type-map))

(defun binary-type-constructor-p (type-form)
  (declare (xargs :guard t))
  (and (true-listp type-form)
       (= 3 (len type-form))
       (member-eq (car type-form) *binary-type-constructors*)))



(defthm acl2-count-cadr-when-binary-type-constructor-p
  (implies (binary-type-constructor-p type-form)
           (< (acl2-count (cadr type-form))
              (acl2-count type-form))))

(defthm acl2-count-caddr-when-binary-type-constructor-p
  (implies (binary-type-constructor-p type-form)
           (< (acl2-count (caddr type-form))
              (acl2-count type-form))))

(defthm binary-type-constructor-p-implies-consp-cdr
  (implies (binary-type-constructor-p type-form)
           (consp (cdr type-form))))

(defthm binary-type-constructor-p-implies-consp-cddr
  (implies (binary-type-constructor-p type-form)
           (consp (cddr type-form))))

;; Checks that the given s-expression might be a valid type constructor.


;; Only checks the top level of the given s-expression.
;; If there is junk below that, we will detect that later.
(defun toplevel-type-constructor-p (s-exp)
  (declare (xargs :guard t))
  (or (binary-type-constructor-p s-exp)
      (unary-type-constructor-p s-exp)))

(defun type-constructor-p (s-exp)
  (declare (xargs :guard t))
  (or (type-ref-constructor-p s-exp)
      (nullary-type-constructor-p s-exp)
      (unary-type-constructor-p s-exp)
      (binary-type-constructor-p s-exp)))

#||
;; Examples:

(s-type-set (s-type-boolean)) ; not very useful
(s-type-map (s-type-boolean) (s-type-string)) ; two sets in one map
(s-type-sequence (s-type-character)) ; can APT turn this into a string?
(s-type-option (s-type-boolean)) ; for those opposed to the law of the excluded middle

(s-type-option (s-type-set (s-type-sequence (s-type-integer))))
(s-type-set (s-type-option (s-type-integer)))

;; Note, this depends on the existence of named types TT1, TT2, TT3, and TT4
(s-type-map (s-type-map (s-type-set (s-type-ref "TT1"))
                        (s-type-map (s-type-option (s-type-ref "TT2"))
                                    (s-type-ref "TT3")))
            (s-type-sequence (s-type-ref "TT4")))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; recognizers of valid type constructor trees

(defun valid-leaf-type-form-p (type-form)
  (declare (xargs :guard t))
  (or (nullary-type-constructor-p type-form)
      (type-ref-constructor-p type-form)))

(mutual-recursion

 (defun valid-unary-type-constructor-p (type-form)
   (declare (xargs :measure (two-nats-measure (acl2-count type-form) 0)))
   (and (unary-type-constructor-p type-form)
        (valid-type-constructor-p (second type-form))))

 (defun valid-binary-type-constructor-p (type-form)
   (declare (xargs :measure (two-nats-measure (acl2-count type-form) 0)))
   (and (binary-type-constructor-p type-form)
        (valid-type-constructor-p (second type-form))
        (valid-type-constructor-p (third type-form))))

 (defun valid-type-constructor-p (type-form)
   (declare (xargs :measure (two-nats-measure (acl2-count type-form) 1)))
   (or (valid-leaf-type-form-p type-form)
       (valid-unary-type-constructor-p type-form)
       (valid-binary-type-constructor-p type-form)))
 )
(verify-guards valid-unary-type-constructor-p)

;; Checks if type-form is a well-formed full type form.
;; "full" type form means it is a constructor satisfying
;; toplevel-type-constructor-p but also that the underneath
;; structure is valid.
(defun valid-full-type-form-p (type-form)
  (declare (xargs :guard t))
  (and (toplevel-type-constructor-p type-form)
       (or (valid-unary-type-constructor-p type-form)
           (valid-binary-type-constructor-p type-form))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert shallow type spec to name of fty defining form

;; We are generating names of top level definitions for unnamed types
;; that are used to declare parameters and local variables.
;; Smaller, inside types are defined first.
;; For example, if you have
;;
;;   let x: set(sequence(integer)) ...
;;
;; we define
;;
;;   (fty::deflist SYNDEF::SEQUENCE[INT] :ELT-TYPE INT ..)
;;   (fty::defset SYNDEF::SET[SEQUENCE[INT]] :ELT-TYPE SYNDEF::SEQUENCE[INT] ..)
;;
;; prior to the definition containing the let.
;;
;; S-TYPE-TO-FTY-NAME (see below) generates these names.


;; For use within composite strings only.
(defund nullary-type-constructor-to-type-string (type-form)
  (declare (xargs :guard (nullary-type-constructor-p type-form)))
  (cond ((equal type-form '(s-type-boolean))
         "BOOL")
        ((equal type-form '(s-type-integer))
         "INT")
        ((equal type-form '(s-type-character))
         "CHARACTER")
        ((equal type-form '(s-type-string))
         "STRING")
        (t (er hard? 'top-level "bad field type"))))

(defthm stringp-of-nullary-type-constructor-to-type-string
  (implies (nullary-type-constructor-p type-form)
           (stringp (nullary-type-constructor-to-type-string type-form)))
  :hints (("Goal" :in-theory (enable nullary-type-constructor-to-type-string))))


;; Currently, the base type names are not in the SYNDEF package,
;; but they are accessible from the ACL2 package.
(defun nullary-type-constructor-to-type-symbol (type-form)
  (declare (xargs :guard (nullary-type-constructor-p type-form)))
  (intern (nullary-type-constructor-to-type-string type-form) "ACL2"))

(defun unary-type-constructor-name-to-type-string (type-form)
  (declare (xargs :guard (unary-type-constructor-p type-form)))
  (cond ((equal (car type-form) 's-type-set) "SET")
        ((equal (car type-form) 's-type-sequence) "SEQUENCE")
        ((equal (car type-form) 's-type-option) "OPTION")
        (t (er hard? 'top-level "unknown unary type constructor name"))))

(defthm stringp-of-unary-type-constructor-to-type-string
  (implies (unary-type-constructor-p type-form)
           (stringp (unary-type-constructor-name-to-type-string type-form))))

(defun binary-type-constructor-name-to-type-string (type-form)
  (declare (xargs :guard (binary-type-constructor-p type-form)))
  (cond ((equal (car type-form) 's-type-map) "MAP")
        (t (er hard? 'top-level "unknown binary type constructor name"))))

(defthm stringp-of-binary-type-constructor-to-type-string
  (implies (binary-type-constructor-p type-form)
           (stringp (binary-type-constructor-name-to-type-string type-form))))

(in-theory (disable nullary-type-constructor-p type-ref-constructor-p unary-type-constructor-p binary-type-constructor-p
                    unary-type-constructor-name-to-type-string))

;; Do not use this on top-level nullary (base) type forms
(defun s-type-to-fty-name-string (type-form)
  (declare (xargs :verify-guards nil))
  (cond ((nullary-type-constructor-p type-form)
         (nullary-type-constructor-to-type-string type-form))
        ((type-ref-constructor-p type-form)
         (second type-form)) ; just the string
        ((unary-type-constructor-p type-form)
         (concatenate 'string
                      (unary-type-constructor-name-to-type-string type-form)
                      "["
                      (s-type-to-fty-name-string (second type-form))
                      "]"))
        ((binary-type-constructor-p type-form)
         (concatenate 'string
                      (binary-type-constructor-name-to-type-string type-form)
                      "["
                      (s-type-to-fty-name-string (second type-form))
                      "->"
                      (s-type-to-fty-name-string (third type-form))
                      "]"))
        (t (prog2$ (er hard? 'top-level "invalid shallow embedding type descriptor")
                   ""))))

(defthm stringp-of-s-type-to-fty-name-string
  (stringp (s-type-to-fty-name-string type-form)))

(verify-guards s-type-to-fty-name-string
  :hints (("Goal" :in-theory (enable binary-type-constructor-p))))

;; At the top level, the base type symbols are in the ACL2 package
(defun s-type-to-fty-name-symbol (type-form)
  (declare (xargs :guard (valid-type-constructor-p type-form)))
  (if (nullary-type-constructor-p type-form)
      (intern (nullary-type-constructor-to-type-string type-form) "ACL2")
    (intern-syndef (s-type-to-fty-name-string type-form))))

(defthm symbolp-of-s-type-to-fty-name-symbol
  (implies (valid-type-constructor-p type-form)
           (symbolp (s-type-to-fty-name-symbol type-form))))

