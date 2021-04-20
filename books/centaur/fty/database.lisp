; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")
(include-book "std/util/da-base" :dir :system)
(include-book "xdoc/str" :dir :system)
(program)

; Type Database Structures ----------------------------------------------------

; The primitive aggregates here contain the meta-data about each kind of
; structure that has been introduced by FTY.  Our type-introducing macros
; generally work by parsing the user-level forms (defprod, deftypes,
; defflexsum, ...) into these internal meta-data structures.  We then process
; the structures to create the main ACL2 events, documentation, etc.  We also
; save the metadata into an ACL2 table, which allows us to easily look up the
; definitions of, e.g., the types of individual fields, etc.

(def-primitive-aggregate flexprod-field
  ;; A single field within a Product type.
  ;; Typically only exist in the fields of a flexprod.
  (name               ;; field name, e.g., fullname
   acc-body           ;; accessor body, without fixing, e.g., (cdadar x)
   acc-name           ;; accessor function name, e.g., student->fullname
;; [Jared] BOZO rename type to pred
   type               ;; element type, e.g., stringp, or nil for an untyped field
   fix                ;; element fix, e.g., string-fix, or nil for an untyped field
   equiv              ;; element equiv, e.g., string-equiv, or nil for an untyped field
   reqfix             ;; dependent type fix (term)
   default            ;; default value
   doc                ;; short xdoc string about this field
   rule-classes       ;; for the return-type theorem: empty or (:rule-classes ...)
   recp               ;; is .type part of the mutual recursion?
   )
  :tag :field)

(def-primitive-aggregate flexprod
  ;; A single Product type.
  ;; Typically only exist in the prods of a flexsum.
  ;; (a top-level defprods becomes a single-member sum)
  (kind               ;; kind symbol, e.g., :foo
   cond               ;; term to check whether x is of this kind, after checking previous ones
   guard              ;; additional guard for accessors
   shape              ;; other requirements, given kindcheck
   require            ;; dependent type requirement (term)
   fields             ;; list of flexprod-fields, members of this product
   type-name          ;; base for constructing default accessor names, e.g., foo
   ctor-name          ;; constructor function name, e.g., foo
   ctor-macro         ;; constructor macro (keyword args) name, e.g., make-foo
   ctor-body          ;; constructor body, without fixing, e.g., (list ...)
   remake-name        ;; remake function name, e.g., remake-foo, or NIL if there is no remaker
   remake-body        ;; remake body, without fixing, or NIL if inapplicable
   short              ;; xdoc short string for the whole product
   long               ;; xdoc long string for the whole product
   inline             ;; inline keywords
   extra-binder-names ;; extra x.foo b* binders for not-yet-implemented accessors
   count-incr         ;; boolean -- add an extra 1 to count?
   no-ctor-macros     ;; boolean -- omit maker and changer macros?
   )
  :tag :prod)

(def-primitive-aggregate flexsum
  ;; A single Sum of Products type.
  (name               ;; name of this type, e.g., mysum
   pred               ;; predicate function name, e.g., mysum-p
   fix                ;; fix function name, e.g., mysum-fix
   equiv              ;; equiv function name, e.g., mysum-equiv
   kind               ;; kind function name, e.g., mysum-kind
   kind-body          ;; :exec part of kind function, e.g., could be (tag x) for a tagsum
   count              ;; count function name, e.g., mysum-count
   case               ;; case macro name, e.g., mysum-case
   prods              ;; list of flexprods, the members of this sum type
   measure            ;; termination measure, e.g., (two-nats-measure ...)
   shape              ;; shape for all prods
   xvar               ;; special x variable name, e.g., mypkg::x
   kwd-alist          ;; alist of options, see *flexsum-keywords*
   orig-prods         ;; original products before parse-flexsum
   inline             ;; inline kind, fix functions
   recp               ;; has a recusive field in some product
   typemacro          ;; defflexsum, deftagsum, defprod, etc
   )
  :tag :sum)

(def-primitive-aggregate flexlist
  ;; A single List type.
  (name               ;; name of this list type, e.g., foolist
   pred               ;; preducate function name, e.g., foolist-p
   fix                ;; fix function name, e.g., foolist-fix
   equiv              ;; equiv function name, e.g., foolist-equiv
   count              ;; count function name, e.g., foolist-count
   elt-type           ;; element type name, e.g., foo
   elt-fix            ;; element fixing function, e.g., foo-fix
   elt-equiv          ;; element equiv function, e.g., foo-equiv
   measure            ;; termination measure, e.g., (two-nats-measure ...)
   xvar               ;; special x variable name, e.g., mypkg::x
   non-emptyp         ;; require the list to be non-empty
   kwd-alist          ;; alist of options, see *flexlist-keywords*
   true-listp         ;; boolean -- should we require a nil final cdr?
   elementp-of-nil    ;; t, nil, or :unknown -- for optimizing theorems
   cheap              ;; passed to std::deflist
   recp               ;; is .elt-type part of the mutual recursion?
   already-definedp
   fix-already-definedp
   )
  :tag :list)

(def-primitive-aggregate flexalist
  ;; A single Alist type.
  (name               ;; name of this alist type, e.g., myalist
   pred               ;; predicate function name, e.g., myalist-p
   fix                ;; fix function name, e.g., myalist-fix
   equiv              ;; equiv function name, e.g., myalist-equiv
   count              ;; count function name, e.g., myalist-count
   key-type           ;; key type name, e.g., mykey-p
   key-fix            ;; key fixing function, e.g., mykey-fix
   key-equiv          ;; key equiv function, e.g., mykey-equiv
   val-type           ;; value type name, e.g., myval-p
   val-fix            ;; value fixing function, e.g., myval-fix
   val-equiv          ;; value equiv function, e.g., myval-equiv
   strategy           ;; fixing strategy: :fixkeys or :dropkeys
   measure            ;; termination measure, e.g., (two-nats-measure ...)
   xvar               ;; special x variable name, e.g., mypkg::x
   kwd-alist          ;; alist of options, see *flexalist-keywords*
   keyp-of-nil        ;; t, nil, or :unknown -- for optimizing theorems
   valp-of-nil        ;; t, nil, or :unknown -- for optimizing theorems
   true-listp         ;; boolean -- should we require a nil final cdr?
   unique-keys        ;; boolean -- require keys to be unique
   recp               ;; is this alist type part of the mutual recursion?
   already-definedp
   fix-already-definedp)
  :tag :alist)

(def-primitive-aggregate flextranssum-member
  ;; A single member of a flextranssum
  (name               ;; name of this member type, e.g., foo
   pred               ;; predicate for this member type, e.g., foo-p
   fix                ;; fixing function this member type, e.g., foo-fix
   equiv              ;; equivalence relation for this member type, e.g., foo-equiv
   tags               ;; possible tags for this type, e.g., (:foo :bar ...)
   recp               ;; boolean -- is this member part of the mutual recursion?
   )
  :tag :flextranssum-member)

(def-primitive-aggregate flextranssum
  ;; A single Transparent Sum Type
  (name               ;; name of this type, e.g., mysum
   pred               ;; predicate function name, e.g., mysum-p
   fix                ;; fix function name, e.g., mysum-fix
   equiv              ;; equiv function name, e.g., mysum-equiv
   count              ;; count function name, e.g., mysum-count
   case               ;; case macro name, e.g., mysum-case
   kind               ;; kind function name, e.g., mysum-kind
   members            ;; list of flextranssum-members
   measure            ;; termination measure, e.g., (two-nats-measure ...)
   xvar               ;; special x variable name, e.g., mypkg::x
   kwd-alist          ;; alist of options, see *transsum-keywords*
   inline             ;; functions to inline
   recp               ;; boolean -- are some of these types mutually recursive?
   )
  :tag :transsum)

(def-primitive-aggregate flexset
  ;; A single Set type.
  (name               ;; name of this set type, e.g., fooset
   pred               ;; preducate function name, e.g., fooset-p
   fix                ;; fix function name, e.g., fooset-fix
   equiv              ;; equiv function name, e.g., fooset-equiv
   count              ;; count function name, e.g., fooset-count
   elt-type           ;; element type name, e.g., foo
   elt-fix            ;; element fixing function, e.g., foo-fix
   elt-equiv          ;; element equiv function, e.g., foo-equiv
   measure            ;; termination measure, e.g., (two-nats-measure ...)
   xvar               ;; special x variable name, e.g., mypkg::x
   ;; non-emptyp         ;; require the set to be non-empty (NYI. sjw: Not sure if it is useful)
   kwd-alist          ;; alist of options, see *flexset-keywords*
   elementp-of-nil    ;; t, nil, or :unknown -- for optimizing theorems
   recp               ;; is .elt-type part of the mutual recursion?
   already-definedp
   fix-already-definedp
   )
  :tag :set)

(def-primitive-aggregate flextypes
  ;; A top-level entry in the flextypes table.
  ;; May bundle up a group of mutually recursive types.
  ;; Alternately, may contain a singleton type (e.g., from defprod, deflist, etc.)
  (name               ;; wrapper name, often shared by a member type
   types              ;; member types -- list of flexsum, flexlist, flexalists, flextranssums, or flexset
                      ;;  (no flexprods here, they'll be inside flexsums)
   kwd-alist          ;; alist of options, see *flextypes-keywords*
   no-count           ;; boolean -- skip the count function?
   recp               ;; bozo could be inferred from types?
   )
  :tag :flextypes)

; The Global Type Database ----------------------------------------------------

(table flextypes-table)

(defun get-flextypes (world)
  "Get the database of defined flextypes."
  (table-alist 'flextypes-table world))

(defmacro add-flextype (x)
  (declare (xargs :guard (flextypes-p x)))
  `(table flextypes-table ',(flextypes->name x) ',x))



; Basic Utilities -------------------------------------------------------------

(defun flexprod-fields->names (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->name (car fields))
          (flexprod-fields->names (cdr fields)))))

(defun flexprod-fields->defaults (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->default (car fields))
          (flexprod-fields->defaults (cdr fields)))))

(defun flexprod-fields->acc-names (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->acc-name (car fields))
          (flexprod-fields->acc-names (cdr fields)))))

(defun flexprods->kinds (prods)
  (if (atom prods)
      nil
    (cons (flexprod->kind (car prods))
          (flexprods->kinds (cdr prods)))))



; with-flextype-bindings ------------------------------------------------------

(defun replace-*-in-symbol-with-str (x str)
  (b* ((name (symbol-name x))
       (idx (search "*" name))
       ((unless idx) x)
       (newname (cat (subseq name 0 idx) str (subseq name (+ 1 idx) nil))))
    (intern-in-package-of-symbol newname x)))

(defun replace-*-in-symbols-with-str-rec (x str)
  (b* (((when (atom x))
        (if (symbolp x)
            (let* ((newx (replace-*-in-symbol-with-str x str)))
              (if (eq newx x)
                  (mv nil x)
                (mv t newx)))
          (mv nil x)))
       ((mv changed1 car) (replace-*-in-symbols-with-str-rec (car x) str))
       ((mv changed2 cdr) (replace-*-in-symbols-with-str-rec (cdr x) str))
       ((unless (or changed1 changed2))
        (mv nil x)))
    (mv t (cons car cdr))))

(defun has-vardot-syms (x vardot)
  (if (atom x)
      (and (symbolp x)
           (eql (search vardot (symbol-name x)) 0))
    (or (has-vardot-syms (car x) vardot)
        (has-vardot-syms (cdr x) vardot))))

(defun replace-*-in-symbols-with-str (x str)
  (b* (((mv ?ch newx) (replace-*-in-symbols-with-str-rec x str)))
    newx))

(defun with-flextype-bindings-fn (binding body default)
  (b* ((var (if (consp binding) (car binding) binding))
       (add-binds (has-vardot-syms body (cat (symbol-name var) ".")))
       (sumbody      (replace-*-in-symbols-with-str body "SUM"))
       (listbody     (replace-*-in-symbols-with-str body "LIST"))
       (alistbody    (replace-*-in-symbols-with-str body "ALIST"))
       (transsumbody (replace-*-in-symbols-with-str body "TRANSSUM"))
       (setbody      (replace-*-in-symbols-with-str body "SET"))
       (cases
        `(case (tag ,var)
           (:sum ,(if add-binds `(b* (((flexsum ,var) ,var)) ,sumbody) sumbody))
           (:list ,(if add-binds `(b* (((flexlist ,var) ,var)) ,listbody) listbody))
           (:alist ,(if add-binds `(b* (((flexalist ,var) ,var)) ,alistbody) alistbody))
           (:transsum ,(if add-binds `(b* (((flextranssum ,var) ,var)) ,transsumbody) transsumbody))
           (:set ,(if add-binds `(b* (((flexset ,var) ,var)) ,setbody) setbody))
           (otherwise ,default))))
    (if (consp binding)
        `(let ((,var ,(cadr binding))) ,cases)
      cases)))

(defmacro with-flextype-bindings (binding body &key default)
  (with-flextype-bindings-fn binding body default))


; Generic Utilities for Top-Level Types ---------------------------------------

(defun flextypelist-recp (x)
  (if (atom x)
      nil
    (or (with-flextype-bindings (x (car x)) x.recp)
        (flextypelist-recp (cdr x)))))

(defun flextypelist-names (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.name)
          (flextypelist-names (cdr types)))))

(defun flextypelist-fixes (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.fix)
          (flextypelist-fixes (cdr types)))))

(defun flextypelist-equivs (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.equiv)
          (flextypelist-equivs (cdr types)))))

(defun flextypelist-predicates (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.pred)
          (flextypelist-predicates (cdr types)))))



(defun flextypes-find-count-for-pred (pred types)
  (if (atom types)
      nil
    (or (with-flextype-bindings (x (car types))
          (and (eq pred x.pred) x.count))
        (flextypes-find-count-for-pred pred (cdr types)))))

(defun search-deftypes-types (type-name types)
  (if (atom types)
      nil
    (or (with-flextype-bindings (x (car types))
          (and (eq type-name x.name) x))
        (search-deftypes-types type-name (cdr types)))))

(defun search-deftypes-table (type-name table)
  ;; Returns (mv flextypes-obj type-obj)
  ;;  - type-obj describes either a sum, list, or alist type,
  ;;  - flextypes-obj is the superior type, whose .types contains the type-obj,
  ;;    and perhaps other types created in the mutual recursion.
  (if (atom table)
      (mv nil nil)
    (let ((type (search-deftypes-types type-name (flextypes->types (cdar table)))))
      (if type
          (mv (cdar table) ;; info for whole deftypes form
              type) ;; info for this type
        (search-deftypes-table type-name (cdr table))))))
