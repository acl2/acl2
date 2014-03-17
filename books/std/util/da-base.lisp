; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; Additional copyright notice:
;
; This file is adapted from Milawa, which is also released under the GPL.

(in-package "STD")
(include-book "support")

(defsection tag
  :parents (defaggregate)
  :short "Alias for @('car') used by @(see defaggregate)."

  :long "<p>The types introduced by @('defaggregate') are basically objects of
the form @('(tag . field-data)'), where the tag says what kind of object is
being represented (e.g., \"employee\").</p>

<p>The @('tag') function is an alias for @('car'), and so it can be used to get
the tag from these kinds of objects.  We introduce this alias and keep it
disabled so that reasoning about the tags of objects does not slow down
reasoning about @('car') in general.</p>"

  (defund-inline tag (x)
    (declare (xargs :guard t))
    (mbe :logic (car x)
         :exec (if (consp x)
                   (car x)
                 nil)))

  (defthm tag-forward-to-consp
    (implies (tag x)
             (consp x))
    :rule-classes :forward-chaining
    :hints(("Goal" :in-theory (enable tag)))))

(deftheory defaggregate-basic-theory
  (union-theories
   '(tag
     car-cons
     cdr-cons
     alistp
     assoc-equal
     hons
     booleanp
     booleanp-compound-recognizer
     tag)
   (theory 'minimal-theory)))


(program)

; NAME GENERATION.  We introduce some functions to generate the names of
; constructors, recognizers, accessors, making macros, changing macros, etc.,
; when given the base name of the aggregate.

(defun da-x (basename)
  (intern-in-package-of-symbol "X" basename))

(defun da-constructor-name (basename)
  basename)

(defun da-honsed-constructor-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "HONSED-" (symbol-name basename))
   basename))

(defun da-accessor-name (basename field)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name basename) "->" (symbol-name field))
   basename))

(defun da-accessor-names (basename fields)
  (if (consp fields)
      (cons (da-accessor-name basename (car fields))
            (da-accessor-names basename (cdr fields)))
    nil))

(defun da-recognizer-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name basename) "-P")
   basename))

(defun da-changer-fn-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "CHANGE-" (symbol-name basename) "-FN")
   basename))

(defun da-changer-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "CHANGE-" (symbol-name basename))
   basename))

(defun da-maker-fn-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "MAKE-" (symbol-name basename) "-FN")
   basename))

(defun da-maker-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "MAKE-" (symbol-name basename))
   basename))

(defun da-honsed-maker-fn-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "MAKE-HONSED-" (symbol-name basename) "-FN")
   basename))

(defun da-honsed-maker-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "MAKE-HONSED-" (symbol-name basename))
   basename))


; FIELDS MAPS.
;
; We can lay out the components of the structure in one of three ways:
;
;   :legible    -- alist-based recognizer (any order permitted)
;   :ordered    -- ordered alist-based recognizer (but still with names)
;   :illegible  -- tree-based recognizer without names
;
; Illegible structures are most efficient, but are not very convenient when you
; are trying to debug your code.  By default, we lay out the structure legibly.
;
; A "fields map" is an alist that binds each field name to an s-expression that
; describes how to access it.  For instance, suppose the fields are (A B C).
; For a legible structure, the fields map will be:
;
;   ((A . (cdr (assoc 'a <body>)))
;    (B . (cdr (assoc 'b <body>)))
;    (C . (cdr (assoc 'c <body>))))
;
; Where <body> is either X or (cdr X), depending on whether the structure is
; tagless or not.  For an illegible structure, the (cdr (assoc ...)) terms just
; get replaced with something horrible like (CAR (CDR (CAR <body>))).

(defun da-body (basename tag)
  (if tag
      `(cdr ,(da-x basename))
    (da-x basename)))

(defun da-illegible-split-fields (fields)
  ;; Convert a linear list of fields into a balanced tree with the same fields
  (let ((length (len fields)))
    (cond ((equal length 1)
           (first fields))
          ((equal length 2)
           (cons (first fields) (second fields)))
          (t
           (let* ((halfway   (floor length 2))
                  (firsthalf (take halfway fields))
                  (lasthalf  (nthcdr halfway fields)))
             (cons (da-illegible-split-fields firsthalf)
                   (da-illegible-split-fields lasthalf)))))))

(defun da-illegible-fields-map-aux (split-fields path)
  ;; Convert the balanced tree into a map from field names to paths, e.g.,
  ;; field1 might be bound to (car (car x)), field2 to (cdr (car x)), etc.
  (if (consp split-fields)
      (append (da-illegible-fields-map-aux (car split-fields) `(car ,path))
              (da-illegible-fields-map-aux (cdr split-fields) `(cdr ,path)))
    (list (cons split-fields path))))

(defun da-illegible-fields-map (basename tag fields)
  ;; Convert a linear list of fields into a map from field names to paths.
  (da-illegible-fields-map-aux (da-illegible-split-fields fields)
                               (da-body basename tag)))

(defun da-illegible-structure-checks-aux (split-fields path)
  ;; Convert the balanced tree into a list of the consp checks we'll need.
  (if (consp split-fields)
      (cons `(consp ,path)
            (append (da-illegible-structure-checks-aux (car split-fields) `(car ,path))
                    (da-illegible-structure-checks-aux (cdr split-fields) `(cdr ,path))))
    nil))

(defun da-illegible-structure-checks (basename tag fields)
  ;; Convert a linear list of fields into the consp checks we'll need.
  (da-illegible-structure-checks-aux (da-illegible-split-fields fields)
                                     (da-body basename tag)))

(defun da-illegible-pack-aux (honsp split-fields)
  ;; Convert the tree of split fields into a cons tree for building the struct.
  (if (consp split-fields)
      `(,(if honsp 'hons 'cons)
        ,(da-illegible-pack-aux honsp (car split-fields))
        ,(da-illegible-pack-aux honsp (cdr split-fields)))
    split-fields))

(defun da-illegible-pack-fields (honsp tag fields)
  ;; Convert a linear list of fields into consing code
  (let ((body (da-illegible-pack-aux honsp (da-illegible-split-fields fields))))
    (if tag
        `(,(if honsp 'hons 'cons) ,tag ,body)
      body)))

#||
(da-illegible-fields-map 'taco :taco '(shell meat cheese lettuce sauce))
(da-illegible-pack-fields nil :taco '(shell meat cheese lettuce sauce))

;; (CONS :TACO (CONS (CONS SHELL MEAT)
;;                   (CONS CHEESE (CONS LETTUCE SAUCE))))

||#

(defun da-legible-fields-map (basename tag fields)
  ;; Convert a linear list of fields into a map from field names to paths.
  (if (consp fields)
      (cons (cons (car fields) `(cdr (assoc ',(car fields) ,(da-body basename tag))))
            (da-legible-fields-map basename tag (cdr fields)))
    nil))

(defun da-legible-pack-fields-aux (honsp fields)
  ;; Convert a linear list of fields into the pairs for a list operation
  (if (consp fields)
      `(,(if honsp 'hons 'cons)
        (,(if honsp 'hons 'cons) ',(car fields) ,(car fields))
        ,(da-legible-pack-fields-aux honsp (cdr fields)))
    nil))

(defun da-legible-pack-fields (honsp tag fields)
  ;; Convert a linear list of fields into consing code for a legible map
  (let ((body (da-legible-pack-fields-aux honsp fields)))
    (if tag
        `(,(if honsp 'hons 'cons) ,tag ,body)
      body)))

#||

(da-legible-fields-map 'taco :taco '(shell meat cheese lettuce sauce))
(da-legible-pack-fields nil :taco '(shell meat cheese lettuce sauce))

;; (CONS :TACO (CONS (CONS 'SHELL SHELL)
;;                   (CONS (CONS 'MEAT MEAT)
;;                         (CONS (CONS 'CHEESE CHEESE)
;;                               (CONS (CONS 'LETTUCE LETTUCE)
;;                                     (CONS (CONS 'SAUCE SAUCE) NIL))))))

||#

(defun da-nthcdr-fn (n x)
  (if (zp n)
      x
    `(cdr ,(da-nthcdr-fn (- n 1) x))))

(defmacro da-nth (n x)
  `(car ,(da-nthcdr-fn n x)))

(defun da-ordered-fields-map (n basename tag fields)
  ;; Convert a linear list of fields into a map from field names to paths.
  (if (consp fields)
      (cons (cons (car fields)
                  `(cdr (da-nth ,n ,(da-body basename tag))))
            (da-ordered-fields-map (+ 1 n) basename tag (cdr fields)))
    nil))

(defun da-ordered-pack-fields-aux (honsp fields)
  ;; Convert a linear list of fields into the pairs for a list operation
  (if (consp fields)
      `(,(if honsp 'hons 'cons)
        (,(if honsp 'hons 'cons) ',(car fields) ,(car fields))
        ,(da-ordered-pack-fields-aux honsp (cdr fields)))
    nil))

(defun da-ordered-pack-fields (honsp tag fields)
  ;; Convert a linear list of fields into consing code for a ordered map
  (let ((body (da-ordered-pack-fields-aux honsp fields)))
    (if tag
        `(,(if honsp 'hons 'cons) ,tag ,body)
      body)))



(defun da-ordered-structure-checks-aux (fields path)
  ;; Path is something like (cdddr x).  It's how far down the structure
  ;; we are, so far.
  (if (consp fields)
      (list* `(consp ,path)
             `(consp (car ,path))
             `(eq (caar ,path) ',(car fields))
             (da-ordered-structure-checks-aux (cdr fields) `(cdr ,path)))
    (list `(not ,path))))

(defun da-ordered-structure-checks (basename tag fields)
  ;; Here we want to check that the structure has the right names and
  ;; cons structure.  I.e., (:taco (:shell . __) (:meat . __) ...)
  (da-ordered-structure-checks-aux fields (da-body basename tag)))

#||

(da-ordered-fields-map 0 'taco nil '(shell meat cheese lettuce sauce))
(da-ordered-pack-fields nil :taco '(shell meat cheese lettuce sauce))
(da-ordered-structure-checks 'taco nil '(shell meat cheese lettuce sauce))

||#


(defun da-fields-map (basename tag layout fields)
  ;; Create a fields map of the appropriate type
  (case layout
    (:legible (da-legible-fields-map basename tag fields))
    (:ordered (da-ordered-fields-map 0 basename tag fields))
    (:illegible (da-illegible-fields-map basename tag fields))))

(defun da-pack-fields (honsp layout tag fields)
  ;; Create a fields map of the appropriate type
  (case layout
    (:legible   (da-legible-pack-fields honsp tag fields))
    (:ordered   (da-ordered-pack-fields honsp tag fields))
    (:illegible (da-illegible-pack-fields honsp tag fields))))

(defun da-structure-checks (basename tag layout fields)
  ;; Check that the object's cdr has the appropriate cons structure
  (case layout
    (:legible `((alistp ,(da-body basename tag))
                (consp ,(da-body basename tag))))
    (:ordered   (da-ordered-structure-checks basename tag fields))
    (:illegible (da-illegible-structure-checks basename tag fields))))

(defun da-fields-map-let-bindings (map)
  ;; Convert a fields map into a list of let bindings
  (if (consp map)
      (let* ((entry (car map))
             (field (car entry))
             (path  (cdr entry)))
        (cons (list field path)
              (da-fields-map-let-bindings (cdr map))))
    nil))



; (FOO ...) CONSTRUCTOR.

(defun da-make-constructor-raw (basename tag fields guard honsp layout)
  ;; Previously we allowed construction to be inlined, but we prefer to only
  ;; inline accessors.
  (let ((foo (da-constructor-name basename)))
    `(defund ,foo ,fields
       (declare (xargs :guard ,guard
                       :guard-hints
                       (("Goal" :in-theory (theory 'minimal-theory))
                        (and stable-under-simplificationp
                             ;; I hadn't expected to need to do this, because
                             ;; the constructor is just consing something
                             ;; together, so how could it have guard
                             ;; obligations?
                             ;;
                             ;; But it turns out that it CAN have other guard
                             ;; obligations, since the ,guard above can be
                             ;; arbitrarily complicated.  So, we will rely on
                             ;; the user to provide a theory that can satisfy
                             ;; these obligations.
                             ;;
                             ;; This looks like it does nothing, but really it
                             ;; "undoes" the in-theory event above.
                             '(:in-theory (enable ))))))
       ,(da-pack-fields honsp layout tag fields))))

(defun da-make-honsed-constructor-raw (basename tag fields guard layout)
  (let ((foo        (da-constructor-name basename))
        (honsed-foo (da-honsed-constructor-name basename)))
    `(defun ,honsed-foo ,fields
       (declare (xargs :guard ,guard
                       ;; Same hints as for the ordinary constructor
                       :guard-hints
                       (("Goal"
                         :in-theory (union-theories
                                     '(,foo)
                                     (theory 'minimal-theory)))
                        (and stable-under-simplificationp
                             '(:in-theory (enable ))))))
       (mbe :logic (,foo . ,fields)
            :exec ,(da-pack-fields t layout tag fields)))))



; (FOOP X) RECOGNIZER.

(defun da-make-recognizer-raw (basename tag fields guard layout)
  ;; Previously we allowed recognizers to be inlined, but now we prefer to
  ;; only inline accessors.
  (let* ((foo-p      (da-recognizer-name basename))
         (x          (da-x basename))
         (fields-map (da-fields-map basename tag layout fields))
         (let-binds  (da-fields-map-let-bindings fields-map)))
  `(defund ,foo-p (,x)
     (declare (xargs :guard t
                     :guard-hints
                     (("Goal"
                       :in-theory (union-theories
                                   '((:executable-counterpart acl2::eqlablep)
                                     acl2::consp-assoc-equal
                                     acl2::assoc-eql-exec-is-assoc-equal)
                                   (theory 'defaggregate-basic-theory)))
                      (and stable-under-simplificationp
                           ;; This looks like it does nothing, but the basic
                           ;; effect is to undo the "goal" theory and go back
                           ;; into the default theory.
                           ;;
                           ;; This is sometimes necessary because the later
                           ;; requirements might have guards that depend on the
                           ;; previous requirements.  The user needs to provide
                           ;; a theory that is adequate to show this is the
                           ;; case.
                           '(:in-theory (enable ))))))
     (and ,@(if tag
                `((consp ,x)
                  (eq (car ,x) ,tag))
              nil)
          ,@(da-structure-checks basename tag layout fields)
          (let ,let-binds
            (declare (ACL2::ignorable ,@fields))
            ,guard)))))



; (FOO->BAR X) ACCESSORS.

(defun da-make-accessor (basename field map)
  (let ((foo-p    (da-recognizer-name basename))
        (foo->bar (da-accessor-name basename field))
        (x        (da-x basename))
        (body     (cdr (assoc field map))))
  `(defund-inline ,foo->bar (,x)
     (declare (xargs :guard (,foo-p ,x)
                     :guard-hints (("Goal"
                                    ;; expand hint sometimes needed due to mutual
                                    ;; recursions
                                    :expand (,foo-p ,x)
                                    :in-theory
                                    (union-theories
                                     '(,foo-p
                                       (:executable-counterpart acl2::eqlablep)
                                       acl2::consp-assoc-equal
                                       acl2::assoc-eql-exec-is-assoc-equal)
                                     (theory 'defaggregate-basic-theory))))))
     ,body)))

#||

(da-make-accessor 'taco 'meat
  (da-fields-map 'taco :taco t '(shell meat cheese lettuce sauce) ))

;; (DEFUND-INLINE TACO->MEAT (X)
;;         (DECLARE (XARGS :GUARD (TACO-P X)
;;                         :GUARD-HINTS (("Goal" :IN-THEORY (ENABLE TACO-P)))))
;;         (CDR (ASSOC 'MEAT (CDR X))))

||#

(defun da-make-accessors-aux (basename fields map)
  (if (consp fields)
      (cons (da-make-accessor basename (car fields) map)
            (da-make-accessors-aux basename (cdr fields) map))
    nil))

(defun da-make-accessors (basename tag fields layout)
  (da-make-accessors-aux basename fields (da-fields-map basename tag layout fields)))

(defun da-make-accessor-of-constructor (basename field all-fields)
  (let ((foo->bar (da-accessor-name basename field))
        (foo      (da-constructor-name basename)))
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string (symbol-name foo->bar) "-OF-" (symbol-name foo))
             basename)
     (equal (,foo->bar (,foo . ,all-fields))
            ,field)
     :hints(("Goal"
             :in-theory
             (union-theories
              '(,foo->bar ,foo)
              (theory 'defaggregate-basic-theory)))))))

(defun da-make-accessors-of-constructor-aux (basename fields all-fields)
  (if (consp fields)
      (cons (da-make-accessor-of-constructor basename (car fields) all-fields)
            (da-make-accessors-of-constructor-aux basename (cdr fields) all-fields))
    nil))

(defun da-make-accessors-of-constructor (basename fields)
  (da-make-accessors-of-constructor-aux basename fields fields))



; (CHANGE-FOO ...) MACRO.

(defun da-changer-args-to-alist
  (args           ; user-supplied args to an actual (change-foo ...) macro, i.e.,
                  ; should be like (:field1 val1 :field2 val2)
   valid-fields   ; list of valid fields (already keywordified) for this aggregate
   )
  ;; Makes sure args are valid, turns them into a (field . value) alist
  (b* (((when (null args))
        nil)
       ((when (atom args))
        (er hard? 'da-changer-args-to-alist
            "Expected a true-list, but instead it ends with ~x0." args))
       ((when (atom (cdr args)))
        (er hard? 'da-changer-args-to-alist
            "Expected :field val pairs, but found ~x0." args))
       (field (first args))
       (value (second args))
       ((unless (member-equal field valid-fields))
        (er hard? 'da-changer-args-to-alist
            "~x0 is not among the allowed fields, ~&1." field valid-fields))
       (rest (da-changer-args-to-alist (cddr args) valid-fields))
       ((when (assoc field rest))
        (er hard? 'da-changer-args-to-alist
            "Multiple occurrences of ~x0 in change/make macro." field)))
    (cons (cons field value)
          rest)))

(defun da-make-valid-fields-for-changer (fields)
  ;; Convert field names into keywords for the (change-foo ...) macro
  (if (consp fields)
      (cons (intern-in-package-of-symbol (symbol-name (car fields)) :keyword)
            (da-make-valid-fields-for-changer (cdr fields)))
    nil))

(defun da-alist-name (basename)
  (intern-in-package-of-symbol "ALIST" basename))

(defun da-make-changer-fn-aux (basename field-alist)
  ;; Writes the body of the change-foo macro.  For each field, look up whether the
  ;; field is given a value, or else use the accessor to preserve previous value
  (if (consp field-alist)
      (let* ((field    (caar field-alist))
             (acc      (cdar field-alist))
             (kwd-name (intern-in-package-of-symbol (symbol-name field) :keyword))
             (alist    (da-alist-name basename))
             (x        (da-x basename)))
        (cons `(if (assoc ,kwd-name ,alist)
                   (cdr (assoc ,kwd-name ,alist))
                 (list ',acc ,x))
              (da-make-changer-fn-aux basename (cdr field-alist))))
    nil))

(defun da-make-changer-fn-gen (basename field-alist)
  (let ((alist         (intern-in-package-of-symbol "ALIST" basename))
        (x             (da-x basename))
        (change-foo-fn (da-changer-fn-name basename))
        (foo           (da-constructor-name basename)))
    `(defun ,change-foo-fn (,x ,alist)
       (declare (xargs :mode :program))
       (cons ',foo ,(cons 'list (da-make-changer-fn-aux basename field-alist))))))

(defun da-make-changer-fn (basename fields)
  (da-make-changer-fn-gen basename (pairlis$ fields (da-accessor-names basename fields))))

(defun da-make-changer (basename fields)
  (let ((x             (da-x basename))
        (change-foo    (da-changer-name basename))
        (change-foo-fn (da-changer-fn-name basename))
        (kwd-fields    (da-make-valid-fields-for-changer fields)))
    `(defmacro ,change-foo (,x &rest args)
       (,change-foo-fn ,x (da-changer-args-to-alist args ',kwd-fields)))))



; (MAKE-FOO ...) MACRO.

(defun da-make-maker-fn-aux (basename fields defaults)
  (if (consp fields)
      (let ((kwd-name (intern-in-package-of-symbol (symbol-name (car fields)) :keyword))
            (alist    (da-alist-name basename)))
        (cons `(if (assoc ,kwd-name ,alist)
                   (cdr (assoc ,kwd-name ,alist))
                 ',(car defaults))
              (da-make-maker-fn-aux basename (cdr fields) (cdr defaults))))
    nil))

(defun da-make-maker-fn (basename fields defaults)
  (let ((alist       (da-alist-name basename))
        (make-foo-fn (da-maker-fn-name basename))
        (foo         (da-constructor-name basename)))
    `(defun ,make-foo-fn (,alist)
       (declare (xargs :mode :program))
       (cons ',foo ,(cons 'list (da-make-maker-fn-aux basename fields defaults))))))

(defun da-make-maker (basename fields)
  (let ((make-foo    (da-maker-name basename))
        (make-foo-fn (da-maker-fn-name basename))
        (kwd-fields  (da-make-valid-fields-for-changer fields)))
  `(defmacro ,make-foo (&rest args)
     (,make-foo-fn (da-changer-args-to-alist args ',kwd-fields)))))

(defun da-make-honsed-maker-fn (basename fields defaults)
  (let ((alist              (intern-in-package-of-symbol "ALIST" basename))
        (make-honsed-foo-fn (da-honsed-maker-fn-name basename))
        (honsed-foo         (da-honsed-constructor-name basename)))
    `(defun ,make-honsed-foo-fn (,alist)
       (declare (xargs :mode :program))
       (cons ',honsed-foo ,(cons 'list (da-make-maker-fn-aux basename fields defaults))))))

(defun da-make-honsed-maker (basename fields)
  (let ((make-honsed-foo    (da-honsed-maker-name basename))
        (make-honsed-foo-fn (da-honsed-maker-fn-name basename))
        (kwd-fields         (da-make-valid-fields-for-changer fields)))
    `(defmacro ,make-honsed-foo (&rest args)
       (,make-honsed-foo-fn (da-changer-args-to-alist args ',kwd-fields)))))


; SUPPORT FOR B* INTEGRATION

(defun da-patbind-make-field-acc-alist (var fields-accs)
  ;; Given var = 'foo and fields = '(a b c),
  ;; Constructs '(("FOO.A" . a) ("FOO.B" . b) ("FOO.C" . c))
  (if (atom fields-accs)
      nil
    (acons (concatenate 'string (symbol-name var) "." (symbol-name (caar fields-accs)))
           (cdar fields-accs)
           (da-patbind-make-field-acc-alist var (cdr fields-accs)))))

(defun da-patbind-find-used-vars (form varstrs acc)
  ;; Varstrs is a list of strings such as "X.FOO" "X.BAR" etc.
  ;; Acc accumulates (uniquely) all the symbols in FORM for which the
  ;; symbol-name is in varstrs.
  (if (atom form)
      (if (and (symbolp form)
               (member-equal (symbol-name form) varstrs)
               (not (member-eq form acc)))
          (cons form acc)
        acc)
    (da-patbind-find-used-vars (car form) varstrs
                               (da-patbind-find-used-vars (cdr form) varstrs acc))))

(defun da-patbind-alist-to-bindings (vars valist target)
  (if (atom vars)
      nil
    (let* ((accessor (cdr (assoc-equal (symbol-name (car vars)) valist)))
           (call     (list accessor target))     ;; (taco->shell foo)
           (binding  (list (car vars) call))) ;; (x.foo (taco->shell foo))
      (cons binding
            (da-patbind-alist-to-bindings (cdr vars) valist target)))))


(defxdoc defaggregate-b*-syntax-error
  :parents (defaggregate)
  :short "The @(see b*) binders introduced by @(see defaggregate) now cause
syntax errors in certain cases that were previously accepted."

  :long "<p>Say we have a simple aggregate such as:</p>
@({
    (defaggregate employee (name title phone))
})

<p>Previously the following was a valid (but error-prone!) use of @('b*'):</p>

@({
    (b* ((x            'oops)
         ((employee x) (make-employee :name \"Jimmy\"
                                      :title \"Beta Tester\"
                                      :phone 3145)))
      (list :name x.name
            :title x.title
            :phone x.phone
            :whole x))
})

<p>Here, the @('b*') binder for the aggregate would properly bind the values of
@('x.name'), @('x.title'), and so forth.  However, it previously <b>did not
rebind @('x') itself</b>.  So, the result produced by the above is:</p>

@({
    (:name \"Jimmy\" :title \"Beta Tester\" :phone 3145 :whole oops)
})

<p>This was counter-intuitive, since it sure looks like @('x') is being
re-bound to the @('make-employee') call.</p>

<p>To reduce the chance for confusion, we now detect cases like this and cause
an error.</p>

<h3>Future Plan</h3>

<p>This restriction is a temporary measure, meant to help to ensure that any
existing code based on @('b*') can be updated safely.</p>

<p>After the release of ACL2 6.5, we will remove this restriction and change
the way that these @('b*') binders work, so that they will also bind the
variable itself.</p>

<p>See also <a
href='https://code.google.com/p/acl2-books/issues/detail?id=41'>Issue 41</a> in
the acl2-books issue tracker.</p>")

;; notes: fields-accs is now a mapping from field names to accessors.
;; Defaggregate itself just needs the field names because it always generates
;; the accessor names in the same way, but this now could work in a broader
;; context where the accessors are various different sorts of things.
(defun da-patbind-fn (name fields-accs args forms rest-expr)
  (b* ((- (or (and (tuplep 1 args)
                   (tuplep 1 forms)
                   (symbolp (car args))
                   (not (booleanp (car args))))

              (er hard? 'da-patbind-fn
                  "B* bindings for ~x0 aggregates must have the form ((~x0 ~
                   <name>) <expr>), where <name> is a symbol and <expr> is a ~
                   single term.  The attempted binding of~|~% ~p1~%~%is not ~
                   of this form."
                  name (cons (cons name args) forms))))

       (var             (car args))
       ;; maps variable names (strings) to accessor functions
       (full-vars-alist (da-patbind-make-field-acc-alist var fields-accs))
       (field-vars      (strip-cars full-vars-alist))
       (used-vars       (da-patbind-find-used-vars rest-expr field-vars nil))
       ((unless used-vars)
        (progn$
         (cw "Note: not introducing any ~x0 field bindings for ~x1, since ~
              none of its fields appear to be used.~%" name var)
         rest-expr))

       ;;(- (cw "Var is ~x0.~%" var))
       ;;(- (cw "Full vars alist is ~x0.~%" full-vars-alist))
       ;;(- (cw "Unnecessary field vars are ~x0.~%" unused-vars))
       ;;(- (cw "Optimized vars alist is ~x0.~%" vars-alist))

       ;; The below is adapted from patbind-nth.  Sol is using (pack binding)
       ;; to generate a name that is probably unused.  We'll do the same.

       (binding  (if forms (car forms) var))
       (evaledp  (or (atom binding) (eq (car binding) 'quote)))
       (target   (if evaledp binding (acl2::pack binding)))
       (bindings (da-patbind-alist-to-bindings used-vars full-vars-alist target))

       ;;(- (cw "Binding is ~x0.~%" var))
       ;;(- (cw "Evaledp is ~x0.~%" var))
       ;;(- (cw "Target is ~x0.~%" target))
       ;;(- (cw "New bindings are ~x0.~%" bindings))

       (rest-expr
        (if (equal var binding)
            ;; E.g., The something like ((vl-module x) x) -- this is a common pattern
            ;; and a safe thing to do, so don't cause an error.
            rest-expr
          ;; Found something like ((vl-module x) (change-module y ...)) -- we want to
          ;; make sure x never occurs in the rest-expr now, so that we can bind it in
          ;; future versions of defaggregate.
          `(acl2::translate-and-test
            (lambda (term)
              (or (not (member ',var (all-vars term)))
                  (msg "B* binding of ~x0 to ~x1 is not currently allowed.  See :doc ~x2."
                       ',var ',binding 'defaggregate-b*-syntax-error)))
            ,rest-expr))))

    (if evaledp
        `(b* ,bindings ,rest-expr)
      `(let ((,target ,binding))
         (b* ,bindings
           (check-vars-not-free (,target) ,rest-expr))))))

;; more general than da-make-binder: takes the mapping from fields to accessors
;; instead of generating it
(defun da-make-binder-gen (name field-alist)
  `(defmacro ,(intern-in-package-of-symbol
               (concatenate 'string "PATBIND-" (symbol-name name))
               name)
     (args forms rest-expr)
     (da-patbind-fn ',name
                    ',field-alist
                    args forms rest-expr)))

(defun da-make-binder (name fields)
  (da-make-binder-gen name (pairlis$ fields (da-accessor-names name fields))))

(defun def-primitive-aggregate-fn (basename fields tag)
  (let ((honsp nil)
        (layout :legible)
        (guard t))
    `(progn
       ,(da-make-recognizer-raw basename tag fields guard layout)
       ,(da-make-constructor-raw basename tag fields guard honsp layout)
       ,@(da-make-accessors basename tag fields layout)
       ,@(da-make-accessors-of-constructor basename fields)
       ,(da-make-binder basename fields)
       ,(da-make-changer-fn basename fields)
       ,(da-make-changer basename fields)
       ,(da-make-maker-fn basename fields nil)
       ,(da-make-maker basename fields))))

(defmacro def-primitive-aggregate (name fields &key tag)
  `(make-event
    (def-primitive-aggregate-fn ',name ',fields ',tag)))

#||

(def-primitive-aggregate employee
  (name title department manager salary)
  :tag :foo)

(b* ((emp (make-employee :name "jared"))
     ((employee emp) emp))
  emp.name)

||#
