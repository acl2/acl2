; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>
;
; Additional Copyright Notice.
;
; This file is adapted from the Milawa Theorem Prover, Copyright (C) 2005-2009
; Kookamara LLC, which is also available under an MIT/X11 style license.

(in-package "STD")
(include-book "support")
(include-book "tools/rulesets" :dir :system)

(defsection tag
  :parents (defaggregate)
  :short "Get the tag from a tagged object."

  :long "<p>The @('tag') function is simply an alias for @('car') that is
especially meant to be used for accessing the <i>tag</i> of a <i>tagged
object</i>.</p>

<p>When new types are introduced by macros such as @(see defaggregate), @(see
fty::defprod), @(see fty::deftagsum), etc., they may be tagged.  When a type is
tagged, its objects have the form @('(tag . data)'), where the @('tag') says
what kind of object is being represented (e.g., ``employee'', ``student'',
etc.) and @('data') contains the actual information for this kind of
structure (e.g., name, age, ...).  Tagging objects has some runtime/memory
cost (an extra cons for each object), but makes it easy to tell different kinds
of objects apart by inspecting their tags.</p>

<p>We could (of course) just get the tag with @(see car), but @('car') is a
widely used function and we do not want to slow down reasoning about it.
Instead, we introduce @('tag') as an alias for @('car') and keep it disabled so
that reasoning about the tags of objects does not slow down reasoning about
@('car') in general.</p>

<p>Even so, tag reasoning can occasionally get expensive.  Macros like
@('defaggregate'), @(see defprod), etc., generally add their tag-related rules
to the @('tag-reasoning') ruleset; see @(see rulesets).  You may generally want
to keep this ruleset disabled, and only enable it when you really want to use
tags to distinguish between objects.</p>

<p>Note: if you are using the @(see fty) framework, it is generally best to
avoid using @('tag') to distinguish between members of the same sum of products
type.  Instead, consider using the custom @('-kind') macros that are introduced
by macros such as @(see fty::deftagsum) and @(fty::deftranssum).</p>"

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
    :hints(("Goal" :in-theory (enable tag))))

  (def-ruleset! std::tag-reasoning nil))

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

(defun da-changer-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "CHANGE-" (symbol-name basename))
   basename))

(defun da-maker-name (basename)
  (intern-in-package-of-symbol
   (concatenate 'string "MAKE-" (symbol-name basename))
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

(defun da-make-valid-fields-for-changer (fields)
  ;; Convert field names into keywords for use in da-changer-args-to-alist.
  (if (consp fields)
      (cons (intern-in-package-of-symbol (symbol-name (car fields)) :keyword)
            (da-make-valid-fields-for-changer (cdr fields)))
    nil))

(defun da-changer-args-to-alist
  ;; Makes sure user-supplied args are valid for this kind of a structure,
  ;; and turn them into a (field . value) alist
  (macroname      ; change-foo or make-foo, for error reporting.
   args           ; user-supplied args to an actual (change-foo ...) macro, i.e.,
                  ; should be like (:field1 val1 :field2 val2)
   kwd-fields     ; list of valid fields (already keywordified) for this aggregate
   )
  (b* (((when (null args))
        nil)
       ((when (atom args))
        (er hard? macroname "Expected a true-list, but instead it ends with ~x0." args))
       ((when (atom (cdr args)))
        (er hard? macroname "Expected :field val pairs, but found ~x0." args))
       (field (first args))
       (value (second args))
       ((unless (member-equal field kwd-fields))
        (er hard? macroname "~x0 is not among the allowed fields, ~&1." field kwd-fields))
       (rest (da-changer-args-to-alist macroname (cddr args) kwd-fields))
       ((when (assoc field rest))
        (er hard? macroname "Multiple occurrences of ~x0 in change/make macro." field)))
    (cons (cons field value)
          rest)))

(defun da-changer-fill-in-fields
  ;; Build the actual arguments to give to the structure's raw constructor
  (obj        ; object being changed, in case we need to extract fields from it
   acc-map    ; binds keywordified fields to their accessors, ordered per constructor
   alist      ; binds keywordified fields to their values, if provided by the user
   )
  (b* (((when (atom acc-map))
        nil)
       (rest (da-changer-fill-in-fields obj (cdr acc-map) alist))
       ((cons field1 accessor1) (car acc-map))
       (look1 (assoc field1 alist))
       ((when look1)
        ;; User gave us a value for this field, so insert it.
        (cons (cdr look1) rest)))
    ;; No value for this field, so get it from the object.
    (cons `(,accessor1 ,obj) rest)))

(defun change-aggregate
  (basename    ; basename for this structure, for name generation
   obj         ; object being changed, e.g., a term in the user's program.
   args        ; user-level arguments to the change macro, e.g., (:name newname :age 5)
   acc-map     ; binds fields to their accessors, e.g., ((name . student->name) ...), ordered per constructor
   macroname   ; e.g., change-student, for error reporting
   )
  (b* ((ctor-name  (da-constructor-name basename))
       (kwd-fields (strip-cars acc-map))
       (alist      (da-changer-args-to-alist macroname args kwd-fields))
       (nobind-p   (or
                    ;; If the object being changed is already evaluated, there's no
                    ;; need to evaluate it. (variables, constants)
                    (atom obj)
                    (and (consp obj)
                         (equal (car obj) 'quote))
                    ;; If the object being changed is never accessed, there's no
                    ;; need to evaluate it.
                    (subsetp kwd-fields (strip-cars alist))))
       (newvar     (if nobind-p
                       obj
                     (acl2::pack (cons macroname obj))))
       (ctor-call  (cons ctor-name
                         (da-changer-fill-in-fields newvar acc-map alist))))
    (if nobind-p
        ctor-call
      `(let ((,newvar ,obj))
         ,ctor-call))))

(defun da-make-changer (basename fields)
  (let* ((x          (da-x basename))
         (change-foo (da-changer-name basename))
         (acc-names  (da-accessor-names basename fields))
         (kwd-fields (da-make-valid-fields-for-changer fields))
         (acc-map    (pairlis$ kwd-fields acc-names)))
    `(defmacro ,change-foo (,x &rest args)
       (change-aggregate ',basename ,x args ',acc-map ',change-foo))))


; (MAKE-FOO ...) MACRO.

(defun da-maker-fill-in-fields
  ;; Build the actual arguments to give to the structure's raw constructor
  (dflt-map  ; binds keywordified fields to default values, ordered per constructor
   alist     ; binds keywordified fields to their values, if provided by the user
   )
  (b* (((when (atom dflt-map))
        nil)
       (rest (da-maker-fill-in-fields (cdr dflt-map) alist))
       ((cons field1 default1) (car dflt-map))
       (look1 (assoc field1 alist))
       ((when look1)
        ;; User gave us a value for this field, so insert it.
        (cons (cdr look1) rest)))
    ;; No value for this field, so use the default value.
    ;; Not quoting the default values is a little scary, but allows for
    ;; the use of things like (pkg-witness "ACL2") and *foo*
    (cons default1 rest)))

(defun make-aggregate
  (basename    ; basename for this structure, for name generation
   args        ; user-level arguments to the make macro, e.g., (:name newname :age 5)
   dflt-map    ; binds keywordified fields to default values, ordered per constructor
   macroname   ; e.g., make-student or make-honsed-student, for error reporting
   honsp       ; call the honsed constructor or not?
   )
  (b* ((ctor-name  (if honsp
                       (da-honsed-constructor-name basename)
                     (da-constructor-name basename)))
       (kwd-fields (strip-cars dflt-map))
       (alist      (da-changer-args-to-alist macroname args kwd-fields)))
    (cons ctor-name
          (da-maker-fill-in-fields dflt-map alist))))

(defun da-make-maker (basename fields defaults)
  (let* ((make-foo    (da-maker-name basename))
         (kwd-fields  (da-make-valid-fields-for-changer fields))
         (dflt-map    (pairlis$ kwd-fields defaults)))
    `(defmacro ,make-foo (&rest args)
       (make-aggregate ',basename args ',dflt-map ',make-foo nil))))

(defun da-make-honsed-maker (basename fields defaults)
  (let* ((make-foo    (da-honsed-maker-name basename))
         (kwd-fields  (da-make-valid-fields-for-changer fields))
         (dflt-map    (pairlis$ kwd-fields defaults)))
    `(defmacro ,make-foo (&rest args)
       (make-aggregate ',basename args ',dflt-map ',make-foo t))))


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
               (not (keywordp form))
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

;; notes: fields-accs is now a mapping from field names to accessors.
;; Defaggregate itself just needs the field names because it always generates
;; the accessor names in the same way, but this now could work in a broader
;; context where the accessors are various different sorts of things.
(defun da-patbind-fn (name fields-accs args forms rest-expr)
  (b* (((mv kwd-alist args)
        (extract-keywords `(da-patbind-fn ',name) '(:quietp) args nil))
       ;; allow ((binder name)) abbrev for ((binder name) name)
       (forms (if (and (not forms)
                       (tuplep 1 args)
                       (symbolp (car args)))
                  args
                forms))
       (- (or (and (tuplep 1 args)
                   (tuplep 1 forms)
                   (symbolp (car args))
                   (not (booleanp (car args))))

              (er hard? 'da-patbind-fn
                  "B* bindings for ~x0 aggregates must have the form ((~x0 ~
                   <name>) <expr>), where <name> is a symbol and <expr> is a ~
                   single term.  The attempted binding of~|~% ~p1~%~%is not ~
                   of this form.~%(Exception:  ((~x0 <name>)) is allowed as ~
                   an abbreviation for ((~x0 <name>) <name>).)"
                  name (cons (cons name args) forms))))

       (var             (car args))
       ;; maps variable names (strings) to accessor functions
       (full-vars-alist (da-patbind-make-field-acc-alist var fields-accs))
       (field-vars      (strip-cars full-vars-alist))
       (used-vars       (da-patbind-find-used-vars rest-expr field-vars nil))
       (- (or used-vars
              (cdr (assoc :quietp kwd-alist))
              (cw "Note: not introducing any ~x0 field bindings for ~x1, ~
                   since none of its fields appear to be used.~%" name var)))

       (bindings (da-patbind-alist-to-bindings used-vars full-vars-alist var)))
    (if (eq var (car forms))
        ;; No need to rebind: this actually turns out to matter for some
        ;; expansion heuristics in the svex library (3vec-fix), which is
        ;; annoying because you'd think a (let nil ...) should be equivalent to
        ;; ... but, well, whatever.
        `(b* ,bindings ,rest-expr)
      `(let ((,var ,(car forms)))
         (declare (ignorable ,var))
         ;; We know var is used in at least the bindings
         (b* ,bindings ,rest-expr)))))

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
       ,(da-make-changer basename fields)
       ,(da-make-maker basename fields nil))))

(defmacro def-primitive-aggregate (name fields &key tag)
  `(make-event
    (def-primitive-aggregate-fn ',name ',fields ',tag)))

#||

(def-primitive-aggregate employee
  (name title department manager salary)
  :tag :helper)

(b* ((emp (make-employee :name "jared"))
     ((employee emp) emp))
  emp.name)

(b* ((emp (make-employee :name "anakin")))
  (change-employee emp :name "vader" :department "evil"))

||#
