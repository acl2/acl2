; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Translate R1CS json files from Aleo into ACL2 R1CS s-expressions.

;; NOTE: this should eventually go to a different repository.
;; Leo Language is not quite right.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For now, just parse in the blake2s json spec for investigation purposes.

(include-book "kestrel/json-parser/parse-json-file" :dir :system)

(include-book "kestrel/json/top" :dir :system)

(include-book "std/strings/decimal" :dir :system) ; for str::strval and str::intstr

(include-book "projects/regex/regex-ui" :dir :system) ; for b* binder for string regex matching

;; This is currently just for the r1cs package, but we will use other parts in the future.
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)



#||
; Do:
;(in-package "ACL2")
;(include-book "r1cs-json2acl2")

(make-event
 (mv-let (j state) (parse-file-as-json "/home/batman/aleo-notes/r1cs/b2-one-round-v1.0.1.json" state)
   (value `(defconst *blake2s-json-sexp* ',j))))

(make-event
 (mv-let (erp val) (json::parsed-to-value *blake2s-json-sexp*)
   (declare (ignorable erp))
   (value `(defconst *blake2s-json-fty* ',val))))
||#

#||
> (len (json::value-object->members *blake2s-json-fty*))
10
;; This does not work, with error about JSON::MEMBER->NAME$INLINE has no badge:
;; (loop$ for i in (json::value-object->members *blake2s-json-fty*) collect (json::member->name i))
||#

;; this should be in kestrel/json/abstract-syntax.lisp:
(defun member-names (memberlist)
  (if (endp memberlist)
      nil
    (cons (json::member->name (car memberlist))
          (member-names (cdr memberlist)))))

#||
;;; Updated for blake2 one-round v1.0.1
>(member-names (json::value-object->members *blake2s-json-fty*))
("num_inputs" "num_aux"
              "num_constraints" "input_assignment"
              "aux_assignment" "input_indices"
              "output_indices" "at" "bt" "ct")

For original blake2s:
From the .json file:
  "num_inputs": 0,
  "num_aux": 21728,
  "num_constraints": 22048,
  "input_assignment": [],
  "aux_assignment":  ["1", ...] // 21728 single-bit digit strings
  // "at", "bt", "ct" are constraints
  // apparently stored as columns, each of which is a json-array
  // of length 22048

What is the field size for this R1CS?
It looks like it is
8444461749428370424248824938781546531375899335154063827935233455917409239041
= 0x12AB655E9A2CA55660B44D1E5C37B00159AA76FED00000010A11800000000001

because
8444461749428370424248824938781546531375899335154063827935233455917409239040
which shows up often in the R1CS, is likely to be -1 mod p, where p is the group
order for BLS12-377.  Aleo's terminology is "scalar field size" of BLS12-377.
See https://lib.rs/crates/snarkos-curves

Each constraint clause is also a json-array.  Some are empty.  For example,
ct starts with a bunch of empty ones.  It looks like those come from bit constraints,
such as (1-b)b = 0.

Are there any big constraint clauses?

||#

#|| If you want to see a histogram do this in raw lisp:
(in-package "CL-USER")
(defun constraint-clause-size-histogram (clauses)
  (let ((counts nil))
    (dolist (c clauses)
      (let ((c-len (length (json::value-array->elements c))))
        (if (assoc c-len counts :test '=)
            (incf (cdr (assoc c-len counts :test '=)))
          (push (cons c-len 1) counts))))
    counts))
;; then call this:
(constraint-clause-size-histogram
  (append
   (json::value-array->elements (json::object-member-value "at" leo::*blake2s-json-fty*))
   (json::value-array->elements (json::object-member-value "bt" leo::*blake2s-json-fty*))
   (json::value-array->elements (json::object-member-value "ct" leo::*blake2s-json-fty*))))
-> ((0 . 12128) (1 . 21728) (2 . 21728) (3 . 10240) (71 . 4) (72 . 4) (98 . 156) (131 . 156)  )
This is interesting!

Here is an example 2-element clause:

    [
      [
        "1",
        {
          "Input": 0
        }
      ],
      [
        "8444461749428370424248824938781546531375899335154063827935233455917409239040",
        {
          "Aux": 0
        }
      ]
    ]

Next step is to make the s-expressions!
||#

;; Not currently used, but can be used if we use do-regex-match
(defconst *output-bit-descriptor-parse-opts*
  (acl2::parse-options 'acl2::ere
                       nil ; :strict-paren
                       nil ; :strict-brace
                       nil ; :strict-repeat
                       nil ; :case-insensitive
                       ))

(defconst *output-bit-descriptor-regex*
  ;; use "." instead of "(" or ")" to make it easier to read.
  "^(Not|Is).AllocatedBit *{ *variable: *Variable.Aux.([0-9]+).., *value: *Some.(true|false). *})$")

;; Parse "output_indices" and come up with new constraints that map them to output vars.
;; The bit output variables in json are either Is(Aux(NNN)) or Not(Aux(NNN)), and they can
;; have values true or false.
;; Here are four examples from b2-one-round-v1.0.1.json, along with what they mean in terms
;; of an output bit:
;;  "Not(AllocatedBit { variable: Variable(Aux(2352)), value: Some(false) })",
;;    => 1
;;  "Is(AllocatedBit { variable: Variable(Aux(2355)), value: Some(false) })",
;;    => 0
;;  "Is(AllocatedBit { variable: Variable(Aux(2359)), value: Some(true) })",
;;    => 1
;;  "Not(AllocatedBit { variable: Variable(Aux(2366)), value: Some(true) })",
;;    => 0
;; It will be more clear to have R1CS variables that are explictly named OutputNNN
;; that don't have the extra Not() Is() wrapper, that describe the output of the gadget.
;;
;; For each descriptor in "output_indices", we parse it and create an R1CS constraint.
;; * output-index is the index of the input string in output_indices, and is used to make
;;   the output variable name.

#||
;; This works:
(do-regex-match "Not(AllocatedBit { variable: Variable(Aux(2352)), value: Some(false) })"
                        *output-bit-descriptor-regex* *output-bit-descriptor-parse-opts*)
;; But I will use the b* binder instead.
||#

(define parse-output-bit-descriptor ((output-bit-descriptor stringp))
  :returns (mv (idx natp) (i? booleanp) (b booleanp))
  #|| take out xdoc for now
  :short "Parses an output bit descriptor string."
  :long "The @('Is') or @('Not') is part of the R1CS semantics. It returned in the @('is?') value.
         The @('true') or @('false') in the string is the result of satisfying the constraint system.  It is returned in the @('boolval') value.
         If there is any parse error, a runtime error is signalled."
  ||#
  ;; Note: if the hard error is problematic, we can change this to return an erp value instead.
  :verify-guards nil
  (b* (((match *output-bit-descriptor-regex*
               :e ; extended regex
               :full matchvar
               :substrs (is-or-not aux-idx-str true-or-false))
        output-bit-descriptor)
       ((unless matchvar)
        (prog2$ (er hard? 'top-level "unrecognized descriptor in output_indices")
                (mv 0 nil nil)))
       (is? (if (equal is-or-not "Is")
                    t
                  (if (equal is-or-not "Not")
                      nil
                    (prog2$ (er hard? 'top-level "unrecognized Is or Not string in output_indices")
                            nil))))
       (aux-index (str::strval aux-idx-str))
       ((unless (natp aux-index))
        (prog2$ (er hard? 'top-level "incorrect Aux index string in output_indices")
                (mv 0 nil nil)))
       (boolval (if (equal true-or-false "true")
                    t
                  (if (equal true-or-false "false")
                      nil
                    (prog2$ (er hard? 'top-level "unrecognized true or false string in output_indices")
                             nil)))))
    (mv aux-index is? boolval)))

(define output-bit-adapter-constraint ((outvar-base-name string)
                                       (outvar-index natp)
                                       (currvar-base-name string)
                                       (currvar-index natp)
                                       (is? booleanp))
  :verify-guards nil
  #|| take out xdoc for now
  :short "Make output bit variable adapter constraint."
  :long "Returns an R1CS constraint introducing a new bit output variable that
         normalizes the current bit variable.
         If @('is?') is true, the output bit variable is the same as the
         current bit variable.
         If @('is?') is false (i.e., the Boolean constraint has @('Not') in it),
         the output bit variable will have the opposite meaning as the current
         bit variable (i.e., the bit is flipped)."
  ||#
  (if is?
      `((R1CS::A (1 ,(intern-in-package-of-symbol (concatenate 'string outvar-base-name (str::natstr outvar-index)) 'r1cs::hoy)))
        (R1CS::B (1 R1CS::|Input0|))  ; note, Input0 is a special variable meaning 1 (ONE).
        (R1CS::C (1 ,(intern-in-package-of-symbol (concatenate 'string currvar-base-name (str::natstr currvar-index)) 'r1cs::hoy))))
    ;; Otherwise, the constraint sets the output variable to the inverse of the current variable (base 2).
    `((R1CS::A (1 ,(intern-in-package-of-symbol (concatenate 'string outvar-base-name (str::natstr outvar-index)) 'r1cs::hoy))
               (1 ,(intern-in-package-of-symbol (concatenate 'string currvar-base-name (str::natstr currvar-index)) 'r1cs::hoy)))
      (R1CS::B (1 R1CS::|Input0|))
      (R1CS::C (1 R1CS::|Input0|)))))

;; Currently wired in output var base name "Output" and existing constraint var base name "Aux".
(define output-index-bit-string-to-constraint ((output-index natp)
                                               (output-bit-descriptor stringp))
  :verify-guards nil
  (mv-let (aux-index is-p boolval)
      (parse-output-bit-descriptor output-bit-descriptor)
    (declare (ignore boolval))
    (output-bit-adapter-constraint "Output" output-index "Aux" aux-index is-p)))

(define output-index-bit-strings-to-constraints ((starting-outvar-index natp) (bit-descriptors string-listp))
  :verify-guards nil
  (if (endp bit-descriptors)
      nil
    (cons (output-index-bit-string-to-constraint starting-outvar-index (car bit-descriptors))
          (output-index-bit-strings-to-constraints (+ starting-outvar-index 1) (cdr bit-descriptors)))))

;; Another helper function.
;; If you have a list of booleanp values (T or NIL)
;; where T means the output bit is correct and
;; and NIL means the output bit must be flipped,
;; then you can use that to generate the new constraints.
;; WARNING: assumes currvar output vars are sequential.
;;   You must check this property on R1CS before using this tool!
;; Example call:
;;   (output-adapter-booleans-to-constraints "Output" 0 "Aux" 21216 adapter-boolean-list)
(define output-adapter-booleans-to-constraints ((outvar-base-name string)
                                                (outvar-index natp)
                                                (currvar-base-name string)
                                                (currvar-index natp)
                                                (adapter-booleans boolean-listp))
  :verify-guards nil
  (if (endp adapter-booleans)
      nil
    (cons (output-bit-adapter-constraint outvar-base-name outvar-index currvar-base-name currvar-index (car adapter-booleans))
          (output-adapter-booleans-to-constraints outvar-base-name (+ outvar-index 1) currvar-base-name (+ currvar-index 1) (cdr adapter-booleans)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; jr = json r1cs from Aleo in fty form
;; ar = acl2 r1cs in Kestrel's sparse format
;; jr2ar-xxx = convert xxx from jr format to ar format

(define jr2ar-term ((term (json::valuep term)))
  :returns (mv (erp booleanp) (ar-term listp))
  (b* (((unless (and (json::valuep term)
                     (eq :array (json::value-kind term))))
        (mv t nil))
       (jr-term-elements (json::value-array->elements term))
       ;; make sure there are exactly 2 elements
       ((unless (and (consp jr-term-elements) (consp (cdr jr-term-elements))
                     (endp (cddr jr-term-elements))))
        (mv t nil))
       ;; The first json-array element represents the coefficient.
       ;; It should be a string that parses to a positive
       ;; integer, possibly large (253 bits, in this case).
       ((unless (and (json::valuep (first jr-term-elements))
                     (eq :string (json::value-kind (first jr-term-elements)))
                     (stringp (json::value-string->get (first jr-term-elements)))))
        (mv t nil))
       (coefficient (str::strval (json::value-string->get (first jr-term-elements))))
       ((unless (natp coefficient))
        (mv t nil))
       ;; special hack for BLS12-377 scalar field minus 1
       (coefficient-1 (if (= coefficient 8444461749428370424248824938781546531375899335154063827935233455917409239040)
                          -1
                        coefficient))
       ;; The second json-array element represents the variable.
       ;; It should be an object with one member
       ;; that has name either "Input" or "Aux"
       ;; and value that has value-kind :number that parses to a nat.
       ;; We can construct symbols by simply appending the integer value to the
       ;; name.
       ((unless (and (json::valuep (second jr-term-elements))
                     (eq :object (json::value-kind (second jr-term-elements)))))
        (mv t nil))
       ;; @@ next: get the members, then check the rest
       (membs (json::value-object->members (second jr-term-elements)))
       ((unless (and (consp membs)
                     (endp (cdr membs)) ; list has exactly one element
                     (json::memberp (car membs))))
        (mv t nil))
       (base-name (json::member->name (car membs)))
       ((unless (member-equal base-name '("Input" "Aux")))
        (prog2$ (cw "unknown member name for variable in Leo R1CS: ~x0"
                    base-name)
                (mv t nil)))
       (name-index-value (json::member->value (car membs)))
       ((unless (and (json::valuep name-index-value)
                     (eq :number (json::value-kind name-index-value))
                     (natp (json::value-number->get name-index-value))))
        (mv t nil)))
    (mv nil
        (list coefficient-1 (intern-in-package-of-symbol
                             (string-append base-name
                                            (str::intstr (json::value-number->get
                                                          name-index-value)))
                             'r1cs::hoy)))))

(define jr2ar-terms ((terms (true-listp terms)))
  :returns (mv (erp booleanp) (ar-terms listp))
  (b* (((when (endp terms))
        (mv nil nil))
       ((unless (json::valuep (first terms)))
        (mv t nil))
       ((mv erp ar-term) (jr2ar-term (first terms)))
       ((when erp)
        (mv t nil))
       ((mv erp rest-ar-terms) (jr2ar-terms (rest terms)))
       ((when erp)
        (mv t nil)))
    (mv nil (cons ar-term rest-ar-terms))))

;; If Ai*Bi=Ci, Ai, Bi, and Ci are "clauses".
;; However, the return value does not have the symbol R1CS::A, R1CS::B, or
;; R1CS::C, as the first element.  That is done by the caller.
(define jr2ar-clause ((jr-clause json::valuep))
  :returns (mv (erp booleanp) (ar-clause listp))
  (b* (((unless (and (json::valuep jr-clause)
                     (equal :array (json::value-kind jr-clause))))
        (mv t nil))
       (jr-terms (json::value-array->elements jr-clause))
       ((unless (true-listp jr-terms))
        (mv t nil))
       ;; Not sure why I can't just return (jr2ar-terms jr-terms)
       ;; here... the defthm listp-of-jr2ar-clause.ar-clause fails.
       ;; I think I might need to open up the callee.
       ;; I tried doing
       ;; (ar-clause listp :hints (("Goal" :in-theory (enable jr2ar-terms))))
       ;; in the :returns but that didn't work, either.
       ((mv erp ar-terms) (jr2ar-terms jr-terms))
       ((unless (and (not erp)
                     (listp ar-terms)))
        (mv t nil)))
    (mv nil ar-terms)))

(define zip-3-clause-lists-to-1-constraint-list ((at true-listp)
                                                 (bt true-listp)
                                                 (ct true-listp))
  :returns (mv (erp booleanp) (contraint-list listp))
  (b* (((when (and (endp at) (endp bt) (endp ct)))
        (mv nil nil))
       ((when (or (endp at) (endp bt) (endp ct)))
        (mv t nil))
       (at1 (first at))
       (bt1 (first bt))
       (ct1 (first ct))
       ((unless (and (json::valuep at1)
                     (json::valuep bt1)
                     (json::valuep ct1)))
        (mv t nil))
       ((mv erp at1-ar) (jr2ar-clause (first at)))
       ((when erp) (mv t nil))
       ((mv erp bt1-ar) (jr2ar-clause (first bt)))
       ((when erp) (mv t nil))
       ((mv erp ct1-ar) (jr2ar-clause (first ct)))
       ((when erp) (mv t nil))
       ((mv erp rest-constraint-list)
        (zip-3-clause-lists-to-1-constraint-list
         (rest at) (rest bt) (rest ct)))
       ((when erp) (mv t nil)))
    (mv nil
        (cons (list (cons 'r1cs::a at1-ar)
                    (cons 'r1cs::b bt1-ar)
                    (cons 'r1cs::c ct1-ar))
              rest-constraint-list))))

;; Call this on the json you get from parsing the r1cs file from Aleo
(define jr2ar-top ((jr-top json::valuep))
  :returns (mv (erp booleanp) (ar-constraints listp))
  (b* (((unless (and (json::valuep jr-top)
                     (equal :object (json::value-kind jr-top))))
        (mv t nil))
       ((unless (and (json::object-has-member-p "at" jr-top)
                     (json::object-has-member-p "bt" jr-top)
                     (json::object-has-member-p "ct" jr-top)))
        (mv t nil))
       (at-value (json::object-member-value "at" jr-top))
       (bt-value (json::object-member-value "bt" jr-top))
       (ct-value (json::object-member-value "ct" jr-top))
       ((unless (and (json::valuep at-value) (json::value-case at-value :array)
                     (json::valuep bt-value) (json::value-case bt-value :array)
                     (json::valuep ct-value) (json::value-case ct-value :array)))
        (mv t nil))
       (at-list (json::value-array->elements at-value))
       (bt-list (json::value-array->elements bt-value))
       (ct-list (json::value-array->elements ct-value))
       ((unless (and (true-listp at-list)
                     (true-listp bt-list)
                     (true-listp ct-list)))
        (mv t nil))
       ((mv erp constraints)
        (zip-3-clause-lists-to-1-constraint-list at-list bt-list ct-list))
       ((unless (and (not erp)
                     (listp constraints)))
        (mv t nil)))
    (mv nil constraints)))

#||
(make-event
 (mv-let (erp val) (jr2ar-top *blake2s-json-fty*)
   (declare (ignorable erp))
   (b* ((outs (json::object-member-value  "output_indices" *blake2s-json-fty*))
        ((json::pattern (:array json-strings..)) outs)
        ((unless json::match?)
         (prog2$ (er hard? 'top-level "incorrect output_indices member in json R1CS")
                 (mv t nil state)))
        (strings.. (loop$ for s in json-strings.. collect (cadr s))) ;(json::value-string->get s)
        (constraints-to-append (output-index-bit-strings-to-constraints 0 strings..))
        (newval (append val constraints-to-append)))
     (value `(defconst *blake2s-acl2-r1cs* ',newval)))))

(include-book "std/strings/pretty" :dir :system)  ; defines str::pretty

(length (str::pretty *blake2s-acl2-r1cs*))
--> 7,836,057 (that was for the full blake2s, not the one-round)
--> 631,775 for the one-round including 256 added output constraints

(include-book "kestrel/file-io-light/write-strings-to-file" :dir :system)

(acl2::write-strings-to-file (list (str::pretty *blake2s-acl2-r1cs*))
                             "~/aleo-notes/r1cs/blake2s-1r-outvars-acl2.r1cs"
                             'acl2::top-level
                             state)
||#
