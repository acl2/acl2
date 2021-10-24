; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Testing the shallow embedding macros

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "composite-types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test each kind of type, and some composite types, in a named product type.

(make-product-type "simple-test"
  :shortdoc "Simple named type"
  ("my_int1" (s-type-integer))
  ("my_int2" (s-type-integer)))

;; (syndef::|MAKE-simple-test| :|my_int1| 10 :|my_int2| 20)

(make-product-type "test-primitive-types"
  :shortdoc "Field names have test names."
  ("my_bool" (s-type-boolean))
  ("my_int" (s-type-integer))
  ("my_char" (s-type-character))
  ("my_string" (s-type-string))
  ("my_simple_test" (s-type-ref "simple-test")))

;; (syndef::|MAKE-test-primitive-types| :|my_bool| (s-literal-false) :|my_int| -1 :|my_char| (s-literal-char 95) :|my_string| "_" :|my_simple_test| (syndef::|MAKE-simple-test| :|my_int1| 11 :|my_int2| 21))

(make-product-type "test-options-of-primitive-types"
  :shortdoc "Option types can be confusing."
  ("my_opt1" (s-type-option (s-type-boolean)))
  ("my_opt2" (s-type-option (s-type-integer)))
  ("my_opt3" (s-type-option (s-type-character)))
  ("my_opt4" (s-type-option (s-type-string)))
  ("my_opt5" (s-type-option (s-type-ref "simple-test"))))


;; move this out to the option operator tests
;; (make-product-type "ETEST-1" ("MY-OPT" (s-type-option (s-type-integer))))
;; ...


;; TODO: design operations on option types
;; (syndef::|MAKE-test-options-of-primitive-types| :|my_opt1| (???) :|my_opt2| (???) :|my_opt3| (???) :|my_opt4| (???) :|my_opt5| (???))


(make-product-type "test-types-random1"
  :shortdoc "Field names have test names."
  ;; component primitve types randomly chosen
  ("my_set1" (s-type-set (s-type-boolean)))
  ("my_seq1" (s-type-sequence (s-type-integer)))
  ("my_opt1" (s-type-option (s-type-ref "simple-test")))
  ("my_map1" (s-type-map (s-type-boolean) (s-type-string)))
  ;; 1 composite level randomly chosen then 1 primitve level randomly chosen
  ("my_set2" (s-type-set (s-type-set (s-type-string))))
  ("my_seq2" (s-type-sequence (s-type-map (s-type-ref "simple-test")
                                          (s-type-integer))))
  ;; this was chosen randomly, but what does it mean?
  ("my_opt2" (s-type-option (s-type-option (s-type-ref "simple-test"))))
  ("my_map2" (s-type-map (s-type-sequence (s-type-integer))
                         (s-type-set (s-type-string))))
)

(make-product-type "test-types-misc-set"
  ;; component types (primitive or composite) chosen to cover things that were
  ;; not yet covered
  ("my_set3" (s-type-set (s-type-integer)))
  ("my_set4" (s-type-set (s-type-character)))
  ("my_set5" (s-type-set (s-type-ref "simple-test")))
  ("my_set6" (s-type-set (s-type-sequence (s-type-boolean))))
  ("my_set7" (s-type-set (s-type-option (s-type-boolean))))
  ("my_set8" (s-type-set (s-type-map (s-type-character) (s-type-integer)))))

(make-product-type "test-types-misc-seq"
  ("my_seq3" (s-type-sequence (s-type-character)))
  ("my_seq4" (s-type-sequence (s-type-string)))
  ("my_seq5" (s-type-sequence (s-type-set (s-type-integer))))
  ("my_seq6" (s-type-sequence (s-type-sequence (s-type-sequence (s-type-set (s-type-string))))))
  ("my_seq7" (s-type-sequence (s-type-option (s-type-integer)))))


(make-product-type "test-types-misc-opt"
  ("my_opt3" (s-type-option (s-type-character)))
  ("my_opt4" (s-type-option (s-type-string)))
  ("my_opt5" (s-type-option (s-type-set (s-type-option (s-type-set (s-type-boolean))))))
  ("my_opt6" (s-type-option (s-type-sequence (s-type-integer))))
  ("my_opt7" (s-type-option (s-type-map (s-type-character) (s-type-ref "simple-test")))))


(make-product-type "test-types-misc-map"
  ("my_map_3" (s-type-map (s-type-integer) (s-type-boolean)))
  ("my_map_4" (s-type-map (s-type-string) (s-type-string)))
  ("my_map_5" (s-type-map (s-type-string) (s-type-character)))
  ("my_map_6" (s-type-map (s-type-set (s-type-ref "simple-test")) (s-type-ref "simple-test")))
  ("my_map_7" (s-type-map (s-type-option (s-type-integer)) (s-type-option (s-type-string))))
  ("my_map_8" (s-type-map (s-type-option (s-type-boolean)) (s-type-option (s-type-boolean))))
  ("my_map_9" (s-type-map (s-type-map (s-type-sequence (s-type-option (s-type-boolean)))
                                      (s-type-set (s-type-character)))
                          (s-type-map (s-type-set (s-type-character))
                                      (s-type-sequence (s-type-option (s-type-boolean)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test product type invariant

(make-product-type "str-and-len"
  :shortdoc "str-and-len"
  :longdoc "string and length"
  ("str" (s-type-string))
  ("len" (s-type-integer))
  :invariant (s-equal (s-string-length (s-var-ref "str")) (s-var-ref "len"))
  :fixvals ("" 0))

(defconst *example-str-and-len*
  (syndef::|MAKE-str-and-len| :|str| "abc" :|len| 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sum type tests

(make-sum-type "tiny-mid-big"
  ("tiny" ()) ; just a tag
  ("mid" ( ("x" (s-type-integer))
           ("y" (s-type-integer)) ))
  ("big" ( ("quantifier" (s-type-character))
           ("variables" (s-type-sequence (s-type-string))) )))
;; I also had this here, but we don't yet have an operator that makes instances!
;;           ("matrix" (s-type-ref "str-and-len"))

(defconst *example-tiny*
  (syndef::|MAKE-tiny-mid-big-tiny|))

(defconst *example-mid*
  (syndef::|MAKE-tiny-mid-big-mid| :|x| 1 :|y| -1))

#|| This doesn't work unless s-literal-sequence is defined as a macro.
    If we (include-book "expressions-macros") it will be, but I am
    reluctant to do that since other tests might be perturbed.
    Consider always including expressions-macros so that we can generally have
    ACL2 code with these macros mixed in.
(defconst *example-big*
  (syndef::|MAKE-tiny-mid-big-big|
           :|quantifier| "E"
           :|variables| (s-literal-sequence "some-name" "some-other-name")))
;;           :matrix (s-?? how to make an instance?)
||#

;; type invariant on a product type that is in a sum type

#|| Try to duplicate the fty::deftagsum example at the bottom of composite-types.lisp:

(fty::deftagsum sum-of-two-invariants
  ;; the fill pointer must be nonnegative and less than or equal to the length of the string
  (:str-with-fill-pointer ((str STRING :reqfix (str-reqfix str fill-pointer))
                           (fill-pointer INT :reqfix (fp-reqfix str fill-pointer)))
                           ;; it would make most sense to reuse the following expression
                           ;; in the reqfix functions, but let's try this:
                           :require (str-fill-pointer-compat str fill-pointer))

  ;; the radius must be nonnegative and the angle must be 0 <= angle < 360
  (:polar-coords ((radius INT :reqfix (radius-reqfix radius angle))
                  (angle INT :reqfix (angle-reqfix radius angle)))
                  :require (polar-coords-p radius angle))
  )
)
||#

(make-sum-type "sum-of-two-inv"
    :shortdoc "2" :longdoc "two invariants"
    ("str-with-fill-pointer" ( ("str" (s-type-string))
                               ("fill-pointer" (s-type-integer))
                               :invariant (s-and (s-lte 0 (s-var-ref "fill-pointer"))
                                                 (s-lte (s-var-ref "fill-pointer") (s-string-length (s-var-ref "str"))))
                               :fixvals ("" 0) ))
    ("polar-coords" ( ("radius" (s-type-integer))
                      ("angle" (s-type-integer))
                      :invariant (s-and (s-and (s-lte 0 (s-var-ref "radius"))
                                               (s-lte 0 (s-var-ref "angle")))
                                        (s-lt (s-var-ref "angle") 360))
                      :fixvals (0 0) )))

(defconst *example-sum-alt-1*
  (syndef::|MAKE-sum-of-two-inv-str-with-fill-pointer| :|str| "abc" :|fill-pointer| 3))

(defconst *example-sum-alt-2*
  (syndef::|MAKE-sum-of-two-inv-polar-coords| :|radius| 3 :|angle| 2))

#||
;; can something like this work in a file setting?
(set-guard-checking :none)
(equal (syndef::|MAKE-sum-of-two-inv-str-with-fill-pointer| :|str| "abc" :|fill-pointer| 4) (syndef::|MAKE-sum-of-two-inv-str-with-fill-pointer| :|str| "" :|fill-pointer| 1))
||#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; make-subtype tests

(make-subtype "pos" (s-type-integer)
              "a" (s-gt (s-varref "a") 0)
              1)

(make-subtype "poseven" (s-type-ref "pos")
              "b" (s-equal (s-rem (s-varref "b") 2) 0)
              2)

;; This one demonstrates on-the-fly definition of SEQUENCE[INT].
(make-subtype "fourints" (s-type-sequence (s-type-integer))
              "x" (s-equal (s-length (s-varref "x")) 4)
              (s-literal-sequence 0 0 0 0))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests from MIDAS/example.ams/spec-v0.lisp

;; EM: changed these to match the Syntheto language, where possible,
;;     but tried to keep some comments about the changes.

#||
    These correspond to the type declarations extracted from
    MIDAS/example.ams/spec-v0.lisp
    One persistent difference is that the names of the user-defined types
    and type field names and predicates must all be in the SYNDEF package.
    Also, the recognizer predicates here all have "-P" at the end.
||#

;; The ID part probably doesn't need a package prefix.
;; However, we are standardizing on the names of new types and their fields
;; being in the SYNDEF package.

;; EM: changed from POS to (s-type-integer) since (s-type-pos) not yet in the language
(make-product-type "acid" ("id" (s-type-integer)))

(make-sum-type "actype"
  ("a" ())
  ("b" ())
  ("c" ()))

(make-product-type "aircraft"
  ("id" (s-type-ref "acid")) ; turns into syndef::acid
  ("type" (s-type-ref "actype")))

#||
;; DO NOT USE THIS - NOT IN LANGUAGE!
;; Top-level named option types are not supposed to be in
;; v1 of the Syntheto language.
(make-option-type "maybe-aircraft" (s-type-ref "aircraft"))

;; INSTEAD, use (s-type-object (s-type-ref "aircraft")) wherever it is needed,
;; as an unnamed type.
||#

#||
;; DO NOT USE THIS - NOT IN LANGUAGE!
;; Top-level named set types are not supposed to be in
;; v1 of the Syntheto language,
(make-set-type "acroster" (s-type-ref "aircraft"))

;; INSTEAD, use (s-type-set (s-type-ref "aircraft"))
||#

(make-product-type "mission"
  ("required" (s-type-ref "actype")))

#||
;; DO NOT USE THIS - NOT IN LANGUAGE!
;; Top-level named set types are not supposed to be in
;; v1 of the Syntheto language.
(make-sequence-type "mission-list" (s-type-ref "mission"))

;; INSTEAD, use (s-type-sequence (s-type-ref "mission"))
||#

#||
;; DO NOT USE THIS - NOT IN LANGUAGE!
;; Top-level named set types are not supposed to be in
;; v1 of the Syntheto language.
(make-sequence-type "assignment" (s-type-ref "acid"))

;; INSTEAD, use (s-type-sequence (s-type-ref "acid"))
||#


#||
;; This works if you use the forbidden (make-sequence-type "assignment" ..):
(make-sum-type "result--dont-use"
  ("solution" (("get" (s-type-ref "assignment"))))
  ("nosolution" ()))
||#
;; However, the previous can be rewritten as:

(make-sum-type "result"
  ("solution" (("get" (s-type-sequence (s-type-ref "acid")))))
  ("nosolution" ()))


;; A couple of tests based on type "acid:

(make-sequence-type "seq2"
  (s-type-sequence (s-type-sequence (s-type-ref "acid"))))

(make-map-type "map3"
  (s-type-sequence (s-type-sequence (s-type-ref "acid")))
  (s-type-set (s-type-sequence (s-type-sequence (s-type-ref "acid")))))
