; Lists of rule names (general purpose)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Lists of rules to be used by Axe and other tools.  This book does not
;; actually include the theorems mentioned in these lists of rules (should it?).

;; I am defining these as 0-ary functions instead of defconsts so I can change
;; them after the fact using :redef.

(include-book "make-axe-rules") ;todo: do we actually want to make the axe-rules here or not?
(include-book "kestrel/sequences/defmap" :dir :system) ;for map-runes (TODO: rename that)
(include-book "priorities")

(include-book "kestrel/lists-light/true-list-fix" :dir :system) ;to ensure we have these rules -- todo

(defun lookup-rules ()
  (declare (xargs :guard t))
  '(lookup-eq-becomes-lookup-equal
    lookup-becomes-lookup-equal
    ;; lookup-equal-of-acons-same ;subsumed by lookup-equal-of-acons
    ;; lookup-equal-of-acons-diff ;subsumed by lookup-equal-of-acons
    lookup-equal-of-acons
    lookup-equal-of-cons
    lookup-equal-of-append))

(defun booleanp-bv-rules ()
  (declare (xargs :guard t))
  '(booleanp-of-sbvlt ;add more!
    booleanp-of-sbvle ;remove if sbvle will always be enabled
    booleanp-of-bvlt
    booleanp-of-bvle ;remove if bvle will always be enabled
    ))

;keep this in sync with the list of known booleans?
;see also boolean-rules
;any defforall should go in this list?
(defun booleanp-rules ()
  (declare (xargs :guard t))
  (append (booleanp-bv-rules) ;drop?  or pass into Axe?  trying to not have axe depend on BV rules.
          '(booleanp-of-myif
            booleanp-of-not
            booleanp-of-equal
            booleanp-of-boolif
            booleanp-of-boolor
            booleanp-of-booland
            booleanp-of-bool-fix-rewrite ;new
            booleanp-of-consp ;move to list rules? ;i guess we are opening atom and endp
            booleanp-of-<
            booleanp-of-unsigned-byte-p
            booleanp-of-all-unsigned-byte-p ;new
            booleanp-of-true-listp           ;new
            booleanp-of-acl2-numberp
            booleanp-of-integerp
            booleanp-of-natp
            booleanp-of-endp ;Tue May 25 04:47:29 2010 drop, since we are opening endp?
            booleanp-of-items-have-len ;new
            )))

(defun boolean-rules-safe ()
  (declare (xargs :guard t))
  '(;; Rules handling constant args:
    booland-of-constant-arg1
    booland-of-constant-arg2
    ;; booland-commute-constant ; trying without since we know how to handle any particular constant
    boolor-of-constant-arg1
    boolor-of-constant-arg2
    boolxor-of-constant-arg1
    boolxor-of-constant-arg2
    ;; Rules about repeated arguments in nests:
    booland-same
    booland-same-2
    boolor-same
    boolor-same-2
    boolxor-same-1
    boolxor-same-2
    ;; Rules about contradicting arguments in nests:
    booland-of-not-same
    booland-of-not-same-alt ;drop?
    booland-of-not-and-booland-same
    booland-of-not-and-booland-same-alt ;drop?
    boolor-of-not-same
    boolor-of-not-same-alt
    boolor-of-not-same-three-terms-alt ; todo: make name more similar to the booland rule
    boolor-of-not-same-three-terms ; todo: make name more similar to the booland rule
    ;; Rules to drop bool-fix when applied to arguments:
    booland-of-bool-fix-arg1
    booland-of-bool-fix-arg2
    boolor-of-bool-fix-arg1
    boolor-of-bool-fix-arg2
    boolxor-of-bool-fix-arg1
    boolxor-of-bool-fix-arg2
    boolif-of-bool-fix-arg1
    boolif-of-bool-fix-arg2
    boolif-of-bool-fix-arg3
    not-of-bool-fix
    if-of-bool-fix-arg1 ; add a rule for myif too?
    bool-fix-of-bool-fix
    ;; Rules about not:
    not-of-not
    ;; Rules about bool-fix:
    bool-fix-when-booleanp
    ;; Rules about boolif:
    boolif-same-branches
    boolif-same-arg1-arg2
    boolif-of-t-and-nil
    boolif-of-nil-and-t
    boolif-when-quotep-arg1 ; for when the test can be resolved
    boolif-of-not-same-arg2-alt
    boolif-of-not-same-arg3-alt
    boolif-of-equal-and-nil-and-equal-diff ; could restrict to constants if needed
    boolif-when-quotep-and-not-booleanp-arg2
    boolif-when-quotep-and-not-booleanp-arg3
    ;; Rules about equal:
    equal-of-t-when-booleanp-arg1
    equal-of-t-when-booleanp-arg2
    ;; Rules about iff (or should we open iff, perhaps to expose and equality of bool-fixes)?:
    iff-of-constant-arg1
    iff-of-constant-arg2
    iff-same
    iff-bool-fix-arg1
    iff-bool-fix-arg2))

;some of these may be necessary for case-splitting in the dag prover to work right
(defun boolean-rules ()
  (declare (xargs :guard t))
  (append
   (boolean-rules-safe)
   `(;; Rules about boolor:
     boolor-of-not-of-boolor-of-not-same ; do we need this?

     ;; Rules about boolif:
     ;; todo: think about these: sometimes we prefer boolif:
     boolif-when-quotep-arg2 ; introduces boolor, or booland of not
     boolif-when-quotep-arg3 ; introduces boolor of not, or booland
     boolif-x-x-y-becomes-boolor ; introduces boolor
     boolif-x-y-x-becomes-booland ; introduces booland
     )))

(defun mv-nth-rules ()
  (declare (xargs :guard t))
  '(mv-nth-of-cons-safe ; since mv expands to cons
    mv-nth-of-myif))

;; Basic rules that we very often want.
(defun base-rules ()
  (declare (xargs :guard t))
  (append '(;axe-rewrite-objective ;fixme investigate why this is needed...
            implies-opener ;; goes to boolor
            force-of-non-nil ;do we still need this?
            equal-nil-of-not
            not-of-not ;BOZO what do we do with the resulting bool-fix?
            equal-same
            not-<-same
            turn-equal-around-axe ; may be dangerous?

            ifix-when-integerp
            ;; ifix can lead to problems (add rules to handle the expanded ifix in an argument position?)

            ;; TODO: eventually phase out myif in favor of if
            myif-becomes-boolif-axe
            myif-of-not
            myif-of-nil
            myif-of-t
            myif-of-constant-when-not-nil
            myif-nil-t
            myif-of-t-and-nil-when-booleanp
            myif-same-branches
            myif-same-test
            myif-same-test2
            myif-same-arg1-arg2-when-booleanp

            ;; todo: compare to the myif rules:
            if-of-t
            if-of-nil
            if-same-branches
            if-of-t-and-nil-when-booleanp
            not-of-if

            fix-when-acl2-numberp
            acl2-numberp-of-+
            acl2-numberp-of-fix
            integerp-of-ifix
            = ; introduces EQUAL
            eql ; introduces EQUAL ; EQL can arise from CASE
            eq ; introduces EQUAL
            /= ; "not equal"

            null ; opens to EQ, which opens to EQUAL (todo: go directly)
            zerop ; opens to EQL, which opens to EQUAL (todo: go directly)

            double-rewrite ; todo: or remove these when we make the axe-rules
            return-last

            not-stringp-of-cons)
          (mv-nth-rules)
          (boolean-rules-safe)
          (booleanp-rules)))

;todo: do we have the complete set of these?
;todo: split the bv ones from the arithmetic ones:
(defun type-rules ()
  (declare (xargs :guard t))
  '(integerp-of-ceiling-of-lg natp-of-ceiling-of-lg
    integerp-of-bitand natp-of-bitand
    integerp-of-bitor natp-of-bitor
    integerp-of-bitxor natp-of-bitxor
    integerp-of-bitnot natp-of-bitnot
    integerp-of-bvcat natp-of-bvcat
    integerp-of-bvsx natp-of-bvsx
    integerp-of-bv-array-read natp-of-bv-array-read
    integerp-of-bvnot natp-of-bvnot
    integerp-of-bvor natp-of-bvor
    integerp-of-bvxor natp-of-bvxor
    integerp-of-bvand natp-of-bvand
    integerp-of-bvif natp-of-bvif
    integerp-of-bvplus natp-of-bvplus
    integerp-of-bvminus natp-of-bvminus
    integerp-of-bvuminus natp-of-bvuminus
    integerp-of-bvmult natp-of-bvmult
    integerp-of-bvmod natp-of-bvmod ;new
    integerp-of-bvdiv natp-of-bvdiv ;new
    integerp-of-sbvdiv natp-of-sbvdiv ;new
    integerp-of-sbvrem natp-of-sbvrem ;new
    integerp-of-bvchop natp-of-bvchop
    integerp-of-slice natp-of-slice
    integerp-of-getbit natp-of-getbit
    integerp-of-leftrotate natp-of-leftrotate
    integerp-of-leftrotate32 natp-of-leftrotate32
    integerp-of-rightrotate natp-of-rightrotate ;drop if we are getting rid of right-rotate
    integerp-of-rightrotate32 natp-of-rightrotate32 ;drop if we are getting rid of right-rotate
    ;how do we handle these?
    integerp-of-bvshl natp-of-bvshl
    integerp-of-bvshr natp-of-bvshr
    integerp-of-bvashr natp-of-bvashr
    integerp-of-repeatbit natp-of-repeatbit

    ;;other shift? ;other math ones?
    integerp-of-logext ;move to logext rules?

    integerp-of--
    integerp-of-+

    integerp-when-unsigned-byte-p-free))

(defun safe-trim-rules ()
  (declare (xargs :guard t))
  '(;these should be safe, because each replaces an argument of a BV op with a
    ;strict subterm of that argument:
    ;; bvcat rules:
    bvand-of-bvcat-low-arg2
    bvand-of-bvcat-low-arg3
    bvor-of-bvcat-low-arg2
    bvor-of-bvcat-low-arg3
    bvxor-of-bvcat-low-arg2
    bvxor-of-bvcat-low-arg3
    bitand-of-bvcat-low-arg1
    bitand-of-bvcat-low-arg2
    bitor-of-bvcat-low-arg1
    bitor-of-bvcat-low-arg2
    bitxor-of-bvcat-low-arg1
    bitxor-of-bvcat-low-arg2
    bvplus-of-bvcat-low-arg2
    bvplus-of-bvcat-low-arg3
    bvmult-of-bvcat-low-arg2
    bvmult-of-bvcat-low-arg3
    bvminus-of-bvcat-low-arg2
    bvminus-of-bvcat-low-arg3
    bvuminus-of-bvcat-low ; todo: also rules for bitnot and bvnot?
    bvif-of-bvcat-low-arg3
    bvif-of-bvcat-low-arg4
    bvcat-of-bvcat-tighten-arg2
    bvcat-of-bvcat-tighten-arg4
    ;; bvsx rules:
    bitand-of-bvsx-low-arg1
    bitand-of-bvsx-low-arg2
    bitor-of-bvsx-low-arg1
    bitor-of-bvsx-low-arg2
    bitxor-of-bvsx-low-arg1
    bitxor-of-bvsx-low-arg2
    bvand-of-bvsx-low-arg2
    bvand-of-bvsx-low-arg3
    bvor-of-bvsx-low-arg2
    bvor-of-bvsx-low-arg3
    bvxor-of-bvsx-low-arg2
    bvxor-of-bvsx-low-arg3
    bvplus-of-bvsx-low-arg2
    bvplus-of-bvsx-low-arg3
    bvmult-of-bvsx-low-arg2
    bvmult-of-bvsx-low-arg3
    bvminus-of-bvsx-low-arg2
    bvminus-of-bvsx-low-arg3
    bvuminus-of-bvsx-low
    ;; todo: what about rules like bvand-of-bvcat-tighten-arg2 here?

    ;;these also seem safe (perhaps trimming constants is always safe?):
    bvcat-normalize-constant-arg2
    bvcat-normalize-constant-arg4
    bvplus-trim-leading-constant))

(defun leftrotate-intro-rules ()
  (declare (xargs :guard t))
  '(;;todo: think about these rules (why so many?):
    ;; TODO: These can't fire if we are expanding the shift ops, which we usually are
    ;; TTODO: handle other idioms (bvxor, bvplus, and a version with shift ops expanded)
    bvor-of-bvshl-and-bvshr-becomes-leftrotate
    bvor-of-bvshr-and-bvshl-becomes-leftrotate
    bvor-of-bvshl-and-bvshr-becomes-leftrotate32-gen
    bvor-of-bvshr-and-bvshl-becomes-leftrotate32-gen
    bvor-of-bvshl-and-bvshr       ;; introduces leftrotate
    bvor-of-bvshr-and-bvshl       ;; introduces leftrotate
    bvor-of-bvshl-and-bvshr-alt   ;; introduces leftrotate
    bvor-of-bvshr-and-bvshl-alt   ;; introduces leftrotate
    bvor-of-bvshl-and-bvashr      ;; introduces leftrotate
    bvor-of-bvashr-and-bvshl      ;; introduces leftrotate
    bvor-of-bvshl-and-bvashr-alt  ;; introduces leftrotate
    bvor-of-bvashr-and-bvshl-alt  ;; introduces leftrotate
    bvcat-of-slice-becomes-leftrotate ;; todo: loops with defn?
    bvcat-of-getbit-becomes-leftrotate ;; todo: loops with defn?
    ))

;; Some of these may not be needed if we are commuting constants forward
(defun bv-constant-chop-rules ()
  (declare (xargs :guard t))
  '(bvand-of-constant-chop-arg2
    bvand-of-constant-chop-arg3
    bvor-of-constant-chop-arg2
    bvor-of-constant-chop-arg3
    bvxor-of-constant-chop-arg2
    bvxor-of-constant-chop-arg3
    bitand-of-constant-chop-arg1
    bitand-of-constant-chop-arg2
    bitor-of-constant-chop-arg1
    bitor-of-constant-chop-arg2
    bitxor-of-constant-chop-arg1
    bitxor-of-constant-chop-arg2
    ;; todo: more like this?
    ;; todo: rename these 4?:
    bvlt-trim-constant-arg1
    bvlt-trim-constant-arg2
    sbvlt-trim-constant-left
    sbvlt-trim-constant-right))

;; Keep this in sync with unsigned-byte-p-forced-rules below.
;todo: Should any of these be generalized?
;todo: what about shift operators?  we need an official list of BV ops
(defun unsigned-byte-p-rules ()
  (declare (xargs :guard t))
  '( ;; todo: add more?
    unsigned-byte-p-of-bvchop
    unsigned-byte-p-of-bvcat-all-cases ;todo name
    unsigned-byte-p-of-bvcat ;todo drop?
    unsigned-byte-p-of-slice-gen
    unsigned-byte-p-of-getbit
    unsigned-byte-p-of-bvif-gen ;todo name
    unsigned-byte-p-of-bvand
    unsigned-byte-p-of-bvor-gen ;improve name
    unsigned-byte-p-of-bvxor-gen ;improve name
    unsigned-byte-p-of-bvnot
    unsigned-byte-p-of-bitand
    unsigned-byte-p-of-bitor
    unsigned-byte-p-of-bitxor
    unsigned-byte-p-of-bitnot
    unsigned-byte-p-of-bvplus
    unsigned-byte-p-of-bvminus-gen-better ;todo name
    unsigned-byte-p-of-bvuminus
    unsigned-byte-p-of-bvmult
    unsigned-byte-p-of-bvdiv
    unsigned-byte-p-of-bvmod-gen ;todo name
    unsigned-byte-p-of-sbvrem
    unsigned-byte-p-of-sbvdiv
    unsigned-byte-p-of-bvsx
    unsigned-byte-p-of-repeatbit
    unsigned-byte-p-of-leftrotate
    unsigned-byte-p-of-leftrotate32
    unsigned-byte-p-of-rightrotate
    unsigned-byte-p-of-rightrotate32
    unsigned-byte-p-of-bv-array-read-gen ;todo name
    unsigned-byte-p-of-bvshl-gen
    unsigned-byte-p-of-bvshr-gen
    unsigned-byte-p-of-bvashr-gen
    unsigned-byte-p-of-0-arg1
    ))

;; Keep this in sync with unsigned-byte-p-rules above.
(defund unsigned-byte-p-forced-rules ()
  (declare (xargs :guard t))
  '(unsigned-byte-p-forced-of-bvchop
    unsigned-byte-p-forced-of-bvcat
    unsigned-byte-p-forced-of-slice
    unsigned-byte-p-forced-of-getbit
    unsigned-byte-p-forced-of-bvif
    unsigned-byte-p-forced-of-bvand
    unsigned-byte-p-forced-of-bvor
    unsigned-byte-p-forced-of-bvxor
    unsigned-byte-p-forced-of-bvnot
    unsigned-byte-p-forced-of-bitand
    unsigned-byte-p-forced-of-bitor
    unsigned-byte-p-forced-of-bitxor
    unsigned-byte-p-forced-of-bitnot
    unsigned-byte-p-forced-of-bvplus
    unsigned-byte-p-forced-of-bvminus
    unsigned-byte-p-forced-of-bvuminus
    unsigned-byte-p-forced-of-bvmult
    unsigned-byte-p-forced-of-bvdiv
    unsigned-byte-p-forced-of-bvmod
    unsigned-byte-p-forced-of-sbvrem
    unsigned-byte-p-forced-of-sbvdiv
    unsigned-byte-p-forced-of-bvsx
    unsigned-byte-p-forced-of-leftrotate
    unsigned-byte-p-forced-of-rightrotate
    unsigned-byte-p-forced-of-leftrotate32
    unsigned-byte-p-forced-of-rightrotate32
    unsigned-byte-p-forced-of-repeatbit
    unsigned-byte-p-forced-of-bool-to-bit
    unsigned-byte-p-forced-of-bvshl
    unsigned-byte-p-forced-of-bvshr
    ;;todo bvashr
    unsigned-byte-p-forced-of-bv-array-read
    ))

;; todo: can these be included in more general convert-to-bv rules?
(defun if-becomes-bvif-rules ()
  (declare (xargs :guard t))
  '(bvchop-of-if-becomes-bvif
    slice-of-if-becomes-slice-of-bvif
    bvcat-of-if-becomes-bvcat-of-bvif-arg2
    bvcat-of-if-becomes-bvcat-of-bvif-arg4
    getbit-of-if-becomes-getbit-of-bvif
    bitand-of-if-becomes-bitand-of-bvif-arg1
    bitand-of-if-becomes-bitand-of-bvif-arg2
    bitor-of-if-becomes-bitor-of-bvif-arg1
    bitor-of-if-becomes-bitor-of-bvif-arg2
    bitxor-of-if-becomes-bitxor-of-bvif-arg1
    bitxor-of-if-becomes-bitxor-of-bvif-arg2
    bitnot-of-if-becomes-bitnot-of-bvif
    bvand-of-if-becomes-bvand-of-bvif-arg2
    bvand-of-if-becomes-bvand-of-bvif-arg3
    bvor-of-if-becomes-bvor-of-bvif-arg2
    bvor-of-if-becomes-bvor-of-bvif-arg3
    bvxor-of-if-becomes-bvxor-of-bvif-arg2
    bvxor-of-if-becomes-bvxor-of-bvif-arg3
    bvnot-of-if-becomes-bvnot-of-bvif
    bvuminus-of-if-becomes-bvuminus-of-bvif
    bvplus-of-if-becomes-bvplus-of-bvif-arg2
    bvplus-of-if-becomes-bvplus-of-bvif-arg3
    bvminus-of-if-becomes-bvminus-of-bvif-arg2
    bvminus-of-if-becomes-bvminus-of-bvif-arg3
    bvmult-of-if-becomes-bvmult-of-bvif-arg2
    bvmult-of-if-becomes-bvmult-of-bvif-arg3
    bvdiv-of-if-becomes-bvdiv-of-bvif-arg2
    bvdiv-of-if-becomes-bvdiv-of-bvif-arg3
    bvmod-of-if-becomes-bvmod-of-bvif-arg2
    bvmod-of-if-becomes-bvmod-of-bvif-arg3
    sbvdiv-of-if-becomes-sbvdiv-of-bvif-arg2
    sbvdiv-of-if-becomes-sbvdiv-of-bvif-arg3
    sbvrem-of-if-becomes-sbvrem-of-bvif-arg2
    sbvrem-of-if-becomes-sbvrem-of-bvif-arg3
    bvlt-of-if-becomes-bvlt-of-bvif-arg2
    bvlt-of-if-becomes-bvlt-of-bvif-arg3
    sbvlt-of-if-becomes-sbvlt-of-bvif-arg2
    sbvlt-of-if-becomes-sbvlt-of-bvif-arg3
    bvif-of-if-becomes-bvif-of-bvif-arg3
    bvif-of-if-becomes-bvif-of-bvif-arg4
    bvsx-of-if-becomes-bvsx-of-bvif-arg3
    repeatbit-of-if-becomes-repeatbit-of-bvif-arg2))

;; These are needed only when operations like logxor or + may appear
;; Used in the x86/ dir.
(defun convert-to-bv-rules ()
  (declare (xargs :guard t))
  '(bvchop-convert-arg2-to-bv-axe
    bvplus-convert-arg2-to-bv-axe-restricted ; todo: use the unrestricted ones
    bvplus-convert-arg3-to-bv-axe-restricted
    bvmult-convert-arg2-to-bv-axe
    bvmult-convert-arg3-to-bv-axe
    ;; logext-convert-arg2-to-bv-axe ; todo: try
    ;; bvminus-convert-arg2-to-bv-axe ; these seemed to cause loops
    ;; bvminus-convert-arg3-to-bv-axe
    bvuminus-convert-arg2-to-bv-axe
    bvand-convert-arg2-to-bv-axe
    bvand-convert-arg3-to-bv-axe
    bvor-convert-arg2-to-bv-axe
    bvor-convert-arg3-to-bv-axe
    bvxor-convert-arg2-to-bv-axe
    bvxor-convert-arg3-to-bv-axe
    getbit-convert-arg2-to-bv-axe
    ;bvcat-convert-arg2-to-bv-axe ; todo: these seemed to cause problems
    ;bvcat-convert-arg4-to-bv-axe ; todo: more!
    ;; logext-convert-arg2-to-bv-axe ; loops with logext-of-bvplus-64
    ;; keep this list in sync with *functions-convertible-to-bv*:
    trim-of-logand-becomes-bvand
    trim-of-logior-becomes-bvor
    trim-of-logxor-becomes-bvxor
    trim-of-lognot-becomes-bvnot
    trim-of-+-becomes-bvplus ; fixme: loop on (bvplus 32 x (+ -4 (rsp x86))) involving bvplus-of-constant-when-overflow?
    trim-of-*-becomes-bvmult
    trim-of-unary---becomes-bvuminus
    ))

;; TODO: Consider also the analogous rules about getbit?
(defun bv-function-of-bvchop-rules ()
  (declare (xargs :guard t))
  '(;; TODO: add all other rules like this!:
    bvnot-of-bvchop
    bvand-of-bvchop-1 ; rename
    bvand-of-bvchop-2 ; rename
    bvor-of-bvchop-arg2 ;newly added: are other similar rules missing?
    bvor-of-bvchop-arg3
    bvxor-of-bvchop-1 ; rename
    bvxor-of-bvchop-2 ; rename
    bvplus-of-bvchop-arg2 ;gen?
    bvplus-of-bvchop-arg3 ;gen?
    bvminus-of-bvchop-arg2
    bvminus-of-bvchop-arg3
    bvuminus-of-bvchop-arg2
    bvif-of-bvchop-arg3 ;mon feb 28 12:18:59 2011
    bvif-of-bvchop-arg4 ;mon feb 28 12:19:01 2011
    bitand-of-bvchop-arg1
    bitand-of-bvchop-arg2
    bitor-of-bvchop-arg1
    bitor-of-bvchop-arg2
    bitxor-of-bvchop-arg1
    bitxor-of-bvchop-arg2
    bvcat-of-bvchop-high
    bvcat-of-bvchop-low
    bvshl-of-bvchop  ;gen?
    bvshr-of-bvchop  ;gen?
    bvashr-of-bvchop ;gen?
    leftrotate32-of-bvchop-arg2
    leftrotate32-of-bvchop-5            ;new ;gen!
    leftrotate-of-bvchop-arg2
    leftrotate-of-bvchop-arg3
    rightrotate-of-bvchop-arg2
    rightrotate-of-bvchop-arg3
    sbvlt-of-bvchop-arg2
    sbvlt-of-bvchop-arg3
    bvlt-of-bvchop-arg2
    bvlt-of-bvchop-arg3
    bvchop-of-bvchop
    getbit-of-bvchop
    slice-of-bvchop-low-gen
    slice-of-bvchop-too-high
    bvdiv-of-bvchop-arg2
    bvdiv-of-bvchop-arg3
    bvmod-of-bvchop-arg2
    bvmod-of-bvchop-arg3
    sbvdiv-of-bvchop-arg2
    sbvdiv-of-bvchop-arg3
    ;; todo: sbvmoddown?
    ))

(defun bvchop-of-bv-rules ()
  (declare (xargs :guard t))
  '(bvchop-of-bvplus ;may not want these?  must have these if we have any of the -all trim rules?!
    bvchop-of-bvminus
    bvchop-of-bvuminus
    bvchop-of-bvmult
    bvchop-of-bvif
    bvchop-of-bvnot
    bvchop-of-bvand
    bvchop-of-bvor
    bvchop-of-bvxor                 ;dup in core rules
    ;;    bvchop-of-bv-array-read ;;we are no longer trimming array reads
    bvchop-of-bvsx
    bvchop-of-slice-both
    bvchop-of-bvchop
    bvchop-of-bvcat-cases))


;fixme a few of these are -all rules...
;; todo: we shouldn't use these without the trim-helpers  - add them to this?
;; add bvlt-trim rules?
(defun trim-rules ()
  (declare (xargs :guard t))
  '(;; -all and -non-all versions?
    slice-trim-axe-all ;new
    getbit-trim-axe-all  ;new
    bvmult-trim-arg1-axe-all  ;seemed to need this for rc6 decrypt
    bvmult-trim-arg2-axe-all  ;seemed to need this for rc6 decrypt
    ;; bvmult-trim-arg1-axe
    ;; bvmult-trim-arg2-axe
    bvminus-trim-arg2-axe-all
    bvminus-trim-arg3-axe-all
    bvplus-trim-arg2-axe-all
    bvplus-trim-arg3-axe-all
    bvuminus-trim-axe-all
    bvnot-trim-axe-all
    bvand-trim-arg1-axe-all
    bvand-trim-arg2-axe-all
    ;; bvand-trim-arg1-axe
    ;; bvand-trim-arg2-axe
    bvor-trim-arg1-axe
    bvor-trim-arg2-axe
    ;; bvor-trim-arg1-axe-all ; use instead?
    ;; bvor-trim-arg2-axe-all ; use instead?
    bvxor-trim-arg1-axe
    bvxor-trim-arg2-axe
    ;; bvxor-trim-arg1-axe-all ; use instead?
    ;; bvxor-trim-arg2-axe-all ; use instead?
    bitnot-trim-axe-all
    bitxor-trim-arg1-axe-all
    bitxor-trim-arg2-axe-all
    bitor-trim-arg1-axe-all
    bitor-trim-arg2-axe-all
    bitand-trim-arg1-axe-all
    bitand-trim-arg2-axe-all
    bvcat-trim-arg4-axe-all ;hope these are okay; seemed key for rc2 and maybe other proofs
    bvcat-trim-arg2-axe-all
    ;; bvcat-trim-arg2-axe
    ;; bvcat-trim-arg4-axe
    bvif-trim-arg1-axe
    bvif-trim-arg2-axe
    ;; bvif-trim-arg1-axe-all ; use instead?
    ;; bvif-trim-arg2-axe-all ; use instead?
    leftrotate32-trim-arg1-axe-all))

(defun trim-helper-rules ()
  (declare (xargs :guard t))
  (append ;(bvchop-of-bv-rules) ; why?
  '(;;need all of these if we are trimming (make sure we have the complete set for all ops we trim!)
    trim-of-repeatbit ;improve?
    trim-of-bvplus ;may not want these?  must have these if we have any of the -all trim rules?!
    trim-of-bvmult
    trim-of-bvminus
    trim-of-bvuminus
    trim-of-bvif
    trim-of-bvnot
    trim-of-bvand
    trim-of-bvor
    trim-of-bvxor
    trim-of-bv-array-read
    trim-of-bvsx
    trim-of-slice
    trim-of-bvchop
    trim-of-bvcat
    trim-of-1-and-leftrotate ; todo: add full trim support for rotate ops
    ;; trim-does-nothing-axe ; should not be needed?
    )))

(defun all-trim-rules ()
  (declare (xargs :guard t))
  (append '(;;bvcat-trim-arg2-axe-all
            ;;bvcat-trim-arg4-axe-all
            )
          (trim-rules)))

;;includes rules from bv-rules-axe.lisp and rules1.lisp and axe-rules-mixed.lisp and dagrules.lisp ?
(defun core-rules-bv ()
  (declare (xargs :guard t))
  (append
   (bvchop-of-bv-rules) ; todo: consider dropping these
   (unsigned-byte-p-rules)
   (bv-constant-chop-rules)
   (leftrotate-intro-rules) ; todo: remove, but this breaks proofs
   (safe-trim-rules) ;in case trimming is disabled
   (trim-helper-rules) ; in case some rule introduces trim (harmless if no rule does)
   (bv-function-of-bvchop-rules)
   (unsigned-byte-p-forced-rules) ; needed for some rules below
   '(;; our normal form is to let these open up to calls to bvlt and sbvlt:
     bvle ;Thu Jan 19 16:35:59 2017
     bvge ;Thu Jan 19 16:35:59 2017
     bvgt ;Thu Jan 19 16:35:59 2017
     sbvle ;new
     sbvge ;Thu Jan 19 16:35:59 2017
     sbvgt ;Thu Jan 19 16:35:59 2017
     bitxor$ ; always expand

     ;; Handling rotates: ; todo: compare to the rules below for leftrotate32
     rightrotate-becomes-leftrotate ;turn rightrotate into leftrotate
     leftrotate-of-0-arg2
     leftrotate-of-0-arg3
     equal-of-leftrotate-and-leftrotate
     getbit-of-leftrotate-simple
     bitand-of-leftrotate-arg1-trim ; move these to trim-rules?
     bitand-of-leftrotate-arg2-trim
     bitor-of-leftrotate-arg1-trim
     bitor-of-leftrotate-arg2-trim
     bitxor-of-leftrotate-arg1-trim
     bitxor-of-leftrotate-arg2-trim

     ;; Handling rotates (32 bit):
     rightrotate32-becomes-leftrotate32-gen ;turn rightrotate32 into leftrotate32
     getbit-of-leftrotate32-simple
     ;; getbit-of-leftrotate32-high
     leftrotate32-of-0-arg1
     leftrotate32-of-0-arg2

     ;; rightrotate32-trim-amt-axe ;move to trim rules? or drop since we go to leftrotate32
     ;;i don't think we want these any more (trying without them):
     ;;opening rotates (by constant amounts) in sha1 caused problems with trimming the same term to lots of different sizes
     ;; LEFTROTATE32-open-when-constant-shift-amount
     ;; leftrotate-open-when-constant-shift-amount
     ;; rightrotate-open-when-constant-shift-amount ;bozo just go to leftrotate
     bvchop-of-leftrotate32-does-nothing ;drop since we have bvchop-identity-axe?
     leftrotate32-of-leftrotate32
     leftrotate-becomes-leftrotate32 ;go to leftrotate32 when possible (since the STP translation supports it) ; warning: loops with defn of leftrotate32
     ;;leftrotate-becomes-leftrotate64
     equal-of-leftrotate32-and-leftrotate32
     equal-of-constant-and-leftrotate32
     slice-of-leftrotate32-high

     not-sbvlt-when-sbvlt-rev-cheap-2
     equal-of-constant-when-sbvlt ; rename
     equal-constant-when-not-sbvlt ; rename
     not-sbvlt-same
     sbvlt-transitive-1-a ;these are new
     sbvlt-transitive-2-a
     sbvlt-transitive-1-b
     sbvlt-transitive-2-b
     sbvlt-transitive-3-a
     sbvlt-transitive-3-b
     sbvlt-transitive-another-cheap ;    sbvlt-transitive-another ;;trying to remove this Mon Feb  1 17:00:34 2016


     bvif-of-equal-1-0                       ;Mon Apr 25 14:56:14 2016
     bvif-of-equal-0-1                       ;Mon Apr 25 14:56:14 2016
     equal-of-constant-and-bitxor-of-constant ;Sun Apr 24 19:42:42 2016

     ;; or should we always open bvminus to bvplus of bvuminus?
     bvminus-same                             ;tue dec 15 12:03:12 2015
     bvplus-of-bvminus-same-arg2
     bvplus-of-bvminus-same-arg3
     bvminus-of-0-arg1
     bvminus-of-0-arg2
     bvminus-of-0-arg3
     bvminus-of-bvplus-and-bvplus-same
     bvminus-of-constant-and-bvplus-of-constant
     bvminus-of-bvplus-of-constant-and-constant
     bvminus-cancel-3-2 ; todo: more!

     bvplus-of-0-arg2
     bvplus-of-ifix-arg2
     bvplus-of-ifix-arg3

     bvand-of-0-arg2
     bvand-of-0-arg3 ; could drop if commuting constants forward
     bvor-of-0-arg2
     bvor-of-0-arg3 ; could drop if commuting constants forward
     bvxor-of-0-arg2
     bvxor-of-0-arg3 ; could drop if commuting constants forward

     bitand-of-0-arg1
     bitand-of-0-arg2 ; could drop if commuting constants forward
     bitand-of-1-arg1
     bitand-of-1-arg2 ; could drop if commuting constants forward
     bitor-of-0-arg1
     bitor-of-0-arg2 ; could drop if commuting constants forward
     bitor-of-1-arg2
     bitor-of-1-arg1 ; could drop if commuting constants forward
     bitxor-of-0-arg1
     bitxor-of-0-arg2 ; could drop if commuting constants forward
     ;; bitxor-of-1-becomes-bitnot-arg2 ; best to keep the bitxor since we have special handling for bitxor nests
     ;; bitxor-of-1-becomes-bitnot-arg1 ; best to keep the bitxor since we have special handling for bitxor nests

     bvand-same
     bvand-same-2
     bvor-same
     bvor-same-2
     bvxor-same
     bvxor-same-2
     bitand-same
     bitand-same-2
     bitor-same
     bitor-same-2
     bitxor-same
     bitxor-same-2

     bvnot-of-bvnot
     bitnot-of-bitnot

     bvand-of-myif-arg1
     bvand-of-myif-arg2
     bvxor-of-myif-1
     bvxor-of-myif-2
     bitxor-of-myif-arg1
     bitxor-of-myif-arg2

     equal-of-bvchop-and-constant-when-bvlt-constant-1
     equal-of-bvchop-and-constant-when-bvlt-constant-2
     equal-of-bvchop-and-constant-when-not-bvlt-constant-1
     equal-of-bvchop-and-constant-when-not-bvlt-constant-2

     getbit-identity-free ;Sun Mar 13 03:18:26 2011

     ;; TODO: More like this?
     bvand-combine-constants
     bvor-combine-constants
     bvxor-combine-constants
     bitand-combine-constants
     bitor-combine-constants
     bitxor-combine-constants
     bvplus-combine-constants
     bvmult-combine-constants
     bvdiv-of-bvdiv-arg2-combine-constants
     sbvdiv-of-sbvdiv-arg2-combine-constants
     bvcat-combine-constants

     bvshr-of-0-arg1
     bvshr-of-0-arg2
     bvshr-of-0-arg3

     bvashr-of-0-arg1
     bvashr-of-0-arg2
     bvashr-of-0-arg3

     bvshl-of-0-arg1
     bvshl-of-0-arg2
     bvshl-of-0-arg3
     ;; bvchop-of-bvshl ; this can change the size of the bvshl, so refrain until we improve the pre-stp translation to handle arbitrary sizes
     bvchop-of-bvshl-same
     bvchop-of-bvshl-does-nothing

     equal-of-bvplus-and-bvplus-cancel-arg2-arg2 ;sat feb 19 17:28:05 2011
     equal-of-bvplus-and-bvplus-cancel-arg1-arg2
     equal-of-bvplus-and-bvplus-cancel-arg2-arg1

     not-equal-bvchop-when-not-equal-bvchop      ;tue feb  8 12:55:33 2011
     bvmod-of-0-arg2
     slice-when-not-bvlt-free ;fri jan 28 18:39:08 2011
     slice-when-bvlt-gen      ;wed mar 16 00:47:10 2011 was in axe-rules
     equal-constant-when-not-slice-equal-constant ;was in axe prover rules
     equal-constant-when-slice-equal-constant     ;was in axe prover rules
     bvnot-becomes-bvxor ;new! fri jan 28 13:08:38 2011

     equal-of-0-and-bvxor
     ;; equal-of-0-and-bitxor
     bvxor-tighten-axe-bind-and-bind ;Sat Jan 22 07:15:44 2011

     bitxor-of-unary-minus-arg1 ;fixme lots of others like this, or use trim!
     bitxor-of-unary-minus-arg2
     bvcat-of-unary-minus-low
     bvcat-of-unary-minus-high
     bvcat-of-ifix-arg2
     bvcat-of-ifix-arg4

     bvplus-of-bvplus-of-bvuminus

     natp-when-unsigned-byte-p ;uses the dag assumptions, has a free var so should be cheap? (put last of the natp rules?) moved from yet-more-rules
     not-<-of-0-when-unsigned-byte-p
     <-of-constant-when-unsigned-byte-p ; causes problems for md5-loop-one-case (todo: why?)

     equal-of-bvmod-and-mod ;where should these go?
     equal-of-mod-and-bvmod

     bvmod-trim-arg1-axe-all ;moved from axe-prover-rules
     bvmod-trim-arg2-axe-all ;moved from axe-prover-rules

;bvmod-of-bvplus-of-bvmod ;has a work-hard
     bvlt-of-bvmod-same
     mod-becomes-bvmod-free-and-free ; use a better one? ; todo: include more rules?
     mod-becomes-bvmod-axe-free-and-bind-free
     mod-becomes-bvmod-axe-bind-free-and-free

     bvcat-of-0-arg2 ;trying... for when the highval is 0

     ;; TODO: more like this?
     ;; TODO: Replace these with of-0-arg1 rules, which may fail faster (no need
     ;; to relieve a hyp).  Or might a negative size actually arise?
     bvxor-when-size-is-not-positive
     bvor-when-size-is-not-positive
     bvand-when-size-is-not-positive
     bvnot-when-size-is-not-positive
     bvplus-when-size-is-not-positive
     bvmult-when-size-is-not-positive
     bvminus-when-size-is-not-positive
     bvuminus-when-size-is-not-positive
     bvmod-when-size-is-not-positive
     bvdiv-when-size-is-not-positive
     bvif-when-size-is-not-positive ;bvif-of-0-arg1
     bvlt-when-not-posp-arg1
     ;; Rules about size=0:
     bvcat-of-0-arg1
     bvcat-of-0-arg3

     not-equal-constant-when-unsigned-byte-p ;Fri Dec 17 01:47:42 2010
     ;;not-equal-constant-when-unsigned-byte-p-alt ;not needed since we commute constants forward?

     equal-of-slice-and-slice-same-low

     getbit-of-bvcat-all ;newly moved here
     getbit-of-bvmult-of-expt-constant-version

;slice-of-bvplus-cases-no-split-case-no-carry-constant-version ;new
     bitxor-of-ifix-arg1
     bitxor-of-ifix-arg2

     getbit-of-slice ;new
     slice-subst-in-constant
     slice-subst-in-constant-alt
     slice-when-bvchop-known    ;new
     ;bvplus-of-bvshl              ;new ; rename or drop
     bvplus-of-bvshl-becomes-bvcat-arg2
     bvplus-of-bvshl-becomes-bvcat-arg3
     bvuminus-of-bvcat-of-0-16-8 ;new!

     bvplus-of-bvchop-and-bvshl ;new
     bvchop-of-bvshr-becomes-slice-safe ;newish: remove?? with bvshr we can split into cases easily.
     bvchop-of-bvashr-safe ; introduces slice
     bvchop-of-bvif ; drop, if we keep bvchop-of-bv-rules?

     ;; TODO: More like this:
     bvcat-of-getbit-arg2
     bvcat-of-getbit-arg4
     bitnot-of-getbit-0
     bitand-of-getbit-arg1
     bitand-of-getbit-arg2
     bitor-of-getbit-arg1
     bitor-of-getbit-arg2
     bitxor-of-getbit-arg1
     bitxor-of-getbit-arg2
     bvif-of-getbit-arg3
     bvif-of-getbit-arg4

     not-bvlt-self
     bvlt-of-bvmod-false
     bvlt-transitive-1-a
     bvlt-transitive-1-b
     bvlt-transitive-2-a
     bvlt-transitive-2-b
     bvlt-transitive-3-a
     bvlt-transitive-3-b
     bvlt-transitive-4-a
     bvlt-transitive-4-b
     bvlt-transitive-5-a
     bvlt-transitive-5-b
     not-bvlt-when-not-bvlt-narrower
     not-bvlt-when-not-bvlt-narrower2

     not-bvlt-of-max-arg2-constant-version
     bvlt-of-max-when-bvlt-constant-version
     ;bvlt-of-max-arg3-constant-version-axe ; has a rewrite-objective
     bvlt-of-max-minus-1-arg2-constant-version

     not-equal-max-int-when-<=      ;new, rename

     repeatbit-of-1     ;new
     lg                 ;new
     getbit-of-repeatbit ;new - what else do we need about repeatbit?

     sbvlt-becomes-bvlt-better   ;expensive?
     SBVLT-OF-0-WHEN-SHORTER2-axe ;new
     bvif-of-bvif-same-1
     bvif-of-bvif-same-2
     bvif-of-bvif-same-3
     bvif-of-bvif-same-4
     equal-of-bvif-constants
     equal-of-bvif-constants2
     bvif-of-not


;    bvlt-of-0-arg2 ;fixme use polarity?
     bvlt-of-0-arg3

     bvmult-of-0-arg2
     bvmult-of-1-arg2
     bvmult-of-ifix-arg2
     bvmult-of-ifix-arg3


     bvminus-solve ;don't we get rid of bvminus?
;    bvminus-solve-for-dag2 ;drop, if we commute constants to the front of the equal?
     bvchop-identity-axe

;clean up these bvchop rules..
;trying without...

     ;; BVCHOP-OF-BVPLUS  ;do we want to do this, or does it replicate the bvplus term at many different sizes?
     ;; bvchop-of-bvminus2 ;see bvchop-identity-axe
     ;bvchop-of-bvminus ;don't we get rid of bvminus?
     ;bvchop-of-bvuminus

;trying without...
     ;; bvchop-of-bvmult2 ; just a special case of bvchop-identity
     ;; bvchop-of-bvmult ;i'm not sure we want to do this...  this can replicate the bvmult term at many different sizes

     ;; BVCHOP-OF-BVOR-GEN ;trying without, since this might cause a lot of work to be done
;BVCHOP-OF-BVOR-does-nothing ;see bvchop-identity-axe
;            bvchop-of-getbit ;see bvchop-identity-axe

     bvchop-of-bvcat-cases
     bvchop-of-0-arg1
     bvchop-1-becomes-getbit
     bvchop-of-slice-both
;this may be bad... trying without..
;                bvchop-of-bvxor-gen ;perhaps we could be a bit more efficient when n=size?
;    bvchop-of-bvxor-does-nothing ;this one seems safe..
     bvchop-of-bvxor ; drop?

     ;; these replace the numeric bound rules, and require the unsigned-byte-p-forced rules
     <-lemma-for-known-operators-axe-alt
     <-lemma-for-known-operators-axe
     <-lemma-for-known-operators-axe2
     <-lemma-for-known-operators-axe3

     <-of-bv-and-non-positive-constant ;Thu May 17 00:37:24 2012

     ;; We leave most commutativity rules out of core-rules-bv, because they can be expensive for large nests
     ;; TODO: What about rules like bvplus-commute-constant2 ?
     bvplus-commute-constant
     bvmult-commute-constant
     bvand-commute-constant
     bvor-commute-constant
     bvxor-commute-constant
     bitand-commute-constant
     bitor-commute-constant
     bitxor-commute-constant

;think about these:
     bvand-of-bvxor-of-ones-same-alt
     bvand-of-bvxor-of-ones-same
;rename these?:
     bvand-of-bvand-of-bvnot-same-xor-version
     bvand-of-bvand-of-bvnot-same-alt-xor-version

;in case we can't choose which form to prefer (but we should probably choose?)
     equal-of-bvnot-and-bvxor-ones
     equal-of-bvxor-ones-and-bvnot
     bvlt-of-constant-when-too-narrow-axe
     not-bvlt-of-constant-when-too-narrow-axe
     equal-of-maxint-when-sbvlt ;Sun Oct 26 16:32:40 2014 ; rename
     sbvlt-of-bvplus-of-1       ;Sun Oct 26 16:32:17 2014

     ;; rules about bvsx:
     bvchop-of-bvsx-low          ;new
     ; slice-of-bvsx-high ; introduces repeatbit..
     equal-of-0-and-bvsx ;Wed Oct 14 13:28:17 2015
     equal-of-bvsx-and-bvsx
     bvsx-too-high-axe
     bvsx-when-sizes-match
     getbit-of-bvsx
     ;; bvsx base cases?
     ;; introduce-bvsx-25-7 ;fixme yuck
     bvsx-of-bvsx
     bvsx-of-bvchop
     bvsx-when-equal-of-getbit-and-0

     ;;bvif-trim-constant-arg1
     ;;bvif-trim-constant-arg2

     bvuminus-of-bvuminus

     bvlt-of-bvif-arg2-safe
     bvlt-of-bvif-arg3-safe
     bvplus-of-bvif-arg2-safe
     bvplus-of-bvif-arg3-safe
     equal-of-bvif-safe

     bvcat-associative ;trying...

     bvcat-of-bvcat-high-tighten ;bozo general rule?
     bvcat-of-getbit-high-tighten
     bvcat-of-bvchop-high-tighten-axe ;gen the bvchop to any bv term
;            bvcat-of-bvcat-tighten-arg2 ;use trim Mon Mar 14 18:54:23 2011
;    bvmult-27-bvcat-hack ;;trying without...
;            bvmult-8-27-blast-hack
;           bvmult-8-27-blast
;bvmult-of-bvcat-trim-arg2 handled by trim rules
;bvmult-of-bvcat-trim-arg1 handled by trim rules
     bvand-1-becomes-bitand
     bvxor-1-becomes-bitxor
     bvor-1-becomes-bitor

     bvand-with-constant-mask-arg2
     bvand-of-constant-when-power-of-2p
     bvand-of-constant-when-low-byte-0 ; for masks that pick out bytes
     ;; trying without
;            bvor-appending-idiom-low
;           bvor-appending-idiom-low-alt

;dropping since we go to bitxor
;            bvxor-1-of-getbit-arg1 ;bozo analogues for other ops?
;           bvxor-1-of-getbit-arg2 ;bozo analogues for other ops?

;            bitand-of-slice-arg1
;           bitand-of-slice-arg2
;            bitxor-of-slice-arg1 done by trim rule and slice-becomes-getbit
;            bitxor-of-slice-arg2 done by trim rule and slice-becomes-getbit
;these may have caused big problems:
     ;;                 bitxor-of-bitnot-arg2
     ;;                 bitxor-of-bitnot-arg1
;            bitxor-of-bvor-arg1 ;done by trim rules
;           bitxor-of-bvor-arg2 ;done by trim rules
;            bitxor-of-bvchop-arg1 ;done by trim rules and BVCHOP-1-BECOMES-GETBIT
;           bitxor-of-bvchop-arg2 ;done by trim rules and BVCHOP-1-BECOMES-GETBIT

     getbit-test-is-self ;make a myif version?

     getbit-too-high-is-0-bind-free-axe
     getbit-too-high-cheap-free
     ;; high-getbit-of-getbit-is-0 ; handled by getbit-too-high-is-0-bind-free-axe
     getbit-of-if
;            getbit-of-bvif ;could be expensive? newww
;            GETBIT-OF-SLICE-TOO-HIGH ;handled by getbit-too-high-is-0-bind-free-axe
;fixme do we want these?
; trying without these... todo: do we want these or not?:
     ;; getbit-of-bvor-eric
     ;; getbit-of-bvor-eric-2
     getbit-of-bvor-when-narrow-arg2-axe
     getbit-of-bvor-when-narrow-arg3-axe
     ;; getbit-of-bvand-eric
     ;; getbit-of-bvand-eric-2
     ;; getbit-0-of-bvxor-eric
     ;; getbit-of-bvxor-eric-2
     getbit-identity-axe
     ;; getbit-0-of-getbit ; not needed if we have getbit-identity-axe
     getbit-of-bitxor-all-cases ;covered by the too-high and identity rules if n is a constant
     getbit-of-bitor-all-cases ;covered by the too-high and identity rules if n is a constant
     getbit-of-bitand-all-cases ;covered by the too-high and identity rules if n is a constant
     ;; getbit-of-bvchop-too-high ; covered by getbit-too-high-is-0-bind-free-axe

     slice-out-of-order
     slice-too-high-is-0-bind-free-axe
     slice-too-high-when-unsigned-byte-p ; requires an unsigned-byte-p hyp, should be fairly cheap
     ;; slice-of-getbit-too-high ; just use slice-too-high-is-0-bind-free-axe
     slice-becomes-getbit
     slice-becomes-bvchop
     slice-of-slice
;            slice-of-bvcat-hack-gen-better-case-1 ;trying the real versions
;           slice-of-bvcat-hack-gen-better-case-2
;          slice-of-bvcat-hack-gen-better-case-3
     slice-of-bvcat-gen

     bvsx-of-bvif-safe

     bvlt-when-bvlt-false
     bvlt-when-bvlt-false2

     myif-of-sbvlt-of-0-and-not-sbvlt-of-0 ;; useful for the JVM's LCMP instruction
     myif-of-sbvlt-of-0-and-equal-of-0
     booland-of-not-sbvlt-and-not-equal

     ;; Rules to get rid of shift ops:
     bvshl-rewrite-with-bvchop-for-constant-shift-amount ;introduces bvcat ; todo: replace with the definition of bvshl?
     bvshr-rewrite-for-constant-shift-amount ; introduces slice
     bvashr-rewrite-for-constant-shift-amount ;new, introduces bvsx
     getbit-of-bvashr-becomes-getbit-of-bvshr
     <-of-constant-and-minus ; helps with getbit-of-bvashr-becomes-getbit-of-bvshr

     bvplus-of-bvuminus-same
     bvplus-of-bvuminus-same-alt
     bvplus-of-bvuminus-same-2
     bvplus-of-bvuminus-same-2-alt

     bvdiv-of-0-arg2
     bvdiv-of-0-arg3 ; unusual case
     bvdiv-of-1-arg3
     bvdiv-same
     sbvdiv-of-0-arg1
     sbvdiv-of-0-arg2 ; unusual casae
     sbvdiv-of-1-arg3
     sbvdiv-same

     bvchop-of-ifix ; more like this?
     slice-tighten-top-axe

     unsigned-byte-p-when-unsigned-byte-p-smaller

     ;; rules to introduce bvequal (these change the flow of proofs like rc4-loop2-auto.lisp):
     ;; equal-becomes-bvequal-axe-1-strong
     ;; equal-becomes-bvequal-axe-2-strong

     ;; rules about bvequal, in case it is being introduced:
     bvequal-same
     bvequal-of-0-arg1
     bvequal-of-bvchop-arg2
     bvequal-of-bvchop-arg3
     bvequal-convert-arg2-to-bv-axe
     bvequal-convert-arg3-to-bv-axe
     bvequal-of-bvplus-and-bvplus-cancel-1+-1+
     bvequal-of-bvplus-arg2-cancel-1
     bvequal-of-bvplus-arg1-cancel-1
     bvequal-trim-arg2-axe-all
     bvequal-trim-arg3-axe-all
     bvequal-of-constant-and-bvplus-of-constant
     bvequal-of-bvplus-of-constant-and-constant
     bvequal-tighten-axe-bind-and-bind
     bvequal-of-constant-and-bvuminus
     bvequal-of-bvuminus-and-constant

     bvif-of-if-becomes-bvif-of-boolif-arg2

     ;; for now, we open these to expose bvcat:
     putbyte
     putbits

     unsigned-byte-p-of-bvmult-of-expt2-constant-version
     unsigned-byte-p-of-bvchop-becomes-bvlt

     ;; These recognize idioms for bvcat (these are probably not fully general;
     ;; need to support bvcats with 0 anywhere and other args with 1s only in
     ;; the 0 region):
     ;; bvor-disjoint-ones-arg1-gen
     ;; bvor-disjoint-ones-arg2-gen
     bvor-of-bvcat-becomes-bvcat-arg2
     bvor-of-bvcat-becomes-bvcat-arg3
     bvxor-of-bvcat-becomes-bvcat-arg2
     bvxor-of-bvcat-becomes-bvcat-arg3
     bvplus-of-bvcat-becomes-bvcat-arg2
     bvplus-of-bvcat-becomes-bvcat-arg3

     ;; this made one of the mavlink dags much longer (too big) but the culprit was the subsequent xor normalization:
     getbit-of-bvif-quoteps ; more like this?  slice bvchop, etc.?  any term with everything constant but the bvif, like (bvcat 8 1 8 (bvif 8 test 5 7))?
     )))

;todo combine this with core-rules-bv
;todo: some of these are not bv rules?
(defun more-rules-bv-misc ()
  (declare (xargs :guard t))
  '(if-becomes-myif ;can ifs ever arise from simulation?  probably? ; todo: move

    bitnot-becomes-bitxor-with-1 ; todo: which way should we go here?

    <-of-bvif-constants-false
    <-of-bvif-constants-true

;    bvxor-all-ones ;do we want this? ;trying without...

    bvminus-becomes-bvplus-of-bvuminus ;trying...

    bvminus-bound-2
    ;; slice-of-logtail

    bound-when-usb2 ;uses the dag assumptions - huh? (expensive?)

    bvplus-disjoint-ones-arg1-gen
    bvplus-disjoint-ones-arg2-gen
    bvplus-disjoint-ones-2-alt
    bvplus-disjoint-ones-2

    bvand-with-small-arg1
    bvand-with-small-arg2

    myif-becomes-bvif-1-axe ; kill special case rules for this?
    myif-becomes-bvif-2-axe
    myif-becomes-bvif-3-axe

;    bvminus-of-bvplus-tighten ;now done by trim rules

    ;;these are the ident rules:
;bvchop-of-bitand
;bvchop-of-bitor
;bvchop-of-bitxor

    ;;outdated trim rules:
    ;;     bitxor-of-bvif-arg2
    ;;     bitxor-of-bvif-arg1

    ;;these must be on if we have rules like bitxor-trim-arg2-dag-all on (those other rules can add a bvchop-0 to trim arithmetic op, and the bvchop-0 turns into a getbit)
    getbit-0-of-bvmult
    getbit-0-of-bvminus   ;better rhs?
    getbit-0-of-bvplus ;think about whether to push the getbits..

    myif-x-x-t-not-nil

    bvcat-equal-rewrite-constant ;seemed to cause problems for aes?

;all-signed-byte-p-of-myif-strong ;slow?
;    make-frame-of-bvif-around-pc
;    myif-nil-becomes-and ;looped

    bvcat-of-bitxor-trim-high-size ;rename
    bvmult-1-becomes-bitand
    bvplus-1-becomes-bitxor
;    bvplus-disjoint-ones-32-24-8 ;trying

    ;; leftrotate32-cases
    leftrotate32alt ;this is what we rewrite to if we want to expand stuff
;    unsigned-byte-p-of-bvminus-gen-better
    bvchop-upper-bound-3-constant-version
    slice-bound-3-constant-version ;bozo make a dag version

    myif-of-getbit-becomes-bvif-arg2
    myif-of-getbit-becomes-bvif-arg1

    myif-of-bvxor-becomes-bvif-arg1
    myif-of-bvxor-becomes-bvif-arg2

    myif-of-myif-test

    ;;well this didn't work, since other instances of g of g (ones which didn't correspond to get-field) got turned into get-fields:
    ;;    get-field-reassemble ;reintroduces get-field (will loop with :definition get-field)
; so we restrict it to the cases in which we break the get-field/set-field abstraction:
;bozo make sure i have the complete set:

    bvif-1-equal-0-y-bitxor-1-x-x
    bvif-1-equal-0-y-x-bitxor-1-x
    bvif-1-equal-1-y-x-bitxor-1-x
    bvif-1-equal-1-y-bitxor-1-x-x

    ;; move to bv-rules?:
    bvif-equal-0-0-1
    bvif-equal-0-0-1-alt
    bvif-equal-1-usb1
    bvif-equal-1-usb1-alt

    bvif-equal-0-usb1

    myif-of-bvif-becomes-bvif-arg2
    myif-of-bvif-becomes-bvif-arg1
    myif-of-bvcat-becomes-bvif-arg1
    myif-of-bvcat-becomes-bvif-arg2
    bvif-of-myif-t-nil

    ;; bitor (what else?  trim args?):

    ;; getbit-of-bvif-too-high ; trying without
;    unsigned-byte-p-of-bvif-gen
    signed-byte-p-of-bvif
;    inst-length-of-myif
;    index-into-program-of-bvif ;or should we enable index-into-program?
    ;; lookup-of-bvif ; drop or move?

    myif-of-constants-becomes-bvif

    ;; myif-when-not-nil ;expensive! replaced 1/12/09

    ;;     BVAND-TRIM-CONSTANT-3
    ;;     BVAND-TRIM-CONSTANT-2

    len-of-getbit-list
    all-unsigned-byte-p-of-getbit-list

    ;; logtail-of-bvchop-becomes-slice ;drop?

    equal-bvcat-0-left ; gen and move
    equal-bvcat-0-right ; gen and move

    bvchop-of-myif-constant-branches
    slice-of-myif-constant-branches
    ; todo: add one for getbit?

    bvcat-bound-hack-2
;                          bvor-1-bound-2

    bvcat-0-<-hack
    repeatbit-equal-0-rewrite-1
    repeatbit-equal-0-rewrite-2

    <-bvchop-31-x-64
    <-bvchop-32-x-64

    bvor-bound-64-hack
    bvcat-bound-hack-1
    natp-of-myif2  ; slow?  limit?
;    BVOR-6--64-HACK2
    <-of-myif-arg1-when-constant ;bad?
;    bvxor-bound-3
;    bvor-bound-3

;    getbit-of-bvxor-too-high ;see identity rule
;   getbit-of-bvor-too-high ;see identity rule
;  getbit-of-bvand-too-high ;see identity rule

;bbbozo
;    getbit-of-bvxor-when-other-bit-is-0-arg2 ;put a limit on these?
;   getbit-of-bvxor-when-other-bit-is-0-arg1
;  getbit-of-bvor-when-other-bit-is-0-arg2
; getbit-of-bvor-when-other-bit-is-0-arg1

    bvchop-of-myif
;;;    unsigned-byte-p-of-bvchop-of-logext-7-32-8 ;bozo
    ;; unSIGNED-BYTE-P-OF-MYIF-strong ;slow?
    ;; BVCHOP-IDENTITY ;trying  - restrict to vars? ;trying without this since we have the dag one - what about vars? other terms?
;newest is without this:    getbit-identity ;restrict to vars? trying.. try without this, since we have the dag version?  or limit?
    unsigned-byte-p-of-bvor2
    unsigned-byte-p-of-bvor3))

(defun update-nth2-rules ()
  (declare (xargs :guard t))
  '(true-listp-of-update-nth2
    consp-of-update-nth2
    len-of-update-nth2
    nth-update-nth2-safe
    update-nth2-of-update-nth2-same
    nth-of-update-nth2-too-high ;new
    ;; update-nth2-of-update-nth2-diff ;bozo this can cause the representation of array writes to blowup!!
    update-nth2-not-nil2
    update-nth2-not-nil1
    bvchop-list-of-update-nth2))

; trying to see if we can use these instead of going to update-nth2
(defun update-nth-rules ()
  (declare (xargs :guard t))
  '(not-equal-of-update-nth-and-nil
    not-equal-of-nil-and-update-nth
    consp-of-update-nth))

;; One goal of this rule-list is to be able to simplify terms involving the
;; special functions that unroll-spec-basic has been instructed NOT to unroll
;; when :rules is :auto.
(defun list-rules ()
  (declare (xargs :guard t))
  '(;; Simple opener rules:
    atom ; opens to expose CONSP
    endp ; opens to expore ATOM (todo: go directly?)

    ;; Rules about cons:
    car-cons
    cdr-cons
    consp-of-cons ;also elsewhere?
    len-of-cons
    true-listp-of-cons
    take-of-cons
    nth-of-cons-constant-version

    ;; Rules about cdr:
    ;; todo: rule for car-of-cdr?
    ;; todo: cdr-of-cdr-becomes-nthcdr
    consp-of-cdr ; introduces len
    len-of-cdr
    true-listp-of-cdr
    ;; todo: rule for take-of-cdr?
    nth-of-cdr

    ;; Rules about take:
    car-of-take-strong
    cdr-of-take
    consp-of-take
    len-of-take
    true-listp-of-take
    take-of-take
    nth-of-take-2-gen ;quite aggressive

    ;; Rules about append:
    car-of-append
    cdr-of-append
    consp-of-append
    len-of-append
    true-listp-of-append
    take-of-append
    nth-of-append ;may be bad if we can't resolve the if test?

    ;; Rules about nthcdr:
    car-of-nthcdr ; introduces nth
    cdr-of-nthcdr ; combines the cdr and the nthcdr
    consp-of-nthcdr
    len-of-nthcdr
    true-listp-of-nthcdr-2
    ;; should we have a take-of-nthcdr rule?  would have to go to subrange?  or move the take inside...
    nth-of-nthcdr

    ;; Rules about update-nth:
    car-of-update-nth
    cdr-of-update-nth
    consp-of-update-nth
    len-update-nth ;pretty aggressive, todo: rename?  but this is built in
    true-listp-of-update-nth-2
    ;; should we have a rule for take-of-update-nth ?
    nth-update-nth-safe

    ;; Rules about firstn (or we can always convert it to take -- todo: try that rule first?):
    car-of-firstn
    ;; todo: cdr-of-firstn?
    consp-of-firstn
    len-of-firstn
    true-listp-of-firstn
    ;; todo: take-of-firstn?
    nth-of-firstn

    ;; Rules about true-list-fix
    car-of-true-list-fix
    cdr-of-true-list-fix
    consp-of-true-list-fix
    len-of-true-list-fix
    true-listp-of-true-list-fix
    take-of-true-list-fix ; more like this, but lower priority?
    nth-of-true-list-fix

    ;; Rules about reverse-list
    car-of-reverse-list
    cdr-of-reverse-list
    consp-of-reverse-list
    len-of-reverse-list
    true-listp-of-reverse-list
    ;; todo: take-of-reverse-list
    nth-of-reverse-list

    ;; Rules about repeat
    car-of-repeat
    cdr-of-repeat
    consp-of-repeat
    len-of-repeat  ;since initializing an array calls repeat
    true-listp-of-repeat
    take-of-repeat-2 ; todo: take-of-repeat
    nth-of-repeat

    ;; mixed rules:

    take-of-0 ;take-when-zp-n
    take-does-nothing ; introduces true-list-fix

    ;; what do we want to do about LISTP (not used very much)?

    nthcdr-of-nil
    repeat-becomes-repeat-tail
    repeat-of-0
    nthcdr-of-cons
    equal-cons-nth-0-self
    equal-of-nthcdr-and-cons-of-nth
    equal-of-cdr-and-cons-of-nth-of-1
    equal-of-nil-and-nthcdr
    cdr-of-cdr-becomes-nthcdr ;these nthcdr rules are new
    nthcdr-of-cdr-combine

    nthcdr-of-1
    nthcdr-of-0
    nthcdr-when-not-posp ;drop?
    firstn-when-zp-cheap

    append-of-cons-arg1

    append-of-nil-arg1
    append-of-nil-arg2

    true-list-fix-when-true-listp

    integerp-of-len
    natp-of-len
    len-non-negative
    nthcdr-of-append-gen
    firstn-of-append ;todo: do we prefer firstn or take?  are rules about both needed?
    firstn-becomes-take-gen ;try this first?
    reverse-list-of-cons

    equal-cons-nil-1
    equal-cons-nil-2
    consp-of-myif-strong

    consp-when-len-equal-constant
    consp-when-len-equal-constant-alt))

;; TODO: Move some of these into list-rules.
(defun list-rules2 ()
  (declare (xargs :guard t))
  (append (list-rules)
          '(finalcdr-iff
            ;;consp-of-finalcdr ;wed sep 22 17:46:19 2010

            cons-equal-rewrite-constant-version ;sun sep  5 05:09:23 2010
            nthcdr-of-nthcdr                    ;sun sep  5 05:01:31 2010
            ;;list::nthcdr-of-len-or-more ;make a cheap version?

            equal-of-subrange-opener ;not in the usual rule set
            cons-nth-0-equal-self
            append-of-firstn-and-subrange

            equal-of-take-and-firstn
            firstn-when-<=-of-len
            ;; nth-of-take-2
            append-of-firstn-and-cons-when-nth
            append-of-firstn-of-cons-of-nth
            cons-nth-onto-subrange-alt
            equal-subrange-nthcdr-rewrite

            ;;firstn-of-cdr-becomes-subrange ; drop?
            append-of-take-and-cons-when-nth ;could be expensive
            append-subrange-subrange-adjacent-alt
            equal-of-append-arg1
            cons-of-nth-and-nth-plus-1
            append-of-take-and-subrange-alt
            equal-of-cons
            cdr-iff
            car-becomes-nth-of-0 ; aggressive, try last?
            nthcdr-iff
            +-combine-constants
            <-of-+-arg2-when-negative-constant
            nth-append-1
            nth-append-2)))

;; These are ACL2 runes, not legal axe rules names.
(defun list-rules2-executable-counterparts ()
  (declare (xargs :guard t))
  '((:executable-counterpart zp)
    (:executable-counterpart min)
    (:executable-counterpart max)
    (:executable-counterpart <)
    (:executable-counterpart len)
    (:executable-counterpart binary-+)
    (:executable-counterpart nfix)
    (:executable-counterpart natp)))

;; uses in the JVM for arraycopy
(defun subrange-rules ()
  (declare (xargs :guard t))
  '(subrange-of-0
    subrange-not-nil1
    subrange-not-nil2
    len-of-subrange
    true-listp-of-subrange
    nth-of-subrange
    subrange-out-of-order
    subrange-of-cdr))

(defun update-subrange-rules ()
  (declare (xargs :guard t))
  '(len-of-update-subrange ;drop?
    update-subrange-not-nil1
    update-subrange-not-nil2
    update-subrange-of-true-list-fix
    update-subrange-all
    nth-of-update-subrange-diff-1 ;reorder hyps
    nth-of-update-subrange-diff-2
    nth-of-update-subrange-same))

(defun list-rules3 ()
  (declare (xargs :guard t))
  (append
   (subrange-rules)
   (update-subrange-rules)
  '(;; rules about update-subrange2 (used in the JVM for arraycopy):
    equal-of-nil-and-update-subrange2 ;new
    len-of-update-subrange2
    update-subrange2-all ;used, for example, when we initialize an array to 0's (using repeat) and then copy another array into it
    bv-array-read-of-update-subrange2
    true-listp-of-update-subrange2
    all-unsigned-byte-p-of-update-subrange2 ;where should this go?
    nth-of-update-subrange2

    union-equal-of-nil-arg1
    union-equal-of-nil-arg2

    all-equal$-of-cons
    all-equal$-of-append)))

(defun alist-rules ()
  (declare (xargs :guard t))
  '(strip-cdrs-of-cons
    strip-cdrs-of-append
    strip-cars-of-cons
    strip-cars-of-append))

;rename to bv-list-rules?
(defun core-rules-non-bv ()
  (declare (xargs :guard t))
  '(all-unsigned-byte-p-of-update-nth
    ;; bvchop-8-bvnth-8 ;gen
    ;; bvchop-of-logtail-becomes-slice
    ;; getbit-of-bvnth-when-getbit-is-always-0
    ;; getbit-of-bvnth-when-getbit-is-always-1
    ;; bvnth-of-bvchop
    ;; bvnth-of-bvcat-8-case
    ;; bvnth-when-data-isnt-an-all-unsigned-byte-p
    ))

(defun bvif-rules ()
  (declare (xargs :guard t))
  '(bvif-same-branches
    bvif-equal-1-usb1
    bvif-when-true
    bvif-when-false
    bvif-of-bool-fix
    equal-of-bvif-same-1
    equal-of-bvif-same-2))

(defun bvchop-list-rules ()
  (declare (xargs :guard t))
  '(consp-of-bvchop-list
    len-of-bvchop-list
    equal-of-bvchop-list-and-nil
    equal-of-nil-and-bvchop-list
    true-listp-of-bvchop-list
    all-unsigned-byte-p-of-bvchop-list-gen
    bvchop-list-of-nil
    bvchop-list-of-cons
    bvchop-list-does-nothing ; rename
    bvchop-list-does-nothing-rewrite-alt ;rename
    bvchop-list-does-nothing-rewrite ;rename
    bvchop-list-of-bvchop-list))

(defun bv-of-logext-rules ()
  (declare (xargs :guard t))
  '(bvplus-of-logext-arg2
    bvplus-of-logext-arg3

    bvminus-of-logext-arg2
    bvminus-of-logext-arg3

    bvmult-of-logext-arg2
    bvmult-of-logext-arg3

    bvuminus-of-logext

    bvand-of-logext-arg2
    bvand-of-logext-arg3
    bvor-of-logext-arg2
    bvor-of-logext-arg3
    bvxor-of-logext-arg2
    bvxor-of-logext-arg3

    bitand-of-logext-arg1
    bitand-of-logext-arg2
    bitor-of-logext-arg1
    bitor-of-logext-arg2
    bitxor-of-logext-arg1
    bitxor-of-logext-arg2

    bvif-of-logext-arg3
    bvif-of-logext-arg4

;    bvcat-of-logext-high-eric ;trying without this one
    slice-of-logext

    bvcat-of-logext-high
    bvchop-of-logext

    getbit-of-logext
    getbit-of-logext-high

    bvshr-of-logext-arg2
    bvshl-of-logext-arg2
    bvshr-of-logext-arg2
    bvshl-of-logext-arg2
    bvchop-of-logext-becomes-bvsx

    high-slice-of-logext ;introduces bvsx

    bv-array-read-of-logext-arg3))

(defun logext-rules ()
  (declare (xargs :guard t))
  (append
   (bv-of-logext-rules)
  '(logext-of-0

    logext-equal-0-rewrite-32 ;bozo gen

    ;;bvchop-32-logext-8 ;bozo
    logext-64-bound-hack-8 ;bozo
    logext-64-bound-hack ;bozo
    logext-bound-when-unsigned-byte-p
    logext-negative
    <-of-0-and-logext
    <-of-logext-when-signed-byte-p
    <-of-logext-when-signed-byte-p-alt
    ;;replace these with a trim rule:
    equal-of-logext-and-logext
    logext-of-logext

    logext-not-nil1
    logext-not-nil2)))

;; ;these are now all/mostly related to 2d arrays?
;; (defconst *misc-rules*
;;   '(
;;     ;; SLICE-OF-BVCAT-HACK-GEN-BETTER

;; ;    get-rid-of-logtail ;bbozo drop me! we need a more systematic way to get rid of logtail? or does it not appear?

;;     subrange-rewrite ;fixme rename subrange-unroll? or -opener?
;; ;    get-column-of-cons
;;     ;; cols-to-array
;;     ;; cols-to-array-aux
;;     ;; cols-to-row-of-cons2
;;     ;; cols-to-row-of-nil
;;     ;array-elem-2d

;; ;;;   slice-7-0-bvnth
;; ;;;   slice-15-8-bvnth
;; ;;;  slice-23-16-bvnth
;; ;;; slice-31-24-bvnth
;;     ))

;; (defun basic-rules2 (state)
;;   (declare (xargs :mode :program
;;                   :stobjs state))
;;   (append (core-rules2 state)
;;           (logext-rules2 state)
;;           (misc-rules2 state) ;fixme yuck
;;           ))

(defun bv-array-rules-simple ()
  (declare (xargs :guard t))
  '(bv-array-read-of-bv-array-write-same ;bv-array-read-of-bv-array-write-same-work-hard
    bv-array-read-of-bv-array-write-diff-safe-gen ;added the -gen ;thu mar 25 04:05:19 2010
    BV-ARRAY-WRITE-OF-BVCHOP-ARG3
    BV-ARRAY-WRITE-OF-BVCHOP-ARG4
    ))

(defun bv-array-rules ()
  (declare (xargs :guard t))
  (append
   (bv-array-rules-simple)
   '(bv-array-write-of-bvxor             ;use a trim rule?
     len-of-bv-array-write
     all-unsigned-byte-p-of-bv-array-write
     true-listp-of-bv-array-write
;bitxor-of-bv-array-read-and-bv-array-read-constant-arrays-alt
;bitxor-of-bv-array-read-and-bv-array-read-constant-arrays
     bvxor-list-base  ;move
     bvxor-list-unroll ;move
     bv-array-read-of-0-arg1
     bv-array-read-of-bv-array-write-too-narrow-cheap ;new
     bv-array-read-of-append-arrays
     bv-array-clear-1-0
     bv-array-clear-of-bv-array-clear-same
     consp-of-bv-array-write ;moved here
     equal-of-bv-array-write-of-1-constant-version

     bv-array-read-trim-index-axe

     bv-array-read-of-bvchop
     bv-array-read-of-logext-64-32 ;bozo
     bv-array-read-of-cons-base
     bv-array-read-of-cons
     ;; bv-array-read-of-myif ;bozo seems expensive!  restrict to cases when it will help? seemed necessary for proving that array accesses are in bounds
     bv-array-read-of-subrange-better ;added -better fri dec 24 17:14:55 2010
     bv-array-read-of-upddate-subrange-128
     bv-array-write-of-bv-array-write-tighten

     bv-array-read-shorten-data ;expensive?  needed for triple-des? add a cheaper version?
     bv-array-read-of-bv-array-write-shorten ;this is need since bv-array-read-shorten-data has been restricted to constant data (why does the lsh of this rule arise?)
     bv-array-read-of-bv-array-write-tighten-better
     bv-array-read-of-getbit-list
     bv-array-read-numeric-bound
     bv-array-read-non-negative
     bv-array-read-when-data-isnt-an-all-unsigned-byte-p ; requires the evaluator to know about bvchop-list
     bv-array-write-when-data-isnt-an-all-unsigned-byte-p ; requires the evaluator to know about bvchop-list
     getbit-of-bv-array-read-too-high ; drop?
     ;;getbit-of-bv-array-read-gen ; just blast the array read?
     equal-of-bvchop-of-nth-and-bv-array-read
     equal-of-bvchop-of-nth-and-bv-array-read-alt
     equal-of-nth-and-bv-array-read
     equal-of-nth-and-bv-array-read-alt
     bv-array-read-trim-element-size ;might this be expensive?
     bv-array-read-of-getbit-when-len-is-2
;    nth-of-bv-array-write-becomes-bv-array-read ;for some reason an nth appears in aeslight? why? ;trying without this
     bv-array-write-of-bvchop-list-tighten
     bv-array-read-of-bvchop-list-tighten

     firstn-of-bv-array-write
     bv-array-read-of-bvchop-list
     cons-of-bv-array-write
;    cons-becomes-bv-array-write-gen ;bozo, don't do this right away... ;removed, since now the jvm model has bv-array-write already
     cons-of-bv-array-write-gen

     ;; myif-of-bv-array-write-arg1-safe
     ;; myif-of-bv-array-write-arg2-safe
     bv-array-read-of-bv-array-write-tighten2
     myif-of-bv-array-read-becomes-bvif-arg1
     myif-of-bv-array-read-becomes-bvif-arg2
     bv-array-read-of-myif ;slows things down a lot... go to bvif..
     equal-of-bvchop-of-car-and-bv-array-read
     equal-of-bvchop-of-nth-and-bv-array-read-strong
     equal-of-bvchop-of-nth-and-bv-array-read-alt-strong
     nthcdr-of-bv-array-write
     take-of-bv-array-write-better ;fri jan 15 21:26:25 2010
     all-unsigned-byte-p-of-bv-array-write-gen-2
;    all-signed-byte-p-of-bv-array-write ;yuck?
     myif-of-bv-array-write-arg1-safe
     myif-of-bv-array-write-arg2-safe
     bv-array-write-trim-value-all ;not a bv rule? ; todo: move to trim rules?

;only do this when we can tell syntactically that the write does nothing?
;    bv-array-write-does-nothing ;caused problems for des-encrypt-sun - why? actually it seemed to help for that! ;bbozo think about how to make this cheap enough...
     bv-array-write-does-nothing-cheap
     bv-array-write-of-bvcat-reduce
     bv-array-write-of-bv-array-write-diff-constant-indices ;faster when the sizes are the same
     bv-array-write-of-bv-array-write-diff-constant-indices-gen ;added the gen sun jan  9 19:19:17 2011
     bv-array-write-of-bv-array-write-same-index
     getbit-list-of-bv-array-write
     ;; bv-array-write-tighten-when-quotep-data ;trying without this, since it led to a size mismatch between nested bv-array-writes
     ;; nth2-of-bv-array-write
     ;; ;is this stuff only used to get rid of logext-list?
     ;; push-bvchop-list-of-bv-array-write
     ;; push-bvchop-list-of-push-bvchop-list
     ;; push-bvchop-list-of-myif ;could this be really expensive? maybe memoization helps?
     ;; push-bvchop-list-of-logext-list

     all-integerp-of-bv-array-write

     bv-array-write-of-bv-array-write-tighten2
     bv-array-write-of-bvif-tighten

     equal-of-nil-and-bv-array-write
     equal-of-bv-array-write-and-nil)))

(defun bit-blast-rules-basic ()
  (declare (xargs :guard t))
  '(bvor-blast
    bvxor-blast
    bvand-blast
    bvcat-blast-high
    bvnot-blast
;    bvcat-blast-low ;first fix the issue with the low val being too narrow
    bvchop-blast ;maybe we shouldn't blast this?
    slice-blast
    bvif-blast
    bv-array-read-blast ;new! ;i'm not sure i like this?!
    leftrotate ; exposes bvcat
    ;;leftrotate32 ;todo: try
    ))

;bozo blast the arithmetic functions in a second pass?
(defun bit-blast-rules ()
  (declare (xargs :guard t))
  (append (bit-blast-rules-basic)
          '(blast-bvmult-into-bvplus-constant-version-arg1 ;
            blast-bvmult-into-bvplus-constant-version-arg2 ;
            bvplus-becomes-ripple-carry-adder
            ripple-carry-adder-recursive
            ripple-carry-adder-base
            full-adder-sum
            full-adder-carry)))

;fixme do i ever see logtail?
(defun more-rules-yuck ()
  (declare (xargs :guard t))
  '(
;    bvand-logtail-arg1 ;trying without these (logtail now never appears?) Thu Mar  3 01:55:15 2011
;    bvand-logtail-arg2
;    bvor-logtail-arg1
;    bvor-logtail-arg2
;    bvxor-logtail-arg1
;    bvxor-logtail-arg2
    ;; logtail-of-bvcat-when-extends-into-upper
    ;; logtail-of-bvcat-low
    ;; logtail-of-bvxor
    ;; logtail-of-bvor
    ;; logtail-of-bvand

;    BV-ARRAY-READ-OF-MYIF-DROP-LOGEXT-LISTS-ARG1
;    BV-ARRAY-READ-OF-MYIF-DROP-LOGEXT-LISTS-ARG2
;    bv-array-write-of-myif-drop-logext-lists-arg1
;    bv-array-write-of-myif-drop-logext-lists-arg2
    ;; push-bvchop-list-of-bv-array-write
    ;; push-bvchop-list-of-push-bvchop-list
    ;; push-bvchop-list-of-myif ;could this be really expensive? maybe memoization helps?
    ;; push-bvchop-list-of-logext-list

;    getbit-list-of-logext-list

;    myif-of-logext-list-arg2
;    myif-of-logext-list-arg1

    signed-byte-p-of-myif
    ;;all-signed-byte-p-of-myif
    ;;all-signed-byte-p-of-nil
    ;;all-signed-byte-p-of-cons
;    all-signed-byte-p-of-logext-list

;    logext-list-of-logext-list

    ;; bvchop-of-bvnth
    ))


(defun list-to-bv-array-rules ()
  (declare (xargs :guard t))
  '(list-to-bv-array
    list-to-bv-array-aux-base
    list-to-bv-array-aux-unroll
    list-to-byte-array ; wrapper for list-to-bv-array
    ))

(defun byte-array-to-bit-array-rules ()
  (declare (xargs :guard t))
  '(byte-array-to-bit-array
    byte-array-to-bit-array-aux-base
    byte-array-to-bit-array-aux-opener))

;rename
(defun yet-more-rules-non-jvm ()
  (declare (xargs :guard t))
  '(true-listp-of-myif

    integerp-of-myif

    all-unsigned-byte-p-of-cons
    unsigned-byte-p-of-myif ;can be expensive?!
    ;;myif-of-constant-lists ;trying without mon jul  5 21:14:49 2010
    len-of-myif

;    logext-list-does-nothing
    ;;all-signed-byte-p-when-all-unsigned-byte-p
;these help us resolve questions about symbolic indices (e.g., for bvshl and bvshr)
    <-of-+-cancel-1-1+ ; <-of-sums-cancel
    <-of-constant-and-minus ; <-0-minus
    binary-+-bring-constant-forward
    ;subrange-out-of-order-cheap
    ))

(defun array-reduction-rules ()
  (declare (xargs :guard t))
  '(; todo: are these slow??  make axe versions of more of these?
    array-reduction-when-top-bit-is-xored-in ;; at least one of these seems needed for aes-128-decrypt
    array-reduction-when-top-bit-is-irrelevant  ;; at least one of these seems needed for aes-128-decrypt
    array-reduction-0-1
    array-reduction-1-0
    bv-array-read-when-all-same-axe
    bv-array-read-of-bvmult-discard-vals
    bv-array-read-of-bvplus-of-bvmult-discard-vals
    bv-array-read-of-+-of-constant-shorten ; for an index that is a +
    bv-array-read-of-bvplus-of-constant-no-wrap ; for an index that is a bvplus
    ))

(defun bvplus-rules ()
  (declare (xargs :guard t))
  '(;; bvplus rules (can be expensive, perhaps try just bvplus-commutative-axe):
    bvplus-commutative-axe
    bvplus-commutative-2-axe ;seemed to fire a lot?! in rc4 example
    bvplus-associative))

; despite the name, this also includes bv-array-rules and list rules!
;; TODO: Remove non-bv stuff from this:
;; TODO: Consider removing the trim-rules from this, as they can cause blowup and perhaps also obscure rotate patterns
(defun amazing-rules-bv ()
  (declare (xargs :guard t))
  (append (bvplus-rules) ; todo: maybe drop, as these are bad for md5, for example
          ;; todo: a lot of cruft in here:
          '(;bvand-of-constant-tighten-axe ; warning: can change the size of the bvand

            max-constants-lemma ;bozo more like this?
            myif-not-myif-same  ;bozo more like this?


            bvuminus-1 ; introduces getbit
            bvuminus-of-bvplus

            bvand-commutative-axe
;    bvxor-smaller-term-becomes-cat-arg1 ;yuck? Sat Jan 22 01:06:43 2011
;   bvxor-smaller-term-becomes-cat-arg2 ;yuck? Sat Jan 22 01:06:45 2011

            ;; logtail-becomes-slice-bind-free-axe       ;drop?

            bvmult-of-2-gen
;trying these:
            bitand-commutative-axe

            bvnot-1-becomes-bitnot-better
            getbit-of-bvnot          ;bozo add a getbit trim -all rule instead
            getbit-of-bvplus         ;use trim?

;for specs:
            ;; nth2-becomes-bvnth-for-natps-dag

            myif-of-myif-x-x-t
            myif-myif-myif-1
            myif-myif-myif-2

            bvif-tighten
            bvif-test-test2-test
            bvif-test-test2-test-alt
            bvif-test-test2-test-alt2
            bvif-test-test2-test-alt3

            bvif-same-tests2
            bvif-same-tests

            bvcat-tighten-upper-size-axe
            ;; bvif-with-small-arg1
            ;; bvif-with-small-arg2
            bvor-with-small-arg1
            bvor-with-small-arg2

            getbit-of-bvxor ; perhaps move to bv-rules-core

            myif-equal-nil-rewrite
            myif-becomes-boolif-t-arg1
            myif-becomes-boolif-t-arg2
            myif-becomes-boolif-nil-arg1
            myif-becomes-boolif-nil-arg2
;    myif-boolif
            <-of-myif-arg2 ;fffixme bad?
            myif-lemma     ;rename

            boolif-boolif-lift-same
            myif-myif-lift-same
            myif-equal-lemma ; move? ;rename ;make alt versions

            my-right-cancellation-for-+

            bvcat-trim-high-size-when-constant-1
            )
          (boolean-rules)
          (base-rules)
          (bv-array-rules) ;todo: drop?
          (type-rules)
          (core-rules-bv)
          (core-rules-non-bv) ; todo: remove these?
          (bvif-rules)
          (unsigned-byte-p-rules)
          ;; probably more stuff needs to be added to this??  list stuff from more-rules / more-rules-yuck / jvm-rules-jvm?
          ;; (logext-rules)
          (trim-rules) ; remove?
          ;(trim-helper-rules)      ;many dups here with the above...
          (list-to-bv-array-rules) ;move to parents?
          ;;(yet-more-rules-jvm) ;TTODO: Drop this.  It includes JVM rules..  dropping this broke des-encrypt
          (yet-more-rules-non-jvm) ; not bv rules?
          (array-reduction-rules)
          (more-rules-bv-misc)))

;; ;rules to simplify applications of dag-val2-no-array (when rewriting a term with an embedded dag)
;; ;currently there seem to be lots of crashes when doing this, due to guard violations in eval-fn
;; ;rules that support eval-dag (may crash without these - unresolved ifs lead to bad calls)
;; (defun dag-val-rules ()
;;   (declare (xargs :guard t))
;;   (append (lookup-rules)
;;           '(DAG-VAL-WITH-AXE-EVALUATOR
;;             dag-val2-no-array
;;             ASSOC-EQ-BECOMES-ASSOC-EQUAL ;same for assoc?
;;             assoc-equal-of-acons-diff
;;             assoc-equal-of-acons-same

;;             get-arg-vals-no-array-base
;;             get-arg-vals-no-array-opener
;;             EVAL-DAG-WITH-AXE-EVALUATOR-BASE
;;             EVAL-DAG-WITH-AXE-EVALUATOR-opener
;;             eval-dag2-no-array-opener
;;             eval-dag2-no-array-base
;; ;fixme - gross to still use eval-fn?
;;             eval-fn
;;             eval-fn-unary
;;             eval-fn-binary
;;             eval-fn-ternary
;;             eval-fn-quaternary-rewrite
;;             eval-fn-5ary-rewrite
;;             eval-fn-6ary
;;             eq
;;             top-nodenum
;;             quotep
;;             atom ;this doesn't really save us from the crash when instantiating the body

;;             fix)))

;;normalize boolif nests that are really ands?

;; TODO: add many more rules to this?
(defun arithmetic-rules ()
  (declare (xargs :guard t))
  '(fold-consts-in-+
    unicity-of-0
    acl2-numberp-of-+
    integerp-of-+
    ))

;still need these for the aes spec
;but they get in the way by applying to locals in jvm
(defun introduce-bv-array-rules ()
  (declare (xargs :guard t))
  '(nth-becomes-bv-array-read
    ;; bvnth-becomes-bv-array-read
    nth-of-bv-array-write-becomes-bv-array-read
    ;cons-becomes-bv-array-write-gen
    ))

;; ;bozo think about the order in which these should fire
;; (defun bitxor-rules ()
;;   (declare (xargs :guard t))
;;   '(bitxor-associative
;;     bitxor-combine-constants
;;     bitxor-same-2 ;add bitxor-same?
;;     bitxor-commutative-2-axe
;;     bitxor-commutative-axe))

;used for sha1 and md5?: ;fixme deprecate?
;also called by axe-rules.
(defun miter-rules ()
  (declare (xargs :guard t))
  '(bvlt-of-bvmult-of-expt-arg2-constant-version
    bvlt-of-bvmult-of-expt-arg3-constant-version
    nthcdr-of-cons ;drop?
    equal-of-nil-and-group
    bvlt-of-bvcat-arg3
    slice-of-bvmult-of-expt-gen-constant-version
;ceiling-in-terms-of-floor2 ;introduces ;make a bvceil operator? ;removed in favor of the 3 rule?
    ceiling-in-terms-of-floor3
    floor-of-expt2-becomes-slice-when-bv-axe
    *-becomes-bvmult-8
    ceiling-of-*-same
    <-of-*-of-constant-and-*-of-constant
    group-of-true-list-fix
    len-of-true-list-fix
    <-of-floor-and-0
    <-of-*-and-0

    bvplus-when-equal-of-constant-and-bvchop-arg2
    bvplus-when-equal-of-constant-and-bvchop-arg3
;    bvplus-when-bvchop-known-subst
;   bvplus-when-bvchop-known-subst-alt

    bvchop-impossible-value ;gen to any bv?
    <-becomes-bvlt-dag-GEN-BETTER
;    <-becomes-bvlt-axe-bind-free-arg1 ;Wed Feb 24 15:00:14 2010

    zp
    booleanp-of-all-same
    booleanp-of-all-equal$
    equal-of-constant-and-repeat
    equal-of-bvmult-and-expt-of-2-constant-version
    slice-of-times-of-expt-constant-version
    bvplus-of-*-arg2
    bvuminus-of-+
    bvplus-of-unary-minus
    bvchop-of-+-becomes-bvplus
    ;move these to type-rules:
    integerp-of-*
    acl2-numberp-of-+
    acl2-numberp-of-*
    acl2-numberp-of-unary--
    fix
    integerp-of-+-when-integerp-1-cheap
    mod-becomes-bvchop-when-power-of-2p
    bvlt-of-bvmult-6-5-20 ;which one of these helps?
    bvlt-of-bvmult-6-5-20-alt
    bvlt-trim-arg1-axe-all
    bvlt-trim-arg2-axe-all
    equal-of-bvplus-constant-and-constant
    equal-of-bvplus-constant-and-constant-alt
    bvlt-of-bvplus-of-bvcat-of-slice-sha1
    bvlt-of-bvif-same-1
    unsigned-byte-p-of-bvplus-of-1-sha1 ;would it fire with a free var for the 31?
    equal-of-bvplus-and-bvplus-hack-sha1
    equal-of-slice-and-slice-of-bvplus-of-1
    bvplus-of-bvuminus-of-bvmult-of-slice-same
    not-bvlt-self ;drop
    bvlt-of-bvcat-arg3-bvmult-version
    bvdiv-31-4

    bvlt-when-bound-axe
    ;; bvlt-add-to-both-sides-constant-lemma-no-split ;Wed Feb 24 14:15:59 2010
;    not-bvlt-of-max-arg2          ;alt version?
    ;bvlt-of-bvchop-arg3-same  ;gen and move? or drop?
    bvmod-of-power-of-2
    unsigned-byte-p-of-bvmod-gen ;remove since added to big list
;    slice-of-bvmult-of-expt
    equal-of-constant-and-bv-array-read-of-bv-array-write-of-constant ;todo: gen or drop
    unsigned-byte-p-of-bvplus-when-both-smaller
    bvmod-31-4 ;drop?
    bvchop-of-bvmod
    bvmod-of-bvmult-of-expt-constant-version
    unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger-alt
    bvlt-of-bvplus-of-bvuminus-and-bvmult-of-bvdiv-sha1
    bvlt-of-bvmult-of-bvdiv
    bound-theorem-for-sha1-hack
    getbit-of-bvplus-of-1-32
    equal-of-bv-array-write-same
    equal-of-bvcat-and-bvmult-32-3
    equal-of-bvcat-and-bvmult-32-3-alt
    boolor-of-not-equal-and-not-bvlt-5-31-13
    unsigned-byte-p-of-*-of-expt-constant-version
    turn-equal-around-axe4
    equal-of-nil-when-booleanp
    bvlt-tighten-bind-and-bind-dag

    myif-lemma-arg2
    equal-of-bvmult-and-*
    equal-of-bvmult-and-*-alt
    bvplus-when-<=-15-hack-for-sha1 ;bad?!
    bvlt-of-bvplus-31-14-5-1

    nfix-does-nothing
    natp-of-len ;add to some rule list
    integerp-of-len
    bvchop-of-*-becomes-bvmult
    unsigned-byte-p-of-bvplus-of-bvuminus-one-bigger
;    sha1-loop-10-theorem-1
    equal-of-constant-and-bitxor-1
    unsigned-byte-p-when-unsigned-byte-p-smaller
    car-becomes-nth-of-0
    nth-of-cdr
    bvchop-does-nothing-rewrite))

;; These get added to axe-rules
(defun axe-prover-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   '(equal-of-firstn-same ;tue dec  7 01:51:27 2010
     equal-of-bv-array-read-and-bv-array-read-leibniz
     bvplus-of-bvcat-fits-in-low-bits-negative-constant
;     bvplus-of-bvcat-4294967292-4
 ;    bvplus-of-bvcat-4294967293-4
  ;   bvplus-of-bvcat-4294967294-4
   ;  bvplus-of-bvcat-4294967295-4

     cdr-of-bv-array-write-better-work-hard ;Fri Aug 27 18:41:44 2010

     nth-of-cons ;might be expensive, but i saw failures with the nth of cons pattern (led to lots of cases - do it only as a last resort?)

;     hard-error ;why? ;Sat Mar 27 05:52:33 2010
;     assoc-eq-becomes-assoc-equal

     lookup-equal ;why?
     assoc-equal-of-acons-same
     assoc-equal-of-acons-diff
;                               CONSP-OF-GET-ARG-VALS-NO-ARRAY
;                              cdr-of-get-arg-vals-no-array
     ;; make-alist-base
     ;; make-alist-opener
     true-listp-of-myif-strong
     unsigned-byte-p-of-myif
     equal-of-t-when-booleanp-arg2 ; todo: drop

     booland-of-myif-arg1
;nth-of-myif ;ffixme this may be slowing down the prover since it fires repeatedly (on a context node) but is not used in the rewriter

;equal-of-myif-arg2 ;trying without this..
     plus-of-bvplus-of-minus1
     boolif-of-myif-arg2
     boolif-of-myif-arg3

     ;;           not-of-booland ;trying without this? new4

     not-sbvlt-from-bound-better
;     SBVLT-BECOMES-BVLT ;Sun Mar 28 16:56:24 2010
     not-sbvlt-of-0-when-sbvlt-free
;                        SBVLT-REWRITE ;trying without this..

;                        GETBIT-OF-BVPLUS-SPLIT ;bad?
     ;equal-of-bvif-hack
     ;equal-of-bvif-hack2
     bvchop-equal-when-bvlt-hack
     bvchop-equal-when-bvlt-hack-32
;     bvplus-trim-constant-arg1
     sbvdivdown-rewrite-gen

;    unsigned-byte-p-tighten ;;removed tue jan 12 06:27:23 2010
     bvif-of-1-and-0-becomes-bool-to-bit ; not sure it's a good idea to introduce bool-to-bit since the STP translation doesn't know about it.
     equal-of-bool-to-bit-and-0
     equal-of-bool-to-bit-and-1
     ;;fixme what about backchain-limit? <- for which rule??

     equal-of-bvchop-impossible
     ;;equal-of-bvchop-impossible-alt

;bvlt-transitive-free2
     bvlt-transitive-free2-back
     unsigned-byte-p-of-plus-of-minus-1

     bvif-t-x-and-bitxor-1-x
     bvif-t-bitxor-1-x-and-x
     ;;    bitxor-associative ;caused problems removing 1/12/09
     equal-of-bvuminus-and-constant ; move
     getbit-0-of-bool-to-bit
     logext-when-top-bit-0 ;move?
     <-becomes-bvlt-dag
     sbvdiv-when-both-positive
     ; move these?  add abvdiv-trim
     bvdiv-trim-arg1-axe ;don't need this if we have the -all rule?
     bvdiv-trim-arg2-axe ;don't need this if we have the -all rule?
     bvdiv-trim-arg1-axe-all
     bvdiv-trim-arg2-axe-all

     bvdiv-of-bvplus-minus-5
     bvchop-of-bvdiv
     bvdiv-equal-0-rewrite-alt
     bvdiv-equal-0-rewrite
     zp-when-unsigned-byte-p
     bvlt-add-to-both-sides-constant-lemma-no-split2

;without this, substitution can lead to loops?
     nthcdr-of-take-same
     take-of-bvplus-32-1

;     ALL-UNSIGNED-BYTE-P-OF-TAKE ;Fri Dec 17 01:55:59 2010
     len-of-nthcdr
     <-of-myif-arg1                                    ;bad?
     <-of-myif-arg2                                        ;bad?
     cancel-from-<-of-+
     <-+-negative-0-1

     car-when-equal-nthcdr
     true-listp-subst-rule
     list-equiv
     take-of-1
     cdr-of-bv-array-write-better
     +-of-bvplus-1-same-and-unary-minus
     inverse-of-+
     bvlt-of-bvplus-of-1-and-same
     ;; <-becomes-bvlt-axe-bind-free-arg1 ;wed feb 24 15:00:17 2010
     ;len-when-equal-take
     car-of-nthcdr
     consp-of-nthcdr
     equal-cons-cases2 ;hope this is ok
     boolor-of-booland-same
     boolor-of-booland-same-alt
     bv-array-clear-of-bv-array-write-same
     bvif-0-1
     getbit-of-bvuminus
     bvlt-tighten-gen2
     ;;bvplus-of-1-tighten
     bvplus-of-1-tighten-no-split
     equal-of-bvplus-and-bvplus-hack
     nthcdr-of-bvplus-1
     +-of-minus-1-and-bv2
     +-of-minus-1-and-bv
     equal-of-bvplus-and-bvplus-cancel-arg3-and-arg3 ; todo: move to core-rules-bv
     equal-of-minval-and-bvplus-of-bvminus
     equal-of-minval-and-bvplus-of-bvminus-alt

     unsigned-byte-p-of-bvplus-minus-1
     equal-of-bvplus-and-bvplus-cancel-arg2-and-arg3 ; todo: move to core-rules-bv
     unsigned-byte-p-of-bvplus-1

     ;;CONSP-FROM-LEN ;new ;loops with LIST::LEN-OF-NON-CONSP
     consp-when-len-equal-constant
     add-to-end
     car-of-bv-array-write
;     bvlt-tighten-free-alt ;problems? ;Tue Aug 31 19:45:37 2010
;     bvlt-tighten-free ;problems? ;Tue Aug 31 19:45:37 2010
     bvplus-tighten-arg2
     plus-becomes-bvplus-free
     bvmod-by-8

     bvplus-10-shrink-to-9

     ;; bvlt-add-to-both-sides-constant-lemma-no-split ;Wed Feb 24 14:16:05 2010
     <-becomes-bvlt-alt-weak
     assoc-equal-of-cons
     bvplus-commutative-axe
     bvplus-commutative-2-axe

     all-unsigned-byte-p-of-cdr
     true-listp-of-cdr
     len-of-cdr
     ;fix-of-len ;is fix enabled in axe-rules though?
     fix-when-acl2-numberp
     acl2-numberp-of-len
;     equal-of-myif-same
     ;;<-becomes-bvlt-alt
     <-becomes-bvlt-axe-bind-free-and-bind-free
     not-equal-when-bvlt
     not-equal-when-bvlt-alt
     bvplus-of-bvuminus-tighten-gen-no-split-dag
     ;;turn-equal-around-axe3 ;this seemed to loop with the ...4 version
     unsigned-byte-p-of-bvplus-wider-9-10
     bvlt-add-to-both-sides-constant-lemma-alt-no-split
     bvlt-add-to-both-sides-constant-lemma-alt ;new
;     not-bvlt-of-max-arg2
;                        bvlt-of-max-when-bvlt

     ;;trying without these:
     ;;bvuminus-when-smaller-bind-free-dag ;this may be a bad idea
;bvplus-of-bvuminus-tighten2
;bvplus-of-bvuminus-tighten2-alt

;and with this instead:
     bvplus-of-bvuminus-expand
     bvplus-of-bvplus-narrower-when-no-carry ;might this loop?
;     bvplus-of-bvplus-narrower-quoteps ;sun mar 28 18:47:07 2010
;equal-of-bvif ;too strong? trying without
     bvlt-when-bvlt-must-be-fake-free
     sbvlt-of-0-when-shorter
     bvle-to-bvlt
     bvplus-of-bvuminus-same-gen
;    bvlt-of-bvplus-1-when-not-bvlt ;tue jan 12 06:49:37 2010
     bvplus-of-bvuminus-tighten-10-to-9
     ;bvlt-of-511

     bvchop-when-top-bit-not-1-fake-free
     turn-equal-around-axe4 ;this subsumes the other rules?
     bvlt-of-bvplus-32-31-trim-alt ;gen (but only when "trimmable"?)
     bvlt-of-bvplus-32-31-trim  ;gen (but only when "trimmable"?)

;sbvlt-becomes-bvlt
;     sbvlt-becomes-bvlt-better
     bv-array-write-of-0
     ;bvplus-of-+

     bvlt-when-unsigned-byte-p-better-helper
;;     recollapse-hack ;sun mar 28 15:19:01 2010
     bvlt-when-bit-2-1-hack
     bvlt-of-4-hack

;                        not-equal-of-constant-when-bvlt-constant-1-alt
;                       not-equal-of-constant-when-bvlt-constant-2-alt

     bvplus-minus-13-tighten-32
     bvlt-of-bvmult5-4-13
     bvlt-of-bvuminus-3-3-4
     bvlt-of-slice-top-gen-no-split
     equal-slice-0-when-bvlt
;                        bvplus-of-bvplus-constants-size-differs-better-no-split-case2
     bvplus-minus-3-tighten-32
;     bvplus-minus-4-tighten-32 ;wed apr  7 19:47:05 2010 was part of a loop?
;     bvplus-minus-4-tighten-32-gen ;wed apr  7 19:47:05 2010
     plus-of-minus-3-bv-5
     sbvmoddown-32-4-non-neg ;gen

     sbvrem-when-positive
     sbvrem-of-bvchop-arg2
     sbvrem-of-bvchop-arg3
     sbvrem-rewrite

     sbvdiv-when-y-negative
;sbvdiv-when-x-negative
     bvdiv-of-4
     recollapse-hack-slice-version

     equal-0-top-slice-5-4-2
     unsigned-byte-p-of-bvplus-smaller
;bvlt-of-bvuminus-and-constant-no-split
     ;;    unsigned-byte-p-when-equal-bv-dag ;disabling because the free var gets bound to a term, which crashes bind-bv-size-axe
     equal-of-bvplus-hack-for-sha1
     bvlt-4-when-unsigned-byte-p-back
     boolor-of-not-of-boolor-same
     myif-of-myif-of-boolor-same
     nthcdr-of-myif-arg2
;    bvlt-of-bvif-arg2 ;bad?
;    bvlt-of-bvif-arg3 ;bad?
     bvlt-of-31-and-2147483646
     boolor-of-booland-not-boolor
     times-of-bvmult-4
     bvchop-chop-leading-constant
     bvplus-minus-3-tighten-4
;sbvdiv-rewrite ;trying
     slice-31-2-minus-4
     getbit-of-+-becomes-getbit-of-bvplus
     bvplus-minus-7-tighten-30
     unsigned-byte-p-of-plus-minus-4-gen-axe
     equal-1-slice-4-2-5

;     bvlt-transitive-free-back
     bvplus-minus-16-tighten-32
     bvplus-minus-15-tighten-32
     bvplus-minus-14-tighten-32
;slice-of-bvplus-cases-no-split-carry
;     slice-of-bvplus-cases-no-split-no-carry2 ;fri mar 18 18:06:51 2011
     bvuminus-when-bvchop-known-subst
     slice-of-bvplus-cases-no-split-case-no-carry
;slice-of-bvuminus ;trying
     bvlt-flip-top-bit-3-4
     bvcat-equal-rewrite                                   ;bad?
     bvmult-of-bvplus-4-3-5
;    bvuminus-when-bvchop-gen-for-5 ;slow? tue jan 12 21:44:34 2010
     bvlt-of-bvmult-5-5-4-14 ;gen
     bvlt-of-bvmult-5-5-4-15
     bvlt-of-bvmult5-4-16

     bvlt-of-bvplus-same2
     bvplus-minus-15-tighten-6
     bvplus-minus-14-tighten-6
     bvplus-minus-13-tighten-6
     bv-array-read-of-bv-array-write-same-gen
     bvplus-of-bvplus-constants-size-differs-better-no-split
     bvlt-of-bvmult-5-5-4-28
     bvlt-of-bvmult-5-5-4-30
     bvlt-of-bvmult-5-5-4-31
     minus-<-minus-hack
     bvplus-minus-3-tighten-5
     inverse-of-+-as=0
     cdr-of-nthcdr-of-bvplus
;bv-array-write-equal-rewrite ;introduces bv-array-clear

     integerp-implies-acl2-numberp
     bvlt-of-bvmod-hack
     bvplus-of-1-33-32
     unsigned-byte-p-of-bvmod-hack
     bvmod-tighten-axe
     bvdiv-tighten-dag ;new
     bvmod-cancel-hack-8-1-44-6-1
     bvmod-tighten-axe-free-1
     bvmod-does-nothing-6-44
     unsigned-byte-p-of-bvmod ;gen and add to usb rules
     unsigned-byte-p-of-mod
     bvlt-of-mod-hack
     equal-of-bvplus-and-bvplus-diff-sizes
     equal-of-bvplus-and-bvplus-diff-sizes-alt
     bvif-trim-arg1-axe-all
     bvif-trim-arg2-axe-all
     bvlt-of-bvplus-constants2
     equal-of-bvplus-and-bvplus-reduce-constants

     len-of-car-when-items-have-len
     items-have-len-of-cdr
     equal-of-constant-and-cons
     ;;nthcdr-is-nil ;seemed very slow! ;wed feb 24 01:37:03 2010
     equal-of-+-of-unary-minus
     subrange-of-cons

     equal-of-bv-array-write-and-bv-array-write-same
     ;;new stuff:
     ;;fixme: this rule seems bad so try without it (or with a replacement?): add a polarity?
     equal-of-nil-when-true-listp ;Wed May  5 13:13:53 2010 (put back Fri May 21 01:12:47 2010)
     ;; consp-when-true-listp2 ;trying without..
     ;;consp-when-true-listp ;trying without this since we're using equal-of-nil-when-true-listp
     ;; list::len-equal-0-rewrite
     ;; len-equal-0-rewrite-alt

;     bv-array-write-trim-index ;Mon Jul 19 21:04:17 2010

;bvplus-commutative-2-sizes-differ-other-case

     bvlt-when-not-max
;bvlt-of-bvplus-same-subst ;seemd to loop
;trying without these:
;                        sha1-lemma-0
;                        sha1-lemma-0b

     sha1-lemma-9 ;yuck?
     sha1-lemma-9-alt ;yuck?
     slice-when-large-alt
     slice-when-large
     equal-of-bvmult-of-power-of-2
;     equal-of-0-and-bvchop-when-large ;Fri Mar 18 18:06:36 2011
;     slice-when-bvlt-30-2-31-4 ;kill
     sha1-lemma-8
     equal-of-slice-and-slice-when-bvchops-same
     bvlt-when-not-bvlt-of-slice-and-slice2
     bvlt-when-not-bvlt-of-slice-and-slice
     bvplus-of-bvmult-tighten
     bvlt-of-bvcat-arg3-lemma-constant-version
     bvlt-of-bvcat-arg2-lemma-constant-version
     sha1-lemma-7
     bvlt-of-bvplus-and-bvplus-of-bvchop-same4
     bvlt-of-bvplus-and-bvplus-of-bvchop-same5
     bvlt-of-bvplus-and-bvplus-cancel-constants
     sha1-helper-100
     bvlt-of-slice-and-slice
     bvlt-of-bvplus-and-bvplus-of-bvchop-same3
     bvlt-of-bvplus-and-bvplus-of-bvchop-same-another2
     bvlt-of-bvplus-and-bvplus-of-bvchop-same-another
     bvlt-of-bvplus-and-bvplus-of-bvchop-same
     another-bound-hack-for-sha1
     bound-hack-for-sha1
     equal-of-bvplus-move-bvminus-alt-better
     equal-of-bvplus-move-bvminus-better
     equal-of-bvplus-move-bvminus-2-alt-better
     equal-of-bvplus-move-bvminus-2-better
     equal-of-bvplus-move-bvminus-2-alt
     equal-of-bvplus-move-bvminus-2
;     bvlt-when-unsigned-byte-p-better-non-constant ;wed sep  1 00:22:15 2010 problem?
     bvlt-of-bvplus-and-bvplus-cancel-1-1
     getbit-of-bvplus-of-bvuminus-when-bvle
     bvplus-commutative-2-sizes-differ2-axe
     bvlt-of-max-when-both-narrow
     ;;           bvlt-of-bvuminus ;trying without this 01/10
     bvplus-of-bvuminus-same-3-2
     equal-of-0-and-bvplus-of-bvplus-of-bvuminus
     getbit-of-bvplus-flip
     bvplus-associative-sizes-differ
     bvlt-when-not-equal-2-3

     bvplus-commutative-2-sizes-differ
     unsigned-byte-p-when-not-bvlt-tighten
     booland-of-boolor-and-not-same-1
     booland-of-boolor-and-not-same-2

     boolif-of-boolor-same-1
     boolif-of-boolor-same-2
     boolor-of-booland-of-not-same-1
     boolif-lemma-1
     boolif-lemma-2
     ;;                        bvplus-of-bvuminus-32-31-special-case ;make a cheap version?  or try last?
     equal-of-0-and-bvplus-of-bvuminus-32-31
     bvlt-of-bvplus-of-bvminus-expt-new
     bvlt-false-when-usb
     equal-when-bv-sizes-differ-1-dag
     bvlt-of-bvplus-of-bvminus-expt
     bvlt-of-bvplus-of-bvminus-expt-alt
     sha1-loop-hack
     sha1-loop-hack2

     boolif-of-not-of-boolor-same
     bvlt-of-bvplus-same-arg2
     bvlt-of-bvplus-same-arg2-alt
;     bvplus-of-bvplus-combine-constants-when-not-overflow ;fri mar 26 15:37:26 2010
     bvlt-of-bvuminus-and-bvuminus
     bvplus-of-bvuminus-tighten-hack

     equal-of-bvplus-cancel-arg2 ;drop?

     equal-of-0-and-bitxor ; tried moving this to core-rules-bv, but that caused problems.  we need bitxor cancellation rules.  (why doesn't the same thing happen for bvxor?)
     equal-of-bool-to-bit-split
     iff ;causes a split (todo: consider opening iff to equal of bool-fixes)
     bvlt-of-bvplus-of-bvuminus
;                               bvlt-of-bvplus-of-bvuminus-alt ;tue feb 23 00:54:24 2010
     bvlt-of-bvplus-same
     equal-of-bitxor-same
     equal-of-bitxor-same-alt
     unsigned-byte-p-1-of-bool-to-bit ;gen
;bvlt-when-bvlt-reverse ;seems expensive mon feb  1 20:26:19 2010
     bvlt-of-bvplus-and-bvplus-cancel

     equal-of-take-same
     bvlt-cancel-for-sha1
     bvlt-of-bvmult-for-sha1
     sbvmoddown-of-bvmult-same-32-5-5-5
     sbvmoddown-rewrite
     bvmod-of-bvmult-same
     bvmod-of-bvplus
     bvmult-of-bvplus-for-sha1
     bvmult-when-bvlt-6-5-3-4
     equal-of-nil-when-booleanp
     bvmod-of-bvplus-gen
     bvmult-tighten-hack-for-sha1
     bvlt-of-bvmult-for-sha1-gen2
     bvlt-of-bvmult-for-sha1-gen
     bvplus-of-bvmult-tigthen-for-sha1
     bvplus-of-bvmult-tigthen-for-sha1-2
     bvmult-tigthen-for-sha1-1000
     nthcdr-of-len-same
     ;equal-of-nil-and-finalcdr
     <-when-unsigned-byte-p
     <-when-unsigned-byte-p-alt
     ;;list::nthcdr-iff
     not-of-nthcdr
     bv-array-read-of-bv-array-write-both-better
     bvlt-hack-for-sha1
     bvlt-hack-for-sha1-alt
     bvlt-of-bvplus-of-bvuminus-other
;list::len-of-non-consp ;limit this? looped!
     bvlt-of-bvplus-and-bvplus-lemma-sha1)

 ;this doesn't remove these from the rules below - add an option to remove from both?
;which of these are already in : rules?
;more-dag-prover rules (remove some!)

;these get removed:
   '(sbvlt-becomes-bvlt-better       ;fri mar 26 08:12:17 2010
     myif-of-bvif-becomes-bvif-arg2  ;thu mar 25 12:59:18 2010 (4)
     myif-of-bvif-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg2

     bound-when-usb2 ;thu mar 25 05:33:45 2010

;bv-array-read-shorten-data
     myif-of-bv-array-write-arg1-safe ;may have caused big problems
     myif-of-bv-array-write-arg2-safe ;may have caused big problems
     unsigned-byte-p-of-myif
     bvplus-commutative-2-sizes-differ ;also the 2 rule?
     <-of-myif-arg1
     <-of-myif-arg2)))

              ;;ffixme remove duplicate rules!
;maybe add bvplus-comm-2..
              ;;boolor commut?

(defun axe-rewriter-rules ()
  (declare (xargs :guard t))
  '(work-hard                            ;drop
;    nth-of-myif ;Tue Mar 16 00:57:56 2010 (could restrict to myifs of conses) ;bad? ;Sun May  9 21:51:07 2010
    ))

;; Only used in the equivalence checker
;; todo: add more to this list!
;turn equal around... equal t and predicate...
;fixme consider adding *DEFINITION-MINIMAL-THEORY* to this, since acl2 will use those even when they are turned off?
;or avoid calling acl2 and all and just call prove-theorem?
;fixme should we turn sbvlts into bvlts?
;fixme make this a constant?
(defun exit-test-simplification-rules ()
  (declare (xargs :guard t))
  (append ;(base-rules) ;new! was bad in that it turned around equalities
   (unsigned-byte-p-forced-rules)                  ;new
   (booleanp-rules) ;new!
   (boolean-rules-safe) ;new!
   (type-rules)     ;very new (seems safe)
   '(equal-of-not-and-nil               ;tue jan 11 16:52:09 2011
     bvlt-of-bvchop-arg2
     bvlt-of-bvchop-arg3
     bvlt-tighten-free-and-free ;hope this is okay. fixme use polarities?
     <-of-bv-and-non-positive-constant
     not-of-not
     equal-nil-of-not
     ;;not-of-bool-fix ; just include boolean-rules-safe?
     ;;bool-fix-when-booleanp ; just include boolean-rules-safe?
     equal-same
     not-<-same
     if-of-t
     if-of-nil
     if-same-branches
     ifix-when-integerp
     bvchop-of-bvchop-same
     bvuminus-of-bvuminus ;just use core-rules-bv?
     consp-of-nthcdr
     nfix-does-nothing
     bvplus-of-bvuminus-same-2-alt
     bvplus-of-bvuminus-same-2
     bvuminus-of-bvplus
     bvplus-of-bvuminus-same-alt
     bvplus-of-bvuminus-same

     endp
     atom ;new

     ;;lots of new stuff:

     sbvlt-of-bvplus-of-constant-minus-1 ;new

     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt2
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt3
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt2
     boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt3
     boolor-of-sbvlt-combine-gen
     boolor-of-sbvlt-combine-gen-alt
     boolor-of-sbvlt-combine-gen-better
     boolor-of-sbvlt-combine-gen-better-alt
     boolor-of-sbvlt-combine-gen-extra-disjunct
     boolor-of-sbvlt-combine-gen-alt-extra-disjunct
     boolor-of-sbvlt-combine-gen-better-extra-disjunct
     boolor-of-sbvlt-combine-gen-better-alt-extra-disjunct

     sbvlt-when-sbvmoddown-hack ;gen!
     sbvlt-when-sbvmoddown-hack2
     sbvlt-when-sbvmoddown-hack3
     sbvlt-when-sbvmoddown-hack4

     boolor-of-bvlt-of-constant-and-bvlt-of-constant
     boolor-of-bvlt-of-constant-and-bvlt-of-constant-2
;            sbvlt-transitive-hack
     natp-when-unsigned-byte-p
     sbvlt-of-negative-constant-when-unsigned-byte-p
     sbvlt-trim-constant-left ; replace with a general trim rule?
     sbvlt-trim-constant-right ; replace with a general trim rule?
     sbvlt-transitive-1-a
     sbvlt-transitive-2-a
     sbvlt-transitive-1-b
     sbvlt-transitive-2-b
     sbvlt-transitive-3-a
     sbvlt-transitive-3-b

     sbvle
     bvle ;Sat Apr  9 15:52:09 2011
     sbvlt-of-bvplus-of-constant ;new

     if-x-x-nil                     ;new
     natp-of-len                ;new
     <-becomes-bvlt-axe-bind-free-arg1 ;new
     <-becomes-bvlt-axe-bind-free-arg2     ;new
     <-becomes-bvlt-axe-bind-free-and-free       ;new
     <-becomes-bvlt-axe-free-and-bind-free       ;new
     <-becomes-bvlt-free-alt    ;fri jan 14 04:10:47 2011
     <-becomes-bvlt-free        ;fri jan 14 04:10:49 2011

     sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger
     sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger-alt
     bvminus-becomes-bvplus-of-bvuminus
     sbvlt-becomes-bvlt-better
     unsigned-byte-p-when-unsigned-byte-p-smaller ;what else?  all predicates should be safe to include?
     bvlt-tighten-free-alt
     bvlt-tighten-free
     nth-of-cons-constant-version
     lookup-equal-of-acons          ;new
     ;;we may not want these because making a rule requires (equal (pred x) t) instead of (pred x)
     ;;EQUAL-OF-T-WHEN-BOOLEANP-ARG2 ;newer
     ;;EQUAL-OF-T-WHEN-BOOLEANP-ARG1 ;newer
     )))

;; Only used in the equivalence checker
;we do seem to sometimes need these when verifying that the simplified exit tests are the same as the original exit tests
(defun exit-test-simplification-proof-rules ()
  (declare (xargs :guard t))
  (append '(equal-of-t-when-booleanp-arg2 ;new ; todo: instead of these, include boolean-rules-safe?
            equal-of-t-when-booleanp-arg1 ;new
            turn-equal-around-axe ;Fri Apr  9 22:30:45 2010 hope this is okay
            )
          (boolean-rules)
          (exit-test-simplification-rules)))

;; ;todo: add to this (and/or of constants, etc.)
;; (defun rules-that-throw-stuff-away ()
;;   (declare (xargs :guard t))
;;   '(equal-same
;;     nth-of-cons-constant-version
;;     mv-nth-of-cons-safe))

(defun reassemble-bv-rules ()
  (declare (xargs :guard t))
  '(bvcat-of-slice-and-slice-adjacent
    bvcat-of-slice-and-getbit-adjacent
    bvcat-of-getbit-and-slice-adjacent
    bvcat-of-getbit-and-getbit-adjacent
    bvcat-of-slice-and-x-adjacent
    bvcat-of-getbit-and-x-adjacent
    ;; versions with 3 BVs:
    bvcat-of-slice-and-slice-adjacent-2
    bvcat-of-slice-and-getbit-adjacent-2
    bvcat-of-getbit-and-slice-adjacent-2
    bvcat-of-getbit-and-getbit-adjacent-2
    bvcat-of-slice-and-x-adjacent-2
    bvcat-of-getbit-and-x-adjacent-2))

;; ;deprecate?
;; (defun anti-blast-rules ()
;;   (declare (xargs :guard t))
;;   (reassemble-bv-rules))

;; Only used in the equivalence checker
(defun strengthening-rules ()
  (declare (xargs :guard t))
  (append '(bvlt-trim-constant-arg1 ; replace with a general trim rule?
            bvlt-trim-constant-arg2 ; replace with a general trim rule?
            bvlt-when-bvlt-wider
            not-bvlt-when-not-bvlt-narrower
            not-bvlt-when-not-bvlt-narrower2
;            bvlt-of-bvplus-constant-and-constant-other ;can cause case splits?
            bvlt-of-bvplus-constant-and-constant-safe
            bvlt-of-bvplus-constant-and-constant-safe2
            bvplus-trim-leading-constant ;consider the full trim
            integerp-of-len
            bvlt-of-plus-arg1
            bvlt-of-plus-arg2
            equal-of-bvchop-and-constant-when-bvlt-constant-1
            equal-of-bvchop-and-constant-when-bvlt-constant-2
            equal-of-bvchop-and-constant-when-not-bvlt-constant-1
            equal-of-bvchop-and-constant-when-not-bvlt-constant-2
            bvlt-when-bvlt-must-be-fake-free-axe ;thu mar 17 15:36:51 2011
            bvlt-when-bvlt-must-be-gen-axe ;fri may  6 21:22:34 2011
            bvlt-of-max-arg3-axe
            bvlt-of-constant-arg3
            bvlt-of-constant-arg2
            slice-when-bvlt-gen      ;wed mar 16 00:52:46 2011
            slice-when-not-bvlt-free ;wed mar 16 00:52:46 2011
            equal-of-0-and-slice-when-bvlt
            equal-of-bvchop-extend-when-bvlt
            equal-of-bvchop-extend-when-not-bvlt
            bvlt-when-bvchop-known-subst-alt
            bvlt-when-bvchop-known-subst
            bvlt-must-be-axe ;fixme more like this?
            not-equal-when-not-equal-bvchop
            not-equal-bvchop-when-not-equal-bvchop
            bvlt-of-constant-arg2-weaken
            bvlt-of-constant-arg2-strengthen
            bvlt-of-constant-arg3-strengthen
            bvlt-of-constant-arg3-weaken
            equal-of-constant-and-bvchop-when-bvlt ;new!
            bvlt-of-two-less-than-max-when-not-max  ;yuck?
            equal-of-constant-and-slice-when-bvlt   ;new
            equal-of-constant-and-slice-when-equal-of-constant-and-bvchop
            bvchop-subst-constant
            bvlt-transitive-1-a
            bvlt-transitive-1-b
            bvlt-transitive-2-a
            bvlt-transitive-2-b
            bvlt-transitive-3-a
            bvlt-transitive-3-b
            bvlt-transitive-4-a
            bvlt-transitive-4-b
            bvlt-transitive-5-a
            bvlt-transitive-5-b
            not-equal-of-max-when-huge
            bvlt-when-equal-of-constant
            ;; turn-equal-around-axe ;hope this doesn't mess up the assumptions..
            ;; equal-of-t-when-booleanp-arg1 ;new..
            ;; equal-of-t-when-booleanp-arg2 ;new require it to be a *known-predicates-except-not*, so make-equality-pairs can handle it?
            equal-of-nil-when-booleanp    ;new
            )
          (base-rules)
          (boolean-rules)))

;; todo: think about when we want these
(defun update-nth2-intro-rules ()
  (declare (xargs :guard t))
  '(update-nth-becomes-update-nth2 ; drop once arraycopy keeps types better?
    ;; update-nth-becomes-update-nth2-extend
    ;; update-nth-becomes-update-nth2-extend-gen
    update-nth-becomes-append ; drop once arraycopy keeps types better?
    ))

;; todo: get rid of this?
(defun jvm-rules-unfiled-misc ()
  (declare (xargs :guard t))
  (append '(equal-nil-of-myif
;basic rules:
            if-of-if-t-nil
;    possible-exception-of-nil
;    len-of-update-nth-rewrite-2
            ;; nth-of-bvchop-becomes-nth2 ;yuck?
            ;; nth-of-bvxor-becomes-nth2 ;yuck?
            ;; nth-of-slice-becomes-nth2 ;yuck?
;    true-listp-of-logext-list
;    logext-list-equal-nil-rewrite2
;    logext-list-equal-nil-rewrite
;    iushr-constant-opener
;            usbp8-implies-sbp32-2 ;fixme do we still need this?
            integerp-of-nth-when-all-integerp
;    logext-identity;;this caused problems.  trying without.
            sbp-32-when-non-neg ;do we need still this?
            one-plus-len-hack
            <-of-+-cancel-1-2
            <-of-+-cancel-2-1)))

;move?
;; TODO: Add more
(defun map-rules ()
  (declare (xargs :guard t))
  '(not-equal-of-nil-and-s))

;; todo: rename
;used by many axe examples
;; todo: include list-rules2?
(defun amazing-rules-spec-and-dag ()
  (declare (xargs :guard t))
  (append (amazing-rules-bv)
          (bvchop-list-rules)
          (lookup-rules) ;Sat Dec 25 23:52:09 2010
          (list-rules)
          (logext-rules) ;move to parent?
          (list-rules3)
          (alist-rules)
          (update-nth2-rules) ;since below we have rules to introduce update-nth2
          (update-nth2-intro-rules)
          (update-nth-rules)
          (jvm-rules-unfiled-misc)
          (more-rules-yuck)
          '(getbit-list-of-bv-array-write-too-high
            map-packbv-constant-opener)))

;todo: rename?  Maybe to miter-rules?
;todo: build this from smaller lists of rules?
;GETBIT-OF-BVXOR-ERIC ;seemed to be bad for dag prover Tue Jan 12 06:24:08 2010
(defun axe-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append '(mod-of-0-arg1

             equal-of-map-reverse-list-and-map-reverse-list ;Tue Feb  8 15:08:06 2011

             ;; logext can still appear (if arraycopy is called):
             logext-when-usb-cheap
             logext-identity-when-usb-smaller-axe

             all-unsigned-byte-p-of-take-of-subrange ;Fri Dec 17 03:22:09 2010
             all-true-listp-of-map-unpackbv
             items-have-len-of-map-unpackbv
             map-packbv-of-map-unpackbv
             group-of-ungroup-same
             all-true-listp-of-map-reverse-list
             items-have-len-of-map-reverse-list
             all-unsigned-byte-p-of-reverse-list
             all-all-unsigned-byte-p-of-map-reverse-list

             equal-of-map-packbv-and-map-packbv

             bvlt-transitive-3-a
             bvlt-transitive-3-b
             bvlt-transitive-4-a
             bvlt-transitive-4-b
             bvlt-transitive-5-a
             bvlt-transitive-5-b

             equal-of-bvchop-extend-when-bvlt     ;new
             bvplus-of-bvuminus-of-bvcat-of-slice32 ;new
             bvplus-of-bvuminus-of-bvcat-of-slice   ;new
             bvlt-of-floor-arg3
             bvlt-of-floor-arg2
             bvchop-numeric-bound ;applied for even non-constant widths Fri Sep  3 10:19:33 2010
             ;; equal-of-nth2-and-bv-array-read ;Tue Aug 31 03:44:49 2010 drop?
             ;; equal-of-nth2-and-bv-array-read-alt ;Tue Aug 31 03:44:49 2010 drop?
             ;; unsigned-byte-p-of-nth2 ;Tue Aug 31 03:44:58 2010 drop?
             sbvrem-when-positive-work-hard ;added work-hard Sat Dec 18 23:31:50 2010 ;was just in axe-prover-rules ;Fri Aug 13 00:51:36 2010
             equal-of-0-and-sbvrem-when-small
             unsigned-byte-p-of-*-of-constant ;Mon Jul 19 16:25:03 2010
             equal-of-0-and-+-of-minus-2 ;gen the 0?!
             boolor-of-bvlt-of-constant-and-bvlt-of-constant-3-disjuncts ;fffixme add the rest of these
             boolor-of-bvlt-of-constant-and-bvlt-of-constant
             boolor-lemma-sha-1
             unsigned-byte-p-of-minus
             bv-array-read-when-index-is-len

             leftrotate-32-of-myif-arg2
             bvnot-of-myif

             bvlt-of-myif-arg3
             bvlt-of-myif-arg2
             bvcat-of-myif-arg2
             bvcat-of-myif-arg4

             bvcat-of-constant-when-equal-of-constant-and-bvchop
             equal-of-bvchop-and-bvplus-of-same
             equal-of-bvchop-and-bvplus-of-same-alt
             <-of-+-of-minus-and-constant
             <-of-+-of-minus-and-constant-alt
             bvlt-unique
;equal-of-constant-and-getbit-extend ;loops with BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE?
             unsigned-byte-p-of-1-when-not-nil
             nth-when-all-same-cheap
             equal-of-nil-and-map-packbv
             bv-array-read-of-append
             bv-array-read-of-map-packbv
             bvcat-of-slice-when-slice-known
             nth-becomes-bv-array-read-strong2
             nth-of-bv-when-all-same
             unsigned-byte-p-of-+-of-minus-better
             bv-array-write-shorten-constant-data
             EQUAL-OF-CONSTANT-AND-BVXOR-OF-CONSTANT
             bvlt-6-4
             bvlt-of-bvuminus-same
             bvplus-of-same
             bvlt-of-bvmult-of-constant-and-constant
             ASSOCIATIVITY-OF-+
             bvcat-of-slice-extend-constant-region
             ;len-of-FINALCDR
             ;group-of-FINALCDR
             bvcat-when-unsigned-byte-p
             unsigned-byte-p-of-2-when-bvlt
             nth-of-myif-limited ;Mon May 10 02:08:59 2010 trying this since i needed nth of myif to make two nodes in the miter agree? - maybe we should always blast a multiple-value expression?
             equal-0-getbit-when-bvlt
             equal-of-0-and-slice-extend
             nthcdr-of-firstn-same
             bvlt-6-1
             equal-of-0-and-getbit-when-bvlt-hack
;             slice-when-not-bvlt-hack ;kill
             drop->-hyps
             <-of-+-of-minus
             <-of-+-of-minus-alt
             equal-of-+-of-minus-alt
             equal-of-+-of-minus
             <-of-+-of-minus-32
             <-of-+-of-minus-alt-32
             equal-of-+-of-minus-alt-32
             equal-of-+-of-minus-32

             bvcat-when-top-bit-0-2
             bvcat-when-top-bit-0
             nth-of-nil
             equal-of-nil-when-equal-of-len
             move-minus-hack
             move-minus-hack2
             firstn-of-+-of-minus
             firstn-of-+-of-minus-2
             unsigned-byte-p-tighten-when-slice-is-0
             unsigned-byte-p-false-when-not-longer
             equal-of-0-and-bvchop-6
             bvlt-of-64
             unsigned-byte-p-of-+-of-minus2
             sbvlt-of-+-arg1
             sbvlt-of-+-arg2
             bvplus-of-unary-minus-arg2
             all-all-unsigned-byte-p-of-append
             all-all-unsigned-byte-p-of-cons
             items-have-len-of-cons
             items-have-len-of-append
             firstn-of-nil
             all-all-unsigned-byte-p-of-nil
;             equal-of-0-and-len-when-true-listp ;loops with equal-of-nil-when-true-listp ;fri may 21 01:25:02 2010
             bvlt-of-33554432 ;todo: gross
             unsigned-byte-p-shrink
             times-of-64-becomes-bvmult
             subrange-of-cons-constant-version
             bv-arrayp ;think about this...
             bv-array-clear-of-bv-array-write-both
             <-of-constant-when-natp-2
             unsigned-byte-p-when-bvlt
             bvcat-when-highsize-is-not-posp
             bvcat-when-lowsize-is-not-posp
             fold-consts-in-*
             booland-of-bvlt-of-constant-and-bvle-of-constant
             sbvlt-of-bvplus-of-bvuminus-tighten-31-32
             sbvlt-of-negative-constant-when-unsigned-byte-p-2
             <-of-constant-when-usb
             my-integerp-<-non-integerp
             my-non-integerp-<-integerp
             booland-combine-adjacent-bvles
             booland-combine-adjacent-bvles-alt
             boolif-of-not-same-arg2 ;moved from axe-prover-rules
             boolif-of-not-same-arg3 ;moved from axe-prover-rules

             sbvlt-of-bvplus-of-constant-and-constant
             nth-when-equal-of-take-hack
             prefixp-same
             prefixp-of-cdr-rule
             bvchop-when-must-be-1
             bvplus-subst-value
             bvplus-subst-value-alt
             subrange-of-bv-array-write-irrel ;drop?
;subrange-of-bv-array-write-in-range
             subrange-of-bv-array-write

             cdr-of-subrange
             bv-array-clear-range-of-bv-array-write-both
             cdr-of-bv-array-clear
             nth-of-bv-array-clear-both
             sbvlt-of-constant-when-<-of-constant
             bvlt-of-constant-when-<-of-constant
             sbvlt-of-bvplus-32 ;yuck?
             bvchop-identity-when-<
             bv-array-clear-range-of-1-and-cons-of-0
             bv-array-read-of-append-of-cons
             bv-array-clear-range-of-append-one-more
             append-of-constant-and-cons-of-constant
             bv-array-clear-range-of-cons
             bv-array-clear-range-of-append-of-cons
             bv-array-clear-range-of-cons-of-cons
             bv-array-clear-range-of-bv-array-write-too-high

             bv-array-clear-length-1-of-list-zero ;Wed Apr 14 00:23:10 2010
             bvchop-identity-cheap ;moved from prover rules
             bvplus-of-bvcat-and-bvuminus-of-bvcat ;Tue Apr 13 16:17:40 2010
             bvminus-of-constant-and-bvplus-of-constant ;Sun Apr 11 17:17:35 2010
             true-listp-of-add-to-end
             len-of-add-to-end ;fixme just expand add-to-end ?
             ;append-of-final-cdr-arg1
             prefixp-of-true-list-fix-arg2
             prefixp-of-true-list-fix-arg1
             prefixp-of-add-to-end
             prefixp-of-nil-arg2
             prefixp-of-nil-arg1
             equal-of-+-of-minus-same
             equal-of-fix-same ;reorder?
             <-of-256

             <-becomes-bvlt-axe-bind-free-arg1-strong-safe ;these are from md5
             equal-of-bvplus-cancel-2-of-more-and-1-of-more
             equal-of-bvplus-cancel-3-of-more-and-1-of-more
;              bound-when-usb2
;              myif-of-bvif-becomes-bvif-arg2
;             myif-of-bvif-becomes-bvif-arg1
;            myif-of-bvcat-becomes-bvif-arg1
;           myif-of-bvcat-becomes-bvif-arg2
;             getbit-of-bvplus-split ;bad? introduces ifs sat dec 25 23:51:03 2010

             sbvlt-becomes-bvlt-cheap
             sbvlt-becomes-bvlt-cheap-1
             sbvlt-becomes-bvlt-cheap-2
             equal-of-bvplus-cancel-arg1 ;was just in prover-rules
             firstn-of-0
             bv-array-clear-of-cons
             bv-array-read-of-cons-both
             equal-of-myif-and-bvif-same
             equal-of-myif-and-bvif-same-alt
             bvplus-of-bvplus-of-bvuminus-of-bvcat ;new without this there was a problem
             boolor-of-equal-and-not-of-equal-constants
             boolor-of-equal-and-not-of-equal-constants-alt
             booland-of-booland-of-boolif
             not-equal-constant-when-unsigned-byte-p-bind-free-axe ;was just in prover-rules ;Wed Mar 17 04:03:01 2010
             sha1-context-hack ;Wed Mar 17 03:54:02 2010 (how much does this help?)
             boolor-of-booland-same-2 ;Wed Mar 17 03:06:45 2010
             bvlt-of-constant-when-unsigned-byte-p-tighter
             equal-of-repeat-and-bv-array-write-hack-alt
             equal-of-repeat-and-bv-array-write-hack

             all-unsigned-byte-p-of-append ;fri mar 12 03:05:08 2010

             booleanp-of-prefixp
             equal-of-constant-and-bv-array-write
             equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus-alt
             equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus
             all-unsigned-byte-p-of-repeat ;are these needed?

             ;;these are for the rolled proof:
             <-of-len-and-constant
             <-becomes-bvlt-axe-bind-free-arg1-strong ; todo: above we use the safe one
             <-becomes-bvlt-dag-gen-better2

             bvplus-of-bvuminus-of-bvcat-and-bvcat

             unsigned-byte-p-of-smaller
             bvxor-cancel-2-of-more-and-1-of-more
             bitxor-when-equal-of-constant-and-bvchop-arg1
             bitxor-when-equal-of-constant-and-bvchop-arg2
             <-of-+-cancel-1-2+  ; todo: also add commutativity of plus?
             getbit-when-equal-of-constant-and-bvchop
             not-equal-of-constant-when-not-bvlt-constant-1
             not-equal-of-constant-when-not-bvlt-constant-2
             not-equal-of-constant-when-bvlt-constant-1
             not-equal-of-constant-when-bvlt-constant-2

             bv-array-read-of-unary-minus-32-2 ;new
             bvuminus-of-myif-arg2
             equal-of-firstn-and-firstn-same
             true-listp-of-firstn ;wasn't already included?!
             bvchop-0-hack
             slice-of-bvif-safe
             equal-of-constant-and-slice-when-bvlt
             equal-of-constant-and-slice-when-equal-of-constant-and-slice
             equal-of-constant-and-slice-when-equal-of-constant-and-bvchop ;may help a lot?  more like this?

             bvlt-of-constant-and-slice
             bvif-of-equal-of-bvchop-same
             equal-of-0-and-slice-when-bvlt
             equal-of-0-and-slice-when-bvlt2
;             unsigned-byte-p-of-+-of-minus ;thu apr 29 05:44:14 2010
;            unsigned-byte-p-of-+-of-minus-alt ;thu apr 29 05:44:17 2010
             bvxor-subst-arg2
             bvxor-subst-arg3

             ;;bvlt-of-bvchop-arg3
             ;;bvlt-of-bvchop-arg2

             bvcat-subst-constant-arg2
             bvcat-subst-constant-arg4

             firstn-of-firstn ;make a safe non-splitting version?
             bvlt-of-2147483583
             nthcdr-of-bv-array-write-is-nil
             slice-of-floor-of-expt-constant-version
             consp-becomes-<-of-len
             getbit-when-slice-is-known-constant
             bitxor-of-minus
             floor-of-*-of-8-and-32
             consp-of-ungroup

             equal-of-constant-and-+-of-minus-and-bv
             group-of-cons
             <-of-non-integerp-and-integerp
             bvlt-of-bitxor-of-1-same
             bvlt-of-bitxor-of-1-same-two

             <-of-constant-and-+-of-bv-and-minus-and-bv
             <-of-+-of-minus-becomes-bvlt
             unsigned-byte-p-of-slice-one-more
             equal-of-plus-minus-move
             equal-of-0-and-+-of-minus ;these should have similar names
             myfirst-of-myif-arg2
             map-packbv-of-myif-arg3
             group-of-myif-arg2
             booland-of-not-of-equal-and-equal-constants
             booland-of-not-of-equal-and-equal-constants-alt


             equal-of-bitxor-and-bitxor-same-6
             ;bvplus-of-bvcat-constants ; trying..
             slice-when-bvchop-known-2

             consp-of-group
             ;;BV-ARRAY-READ-OF-BV-ARRAY-WRITE-DIFF-SAFE-fixme ;make it not true?! huh?
             bv-array-clear-range-of-bv-array-write-contained
             sbvlt-of-constant-and-bvplus-of-constant ;yuck?
             equal-of-bvplus-of-bvchop-and-bvplus-same
             boolor-of-not-and-booland-same-1
             unsigned-byte-p-of-bvuminus-bigger
             <-of-len-and-expt-of-2-constant-version
             <-of-constant-and-*-of-constant     ;can introduce fractions...
             <-of-*-of-constant-and-constant ;can introduce fractions...
             <-of-floor-constant-when-not-integerp
             move-minus-to-constant
             <-of-minus1-and-floor

             equal-of-*-of-1/4-and-slice-of-2
             <-of-0-and-*
             bvchop-of-1/4
             equal-of-0-and-*-of-constant
             *-of-1/4-and-bvcat-of-0
             *-of-1/16-and-bvcat-of-0
             integerp-of-*-of-1/4 ;gen!

             ;;sha1-spec-case-rules:
             equal-of-0-and-bvmult-of-expt-constant-version
             bvmult-tighten-6-8-2
             bvuminus-of-*
             equal-of-bvmult-of-expt-constant-version
             acl2-numberp-of-mod
             integerp-of-mod
             bvchop-shift-gen-constant-version

             bvlt-of-*-arg3

             bvlt-add-to-both-sides-constant-lemma ;expensive?

             ;rationalp-when-integerp ;drop
             rationalp-of-floor
             rationalp-*2
             integerp-of-floor
;             bvuminus-of-bvuminus
             consp-of-repeat ;move

             boolor-hack-sha1
             booland-of-not-of-boolor
             bvlt-add-to-both-sides-constant-lemma-alt-dag
             bvlt-of-bvuminus-and-constant
             boolor-of-booland-of-not-same-2

             booland-of-boolor-and-not-same-5
             booland-of-boolor-and-not-same-5-alt
             booland-of-boolor-and-not-same-3
             booland-of-boolor-and-not-same-4
             bvlt-of-bvuminus-5-4
             rationalp-of-ceiling
             integerp-of-ceiling
             bvlt-of-bvuminus-arg2-constant
             ;; <-becomes-bvlt-axe-bind-free-and-bind-free
             <-0-+-negative-2
;    +-of-myif-arg1 ;new5
;   +-of-myif-arg2 ;new5
             repeat-of-myif-arg1
             take-of-nil
             integerp-of-+-when-integerp-1
;    unary---of-bvif ;new5
             nfix
             *-of-1/32-and-bvcat-of-0
;    bvlt-of-bvif-arg3 ;bad?
;    bvlt-of-bvif-arg2 ;bad?

             booland-of-not-same2
;    equal-of-bvif ;trying without..
             plus-of-minus-one-and-bv-dag
             <-of-+-arg1-when-negative-constant
             ; <-of-+-arg2-when-negative-constant ;uncomment?
;bvuminus-when-smaller-bind-free
;    bvuminus-when-smaller-bind-free-dag
             commutativity-2-of-+-when-constant
             rationalp-of--
             rationalp-of-+
             bvlt-of-1
             max
             bvchop-of-times-of-/-32
             integerp-of-1-times-1/32
             commutativity-of-*-when-constant
             bvmult-32
             <-of-bvcat-alt
             +-of-bvplus
             take-of-repeat
             rationalp-of-myif
             rationalp-of-len
             booleanp-of-rationalp
             len-of-group
             floor-of-16-when-usb-31
             *-becomes-bvmult-axe
;ceiling-in-terms-of-floor

             floor-of-32-when-usb
             list-fix-of-append
             not-bvlt-of-constant-when-usb-dag
             minus-becomes-bv-2
;commutativity-2-of-+

             nthcdr-of-repeat
             functional-self-inversion-of-minus
             distributivity-of-minus-over-+

             ;; <-becomes-bvlt-axe-bind-free-arg1 ;Wed Feb 24 15:00:10 2010
             +-combine-constants
             <-of-negative-constant-and-unary-minus
             move-negative-addend-1
             unicity-of-0
             collect-constants-over-<
             collect-constants-over-<-2

             natp

             rationalp-when-bv-operator
             acl2-numberp-when-bv-operator

             ;; +-becomes-bvplus-hack-gen
;group-of-append-new ;too aggressive? ;Fri May 21 07:20:55 2010
             append-associative ;move

;(bit-blast-rules-basic) ;new! we only want these when mitering?
             unsigned-byte-p-of-+-of-constant-strong
             nth-of-repeat
             +-of-minus-1-and-bv2-alt-bind-free
             <-of-constant-and-+-of-bv-and-minus
             <-of-constant-and-+-of-minus-and-bv

             nth-of-plus-of-bv-and-minus
             nth-of-plus-of-bv-and-minus-alt
             repeat-of-plus-of-bv-and-minus
             repeat-of-plus-of-bv-and-minus-alt

;;;FLOOR-OF-MINUS-ARG1 ;scary
;;;FLOOR-OF-sum ;scary

             equal-of-booleans-axe ;EQUAL-OF-BOOLEANS-SPLIT
             getbit-of-myif

             true-listp-of-ungroup
             bvplus-of-bvuminus-of-slice-and-bvcat-of-slice

             equal-of-+-and-bv
             equal-of-0-and-floor
             equal-of-getbit-and-bitxor-same
             equal-of-getbit-and-bitxor-same-alt
             equal-of-floor-of-expt-and-bv-constant-version-dag
             <-of-diff-of-bv-and-constant
             <-of-constant-when-<=-of-free
             bvxor-cancel-lemma1-bvchop-version-alt3
             bvxor-cancel-lemma1-bvchop-version-alt2
             floor-bound-lemma3
             equal-of-bvplus-cancel-arg2-alt ;more?
             equal-of-constant-and-bvif-of-constant-and-constant

             ;;                                      <-of-constant-and-+-of-minus
             ;;                                      <-of-*-of-floor-and-same
             ;;                                      +-of-bvplus-of-1-and-unary-minus-same
             ;;                                      +-of-bvplus-of-2-and-unary-minus-same

             +-of-minus-bind-free-constant-version ;more like this?!
             unsigned-byte-p-of-floor-of-expt-constant-version
             bvplus-of-floor-4-32
             bvplus-of-floor-4-32-alt
             bvmult-of-expt2-constant-version
             equal-constant-+-alt

             ;;new (try with the back?!):
             ;;                                      bvand-of-bvxor-of-ones-same
             ;;                                      bvand-of-bvxor-of-ones-same-alt
             ;;                                      bvand-of-bvand-of-bvxor-of-ones-same
             ;;                                      bvand-of-bvand-of-bvxor-of-ones-same-alt
             ;;                                      BITXOR-COMMUTATIVE-2-INCREASING-AXE
             ;;                                      BITXOR-COMMUTATIVE-INCREASING-AXE

             ;;                                      EQUAL-OF-CONSTANT-AND-BVXOR-OF-CONSTANT
             ;;                                      bvnot-becomes-bvxor
             ;;                                      BVCAT-EQUAL-REWRITE ;wait, why didn't this fire when the slow dag is rewritten?
             ;;                                      BVCAT-EQUAL-REWRITE-ALT


             ;;                                      BVXOR-COMMUTATIVE-AXE
             ;;                                      BVXOR-COMMUTATIVE-2-AXE
             ;;                                      ;BVXOR-ASSOCIATIVE
             ;;                                      SLICE-OF-BVXOR
             ;;                                      EQUAL-OF-BITXOR-SAME
             ;;                                      EQUAL-OF-BITXOR-SAME-alt
             ;;                                      TURN-EQUAL-AROUND-AXE4
             ;;                                      equal-of-getbit-and-bitxor-same
             ;;                                      equal-of-getbit-and-bitxor-same-alt
             ;;                                      equal-of-getbit-and-bitxor-same-alt2
             ;;                                      equal-of-getbit-and-bitxor-same-alt3
             ;; ;                         BOOLAND-ASSOCIATIVE
             ;;                                      equal-of-bitxor-and-bitxor-same
             ;;                                      equal-of-bitxor-and-bitxor-same-2
             ;;                                      equal-of-bitxor-and-bitxor-same-3
             ;;                                      equal-of-bitxor-and-bitxor-same-4
             ;;                                      equal-of-bitxor-and-bitxor-same-5
             ;;                                      equal-of-bitxor-and-bitxor-same-6
             ;;                                      equal-of-bvxor-and-bvxor-same-7
             ;;                                      equal-of-bvxor-and-bvxor-same-8
             ;;                                      BVCAT-EQUAL-REWRITE
             ;;                                      BVMULT-OF-EXPT2-constant-version
             ;;end of new stuff

             equal-of-nth-and-bv-array-read-better
             equal-of-nth-and-bv-array-read-alt-better

             boolor-adjacent-ranges-sha1-hack ;fragile! ;maybe not needed?

             equal-of-bitxor-and-bitxor-same
             getbit-of-bvmult-of-expt-constant-version
             equal-of-myif-same-1
             equal-of-myif-same-2
             bvif-of-myif-arg3
             bvif-of-myif-arg4
             bvplus-of-+-arg3
             bvplus-of-+-arg2
             slice-of-+-becomes-slice-of-bvplus ;ffixme complete set..
             bv-array-read-of-+
             <-of-+-of-minus-and-bv
             equal-of-+-of-minus-and-bv
             nth-of-bv-array-write-becomes-bv-array-read-strong
             sha1-hack-four-million-six
             equal-of-0-and-bvplus-of-bvuminus-alt
             equal-of-0-and-bvplus-of-bvuminus
             sha1-hack-four-million-four
;                                bvplus-of-bvplus-constants-size-differs-better-no-split-case2 ;wed feb 24 14:58:25 2010
             acl2-numberp-of-myif
             boolif-of-booland-same
             boolif-of-boolor-same
             sha1-hack-four-million-five-alt
             sha1-hack-four-million-five


             sha1-hack-four-million-one
             sha1-hack-four-million-three
             boolif-of-not
             sha1-hack-four-million
             ;;bvchop-of-nth-becomes-bv-array-read2
             nth-becomes-bv-array-read-strong ;why doesn't this fire?
;bvif-of-nth-arg3
;bvif-of-nth-arg4
             bvplus-of-myif-arg3
             bvplus-of-myif-arg2
;BOOLOR-ASSOCIATIVE ;new - do we have dag versions of the comm rules? - was this slow?!
;bvcat-of-nth-arg2
;bvcat-of-nth-arg4
;bvxor-of-nth-arg2
;bvxor-of-nth-arg3
;bitxor-of-nth-arg1
;bitxor-of-nth-arg2
;slice-of-nth-becomes-bv-array-read ;i have high hopes for this. yeeg.
             boolif-of-booland-of-boolor
             boolif-of-boolor-of-boolor
             bvif-of-+-arg3
             bvif-of-+-arg4
             bvif-of-minus-arg3
             bvif-of-minus-arg4
             slice-of-myif
             bvlt-of-huge-when-slice-not-max
             bvchop-of-minus-becomes-bvuminus
             items-have-len-of-nil
             items-have-len-of-myif
             bvlt-when-slice-known-hack
             equal-of-slice-and-slice-when
             equal-of-slice-and-slice-when-alt
             slice-monotone-strong-30-6-bv
             equal-of-subrange-and-subrange-same-lsts-and-ends
             sha1-hack-three-million
             sha1-hack-two-million
             sha1-hack-two-million-alt
             bvchop-subst-constant

             equal-of-packbv-and-packbv
             bvlt-of-bvplus-of-bvcat-of-slice
             unsigned-byte-p-of-myif-strong ;expensive..
             bvlt-of-bvmult-of-expt-arg2-constant-version2

             acl2-numberp-of-floor
             integerp-of-myif-strong

             ;bvchop-of-minus-trim
             ;bvchop-convert-arg2-to-bv-axe ; need the rest of the convert-to-bv-rules...

             sha1-hack-a-million
             subrange-of-take
             nthcdr-of-subrange
             subrange-of-group
             equal-of-group-and-group
             subrange-when-end-is-negative

             consp-of-subrange

;fffixme do these contradict what simplifying bitxors does?
             ;;BITXOR-commutative-axe
             ;; BITXOR-commutative-2-axe

             bvxor-of-bvcat-arg3     ;dangerous?
             bvxor-of-bvcat-arg2 ;dangerous?

             bvxor-cancel-lemma1-bvchop-version
             bvxor-cancel-lemma1-bvchop-version-alt


;             bvcat-of-slice-and-bvcat-of-getbit
             bvcat-of-slice-of-bv-array-read-and-bvcat-of-getbit-of-bv-array-read
             equal-of-bvxor-and-bvxor-arg1-arg2
             slice-of-bvxor ;needed due to an issue with bv-array-reads being trimmed
             bvxor-cancel-lemma1-alt
             bvxor-cancel-lemma1

             equal-of-0-when-bvlt
             trim-of-0-arg1
             bvmult-of-power-of-2-subst-9-8
             equal-of-slice-and-constant-when-equal-of-bvchop-and-constant2
             all-unsigned-byte-p-of-subrange
             bvmult-subst2-alt-constant-version
             bvmult-subst2-constant-version

             nth-of-unpackbv ;or should we unroll unpackbv?
             nth-of-ungroup-gen
             map-packbv-of-group-of-ungroup-of-map-unpackbv ;Sat Feb  5 13:02:18 2011
            ;drop?:
             map-packbv-of-map-ungroup-of-map-map-unpackbv ;Thu Feb  3 14:20:47 2011
             ;group-of-map-unpackbv ;Tue Feb  8 15:05:59 2011 yuck?!
             packbv-base ;drop?
             packbv-opener ;drop? would need trim of packbv and getbit of packbv ;add syntaxp hyp..
             bvchop-of-packbv
             all-unsigned-byte-p-of-map-packbv
             unsigned-byte-p-of-packbv-gen

;                                    bitlist-to-bv2-rewrite
             bv-array-read-when-equal-of-firstn-and-constant
             bv-array-read-when-equal-of-take-and-constant

;                                    UNSIGNED-BYTE-P-OF-BITLIST-TO-BV2
             nthcdr-of-ungroup
             bvplus-of-bvuminus-of-bvcat-of-0
;bool-to-bit ;was expensive
             bvcat-of-slice-onto-constant
             getbit-when-not-bvlt-constant

             bvxor-cancel-cross-1
             bvxor-cancel-cross-2
             bvxor-cancel
             bvxor-cancel-alt

             unsigned-byte-p-of-nth

             <-of-constant-and-unary-minus
             bvplus-and-bvcat-hack ;caused problems?
             <-of-minus-and-constant
             <-of-negative-constant-and-bv
;bvchop-of-nth-becomes-bv-array-read
             bvlt-of-one-less-than-max-25
             all-true-listp-of-nthcdr
             all-all-unsigned-byte-p-of-nthcdr
             all-unsigned-byte-p-of-nthcdr
             equal-of-0-and-getbit-of-bvplus
;                                GETBIT-OF-BVPLUS-SPLIT ;trying this - bad!
             items-have-len-of-nthcdr
             bvplus-of-bvcat-constants-hack
             bvlt-of-bvcat-arg2
             bvmult-of-4-gen

             nth-of-group
             bvmult-of-bvcat-hack100


             bvplus-of-bvuminus-of-bvcat-same
             items-have-len-of-group-strong
             bvdiv-of-64
;             sbvlt-becomes-bvlt-better

             group2-in-terms-of-group
             equal-of-group-and-group2-alt
             equal-of-group-and-group2
;                                    ceiling-in-terms-of-floor2 ;introduces /
;                                    group-of-map-byte-to-bit-list
             one-fourth-hack

             bound-when-low-bits-0
             bound-when-low-bits-0-alt
             bvcat-equal-rewrite-alt
             bvlt-of-bvplus-constant-and-constant-other
             len-of-ungroup ;what else is missing?
;                                    len-of-map-map-byte-to-bit-list
;                                    true-lisp-of-map-ungroup
;                                    len-of-map-ungroup
             equal-of-group2-and-group2
             ;group2-of-ungroup ;thu feb  3 17:20:24 2011
             ;group-of-ungroup ;Thu Feb  3 17:20:58 2011
;                                    TAKE-OF-MAP-BYTE-TO-BIT-LIST
;                                    LEN-OF-MAP-BYTE-TO-BIT-LIST
             bvmult-becomes-bvcat-31-64
;                                    group2-of-MAP-BYTE-TO-BIT-LIST
             bytes-to-bits-rewrite
             ;LEN-OF-BYTES-TO-BITS

             take-of-ungroup
             firstn-of-ungroup
             ceiling-of-bvcat-hack

             bvlt-when-bvchop-known-subst
             bvlt-when-bvchop-known-subst-alt
             bvlt-of-bvmult-9-8-400
;                                     slice-of-bvplus-cases-no-split-no-carry2 ;seems expensive...
             bvcat-of-bvmult-hack-another
             bvchop-of-floor-of-expt-of-2-constant-version
             unsigned-byte-p-of-bvmult-29-30-16
             equal-constant-when-bvchop-equal-constant-false

             sha1-hack-123434
             equal-of-bvplus-and-bvplus-cancel-arg1-arg1 ;more like this?!

             equal-of-bvnot-and-bvnot
             bvmult-of-bvcat-hack4
             bvmult-of-bvcat-hack3
             bvmult-of-bvcat-hack2
             take-of-group2
             floor-of-expt2-becomes-slice-when-bv-axe-constant-version
             take-of-bytes-to-bits
;GROUP-BECOMES-GROUP2 ;put this back?
             bvmult-of-bvcat-hack
             take-of-group
             firstn-of-group

             bvplus-of-slice-and-bvuminus-of-bvmult
             all-all-unsigned-byte-p-of-group
             true-listp-of-group
             all-true-listp-of-group
             booleanp-of-all-all-unsigned-byte-p

             majority-idiom1
             majority-idiom2
             majority-idiom3
             majority-idiom4
             majority-idiom5
             majority-idiom6
             majority-idiom7
             majority-idiom8

             bvand-of-bvnot-same
             bvand-of-bvnot-same-alt
             bvand-of-bvand-of-bvnot-same
             bvand-of-bvand-of-bvnot-same-alt

             bvand-associative
             bvand-commutative-2-axe

             bvor-associative
             bvor-commutative-2-axe
             bvor-commutative-axe

             equal-of-bvor-and-bvxor
             equal-of-bvor-and-bvxor-alt
             equal-of-bvxor-and-bvor
             equal-of-bvxor-and-bvor-alt

             plus-of-minus-becomes-bv-dag
             plus-of-minus-becomes-bv-dag-alt

             bvlt-of-slice-29-30-2
             slice-when-not-bvlt-gen
             bvlt-of-slice
             all-all-unsigned-byte-p-of-group2-rewrite
             bvplus-tighten-free-1
             bvplus-tighten-free-2
             bvlt-of-bvplus-when-bvlt-of-slices
             ;;             BVPLUS-OF-BVPLUS-COMBINE-CONSTANTS-WHEN-NOT-OVERFLOW ;Fri Mar 26 17:45:00 2010
             bvlt-of-slice-and-slice2-back

             bvlt-of-bvplus-constant-when-not-bvlt-of-bvplus-constant
;BOOLAND-COMMUTATIVE-2 ;looped? should never be used in the dag world?
;booland-commutative ;looped? should never be used in the dag world?
             booland-associative
             equal-of-0-when-bvlt-of-slice
             floor-becomes-slice-when-unsigned-byte-p
;             bvlt-tighten-free-alt ;problems? ;tue aug 31 19:45:37 2010
;             bvlt-tighten-free ;problems? ;tue aug 31 19:45:37 2010
             minus-becomes-bv
             true-listp-of-bv-array-clear-range
             all-unsigned-byte-p-of-bv-array-clear-range
             len-of-bv-array-clear-range
             bv-array-read-of-bv-array-clear-range-contained
             bv-array-read-of-bv-array-clear-range-high
             bv-array-read-of-bv-array-clear-range-low
             bv-array-clear-of-bv-array-clear-range-contained
             bv-array-clear-whole-range
             bv-array-clear-of-bv-array-clear-adjacent1
             bv-array-clear-of-bv-array-clear-adjacent2
             bv-array-clear-of-bv-array-clear-range-adjacent1
             bv-array-clear-of-bv-array-clear-range-adjacent2
             bv-array-clear-range-of-bv-array-clear-adjacent1
             bv-array-clear-range-of-bv-array-clear-adjacent2
             bv-array-clear-range-of-bv-array-clear-range-adjacent1
             bv-array-clear-range-of-bv-array-clear-range-adjacent2
             bv-array-clear-of-bv-array-write-better
;bv-array-clear-of-bv-array-write
             bvlt-of-bvplus-of-bvuminus-other-alt ;new
             all-true-listp-of-group2
             items-have-len-of-group2
             bvplus-of-bvuminus-trim
             <-becomes-bvlt-free ;ffixme put in the complete theory of this stuff?
             <-becomes-bvlt-free-alt
             <-of-constant-and-floor
             bvmult-of-slice-when-bvchop-0
             bvcat-equal-bvcat
             true-listp-of-nthcdr-2
             bvlt-of-slice-and-slice2
             bv-array-read-of-bv-array-clear
             all-unsigned-byte-p-of-bv-array-clear-gen
             len-of-bv-array-clear
             true-listp-of-bv-array-clear
             bv-array-read-of-take-better ;added -better fri dec 24 17:14:32 2010

             bvmult-of-bvcat
             bv-array-write-equal-rewrite
             bv-array-write-equal-rewrite-alt
             bv-array-write-of-bv-array-write-tighten-len
             min
             unsigned-byte-p-from-bound-constant-version-axe
             acl2-numberp-of-len
             ;; jvm::acl2-numberp-of-call-stack-size ;trying
             equal-of-append
             bvmult-tighten-axe-power-of-2
             bvplus-tighten-axe
             bvmult-tighten-axe ;can we do better for a power of 2?? ffixme
             true-listp-of-group2
             bvmult-of-bvplus-hack-gen-constant-version
             equal-of-bvmult-of-slice
             ;; <-becomes-bvlt-axe-bind-free-arg1 ;wed feb 24 15:00:22 2010
             <-of-floor-of-constant-and-constant-gen

             all-unsigned-byte-p-of-myif-strong
             all-unsigned-byte-p-of-take
             all-unsigned-byte-p-of-firstn   ;just in case

             floor-of-floor
             <-of-0-and-floor

             +-becomes-bvplus-axe-bind-free-and-free ;other ones?
             +-becomes-bvplus-axe-free-and-bind-free ;other ones?
;bvmult-of-slice-when-bvchop-0 ;where did this rule go? ffixme
             bvlt-of-bvmult-hack200
             nth-of-group2-gen
             nth-of-group2 ;drop?
             <-+-negative-0-2

             len-of-group2
             slice-subst-constant
             slice-subst-constant-alt
             bvplus-tighten-hack100
             bvmult-tighten-hack
             bvmult-of-bvplus-hack4
             bvmult-of-bvplus-hack3

;;dup             *-BECOMES-BVMULT-axe
             slice-tighten-top-free
             bvmult-of-bvplus-hack2
             bvmult-of-slice-tighten
             +-becomes-bvplus-axe
             bvmult-of-bvplus-hack
             bvmult-of-bvmult-hack
             nthcdr-of-nthcdr

             cdr-of-group2
             cdr-of-group
             ;; +-becomes-bvplus-when-bv-dag
             natp-of-*
             *-of-1/64-when-multiple
             integerp-of-*-of-1/64

             <-of-slice-and-constant-when-not-positive
             floor-of-64-when-usb-64
             floor-of-64-when-usb-31
             natp-of-floor
             nthcdr-of-group2
             nthcdr-of-group

             <-of-0-and-len-when-consp ;hope this is okay..
             all-true-listp-of-cdr
             all-all-unsigned-byte-p-of-cdr
             all-unsigned-byte-p-when-all-all-unsigned-byte-p
             true-listp-of-nth-when-all-true-listp
             len-nth-from-items-have-len
             equal-of-bvplus-and-bvplus-cancel-gen-alt
             equal-of-bvplus-and-bvplus-cancel-gen
             unsigned-byte-p-of-bvplus-tighten
             bvlt-tighten-arg1
;bvlt-tighten-arg2 ;wed feb 24 01:14:46 2010
             acl2-numberp-when-unsigned-byte-p
             bvlt-of-plus-arg1
             bvlt-of-plus-arg2

             <-of-negative-when-usbp
             bvlt-of-bvplus-1-cancel-alt
             posp
;             natp ;loops with not-<-of-0-when-natp
;natp-when-integerp

             equal-of-cons
;             bv-array-write-with-index-and-len-same ;mon jul 19 21:06:14 2010
;             bvxor-associative ;i can't believe this was missing!
;             bvxor-commutative-axe
;           bvxor-commutative-2-axe
             bvlt-transitive-free2-back-constants
             bvlt-of-bvplus-constant-and-constant
             bvlt-of-bvplus-same-alt
;                                <-of-bvplus-becomes-bvlt-arg1 ;wed feb 24 14:59:16 2010
;                                <-of-bvplus-becomes-bvlt-arg2 ;wed feb 24 14:59:16 2010
             nth-becomes-bv-array-read2
;             bvlt-transitive-free-back ;other rules like this?
             nth-of-take-2-gen
             nth-of-firstn ;move to list-rules?
             bvlt-when-not-bvlt
             bvlt-when-unsigned-byte-p
;                        <-of-bvplus-same-gen
;nth-of-take ;seemed expensive (why suddenly?)

             <-becomes-bvlt
             <-becomes-bvlt-alt
             equal-of-cons-and-cons-same-arg2
             subrange-same
             cons-equal-no-split
             +-of-minus1-and-bvplus-of-1
             take-of-bv-array-write-irrel
             nthcdr-of-take-becomes-subrange
             <-of-bvplus-same-32-1
             equal-of-append-arg1
             +-of-minus-constant-version
             bvlt-when-not-bvlt-one-more
             ;;bvchop-identity ;fri jan 15 22:52:27 2010

             slice-of-bvplus-cases-no-split-case-no-carry-constant-version
             plus-of-minus-of-slice-and-bvmult-of-slice
             plus-of-slice-and-minus-of-bvmult-of-slice
             bvmult-of-16-becomes-bvcat
             bvlt-of-bvmult-of-slice-and-slice

             items-have-len-of-group

             ;;                              ;i think maybe we don't want to open all this stuff until we have to?:
             ;;                              sha1-loop-11-unrollsha1-loop-11-base-case
             ;;                              sha1-loop-12-unrollsha1-loop-12-base-case
             ;;                              sha1-loop-13-unrollsha1-loop-13-base-case
             ;;                              sha1-loop-14-unrollsha1-loop-14-base-case
             ;;                              sha1-loop-15-unrollsha1-loop-15-base-case
             ;;                              sha1-inner-loop-base
             ;;                              sha1-inner-loop-unroll
             ;;                              prepare-message-schedule
             ;;                              prepare-message-schedule-aux-base
             ;;                              prepare-message-schedule-aux-unroll
             )
           (amazing-rules-spec-and-dag)
           (map-rules)
           (miter-rules) ;todo
           (introduce-bv-array-rules) ;do we still want these?

           ;;new, since these will be pulled out:
           (strip-cadrs (map-runes 'map-packbv))
           (strip-cadrs (map-runes 'map-unpackbv))
           (strip-cadrs (map-runes 'map-map-unpackbv))
           (strip-cadrs (map-runes 'map-ungroup)))
   '(sbvlt-becomes-bvlt-better ;fri mar 26 08:12:17 2010 ;delete this from above
     myif-of-bvif-becomes-bvif-arg2 ;thu mar 25 12:59:18 2010 (4)
     myif-of-bvif-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg2
     bound-when-usb2 ;thu mar 25 05:33:45 2010

     myif-of-bv-array-write-arg1-safe ;may have caused big problems
     myif-of-bv-array-write-arg2-safe ;may have caused big problems

     bvplus-when-<=-15-hack-for-sha1
     <-of-myif-arg2 ;wed feb  3 23:56:47 2010
;bv-array-read-shorten-data ;sat jan 16 02:37:49 2010
     firstn-becomes-take-gen  ;take caused problems ;revisit this?
     unsigned-byte-p-of-myif      ;thu jan 14 21:26:14 2010
     getbit-of-bvxor              ;tue jan 12 05:56:17 2010
     ;; nth-of-bvchop-becomes-nth2  ;yuck?
     ;; nth-of-bvxor-becomes-nth2
     ;; nth-of-slice-becomes-nth2

     bvlt-of-bvif-arg2
     bvlt-of-bvif-arg3
     bvplus-commutative-2-sizes-differ ;after including dag prover rules
     bvplus-commutative-axe    ;after including dag prover rules
     bvplus-commutative-2-axe  ;after including dag prover rules
;     bvxor-all-ones            ;why? ;trying without
     )))

(defun unroll-spec-rules ()
  (declare (xargs :guard t))
  (append (amazing-rules-spec-and-dag) ;todo: reduce?
          (introduce-bv-array-rules)
          (leftrotate-intro-rules) ; perhaps not needed if the specs already use rotate ops
          ))

;; todo: compare to unroll-spec-rules above
;; todo: avoid trimming down things like xors (possibly to multiple different sizes)?
;; todo: include reassemble-bv-rules, but they could loop with bit-blasting rules
(defun unroll-spec-basic-rules ()
  (set-difference-eq
   (append (base-rules)
           (amazing-rules-bv)
           (leftrotate-intro-rules) ; perhaps not needed if the specs already use rotate ops
           (list-rules) ; or we could allow the list functions to open (if both, watch for loops with list-rules and the list function openers)
           ;; (introduce-bv-array-rules) ; todo: consider these
           ;; '(list-to-byte-array) ;; todo: add to a rule set (whatever mentions list-to-bv-array)
           (if-becomes-bvif-rules) ; since we want the resulting DAG to be pure
           (bvchop-list-rules) ; I think some rule introduces bvchop-list, like a fixing function
           ;; Handle nth of a 2-d array:
           '(nth-becomes-nth-to-unroll-for-2d-array
             nth-to-unroll-opener
             collect-constants-over-<-2
             ;; group-base group-unroll ; I guess we get these automatically from calling opener-rules-for-fns (but not with :rules :standard, so try adding these back here)
             len-of-group ;; these are not needed if we unroll group/ungroup
             consp-of-group
             nth-of-group
             ungroup-of-cons)
           ;; (bv-array-rules-simple)
           ;; (list-to-bv-array-rules)
           ;; (set-difference-eq (core-rules-bv)
           ;;                    ;; these are kind of like trim rules, and can make the result worse:
           ;;                    '(;BVCHOP-OF-BVPLUS
           ;;                      BVCHOP-OF-bvuminus
           ;;                      ))
           ;; (unsigned-byte-p-forced-rules)
           )
   (append (bvplus-rules) ;; can lead to blowup in lifting md5
           (trim-rules) ;; can make things a lot bigger?
           (bvchop-of-bv-rules)
           )))

;outside-in rules.  Only used in rewriter-alt.lisp.
(defun oi-rules ()
  (declare (xargs :guard t))
  '(if-when-nil
    if-when-not-nil
    myif-when-nil
    myif-when-not-nil
    bvif-when-nil
    bvif-when-not-nil
    boolif-when-nil
    boolif-when-not-nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that this gets supplemented with any rules that are passed to the tactic-prover for rewriting
;; TODO: Use these whenever we translate to STP, not just in the tactic prover.
(defund pre-stp-rules ()
  (declare (xargs :guard t))
  (append
   '(;; since we don't translate these shift operations to STP:
     bvshl-rewrite-with-bvchop-for-constant-shift-amount ;introduces bvcat ; todo: replace with the definition of bvshl?
     bvshr-rewrite-for-constant-shift-amount             ; introduces slice
     bvashr-rewrite-for-constant-shift-amount            ;new, introduces bvsx
     ;; todo: handle more cases.  a general solution? ; see the leftrotate-unroller
     bvshl-16-cases
     bvshl-32-cases
     bvshl-64-cases
     bvshr-16-cases
     bvshr-32-cases
     bvshr-64-cases
     bvashr-16-cases
     bvashr-32-cases
     bvashr-64-cases
     ;; these are needed to resolve claims about the indices being in bounds (todo: generalize the rules above):
     <-lemma-for-known-operators-axe
     <-lemma-for-known-operators-axe-alt
     eql ; introduced by case
     not-equal-of-constant-and-bv-term-axe ; can get rid of impossible shift amounts
     not-equal-of-constant-and-bv-term-alt-axe ; can get rid of impossible shift amounts
     bvcat-of-0-arg1
     bvcat-of-0-arg3 ; can arise from unrolling a rotate
     equal-of-bvuminus-and-constant
     bvcat-of-bvchop-high
     bvcat-of-bvchop-low
     ;; Rules about rotates (since we don't translate most rotates to STP):
     leftrotate-open-when-constant-shift-amount
     rightrotate-open-when-constant-shift-amount
     rightrotate-becomes-rightrotate-unroller-strong2
     rightrotate-unroller-opener
     leftrotate-becomes-leftrotate-unroller-strong2
     leftrotate-unroller-opener
     ;; Introduce bvif when we can:
     if-becomes-bvif-1-axe
     if-becomes-bvif-2-axe
     if-becomes-bvif-3-axe
     if-becomes-bvif-4-axe)
   (bv-function-of-bvchop-rules)
   (type-rules)
   (unsigned-byte-p-forced-rules)))

(in-theory (disable (:e pre-stp-rules))) ; avoid big goals

(defthmd symbol-listp-of-pre-stp-rules
  (symbol-listp (pre-stp-rules))
  :hints (("Goal" :in-theory (enable (:e pre-stp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; priorities
;;

;; Want these to fire before commutativity:
(set-axe-rule-priority booland-of-constant-arg1 -1)
(set-axe-rule-priority booland-of-constant-arg2 -1)

;try this before bv-array-read-of-bv-array-write-both-better-work-hard, since this one has only a single work-hard
;would like a way to NOT try the both version if this one fails
(set-axe-rule-priority bv-array-read-of-bv-array-write-same-better-work-hard -1)

(set-axe-rule-priority natp-when-unsigned-byte-p 1) ;should be tried after the ones for the specific operators

;this one introduces a bvchop-list which usually has no effect, so try it last:
(set-axe-rule-priority bv-array-write-of-bv-array-write-diff-constant-indices-gen 1)

;Wed Feb 24 16:04:04 2010
;this is cheap, so let's try it first
(set-axe-rule-priority <-becomes-bvlt-axe-bind-free-and-bind-free -1)
(set-axe-rule-priority <-becomes-bvlt-axe-bind-free-and-free -1)
(set-axe-rule-priority <-becomes-bvlt-axe-free-and-bind-free -1)

;;rules about if (or should we go straight to myif and have all the rules be about that?!):

(set-axe-rule-priority if-of-t -1)
(set-axe-rule-priority if-of-nil -1)
(set-axe-rule-priority if-same-branches -1)

;want this to fire before the more general rules about boolif of constants:
(set-axe-rule-priority boolif-of-nil-and-t -1)

(set-axe-rule-priority not-bvlt-self -1) ;may fix a loop on (BVLT '32 (BVUMINUS '32 x) (BVUMINUS '32 x)) ??

(set-axe-rule-priority equal-same -1) ;new

;Associativity should fire first, so we always have bitxor nests that are associated to the right:
(set-axe-rule-priority bitxor-associative -10)

(set-axe-rule-priority nth-of-cons-constant-version -1) ;this hits a lot in some proofs, so let's check it first
(set-axe-rule-priority mv-nth-of-cons-safe -1)

;bit-blasting should be the last thing we try (otherwise we may try to bit-blast (bvchop 8 <bit-blasted-8-bit-thing>)
(set-axe-rule-priority bvchop-blast 10)
(set-axe-rule-priority bvxor-blast 10)
;new:
(set-axe-rule-priority bvor-blast 10)
(set-axe-rule-priority bvand-blast 10)
(set-axe-rule-priority bvnot-blast 10)
(set-axe-rule-priority bvcat-blast-high 10)
(set-axe-rule-priority slice-blast 10)
(set-axe-rule-priority bvif-blast 10)
(set-axe-rule-priority bvcat-blast-low 10)


;saw some sort of loop regarding adding to both sides. maybe these will help:
(set-axe-rule-priority bvplus-of-bvuminus-same -1)
(set-axe-rule-priority bvplus-of-bvuminus-same-alt -1)
(set-axe-rule-priority bvplus-of-bvuminus-same-2 -1)
(set-axe-rule-priority bvplus-of-bvuminus-same-2-alt -1)

(set-axe-rule-priority bvplus-becomes-ripple-carry-adder 10)
;new:
(set-axe-rule-priority blast-bvmult-into-bvplus-constant-version-arg2 10)
(set-axe-rule-priority blast-bvmult-into-bvplus-constant-version-arg1 10)

(set-axe-rule-priority unsigned-byte-p-of-0-arg1 -1) ;want this to fire early (may help prevent loops involving natp??)

(set-axe-rule-priority trim-of-0-arg1 -1) ;want this to fire first

(set-axe-rule-priority +-combine-constants -1) ;must happen before commutativity

;the printing rule fires first if it's on..
;(set-axe-rule-priority do-inst-becomes-do-inst-3-with-print -10) ;deprecated - really? no, seems to be used when we have an if-nest of states
;(set-axe-rule-priority do-inst-becomes-do-inst-3 -9)


;this seems crucial for some examples
(set-axe-rule-priority bvchop-of-bvcat-cases -1) ;this must fire before bvchop-identity

;BOZO more like this!
;or have the trim rules use a special bvchop for which we don't have bvchop-identity - we do that now!!
 ;these must happen before bvchop-identity to prevent loops: we might add the bvchop around a term that looks big, but then bvchop-identity might drop it if the term is known to be a usb some other way
(set-axe-rule-priority bvchop-of-bvplus -1)
(set-axe-rule-priority bvchop-of-bvminus -1)
(set-axe-rule-priority bvchop-of-bvmult -1)
(set-axe-rule-priority bvchop-of-bvxor -1)
(set-axe-rule-priority bvchop-of-bvor -1)
(set-axe-rule-priority bvchop-of-bvand -1)
(set-axe-rule-priority bvchop-of-bvif -1)
(set-axe-rule-priority bvchop-of-bv-array-read -1)
(set-axe-rule-priority bvchop-of-bitand -1)
(set-axe-rule-priority bvchop-of-bitor -1)
(set-axe-rule-priority bvchop-of-bitxor -1)
;; (set-axe-rule-priority bvchop-of-bvnth -1)
(set-axe-rule-priority bvchop-of-bvnot -1)
(set-axe-rule-priority bvchop-of-bvsx -1)
(set-axe-rule-priority bvchop-of-bvuminus -1)

(set-axe-rule-priority bv-array-read-of-bv-array-write 1) ;try this only if we fail to prove the indices are in bounds

(set-axe-rule-priority bvxor-combine-constants -11) ;do this before assoc  (really, why?)

;want this to fire late (after the rule for write of write with the same index, for example)
(set-axe-rule-priority bv-array-write-does-nothing 10)

(set-axe-rule-priority bvplus-trim-arg2-axe -3) ;we should trim before commuting the nest
(set-axe-rule-priority bvplus-trim-arg3-axe -3) ;we should trim before commuting the nest
(set-axe-rule-priority bvplus-associative -1) ;trying with this before the commutative rules

;new:
(set-axe-rule-priority bvchop-identity-axe -1/2)
(set-axe-rule-priority getbit-identity-axe -1/2)

;bozo more like this?
(set-axe-rule-priority bvchop-of-bvand -1) ;happens before bvchop-identity to prevent loops?

;these should happen before bv-array-read-of-bv-array-write-tighten:
(set-axe-rule-priority bv-array-read-of-bv-array-write-diff-safe -10)
(set-axe-rule-priority bv-array-read-of-bv-array-write-diff-safe-gen -10) ;thu mar 25 04:05:09 2010
(set-axe-rule-priority bv-array-read-of-bv-array-write-same-gen -10)

;; when rotate unrolling is being done, we prefer these rules:
(set-axe-rule-priority rightrotate-becomes-rightrotate-unroller-strong2 -1)
(set-axe-rule-priority leftrotate-becomes-leftrotate-unroller-strong2 -1)

;; We try these late, since they involve free vars:
(set-axe-rule-priority bvlt-transitive-1-a 1)
(set-axe-rule-priority bvlt-transitive-1-b 1)
(set-axe-rule-priority bvlt-transitive-2-a 1)
(set-axe-rule-priority bvlt-transitive-2-b 1)
(set-axe-rule-priority bvlt-transitive-3-a 1)
(set-axe-rule-priority bvlt-transitive-3-b 1)
(set-axe-rule-priority bvlt-transitive-4-a 1)
(set-axe-rule-priority bvlt-transitive-4-b 1)
(set-axe-rule-priority bvlt-transitive-5-a 1)
(set-axe-rule-priority bvlt-transitive-5-b 1)


;; (defconst *super-rules*
;;   '(
;; ;   slice-of-bvplus-low
;; ;;;    bvplus-trim-arg2-axe
;;  ;;;   bvplus-trim-arg3-axe

;; ;;;    bv-array-write-trim-value
;; ;                                         bv-array-write-of-bvminus-32
;; ;                                        bv-array-write-of-slice-8-31-16
;; ;                                       bv-array-write-of-slice-8-31-8
;; ;;;     LIST-TO-BV-ARRAY
;; ;;;     list-to-bv-array-aux-base
;; ;;;     list-to-bv-array-aux-unroll

;;     ;;bozo restrict to bvcat nests where it's clear?
;;     ;;bozo gen these:
;; ;    BVPLUS-DISJOINT-ONES-32-24-8-TWO
;;  ;   BVPLUS-DISJOINT-ONES-32-24-8
;; ;;;    bvplus-associative
;; ;                                         bvplus-of-bvcat-0-arg2-better
;; ;                                        bvplus-of-bvcat-0-arg1-better

;;     ;; bvplus-when-low-bits-are-zero ;yuck?! ;this rules caused a big slowdown!
;;     bvplus-of-bvcat-0-arg2 ;hmm...
;;     bvplus-of-bvcat-0-arg1 ;hmm...

;; ;;;    bvmult-of-bvplus-trim-arg1
;;   ;;;  bvmult-of-bvplus-trim-arg2
;; ;;;    BVPLUS-1-OF-BVPLUS-TRIM-ARG1
;;   ;;;  BVPLUS-1-OF-BVPLUS-TRIM-ARG2
;;     bvif-blast-when-quoteps
;;     bvplus-of-bvcat-0-hack

;; ;;;    BVMULT-OF-2
;; ;;;    getbit-of-bvplus ;bozo?

;; ;;     BV-ARRAY-WRITE-TRIM-VALUE-all
;; ;;     bvplus-trim-arg1-all
;; ;;     bvplus-trim-arg2-all ;sometime this trims a whole huge nest...
;;     ))

;todo: use this more?
(defun phased-bv-axe-rule-sets (state) ;bozo redo the state stuff here
  (declare (xargs :stobjs state
                  :guard (ilks-plist-worldp (w state))))
;always do this sequence? merge the trim phases into this sequence?
  (list (make-axe-rules! (amazing-rules-bv) (w state))
        (make-axe-rules! (append (amazing-rules-bv) (bit-blast-rules-basic)) (w state))
        ;;we do need to blast the mult of a constant (and the resulting pluses??), it seems
        (make-axe-rules! (append (amazing-rules-bv) (bit-blast-rules)) (w state))))
