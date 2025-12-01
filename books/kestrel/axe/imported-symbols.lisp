; Symbols to import into various Axe packages
;
; Copyright (C) 2017-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This supports packages like the "X" package.

;; In general, we import function names, but not theorem names, from other
;; packages into this package.

;; TODO: Combine some of these lists?

;(include-book "std/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

;; TODO: Add more?
(defconst *axe-tools*
  '(unroll-spec-basic
    unroll-spec

    prove-equal-with-axe
    prove-equality
    prove-with-axe
    prove-equal-with-tactics

    defthm-axe
    defthm-axe-basic
    defthm-stp
    prove-with-stp

    symbolic-byte-assumptions
    symbolic-list
    symbolic-array
    symbolic-byte-list

    byte-types-for-vars
    make-var-names

    set-axe-rule-priority

    def-constant-opener
    defopeners
    add-known-boolean

    defconst-x86
    defconst-computed
    defconst-computed2 ;drop?
    defconst-computed3
    defconst-computed-simple

    def-simplified-basic
    basic ; name of the basic rewriter (may be printed by "The ~x0 rewriter lacks SMT support ...")

    dag-info
    dag-fns
    dag-vars
    dag-size

    ensure-rules-known
    widen-margins
    unwiden-margins

    ;; Testing utilities:
    assert-equal
    deftest
    must-be-redundant ; move
    must-fail ; move

    elf-info

    ))

(defconst *bv-symbols-to-import*
  '(bvchop
    getbit
    bvlt
    bvle
    bvgt
    bvge
    sbvlt
    sbvle
    sbvgt
    sbvge
    bvcat
    bvcat2
    bvplus
    bvminus
    bvuminus
    bvmult
    bvshl
    bvshr
    bvashr
    bvdiv
    sbvdiv
    bvmod
    sbvrem
    slice ;note that we don't get the slice from x86isa
    putbits
    putbit
    putbyte
    trim
    bvcount
    bitxor
    bitnot
    bitand
    bitor
    bvxor
    bvand
    bvor
    bvnot
    bvif
    bvsx
    repeatbit
    leftrotate
    rightrotate
    leftrotate32
    rightrotate32

    unsigned-byte-p-forced
    ))

(defconst *boolean-symbols-to-import*
  '(bit-to-bool
    bool-to-bit
    boolif
    boolor
    booland
    bool-fix
    bool-fix$inline))

(defconst *array-symbols-to-import*
  '(list-to-bv-array
    list-to-bv-array-aux
    list-to-byte-array
    bv-array-to-list
    bv-array-to-list-aux
    bv-array-read
    bv-array-write
    bv-array-read-chunk-little
    bv-arrayp
    array-of-zeros
    bv-array-read-cases
    map-bvplus-val
    map-bvsx))

(defconst *memory-region-symbols*
  '(in-region32p ; todo: move to mem package?
    subregion32p
    disjoint-regions32p
    memory-regionp
    memory-regionsp
    memory-region-addresses-and-lens))

;; Symbols that appear in terms that Axe "knows" about.
;; BV, boolean, and array symbols
(defconst *axe-term-symbols*
  (append *bv-symbols-to-import*
          *boolean-symbols-to-import*
          *array-symbols-to-import*))

(defconst *logops-symbols*
  '(loghead
    loghead$inline
    logtail
    logtail$inline
    logcar
    logcar$inline
    logcdr
    logcdr$inline

    logapp ; not inline
    logmask
    logmask$inline

    expt2 ; used in logapp
    expt2$inline

    ifloor ; used in logtail
    ifloor$inline

    logext

    binary-logand
    binary-logxor
    binary-logior))

(defconst *axe-rule-symbols*
  '(axe-syntaxp
    axe-bind-free
    axe-binding-hyp
    axe-smt
    work-hard ; may not be needed
    axe-rewrite-objective ; may not be needed

    ;; These are for writing axe-syntaxp and axe-bind-free functions:
    pseudo-dag-arrayp
    dargs
    darg1
    darg2
    darg3
    darg4
    dargs

    dag-array ; for calls of axe-syntaxp functions

    ;; axe-syntaxp and axe-bind-free functions:
    bind-bv-size-axe

    syntactic-call-of
    term-should-be-trimmed-axe
    term-should-be-converted-to-bvp
    lighter-dargp
    ))

;; We import these symbols because they may be called in the implementations of
;; the Axe variants.
(defconst *axe-implementation-symbols*
  '(;; Stuff supporting b*
    b*
    when
    patbind-when ; todo: more?
    unless

    *t*
    *nil*
    erp-nil
    erp-t
    enquote
    myquotep
    step-incrementp
    print-levelp
    count-hits-argp
    normalize-xors-optionp
    lifter-targetp
    rule-alistp
    pseudo-dagp
    this-step-increment
    add-limit-for-rules
    limit-for-rule
    simplify-dag-basic
    known-booleans
    real-time-since
    maybe-prune-dag-approximately
    maybe-prune-dag-precisely

    make-term-into-dag-basic
    dag-to-term
    dag-node-to-term
    dag-or-quotep-to-term
    dag-or-quotep-size
    dag-or-quotep-fns
    dag-or-quotep-vars

    remove-assumptions-about
    *non-stp-assumption-functions*
    equivalent-dagsp2
    print-to-hundredths
    print-dag-nicely
    print-dag-nicely-with-base
    print-level-at-least-tp
    print-level-at-least-briefp
    nat-to-string
    defmacrodoc

    ;; todo: organize

    fargs
    ffn-symb
    farg1
    farg2
    farg3
    farg4

    lookup-equal
    lookup-equal-safe
    lookup-eq
    lookup-eq-safe
    lookup
    lookup-safe

    translate-term

    _ ;; used to print non-pure patterns

    simp-dag

    compose-term-and-dag
    compose-term-and-dags
    compose-dags
    make-axe-rules
    make-axe-rules!
    axe-quotep
    result-array-stobj

    nat-to-string
    print-dag-nicely
    print-dag-nicely-with-base
    print-terms-elided
    make-term-into-dag
    remove-assumptions-about
    acl2::*non-stp-assumption-functions*
    ;; simplify-terms-using-each-other
    make-cons-nest ; move?
    make-rule-alist
    make-rule-alist!
    dagify-term
    dagify-term2
    def-simplified-x86
    dag-val-with-axe-evaluator
    defmacrodoc
    simplify-conjunction-basic
    print-to-hundredths
    equivalent-dagsp2
    maybe-add-debug-rules

    call-of
    pack-in-package-of-symbol
    pack-in-package-of-first-symbol
    myif
    extend-progn
    get-vars-from-term
    doublets-to-alist
    translate-term
    translate-terms
    myquotep
    variablep
    empty-alist
    empty-acc
    defforall-simple
    subset-eq
    submit-event
    strip-cadrs

    ;; formal unit tester common stuff:
    print-test-summary
    any-result-unexpectedp

    _  ; for printing non-pure node patterns

    make-event-quiet
    print-list
    print-dag-info
    pack$
    make-acons-nest
    make-interpreted-function-alist
    get-non-built-in-supporting-fns-list
    *axe-evaluator-functions*
    get-conjuncts-of-terms2
    parsed-executablep
    parsed-executable-type

    maybe-remove-temp-dir

    untranslate$
    untranslate$-list

    parse-executable
    parse-elf-file-bytes ; helpful for tracing ; todo: more
    parsed-elfp
    parsed-elf-entry-point
    subroutine-address-elf

    ensure-target-exists-in-executable
    ))

(defconst *arithmetic-symbols*
  '(ceiling-of-lg
    lg
    log2
    power-of-2p))

(defconst *apt-symbols*
  '(;; APT transformations (sometimes used to verify lifted code):
    wrap-output
    extract-output
    rename-params
    flatten-params
    drop-irrelevant-params
    tailrec
    make-tail-rec-bv-up
    make-tail-rec-bv-up2
    def ; handy APT utility
    ))

;; Names of Axe rule-lists
(defconst *axe-rule-lists*
  '(lookup-rules
    list-rules
    core-rules-bv
    amazing-rules-bv
    trim-rules))

(defconst *bv-list-symbols*
  '(packbv-little
    packbvs-little ; todo: more?
    ))

;; todo: classify
(defconst *symbols-from-acl2-package*
  '(;; list and bv-list stuff:
    prefixp
    all-integerp
    all-all-unsigned-byte-p
    all-true-listp
    items-have-len
    all-unsigned-byte-p
    unsigned-byte-listp
    ;; byte-listp ; todo: clash!
    repeat
    bv-list-read-chunk-little ; needed? note that we have bv-array-read-chunk-little

    keyword-listp

    check-arities

    ;; Stuff that can appear in ACL2 rules (but not Axe rules):
    smaller-termp
    want-to-weaken ; for polarity-based reasoning
    want-to-strengthen ; for polarity-based reasoning

    ;; Stuff from ACL2 (TODO: Should these be in *acl2-exports*?):
    my-sublis-var

    define
    __function__
    ///
    defrule

    defpun
    defp

    memberp

    ;; utilities:

    ruleset
    e/d*

    memory-regionp
    memory-regionsp
    memory-region-addresses-and-lens
    ))

;; Ideally, these would all be rewritten to BV ops
(defconst *symbols-from-bitops*
  '(bitops::part-select ; a macro
    bitops::part-select-low-high
    bitops::part-select-low-high$inline
    bitops::part-select-width-low
    bitops::part-select-width-low$inline
    bitops::part-install ; a macro
    bitops::part-install-width-low
    bitops::part-install-width-low$inline
    b-xor ; from ihs, via bitops
    b-xor$inline ; really from ihs
    logbit
    logbit$inline ; really from ihs

    bool->bit$inline
    bool->bit
    bit->bool$inline
    bit->bool

    acl2::bfix
    ;; acl2::bfix$ ; doesn't seem to exist
    acl2::bfix$inline
    ))

;; Ideally, these would all be rewritten away
(defconst *symbols-from-rtl*
  '(rtl::fl
    rtl::bitn
    rtl::bits
    rtl::binary-cat
    rtl::bvecp
    rtl::daz
    rtl::nanp
    rtl::snanp
    rtl::qnanp
    rtl::denormp
    rtl::infp
    rtl::unsupp
    rtl::formatp
    rtl::encodingp
    rtl::explicitp
    rtl::sigw
    rtl::expf
    rtl::sgnf
    rtl::manf
    rtl::sigf
    rtl::prec
    rtl::mxcsr-masks
    ;; rtl::set-flag ; conflict with our set-flag
    rtl::zencode
    rtl::iencode
    rtl::dencode
    rtl::nencode
    rtl::decode
    rtl::ddecode
    rtl::zencode
    rtl::mxcsr-rc))

;; TODO: Think about this...
(defconst *common-acl2-formals*
  '(x y z m n size i
    x1 x2 y1 y2
    free
    freesize
    xsize
    ysize
    lowsize
    highsize
    lowval
    highval
    ;; low high ; can't include these as above we get them from the x86isa package
    size
    size1
    size2))
