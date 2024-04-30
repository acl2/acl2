; Built-Ins Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; This file must not include any other file,
; because we are collecting only the built-in events.

; TODO: get this file to work with ACL2(r)
; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "build/ground-zero-theory.certdep" :dir :system)

; First, we go through the ACL2 world
; and collect all the names introduced by events.
; The world is a list of triples, in reverse chronological order.
; Each triple that starts with EVENT-LANDMARK records an event,
; stored as an event tuple, as described in the ACL2 source code
; (search for "Event Tuples", without quotes, in translate.lisp).
; Based on the documentation on event tuples,
; we collect the names in reverse chronological order
; (which is the natural order in which we go through the world via CDR),
; divided into the following categories:
; - DEFUN/DEFUNS events
; - DEFAXIOM events
; - DEFTHM events
; - DEFCONST events
; - DEFSTOBJ events
; - DEFMACRO events
; - DEFPKG events
; - DEFLABEL events
; - DEFTHEORY events
; - ENCAPSULATE events
; - INCLUDE-BOOK events
; Each category is put into a list returned by the following function;
; the lists are in reverse chronological order, like the triples in the world.
; We put DEFUN and DEFUNS names together, since they are all defined functions.

; Note that we use tail recursion to avoid a stack overflow in Allegro CL and
; perhaps other Lisps that, unlike CCL and SBCL, run interpreted code.  That
; also explains the following set-compile-fns call, which is also necessary for
; Allegro CL and perhaps other Lisps.

(set-compile-fns t)

(defun builtin-event-names-rec (wrld defun-names
                                     defaxiom-names
                                     defthm-names
                                     defconst-names
                                     defstobj-names
                                     defmacro-names
                                     defpkg-names
                                     deflabel-names
                                     deftheory-names
                                     encapsulate-names
                                     includebook-names)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program))
  (if (endp wrld)
      (mv defun-names
          defaxiom-names
          defthm-names
          defconst-names
          defstobj-names
          defmacro-names
          defpkg-names
          deflabel-names
          deftheory-names
          encapsulate-names
          includebook-names)
    (macrolet ((update-event-names
                (pos val)
                (let ((lst '(defun-names
                             defaxiom-names
                             defthm-names
                             defconst-names
                             defstobj-names
                             defmacro-names
                             defpkg-names
                             deflabel-names
                             deftheory-names
                             encapsulate-names
                             includebook-names)))
                  (list* 'builtin-event-names-rec
                         '(cdr wrld)
                         (if pos
                             (update-nth pos val lst)
                           lst)))))
      (let ((triple (car wrld)))
        (if (eq (car triple) 'event-landmark)
            (let* ((event-tuple (cddr triple))
                   (event-type (access-event-tuple-type event-tuple)))
              (cond
               ((eq event-type 'defun)
                (update-event-names
                 0 (cons (access-event-tuple-namex event-tuple)
                         defun-names)))
               ((eq event-type 'defuns)
                (update-event-names
                 0 (revappend (access-event-tuple-namex event-tuple)
                              defun-names)))
               ((eq event-type 'defaxiom)
                (update-event-names
                 1 (cons (access-event-tuple-namex event-tuple)
                         defaxiom-names)))
               ((eq event-type 'defthm)
                (update-event-names
                 2 (cons (access-event-tuple-namex event-tuple)
                         defthm-names)))
               ((eq event-type 'defconst)
                (update-event-names
                 3 (cons (access-event-tuple-namex event-tuple)
                         defconst-names)))
               ((eq event-type 'defstobj)
                (update-event-names
                 4 (cons (car (access-event-tuple-namex event-tuple))
                         defstobj-names)))
               ((eq event-type 'defmacro)
                (update-event-names
                 5 (cons (access-event-tuple-namex event-tuple)
                         defmacro-names)))
               ((eq event-type 'defpkg)
                (update-event-names
                 6 (cons (access-event-tuple-namex event-tuple)
                         defpkg-names)))
               ((eq event-type 'deflabel)
                (update-event-names
                 7 (cons (access-event-tuple-namex event-tuple)
                         deflabel-names)))
               ((eq event-type 'deftheory)
                (update-event-names
                 8 (cons (access-event-tuple-namex event-tuple)
                         deftheory-names)))
               ((eq event-type 'encapsulate)
                (update-event-names
                 9 (revappend (let ((names
                                     (access-event-tuple-namex
                                      event-tuple)))
                                (if (eql names 0)
                                    nil
                                  names))
                              encapsulate-names)))
               ((eq event-type 'include-book)
                (update-event-names 10
                                    (cons (access-event-tuple-namex event-tuple)
                                          includebook-names)))
               (t (update-event-names nil nil))))
          (update-event-names nil nil))))))

(defun builtin-event-names (wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program))
  (builtin-event-names-rec wrld nil nil nil nil nil nil nil nil nil nil nil))

; We introduce a named constants for each list of collected names.
; We reverse the lists, so they are in chronological order.
; Since the two functions above that collect the names are themselves collected,
; we remove them just before defining the named constant for function names.
; the SET-COMPILE-FNS form does not cause any events, it just modifies a table.

(make-event
 (mv-let (defun-names
          defaxiom-names
          defthm-names
          defconst-names
          defstobj-names
          defmacro-names
          defpkg-names
          deflabel-names
          deftheory-names
          encapsulate-names
          includebook-names)
     (builtin-event-names (w state))
   `(progn
      (defconst *builtin-defun-names* ',(reverse (cddr defun-names)))
      (defconst *builtin-defaxiom-names* ',(reverse defaxiom-names))
      (defconst *builtin-defthm-names* ',(reverse defthm-names))
      (defconst *builtin-defconst-names* ',(reverse defconst-names))
      (defconst *builtin-defstobj-names* ',(reverse defstobj-names))
      (defconst *builtin-defmacro-names* ',(reverse defmacro-names))
      (defconst *builtin-defpkg-names* ',(reverse defpkg-names))
      (defconst *builtin-deflabel-names* ',(reverse deflabel-names))
      (defconst *builtin-deftheory-names* ',(reverse deftheory-names))
      (defconst *builtin-encapsulate-names* ',(reverse encapsulate-names))
      (defconst *builtin-includebook-names* ',(reverse includebook-names)))))

; There are no built-in DEFSTOBJ events
; (apparently, STATE is handled specially),
; and there are no built-in INCLUDE-BOOK events
; (which makes sense, since the system is made of source files, not books).
; We add assertions to this effect, so that if ACL2 ever changes
; in a way that these lists are no longer empty, we can detect it.

#-acl2data ; The following assertion is false for certain "acl2data" runs.
(assert-event (and (null *builtin-defstobj-names*)
                   (null *builtin-includebook-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Divide the DEFUN/DEFUNS events into logic-mode and program-mode.

(defun builtin-logic/program-defun-names (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp names)
      (mv nil nil)
    (mv-let (logic-names program-names)
        (builtin-logic/program-defun-names (cdr names) wrld)
      (let ((name (car names)))
        (if (logicp name wrld)
            (mv (cons name logic-names)
                program-names)
          (mv logic-names
              (cons name program-names)))))))

(make-event
 (mv-let (logic-names program-names)
     (builtin-logic/program-defun-names *builtin-defun-names* (w state))
   `(progn
      (defconst *builtin-logic-defun-names* ',logic-names)
      (defconst *builtin-program-defun-names* ',program-names))))

; We introduce a named constant for
; all the axioms and theorems with no rule classes.

(defun builtin-noclass-defaxiom/defthm-names (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp names)
      nil
    (let* ((noclass-names
            (builtin-noclass-defaxiom/defthm-names (cdr names) wrld))
           (name (car names)))
      (if (null (getpropc name 'classes nil wrld))
          (cons name noclass-names)
        noclass-names))))

(make-event
 (let ((names (builtin-noclass-defaxiom/defthm-names
               (append *builtin-defaxiom-names*
                       *builtin-defthm-names*)
               (w state))))
   `(defconst *builtin-noclass-defaxiom/defthm-names* ',names)))

; We introduce a named constant for
; all the axioms and theorems with each of the possible rule classes.

(defun builtin-rule-of-class-p (classes class-keyword)
  (declare (xargs :guard (and (true-listp classes)
                              (keywordp class-keyword))
                  :mode :program))
  (and (not (endp classes))
       (let ((class (car classes)))
         (or (eq (car class) class-keyword)
             (builtin-rule-of-class-p (cdr classes) class-keyword)))))

(defun builtin-defaxiom/defthm-names-of-class (names class-keyword wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (keywordp class-keyword)
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp names)
      nil
    (let* ((rules (builtin-defaxiom/defthm-names-of-class (cdr names)
                                                          class-keyword
                                                          wrld))
           (name (car names)))
      (if (builtin-rule-of-class-p (getpropc name 'classes nil wrld)
                                   class-keyword)
          (cons name rules)
        rules))))

(defun builtin-rule-of-class-defconst-fn (class-keyword state)
  (declare (xargs :guard (keywordp class-keyword)
                  :stobjs state
                  :mode :program))
  (let* ((rules (builtin-defaxiom/defthm-names-of-class
                 (append *builtin-defaxiom-names*
                         *builtin-defthm-names*)
                 class-keyword
                 (w state)))
         (const-name (packn-pos (list '*builtin-
                                      class-keyword
                                      '-defaxiom/defthm-names*)
                                (pkg-witness "ACL2"))))
    `(defconst ,const-name ',rules)))

(defmacro builtin-rule-of-class-defconst (class-keyword)
  (declare (xargs :guard (keywordp class-keyword)))
  `(make-event (builtin-rule-of-class-defconst-fn ,class-keyword state)))

(progn
  (builtin-rule-of-class-defconst :rewrite)
  (builtin-rule-of-class-defconst :rewrite-quoted-constant)
  (builtin-rule-of-class-defconst :built-in-clause)
  (builtin-rule-of-class-defconst :clause-processor)
  (builtin-rule-of-class-defconst :compound-recognizer)
  (builtin-rule-of-class-defconst :congruence)
  (builtin-rule-of-class-defconst :definition)
  (builtin-rule-of-class-defconst :elim)
  (builtin-rule-of-class-defconst :equivalence)
  (builtin-rule-of-class-defconst :forward-chaining)
  (builtin-rule-of-class-defconst :generalize)
  (builtin-rule-of-class-defconst :induction)
  (builtin-rule-of-class-defconst :linear)
  (builtin-rule-of-class-defconst :meta)
  (builtin-rule-of-class-defconst :refinement)
  (builtin-rule-of-class-defconst :tau-system)
  (builtin-rule-of-class-defconst :type-prescription)
  (builtin-rule-of-class-defconst :type-set-inverter)
  (builtin-rule-of-class-defconst :well-founded-relation))

(assert-event
 (and (null *builtin-rewrite-quoted-constant-defaxiom/defthm-names*)
      (null *builtin-built-in-clause-defaxiom/defthm-names*)
      (null *builtin-clause-processor-defaxiom/defthm-names*)
      (null *builtin-generalize-defaxiom/defthm-names*)
      (null *builtin-induction-defaxiom/defthm-names*)
      (null *builtin-meta-defaxiom/defthm-names*)
      (null *builtin-refinement-defaxiom/defthm-names*)
      (null *builtin-type-set-inverter-defaxiom/defthm-names*)
      (null *builtin-well-founded-relation-defaxiom/defthm-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce named constants for lists of axioms and theorems
; that concern certain types or functions.
; The lists are not necessarily disjoint,
; as an axiom or theorem may relate different types or functions.
; There are a lot of axioms and theorems,
; not all of which have been examined in great detail
; as this categorization was made:
; it is possible that something is somewhat out of place and should be moved.
; The following constants are named *builtin-defaxiom/defthm-<topic>*,
; where <topic> describes a type or function.

(defconst *builtin-defaxiom/defthm-logical-connectives*
  '(iff-is-an-equivalence
    iff-implies-equal-implies-1
    iff-implies-equal-implies-2
    iff-implies-equal-not))

(defconst *builtin-defaxiom/defthm-booleans*
  '(booleanp-compound-recognizer
    boolean-listp-cons
    boolean-listp-forward
    boolean-listp-forward-to-symbol-listp))

(defconst *builtin-defaxiom/defthm-cons-pairs*
  '(car-cdr-elim
    car-cons
    cdr-cons
    cons-equal
    completion-of-car
    completion-of-cdr
    default-car
    default-cdr
    cons-car-cdr))

(defconst *builtin-defaxiom/defthm-numbers*
  '(closure
    associativity-of-+
    commutativity-of-+
    unicity-of-0
    inverse-of-+
    associativity-of-*
    commutativity-of-*
    unicity-of-1
    inverse-of-*
    distributivity
    <-on-others
    zero
    trichotomy
    positive
    rational-implies1
    rational-implies2
    integer-implies-rational
    complex-implies1
    complex-definition
    nonzero-imagpart
    realpart-imagpart-elim
    realpart-complex
    imagpart-complex
    nonnegative-product
    integer-0
    integer-1
    integer-step
    lowest-terms
    completion-of-+
    completion-of-*
    completion-of-unary-minus
    completion-of-unary-/
    completion-of-<
    completion-of-complex
    completion-of-numerator
    completion-of-denominator
    completion-of-realpart
    completion-of-imagpart
    zp-compound-recognizer
    zp-open
    zip-compound-recognizer
    zip-open
    complex-equal
    natp-compound-recognizer
    bitp-compound-recognizer
    posp-compound-recognizer
    expt-type-prescription-non-zero-base
    rationalp-expt-type-prescription
    integer-range-p-forward
    signed-byte-p-forward-to-integerp
    unsigned-byte-p-forward-to-nonnegative-integerp
    rationalp-+
    rationalp-*
    rationalp-unary--
    rationalp-unary-/
    rationalp-implies-acl2-numberp
    default-+-1
    default-+-2
    default-*-1
    default-*-2
    default-unary-minus
    default-unary-/
    default-<-1
    default-<-2
    default-complex-1
    default-complex-2
    complex-0
    add-def-complex
    realpart-+
    imagpart-+
    default-numerator
    default-denominator
    default-realpart
    default-imagpart
    commutativity-2-of-+
    fold-consts-in-+
    distributivity-of-minus-over-+
    pos-listp-forward-to-integer-listp))

(defconst *builtin-defaxiom/defthm-dfs*
  '(stringp-df-string
    to-dfp-of-rize to-df-of-df-rationalize
    rationalp-df-rationalize rationalp-df-pi
    dfp-df-pi rationalp-df-abs-fn
    dfp-df-abs-fn rationalp-df-atanh-fn
    dfp-df-atanh-fn rationalp-df-acosh-fn
    dfp-df-acosh-fn rationalp-df-asinh-fn
    dfp-df-asinh-fn rationalp-df-tanh-fn
    dfp-df-tanh-fn rationalp-df-cosh-fn
    dfp-df-cosh-fn rationalp-df-sinh-fn
    dfp-df-sinh-fn rationalp-df-atan-fn
    dfp-df-atan-fn rationalp-df-acos-fn
    dfp-df-acos-fn rationalp-df-asin-fn
    dfp-df-asin-fn rationalp-df-tan-fn
    dfp-df-tan-fn rationalp-df-cos-fn
    dfp-df-cos-fn rationalp-df-sin-fn
    dfp-df-sin-fn rationalp-unary-df-log
    dfp-unary-df-log rationalp-binary-df-log
    dfp-binary-df-log
    rationalp-df-sqrt-fn dfp-df-sqrt-fn
    rationalp-df-exp-fn dfp-df-exp-fn
    rationalp-df-expt-fn dfp-df-expt-fn
    stringp-constrained-df-string
    to-df-of-constrained-df-rationalize
    rationalp-constrained-df-rationalize
    rationalp-constrained-df-pi
    dfp-constrained-df-pi
    rationalp-constrained-df-abs-fn
    dfp-constrained-df-abs-fn
    rationalp-constrained-df-atanh-fn
    dfp-constrained-df-atanh-fn
    rationalp-constrained-df-acosh-fn
    dfp-constrained-df-acosh-fn
    rationalp-constrained-df-asinh-fn
    dfp-constrained-df-asinh-fn
    rationalp-constrained-df-tanh-fn
    dfp-constrained-df-tanh-fn
    rationalp-constrained-df-cosh-fn
    dfp-constrained-df-cosh-fn
    rationalp-constrained-df-sinh-fn
    dfp-constrained-df-sinh-fn
    rationalp-constrained-df-atan-fn
    dfp-constrained-df-atan-fn
    rationalp-constrained-df-acos-fn
    dfp-constrained-df-acos-fn
    rationalp-constrained-df-asin-fn
    dfp-constrained-df-asin-fn
    rationalp-constrained-df-tan-fn
    dfp-constrained-df-tan-fn
    rationalp-constrained-df-cos-fn
    dfp-constrained-df-cos-fn
    rationalp-constrained-df-sin-fn
    dfp-constrained-df-sin-fn
    rationalp-constrained-unary-df-log
    dfp-constrained-unary-df-log
    rationalp-constrained-binary-df-log
    dfp-constrained-binary-df-log
    rationalp-constrained-df-sqrt-fn
    dfp-constrained-df-sqrt-fn
    rationalp-constrained-df-exp-fn
    dfp-constrained-df-exp-fn
    rationalp-constrained-df-expt-fn
    dfp-constrained-df-expt-fn
    dfp-implies-to-df-is-identity
    dfp-implies-rationalp
    dfp-minus
    dfp-to-df
    to-df-default to-df-idempotent
    rationalp-to-df constrained-to-df-0
    constrained-to-df-default
    constrained-to-df-idempotent
    constrained-to-df-monotonicity
    rationalp-constrained-to-df
    df-round-idempotent
    df-round-monotonicity
    df-round-is-identity-for-dfp
    dfp-df-round
    rationalp-df-round
    to-df-minus
    to-df-monotonicity))

(defconst *builtin-defaxiom/defthm-characters*
  '(booleanp-characterp
    characterp-page
    characterp-tab
    characterp-rubout
    characterp-return
    char-code-linear
    code-char-type
    code-char-char-code-is-identity
    char-code-code-char-is-identity
    completion-of-char-code
    completion-of-code-char
    lower-case-p-char-downcase
    upper-case-p-char-upcase
    lower-case-p-forward-to-alpha-char-p
    upper-case-p-forward-to-alpha-char-p
    alpha-char-p-forward-to-standard-char-p
    standard-char-p-forward-to-characterp
    characterp-char-downcase
    characterp-char-upcase
    characterp-nth
    standard-char-listp-append
    character-listp-append
    character-listp-remove-duplicates
    character-listp-revappend
    standard-char-p-nth
    equal-char-code
    default-char-code
    default-code-char
    make-character-list-make-character-list
    true-listp-explode-atom))

(defconst *builtin-defaxiom/defthm-strings*
  '(coerce-inverse-1
    coerce-inverse-2
    character-listp-coerce
    completion-of-coerce
    string<-irreflexive
    stringp-substitute-type-prescription
    true-listp-substitute-type-prescription
    true-listp-explode-nonnegative-integer
    stringp-subseq-type-prescription
    true-listp-subseq-type-prescription
    default-coerce-1
    default-coerce-2
    default-coerce-3
    character-listp-string-downcase-1
    character-listp-string-upcase1-1
    string<-l-irreflexive
    string<-l-asymmetric
    string<-l-transitive
    string<-l-trichotomy))

(defconst *builtin-defaxiom/defthm-symbols*
  '(stringp-symbol-package-name
    symbolp-intern-in-package-of-symbol
    symbolp-pkg-witness
    intern-in-package-of-symbol-symbol-name
    symbol-name-pkg-witness
    symbol-package-name-pkg-witness-name
    symbol-name-intern-in-package-of-symbol
    symbol-package-name-intern-in-package-of-symbol
    intern-in-package-of-symbol-is-identity
    symbol-listp-pkg-imports
    no-duplicatesp-eq-pkg-imports
    completion-of-pkg-imports
    acl2-input-channel-package
    acl2-output-channel-package
    acl2-package
    keyword-package
    string-is-not-circular
    nil-is-not-circular
    completion-of-intern-in-package-of-symbol
    completion-of-symbol-name
    completion-of-symbol-package-name
    keywordp-forward-to-symbolp
    symbol-package-name-of-symbol-is-not-empty-string
    symbol-equality
    default-pkg-imports
    symbol<-asymmetric
    symbol<-transitive
    symbol<-trichotomy
    symbol<-irreflexive
    default-intern-in-package-of-symbol
    default-symbol-name
    default-symbol-package-name
    symbol-listp-cdr-assoc-equal
    symbol-listp-strict-merge-sort-symbol<))

(defconst *builtin-defaxiom/defthm-bad-atoms*
  '(booleanp-bad-atom<=
    bad-atom<=-antisymmetric
    bad-atom<=-transitive
    bad-atom<=-total
    bad-atom-compound-recognizer))

(defconst *builtin-defaxiom/defthm-eqlables*
  '(eqlablep-recog
    eqlablep-nth))

(defconst *builtin-defaxiom/defthm-lists*
  '(symbol-listp-forward-to-eqlable-listp
    eqlable-listp-forward-to-atom-listp
    atom-listp-forward-to-true-listp
    true-listp-append
    append-to-nil
    character-listp-forward-to-eqlable-listp
    standard-char-listp-forward-to-character-listp
    atom-listp-forward-to-true-listp
    eqlable-listp-forward-to-atom-listp
    true-listp-revappend-type-prescription
    keyword-value-listp-forward-to-true-listp
    true-list-listp-forward-to-true-listp
    true-listp-nthcdr-type-prescription
    keyword-value-listp-assoc-keyword
    acl2-number-listp-forward-to-true-listp
    rational-listp-forward-to-acl2-number-listp
    integer-listp-forward-to-rational-listp
    nat-listp-forward-to-integer-listp
    nth-update-nth
    true-listp-update-nth
    nth-update-nth-array
    len-update-nth
    nth-0-cons
    nth-add1
    last-cdr-is-nil
    pairlis$-true-list-fix
    true-listp-first-n-ac-type-prescription
    natp-position-ac-eq-exec
    natp-position-ac-eql-exec
    natp-position-equal-ac
    natp-position-ac
    position-ac-eq-exec-is-position-equal-ac
    position-ac-eql-exec-is-position-equal-ac
    position-eq-exec-is-position-equal
    position-eql-exec-is-position-equal
    member-eq-exec-is-member-equal
    member-eql-exec-is-member-equal
    subsetp-eq-exec-is-subsetp-equal
    subsetp-eql-exec-is-subsetp-equal
    no-duplicatesp-eq-exec-is-no-duplicatesp-equal
    no-duplicatesp-eql-exec-is-no-duplicatesp-equal
    remove-eq-exec-is-remove-equal
    remove-eql-exec-is-remove-equal
    remove1-eq-exec-is-remove1-equal
    remove1-eql-exec-is-remove1-equal
    remove-duplicates-eq-exec-is-remove-duplicates-equal
    remove-duplicates-eql-exec-is-remove-duplicates-equal
    set-difference-eq-exec-is-set-difference-equal
    set-difference-eql-exec-is-set-difference-equal
    add-to-set-eq-exec-is-add-to-set-equal
    add-to-set-eql-exec-is-add-to-set-equal
    union-eq-exec-is-union-equal
    union-eql-exec-is-union-equal
    intersectp-eq-exec-is-intersectp-equal
    intersectp-eql-exec-is-intersectp-equal
    intersection-eq-exec-is-intersection-equal
    intersection-eql-exec-is-intersection-equal
    pairlis$-tailrec-is-pairlis$
    resize-list-exec-is-resize-list
    typed-io-listp-forward-to-true-listp))

(defconst *builtin-defaxiom/defthm-alists*
  '(alistp-forward-to-true-listp
    eqlable-alistp-forward-to-alistp
    symbol-alistp-forward-to-eqlable-alistp
    character-alistp-forward-to-eqlable-alistp
    nat-alistp-forward-to-eqlable-alistp
    fixnat-alistp-forward-to-nat-alistp
    standard-string-alistp-forward-to-alistp
    consp-assoc-equal
    known-package-alistp-forward-to-true-list-listp-and-alistp
    true-list-listp-forward-to-true-listp-assoc-equal
    ordered-symbol-alistp-forward-to-symbol-alistp
    ordered-symbol-alistp-remove1-assoc-eq
    ordered-symbol-alistp-add-pair
    ordered-symbol-alistp-add-pair-forward
    assoc-add-pair
    add-pair-preserves-all-boundp
    bounded-integer-alistp-forward-to-eqlable-alistp
    assoc-eq-exec-is-assoc-equal
    assoc-eql-exec-is-assoc-equal
    rassoc-eq-exec-is-rassoc-equal
    rassoc-eql-exec-is-rassoc-equal
    remove1-assoc-eq-exec-is-remove1-assoc-equal
    remove1-assoc-eql-exec-is-remove1-assoc-equal
    remove-assoc-eq-exec-is-remove-assoc-equal
    remove-assoc-eql-exec-is-remove-assoc-equal
    put-assoc-eq-exec-is-put-assoc-equal
    put-assoc-eql-exec-is-put-assoc-equal
    timer-alistp-forward-to-true-list-listp-and-symbol-alistp
    all-boundp-preserves-assoc-equal))

(defconst *builtin-defaxiom/defthm-arrays*
  '(array1p-forward
    array1p-linear
    array2p-forward
    array2p-linear
    array1p-cons
    array2p-cons))

(defconst *builtin-defaxiom/defthm-total-order*
  '(alphorder-reflexive
    alphorder-anti-symmetric
    alphorder-transitive
    alphorder-total
    lexorder-reflexive
    lexorder-anti-symmetric
    lexorder-transitive
    lexorder-total
    true-listp-merge-sort-lexorder))

(defconst *builtin-defaxiom/defthm-ordinals*
  '(o-p-implies-o<g
    acl2-count-car-cdr-linear))

(defconst *builtin-defaxiom/defthm-random$*
  '(natp-random$
    random$-linear))

(defconst *builtin-defaxiom/defthm-io*
  '(open-channel1-forward-to-true-listp-and-consp
    open-channels-p-forward
    true-listp-cadr-assoc-eq-for-open-channels-p
    file-clock-p-forward-to-integerp
    readable-file-forward-to-true-listp-and-consp
    readable-files-listp-forward-to-true-list-listp-and-alistp
    readable-files-p-forward-to-readable-files-listp
    written-file-forward-to-true-listp-and-consp
    written-file-listp-forward-to-true-list-listp-and-alistp
    written-files-p-forward-to-written-file-listp
    read-file-listp1-forward-to-true-listp-and-consp
    read-file-listp-forward-to-true-list-listp
    read-files-p-forward-to-read-file-listp
    writable-file-listp1-forward-to-true-listp-and-consp
    writable-file-listp-forward-to-true-list-listp
    writeable-files-p-forward-to-writable-file-listp
    canonical-pathname-is-idempotent
    canonical-pathname-type))

(defconst *builtin-defaxiom/defthm-system-utilities*
  '(pseudo-term-listp-forward-to-true-listp
    legal-variable-or-constant-namep-implies-symbolp
    termp-implies-pseudo-termp
    term-listp-implies-pseudo-term-listp
    arities-okp-implies-arity
    arities-okp-implies-logicp
    pseudo-termp-consp-forward
    plist-worldp-forward-to-assoc-eq-equal-alistp
    state-p1-forward
    state-p-implies-and-forward-to-state-p1
    update-acl2-oracle-preserves-state-p1
    read-run-time-preserves-state-p1
    read-acl2-oracle-preserves-state-p1
    nth-0-read-run-time-type-prescription
    ordered-symbol-alistp-getprops
    state-p1-update-main-timer
    state-p1-update-print-base
    state-p1-update-nth-2-world
    pseudo-term-listp-mfc-clause
    type-alistp-mfc-type-alist
    fn-count-evg-rec-type-prescription
    fn-count-evg-rec-bound fn-count-1-type
    integerp-nth-0-var-fn-count-1
    integerp-nth-1-var-fn-count-1
    integerp-nth-2-var-fn-count-1
    ancestors-check-builtin-property
    ancestors-check-constraint
    natp-conjoin-clause-sets-bound
    d-pos-listp-forward-to-true-listp
    true-listp-chars-for-tilde-@-clause-id-phrase/periods
    state-p1-read-acl2-oracle
    all-boundp-initial-global-table
    all-boundp-initial-global-table-alt))

(defconst *builtin-defaxiom/defthm-tau*
  '(basic-tau-rules
    bitp-as-inequality))

(defconst *builtin-defaxiom/defthm-apply$*
  '(all-function-symbolps-ev-fncall+-fns
    ev-fncall+-fns-is-subset-of-badged-fns-of-world
    function-symbolp-ev-fncall+-fns-strictp
    doppelganger-badge-userfn-type
    doppelganger-apply$-userfn-takes-arity-args
    badge-userfn-type
    apply$-userfn-takes-arity-args
    untame-apply$-takes-arity-args
    apply$-equivalence-necc
    fn-equal-is-an-equivalence
    natp-from-to-by-measure
    apply$-warrant-until$-ac-definition
    apply$-warrant-until$-ac-necc
    apply$-until$-ac
    fn-equal-implies-equal-until$-ac-1
    apply$-warrant-until$-definition
    apply$-warrant-until$-necc
    apply$-until$
    fn-equal-implies-equal-until$-1
    apply$-warrant-until$+-ac-definition
    apply$-warrant-until$+-ac-necc
    apply$-until$+-ac
    fn-equal-implies-equal-until$+-ac-1
    apply$-warrant-until$+-definition
    apply$-warrant-until$+-necc
    apply$-until$+
    fn-equal-implies-equal-until$+-1
    apply$-warrant-when$-ac-definition
    apply$-warrant-when$-ac-necc
    apply$-when$-ac
    fn-equal-implies-equal-when$-ac-1
    apply$-warrant-when$-definition
    apply$-warrant-when$-necc
    apply$-when$
    fn-equal-implies-equal-when$-1
    apply$-warrant-when$+-ac-definition
    apply$-warrant-when$+-ac-necc
    apply$-when$+-ac
    fn-equal-implies-equal-when$+-ac-1
    apply$-warrant-when$+-definition
    apply$-warrant-when$+-necc
    apply$-when$+
    fn-equal-implies-equal-when$+-1
    apply$-warrant-sum$-ac-definition
    apply$-warrant-sum$-ac-necc
    apply$-sum$-ac
    fn-equal-implies-equal-sum$-ac-1
    apply$-warrant-sum$-definition
    apply$-warrant-sum$-necc
    apply$-sum$
    fn-equal-implies-equal-sum$-1
    apply$-warrant-sum$+-ac-definition
    apply$-warrant-sum$+-ac-necc
    apply$-sum$+-ac
    fn-equal-implies-equal-sum$+-ac-1
    apply$-warrant-sum$+-definition
    apply$-warrant-sum$+-necc
    apply$-sum$+
    fn-equal-implies-equal-sum$+-1
    apply$-warrant-always$-definition
    apply$-warrant-always$-necc
    apply$-always$
    fn-equal-implies-equal-always$-1
    apply$-warrant-always$+-definition
    apply$-warrant-always$+-necc
    apply$-always$+
    fn-equal-implies-equal-always$+-1
    apply$-warrant-thereis$-definition
    apply$-warrant-thereis$-necc
    apply$-thereis$
    fn-equal-implies-equal-thereis$-1
    apply$-warrant-thereis$+-definition
    apply$-warrant-thereis$+-necc
    apply$-thereis$+
    fn-equal-implies-equal-thereis$+-1
    apply$-warrant-collect$-ac-definition
    apply$-warrant-collect$-ac-necc
    apply$-collect$-ac
    fn-equal-implies-equal-collect$-ac-1
    apply$-warrant-collect$-definition
    apply$-warrant-collect$-necc
    apply$-collect$
    fn-equal-implies-equal-collect$-1
    apply$-warrant-collect$+-ac-definition
    apply$-warrant-collect$+-ac-necc
    apply$-collect$+-ac
    fn-equal-implies-equal-collect$+-ac-1
    apply$-warrant-collect$+-definition
    apply$-warrant-collect$+-necc
    apply$-collect$+
    fn-equal-implies-equal-collect$+-1
    apply$-warrant-append$-ac-definition
    apply$-warrant-append$-ac-necc
    apply$-append$-ac
    fn-equal-implies-equal-append$-ac-1
    apply$-warrant-append$-definition
    apply$-warrant-append$-necc
    apply$-append$
    fn-equal-implies-equal-append$-1
    apply$-warrant-append$+-ac-definition
    apply$-warrant-append$+-ac-necc
    apply$-append$+-ac
    fn-equal-implies-equal-append$+-ac-1
    apply$-warrant-append$+-definition
    apply$-warrant-append$+-necc
    apply$-append$+
    fn-equal-implies-equal-append$+-1
    apply$-warrant-mempos-definition
    apply$-warrant-mempos-necc
    apply$-mempos
    apply$-warrant-d<-definition
    apply$-warrant-d<-necc
    apply$-d<
    apply$-warrant-l<-definition
    apply$-warrant-l<-necc
    apply$-l<
    apply$-warrant-nfix-list-definition
    apply$-warrant-nfix-list-necc
    apply$-nfix-list
    apply$-warrant-lex-fix-definition
    apply$-warrant-lex-fix-necc
    apply$-lex-fix
    apply$-warrant-lexp-definition
    apply$-warrant-lexp-necc
    apply$-lexp
    apply$-warrant-do$-definition
    apply$-warrant-do$-necc
    apply$-do$
    fn-equal-implies-equal-do$-1
    fn-equal-implies-equal-do$-3
    fn-equal-implies-equal-do$-4
    apply$-eviscerate-do$-alist apply$-warrant-eviscerate-do$-alist-necc
    apply$-warrant-eviscerate-do$-alist-definition
    apply$-stobj-print-name
    apply$-warrant-stobj-print-name-necc
    apply$-warrant-stobj-print-name-definition
    apply$-loop$-default-values apply$-warrant-loop$-default-values-necc
    apply$-warrant-loop$-default-values-definition
    apply$-loop$-default-values1
    apply$-warrant-loop$-default-values1-necc
    apply$-warrant-loop$-default-values1-definition
))

; Put all the above names together, and check that
; (1) they are all built-in axiom and theorem names and
; (2) they cover all the builtin axiom and theorem names.

(defconst *builtin-defaxiom/defthm-all*
  (append *builtin-defaxiom/defthm-logical-connectives*
          *builtin-defaxiom/defthm-booleans*
          *builtin-defaxiom/defthm-cons-pairs*
          *builtin-defaxiom/defthm-numbers*
          *builtin-defaxiom/defthm-dfs*
          *builtin-defaxiom/defthm-characters*
          *builtin-defaxiom/defthm-strings*
          *builtin-defaxiom/defthm-symbols*
          *builtin-defaxiom/defthm-bad-atoms*
          *builtin-defaxiom/defthm-eqlables*
          *builtin-defaxiom/defthm-lists*
          *builtin-defaxiom/defthm-alists*
          *builtin-defaxiom/defthm-arrays*
          *builtin-defaxiom/defthm-total-order*
          *builtin-defaxiom/defthm-ordinals*
          *builtin-defaxiom/defthm-random$*
          *builtin-defaxiom/defthm-io*
          *builtin-defaxiom/defthm-system-utilities*
          *builtin-defaxiom/defthm-tau*
          *builtin-defaxiom/defthm-apply$*))

(assert-event (subsetp-eq *builtin-defaxiom/defthm-all*
                          (append *builtin-defaxiom-names*
                                  *builtin-defthm-names*)))

#-acl2data ; The following assertion is false for certain "acl2data" runs.
(assert-event (subsetp-eq (append *builtin-defaxiom-names*
                                  *builtin-defthm-names*)
                          *builtin-defaxiom/defthm-all*))
