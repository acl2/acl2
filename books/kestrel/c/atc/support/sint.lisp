; Rules abut C sints (helpful for derivations)
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Karthik Nukala (nukala@kestrel.edu)
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/c/representation/integer-operations" :dir :system)
(include-book "kestrel/c/atc/let-designations" :dir :system) ; for assign and declar
(local (include-book "kestrel/c/atc/symbolic-execution-rules/integers" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable (:e sint-from-integer)
                    (:e sint-dec-const) ; ensures these are retained by simplify
                    (:e sint-hex-const)
                    (:e sint-oct-const)))

(local (in-theory (enable int-bits sint-integerp sint-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm sint-integerp-forward-to-upper-bound
  (implies (sint-integerp x)
           (<= x 2147483647))
  :rule-classes :forward-chaining)

(defthm sint-integerp-forward-to-lower-bound
  (implies (sint-integerp x)
           (<= -2147483648 x))
  :rule-classes :forward-chaining)

(defthm sint-integer-fix-upper-bound-linear
  (<= (sint-integer-fix x) 2147483647)
  :rule-classes :linear)

(defthm sint-integer-fix-lower-bound-linear
  (<= -2147483648 (sint-integer-fix x))
  :rule-classes :linear)

(defthm signed-byte-p-of-sint-integer-fix
  (implies (and (<= 32 size)
                (integerp size))
           (signed-byte-p size (sint-integer-fix y)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm integer-from-sint-upper-bound-linear
  (<= (integer-from-sint x) 2147483647)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-sint))))

(defthm integer-from-sint-lower-bound-linear
  (<= -2147483648 (integer-from-sint x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-sint))))

(defthm signed-byte-p-of-integer-from-sint
  (implies (and (<= 32 size)
                (integerp size))
           (signed-byte-p size (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable integer-from-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion, etc.

;; Note that integer-from-sint-of-sint-from-integer is built in to ATC

(defthm integer-from-sint-of-sint-dec-const
  (equal (integer-from-sint (sint-dec-const x))
         (sint-integer-fix x))
  :hints (("Goal" :in-theory (enable integer-from-sint
                                     sint-dec-const))))

(defthm integer-from-cinteger-of-sint-dec-const
  (equal (integer-from-cinteger (sint-dec-const x))
         (sint-integer-fix x))
  :hints (("Goal" :in-theory (enable integer-from-cinteger-alt-def sint-dec-const))))

(defthm integer-from-cinteger-of-sint-from-integer
  (equal (integer-from-cinteger (sint-from-integer x))
         (sint-integer-fix x))
  :hints (("Goal" :in-theory (enable integer-from-cinteger-alt-def sint-dec-const))))

;; what about when x or y is a constant?
(defthmd equal-of-integer-from-sint-and-integer-from-sint
  (equal (equal (integer-from-sint x) (integer-from-sint y))
         (equal (sint-fix x) (sint-fix y)))
  :hints (("Goal" :in-theory (enable integer-from-sint sint-fix))))

;; In case we are not rewriting either way:
(defthm equal-of-sint-from-integer-and-sint-dec-const
  (equal (equal (sint-from-integer x) (sint-dec-const x))
         t)
  :hints (("Goal" :in-theory (enable sint-dec-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants

;; Turn sint-from-integer into sint-dec-const (necessary for ATC) when the argument is
;; a quoted constant.  Not clear if this should always be enabled.
(defthmd sint-from-integer-becomes-sint-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (sint-from-integer x)
                  (sint-dec-const x)))
  :hints (("Goal" :in-theory (enable sint-dec-const))))

(theory-invariant (incompatible (:rewrite sint-from-integer-becomes-sint-dec-const-when-constant)
                                (:definition sint-dec-const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm sint-integer-fix-when-not-sint-integerp
  (implies (not (sint-integerp x))
           (equal (sint-integer-fix x)
                  0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd boolean-from-sint-of-sint-dec-const
  (equal (boolean-from-sint (sint-dec-const k))
         (not (equal (sint-integer-fix k) 0)))
  :hints (("Goal" :in-theory (enable boolean-from-sint))))

(defthmd boolean-from-sint-of-sint-from-integer
  (equal (boolean-from-sint (sint-from-integer k))
         (not (equal (sint-integer-fix k) 0)))
  :hints (("Goal" :in-theory (enable boolean-from-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts add-sint-sint to +.
(defthmd integer-from-sint-of-add-sint-sint
  (equal (integer-from-sint (add-sint-sint x y))
         (if (add-sint-sint-okp x y)
             (+ (integer-from-sint x) (integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable add-sint-sint
                                     add-sint-sint-okp))))

;; Alternate phrasing
;; (defthmd integer-from-sint-of-add-sint-sint-strong
;;   (equal (integer-from-sint (add-sint-sint x y))
;;          (sint-integer-fix (+ (integer-from-sint x) (integer-from-sint y))))
;;   :hints (("Goal" :in-theory (enable add-sint-sint))))

;; Converts minus-sint to unary -.
(defthmd integer-from-sint-of-minus-sint
  (implies (minus-sint-okp x)
           (equal (integer-from-sint (minus-sint x))
                  (- (integer-from-sint x))))
  :hints (("Goal" :in-theory (enable minus-sint
                                     minus-sint-okp))))

;; Converts sub-sint-sint to -.
(defthmd integer-from-sint-of-sub-sint-sint
  (equal (integer-from-sint (sub-sint-sint x y))
         (if (sub-sint-sint-okp x y) ;todo: expand?
             (- (integer-from-sint x) (integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable sub-sint-sint sub-sint-sint-okp))))

;; Converts mul-sint-sint to *.
(defthmd integer-from-sint-of-mul-sint-sint
  (equal (integer-from-sint (mul-sint-sint x y))
         (if (mul-sint-sint-okp x y) ;todo: expand?
             (* (integer-from-sint x) (integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable mul-sint-sint sub-sint-sint-okp
                                     mul-sint-sint-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts lt-sint-sint to <
(defthmd boolean-from-sint-of-lt-sint-sint
  (equal (boolean-from-sint (lt-sint-sint x y))
         (< (integer-from-sint x) (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     lt-sint-sint))))


;; Converts le-sint-sint to <=
(defthmd boolean-from-sint-of-le-sint-sint
  (equal (boolean-from-sint (le-sint-sint x y))
         (<= (integer-from-sint x) (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     le-sint-sint))))

;; Converts gt-sint-sint to >
(defthmd boolean-from-sint-of-gt-sint-sint
  (equal (boolean-from-sint (gt-sint-sint x y))
         (> (integer-from-sint x) (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     gt-sint-sint))))

;; Converts ge-sint-sint to >=
(defthmd boolean-from-sint-of-ge-sint-sint
  (equal (boolean-from-sint (ge-sint-sint x y))
         (>= (integer-from-sint x) (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     ge-sint-sint))))

;; Converts eq-sint-sint to equal
(defthmd boolean-from-sint-of-eq-sint-sint
  (equal (boolean-from-sint (eq-sint-sint x y))
         (equal (integer-from-sint x) (integer-from-sint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     eq-sint-sint))))

;; Converts ne-sint-sint to not equal
(defthmd boolean-from-sint-of-ne-sint-sint
  (equal (boolean-from-sint (ne-sint-sint x y))
         (not (equal (integer-from-sint x) (integer-from-sint y))))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     ne-sint-sint))))

;; Converts lognot-sint to equal 0
(defthmd boolean-from-sint-of-lognot-sint
  (equal (boolean-from-sint (lognot-sint x))
         (equal (integer-from-sint x) 0))
  :hints (("Goal" :in-theory (enable boolean-from-sint lognot-sint sint-from-boolean))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + to add-sint-sint.
;; Requires showing that the addition doesn't overflow or underflow.
(defthmd sint-from-integer-of-+
  (implies (and ;;(sint-integerp (+ x y))
                (sint-integerp x)
                (sint-integerp y))
           (equal (sint-from-integer (+ x y))
                  (add-sint-sint (sint-from-integer x) (sint-from-integer y))))
  :hints (("Goal" :in-theory (enable add-sint-sint))))

;; Converts unary - to minus-sint.
(defthm sint-from-integer-of-unary--
  (implies (and ;;(sint-integerp (- x)) ; todo; simplify the hyps?
                (sint-integerp x))
           (equal (sint-from-integer (- x))
                  (minus-sint (sint-from-integer x))))
  :hints (("Goal" :in-theory (enable minus-sint))))

;; Converts binary - to sub-sint-sint
(defthm sint-from-integer-of--
  (implies (and ;;(sint-integerp (- x)) ; todo; simplify the hyps?
            (sint-integerp x)
            (sint-integerp y))
           (equal (sint-from-integer (- x y))
                  (sub-sint-sint (sint-from-integer x) (sint-from-integer y))))
  :hints (("Goal" :in-theory (enable sub-sint-sint))))

;; Converts * to mul-sint-sint.
(defthmd sint-from-integer-of-*
  (implies (and ;;(sint-integerp (* x y))
                (sint-integerp x)
                (sint-integerp y))
           (equal (sint-from-integer (* x y))
                  (mul-sint-sint (sint-from-integer x) (sint-from-integer y))))
  :hints (("Goal" :in-theory (enable mul-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C comparisons:

;; essentially the reverse of the one above
;not used?
(defthmd <-becomes-boolean-from-sint-of-lt-sint-sint
  (implies (and (sint-integerp x)
                (sint-integerp y))
           (equal (< x y)
                  (boolean-from-sint (lt-sint-sint (sint-from-integer x) (sint-from-integer y)))))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     lt-sint-sint))))

(theory-invariant (incompatible (:rewrite boolean-from-sint-of-lt-sint-sint)
                                (:rewrite <-becomes-boolean-from-sint-of-lt-sint-sint)))

;; todo: had to guess the type of x and y
;; weaker version of <-becomes-boolean-from-sint-of-lt-sint-sint (this one is needed for an example)
;; todo: which theory should this be added to?
(defthm sint-from-boolean-of-<-when-sints
  (implies (and (sint-integerp x)
                (sint-integerp y))
           (equal (sint-from-boolean (< x y))
                  (lt-sint-sint (sint-from-integer x) (sint-from-integer y))))
  :hints (("Goal" :in-theory (enable (:e sint-from-integer) lt-sint-sint sint-dec-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; i+1 seems more idiomatic than 1+i
(defthmd add-sint-sint-commute-of-constant-and-var
  (implies (syntaxp (and (consp x)
                         (eq 'sint-dec-const (car x)) ;gen?
                         (symbolp y)))
           (equal (add-sint-sint x y)
                  (add-sint-sint y x)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable add-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

;; todo: (lognot-sint (sint-from-integer 0))
(defthmd lognot-sint-of-ne-sint-sint
  (equal (lognot-sint (ne-sint-sint x y))
         (eq-sint-sint x y))
  :hints (("Goal" :in-theory (enable ne-sint-sint eq-sint-sint
                                     ;;lognot-sint sint-from-integer
                                     (:e sint-from-integer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable sint-removal-rules.

(defthm sintp-of-declar
  (equal (sintp (declar x))
         (sintp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm sintp-of-assign
  (equal (sintp (assign x))
         (sintp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let's keep this enabled, to resolve the case dispatch and expose integer-from-sint.
;; Or we could just enable integer-from-cinteger.
(defthm integer-from-cinteger-when-sintp
  (implies (sintp x)
           (equal (integer-from-cinteger x)
                  (integer-from-sint x)))
  :hints (("Goal" :in-theory (enable ucharp
                                     ushortp
                                     uintp
                                     scharp
                                     sshortp
                                     sintp
                                     integer-from-cinteger
                                     cinteger-kind
                                     cinteger-sint->get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This ruleset turns C operations into ACL2 arithmetic operations
;; It often has to be enabled in guard and termination proofs:
;; todo: improve the name
(deftheory sint-removal-rules
  '(assign
    declar
    ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
    ;; and rewrite/open functions like add-sint-sint without conversion wrappers outside of them:
    integer-from-sint-of-add-sint-sint
    integer-from-sint-of-sub-sint-sint
    integer-from-sint-of-minus-sint
    integer-from-sint-of-mul-sint-sint
    boolean-from-sint-of-lt-sint-sint
    boolean-from-sint-of-le-sint-sint
    boolean-from-sint-of-gt-sint-sint
    boolean-from-sint-of-ge-sint-sint
    boolean-from-sint-of-eq-sint-sint
    boolean-from-sint-of-ne-sint-sint
    boolean-from-sint-of-lognot-sint
    sub-sint-sint-okp
    add-sint-sint-okp
    minus-sint-okp
    mul-sint-sint-okp
    div-sint-sint-okp
    rem-sint-sint-okp
    shl-sint-sint-okp
    shr-sint-sint-okp
    sint-integerp ; exposes signed-byte-p
    int-bits
    sint-dec-const ; exposes sint-from-integer
    sint-hex-const ; exposes sint-from-integer
    sint-oct-const ; exposes sint-from-integer
    )
  :redundant-okp t)

(deftheory sint-intro-rules
  '(sint-from-integer-becomes-sint-dec-const-when-constant
    sint-from-integer-of-+
    sint-from-integer-of-unary--
    sint-from-integer-of--
    sint-from-integer-of-*
    add-sint-sint-commute-of-constant-and-var ; move?
    )
  :redundant-okp t)

(deftheory sint-intro-rules-strong
  (union-theories (theory 'sint-intro-rules)
                  '(<-becomes-boolean-from-sint-of-lt-sint-sint))
  :redundant-okp t)
