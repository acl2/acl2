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

(in-theory (disable (:e c::sint-from-integer)
                    (:e c::sint-dec-const) ; ensures these are retained by simplify
                    (:e c::sint-hex-const)
                    (:e c::sint-oct-const)))

(local (in-theory (enable c::int-bits c::sint-integerp c::sint-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm c::sint-integerp-forward-to-upper-bound
  (implies (c::sint-integerp x)
           (<= x 2147483647))
  :rule-classes :forward-chaining)

(defthm c::sint-integerp-forward-to-lower-bound
  (implies (c::sint-integerp x)
           (<= -2147483648 x))
  :rule-classes :forward-chaining)

(defthm sint-integer-fix-upper-bound-linear
  (<= (c::sint-integer-fix x) 2147483647)
  :rule-classes :linear)

(defthm sint-integer-fix-lower-bound-linear
  (<= -2147483648 (c::sint-integer-fix x))
  :rule-classes :linear)

(defthm signed-byte-p-of-sint-integer-fix
  (implies (and (<= 32 size)
                (integerp size))
           (signed-byte-p size (c::sint-integer-fix y)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm integer-from-sint-upper-bound-linear
  (<= (c::integer-from-sint x) 2147483647)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-sint))))

(defthm integer-from-sint-lower-bound-linear
  (<= -2147483648 (c::integer-from-sint x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-sint))))

(defthm signed-byte-p-of-integer-from-sint
  (implies (and (<= 32 size)
                (integerp size))
           (signed-byte-p size (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::integer-from-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion, etc.

;; Note that c::integer-from-sint-of-sint-from-integer is built in to ATC

(defthm integer-from-sint-of-sint-dec-const
  (equal (c::integer-from-sint (c::sint-dec-const x))
         (c::sint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::integer-from-sint
                                     c::sint-dec-const))))

(defthm integer-from-cinteger-of-sint-dec-const
  (equal (c::integer-from-cinteger (c::sint-dec-const x))
         (c::sint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::integer-from-cinteger-alt-def c::sint-dec-const))))

(defthm integer-from-cinteger-of-sint-from-integer
  (equal (c::integer-from-cinteger (c::sint-from-integer x))
         (c::sint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::integer-from-cinteger-alt-def c::sint-dec-const))))

;; what about when x or y is a constant?
(defthmd equal-of-integer-from-sint-and-integer-from-sint
  (equal (equal (c::integer-from-sint x) (c::integer-from-sint y))
         (equal (c::sint-fix x) (c::sint-fix y)))
  :hints (("Goal" :in-theory (enable c::integer-from-sint c::sint-fix))))

;; In case we are not rewriting either way:
(defthm equal-of-sint-from-integer-and-sint-dec-const
  (equal (equal (c::sint-from-integer x) (c::sint-dec-const x))
         t)
  :hints (("Goal" :in-theory (enable c::sint-dec-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants

;; Turn c::sint-from-integer into c::sint-dec-const (necessary for ATC) when the argument is
;; a quoted constant.  Not clear if this should always be enabled.
(defthmd sint-from-integer-becomes-sint-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (c::sint-from-integer x)
                  (c::sint-dec-const x)))
  :hints (("Goal" :in-theory (enable c::sint-dec-const))))

(theory-invariant (incompatible (:rewrite sint-from-integer-becomes-sint-dec-const-when-constant)
                                (:definition c::sint-dec-const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm sint-integer-fix-when-not-sint-integerp
  (implies (not (c::sint-integerp x))
           (equal (c::sint-integer-fix x)
                  0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd boolean-from-sint-of-sint-dec-const
  (equal (c::boolean-from-sint (c::sint-dec-const k))
         (not (equal (c::sint-integer-fix k) 0)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint))))

(defthmd boolean-from-sint-of-sint-from-integer
  (equal (c::boolean-from-sint (c::sint-from-integer k))
         (not (equal (c::sint-integer-fix k) 0)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts add-sint-sint to +.
(defthmd integer-from-sint-of-add-sint-sint
  (equal (c::integer-from-sint (c::add-sint-sint x y))
         (if (c::add-sint-sint-okp x y)
             (+ (c::integer-from-sint x) (c::integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable c::add-sint-sint
                                     c::add-sint-sint-okp))))

;; Alternate phrasing
;; (defthmd integer-from-sint-of-add-sint-sint-strong
;;   (equal (c::integer-from-sint (c::add-sint-sint x y))
;;          (c::sint-integer-fix (+ (c::integer-from-sint x) (c::integer-from-sint y))))
;;   :hints (("Goal" :in-theory (enable c::add-sint-sint))))

;; Converts c::minus-sint to unary -.
(defthmd integer-from-sint-of-minus-sint
  (implies (c::minus-sint-okp x)
           (equal (c::integer-from-sint (c::minus-sint x))
                  (- (c::integer-from-sint x))))
  :hints (("Goal" :in-theory (enable c::minus-sint
                                     c::minus-sint-okp))))

;; Converts sub-sint-sint to -.
(defthmd integer-from-sint-of-sub-sint-sint
  (equal (c::integer-from-sint (c::sub-sint-sint x y))
         (if (c::sub-sint-sint-okp x y) ;todo: expand?
             (- (c::integer-from-sint x) (c::integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable c::sub-sint-sint c::sub-sint-sint-okp))))

;; Converts mul-sint-sint to *.
(defthmd integer-from-sint-of-mul-sint-sint
  (equal (c::integer-from-sint (c::mul-sint-sint x y))
         (if (c::mul-sint-sint-okp x y) ;todo: expand?
             (* (c::integer-from-sint x) (c::integer-from-sint y))
           0))
  :hints (("Goal" :in-theory (enable c::mul-sint-sint c::sub-sint-sint-okp
                                     c::mul-sint-sint-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts lt-sint-sint to <
(defthmd boolean-from-sint-of-lt-sint-sint
  (equal (c::boolean-from-sint (c::lt-sint-sint x y))
         (< (c::integer-from-sint x) (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::lt-sint-sint))))


;; Converts le-sint-sint to <=
(defthmd boolean-from-sint-of-le-sint-sint
  (equal (c::boolean-from-sint (c::le-sint-sint x y))
         (<= (c::integer-from-sint x) (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::le-sint-sint))))

;; Converts gt-sint-sint to >
(defthmd boolean-from-sint-of-gt-sint-sint
  (equal (c::boolean-from-sint (c::gt-sint-sint x y))
         (> (c::integer-from-sint x) (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::gt-sint-sint))))

;; Converts ge-sint-sint to >=
(defthmd boolean-from-sint-of-ge-sint-sint
  (equal (c::boolean-from-sint (c::ge-sint-sint x y))
         (>= (c::integer-from-sint x) (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::ge-sint-sint))))

;; Converts eq-sint-sint to equal
(defthmd boolean-from-sint-of-eq-sint-sint
  (equal (c::boolean-from-sint (c::eq-sint-sint x y))
         (equal (c::integer-from-sint x) (c::integer-from-sint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::eq-sint-sint))))

;; Converts ne-sint-sint to not equal
(defthmd boolean-from-sint-of-ne-sint-sint
  (equal (c::boolean-from-sint (c::ne-sint-sint x y))
         (not (equal (c::integer-from-sint x) (c::integer-from-sint y))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::ne-sint-sint))))

;; Converts lognot-sint to equal 0
(defthmd boolean-from-sint-of-lognot-sint
  (equal (c::boolean-from-sint (c::lognot-sint x))
         (equal (c::integer-from-sint x) 0))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::lognot-sint c::sint-from-boolean))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + to c::add-sint-sint.
;; Requires showing that the addition doesn't overflow or underflow.
(defthmd sint-from-integer-of-+
  (implies (and ;;(c::sint-integerp (+ x y))
                (c::sint-integerp x)
                (c::sint-integerp y))
           (equal (c::sint-from-integer (+ x y))
                  (c::add-sint-sint (c::sint-from-integer x) (c::sint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-sint-sint))))

;; Converts unary - to c::minus-sint.
(defthm sint-from-integer-of-unary--
  (implies (and ;;(c::sint-integerp (- x)) ; todo; simplify the hyps?
                (c::sint-integerp x))
           (equal (c::sint-from-integer (- x))
                  (c::minus-sint (c::sint-from-integer x))))
  :hints (("Goal" :in-theory (enable c::minus-sint))))

;; Converts binary - to c::sub-sint-sint
(defthm sint-from-integer-of--
  (implies (and ;;(c::sint-integerp (- x)) ; todo; simplify the hyps?
            (c::sint-integerp x)
            (c::sint-integerp y))
           (equal (c::sint-from-integer (- x y))
                  (c::sub-sint-sint (c::sint-from-integer x) (c::sint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::sub-sint-sint))))

;; Converts * to c::mul-sint-sint.
(defthmd sint-from-integer-of-*
  (implies (and ;;(c::sint-integerp (* x y))
                (c::sint-integerp x)
                (c::sint-integerp y))
           (equal (c::sint-from-integer (* x y))
                  (c::mul-sint-sint (c::sint-from-integer x) (c::sint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::mul-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C comparisons:

;; essentially the reverse of the one above
;not used?
(defthmd <-becomes-boolean-from-sint-of-lt-sint-sint
  (implies (and (c::sint-integerp x)
                (c::sint-integerp y))
           (equal (< x y)
                  (c::boolean-from-sint (c::lt-sint-sint (c::sint-from-integer x) (c::sint-from-integer y)))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::lt-sint-sint))))

(theory-invariant (incompatible (:rewrite boolean-from-sint-of-lt-sint-sint)
                                (:rewrite <-becomes-boolean-from-sint-of-lt-sint-sint)))

;; todo: had to guess the type of x and y
;; weaker version of <-becomes-boolean-from-sint-of-lt-sint-sint (this one is needed for an example)
;; todo: which theory should this be added to?
(defthm sint-from-boolean-of-<-when-sints
  (implies (and (c::sint-integerp x)
                (c::sint-integerp y))
           (equal (c::sint-from-boolean (< x y))
                  (c::lt-sint-sint (c::sint-from-integer x) (c::sint-from-integer y))))
  :hints (("Goal" :in-theory (enable (:e c::sint-from-integer) c::lt-sint-sint c::sint-dec-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; i+1 seems more idiomatic than 1+i
(defthmd add-sint-sint-commute-of-constant-and-var
  (implies (syntaxp (and (consp x)
                         (eq 'c::sint-dec-const (car x)) ;gen?
                         (symbolp y)))
           (equal (c::add-sint-sint x y)
                  (c::add-sint-sint y x)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable c::add-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

;; todo: (c::lognot-sint (c::sint-from-integer 0))
(defthmd lognot-sint-of-ne-sint-sint
  (equal (c::lognot-sint (c::ne-sint-sint x y))
         (c::eq-sint-sint x y))
  :hints (("Goal" :in-theory (enable c::ne-sint-sint c::eq-sint-sint
                                     ;;c::lognot-sint c::sint-from-integer
                                     (:e c::sint-from-integer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable sint-removal-rules.

(defthm sintp-of-declar
  (equal (c::sintp (c::declar x))
         (c::sintp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm sintp-of-assign
  (equal (c::sintp (c::assign x))
         (c::sintp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let's keep this enabled, to resolve the case dispatch and expose integer-from-sint.
;; Or we could just enable c::integer-from-cinteger.
(defthm integer-from-cinteger-when-sintp
  (implies (c::sintp x)
           (equal (c::integer-from-cinteger x)
                  (c::integer-from-sint x)))
  :hints (("Goal" :in-theory (enable c::ucharp
                                     c::ushortp
                                     c::uintp
                                     c::scharp
                                     c::sshortp
                                     c::sintp
                                     c::integer-from-cinteger
                                     c::cinteger-kind
                                     c::cinteger-sint->get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This ruleset turns C operations into ACL2 arithmetic operations
;; It often has to be enabled in guard and termination proofs:
;; todo: improve the name
(deftheory sint-removal-rules
  '(c::assign
    c::declar
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
    c::sub-sint-sint-okp
    c::add-sint-sint-okp
    c::minus-sint-okp
    c::mul-sint-sint-okp
    c::div-sint-sint-okp
    c::rem-sint-sint-okp
    c::shl-sint-sint-okp
    c::shr-sint-sint-okp
    c::sint-integerp ; exposes signed-byte-p
    c::int-bits
    c::sint-dec-const ; exposes sint-from-integer
    c::sint-hex-const ; exposes sint-from-integer
    c::sint-oct-const ; exposes sint-from-integer
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
