; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "characters")
(include-book "addresses")
(include-book "types")

(include-book "kestrel/crypto/ecurve/points-fty" :dir :system)

(include-book "kestrel/fty/boolean-result" :dir :system)

(include-book "kestrel/fty/ubyte8" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)
(include-book "kestrel/fty/ubyte64" :dir :system)
(include-book "kestrel/fty/ubyte128" :dir :system)

(include-book "kestrel/fty/sbyte8" :dir :system)
(include-book "kestrel/fty/sbyte16" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/fty/sbyte128" :dir :system)

(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (dynamic-semantics)
  :short "Leo values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the entities that are manipulated at run time.
     We formalize them as being tagged by their types
     (as common in programming language formalizations),
     which lets us express precisely the type correctness requirements
     in our defensive operational semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes value/valuelist

  (fty::deftagsum value
    :short "Fixtype of Leo values."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       boolean values,
       unsigned and signed integer values of five sizes,
       base field element values,
       group element values,
       scalar field element values,
       address values,
       string values,
       tuple values, and
       struct values.")
     (xdoc::p
      "Since the primes that define the base and prime fields may vary
       (see @(see curve-parameterization)),
       here we allow a field or scalar element to consist of any natural number.
       That the natural number is below the respective prime
       is enforced elsewhere.")
     (xdoc::p
      "Analogously, since the elliptic curve that defines the group may vary,
       here we allow a group element
       to consist of any possible point of any possible elliptic curve.
       We use the type of elliptic curve points
       from the elliptic curve library,
       which includes representations for
       both finite points and the point of infinity.")
     (xdoc::p
      "We do not require tuple values to have zero or two or more components
       (i.e. not to have one component).
       We can formulate and prove that invariant separately.
       Keeping the fixtype of values more general
       also facilitates a possible future extension of Leo
       in which tuple values with one components are actually allowed.")
     (xdoc::p
      "Struct values are modeled as finite maps
       from identifiers (i.e. the names of the components)
       to values (i.e. the values of the components).
       We also include the name of the struct type."))
    (:bool ((get bool)))
    (:u8 ((get ubyte8)))
    (:u16 ((get ubyte16)))
    (:u32 ((get ubyte32)))
    (:u64 ((get ubyte64)))
    (:u128 ((get ubyte128)))
    (:i8 ((get sbyte8)))
    (:i16 ((get sbyte16)))
    (:i32 ((get sbyte32)))
    (:i64 ((get sbyte64)))
    (:i128 ((get sbyte128)))
    (:field ((get nat)))
    (:group ((get point)))
    (:scalar ((get nat)))
    (:address ((get address)))
    (:string ((get char-list)))
    (:tuple ((components value-list)))
    (:struct ((type identifier)
               (components value-map)))
    :pred valuep)

  (fty::deflist value-list
    :short "Fixtype of lists of Leo values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp
    ///
    (defrule value-list-fix-of-update-nth
      (implies (< (nfix index) (len values))
               (equal (value-list-fix (update-nth index value values))
                      (update-nth index
                                  (value-fix value)
                                  (value-list-fix values))))))

  (fty::defomap value-map
    :short "Fixtype of finite maps from identifiers to Leo values."
    :key-type identifier
    :val-type value
    :pred value-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption value-option
  value
  :short "Fixtype of optional Leo values."
  :pred value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod name+value
  :short "Fixtype of pairs consisting of a name (identifier) and a value."
  ((name identifier)
   (value value))
  :tag :name+value
  :pred name+value-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection int-value-bound-theorems
  :short "Theorems about the bounds of the integer values."

  (defrule value-i8-lower-bound
    (<= -128 (value-i8->get x))
    :rule-classes :linear
    :enable sbyte8p
    :disable sbyte8p-of-value-i8->get
    :use (:instance sbyte8p-of-value-i8->get))

  (defrule value-i8-upper-bound
    (<= (value-i8->get x) 127)
    :rule-classes :linear
    :enable sbyte8p
    :disable sbyte8p-of-value-i8->get
    :use (:instance sbyte8p-of-value-i8->get))

  (defrule value-i16-lower-bound
    (<= -32768 (value-i16->get x))
    :rule-classes :linear
    :enable sbyte16p
    :disable sbyte16p-of-value-i16->get
    :use (:instance sbyte16p-of-value-i16->get))

  (defrule value-i16-upper-bound
    (<= (value-i16->get x) 32767)
    :rule-classes :linear
    :enable sbyte16p
    :disable sbyte16p-of-value-i16->get
    :use (:instance sbyte16p-of-value-i16->get))

  (defrule value-i32-lower-bound
    (<= -2147483648 (value-i32->get x))
    :rule-classes :linear
    :enable sbyte32p
    :disable sbyte32p-of-value-i32->get
    :use (:instance sbyte32p-of-value-i32->get))

  (defrule value-i32-upper-bound
    (<= (value-i32->get x) 2147483647)
    :rule-classes :linear
    :enable sbyte32p
    :disable sbyte32p-of-value-i32->get
    :use (:instance sbyte32p-of-value-i32->get))

  (defrule value-i64-lower-bound
    (<= -9223372036854775808 (value-i64->get x))
    :rule-classes :linear
    :enable sbyte64p
    :disable sbyte64p-of-value-i64->get
    :use (:instance sbyte64p-of-value-i64->get))

  (defrule value-i64-upper-bound
    (<= (value-i64->get x) 9223372036854775807)
    :rule-classes :linear
    :enable sbyte64p
    :disable sbyte64p-of-value-i64->get
    :use (:instance sbyte64p-of-value-i64->get))

  (defrule value-i128-lower-bound
    (<= -170141183460469231731687303715884105728 (value-i128->get x))
    :rule-classes :linear
    :enable sbyte128p
    :disable sbyte128p-of-value-i128->get
    :use (:instance sbyte128p-of-value-i128->get))

  (defrule value-i128-upper-bound
    (<= (value-i128->get x) 170141183460469231731687303715884105727)
    :rule-classes :linear
    :enable sbyte128p
    :disable sbyte128p-of-value-i128->get
    :use (:instance sbyte128p-of-value-i128->get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-valuep (x)
  :returns (yes/no booleanp)
  :short "Recognizer of Leo integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the unsigned and signed integer values.")
   (xdoc::p
    "We use this function as an abbreviation,
     so we leave it enabled.
     Rules triggered by this function should be generally avoided."))
  (and (valuep x)
       (member-eq (value-kind x)
                  '(:u8 :u16 :u32 :u64 :u128 :i8 :i16 :i32 :i64 :i128))
       t)) ; <- just so result is boolean

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-value-numbits ((int-v int-valuep))
  :returns (result natp :hyp :guard)
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  :short "Returns the number of bits that a value of this kind could take."
  :long
  (xdoc::topstring
   (xdoc::p
    "The integer value of @('int-v') is ignored;
     just its @('kind') is looked at.
     The size of the @('kind') in bits is returned."))
  (case (value-kind int-v)
      (:u8 8)
      (:u16 16)
      (:u32 32)
      (:u64 64)
      (:u128 128)
      (:i8 8)
      (:i16 16)
      (:i32 32)
      (:i64 64)
      (:i128 128)
      (t (prog2$ (impossible) 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-value-to-int ((x int-valuep))
  :returns (int integerp)
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  :short "ACL2 integer value corresponding to a Leo integer value."
  (case (value-kind x)
    (:u8 (value-u8->get x))
    (:u16 (value-u16->get x))
    (:u32 (value-u32->get x))
    (:u64 (value-u64->get x))
    (:u128 (value-u128->get x))
    (:i8 (value-i8->get x))
    (:i16 (value-i16->get x))
    (:i32 (value-i32->get x))
    (:i64 (value-i64->get x))
    (:i128 (value-i128->get x))
    (t (prog2$ (impossible) 0)))
  ///
  (fty::deffixequiv int-value-to-int
    :args ((x valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-of-value
  :short "Leo type of a Leo value."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our current formalization,
     every Leo value has exactly one Leo type.
     This function associates a type to each value."))

  (define type-of-value ((value valuep))
    :returns (type typep)
    (value-case value
                :bool (type-bool)
                :u8 (type-unsigned (bitsize-8))
                :u16 (type-unsigned (bitsize-16))
                :u32 (type-unsigned (bitsize-32))
                :u64 (type-unsigned (bitsize-64))
                :u128 (type-unsigned (bitsize-128))
                :i8 (type-signed (bitsize-8))
                :i16 (type-signed (bitsize-16))
                :i32 (type-signed (bitsize-32))
                :i64 (type-signed (bitsize-64))
                :i128 (type-signed (bitsize-128))
                :field (type-field)
                :group (type-group)
                :scalar (type-scalar)
                :address (type-address)
                :string (type-string)
                :tuple (type-tuple (type-list-of-value-list value.components))
                ;; TODO: consider the 3 other cases
                ;; type-external-named and/or recordp=T
                :struct (type-internal-named value.type nil))
    :measure (value-count value))

  (define type-list-of-value-list ((values value-listp))
    :returns (types type-listp)
    (cond ((endp values) nil)
          (t (cons (type-of-value (car values))
                   (type-list-of-value-list (cdr values)))))
    :measure (value-list-count values)
    ///
    (defret len-of-type-list-of-value-list
      (equal (len types)
             (len values))))

  :verify-guards nil ; done below
  ///
  (verify-guards type-of-value)

  (fty::deffixequiv-mutual type-of-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name+type-of-name+value ((nval name+value-p))
  :returns (ntype name+type-p)
  :short "Name-type pair corresponding to a name-value pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "We leave the name unchanged,
     and turn the value into its type.
     This lifts @(tsee type-of-value) to name-value pairs."))
  (make-name+type :name (name+value->name nval)
                  :type (type-of-value (name+value->value nval)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-map-of-value-map ((vmap value-mapp))
  :returns (tmap type-mapp)
  :short "Type map corresponding to a value map."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type map has the same keys as the value map,
     but with the types of the corresponding (Leo) values as (map) values.
     This lifts @(tsee type-of-value) to value maps."))
  (b* ((vmap (value-map-fix vmap))
       ((when (omap::emptyp vmap)) nil)
       ((mv name val) (omap::head vmap)))
    (omap::update name
                  (type-of-value val)
                  (type-map-of-value-map (omap::tail vmap))))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-result
  :short "Fixtype of Leo values and @(see errors)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The defensive execution of certain Leo constructs
     yield results that are either Leo values or errors.
     This fixtype captures these results."))
  :ok value
  :pred value-resultp
  :prepwork ((local (in-theory (enable value-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-list-result
  :short "Fixtype of lists of Leo values and @(see errors)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The defensive execution of certain Leo constructs
     yield results that are either lists of Leo values or errors.
     This fixtype captures these results."))
  :ok value-list
  :pred value-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-option-result
  :short "Fixtype of optional Leo values and @(see errors)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The defensive execution of certain Leo constructs
     yield results that are either optional Leo values or errors.
     This fixtype captures these results."))
  :ok value-option
  :pred value-option-resultp
  :prepwork ((local (in-theory (enable valuep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *greatest-u8* (- (expt 2 8) 1)) ; 255
(defval *greatest-u16* (- (expt 2 16) 1)) ; 65535
(defval *greatest-u32* (- (expt 2 32) 1)) ; 4294967295
(defval *greatest-u64* (- (expt 2 64) 1)) ; 18446744073709551615
(defval *greatest-u128* (- (expt 2 128) 1)) ; 340282366920938463463374607431768211455

(defval *most-negative-i8* (- (expt 2 7))) ; -128
(defval *most-negative-i16* (- (expt 2 15))) ; -32768
(defval *most-negative-i32* (- (expt 2 31))) ; -2147483648
(defval *most-negative-i64* (- (expt 2 63))) ; -9223372036854775808
(defval *most-negative-i128* (- (expt 2 127))) ; -170141183460469231731687303715884105728

(defval *most-positive-i8* (- (expt 2 7) 1)) ; 127
(defval *most-positive-i16* (- (expt 2 15) 1)) ; 32767
(defval *most-positive-i32* (- (expt 2 31) 1)) ; 2147483647
(defval *most-positive-i64* (- (expt 2 63) 1)) ; 9223372036854775807
(defval *most-positive-i128* (- (expt 2 127) 1)) ; 170141183460469231731687303715884105727

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parametric in the type alternative
(define make-int-value ((int-value-kind symbolp) (int-vv integerp))
  :returns (result value-resultp)
  :short "Makes an integer value or an error."
  (let ((err (reserrf (list :make-int-value int-value-kind int-vv))))
    (case int-value-kind
      (:u8 (if (and (<= 0 int-vv)
                    (<= int-vv *greatest-u8*))
               (value-u8 int-vv)
             err))
      (:u16 (if (and (<= 0 int-vv)
                     (<= int-vv *greatest-u16*))
                (value-u16 int-vv)
              err))
      (:u32 (if (and (<= 0 int-vv)
                     (<= int-vv *greatest-u32*))
                (value-u32 int-vv)
              err))
      (:u64 (if (and (<= 0 int-vv)
                     (<= int-vv *greatest-u64*))
                (value-u64 int-vv)
              err))
      (:u128 (if (and (<= 0 int-vv)
                      (<= int-vv *greatest-u128*))
                 (value-u128 int-vv)
               err))
      (:i8 (if (and (<= *most-negative-i8* int-vv)
                    (<= int-vv *most-positive-i8*))
               (value-i8 int-vv)
             err))
      (:i16 (if (and (<= *most-negative-i16* int-vv)
                     (<= int-vv *most-positive-i16*))
                (value-i16 int-vv)
              err))
      (:i32 (if (and (<= *most-negative-i32* int-vv)
                     (<= int-vv *most-positive-i32*))
                (value-i32 int-vv)
              err))
      (:i64 (if (and (<= *most-negative-i64* int-vv)
                     (<= int-vv *most-positive-i64*))
                (value-i64 int-vv)
              err))
      (:i128 (if (and (<= *most-negative-i128* int-vv)
                      (<= int-vv *most-positive-i128*))
                 (value-i128 int-vv)
               err))
      (t err)))
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte16p ubyte32p
                                           ubyte64p ubyte128p
                                           sbyte8p sbyte16p sbyte32p
                                           sbyte64p sbyte128p))))
