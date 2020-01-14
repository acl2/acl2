; Documentation for Built-In Theorems
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems
  :parents (acl2)
  :short "Built-in theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 source file @('axioms.lisp') provides a number of theorems.
     Here we mean `theorem' in the logical sense,
     introduced not only via @(tsee defthm) but also via @(tsee defaxiom)
     (logically, axioms are easy-to-prove theorems).")
   (xdoc::p
    "This documentation topic (and subtopics)
     collects and display these theorems,
     organized according to the built-in functions and values that they involve.
     These theorems may be easier to read and analyze here
     than in the ACL2 source files, which contain additional code.")
   (xdoc::p
    "The current organization of these theorems in subtopics
     may be improved in the future.
     It may even make sense to repeat certain theorems under certin subtopics,
     when they are relevant to multiple subtopics.")
   (xdoc::p
    "We use the XDOC preprocessor directive @('@(def ...)')
     to list the theorems automatically,
     without copying the forms (just the names).
     Thus, the only way in which this documentation topic may get out of sync
     is when some built-in theorem is added or removed,
     which may be a rare occurrence.")
   (xdoc::p
    "For now we only include the theorems of ``plain'' ACL2, not ACL2(r).")
   (xdoc::p
    "We omit theorems about ``internal'' functions,
     i.e. functions not documented in the manual.
     An example is
     the theorem that rewrites @('member-eq-exec') to @('member-equal'):
     @('member-eq-exec') is internal, and in fact
     the purpose of the aforementioned rewrite rule is to rewrite it away.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-logical-connectives
  :parents (built-in-theorems)
  :short "Built-in-theorems about logical connectives."
  :long
  "@(def iff-is-an-equivalence)
   @(def iff-implies-equal-implies-1)
   @(def iff-implies-equal-implies-2)
   @(def iff-implies-equal-not)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-booleans
  :parents (built-in-theorems)
  :short "Built-in-theorems about booleans."
  :long
  "@(def booleanp-compound-recognizer)
   @(def boolean-listp-cons)
   @(def boolean-listp-forward)
   @(def boolean-listp-forward-to-symbol-listp)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-cons-pairs
  :parents (built-in-theorems)
  :short "Built-in theorems about @(tsee cons) pairs."
  :long
  "@(def car-cdr-elim)
   @(def car-cons)
   @(def cdr-cons)
   @(def cons-equal)
   @(def completion-of-car)
   @(def completion-of-cdr)
   @(def default-car)
   @(def default-cdr)
   @(def cons-car-cdr)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-arithmetic
  :parents (built-in-theorems)
  :short "Built-in theorems about arithmetic."
  :long
  "@(def closure)
   @(def associativity-of-+)
   @(def commutativity-of-+)
   @(def unicity-of-0)
   @(def inverse-of-+)
   @(def associativity-of-*)
   @(def commutativity-of-*)
   @(def unicity-of-1)
   @(def inverse-of-*)
   @(def distributivity)
   @(def <-on-others)
   @(def zero)
   @(def trichotomy)
   @(def positive)
   @(def rational-implies1)
   @(def rational-implies2)
   @(def integer-implies-rational)
   @(def complex-implies1)
   @(def complex-definition)
   @(def nonzero-imagpart)
   @(def realpart-imagpart-elim)
   @(def realpart-complex)
   @(def imagpart-complex)
   @(def nonnegative-product)
   @(def integer-0)
   @(def integer-1)
   @(def integer-step)
   @(def lowest-terms)
   @(def completion-of-+)
   @(def completion-of-*)
   @(def completion-of-unary-minus)
   @(def completion-of-unary-/)
   @(def completion-of-<)
   @(def completion-of-complex)
   @(def completion-of-numerator)
   @(def completion-of-denominator)
   @(def completion-of-realpart)
   @(def completion-of-imagpart)
   @(def zp-compound-recognizer)
   @(def zp-open)
   @(def zip-compound-recognizer)
   @(def zip-open)
   @(def complex-equal)
   @(def natp-compound-recognizer)
   @(def bitp-compound-recognizer)
   @(def posp-compound-recognizer)
   @(def expt-type-prescription-non-zero-base)
   @(def rationalp-expt-type-prescription)
   @(def integer-range-p-forward)
   @(def signed-byte-p-forward-to-integerp)
   @(def unsigned-byte-p-forward-to-nonnegative-integerp)
   @(def rationalp-+)
   @(def rationalp-*)
   @(def rationalp-unary--)
   @(def rationalp-unary-/)
   @(def rationalp-implies-acl2-numberp)
   @(def default-+-1)
   @(def default-+-2)
   @(def default-*-1)
   @(def default-*-2)
   @(def default-unary-minus)
   @(def default-unary-/)
   @(def default-<-1)
   @(def default-<-2)
   @(def default-complex-1)
   @(def default-complex-2)
   @(def complex-0)
   @(def add-def-complex)
   @(def realpart-+)
   @(def imagpart-+)
   @(def default-numerator)
   @(def default-denominator)
   @(def default-realpart)
   @(def default-imagpart)
   @(def commutativity-2-of-+)
   @(def fold-consts-in-+)
   @(def distributivity-of-minus-over-+)
   @(def pos-listp-forward-to-integer-listp)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-characters
  :parents (built-in-theorems)
  :short "Built-in theorems about characters."
  :long
  "@(def booleanp-characterp)
   @(def characterp-page)
   @(def characterp-tab)
   @(def characterp-rubout)
   @(def characterp-return)
   @(def char-code-linear)
   @(def code-char-type)
   @(def code-char-char-code-is-identity)
   @(def char-code-code-char-is-identity)
   @(def completion-of-char-code)
   @(def completion-of-code-char)
   @(def lower-case-p-char-downcase)
   @(def upper-case-p-char-upcase)
   @(def lower-case-p-forward-to-alpha-char-p)
   @(def upper-case-p-forward-to-alpha-char-p)
   @(def alpha-char-p-forward-to-standard-char-p)
   @(def standard-char-p-forward-to-characterp)
   @(def characterp-char-downcase)
   @(def characterp-char-upcase)
   @(def characterp-nth)
   @(def standard-char-listp-append)
   @(def character-listp-append)
   @(def character-listp-remove-duplicates)
   @(def character-listp-revappend)
   @(def standard-char-p-nth)
   @(def equal-char-code)
   @(def default-char-code)
   @(def default-code-char)
   @(def make-character-list-make-character-list)
   @(def true-listp-explode-atom)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-strings
  :parents (built-in-theorems)
  :short "Built-in theorems about strings."
  :long
  "@(def coerce-inverse-1)
   @(def coerce-inverse-2)
   @(def character-listp-coerce)
   @(def completion-of-coerce)
   @(def string<-irreflexive)
   @(def stringp-substitute-type-prescription)
   @(def true-listp-substitute-type-prescription)
   @(def true-listp-explode-nonnegative-integer)
   @(def stringp-subseq-type-prescription)
   @(def true-listp-subseq-type-prescription)
   @(def default-coerce-1)
   @(def default-coerce-2)
   @(def default-coerce-3)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-symbols
  :parents (built-in-theorems)
  :short "Built-in theorems about symbols."
  :long
  "@(def stringp-symbol-package-name)
   @(def symbolp-intern-in-package-of-symbol)
   @(def symbolp-pkg-witness)
   @(def intern-in-package-of-symbol-symbol-name)
   @(def symbol-name-pkg-witness)
   @(def symbol-package-name-pkg-witness-name)
   @(def symbol-name-intern-in-package-of-symbol)
   @(def symbol-package-name-intern-in-package-of-symbol)
   @(def intern-in-package-of-symbol-is-identity)
   @(def symbol-listp-pkg-imports)
   @(def no-duplicatesp-eq-pkg-imports)
   @(def completion-of-pkg-imports)
   @(def acl2-input-channel-package)
   @(def acl2-output-channel-package)
   @(def acl2-package)
   @(def keyword-package)
   @(def string-is-not-circular)
   @(def nil-is-not-circular)
   @(def completion-of-intern-in-package-of-symbol)
   @(def completion-of-symbol-name)
   @(def completion-of-symbol-package-name)
   @(def keywordp-forward-to-symbolp)
   @(def symbol-package-name-of-symbol-is-not-empty-string)
   @(def symbol-equality)
   @(def default-pkg-imports)
   @(def symbol-<-asymmetric)
   @(def symbol-<-transitive)
   @(def symbol-<-trichotomy)
   @(def symbol-<-irreflexive)
   @(def default-intern-in-package-of-symbol)
   @(def default-symbol-name)
   @(def default-symbol-package-name)
   @(def symbol-listp-cdr-assoc-equal)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-bad-atoms
  :parents (built-in-theorems)
  :short "Built-in theorems about bad atoms."
  :long
  "@(def booleanp-bad-atom<=)
   @(def bad-atom<=-antisymmetric)
   @(def bad-atom<=-transitive)
   @(def bad-atom<=-total)
   @(def bad-atom-compound-recognizer)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-eqlables
  :parents (built-in-theorems)
  :short "Built-in theorems about @(tsee eql)ables."
  :long
  "@(def eqlablep-recog)
   @(def eqlablep-nth)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-lists
  :parents (built-in-theorems)
  :short "Built-in theorems about lists."
  :long
  "@(def symbol-listp-forward-to-true-listp)
   @(def true-listp-append)
   @(def append-to-nil)
   @(def character-listp-forward-to-eqlable-listp)
   @(def standard-char-listp-forward-to-character-listp)
   @(def atom-listp-forward-to-true-listp)
   @(def eqlable-listp-forward-to-atom-listp)
   @(def good-atom-listp-forward-to-atom-listp)
   @(def true-listp-revappend-type-prescription)
   @(def true-listp-take)
   @(def keyword-value-listp-forward-to-true-listp)
   @(def true-list-listp-forward-to-true-listp)
   @(def true-listp-nthcdr-type-prescription)
   @(def keyword-value-listp-assoc-keyword)
   @(def acl2-number-listp-forward-to-true-listp)
   @(def rational-listp-forward-to-acl2-number-listp)
   @(def integer-listp-forward-to-rational-listp)
   @(def nat-listp-forward-to-integer-listp)
   @(def nth-update-nth)
   @(def true-listp-update-nth)
   @(def nth-update-nth-array)
   @(def len-update-nth)
   @(def nth-0-cons)
   @(def nth-add1)
   @(def pairlis$-true-list-fix)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-alists
  :parents (built-in-theorems)
  :short "Built-in theorems about alists."
  :long
  "@(def alistp-forward-to-true-listp)
   @(def eqlable-alistp-forward-to-alistp)
   @(def symbol-alistp-forward-to-eqlable-alistp)
   @(def character-alistp-forward-to-eqlable-alistp)
   @(def nat-alistp-forward-to-eqlable-alistp)
   @(def standard-string-alistp-forward-to-alistp)
   @(def consp-assoc-equal)
   @(def known-package-alistp-forward-to-true-list-listp-and-alistp)
   @(def true-list-listp-forward-to-true-listp-assoc-equal)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-arrays
  :parents (built-in-theorems)
  :short "Built-in theorems about arrays."
  :long
  "@(def array1p-forward)
   @(def array1p-linear)
   @(def array2p-forward)
   @(def array2p-linear)
   @(def array1p-cons)
   @(def array2p-cons)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-total-order
  :parents (built-in-theorems)
  :short "Built-in theorems about the total order on values."
  :long
  "@(def alphorder-reflexive)
   @(def alphorder-anti-symmetric)
   @(def alphorder-transitive)
   @(def alphorder-total)
   @(def lexorder-reflexive)
   @(def lexorder-anti-symmetric)
   @(def lexorder-transitive)
   @(def lexorder-total)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-random$
  :parents (built-in-theorems)
  :short "Built-in theorems about @(tsee random$)."
  :long
  "@(def natp-random$)
   @(def random$-linear)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-about-system-utilities
  :parents (built-in-theorems)
  :short "Built-in theorems about system utilities."
  :long
  "@(def pseudo-term-listp-forward-to-true-listp)
   @(def legal-variable-or-constant-namep-implies-symbolp)
   @(def termp-implies-pseudo-termp)
   @(def term-listp-implies-pseudo-term-listp)
   @(def arities-okp-implies-arity)
   @(def arities-okp-implies-logicp)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-in-theorems-for-tau
  :parents (built-in-theorems)
  :short "Built-in theorems specifically for the tau system."
  :long
  "@(def basic-tau-rules)
   @(def bitp-as-inequality)")
