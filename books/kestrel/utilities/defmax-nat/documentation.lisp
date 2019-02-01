; Maximum of a Set of Natural Numbers -- Documentation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmax-nat

  :parents (kestrel-utilities)

  :short "Declaratively define the maximum of a set of natural numbers."

  :long

  (xdoc::topapp

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "This macro captures the mathematical notation
     @($\\max\\: \\{y \\in \\mathbb{N} \\mid \\psi[x_1,\\ldots,x_n,y]\\}$),
     where @($\\mathbb{N}$) is the set of natural numbers,
     @($n \\geq 0$),
     and @($\\psi[x_1,\\ldots,x_n,y]$) is a formula
     that depends on @($x_1,\\ldots,x_n$) and @($y$).
     Each value of the tuple @($\\langle x_1, \\ldots, x_n \\rangle$)
     defines a set of natural numbers,
     which may or may not have a maximum;
     if it does not, we regard @($\\max$) as returning a special value
     distinct from all the natural numbers, e.g. @($\\bot$).
     Thus, the notation defines a function from @($n$)-tuples
     to natural numbers or @($\\bot$).")

   (xdoc::p
    "This macro introduces such a function,
     from a user-supplied term that represents @($\\psi[x_1,\\ldots,x_n,y]$).
     The user also supplies
     the variables to use as @($x_1,\\ldots,x_n$) and @($y$),
     as well as an optional term over @($x_1,\\ldots,x_n$)
     to use as the function's guard.")

   (xdoc::p
    "Besides the function itself,
     this macro introduces auxiliary functions and theorems upon which
     the function definition is based,
     as well as theorems about the function.
     It also introduces theorems to help reason about the function,
     in particular to establish that the maximum exists
     without having to calculate it explicitly,
     and to establish that the maximum is a certain value.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::code
    "(defmax-nat f y (x1 ... xn)"
    "  body"
    "  :guard ...          ; default t"
    "  :verify-guards ...  ; default t"
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('f')"
    (xdoc::p
     "Name of the function to introduce."))

   (xdoc::desc
    "@('y')"
    (xdoc::p
     "Name of the variable to use as @($y$).")
    (xdoc::p
     "This is the variable bound in the set comprehension
      of the mathematical notation shown above.
      Note that the syntax of @('defmax-nat') is similar to
      the syntax of @(tsee defchoose) in this respect."))

   (xdoc::desc
    "@('(x1 ... xn)')"
    (xdoc::p
     "True list of the names of the zero or more variables
      to use as @($x_1,\\ldots,x_n$).")
    (xdoc::p
     "These are the formal parameters of @('f')."))

   (xdoc::desc
    "@('body')"
    (xdoc::p
     "Term to use as the formula @($\\psi[x_1,\\ldots,x_n,y]$).")
    (xdoc::p
     "Its only free variables must be among
      @('x1'), ..., @('xn'), and @('y').")
    (xdoc::p
     "We write this term as @('body<x1,...,xn,y>'),
      to emphasize its dependence on the variables."))

   (xdoc::desc
    "@(':guard') &mdash; default @('t')"
    (xdoc::p
     "Term to use as the guard of @('f').")
    (xdoc::p
     "Its only free variables must be among @('x1'), ..., @('xn').")
    (xdoc::p
     "Let @('guard<x1,...,xn>') be this term,
      emphasizing its dependence on the variables."))

   (xdoc::desc
    "@(':verify-guards') &mdash; default @('t')"
    (xdoc::p
     "Determines whether the guards of @('f'),
      and of the auxiliary functions generated,
      should be verified or not."))

   (xdoc::p
    "The current implementation of this macro
     does not thoroughly validate its inputs,
     but errors caused by the generated functions and theorems
     should be relatively easy to debug,
     based on the documentation below,
     and possibly on the examination of the implementation,
     which uses a readable backquote notation.
     Nonetheless, the implementation of this macro may be improved in the future
     to validate its inputs more thoroughly.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated Functions and Theorems")

   (xdoc::p
    "See the file @('defmax-nat-template.lisp') for more explanations
     about the generated functions and theorems.")

   (xdoc::p
    "Except for @('f') itself,
     the names of the generated functions consist of the name of @('f')
     followed by @('.') and by the suffixes described below.
     All the functions are guard-verified iff @(':verify-guards') is @('t').
     All the functions are disabled;
     all the rewrite rules associated with the @(tsee defun-sk)s
     are disabled;
     if @('n') is 0, i.e. @('f') has no arguments,
     the executable counterpart of @('f') is disabled as well,
     to prevent ACL2 from wrapping calls @('(f)') into @(tsee hide).")

   (xdoc::desc
    "@('f.elementp')"
    (xdoc::p
     "Auxiliary function to test the membership of @('y')
      in the set defined by @('x1'), ..., @('xn').")
    (xdoc::code
     "(defun f.elementp (x1 ... xn y)"
     "  (declare (xargs :guard (and guard<x1,...,xn> (natp y))))"
     "  body<x1,...,xn,y>)"))

   (xdoc::desc
    "@('f.uboundp')"
    (xdoc::p
     "Auxiliary predicate asserting that
      @('y') is an upper bound of the set defined by @('x1'), ..., @('xn'),
      along with associated theorems.")
    (xdoc::code
     "(defun-sk f.uboundp (x1 ... xn y)"
     "  (declare (xargs :guard (and guard<x1,...,xn> (natp y))))"
     "  (forall (y1)"
     "          (impliez (and (natp y1)"
     "                        (f.elementp x1 ... xn y1))"
     "                   (>= (nfix y) y1)))"
     "  :rewrite (implies (and (f.uboundp x1 ... xn y)"
     "                         (natp y1)"
     "                         (f.elementp x1 ... xn y1))"
     "                    (>= (nfix y) y1)))"
     ""
     "(defthm booleanp-of-f.uboundp"
     "  (booleanp (f.uboundp x1 ... xn y)))"))

   (xdoc::desc
    "@('f.existsp')"
    (xdoc::p
     "Auxiliary predicate asserting that
      the set defined by @('x1'), ..., @('xn') has a maximum,
      along with associated theorems.")
    (xdoc::code
     "(defun-sk f.existsp (x1 ... xn)"
     "  (declare (xargs :guard guard<x1,...,xn>))"
     "  (exists (y)"
     "          (and (natp y)"
     "               (f.elementp x1 ... xn y)"
     "               (f.unboundp x1 ... xn y))))"
     ""
     "(defthm booleanp-of-f.existsp"
     "  (booleanp (f.existsp x1 ... xn)))"))

   (xdoc::desc
    "@('f')"
    (xdoc::p
     "The function that returns the maximum if it exists (otherwise @('nil')),
      along with associated theorems.")
    (xdoc::code
     "(defun f (x1 ... xn)"
     "  (declare (xargs :guard guard<x1,...,xn>))"
     "  (if (f.existsp x1 ... xn)"
     "      (f.existsp-witness x1 ... xn)"
     "    nil))"
     ""
     "(defthm maybe-natp-of-f"
     "  (maybe-natp (f x1 ... xn)))"
     ""
     "(defthm natp-of-f-equal-f.existsp"
     "  (equal (natp (f x1 ... xn))"
     "         (f.existsp x1 ... xn)))"
     ""
     "(defthm natp-of-f-when-f.existsp"
     "  (implies (f.existsp x1 ... xn)"
     "           (natp (f x1 ... xn)))"
     "  :rule-classes :type-prescription)"
     ""
     "(defthm f-iff-f.existsp"
     "  (iff (f x1 ... xn)"
     "       (f.existsp x1 ... xn)))"
     ""
     "(defthm not-f-when-not-f.existsp"
     "  (implies (not (f.existsp x1 ... xn))"
     "           (not (f x1 ... xn)))"
     "  :rule-classes :type-prescription)"
     ""
     "(defthm f.elementp-of-f-when-f.existsp"
     "  (implies (f.existsp x1 ... xn)"
     "           (f.elementp x1 ... xn (f x1 ... xn))))"
     ""
     "(defthm f.uboundp-of-f-when-f.existsp"
     "  (implies (f.existsp x1 ... xn)"
     "           (f.uboundp x1 ... xn (f x1 ... xn))))"
     ""
     "(defthm f-geq-when-f.existsp-linear"
     "  (implies (and (f.existsp x1 ... xn)"
     "                (f.elementp x1 ... xn y1) ;; bind free y1"
     "                (natp y1))"
     "           (>= (f x1 ... xn) y1))"
     "  :rule-classes :linear)"
     ""
     "(defthm f-geq-when-f.existsp-rewrite"
     "  (implies (and (f.existsp x1 ... xn)"
     "                (f.elementp x1 ... xn y1)"
     "                (natp y1))"
     "           (>= (f x1 ... xn) y1))"
     ""
     "(defthm f-leq-when-f.existsp-linear"
     "  (implies (and (f.existsp x1 ... xn)"
     "                (f.uboundp x1 ... xn y1) ;; bind free y1"
     "                (natp y1))"
     "           (<= (f x1 ... xn) y1))"
     "  :rule-classes :linear)"
     ""
     "(defthm f-leq-when-f.existsp-rewrite"
     "  (implies (and (f.existsp x1 ... xn)"
     "                (f.uboundp x1 ... xn y1)"
     "                (natp y1))"
     "           (<= (f x1 ... xn) y1))"))

   (xdoc::desc
    "@('f.existsp-when-nonempty-and-bounded')"
    (xdoc::p
     "The helper theorem to establish that the maximum exists
      by exhibiting a member and a bound of the set.")
    (xdoc::code
     "(defthm f.existsp-when-nonempty-and-bounded"
     "  (implies (and (natp y0)"
     "                (f.elementp x1 ... xn y0)"
     "                (natp y1)"
     "                (f.uboundp x1 ... xn y1))"
     "           (f.existsp x1 ... xn))"
     "  :rule-classes nil)"))

   (xdoc::desc
    "@('f.equal-when-member-and-ubound')"
    (xdoc::p
     "The helper theorem to establish that the maximum has a certain value
      by showing that that value is
      both a member and an upper bound of the set.")
    (xdoc::code
     "(defthm f.equal-when-member-and-ubound"
     "  (implies (and (natp y)"
     "                (f.elementp x1 ... xn y)"
     "                (f.uboundp x1 ... xn y))"
     "           (equal (f x) y))"
     "  :rule-classes nil)"))

   (xdoc::p
    "The current implementation of this macro
     does not attempt to generate robust proofs.
     The generated proofs may implicitly rely on rules that,
     if disabled, may cause the proofs to fail.
     However, the generated theorems should be always provable.
     The implementation of this macro will be improved in the future
     to generate more robust proofs.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Future Work")

   (xdoc::p
    "This macro may be generalized from natural numbers to integer numbers,
     or to other suitably ordered domains.")

   (xdoc::p
    "Besides maxima, similar macros could be introduced to declaratively define
     minima, suprema, and infima.")))
