; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmin-int

  :parents (std::std/util-extensions std/util)

  :short "Declaratively define the minimum of a set of integer numbers."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro captures the mathematical notation
      @($\\min\\: \\{y \\in \\mathbb{Z} \\mid \\psi[x_1,\\ldots,x_n,y]\\}$),
      where @($\\mathbb{Z}$) is the set of integer numbers,
      @($n \\geq 0$),
      and @($\\psi[x_1,\\ldots,x_n,y]$) is a formula
      that depends on @($x_1,\\ldots,x_n$) and @($y$).
      Each value of the tuple @($\\langle x_1, \\ldots, x_n \\rangle$)
      defines a set of integer numbers,
      which may or may not have a minimum;
      if it does not, we regard @($\\min$) as returning a special value
      distinct from all the integer numbers, e.g. @($\\bot$).
      Thus, the mathematical notation above defines a function
      from @($n$)-tuples to integer numbers or @($\\bot$).")

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
      in particular to establish that the minimum exists
      without having to calculate it explicitly,
      and to establish that the minimum is a certain value.")

    (xdoc::p
     "See @(tsee defmax-nat) for a related tool."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defmin-int f y (x1 ... xn)"
     "  body"
     "  :guard ...          ; default t"
     "  :verify-guards ...  ; default t"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

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
       Note that the syntax of @('defmin-int') is similar to
       the syntax of @(tsee defchoose) in this respect."))

    (xdoc::desc
     "@('(x1 ... xn)')"
     (xdoc::p
      "List of the names of the zero or more variables
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
       emphasizing its dependence on the variables."))

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
      Nonetheless, the implementation of this macro
      may be improved in the future
      to validate its inputs more thoroughly."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "See the file @('defmin-int-template.lisp') for more explanations
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
     (xdoc::codeblock
      "(defun f.elementp (x1 ... xn y)"
      "  (declare (xargs :guard (and guard<x1,...,xn> (integerp y))))"
      "  body<x1,...,xn,y>)"))

    (xdoc::desc
     "@('f.lboundp')"
     (xdoc::p
      "Auxiliary predicate asserting that
       @('y') is a lower bound of the set defined by @('x1'), ..., @('xn'),
       along with associated theorems.")
     (xdoc::codeblock
      "(defun-sk f.lboundp (x1 ... xn y)"
      "  (declare (xargs :guard (and guard<x1,...,xn> (integerp y))))"
      "  (forall (y1)"
      "          (impliez (and (integerp y1)"
      "                        (f.elementp x1 ... xn y1))"
      "                   (<= (ifix y) y1)))"
      "  :rewrite (implies (and (f.lboundp x1 ... xn y)"
      "                         (integerp y1)"
      "                         (f.elementp x1 ... xn y1))"
      "                    (<= (ifix y) y1)))"
      ""
      "(defthm booleanp-of-f.lboundp"
      "  (booleanp (f.lboundp x1 ... xn y)))"))

    (xdoc::desc
     "@('f.existsp')"
     (xdoc::p
      "Auxiliary predicate asserting that
       the set defined by @('x1'), ..., @('xn') has a minimum,
       along with associated theorems.")
     (xdoc::codeblock
      "(defun-sk f.existsp (x1 ... xn)"
      "  (declare (xargs :guard guard<x1,...,xn>))"
      "  (exists (y)"
      "          (and (integerp y)"
      "               (f.elementp x1 ... xn y)"
      "               (f.lboundp x1 ... xn y))))"
      ""
      "(defthm booleanp-of-f.existsp"
      "  (booleanp (f.existsp x1 ... xn)))"))

    (xdoc::desc
     "@('f')"
     (xdoc::p
      "The function that returns the minimum if it exists (otherwise @('nil')),
       along with associated theorems.")
     (xdoc::codeblock
      "(defun f (x1 ... xn)"
      "  (declare (xargs :guard guard<x1,...,xn>))"
      "  (if (f.existsp x1 ... xn)"
      "      (f.existsp-witness x1 ... xn)"
      "    nil))"
      ""
      "(defthm maybe-integerp-of-f"
      "  (maybe-integerp (f x1 ... xn)))"
      ""
      "(defthm integerp-of-f-equal-f.existsp"
      "  (equal (integerp (f x1 ... xn))"
      "         (f.existsp x1 ... xn)))"
      ""
      "(defthm integerp-of-f-when-f.existsp"
      "  (implies (f.existsp x1 ... xn)"
      "           (integerp (f x1 ... xn)))"
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
      "(defthm f.lboundp-of-f-when-f.existsp"
      "  (implies (f.existsp x1 ... xn)"
      "           (f.lboundp x1 ... xn (f x1 ... xn))))"
      ""
      "(defthm f-leq-when-f.existsp-linear"
      "  (implies (and (f.existsp x1 ... xn)"
      "                (f.elementp x1 ... xn y1) ;; bind free y1"
      "                (integerp y1))"
      "           (<= (f x1 ... xn) y1))"
      "  :rule-classes :linear)"
      ""
      "(defthm f-leq-when-f.existsp-rewrite"
      "  (implies (and (f.existsp x1 ... xn)"
      "                (f.elementp x1 ... xn y1)"
      "                (integerp y1))"
      "           (<= (f x1 ... xn) y1))"
      ""
      "(defthm f-geq-when-f.existsp-linear"
      "  (implies (and (f.existsp x1 ... xn)"
      "                (f.lboundp x1 ... xn y1) ;; bind free y1"
      "                (integerp y1))"
      "           (>= (f x1 ... xn) y1))"
      "  :rule-classes :linear)"
      ""
      "(defthm f-geq-when-f.existsp-rewrite"
      "  (implies (and (f.existsp x1 ... xn)"
      "                (f.lboundp x1 ... xn y1)"
      "                (integerp y1))"
      "           (>= (f x1 ... xn) y1))"))

    (xdoc::desc
     "@('f.existsp-when-nonempty-and-bounded')"
     (xdoc::p
      "The helper theorem to establish that the minimum exists
       by exhibiting a member and a bound of the set.")
     (xdoc::codeblock
      "(defthm f.existsp-when-nonempty-and-bounded"
      "  (implies (and (integerp y0)"
      "                (f.elementp x1 ... xn y0)"
      "                (integerp y1)"
      "                (f.lboundp x1 ... xn y1))"
      "           (f.existsp x1 ... xn))"
      "  :rule-classes nil)"))

    (xdoc::desc
     "@('f.equal-when-member-and-lbound')"
     (xdoc::p
      "The helper theorem to establish that the minimum has a certain value
       by showing that that value is
       both a member and a lower bound of the set.")
     (xdoc::codeblock
      "(defthm f.equal-when-member-and-lbound"
      "  (implies (and (integerp y)"
      "                (f.elementp x1 ... xn y)"
      "                (f.lboundp x1 ... xn y))"
      "           (equal (f x) y))"
      "  :rule-classes nil)"))

    (xdoc::p
     "The current implementation of this macro
      does not attempt to generate robust proofs.
      The generated proofs may implicitly rely on rules that,
      if disabled, may cause the proofs to fail.
      However, the generated theorems should be always provable.
      The implementation of this macro will be improved in the future
      to generate more robust proofs."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Future Work")

   (xdoc::p
    "This macro may be generalized from integer numbers
     to other suitably ordered domains.")

   (xdoc::p
    "Besides minima and maxima (also see @(tsee defmax-nat)),
     similar macros could be introduced to declaratively define
     suprema and infima.")))
