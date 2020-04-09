; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defflatsum")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defflatsum

  :parents (fty-extensions fty)

  :short "Introduce a fixtype for
          the flat (i.e. not tagged) sum of disjoint fixtypes."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is a very preliminary tool for now.
      In particular, it does not perform a thorough input validation.")

    (xdoc::p
     "@(tsee deftagsum) introduces
      a tagged sum of fixtypes,
      some of which may partially or totally overlap
      (the tags distinguish them in the sum);
      it is like a disjoint union in set theory.
      In contrast, this @('defflatsum') macro introduces
      a flat (i.e. untagged) sum of fixtypes;
      it is like a union in set theory.
      However, the summand fixtypes must be pairwise disjoint,
      so that the union is actually disjoint."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defflatsum type"
     "            (:kwd1 type1)"
     "            ..."
     "            (:kwdn typen)"
     "            :pred ..."
     "            :fix ..."
     "            :equiv ..."
     "            :parents ..."
     "            :short ..."
     "            :long ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':type')"
     (xdoc::p
      "A symbol that specifies the name of the new fixtype."))

    (xdoc::desc
     (list
      "@('(:kwd1 type1)')"
      "@('...')"
      "@('(:kwdn typen)')")
     (xdoc::p
      "Two or more doublets, one for each summand.
       The first component of each doublet is a keyword
       that identifies the summand;
       all these keywords must be distinct.
       The second component of each doublet is an existing fixtype
       that is a summand;
       these fixtypes must be pairwise disjoint."))

    (xdoc::desc
     "@(':pred')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's recognizer.
       If this is @('nil') (the default),
       the name of the recognizer is @('type') followed by @('-p')."))

    (xdoc::desc
     "@(':fix')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's fixer.
       If this is @('nil') (the default),
       the name of the fixer is @('type') followed by @('-fix')."))

    (xdoc::desc
     "@(':equiv')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's equivalence.
       If this is @('nil') (the default),
       the name of the equivalence is @('type') followed by @('-equiv')."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to
       the XDOC topic generated for the fixtype.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defflatsum

    (xdoc::p
     "The fixtypes @('type1'), ..., @('typen') must be pairwise disjoint.
      Currently this proof obligation
      is not quite explicated as a theorem to be proved,
      but the generated @(tsee defflexsum) will likely fail
      if the pairwise disjointness does not hold."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "This macro generates a @(tsee defflexsum)
      with some accompanying theorems:")
    (xdoc::codeblock
     "(defflexsum type"
     "  (:kwd1 :fields ((get :type type1 :acc-body x))"
     "         :ctor-body get"
     "         :cond (type1p x))"
     "  (:kwd2 :fields ((get :type type2 :acc-body x))"
     "         :ctor-body get"
     "         :cond (type2p x))"
     "  ..."
     "  (:kwdn :fields ((get :type typen :acc-body x))"
     "         :ctor-body get)"
     "  ///"
     "  (defthm typep-when-type1p"
     "    (implies (type1p x)"
     "             (typep x)))"
     "  (defthm typep-when-type2p"
     "    (implies (type2p x)"
     "             (typep x)))"
     "  ..."
     "  (defthm typep-when-typenp"
     "    (implies (typenp x)"
     "             (typep x))))")
    (xdoc::p
     "Note that the last summand does not have @(':cond'),
      while all the previous ones do."))))
