; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "utilities/top")

(include-book "common-concepts")
(include-book "common-options")

(include-book "casesplit")
(include-book "casesplit-doc")

(include-book "isodata")
(include-book "isodata-doc")

(include-book "parteval")
(include-book "parteval-doc")

(include-book "restrict")
(include-book "restrict-doc")

(include-book "tailrec")
(include-book "tailrec-doc")

; (depends-on "images/apt-logo.png")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc apt

  :parents (acl2::kestrel-books acl2::macro-libraries acl2::projects)

  :short "APT (Automated Program Transformations) is a library of tools
          to transform programs and program specifications
          with automated support."

  :long

  (xdoc::topstring

   (xdoc::img :src "res/kestrel-apt-images/apt-logo.png")

   (xdoc::p
    "The APT transformation tools operate on ACL2 artifacts (e.g. functions)
     and generate corresponding transformed artifacts
     along with theorems asserting the relationship (e.g. equivalence)
     between old and new artifacts.
     The APT transformation tools modify the ACL2 state
     only by submitting sound and conservative events;
     they cannot introduce unsoundness or inconsistency on their own.")

   (xdoc::p
    "APT can be used in <i>program synthesis</i>,
     to derive provably correct implementations from formal specifications
     via sequences of refinement steps carried out via transformations.
     The specifications may be declarative or executable.
     The APT transformations can
     synthesize executable implementations from declarative specifications,
     as well as optimize executable specifications or implementations.
     The APT transformations can also be used
     to generate a variety of diverse implementations
     of the same specification.")

   (xdoc::p
    "APT can also be used in <i>program analysis</i>,
     to help verify existing programs, suitably embedded in the ACL2 logic,
     by raising their level of abstraction via transformations
     that are inverses of the ones used in stepwise program refinement.
     The formal gap between a program and its specification
     can be bridged by applying
     top-down transformations to the specification
     and bottom-up transformations to the code,
     until they ``meet in the middle''.")

   (xdoc::p
    "APT enables the user
     to focus on the creative parts of the program synthesis or analysis process,
     leaving the more mechanical parts to the automation provided by the tools.
     The user guides the process
     by choosing which transformation to apply at each point
     and by supplying key theorems
     (e.g. applicability conditions of transformations),
     while APT takes care of the lower-level, error-prone details
     with speed and assurance.")

   (xdoc::p
    "The <see topic='@(url community-books)'>Community Books</see>
     currently contain only a few APT transformations.
     More transformations exist in Kestrel Institute's private files,
     but they will be eventually moved to the Community Books;
     this includes the latest version of the @('simplify-defun') transformation
     described in the
     <a href=\"http://www.cs.utexas.edu/users/moore/acl2/workshop-2017\"
     >ACL2-2017 Workshop</a> paper
     `A Versatile, Sound Tool for Simplifying Definitions'.")

   (xdoc::p
    "Also see the "
    (xdoc::a :href "http://www.kestrel.edu/home/projects/apt"
      "APT Project Web page") ".")))

(xdoc::order-subtopics apt (common-concepts
                            common-options
                            casesplit
                            isodata
                            parteval
                            restrict
                            tailrec
                            utilities))

(xdoc::add-resource-directory "kestrel-apt-images" "images")
(xdoc::add-resource-directory "kestrel-apt-design-notes" "design-notes")
