; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ program-equivalence
  :parents (acl2-programming-language)
  :short "Program equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a notion of equivalence of ACL2 programs here:
     in terms of the ``top-level'' semantic function @(tsee exec-call):
     two programs are equivalent exactly when
     all function calls yield identical outcomes
     with respect to the two programs.")
   (xdoc::p
    "This is a functional equivalence:
     the two programs may have different non-functional properties,
     i.e. the same function call may take
     a different number of steps in the two programs
     (presumably because it is defined differently,
     or some other function directly or indirectly called by it
     is defined differently);
     but the two outcomes will be the same.")
   (xdoc::p
    "The equality of the two outcomes
     may involve errors or non-termination,
     besides termination without errors.
     That is, one yields an error iff the other one does;
     and one does not terminate iff the other one does not.")
   (xdoc::p
    "It is possible to define
     both stronger and weaker notions of program equivalence.
     A stronger notion could take non-functional properties into account.
     A weaker notion could only take certain function calls into account.
     We may revise our definition of program equivalence in the future,
     or perhaps introduce multiple such notions,
     which may be useful for different purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk program-equivp ((program1 programp)
                           (program2 programp))
  :returns (yes/no booleanp)
  :short "Equivalence of two programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This binary relation is indeed an equivalence:
     reflexive, symmetric, and transitive."))
  (forall (function arguments)
          (implies (and (symbol-valuep function)
                        (value-listp arguments))
                   (equal (exec-call function arguments program1)
                          (exec-call function arguments program2))))
  ///

  (defrule program-equivp-reflexive
    (program-equivp program program))

  (defrule program-equivp-symmetic
    (implies (program-equivp program1 program2)
             (program-equivp program2 program1))
    :rule-classes nil
    :disable program-equivp-necc
    :use (:instance program-equivp-necc
          (function (mv-nth 0 (program-equivp-witness program2 program1)))
          (arguments (mv-nth 1 (program-equivp-witness program2 program1)))))

  (defruled program-equivp-transitive
    (implies (and (program-equivp program1 program2)
                  (program-equivp program2 program3))
             (program-equivp program1 program3))
    :disable program-equivp-necc
    :use ((:instance program-equivp-necc
           (program1 program1)
           (program2 program2)
           (function (mv-nth 0 (program-equivp-witness program1 program3)))
           (arguments (mv-nth 1 (program-equivp-witness program1 program3))))
          (:instance program-equivp-necc
           (program1 program2)
           (program2 program3)
           (function (mv-nth 0 (program-equivp-witness program1 program3)))
           (arguments (mv-nth 1 (program-equivp-witness program1 program3)))))))
