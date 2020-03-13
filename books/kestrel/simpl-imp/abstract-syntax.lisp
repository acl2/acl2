; Simple Programming Language Imp Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Teruhiro Tagomori (NRI SecureTechnologies, Ltd.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SIMPL-IMP")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

; this is so that FTY::DEFLIST below generates more theorems:
(local (include-book "std/lists/append" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (imp-language)
  :short "Abstract syntax of Imp."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize Imp's
     arithmetic expressions,
     boolean expressions, and
     commands,
     as free algebraic fixtypes."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum aexp
  :parents (abstract-syntax)
  :short "Fixtype of Imp arithmetic expressions."
  :long
  (xdoc::topstring-p
   "We use (any) strings as variable names.")
  (:const ((value int)))
  (:var ((name string)))
  (:add ((left aexp) (right aexp)))
  (:mul ((left aexp) (right aexp)))
  :pred aexpp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bexp
  :parents (abstract-syntax)
  :short "Fixtype of Imp boolean expressions."
  (:const ((value bool)))
  (:equal ((left aexp) (right aexp)))
  (:less ((left aexp) (right aexp)))
  (:not ((arg bexp)))
  (:and ((left bexp) (right bexp)))
  :pred bexpp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes comms

  (fty::deftagsum comm
    :parents (abstract-syntax)
    :short "Fixtype of Imp commands."
    :long
    (xdoc::topstring
     (xdoc::p
      "We have assignments, conditionals, and loops.
       It is convenient to capture sequentialization via command lists;
       note that the branches of conditionals and the body of loops
       are command lists, not single commands."))
    (:asg ((var string) (exp aexp)))
    (:if ((cond bexp) (then comm-list) (else comm-list)))
    (:while ((cond bexp) (body comm-list)))
    :pred commp)

  (fty::deflist comm-list
    :parents (abstract-syntax)
    :short "Fixtype of true lists of Imp commands."
    :long
    (xdoc::topstring
     (xdoc::p
      "An empty command list captures a no-op,
       called `skip' in typical formulations of Imp."))
    :elt-type comm
    :true-listp t
    :elementp-of-nil nil
    :pred comm-listp))
