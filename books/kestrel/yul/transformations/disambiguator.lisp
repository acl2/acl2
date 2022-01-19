; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "renaming-variables")
(include-book "renaming-functions")
(include-book "unique-variables")
(include-book "unique-functions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ disambiguator
  :parents (transformations)
  :short "The @('Disambiguator') transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Disambiguator') transformation described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: Disambiguator],
     makes all the variable and function names globally unique
     by renaming them.")
   (xdoc::p
    "Conceptually, this transformation could be split into two:
     one that disambiguates variables, and one that disambiguates functions;
     the two are independent, and can be applied in any order.
     We follow this approach,
     by formalizing the disambiguation of variables and functions separately,
     and by defining @('Disambiguator') as their combination.")
   (xdoc::p
    "There are many possible ways
     to rename variables or functions so that they are globally unique.
     To avoid committing to a specific renaming approach,
     we characterize these transformations relationally instead of functionally:
     instead of defining a function
     that turns the original code into the transformed code,
     we define a predicate over original and transformed code
     that holds when the two have the same structure
     except for possibly the variable or function names.")
   (xdoc::p
    "This relational formulation of
     the disambiguation of variables and functions
     opens the door to defining each as the combination of
     a renaming relation that may or may not yield globally unique names,
     and an additional uniqueness requirement on the transformed code.
     Thus, the @('Disambiguator') transformation
     is characterized relationally as the combination of "
    (xdoc::seetopic "renaming-variables" "variable renaming")
    ", "
    (xdoc::seetopic "renaming-functions" "function renaming")
    ", "
    (xdoc::seetopic "unique-variables" "variable uniqueness")
    ", and "
    (xdoc::seetopic "unique-functions" "function uniqueness")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: define the relation
