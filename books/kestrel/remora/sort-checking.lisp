; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "std/util/definductive" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ sort-checking
  :parents (static-semantics)
  :short "Sort checking."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to ispaces, because the static correctness of ispaces
     involves assigning sorts to ispaces [thesis] [arvix] [esop].")
   (xdoc::p
    "The inference rules for ispaces in [thesis] [arxiv] [esop]
     prove judgements of the form @($\\Theta \\vdash \\iota :: \\gamma$),
     where @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\iota$) is an ispace,
     and @($\\gamma$) is a sort.
     Since our ASTs include sort information as part of the syntax,
     our inference rules prove judgements (i.e. define predicates)
     that omit explicity sort information.
     For the same reason,
     our sort environment is just a set of ispace variables in scope,
     each of which carries its own sort.")
   (xdoc::p
    "We formulate inference rules for dimension, shape, and ispace ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-ok-infrules
  :short "Inference rules for sort checking of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicate for individual dimensions,
     we introduce one for lists of dimensions,
     defined via the two rules @('empty') and @('cons');
     this corresponds to the use of @($\\cdots$) in [thesis] [arxiv] [esop].
     The rules for individual dimensions follow [thesis] [arxiv] [esop],
     with the addition of rules for multiplication and subtraction,
     which are analogous the one for addition."))

  :preds ((dim-ok ivars dim)
          (dims-ok ivars dims))

  :irules

  ((var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-dim name) ivars))
        (dim-ok ivars (dim-var name)))

   (const ((ispace-var-setp ivars)
           (natp val))
          (dim-ok ivars (dim-const val)))

   (add ((ispace-var-setp ivars)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-add dims)))

   (mul ((ispace-var-setp ivars)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-mul dims)))

   (sub ((ispace-var-setp ivars)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-sub dims)))

   (empty ((ispace-var-setp ivars))
          (dims-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (dimp dim)
          (dim-listp dims)
          (dim-ok ivars dim)
          (dims-ok ivars dims))
         (dims-ok ivars (cons dim dims)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: shapes & ispaces
