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

(defxdoc+ ispace-checking
  :parents (static-semantics)
  :short "Ispace checking."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize Remora ispace checking via inference rules
     that correspond to the sorting rules in [thesis] [arxiv] [esop].
     Those sorting rules assign sorts to ispaces,
     via judgements of the form
     @($\\Theta \\vdash \\iota :: \\gamma$),
     where @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\iota$) is an ispace,
     and @($\\gamma$) is a sort.
     Our ASTs have the sort information already in the syntax,
     and thus the predicates (i.e. judgements) defined by our inference rules
     omit the explicit sort
     and model isort environments as sets of ispace variables.
     We formulate rules and judgements for dimensions, shapes, and ispaces."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-check-infrules
  :short "Inference rules for dimension checking."
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

  :preds ((dim-chk ivars dim)
          (dims-chk ivars dims))

  :irules

  ((var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-dim name) ivars))
        (dim-chk ivars (dim-var name)))

   (const ((ispace-var-setp ivars)
           (natp val))
          (dim-chk ivars (dim-const val)))

   (add ((ispace-var-setp ivars)
         (dims-chk ivars dims))
        (dim-chk ivars (dim-add dims)))

   (mul ((ispace-var-setp ivars)
         (dims-chk ivars dims))
        (dim-chk ivars (dim-mul dims)))

   (sub ((ispace-var-setp ivars)
         (dims-chk ivars dims))
        (dim-chk ivars (dim-sub dims)))

   (empty ((ispace-var-setp ivars))
          (dims-chk ivars nil))

   (cons ((ispace-var-setp ivars)
          (dimp dim)
          (dim-listp dims)
          (dim-chk ivars dim)
          (dims-chk ivars dims))
         (dims-chk ivars (cons dim dims)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: shapes & ispaces
