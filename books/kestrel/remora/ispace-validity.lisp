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

(defxdoc+ ispace-validity
  :parents (static-semantics)
  :short "Validity of ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "The inference rules for ispaces in [thesis] [arxiv] [esop]
     prove judgements of the form @($\\Theta \\vdash \\iota :: \\gamma$),
     where @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\iota$) is an ispace (called `index' in those publications),
     and @($\\gamma$) is a sort (`dimension' or `shape').")
   (xdoc::p
    "Since our ASTs include sort information as part of the syntax,
     our inference rules prove judgements (i.e. define predicates)
     that omit explicit sort information,
     i.e. just include @($\\Theta$) and @($\\iota$):
     they say that the ispace satisfies all the static validity conditions
     in the context of the sort environment.
     Since ispace variables carry their own sorts,
     our sort environment is just a set of ispace variables in scope.")
   (xdoc::p
    "We define validity predicates for dimension, shape, and ispace ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-validity-definition
  :short "Inference rules that define dimension validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicate for individual dimensions,
     we define one for lists of dimensions,
     via the two rules @('empty') and @('cons');
     this corresponds to the use of @($\\cdots$) in [thesis] [arxiv] [esop].
     The rules for individual dimensions follow [thesis] [arxiv] [esop],
     with the addition of rules for multiplication and subtraction,
     which are analogous to the one for addition."))

  :preds ((dim-ok ivars dim)
          (dims-ok ivars dims))

  :irules

  (;; dimensions:

   (var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-dim name) ivars))
        (dim-ok ivars (dim-var name)))

   (const ((ispace-var-setp ivars)
           (natp val))
          (dim-ok ivars (dim-const val)))

   (add ((ispace-var-setp ivars)
         (dim-listp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-add dims)))

   (mul ((ispace-var-setp ivars)
         (dim-listp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-mul dims)))

   (sub ((ispace-var-setp ivars)
         (dim-listp dims)
         (dims-ok ivars dims))
        (dim-ok ivars (dim-sub dims)))

   ;; lists of dimensions:

   (empty ((ispace-var-setp ivars))
          (dims-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (dimp dim)
          (dim-listp dims)
          (dim-ok ivars dim)
          (dims-ok ivars dims))
         (dims-ok ivars (cons dim dims)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive shape/ispace-validity-definition
  :short "Inference rules that define shape and ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(see dim-validity-definition),
     besides predicates for individual shapes and ispaces,
     we define predicates for lists of shapes and lists of ispaces.")
   (xdoc::p
    "The rules for individual shapes and ispaces follow [thesis] [arxiv] [esop],
     with the necessary structural adaptations to our ASTs,
     and with additional rules for splices."))

  :preds ((shape-ok ivars shape)
          (shapes-ok ivars shapes)
          (ispace-ok ivars ispace)
          (ispaces-ok ivars ispaces))

  :irules

  (;; shapes:

   (var ((ispace-var-setp ivars)
         (stringp name)
         (set::in (ispace-var-shape name) ivars))
        (shape-ok ivars (shape-var name)))

   (dims ((ispace-var-setp ivars)
          (dim-listp dims)
          (dims-ok ivars dims))
         (shape-ok ivars (shape-dims dims)))

   (append ((ispace-var-setp ivars)
            (shape-listp shapes)
            (shapes-ok ivars shapes))
           (shape-ok ivars (shape-append shapes)))

   (splice ((ispace-var-setp ivars)
            (ispace-listp ispaces)
            (ispaces-ok ivars ispaces))
           (shape-ok ivars (shape-splice ispaces)))

   ;; lists of shapes:

   (empty ((ispace-var-setp ivars))
          (shapes-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (shapep shape)
          (shape-listp shapes)
          (shape-ok ivars shape)
          (shapes-ok ivars shapes))
         (shapes-ok ivars (cons shape shapes)))

   ;; ispaces:

   (dim ((ispace-var-setp ivars)
         (dimp dim)
         (dim-ok ivars dim))
        (ispace-ok ivars (ispace-dim dim)))

   (shape ((ispace-var-setp ivars)
           (shapep shape)
           (shape-ok ivars shape))
          (ispace-ok ivars (ispace-shape shape)))

   ;; lists of ispaces:

   (empty ((ispace-var-setp ivars))
          (ispaces-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (ispacep ispace)
          (ispace-listp ispaces)
          (ispace-ok ivars ispace)
          (ispaces-ok ivars ispaces))
         (ispaces-ok ivars (cons ispace ispaces)))))
