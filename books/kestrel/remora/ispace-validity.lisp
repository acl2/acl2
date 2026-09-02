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
     involves assigning sorts to ispaces [thesis] [arxiv] [esop].")
   (xdoc::p
    "The inference rules for ispaces in [thesis] [arxiv] [esop]
     prove judgements of the form @($\\Theta \\vdash \\iota :: \\gamma$),
     where @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\iota$) is an ispace,
     and @($\\gamma$) is a sort.
     Since our ASTs include sort information as part of the syntax,
     our inference rules prove judgements (i.e. define predicates)
     that omit explicit sort information.
     For the same reason,
     our sort environment is just a set of ispace variables in scope,
     each of which carries its own sort.")
   (xdoc::p
    "We formulate inference rules for dimension, shape, and ispace ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive dim-sort-checking-infrules
  :short "Inference rules for sort checking of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicate for individual dimensions,
     we define one for lists of dimensions,
     defined via the two rules @('empty') and @('cons');
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

(definductive shape/ispace-sort-checking-infrules
  :short "Inference rules for sort checking of shapes and ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(see dim-sort-checking-infrules),
     besides predicates for individual shapes and ispaces,
     we define predicates for lists of shapes and lists of ispaces.")
   (xdoc::p
    "The rules for individual shapes and ispaces follow [thesis] [arxiv] [esop],
     with the necessary structural adaptations to our ASTs,
     and with additional rules for the richer forms of our ASTs."))

  :preds ((shape-ok ivars shp)
          (shapes-ok ivars shps)
          (ispace-ok ivars isp)
          (ispaces-ok ivars isps))

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
            (shape-listp shps)
            (shapes-ok ivars shps))
           (shape-ok ivars (shape-append shps)))

   (splice ((ispace-var-setp ivars)
            (ispace-listp isps)
            (ispaces-ok ivars isps))
           (shape-ok ivars (shape-splice isps)))

   ;; lists of shapes:

   (empty ((ispace-var-setp ivars))
          (shapes-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (shapep shp)
          (shape-listp shps)
          (shape-ok ivars shp)
          (shapes-ok ivars shps))
         (shapes-ok ivars (cons shp shps)))

   ;; ispaces:

   (dim ((ispace-var-setp ivars)
         (dimp dim)
         (dim-ok ivars dim))
        (ispace-ok ivars (ispace-dim dim)))

   (shape ((ispace-var-setp ivars)
           (shapep shp)
           (shape-ok ivars shp))
          (ispace-ok ivars (ispace-shape shp)))

   ;; lists of ispaces:

   (empty ((ispace-var-setp ivars))
          (ispaces-ok ivars nil))

   (cons ((ispace-var-setp ivars)
          (ispacep isp)
          (ispace-listp isps)
          (ispace-ok ivars isp)
          (ispaces-ok ivars isps))
         (ispaces-ok ivars (cons isp isps)))))
