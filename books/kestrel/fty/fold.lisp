; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc fold
  :parents (fty fty-extensions)
  :short "Notion of general folds for fixtypes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The FTY library provides event macros to introduce algebraic data types.
     Algebraic data types have a naturally associated notion of general folds.
     Thus, it makes sense for the FTY library
     to also provide event macros to introduce folds.
     This manual page describes, via an example,
     the notion of general folds for algebraic data types;
     it also discusses ideas for FTY event macros to introduce folds.")
   (xdoc::p
    "Consider the following mutually recursive data types,
     for a form of arithmetic and boolean expressions:")
   (xdoc::codeblock
    "(deftypes exprs"
    "  (deftagsum aexpr"
    "    (:const ((value acl2::int)))"
    "    (:var ((name string)))"
    "    (:add ((left aexpr) (right aexpr)))"
    "    (:cond ((test bexpr) (left aexpr) (right aexpr)))"
    "    :pred aexprp)"
    "  (deftagsum bexpr"
    "    (:true ())"
    "    (:false ())"
    "    (:and ((left bexpr) (right bexpr)))"
    "    (:less ((left aexpr) (right aexpr)))"
    "    :pred bexprp))")
   (xdoc::p
    "This introduces two mutually recursive data types,
     which we can write as follows in more common notation,
     where the constructors are curried:")
   (xdoc::codeblock
    "type aexpr = const int"
    "           | var string"
    "           | add aexpr aexpr"
    "           | neg aexpr"
    "           | cond bexpr aexpr aexpr"
    "type bexpr = true"
    "           | false"
    "           | and bexpr bexpr"
    "           | less aexpr aexpr")
   (xdoc::p
    "A general fold over these two types consists of two higher-order functions,
     one per type, with the following types:")
   (xdoc::codeblock
    "afold<A,B> : (int -> A) ->"
    "             (string -> A) ->"
    "             (A -> A -> A) ->"
    "             (A -> A) ->"
    "             (B -> A -> A -> A) ->"
    "             (aexpr -> A)"
    "bfold<A,B> : B ->"
    "             B ->"
    "             (B -> B -> B) ->"
    "             (A -> A -> B) ->"
    "             (bexpr -> B)")
   (xdoc::p
    "These functions are parameterized over types @('A') and @('B')
     to which they map @('aexpr') and @('bexpr').
     Each function takes constant and function arguments
     that have the same ``shape'' of the constructors,
     but with @('aexpr') and @('bexpr') replaced with @('A') and @('B').")
   (xdoc::p
    "These functions are defined as follows:")
   (xdoc::codeblock
    "afold f_const f_var f_add f_neg f_cond (const i) = f_const i"
    "afold f_const f_var f_add f_neg f_cond (var s) = f_var s"
    "afold f_const f_var f_add f_neg f_cond (add a1 a2) ="
    "  f_add (afold f_const f_var f_add f_neg f_cond a1)"
    "        (afold f_const f_var f_add f_neg f_cond a2)"
    "afold f_const f_var f_add f_neg f_cond (neg a) =
       f_neg (afold f_const f_var f_add f_neg f_cond a1)"
    "afold f_const f_var f_add f_neg f_cond (cond b a1 a2) ="
    "  f_cond (bfold c_true c_false f_and f_less b)"
    "         (afold f_const f_var f_add f_cond a1)"
    "         (afold f_const f_var f_add f_cond a2)"
    "bfold c_true c_false f_and f_less true = c_true"
    "bfold c_true c_false f_and f_less false = c_false"
    "bfold c_true c_false f_and f_less (and b1 b2) ="
    "  f_and (bfold c_true c_false f_and f_less b1)"
    "        (bfold c_true c_false f_and f_less b2)"
    "bfold c_true c_false f_and f_less (less a1 a2) ="
    "  f_less (afold f_const f_var f_add f_cond a1)"
    "         (afold f_const f_var f_add f_cond a2)")
   (xdoc::p
    "In other words, the folds ``replace'' each constructor of the data types
     with the corresponding constant or function passed as argument.
     Recall that every value of the data types is expressible
     as a ground term over the constructors.
     For instance, we have")
   (xdoc::codeblock
    "afold ... (add   (const   3) (var   \"x\")) ="
    "          (f_add (f_const 3) (f_var \"x\"))")
   (xdoc::p
    "where @('...') stands for @('f_const ... f_cond'),
     and where spaces have been added to align things.")
   (xdoc::p
    "There are many different possible choices for the folds'
     result types (@('A') and @('B') above)
     and constant and function arguments (@('c_true'), @('f_add'), etc. above).
     We could consider providing an FTY event macro for general folds,
     which would take a lot of inputs;
     @(tsee defvisitor) seems related to this.
     There are two fairly natural specific fold structures:")
   (xdoc::ul
    (xdoc::li
     "One is characterized by
      all the result types being the same type @('R')
      (i.e. @('A = B = R') in the example above),
      the constants being a specific element @('base') of @('R')
      (e.g. @('c_true = c_false = base') in the example above),
      the non-recursive functions also returning @('base')
      (e.g. @('f_const(x) = f_var(x) = base') in the example above),
      the functions with one recursive argument returning
      the fold result on that argument
      (e.g. @('f_neg(x) = x') in the example above),
      the functions with two recursive arguments
      combining the fold results on those arguments
      with a binary operation @('comb') on @('R')
      (e.g. @('f_add(x,y) = f_and(x,y) = f_less(x,y) = comb(x,y)')
      in the example above),
      and the functions with three or more recursive arguments
      combining the fold results on those arguments with @('comb')
      in some determined order
      (e.g. @('f_cond(x,y,z) = comb(x,comb(y,z))') in the example above).
      The boilerplate code just explained can be overridden case by case,
      e.g. f_const could be overridden
      to return a value of @('R') that depends on the integer.
      We call this a `reducing' fold,
      because it reduces values of the algebraic data types
      to values of a usually simpler type @('R'),
      e.g. add up all the nodes of a tree.
      Sometimes @('(R, comb, base)') forms a monoid,
      but that is not necessary.")
    (xdoc::li
     "Another one is characterized by
      each result type being the same as the corresponding data type
      (e.g. @('A = aexpr') and @('B = bexpr') in the example above),
      and each constant and function being the corresponding constructor
      (e.g. @('c_true = true'), @('f_add = add'), etc. in the example above).
      The boilerplate code just explained can be overridden case by case,
      e.g. f_const  could be overridden to increment the integer by one.
      We call this a `mapping' fold,
      because it maps values of the algebraic data types
      to values of the same algebraic data types,
      with possibly some variations,
      e.g. turning a list of integers into a list of doubled integers."))
   (xdoc::p
    "The @(tsee deffold-reduce) event macro generates reducing folds and
     the @(tsee deffold-map) event macro generates mapping folds.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; example in the manual page above:
(encapsulate
  ()
  (local
   (deftypes exprs
     (deftagsum aexpr
       (:const ((value acl2::int)))
       (:var ((name string)))
       (:add ((left aexpr) (right aexpr)))
       (:cond ((test bexpr) (left aexpr) (right aexpr)))
       :pred aexprp)
     (deftagsum bexpr
       (:true ())
       (:false ())
       (:and ((left bexpr) (right bexpr)))
       (:less ((left aexpr) (right aexpr)))
       :pred bexprp))))
