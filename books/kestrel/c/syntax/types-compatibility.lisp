; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "types")

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "kestrel/data/treemap/submap-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/product-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)

(acl2::controlled-configuration)

(local (include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/submap" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/product" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/induction" :dir :system))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types-compatibility
  :parents (types)
  :short "Compatibility and composites of C types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define when two types are compatible
     and construct the composite of two compatible types
     [C17:6.2.7] [C23:6.2.7]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc types-compatibility-notes
  :short "Notes on interpreting C type compatibility."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type compatibility is not as well-behaved as one would hope.
     At first glance, one might expect an equivalence relation,
     but this is certainly not the case.
     Compatibility is reflexive and symmetric,
     but not transitive.
     For instance, consider the following functions.")
   (xdoc::codeblock
    "int foo();"
    ""
    "int bar(int x);"
    ""
    "int baz(double x);")
   (xdoc::p
    "In this example, the types of @('bar') and @('baz')
     are both compatible with the type of @('foo').
     However, the types of @('bar') and @('baz')
     are not compatible with each other.")
   (xdoc::p
    "Perhaps a better way to view compatibility
     is in terms of the existence of some common lower bound
     according to some imagined notion of type ordering.
     We might say that type @('int [10]') ``refines'' @('int []'),
     that the type of @('int foo(int x)') refines the type of @('int foo()'),
     etc.
     Furthermore, the greatest common lower bound
     would be a type composite,
     making this notion very attractive.
     Unfortunately, it is an imperfect model.
     It works for C23, but not for C17,
     where old-style function types obstruct any such order.")
   (xdoc::p
    "Recall that two old-style function types are compatible
     regardless of their parameter types,
     while a prototype is compatible with an old-style function type
     only if their parameter types agree after default argument promotion
     [C17:6.7.6.3/15, footnote 149].
     Consider the following functions.")
   (xdoc::codeblock
    "int f(x) int x; { return x; }"
    ""
    "int g(x) double x; { return x; }"
    ""
    "int p(int x);"
    ""
    "int q(double x);")
   (xdoc::p
    "The types of @('f') and @('g') are compatible.
     The type of @('p') is compatible with that of @('f') but not @('g'),
     and the type of @('q') is compatible with that of @('g') but not @('f').
     Indeed, no prototype is compatible with the types of both @('f') and @('g'),
     since its parameter type would have to be compatible
     with both @('int') and @('double').")
   (xdoc::p
    "Now suppose that two types are compatible exactly when
     they have a common lower bound under some pre-order.
     Then a type is compatible with everything its lower bounds are:
     if @('z') is a lower bound of @('x')
     and @('y') is compatible with @('z'),
     their common lower bound is, by transitivity,
     also a common lower bound of @('x') and @('y'),
     so @('y') is compatible with @('x').
     In particular, @('z') itself is compatible with @('x'),
     being a common lower bound of the two.")
   (xdoc::p
    "Since the types of @('f') and @('g') are compatible,
     they have a common lower bound @('z'),
     which is therefore compatible with both
     and hence a function type.
     Every function type is compatible with some prototype:
     a prototype is compatible with itself,
     @('int ()') is compatible with the type of @('p'),
     and an old-style function type is compatible with the prototype
     whose parameter types are its own after default argument promotion.
     A prototype @('s') compatible with @('z')
     is then also compatible with the types of both @('f') and @('g'),
     which we saw is impossible.
     Hence no such pre-order exists.")
   (xdoc::p
    "C23 removes identifier lists from function declarators
     and makes @('()') equivalent to @('(void)'),
     so old-style function types no longer exist there
     and the model is not obstructed.")
   (xdoc::p
    "Because this order-based notion is well-behaved on all but
     C17 old-style function types,
     it may be useful to define such a type ordering
     which relates to compatbility/composites in all but this corner case.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-kind-compatible-3p ((x type-array-kindp)
                                       (y type-array-kindp))
  :returns (3vl 3p)
  :short "Check whether two array kinds are compatible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Read literally, C17 and C23 require that two array types be compatible
     iff their element types are compatible and,
     when both size specifiers are present
     and are integer constant expressions,
     their values are equal [C17:6.7.6.2/6] [C23:6.7.7.3/6].
     Under this strict reading,
     two arrays with initializer-inferred sizes
     would be compatible iff their element types are compatible.")
   (xdoc::p
    "However, the implementations we examined
     do not follow that literal reading.
     For compatibility, they treat an initializer-inferred size
     as if it had been supplied
     by an integer constant expression size specifier.
     We follow that practice here.
     The same treatment is proposed in "
    (xdoc::ahref
     "https://www.open-std.org/jtc1/sc23p2/WG14/www/docs/n3495.htm"
     "WG14 N3495")
    ", which has not been adopted.")
   (xdoc::p
    "Accordingly, when both array kinds
     are @(':const-len')
     and both lengths are determined,
     we require the lengths to be equal.
     If the length values are unknown, the result is unknown.
     If one kind is @(':unknown-complete'), the result is unknown
     only if the other may be constant length.
     All other cases are compatible."))
  (type-array-kind-case
   x
   :const-len
   (type-array-kind-case
    y
    :const-len (if (or (not x.len)
                       (not y.len))
                   :unknown
                 (equal x.len y.len))
    :unknown-complete :unknown
    :otherwise t)
   :otherwise (if (and (type-array-kind-case x :unknown-complete)
                       (or (type-array-kind-case y :const-len)
                           (type-array-kind-case y :unknown-complete)))
                  :unknown
                t)))

(defrule type-array-kind-compatible-3p-under-iff-when-same
  (iff (type-array-kind-compatible-3p x x)
       t)
  :enable type-array-kind-compatible-3p)

(defrule 3possibly-type-array-kind-compatible-3p-when-same
  (3possibly (type-array-kind-compatible-3p x x))
  :enable type-array-kind-compatible-3p)

(defrule type-array-kind-compatible-3p-symmetric
  (equal (type-array-kind-compatible-3p y x)
         (type-array-kind-compatible-3p x y))
  :enable type-array-kind-compatible-3p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-compatible-3p-aux
  (define type-compatible-3p-aux ((x typep)
                                  (y typep)
                                  (completions type-completions-p)
                                  (assumed uid-pair-setp)
                                  (ienv ienvp))
    :returns (3vl 3p)
    :short "Auxiliary function for checking whether
            two @(see type)s are compatible."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee type-compatible-3p) for the notion of compatibility
       and the meaning of the three-valued result.")
     (xdoc::p
      "The @('assumed') set contains the pairs of @(see UID)s
       of the tagged structure types whose members are being compared,
       i.e. whose compatibility is currently assumed.
       When such a pair is encountered again while comparing the members,
       it is accepted as compatible.
       The set only grows along the recursion,
       and only by pairs of UIDs of complete types,
       i.e. of keys of the completions map,
       so the number of pairs of keys not in the set
       serves as the first component of the measure."))
    (b* (((when (or (type-case x '(:unknown :unknown-builtin))
                    (type-case y '(:unknown :unknown-builtin))))
          :unknown)
         ((when (type-case x :unknown-scalar))
          (3and (type-scalar-3p y) :unknown))
         ((when (type-case y :unknown-scalar))
          (3and (type-scalar-3p x) :unknown))
         ((when (type-case x :unknown-arithmetic))
          (3and (type-arithmetic-3p y) :unknown))
         ((when (type-case y :unknown-arithmetic))
          (3and (type-arithmetic-3p x) :unknown)))
      ;; Both types are known.
      (type-case
        x
        :struct
        (type-case
          y
          :struct
          (b* (((when (uid-equal x.uid y.uid)) t)
               (same-tunit? (and x.tunit?
                                 y.tunit?
                                 (equal x.tunit? y.tunit?)))
               (c23p? (c::standard-case (ienv->std ienv) :c23)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* (((unless (equal x.tag/members.tag y.tag/members.tag))
                      nil)
                     ;; Distinct types in the same translation unit.
                     ((when (and same-tunit? (not c23p?)))
                      nil)
                     (assumed (uid-pair-sfix assumed))
                     (pair (make-uid-pair :first x.uid :second y.uid))
                     ;; The pair is already assumed compatible.
                     ((when (treeset::in pair assumed))
                      t)
                     (completions (type-completions-fix completions))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ;; An incomplete struct is compatible
                     ;; with any struct with the same tag.
                     ((unless (and x-foundp y-foundp))
                      t))
                  (type-struni-member-list-compatible-3p-aux
                    x-members
                    y-members
                    completions
                    (treeset::insert pair assumed)
                    ienv))
                :untagged nil)
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged nil
                :untagged
                ;; Distinct types in the same translation unit.
                (if same-tunit?
                    nil
                  (type-struni-member-list-compatible-3p-aux
                    x.tag/members.members
                    y.tag/members.members
                    completions
                    assumed
                    ienv)))))
          :otherwise nil)
        :union
        (type-case
          y
          :union
          (b* (((when (uid-equal x.uid y.uid)) t)
               (same-tunit? (and x.tunit?
                                 y.tunit?
                                 (equal x.tunit? y.tunit?)))
               (c23p? (c::standard-case (ienv->std ienv) :c23)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* (((unless (equal x.tag/members.tag y.tag/members.tag))
                      nil)
                     ;; Distinct types in the same translation unit.
                     ((when (and same-tunit? (not c23p?)))
                      nil)
                     (completions (type-completions-fix completions))
                     ;; An incomplete union is compatible
                     ;; with any union with the same tag.
                     ((unless (and (treemap::in x.uid completions)
                                   (treemap::in y.uid completions)))
                      t))
                  ;; The members must correspond in some order,
                  ;; which we do not check yet.
                  :unknown)
                :untagged nil)
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged nil
                :untagged
                ;; Distinct types in the same translation unit;
                ;; otherwise the members must correspond in some order,
                ;; which we do not check yet.
                (if same-tunit?
                    nil
                  :unknown))))
          :otherwise nil)
        :array
        (type-case
          y
          :array (3and$ (type-array-kind-compatible-3p x.kind y.kind)
                        (type-compatible-3p-aux
                          x.of y.of completions assumed ienv))
          :otherwise nil)
        :pointer
        (type-case
          y
          :pointer (type-compatible-3p-aux x.to y.to completions assumed ienv)
          :otherwise nil)
        :function
        (type-case
          y
          :function (3and$ (type-compatible-3p-aux
                             x.ret y.ret completions assumed ienv)
                           (type-params-compatible-3p-aux
                             x.params y.params completions assumed ienv))
          :otherwise nil)
        :enum (3and (type-integer-3p y) :unknown)
        :otherwise
        (if (type-case y :enum)
            (3and (type-integer-3p x) :unknown)
          (type-equiv x y))))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (max (type-count x) (type-count y))))

  (define type-struni-member-list-compatible-3p-aux
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (completions type-completions-p)
     (assumed uid-pair-setp)
     (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether two lists of struct/union members are compatible
            [C17:6.2.7/1] [C23:6.2.7/1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This implements the ``correspondence'' check
       described in @(tsee type-compatible-3p)."))
    (b* (((when (endp x))
          (endp y))
         ((when (endp y))
          nil)
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y))
         ((unless (equal member-x.name? member-y.name?))
          nil))
      (3and$ (type-compatible-3p-aux
               member-x.type member-y.type completions assumed ienv)
             (type-struni-member-list-compatible-3p-aux
               (rest x) (rest y) completions assumed ienv)))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (max (type-struni-member-list-count x)
                   (type-struni-member-list-count y))))

  (define type-params-compatible-3p-aux ((x type-params-p)
                                     (y type-params-p)
                                     (completions type-completions-p)
                                     (assumed uid-pair-setp)
                                     (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether the parameter portions of two function @(see type)s
            are compatible [C17:6.7.6.3/15] [C23:6.7.7.4/15]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the second part of the compatibility check on function types.
       In addition to the earlier check
       that the return types must be compatible,
       the following conditions must also hold."
      (xdoc::ol
       (xdoc::li
        "When both function types correspond to function prototypes,
         both must have the same number of parameters
         and each parameter must have compatible type.
         Furthermore, both must agree on the ellipsis terminator.")
       (xdoc::li
        "When one type corresponds to a function prototype
         and the other is part of an ``old-style'' function definition,
         both must have the same number of parameters,
         and each type in the parameter type list of the prototype
         must be compatible with the corresponding type
         of the old-style function
         after the latter has gone through default argument promotion.
         Furthermore, the prototype must not feature an ellipsis terminator.")
       (xdoc::li
        "When one type corresponds to a function prototype
         and the other has an empty identifier list
         and is not derived from a function definition,
         the type of each parameter in the function prototype
         must be compatible with itself after default argument promotion.
         Furthermore, the prototype must not feature
         an ellipsis terminator."))
      "Note that no checks are required
       when neither function type includes a function prototype;
       it is sufficient that the two function types
       have compatible return types.")
     (xdoc::p
      "In the above mention of parameter types,
       we mean the type after adjustment [C17:6.7.6.3/7-8].
       This requires no special consideration here,
       since we always represent function types post-adjustment
       (see @(see type))."))
    (type-params-case
      x
      :prototype
      (type-params-case
        y
        :prototype (if (equal x.ellipsis y.ellipsis)
                       (type-list-compatible-3p-aux
                         x.params y.params completions assumed ienv)
                     nil)
        :old-style (if x.ellipsis
                       nil
                     (type-list-compatible-3p-aux
                       x.params
                       (type-list-default-arg-promote y.params ienv)
                       completions
                       assumed
                       ienv))
        :unspecified (if x.ellipsis
                         nil
                       (type-list-compatible-3p-aux
                         x.params
                         (type-list-default-arg-promote x.params ienv)
                         completions
                         assumed
                         ienv)))
      :old-style
      (type-params-case
        y
        :prototype (if y.ellipsis
                       nil
                     (type-list-compatible-3p-aux
                       (type-list-default-arg-promote x.params ienv)
                       y.params
                       completions
                       assumed
                       ienv))
        :otherwise t)
      :unspecified
      (type-params-case
        y
        :prototype (if y.ellipsis
                       nil
                     (type-list-compatible-3p-aux
                       (type-list-default-arg-promote y.params ienv)
                       y.params
                       completions
                       assumed
                       ienv))
        :otherwise t))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (max (type-params-count x)
                   (type-params-count y))))

  (define type-list-compatible-3p-aux ((x type-listp)
                                   (y type-listp)
                                   (completions type-completions-p)
                                   (assumed uid-pair-setp)
                                   (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether two @(see type-list)s are compatible [C17:6.2.7]."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each corresponding pair of elements from the two lists
       must be compatible.
       The lists must have the same length."))
    (b* (((when (endp x))
          (endp y))
         ((when (endp y))
          nil))
      (3and$ (type-compatible-3p-aux
               (first x) (first y) completions assumed ienv)
             (type-list-compatible-3p-aux
               (rest x) (rest y) completions assumed ienv)))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (max (type-list-count x)
                   (type-list-count y))))

  :hints (("Goal" :in-theory (e/d (max)
                                  (treeset::cardinality-of-delete-when-in
                                   treeset::cardinality-of-diff))))
  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-compatible-3p-aux))

(encapsulate ()
  (local
    (defthm-type/type-list-compatible-3p-aux-flag
      (defthm type-compatible-3p-aux-when-same-lemma
        (implies (equal x y)
                 (iff (type-compatible-3p-aux
                        x y completions assumed ienv)
                      t))
        :flag type-compatible-3p-aux)
      (defthm type-struni-member-list-compatible-3p-aux-when-same-lemma
        (implies (equal x y)
                 (iff (type-struni-member-list-compatible-3p-aux
                        x y completions assumed ienv)
                      t))
        :flag type-struni-member-list-compatible-3p-aux)
      (defthm type-params-compatible-3p-aux-when-same-lemma
        (implies (equal x y)
                 (iff (type-params-compatible-3p-aux
                        x y completions assumed ienv)
                      t))
        :flag type-params-compatible-3p-aux)
      (defthm type-list-compatible-3p-aux-when-same-lemma
        (implies (equal x y)
                 (iff (type-list-compatible-3p-aux
                        x y completions assumed ienv)
                      t))
        :flag type-list-compatible-3p-aux)
      :hints (("Goal"
               :in-theory
               (enable 3and
                       type-compatible-3p-aux
                       type-struni-member-list-compatible-3p-aux
                       type-params-compatible-3p-aux
                       type-list-compatible-3p-aux
                       type/type-list-compatible-3p-aux-flag)))))

  (defrule type-compatible-3p-aux-under-iff-when-same
    (iff (type-compatible-3p-aux x x completions assumed ienv)
         t))

  (defrule type-struni-member-list-compatible-3p-aux-under-iff-when-same
    (iff (type-struni-member-list-compatible-3p-aux
           x x completions assumed ienv)
         t))

  (defrule type-params-compatible-3p-aux-under-iff-when-same
    (iff (type-params-compatible-3p-aux x x completions assumed ienv)
         t))

  (defrule type-list-compatible-3p-aux-under-iff-when-same
    (iff (type-list-compatible-3p-aux x x completions assumed ienv)
         t)))

(defrule 3possibly-type-compatible-3p-aux-when-same
  (3possibly (type-compatible-3p-aux x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-struni-member-list-compatible-3p-aux-when-same
  (3possibly (type-struni-member-list-compatible-3p-aux
               x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-params-compatible-3p-aux-when-same
  (3possibly (type-params-compatible-3p-aux x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-list-compatible-3p-aux-when-same
  (3possibly (type-list-compatible-3p-aux x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defthm-type/type-list-compatible-3p-aux-flag
  (defthm type-compatible-3p-aux-symmetric
    (equal (type-compatible-3p-aux
             y x completions (uid-pair-set-swap assumed) ienv)
           (type-compatible-3p-aux x y completions assumed ienv))
    :flag type-compatible-3p-aux
    :hints ('(:expand (type-compatible-3p-aux
                        y x completions (uid-pair-set-swap assumed) ienv))))
  (defthm type-struni-member-list-compatible-3p-aux-symmetric
    (equal (type-struni-member-list-compatible-3p-aux
             y x completions (uid-pair-set-swap assumed) ienv)
           (type-struni-member-list-compatible-3p-aux
             x y completions assumed ienv))
    :flag type-struni-member-list-compatible-3p-aux
    :hints ('(:expand (type-struni-member-list-compatible-3p-aux
                        y x completions (uid-pair-set-swap assumed) ienv))))
  (defthm type-params-compatible-3p-aux-symmetric
    (equal (type-params-compatible-3p-aux
             y x completions (uid-pair-set-swap assumed) ienv)
           (type-params-compatible-3p-aux x y completions assumed ienv))
    :flag type-params-compatible-3p-aux
    :hints ('(:expand (type-params-compatible-3p-aux
                        y x completions (uid-pair-set-swap assumed) ienv))))
  (defthm type-list-compatible-3p-aux-symmetric
    (equal (type-list-compatible-3p-aux
             y x completions (uid-pair-set-swap assumed) ienv)
           (type-list-compatible-3p-aux x y completions assumed ienv))
    :flag type-list-compatible-3p-aux
    :hints ('(:expand (type-list-compatible-3p-aux
                        y x completions (uid-pair-set-swap assumed) ienv))))
  :hints (("Goal"
           :in-theory (enable type-compatible-3p-aux
                              type-struni-member-list-compatible-3p-aux
                              type-params-compatible-3p-aux
                              type-list-compatible-3p-aux
                              type/type-list-compatible-3p-aux-flag))))

;; Anti-monotonicity in the completions map.

(defthm-type/type-list-compatible-3p-aux-flag
  (defthm type-compatible-3p-aux-when-submap
    (implies (treemap::submap (type-completions-fix completions1)
                              (type-completions-fix completions))
             (3truth<= (type-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-compatible-3p-aux
                         x y completions1 assumed ienv)))
    :flag type-compatible-3p-aux
    :hints ('(:expand ((type-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-compatible-3p-aux
                         x y completions1 assumed ienv)))))
  (defthm type-struni-member-list-compatible-3p-aux-when-submap
    (implies (treemap::submap (type-completions-fix completions1)
                              (type-completions-fix completions))
             (3truth<= (type-struni-member-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-struni-member-list-compatible-3p-aux
                         x y completions1 assumed ienv)))
    :flag type-struni-member-list-compatible-3p-aux
    :hints ('(:expand ((type-struni-member-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-struni-member-list-compatible-3p-aux
                         x y completions1 assumed ienv)))))
  (defthm type-params-compatible-3p-aux-when-submap
    (implies (treemap::submap (type-completions-fix completions1)
                              (type-completions-fix completions))
             (3truth<= (type-params-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-params-compatible-3p-aux
                         x y completions1 assumed ienv)))
    :flag type-params-compatible-3p-aux
    :hints ('(:expand ((type-params-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-params-compatible-3p-aux
                         x y completions1 assumed ienv)))))
  (defthm type-list-compatible-3p-aux-when-submap
    (implies (treemap::submap (type-completions-fix completions1)
                              (type-completions-fix completions))
             (3truth<= (type-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-list-compatible-3p-aux
                         x y completions1 assumed ienv)))
    :flag type-list-compatible-3p-aux
    :hints ('(:expand ((type-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-list-compatible-3p-aux
                         x y completions1 assumed ienv)))))
  :hints (("Goal"
           :in-theory
           (enable treemap::lookup-when-submap-and-in-of-keys
                   type-compatible-3p-aux
                   type-struni-member-list-compatible-3p-aux
                   type-params-compatible-3p-aux
                   type-list-compatible-3p-aux
                   type/type-list-compatible-3p-aux-flag))))

;; Monotonicity in the assumed pairs.

(defthm-type/type-list-compatible-3p-aux-flag
  (defthm type-compatible-3p-aux-of-union
    (3truth<= (type-compatible-3p-aux
                x y completions assumed ienv)
              (type-compatible-3p-aux
                x y completions
                (treeset::union (uid-pair-sfix assumed)
                                (uid-pair-sfix extra))
                ienv))
    :flag type-compatible-3p-aux
    :hints ('(:expand ((type-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix extra))
                         ienv)))))
  (defthm type-struni-member-list-compatible-3p-aux-of-union
    (3truth<= (type-struni-member-list-compatible-3p-aux
                x y completions assumed ienv)
              (type-struni-member-list-compatible-3p-aux
                x y completions
                (treeset::union (uid-pair-sfix assumed)
                                (uid-pair-sfix extra))
                ienv))
    :flag type-struni-member-list-compatible-3p-aux
    :hints ('(:expand ((type-struni-member-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-struni-member-list-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix extra))
                         ienv)))))
  (defthm type-params-compatible-3p-aux-of-union
    (3truth<= (type-params-compatible-3p-aux
                x y completions assumed ienv)
              (type-params-compatible-3p-aux
                x y completions
                (treeset::union (uid-pair-sfix assumed)
                                (uid-pair-sfix extra))
                ienv))
    :flag type-params-compatible-3p-aux
    :hints ('(:expand ((type-params-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-params-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix extra))
                         ienv)))))
  (defthm type-list-compatible-3p-aux-of-union
    (3truth<= (type-list-compatible-3p-aux
                x y completions assumed ienv)
              (type-list-compatible-3p-aux
                x y completions
                (treeset::union (uid-pair-sfix assumed)
                                (uid-pair-sfix extra))
                ienv))
    :flag type-list-compatible-3p-aux
    :hints ('(:expand ((type-list-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-list-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix extra))
                         ienv)))))
  :hints (("Goal"
           :in-theory
           (enable type-compatible-3p-aux
                   type-struni-member-list-compatible-3p-aux
                   type-params-compatible-3p-aux
                   type-list-compatible-3p-aux
                   type/type-list-compatible-3p-aux-flag))))

(defrule type-compatible-3p-aux-when-subset
  (implies (treeset::subset (uid-pair-sfix assumed)
                            (uid-pair-sfix assumed2))
           (3truth<= (type-compatible-3p-aux
                       x y completions assumed ienv)
                     (type-compatible-3p-aux
                       x y completions assumed2 ienv)))
  :use (:instance type-compatible-3p-aux-of-union
                  (extra assumed2))
  :disable type-compatible-3p-aux-of-union)

(defrule type-struni-member-list-compatible-3p-aux-when-subset
  (implies (treeset::subset (uid-pair-sfix assumed)
                            (uid-pair-sfix assumed2))
           (3truth<= (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv)
                     (type-struni-member-list-compatible-3p-aux
                       x y completions assumed2 ienv)))
  :use (:instance type-struni-member-list-compatible-3p-aux-of-union
                  (extra assumed2))
  :disable type-struni-member-list-compatible-3p-aux-of-union)

(defrule type-params-compatible-3p-aux-when-subset
  (implies (treeset::subset (uid-pair-sfix assumed)
                            (uid-pair-sfix assumed2))
           (3truth<= (type-params-compatible-3p-aux
                       x y completions assumed ienv)
                     (type-params-compatible-3p-aux
                       x y completions assumed2 ienv)))
  :use (:instance type-params-compatible-3p-aux-of-union
                  (extra assumed2))
  :disable type-params-compatible-3p-aux-of-union)

(defrule type-list-compatible-3p-aux-when-subset
  (implies (treeset::subset (uid-pair-sfix assumed)
                            (uid-pair-sfix assumed2))
           (3truth<= (type-list-compatible-3p-aux
                       x y completions assumed ienv)
                     (type-list-compatible-3p-aux
                       x y completions assumed2 ienv)))
  :use (:instance type-list-compatible-3p-aux-of-union
                  (extra assumed2))
  :disable type-list-compatible-3p-aux-of-union)

;; The boolean projections of the two monotonicity properties,
;; binding the free map or set either from the projected fact
;; (the -fix versions, with fixed hypotheses)
;; or from the submap or subset hypothesis.

(defrule 3possibly-type-compatible-3p-aux-when-submap-fix
  (implies (and (3possibly (type-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3possibly (type-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-compatible-3p-aux-when-submap
  :disable type-compatible-3p-aux-when-submap)

(defrule 3possibly-type-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3possibly (type-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3possibly-type-compatible-3p-aux-when-submap-fix
  :disable 3possibly-type-compatible-3p-aux-when-submap-fix)

(defrule 3possibly-type-struni-member-list-compatible-3p-aux-when-submap-fix
  (implies (and (3possibly (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3possibly (type-struni-member-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-struni-member-list-compatible-3p-aux-when-submap
  :disable type-struni-member-list-compatible-3p-aux-when-submap)

(defrule 3possibly-type-struni-member-list-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3possibly (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-struni-member-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3possibly-type-struni-member-list-compatible-3p-aux-when-submap-fix
  :disable 3possibly-type-struni-member-list-compatible-3p-aux-when-submap-fix)

(defrule 3possibly-type-params-compatible-3p-aux-when-submap-fix
  (implies (and (3possibly (type-params-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3possibly (type-params-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-params-compatible-3p-aux-when-submap
  :disable type-params-compatible-3p-aux-when-submap)

(defrule 3possibly-type-params-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3possibly (type-params-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-params-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3possibly-type-params-compatible-3p-aux-when-submap-fix
  :disable 3possibly-type-params-compatible-3p-aux-when-submap-fix)

(defrule 3possibly-type-list-compatible-3p-aux-when-submap-fix
  (implies (and (3possibly (type-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3possibly (type-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-list-compatible-3p-aux-when-submap
  :disable type-list-compatible-3p-aux-when-submap)

(defrule 3possibly-type-list-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3possibly (type-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3possibly-type-list-compatible-3p-aux-when-submap-fix
  :disable 3possibly-type-list-compatible-3p-aux-when-submap-fix)

(defrule 3definitely-type-compatible-3p-aux-when-submap-fix
  (implies (and (3definitely (type-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3definitely (type-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-compatible-3p-aux-when-submap
  :disable type-compatible-3p-aux-when-submap)

(defrule 3definitely-type-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3definitely (type-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3definitely-type-compatible-3p-aux-when-submap-fix
  :disable 3definitely-type-compatible-3p-aux-when-submap-fix)

(defrule 3definitely-type-struni-member-list-compatible-3p-aux-when-submap-fix
  (implies (and (3definitely (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3definitely (type-struni-member-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-struni-member-list-compatible-3p-aux-when-submap
  :disable type-struni-member-list-compatible-3p-aux-when-submap)

(defrule 3definitely-type-struni-member-list-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3definitely (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-struni-member-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3definitely-type-struni-member-list-compatible-3p-aux-when-submap-fix
  :disable
  3definitely-type-struni-member-list-compatible-3p-aux-when-submap-fix)

(defrule 3definitely-type-params-compatible-3p-aux-when-submap-fix
  (implies (and (3definitely (type-params-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3definitely (type-params-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-params-compatible-3p-aux-when-submap
  :disable type-params-compatible-3p-aux-when-submap)

(defrule 3definitely-type-params-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3definitely (type-params-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-params-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3definitely-type-params-compatible-3p-aux-when-submap-fix
  :disable 3definitely-type-params-compatible-3p-aux-when-submap-fix)

(defrule 3definitely-type-list-compatible-3p-aux-when-submap-fix
  (implies (and (3definitely (type-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treemap::submap (type-completions-fix completions1)
                                 (type-completions-fix completions)))
           (3definitely (type-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use type-list-compatible-3p-aux-when-submap
  :disable type-list-compatible-3p-aux-when-submap)

(defrule 3definitely-type-list-compatible-3p-aux-when-submap
  (implies (and (treemap::submap completions1 completions)
                (type-completions-p completions)
                (3definitely (type-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-list-compatible-3p-aux
                   x y completions1 assumed ienv)))
  :use 3definitely-type-list-compatible-3p-aux-when-submap-fix
  :disable 3definitely-type-list-compatible-3p-aux-when-submap-fix)

(defrule 3possibly-type-compatible-3p-aux-when-subset-fix
  (implies (and (3possibly (type-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3possibly (type-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-compatible-3p-aux-when-subset
  :disable type-compatible-3p-aux-when-subset)

(defrule 3possibly-type-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3possibly (type-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3possibly-type-compatible-3p-aux-when-subset-fix
  :disable 3possibly-type-compatible-3p-aux-when-subset-fix)

(defrule 3possibly-type-struni-member-list-compatible-3p-aux-when-subset-fix
  (implies (and (3possibly (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3possibly (type-struni-member-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-struni-member-list-compatible-3p-aux-when-subset
  :disable type-struni-member-list-compatible-3p-aux-when-subset)

(defrule 3possibly-type-struni-member-list-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3possibly (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-struni-member-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3possibly-type-struni-member-list-compatible-3p-aux-when-subset-fix
  :disable 3possibly-type-struni-member-list-compatible-3p-aux-when-subset-fix)

(defrule 3possibly-type-params-compatible-3p-aux-when-subset-fix
  (implies (and (3possibly (type-params-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3possibly (type-params-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-params-compatible-3p-aux-when-subset
  :disable type-params-compatible-3p-aux-when-subset)

(defrule 3possibly-type-params-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3possibly (type-params-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-params-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3possibly-type-params-compatible-3p-aux-when-subset-fix
  :disable 3possibly-type-params-compatible-3p-aux-when-subset-fix)

(defrule 3possibly-type-list-compatible-3p-aux-when-subset-fix
  (implies (and (3possibly (type-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3possibly (type-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-list-compatible-3p-aux-when-subset
  :disable type-list-compatible-3p-aux-when-subset)

(defrule 3possibly-type-list-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3possibly (type-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3possibly (type-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3possibly-type-list-compatible-3p-aux-when-subset-fix
  :disable 3possibly-type-list-compatible-3p-aux-when-subset-fix)

(defrule 3definitely-type-compatible-3p-aux-when-subset-fix
  (implies (and (3definitely (type-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3definitely (type-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-compatible-3p-aux-when-subset
  :disable type-compatible-3p-aux-when-subset)

(defrule 3definitely-type-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3definitely (type-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3definitely-type-compatible-3p-aux-when-subset-fix
  :disable 3definitely-type-compatible-3p-aux-when-subset-fix)

(defrule 3definitely-type-struni-member-list-compatible-3p-aux-when-subset-fix
  (implies (and (3definitely (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3definitely (type-struni-member-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-struni-member-list-compatible-3p-aux-when-subset
  :disable type-struni-member-list-compatible-3p-aux-when-subset)

(defrule 3definitely-type-struni-member-list-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3definitely (type-struni-member-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-struni-member-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3definitely-type-struni-member-list-compatible-3p-aux-when-subset-fix
  :disable
  3definitely-type-struni-member-list-compatible-3p-aux-when-subset-fix)

(defrule 3definitely-type-params-compatible-3p-aux-when-subset-fix
  (implies (and (3definitely (type-params-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3definitely (type-params-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-params-compatible-3p-aux-when-subset
  :disable type-params-compatible-3p-aux-when-subset)

(defrule 3definitely-type-params-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3definitely (type-params-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-params-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3definitely-type-params-compatible-3p-aux-when-subset-fix
  :disable 3definitely-type-params-compatible-3p-aux-when-subset-fix)

(defrule 3definitely-type-list-compatible-3p-aux-when-subset-fix
  (implies (and (3definitely (type-list-compatible-3p-aux
                       x y completions assumed ienv))
                (treeset::subset (uid-pair-sfix assumed)
                                 (uid-pair-sfix assumed2)))
           (3definitely (type-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use type-list-compatible-3p-aux-when-subset
  :disable type-list-compatible-3p-aux-when-subset)

(defrule 3definitely-type-list-compatible-3p-aux-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-pair-setp assumed2)
                (3definitely (type-list-compatible-3p-aux
                       x y completions assumed ienv)))
           (3definitely (type-list-compatible-3p-aux
                   x y completions assumed2 ienv)))
  :use 3definitely-type-list-compatible-3p-aux-when-subset-fix
  :disable 3definitely-type-list-compatible-3p-aux-when-subset-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following definitions and theorems prepare for the proof equating
;; the -exec version of compatibility to the logical version given above.

(define uid-pair-compatible-3p-aux ((pair uid-pairp)
                                    (completions type-completions-p)
                                    (assumed uid-pair-setp)
                                    (ienv ienvp))
  :returns (3vl 3p)
  :short "Compare the members of the structure types of a pair of @(see UID)s,
          as @(tsee type-compatible-3p-aux) does
          when the pair is not assumed compatible."
  (b* (((uid-pair pair) pair)
       (completions (type-completions-fix completions))
       (assumed (uid-pair-sfix assumed))
       ((mv x-foundp x-members)
        (treemap::lookup? pair.first completions))
       ((mv y-foundp y-members)
        (treemap::lookup? pair.second completions))
       ((unless (and x-foundp y-foundp))
        t))
    (type-struni-member-list-compatible-3p-aux
      x-members
      y-members
      completions
      (treeset::insert (uid-pair-fix pair) assumed)
      ienv)))

;; The comparison of the members of a pair of complete structure types
;; is folded into this function,
;; so that the theorems below apply to the check as it makes it.

(defruled type-struni-member-list-compatible-3p-aux-becomes-uid-pair
  (implies
    (and (treeset::in first
                      (treemap::keys (type-completions-fix completions)))
         (treeset::in second
                      (treemap::keys (type-completions-fix completions))))
    (equal (type-struni-member-list-compatible-3p-aux
             (treemap::lookup first (type-completions-fix completions))
             (treemap::lookup second (type-completions-fix completions))
             completions
             (treeset::insert (uid-pair first second) (uid-pair-sfix assumed))
             ienv)
           (uid-pair-compatible-3p-aux (uid-pair first second)
                                       completions assumed ienv)))
  :enable uid-pair-compatible-3p-aux)

;; The comparison is monotone in the assumed pairs,
;; as the check it makes is.

(defrule uid-pair-compatible-3p-aux-when-subset
  (implies (treeset::subset (uid-pair-sfix assumed)
                            (uid-pair-sfix assumed2))
           (3truth<= (uid-pair-compatible-3p-aux
                       pair completions assumed ienv)
                     (uid-pair-compatible-3p-aux
                       pair completions assumed2 ienv)))
  :enable uid-pair-compatible-3p-aux)

;;;;;;;;;;;;;;;;;;;;

(define uid-pair-set-compatible-3p-aux ((pairs uid-pair-setp)
                                        (completions type-completions-p)
                                        (assumed uid-pair-setp)
                                        (ienv ienvp))
  :returns (3vl 3p)
  :short "Conjoin the comparisons of @(tsee uid-pair-compatible-3p-aux)
          over a set of pairs of @(see UID)s."
  (b* ((pairs (uid-pair-sfix pairs))
       ((when (treeset::emptyp pairs))
        t)
       (pair (treeset::min pairs)))
    (3and (uid-pair-compatible-3p-aux pair completions assumed ienv)
          (uid-pair-set-compatible-3p-aux
            (treeset::delete pair pairs) completions assumed ienv)))
  :measure (treeset::cardinality (uid-pair-sfix pairs))
  :verify-guards :after-returns)

(defrule uid-pair-set-compatible-3p-aux-of-empty
  (equal (uid-pair-set-compatible-3p-aux
           (treeset::empty) completions assumed ienv)
         t)
  :enable uid-pair-set-compatible-3p-aux)

;;;;;;;;;;;;;;;;;;;;

;; The conjunction does not depend on the order of the elements.

(defruled uid-pair-set-compatible-3p-aux-when-in
  (implies (treeset::in pair (uid-pair-sfix pairs))
           (equal (uid-pair-set-compatible-3p-aux
                   pairs completions assumed ienv)
                  (3and (uid-pair-compatible-3p-aux
                         pair completions assumed ienv)
                        (uid-pair-set-compatible-3p-aux
                         (treeset::delete pair (uid-pair-sfix pairs))
                         completions assumed ienv))))
  :induct (uid-pair-set-induction pairs pair)
  :enable (uid-pair-set-induction
           uid-pair-set-compatible-3p-aux)
  :prep-lemmas
  ((define uid-pair-set-induction (pairs pair)
     (b* ((pairs (uid-pair-sfix pairs))
          ((when (or (treeset::emptyp pairs)
                     (not (treeset::in pair pairs))))
           t))
       (and (uid-pair-set-induction (treeset::delete (treeset::min pairs) pairs)
                                    pair)
            (uid-pair-set-induction (treeset::delete pair pairs)
                                    (treeset::min pairs))))
     :measure (treeset::cardinality (uid-pair-sfix pairs))
     :verify-guards nil)))

(defrule uid-pair-set-compatible-3p-aux-of-insert
  (implies (and (uid-pair-setp pairs)
                (uid-pairp pair))
           (equal (uid-pair-set-compatible-3p-aux
                    (treeset::insert pair pairs) completions assumed ienv)
                  (3and (uid-pair-compatible-3p-aux
                          pair completions assumed ienv)
                        (uid-pair-set-compatible-3p-aux
                          pairs completions assumed ienv))))
  :use ((:instance uid-pair-set-compatible-3p-aux-when-in
                   (pairs (treeset::insert pair pairs)))
        uid-pair-set-compatible-3p-aux-when-in))

;; Splitting the conjunction over a set into a subset and the difference.

(defruled uid-pair-set-compatible-3p-aux-when-subset
  (implies (and (uid-pair-setp d)
                (uid-pair-setp e)
                (treeset::subset d e))
           (equal (uid-pair-set-compatible-3p-aux e completions assumed ienv)
                  (3and (uid-pair-set-compatible-3p-aux
                          d completions assumed ienv)
                        (uid-pair-set-compatible-3p-aux
                          (treeset::diff e d) completions assumed ienv))))
  :induct (treeset::min-delete-induction d)
  :enable (uid-pair-set-compatible-3p-aux
           treeset::diff-of-arg1-and-delete-when-in-of-arg1
           treeset::min-delete-induction))

;; The conjunction over a set is below each of its members.

(defrule 3truth<=-of-uid-pair-set-compatible-3p-aux-when-in
  (implies (treeset::in pair (uid-pair-sfix pairs))
           (3truth<= (uid-pair-set-compatible-3p-aux
                       pairs completions assumed ienv)
                     (uid-pair-compatible-3p-aux
                       pair completions assumed ienv)))
  :enable uid-pair-set-compatible-3p-aux-when-in)

;;;;;;;;;;;;;;;;;;;;

;; Assuming more pairs compatible can only raise the check,
;; which stops at those pairs instead of comparing their members,
;; but only where their comparisons would have brought it down:
;; given a value below the conjunction of those comparisons,
;; either that value is below the check under the smaller set,
;; or the check under the larger set is.
;; This is first shown for a single pair as the check reaches it,
;; using the monotonicity of the check in the assumed set;
;; then for the whole check, by induction;
;; then for the comparison of a pair and for the conjunction over a set.

(defrule 3truth<=-of-uid-pair-set-compatible-3p-aux-when-in-and-subset
  (implies (and (treeset::in pair (uid-pair-sfix pairs))
                (treeset::subset (uid-pair-sfix base)
                                 (uid-pair-sfix assumed)))
           (3truth<= (uid-pair-set-compatible-3p-aux
                       pairs completions base ienv)
                     (uid-pair-compatible-3p-aux
                       pair completions assumed ienv)))
  :use (:instance 3truth<=-of-uid-pair-set-compatible-3p-aux-when-in
                  (assumed base))
  :disable 3truth<=-of-uid-pair-set-compatible-3p-aux-when-in)

(defthm-type/type-list-compatible-3p-aux-flag
  (defthmd 3truth<=-of-type-compatible-3p-aux-of-union
    (implies (and (treeset::subset (uid-pair-sfix base)
                                   (uid-pair-sfix assumed))
                  (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                  pairs completions base ienv))
                  (not (3truth<= 3vl (type-compatible-3p-aux
                                       x y completions assumed ienv))))
             (3truth<= (type-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix pairs))
                         ienv)
                       (type-compatible-3p-aux
                         x y completions assumed ienv)))
    :flag type-compatible-3p-aux
    :hints ('(:expand ((type-compatible-3p-aux
                         x y completions assumed ienv)
                       (type-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix pairs))
                         ienv)))))
  (defthmd 3truth<=-of-type-struni-member-list-compatible-3p-aux-of-union
    (implies (and (treeset::subset (uid-pair-sfix base)
                                   (uid-pair-sfix assumed))
                  (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                  pairs completions base ienv))
                  (not (3truth<= 3vl (type-struni-member-list-compatible-3p-aux
                                       x y completions assumed ienv))))
             (3truth<= (type-struni-member-list-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix pairs))
                         ienv)
                       (type-struni-member-list-compatible-3p-aux
                         x y completions assumed ienv)))
    :flag type-struni-member-list-compatible-3p-aux)
  (defthmd 3truth<=-of-type-params-compatible-3p-aux-of-union
    (implies (and (treeset::subset (uid-pair-sfix base)
                                   (uid-pair-sfix assumed))
                  (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                  pairs completions base ienv))
                  (not (3truth<= 3vl (type-params-compatible-3p-aux
                                       x y completions assumed ienv))))
             (3truth<= (type-params-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix pairs))
                         ienv)
                       (type-params-compatible-3p-aux
                         x y completions assumed ienv)))
    :flag type-params-compatible-3p-aux)
  (defthmd 3truth<=-of-type-list-compatible-3p-aux-of-union
    (implies (and (treeset::subset (uid-pair-sfix base)
                                   (uid-pair-sfix assumed))
                  (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                  pairs completions base ienv))
                  (not (3truth<= 3vl (type-list-compatible-3p-aux
                                       x y completions assumed ienv))))
             (3truth<= (type-list-compatible-3p-aux
                         x y completions
                         (treeset::union (uid-pair-sfix assumed)
                                         (uid-pair-sfix pairs))
                         ienv)
                       (type-list-compatible-3p-aux
                         x y completions assumed ienv)))
    :flag type-list-compatible-3p-aux)
  :hints
  (("Goal"
    :in-theory
    (enable type-struni-member-list-compatible-3p-aux
            type-params-compatible-3p-aux
            type-list-compatible-3p-aux
            type-struni-member-list-compatible-3p-aux-becomes-uid-pair
            type/type-list-compatible-3p-aux-flag))))

(defruled 3truth<=-of-uid-pair-compatible-3p-aux-of-union
  (implies (and (treeset::subset (uid-pair-sfix base) (uid-pair-sfix assumed))
                (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                pairs completions base ienv))
                (not (3truth<= 3vl (uid-pair-compatible-3p-aux
                                     pair completions assumed ienv)))
                (3truth<= (uid-pair-compatible-3p-aux
                            pair completions assumed ienv)
                          z))
           (3truth<= (uid-pair-compatible-3p-aux
                       pair completions
                       (treeset::union (uid-pair-sfix assumed)
                                       (uid-pair-sfix pairs))
                       ienv)
                     z))
  :enable (uid-pair-compatible-3p-aux
           acl2::transitivity-of-3truth<=-swapped)
  :use (:instance
         3truth<=-of-type-struni-member-list-compatible-3p-aux-of-union
         (x (treemap::lookup (uid-pair->first pair)
                             (type-completions-fix completions)))
         (y (treemap::lookup (uid-pair->second pair)
                             (type-completions-fix completions)))
         (assumed (treeset::insert (uid-pair-fix pair)
                                   (uid-pair-sfix assumed)))))

(defruled 3truth<=-of-uid-pair-set-compatible-3p-aux-of-union
  (implies (and (uid-pair-setp pairs2)
                (treeset::subset (uid-pair-sfix base) (uid-pair-sfix assumed))
                (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                pairs completions base ienv))
                (not (3truth<= 3vl (uid-pair-set-compatible-3p-aux
                                     pairs2 completions assumed ienv))))
           (3truth<= (uid-pair-set-compatible-3p-aux
                       pairs2 completions
                       (treeset::union (uid-pair-sfix assumed)
                                       (uid-pair-sfix pairs))
                       ienv)
                     (uid-pair-set-compatible-3p-aux
                       pairs2 completions assumed ienv)))
  :hints
  (("Goal"
    :induct (treeset::min-delete-induction pairs2)
    :in-theory
    (enable treeset::min-delete-induction
            uid-pair-set-compatible-3p-aux
            3truth<=-of-uid-pair-compatible-3p-aux-of-union))
   ("Subgoal *1/2"
    :cases ((3truth<= 3vl (uid-pair-compatible-3p-aux
                            (treeset::min pairs2) completions assumed ienv))))))

;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-compatible-3p-exec
  (define type-compatible-3p-exec ((x typep)
                                   (y typep)
                                   (completions type-completions-p)
                                   (visited uid-pair-setp)
                                   (ienv ienvp))
    :returns (mv (3vl 3p)
                 (visited$
                  (and (uid-pair-setp visited$)
                       (implies (uid-pair-setp visited)
                                (treeset::subset visited visited$)))))
    :short "Executable counterpart of @(tsee type-compatible-3p-aux)."
    :long
    (xdoc::topstring
     (xdoc::p
      "This makes the same comparisons as @(tsee type-compatible-3p-aux),
       but the set of pairs of @(see UID)s of the tagged structure types
       whose members have been compared is threaded through the check
       and returned, instead of being passed down only:
       a pair reached again along another path is accepted as compatible,
       and its members are not compared again.
       The result is the same,
       because the result is the conjunction of the comparisons
       of all the pairs reachable from the two types,
       and a pair compared once contributes to the conjunction once.
       The difference is the cost:
       the check is linear in the number of reachable pairs,
       instead of the number of paths to them."))
    (b* ((visited (uid-pair-sfix visited))
         ((when (or (type-case x '(:unknown :unknown-builtin))
                    (type-case y '(:unknown :unknown-builtin))))
          (mv :unknown visited))
         ((when (type-case x :unknown-scalar))
          (mv (3and (type-scalar-3p y) :unknown) visited))
         ((when (type-case y :unknown-scalar))
          (mv (3and (type-scalar-3p x) :unknown) visited))
         ((when (type-case x :unknown-arithmetic))
          (mv (3and (type-arithmetic-3p y) :unknown) visited))
         ((when (type-case y :unknown-arithmetic))
          (mv (3and (type-arithmetic-3p x) :unknown) visited)))
      (type-case
        x
        :struct
        (type-case
          y
          :struct
          (b* (((when (uid-equal x.uid y.uid)) (mv t visited))
               (same-tunit? (and x.tunit?
                                 y.tunit?
                                 (equal x.tunit? y.tunit?)))
               (c23p? (c::standard-case (ienv->std ienv) :c23)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* (((unless (equal x.tag/members.tag y.tag/members.tag))
                      (mv nil visited))
                     ((when (and same-tunit? (not c23p?)))
                      (mv nil visited))
                     (pair (make-uid-pair :first x.uid :second y.uid))
                     ((when (treeset::in pair visited))
                      (mv t visited))
                     (completions (type-completions-fix completions))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ((unless (and x-foundp y-foundp))
                      (mv t visited)))
                  (type-struni-member-list-compatible-3p-exec
                    x-members
                    y-members
                    completions
                    (treeset::insert pair visited)
                    ienv))
                :untagged (mv nil visited))
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged (mv nil visited)
                :untagged
                (if same-tunit?
                    (mv nil visited)
                  (type-struni-member-list-compatible-3p-exec
                    x.tag/members.members
                    y.tag/members.members
                    completions
                    visited
                    ienv)))))
          :otherwise (mv nil visited))
        :union
        (type-case
          y
          :union
          (b* (((when (uid-equal x.uid y.uid)) (mv t visited))
               (same-tunit? (and x.tunit?
                                 y.tunit?
                                 (equal x.tunit? y.tunit?)))
               (c23p? (c::standard-case (ienv->std ienv) :c23)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* (((unless (equal x.tag/members.tag y.tag/members.tag))
                      (mv nil visited))
                     ((when (and same-tunit? (not c23p?)))
                      (mv nil visited))
                     (completions (type-completions-fix completions))
                     ((unless (and (treemap::in x.uid completions)
                                   (treemap::in y.uid completions)))
                      (mv t visited)))
                  (mv :unknown visited))
                :untagged (mv nil visited))
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged (mv nil visited)
                :untagged
                (if same-tunit?
                    (mv nil visited)
                  (mv :unknown visited)))))
          :otherwise (mv nil visited))
        :array
        (type-case
          y
          :array
          (b* ((kinds (type-array-kind-compatible-3p x.kind y.kind))
               ((unless kinds) (mv nil visited))
               ((mv ofs visited)
                (type-compatible-3p-exec x.of y.of completions visited ienv)))
            (mv (3and kinds ofs) visited))
          :otherwise (mv nil visited))
        :pointer
        (type-case
          y
          :pointer (type-compatible-3p-exec x.to y.to completions visited ienv)
          :otherwise (mv nil visited))
        :function
        (type-case
          y
          :function
          (b* (((mv rets visited1)
                (type-compatible-3p-exec x.ret y.ret completions visited ienv))
               ((unless rets) (mv nil visited))
               (visited (if (mbt (and (uid-pair-setp visited1)
                                      (treeset::subset visited visited1)))
                            visited1
                          visited))
               ((mv params visited)
                (type-params-compatible-3p-exec
                  x.params y.params completions visited ienv)))
            (mv (3and rets params) visited))
          :otherwise (mv nil visited))
        :enum (mv (3and (type-integer-3p y) :unknown) visited)
        :otherwise
        (if (type-case y :enum)
            (mv (3and (type-integer-3p x) :unknown) visited)
          (mv (type-equiv x y) visited))))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix visited)))
              (max (type-count x) (type-count y))))

  (define type-struni-member-list-compatible-3p-exec
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (completions type-completions-p)
     (visited uid-pair-setp)
     (ienv ienvp))
    :returns (mv (3vl 3p)
                 (visited$
                  (and (uid-pair-setp visited$)
                       (implies (uid-pair-setp visited)
                                (treeset::subset visited visited$)))))
    :short "Executable counterpart of
            @(tsee type-struni-member-list-compatible-3p-aux)."
    (b* ((visited (uid-pair-sfix visited))
         ((when (endp x))
          (mv (endp y) visited))
         ((when (endp y))
          (mv nil visited))
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y))
         ((unless (equal member-x.name? member-y.name?))
          (mv nil visited))
         ((mv first visited1)
          (type-compatible-3p-exec
            member-x.type member-y.type completions visited ienv))
         ((unless first) (mv nil visited))
         (visited (if (mbt (and (uid-pair-setp visited1)
                                (treeset::subset visited visited1)))
                      visited1
                    visited))
         ((mv rest visited)
          (type-struni-member-list-compatible-3p-exec
            (rest x) (rest y) completions visited ienv)))
      (mv (3and first rest) visited))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix visited)))
              (max (type-struni-member-list-count x)
                   (type-struni-member-list-count y))))

  (define type-params-compatible-3p-exec ((x type-params-p)
                                          (y type-params-p)
                                          (completions type-completions-p)
                                          (visited uid-pair-setp)
                                          (ienv ienvp))
    :returns (mv (3vl 3p)
                 (visited$
                  (and (uid-pair-setp visited$)
                       (implies (uid-pair-setp visited)
                                (treeset::subset visited visited$)))))
    :short "Executable counterpart of @(tsee type-params-compatible-3p-aux)."
    (b* ((visited (uid-pair-sfix visited)))
      (type-params-case
        x
        :prototype
        (type-params-case
          y
          :prototype (if (equal x.ellipsis y.ellipsis)
                         (type-list-compatible-3p-exec
                           x.params y.params completions visited ienv)
                       (mv nil visited))
          :old-style (if x.ellipsis
                         (mv nil visited)
                       (type-list-compatible-3p-exec
                         x.params
                         (type-list-default-arg-promote y.params ienv)
                         completions
                         visited
                         ienv))
          :unspecified (if x.ellipsis
                           (mv nil visited)
                         (type-list-compatible-3p-exec
                           x.params
                           (type-list-default-arg-promote x.params ienv)
                           completions
                           visited
                           ienv)))
        :old-style
        (type-params-case
          y
          :prototype (if y.ellipsis
                         (mv nil visited)
                       (type-list-compatible-3p-exec
                         (type-list-default-arg-promote x.params ienv)
                         y.params
                         completions
                         visited
                         ienv))
          :otherwise (mv t visited))
        :unspecified
        (type-params-case
          y
          :prototype (if y.ellipsis
                         (mv nil visited)
                       (type-list-compatible-3p-exec
                         (type-list-default-arg-promote y.params ienv)
                         y.params
                         completions
                         visited
                         ienv))
          :otherwise (mv t visited))))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix visited)))
              (max (type-params-count x)
                   (type-params-count y))))

  (define type-list-compatible-3p-exec ((x type-listp)
                                        (y type-listp)
                                        (completions type-completions-p)
                                        (visited uid-pair-setp)
                                        (ienv ienvp))
    :returns (mv (3vl 3p)
                 (visited$
                  (and (uid-pair-setp visited$)
                       (implies (uid-pair-setp visited)
                                (treeset::subset visited visited$)))))
    :short "Executable counterpart of @(tsee type-list-compatible-3p-aux)."
    (b* ((visited (uid-pair-sfix visited))
         ((when (endp x))
          (mv (endp y) visited))
         ((when (endp y))
          (mv nil visited))
         ((mv first visited1)
          (type-compatible-3p-exec
            (first x) (first y) completions visited ienv))
         ((unless first) (mv nil visited))
         (visited (if (mbt (and (uid-pair-setp visited1)
                                (treeset::subset visited visited1)))
                      visited1
                    visited))
         ((mv rest visited)
          (type-list-compatible-3p-exec
            (rest x) (rest y) completions visited ienv)))
      (mv (3and first rest) visited))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix visited)))
              (max (type-list-count x)
                   (type-list-count y))))

  :hints (("Goal" :in-theory (e/d (max)
                                  (treeset::cardinality-of-delete-when-in
                                   treeset::cardinality-of-diff))))
  :ruler-extenders :all
  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-compatible-3p-exec))

;;;;;;;;;;;;;;;;;;;;

;; The threaded check makes the same comparisons as the path-dependent one
;; up to the pairs it has already visited, whose comparisons
;; are conjoined into its result, so it computes the same result.
;; The three steps of the check that thread the set through two checks,
;; and the step that inserts a pair before checking the members,
;; are stated on the path-dependent checks,
;; as they appear once the results of the threaded checks
;; are replaced by them.

(defruled 3truth<=-and-uid-pair-set-compatible-3p-aux-of-diff
  (implies (and (3truth<= p (uid-pair-set-compatible-3p-aux
                              (treeset::diff s1 (uid-pair-sfix s))
                              completions s ienv))
                (3truth<= b1 (uid-pair-set-compatible-3p-aux
                               (treeset::diff s2 s1) completions s1 ienv))
                (3truth<= b b1)
                (uid-pair-setp s1)
                (uid-pair-setp s2)
                (treeset::subset (uid-pair-sfix s) s1)
                (treeset::subset s1 s2)
                (not (3truth<= p (uid-pair-set-compatible-3p-aux
                                   (treeset::diff s2 (uid-pair-sfix s))
                                   completions s ienv))))
           (3truth<= b
                     (uid-pair-set-compatible-3p-aux
                       (treeset::diff s2 (uid-pair-sfix s))
                       completions s ienv)))
  :use ((:instance uid-pair-set-compatible-3p-aux-when-subset
                   (d (treeset::diff s1 (uid-pair-sfix s)))
                   (e (treeset::diff s2 (uid-pair-sfix s)))
                   (assumed s))
        (:instance 3truth<=-of-uid-pair-set-compatible-3p-aux-of-union
                   (3vl p)
                   (pairs2 (treeset::diff s2 s1))
                   (assumed s)
                   (pairs (treeset::diff s1 (uid-pair-sfix s)))
                   (base s)))
  :enable (acl2::transitivity-of-3truth<=-swapped
           treeset::diff-of-diff-and-diff-becomes-diff-of-union))

(defruled 3and-of-type-struni-member-list-compatible-3p-aux-of-visited
  (implies (and (uid-pair-setp s1)
                (treeset::subset (uid-pair-sfix s) s1)
                (3truth<= p (uid-pair-set-compatible-3p-aux
                              (treeset::diff s1 (uid-pair-sfix s))
                              completions s ienv)))
           (equal (3and p (type-struni-member-list-compatible-3p-aux
                            x y completions s1 ienv))
                  (3and p (type-struni-member-list-compatible-3p-aux
                            x y completions s ienv))))
  :use ((:instance
          3truth<=-of-type-struni-member-list-compatible-3p-aux-of-union
          (3vl p)
          (assumed s)
          (pairs (treeset::diff s1 (uid-pair-sfix s)))
          (base s))
        (:instance acl2::antisymmetry-of-3truth<=-weak
                   (x (3and p (type-struni-member-list-compatible-3p-aux
                                x y completions s1 ienv)))
                   (y (3and p (type-struni-member-list-compatible-3p-aux
                                x y completions s ienv)))))
  :enable acl2::3equiv)

(defruled 3and-of-type-params-compatible-3p-aux-of-visited
  (implies (and (uid-pair-setp s1)
                (treeset::subset (uid-pair-sfix s) s1)
                (3truth<= p (uid-pair-set-compatible-3p-aux
                              (treeset::diff s1 (uid-pair-sfix s))
                              completions s ienv)))
           (equal (3and p (type-params-compatible-3p-aux
                            x y completions s1 ienv))
                  (3and p (type-params-compatible-3p-aux
                            x y completions s ienv))))
  :use ((:instance 3truth<=-of-type-params-compatible-3p-aux-of-union
                   (3vl p)
                   (assumed s)
                   (pairs (treeset::diff s1 (uid-pair-sfix s)))
                   (base s))
        (:instance acl2::antisymmetry-of-3truth<=-weak
                   (x (3and p (type-params-compatible-3p-aux
                                x y completions s1 ienv)))
                   (y (3and p (type-params-compatible-3p-aux
                                x y completions s ienv)))))
  :enable acl2::3equiv)

(defruled 3and-of-type-list-compatible-3p-aux-of-visited
  (implies (and (uid-pair-setp s1)
                (treeset::subset (uid-pair-sfix s) s1)
                (3truth<= p (uid-pair-set-compatible-3p-aux
                              (treeset::diff s1 (uid-pair-sfix s))
                              completions s ienv)))
           (equal (3and p (type-list-compatible-3p-aux
                            x y completions s1 ienv))
                  (3and p (type-list-compatible-3p-aux
                            x y completions s ienv))))
  :use ((:instance 3truth<=-of-type-list-compatible-3p-aux-of-union
                   (3vl p)
                   (assumed s)
                   (pairs (treeset::diff s1 (uid-pair-sfix s)))
                   (base s))
        (:instance acl2::antisymmetry-of-3truth<=-weak
                   (x (3and p (type-list-compatible-3p-aux
                                x y completions s1 ienv)))
                   (y (3and p (type-list-compatible-3p-aux
                                x y completions s ienv)))))
  :enable acl2::3equiv)

(defruled 3truth<=-of-uid-pair-compatible-3p-aux-and-set-of-diff
  (b* ((comparison (uid-pair-compatible-3p-aux pair completions s ienv))
       (visited (treeset::insert pair (uid-pair-sfix s))))
    (implies (and (3truth<= comparison
                            (uid-pair-set-compatible-3p-aux
                              (treeset::diff s1 visited)
                              completions visited ienv))
                  (uid-pairp pair)
                  (uid-pair-setp s1)
                  (not (treeset::in pair (uid-pair-sfix s)))
                  (treeset::subset visited s1))
             (3truth<= comparison
                       (uid-pair-set-compatible-3p-aux
                         (treeset::diff s1 (uid-pair-sfix s))
                         completions s ienv))))
  :use ((:instance 3truth<=-of-uid-pair-set-compatible-3p-aux-of-union
                   (3vl (uid-pair-compatible-3p-aux pair completions s ienv))
                   (pairs2 (treeset::diff s1 (treeset::insert
                                               pair (uid-pair-sfix s))))
                   (assumed s)
                   (pairs (treeset::insert pair (treeset::empty)))
                   (base s))
        (:instance uid-pair-set-compatible-3p-aux-when-in
                   (pairs (treeset::diff s1 (uid-pair-sfix s)))
                   (assumed s))))

(defthm-type/type-list-compatible-3p-exec-flag
  (defthm type-compatible-3p-exec-correct
    (b* (((mv 3vl visited$)
          (type-compatible-3p-exec x y completions visited ienv))
         (visited (uid-pair-sfix visited)))
      (and (equal 3vl
                  (type-compatible-3p-aux x y completions visited ienv))
           (3truth<= 3vl
                     (uid-pair-set-compatible-3p-aux
                       (treeset::diff visited$ visited)
                       completions visited ienv))))
    :flag type-compatible-3p-exec
    :hints ('(:expand ((type-compatible-3p-exec x y completions visited ienv)
                       (type-compatible-3p-aux
                         x y completions visited ienv)))))
  (defthm type-struni-member-list-compatible-3p-exec-correct
    (b* (((mv 3vl visited$)
          (type-struni-member-list-compatible-3p-exec
            x y completions visited ienv))
         (visited (uid-pair-sfix visited)))
      (and (equal 3vl
                  (type-struni-member-list-compatible-3p-aux
                    x y completions visited ienv))
           (3truth<= 3vl
                     (uid-pair-set-compatible-3p-aux
                       (treeset::diff visited$ visited)
                       completions visited ienv))))
    :flag type-struni-member-list-compatible-3p-exec
    :hints ('(:expand ((type-struni-member-list-compatible-3p-exec
                         x y completions visited ienv)
                       (type-struni-member-list-compatible-3p-aux
                         x y completions visited ienv)))))
  (defthm type-params-compatible-3p-exec-correct
    (b* (((mv 3vl visited$)
          (type-params-compatible-3p-exec x y completions visited ienv))
         (visited (uid-pair-sfix visited)))
      (and (equal 3vl
                  (type-params-compatible-3p-aux
                    x y completions visited ienv))
           (3truth<= 3vl
                     (uid-pair-set-compatible-3p-aux
                       (treeset::diff visited$ visited)
                       completions visited ienv))))
    :flag type-params-compatible-3p-exec
    :hints ('(:expand ((type-params-compatible-3p-exec
                         x y completions visited ienv)
                       (type-params-compatible-3p-aux
                         x y completions visited ienv)))))
  (defthm type-list-compatible-3p-exec-correct
    (b* (((mv 3vl visited$)
          (type-list-compatible-3p-exec x y completions visited ienv))
         (visited (uid-pair-sfix visited)))
      (and (equal 3vl
                  (type-list-compatible-3p-aux
                    x y completions visited ienv))
           (3truth<= 3vl
                     (uid-pair-set-compatible-3p-aux
                       (treeset::diff visited$ visited)
                       completions visited ienv))))
    :flag type-list-compatible-3p-exec
    :hints ('(:expand ((type-list-compatible-3p-exec
                         x y completions visited ienv)
                       (type-list-compatible-3p-aux
                         x y completions visited ienv)))))
  :hints
  (("Goal"
    :in-theory
    (enable type/type-list-compatible-3p-exec-flag
            type-struni-member-list-compatible-3p-aux-becomes-uid-pair
            3truth<=-and-uid-pair-set-compatible-3p-aux-of-diff
            3and-of-type-struni-member-list-compatible-3p-aux-of-visited
            3and-of-type-params-compatible-3p-aux-of-visited
            3and-of-type-list-compatible-3p-aux-of-visited
            3truth<=-of-uid-pair-compatible-3p-aux-and-set-of-diff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-compatible-3p ((x typep)
                            (y typep)
                            (completions type-completions-p)
                            (ienv ienvp))
  :returns (3vl 3p)
  :short "Check whether two @(see type)s are compatible
          [C17:6.2.7] [C23:6.2.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type compatibility is a check that two types are
     in some sense ``consistent''.
     Compatibility affects whether a redeclaration is permissible,
     whether one type may be used when another is expected,
     and whether two declarations referring to
     the same object or function are well-defined.")
   (xdoc::p
    "Because we currently only model an approximation of C types,
     our notion of compatibility is also approximate,
     and the result is "
    (xdoc::seetopic "acl2::3vl" "three-valued")
    ".")
   (xdoc::p
    "Note that the provided @('completions') map is interpreted
     as the final map after processing all translation units.
     This is crucial for determining the compatibility of structure types
     across translation units,
     which require knowing whether a type is completed <em>anywhere</em>
     in the relevant translation unit [C17:6.2.7/1] [C23:6.2.7/1].
     That said, compatibility is anti-monotone
     with respect to extensions to the completion map,
     meaning types that which are incompatible in a given completion map
     cannot be compatible under an extended completion map.
     This is exploited by the validator,
     which checks possible compatibility as it goes
     instead of at the end.")
   (xdoc::p
    "When comparing two tagged structure types
     that are declared in different translation units
     (or, under C23, in general),
     we compare their members under the assumption
     that the two types are compatible.
     This is what makes the definition terminate
     on self-referential and mutually recursive structure types.
     See @('type-compatible-3p-aux') and the @('assumed') accumulator.
     For execution, we use @(tsee type-compatible-3p-exec),
     which threads that set through the check instead,
     so that a pair reachable along many paths is compared once;
     it computes the same result,
     as proved by @('type-compatible-3p-exec-correct').")
   (xdoc::p
    "Our approximate notion of type compatibility
     is established by the following cases:")
   (xdoc::ul
    (xdoc::li
     "If any type is unknown, or unknown built-in,
      the result is unknown.")
    (xdoc::li
     "If one of the types is unknown scalar,
      the result is unknown if the other type may be scalar,
      and the types are incompatible otherwise.")
    (xdoc::li
     "If one of the types is unknown arithmetic,
      the result is unknown if the other type may be arithmetic,
      and the types are incompatible otherwise.")
    (xdoc::li
     "Two structure types with the same @(see UID) are compatible:
      the UID establishes that they correspond to
      the same declaration in the same scope [C17:6.7.2.3/4-5].
      Otherwise, structure type compatibility depends on
      whether they are declared in the same translation unit.
      If they are, they are distinct types, and thus incompatible,
      except that under C23 two tagged structure types are compared
      as if they were declared in separate translation units
      (see below).
      If the structure types are declared in different translation units,
      both must be tagged with the same tag, or both untagged,
      and, if both types are complete
      with respect to the type completion environment,
      there must be a one-to-one correspondence between their members
      (the members of untagged structure types are stored directly
      in the types, and they are always complete).
      For a member of one structure type to correspond
      with a member of the other,
      the names must agree and their types must be compatible.
      We do not yet check that member alignment specifiers agree.
      Furthermore, the members of one structure type
      must appear in the same order as
      the corresponding members of the other structure type
      [C17:6.2.7/1] [C23:6.2.7/1].
      Note that, for the purpose of compatibility,
      anonymous structures/unions
      are considered regular members of their containing type.
      (This is not so explicit in C17, but is clarified in [C23:6.2.7/1].)")
    (xdoc::li
     "Union type compatibility mirrors structure type compatibility,
      with the exception that
      corresponding members do not need to appear in the same order
      when comparing unions across translation units [C17:6.2.7/1].
      For now, we do not check the members of two complete unions
      (across translation units, or under C23),
      and the result is unknown in that case.")
    (xdoc::li
     "Due to their approximate representation,
      the compatibility of an enumeration type
      with any enumeration or integer type is unknown [C17:6.7.2.2/4]:
      each enumeration type is compatible with
      an implementation-defined integer type,
      which may vary for different enumeration types.
      An enumeration type is incompatible with any other type.")
    (xdoc::li
     "Pointer types are compatible if they are derived from compatible types;
      we do not currently consider whether the types are qualified
      [C17:6.7.6.1/2].")
    (xdoc::li
     "Array types are compatible
      if their element types are compatible
      and their kinds are compatible
      (see @(tsee type-array-kind-compatible-3p)).")
    (xdoc::li
     "Function types are compatible if
      their return types are compatible [C17:6.7.6.3/15]
      and their @(tsee type-params) are compatible
      (see @(tsee type-params-compatible-3p-aux)).")
    (xdoc::li
     "For any other case, the types are compatible only if they are equal."))
   (xdoc::section
    "C23 Standard"
    (xdoc::p
     "The C23 standard makes various changes to type compatibility,
      of which we only implement some subset.
      When the implementation environment specifies the C23 standard,
      we make the following changes to the C17 type compatibility
      outlined above.")
    (xdoc::ul
     (xdoc::li
      "Two tagged struct types are compared as if
       they were declared in separate translation units [C23:6.2.7/1].")
     (xdoc::li
      "Two tagged union types are compared as if
       they were declared in separate translation units [C23:6.2.7/1]."))))
  (mbe :logic (type-compatible-3p-aux x y completions (treeset::empty) ienv)
       :exec (b* (((mv 3vl &)
                   (type-compatible-3p-exec
                     x y completions (treeset::empty) ienv)))
               3vl))

  ///

  (defrule type-compatible-3p-under-iff-when-same
    (iff (type-compatible-3p x x completions ienv)
         t)
    :enable type-compatible-3p)

  (defrule 3possibly-type-compatible-3p-when-same
    (3possibly (type-compatible-3p x x completions ienv))
    :enable type-compatible-3p)

  (defrule type-compatible-3p-symmetric
    (equal (type-compatible-3p y x completions ienv)
           (type-compatible-3p x y completions ienv))
    :enable type-compatible-3p
    :use (:instance type-compatible-3p-aux-symmetric
                    (assumed (treeset::empty)))
    :disable type-compatible-3p-aux-symmetric)

  (defrule type-compatible-3p-when-submap
    (implies (treemap::submap (type-completions-fix completions1)
                              (type-completions-fix completions))
             (3truth<= (type-compatible-3p x y completions ienv)
                       (type-compatible-3p x y completions1 ienv)))
    :enable (type-compatible-3p
             type-compatible-3p-aux-when-submap))

  (defrule 3possibly-type-compatible-3p-when-submap-fix
    (implies (and (3possibly (type-compatible-3p x y completions ienv))
                  (treemap::submap (type-completions-fix completions1)
                                   (type-completions-fix completions)))
             (3possibly (type-compatible-3p x y completions1 ienv)))
    :use type-compatible-3p-when-submap
    :disable type-compatible-3p-when-submap)

  (defrule 3possibly-type-compatible-3p-when-submap
    (implies (and (treemap::submap completions1 completions)
                  (type-completions-p completions)
                  (3possibly (type-compatible-3p x y completions ienv)))
             (3possibly (type-compatible-3p x y completions1 ienv)))
    :use 3possibly-type-compatible-3p-when-submap-fix
    :disable 3possibly-type-compatible-3p-when-submap-fix)

  (defrule 3definitely-type-compatible-3p-when-submap-fix
    (implies (and (3definitely (type-compatible-3p x y completions ienv))
                  (treemap::submap (type-completions-fix completions1)
                                   (type-completions-fix completions)))
             (3definitely (type-compatible-3p x y completions1 ienv)))
    :use type-compatible-3p-when-submap
    :disable type-compatible-3p-when-submap)

  (defrule 3definitely-type-compatible-3p-when-submap
    (implies (and (treemap::submap completions1 completions)
                  (type-completions-p completions)
                  (3definitely (type-compatible-3p x y completions ienv)))
             (3definitely (type-compatible-3p x y completions1 ienv)))
    :use 3definitely-type-compatible-3p-when-submap-fix
    :disable 3definitely-type-compatible-3p-when-submap-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-kind-composite-conditions-3p ((x type-array-kindp)
                                                 (y type-array-kindp)
                                                 (composite type-array-kindp))
  :returns (3vl 3p)
  :short "Check whether an array kind satisfies the conditions
          for being the composite of two array kinds,
          other than compatibility."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the rules for the sizes of composite array types
     [C17:6.2.7/3] [C23:6.2.7/3];
     the element types are handled in @(tsee type-composite-conditions-3p).
     As there, the input kinds are assumed to be compatible.")
   (xdoc::p
    "If either input has constant length, the composite has constant length,
     and the same length as the input whose length is known, if any;
     if no length is known, we cannot tell whether the lengths agree.
     Otherwise, if either input has nonconstant length,
     its size expression may be one that is not evaluated,
     in which case the behavior is undefined,
     and since we cannot tell, the result is unknown.
     The same applies if either input is complete of unknown kind,
     which may have nonconstant length.
     Otherwise both inputs are incomplete, and so must be the composite."))
  (b* ((x-len? (type-array-kind-case x :const-len x.len :otherwise nil))
       (y-len? (type-array-kind-case y :const-len y.len :otherwise nil))
       ;; Two known lengths that differ are not even compatible.
       ((when (and x-len? y-len? (not (equal x-len? y-len?))))
        nil)
       (len? (or x-len? y-len?)))
    (cond ((or (type-array-kind-case x :const-len)
               (type-array-kind-case y :const-len))
           (type-array-kind-case
             composite
             :const-len (if (and len? composite.len)
                            (equal len? composite.len)
                          :unknown)
             :otherwise nil))
          ((and (type-array-kind-case x :incomplete)
                (type-array-kind-case y :incomplete))
           (type-array-kind-case composite :incomplete))
          (t :unknown))))

(defrule type-array-kind-composite-conditions-3p-under-iff-when-same
  (iff (type-array-kind-composite-conditions-3p x x x)
       t)
  :enable type-array-kind-composite-conditions-3p)

(defrule 3possibly-type-array-kind-composite-conditions-3p-when-same
  (3possibly (type-array-kind-composite-conditions-3p x x x))
  :enable type-array-kind-composite-conditions-3p)

(defrule type-array-kind-composite-conditions-3p-symmetric
  (equal (type-array-kind-composite-conditions-3p y x composite)
         (type-array-kind-composite-conditions-3p x y composite))
  :enable type-array-kind-composite-conditions-3p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-conditions-3p
  (define type-composite-conditions-3p ((x typep)
                                        (y typep)
                                        (composite typep)
                                        (completions type-completions-p)
                                        (assumed uid-triple-setp)
                                        (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether a type satisfies the conditions
            for being a composite of two types,
            other than compatibility [C17:6.2.7/3] [C23:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are the conditions on the composite
       beyond its being compatible with the two input types,
       which are themselves compatible;
       @(tsee type-composite-3p) checks compatibility too.
       Here compatibility is assumed, also for the component types,
       since compatibility is recursive.")
     (xdoc::p
      "In C23, if the two input types are the same type,
       the composite is that type [C23:6.2.7/3];
       C17 has no such rule.
       When we cannot tell whether the types are the same,
       we do not know which case of the rule applies,
       so the result is definite only if both cases give the same answer,
       i.e. it is the join of the two answers.")
     (xdoc::p
      "The remaining conditions are by the kinds of the input types,
       which must agree with the kind of the composite;
       otherwise, the result is unknown.
       The conditions are as follows,
       which apply recursively to the component types
       [C17:6.2.7/3] [C23:6.2.7/3].")
     (xdoc::ul
      (xdoc::li
       "For array types, the array kinds must satisfy
        @(tsee type-array-kind-composite-conditions-3p),
        and the element type must be a composite of the element types
        [C17:6.2.7/3] [C23:6.2.7/3].")
      (xdoc::li
       "For pointer types, the referenced type
        must be a composite of the referenced types.")
      (xdoc::li
       "For function types, the return type
        must be a composite of the return types,
        and the parameters must satisfy
        @(tsee type-params-composite-conditions-3p)
        [C17:6.2.7/3] [C23:6.2.7/3].")
      (xdoc::li
       "For structure types, the composite is formed member-wise
        [C23:6.2.7/3],
        which C17 leaves to the recursive application
        of its rules to the member types [C17:6.2.7/3]:
        if both inputs are complete, so is the composite,
        and its members satisfy
        @(tsee type-struni-member-list-composite-conditions-3p);
        if exactly one input is complete, the composite is complete
        and its members are equal to that input's;
        if both inputs are incomplete, so is the composite.")
      (xdoc::li
       "Union types are treated like structure types,
        except that the members of two complete unions
        may correspond in any order,
        which is not checked yet, so the result is unknown.")
      (xdoc::li
       "For enumerated types, in C23 the composite is an enumerated type
        [C23:6.2.7/3], so a composite of another known kind
        is definitely rejected;
        in C17 the composite may also be an integer type
        compatible with both, which we cannot determine.")
      (xdoc::li
       "For all other types, compatibility is the only requirement."))
     (xdoc::p
      "The @('assumed') set contains the triples of @(see UID)s
       of the tagged structure types whose members are being checked,
       i.e. whose composite relation is currently assumed,
       analogously to the pairs in @(tsee type-compatible-3p-aux).
       When such a triple is encountered again while checking the members,
       it is accepted.
       The set only grows along the recursion,
       and only by triples of UIDs of complete types,
       i.e. of keys of the completions map,
       so the number of triples of keys not in the set
       serves as the first component of the measure.")
     (xdoc::p
      "If the requirements cannot be checked
       because of unknown components of the types,
       the result is unknown."))
    (b* ((c23p (c::standard-case (ienv->std ienv) :c23))
         (conditions-by-kind
          (b* (;; We assume the types are compatible,
               ;; so the kinds are only different
               ;; if one or both is one of the unknown types,
               ;; in which case we cannot check any of the conditions.
               ((unless (equal (type-kind x) (type-kind y)))
                :unknown)
               ((unless (equal (type-kind composite) (type-kind x)))
                ;; In C23, two enumerated types
                ;; compose to an enumerated type.
                (if (and c23p
                         (type-case x :enum)
                         (not (type-some-unknownp composite)))
                    nil
                  :unknown)))
          (type-case
            x
            :array
            (b* (((type-array y) y)
                 ((type-array composite) composite))
              (3and$ (type-array-kind-composite-conditions-3p
                       x.kind y.kind composite.kind)
                     (type-composite-conditions-3p
                       x.of y.of composite.of completions assumed ienv)))
            :pointer
            (b* (((type-pointer y) y)
                 ((type-pointer composite) composite))
              (type-composite-conditions-3p
                x.to y.to composite.to completions assumed ienv))
            :function
            (b* (((type-function y) y)
                 ((type-function composite) composite))
              (3and$ (type-composite-conditions-3p
                       x.ret y.ret composite.ret
                       completions assumed ienv)
                     (type-params-composite-conditions-3p
                       x.params y.params composite.params
                       completions assumed ienv)))
            :struct
            (b* (((type-struct y) y)
                 ((type-struct composite) composite)
                 (kind (type-struni-tag/members-kind x.tag/members))
                 ((unless (and (equal (type-struni-tag/members-kind
                                        y.tag/members)
                                      kind)
                               (equal (type-struni-tag/members-kind
                                        composite.tag/members)
                                      kind)))
                  :unknown))
              (type-struni-tag/members-case
                x.tag/members
                :tagged
                (b* ((completions (type-completions-fix completions))
                     (assumed (uid-triple-sfix assumed))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ((mv composite-foundp composite-members)
                      (treemap::lookup? composite.uid completions))
                     ((when (and (not x-foundp) (not y-foundp)))
                      ;; Both inputs are incomplete,
                      ;; so the composite must be as well.
                      (not composite-foundp))
                     ;; Some input is complete,
                     ;; so the composite must be as well.
                     ((unless composite-foundp)
                      nil)
                     ((unless x-foundp)
                      ;; Only y is complete,
                      ;; so the composite has its members.
                      (type-struni-member-list-equal-3p
                        composite-members y-members))
                     ((unless y-foundp)
                      ;; Only x is complete,
                      ;; so the composite has its members.
                      (type-struni-member-list-equal-3p
                        composite-members x-members))
                     ;; Both x and y are complete.
                     (triple (make-uid-triple :first x.uid
                                              :second y.uid
                                              :third composite.uid))
                     ;; The triple is already assumed.
                     ((when (treeset::in triple assumed))
                      t))
                  (type-struni-member-list-composite-conditions-3p
                    x-members
                    y-members
                    composite-members
                    completions
                    (treeset::insert triple assumed)
                    ienv))
                :untagged
                (type-struni-member-list-composite-conditions-3p
                 x.tag/members.members
                 (type-struni-tag/members-untagged->members y.tag/members)
                 (type-struni-tag/members-untagged->members
                  composite.tag/members)
                 completions
                 assumed
                 ienv)))
            :union
            (b* (((type-union y) y)
                 ((type-union composite) composite)
                 (kind (type-struni-tag/members-kind x.tag/members))
                 ((unless (and (equal (type-struni-tag/members-kind
                                        y.tag/members)
                                      kind)
                               (equal (type-struni-tag/members-kind
                                        composite.tag/members)
                                      kind)))
                  :unknown))
              (type-struni-tag/members-case
                x.tag/members
                :tagged
                (b* ((completions (type-completions-fix completions))
                     (assumed (uid-triple-sfix assumed))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ((mv composite-foundp composite-members)
                      (treemap::lookup? composite.uid completions))
                     ((when (and (not x-foundp) (not y-foundp)))
                      ;; Both inputs are incomplete,
                      ;; so the composite must be as well.
                      (not composite-foundp))
                     ;; Some input is complete,
                     ;; so the composite must be as well.
                     ((unless composite-foundp)
                      nil)
                     ((unless x-foundp)
                      ;; Only y is complete,
                      ;; so the composite has its members.
                      (type-struni-member-list-equal-3p
                        composite-members y-members))
                     ((unless y-foundp)
                      ;; Only x is complete,
                      ;; so the composite has its members.
                      (type-struni-member-list-equal-3p
                        composite-members x-members))
                     ;; Both x and y are complete.
                     (triple (make-uid-triple :first x.uid
                                              :second y.uid
                                              :third composite.uid))
                     ;; The triple is already assumed.
                     ((when (treeset::in triple assumed))
                      t))
                  ;; Members may correspond in any order,
                  ;; not checked yet.
                  :unknown)
                :untagged
                ;; Members may correspond in any order,
                ;; not checked yet.
                :unknown))
            :otherwise t)))
         ;; [C23:6.2.7/3]: if the input types are the same type,
         ;; the composite is that type; otherwise the conditions apply.
         ;; C17 has no such rule.
         (c23p-and-same (3and$ c23p (type-equal-3p x y)))
         ((unless (3possibly c23p-and-same))
          conditions-by-kind)
         (composite-is-input (3and$ (type-equal-3p composite x)
                                    (type-equal-3p composite y)))
         ((when (3definitely c23p-and-same))
          composite-is-input))
      ;; We cannot tell whether the input types are the same type,
      ;; so we do not know which case applies.
      ;; The result is definite only if both cases give the same answer.
      (3join composite-is-input conditions-by-kind))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys (treeset::product keys keys)))
                  (uid-triple-sfix assumed)))
              (+ (type-count x)
                 (type-count y)
                 (type-count composite))))

  (define type-struni-member-list-composite-conditions-3p
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (composite type-struni-member-listp)
     (completions type-completions-p)
     (assumed uid-triple-setp)
     (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether a list of structure or union members
            satisfies the conditions for consisting of composites
            of the corresponding members of two lists of members."
    :long
    (xdoc::topstring
     (xdoc::p
      "The lists must have the same length,
       the names must correspond,
       and each member type must be a composite
       of the corresponding member types."))
    (b* (((when (endp x))
          (and (endp y) (endp composite)))
         ((when (or (endp y) (endp composite)))
          nil)
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y))
         ((type-struni-member member-composite) (first composite))
         ((unless (and (equal member-x.name? member-y.name?)
                       (equal member-composite.name? member-x.name?)))
          nil))
      (3and$ (type-composite-conditions-3p
               member-x.type member-y.type member-composite.type
               completions assumed ienv)
             (type-struni-member-list-composite-conditions-3p
               (rest x) (rest y) (rest composite)
               completions assumed ienv)))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys (treeset::product keys keys)))
                  (uid-triple-sfix assumed)))
              (+ (type-struni-member-list-count x)
                 (type-struni-member-list-count y)
                 (type-struni-member-list-count composite))))

  (define type-params-composite-conditions-3p ((x type-params-p)
                                               (y type-params-p)
                                               (composite type-params-p)
                                               (completions type-completions-p)
                                               (assumed uid-triple-setp)
                                               (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether the parameter portion of a function type
            satisfies the conditions for being the composite
            of the parameter portions of two function types
            [C17:6.2.7/3] [C23:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "If both inputs are prototypes, the composite is a prototype
       with the same ellipsis terminator
       whose parameters are composites of the corresponding parameters.
       If exactly one input is a prototype,
       the composite is a prototype with the same parameter list.
       If neither input is a prototype,
       there is no requirement beyond compatibility,
       which is checked in @(tsee type-composite-3p)."))
    (b* ((x-prototypep (type-params-case x :prototype))
         (y-prototypep (type-params-case y :prototype))
         ((unless (or x-prototypep y-prototypep))
          t)
         ((unless (type-params-case composite :prototype))
          nil)
         ((type-params-prototype composite) composite)
         ((when (and x-prototypep y-prototypep))
          (b* (((type-params-prototype x) x)
               ((type-params-prototype y) y))
            (if (and (equal composite.ellipsis x.ellipsis)
                     (equal composite.ellipsis y.ellipsis))
                (type-list-composite-conditions-3p
                  x.params y.params composite.params completions assumed ienv)
              nil)))
         (prototype (if x-prototypep x y))
         ((type-params-prototype prototype) prototype))
      (if (equal composite.ellipsis prototype.ellipsis)
          (type-list-equal-3p composite.params prototype.params)
        nil))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys (treeset::product keys keys)))
                  (uid-triple-sfix assumed)))
              (+ (type-params-count x)
                 (type-params-count y)
                 (type-params-count composite))))

  (define type-list-composite-conditions-3p ((x type-listp)
                                             (y type-listp)
                                             (composite type-listp)
                                             (completions type-completions-p)
                                             (assumed uid-triple-setp)
                                             (ienv ienvp))
    :returns (3vl 3p)
    :short "Check whether a list of types satisfies the conditions
            for consisting of composites
            of the corresponding elements of two lists of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "The lists must have the same length."))
    (b* (((when (endp x))
          (and (endp y) (endp composite)))
         ((when (or (endp y) (endp composite)))
          nil))
      (3and$ (type-composite-conditions-3p
               (first x) (first y) (first composite)
               completions assumed ienv)
             (type-list-composite-conditions-3p
               (rest x) (rest y) (rest composite)
               completions assumed ienv)))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys (treeset::product keys keys)))
                  (uid-triple-sfix assumed)))
              (+ (type-list-count x)
                 (type-list-count y)
                 (type-list-count composite))))

  :hints (("Goal" :in-theory (e/d (max)
                                  (treeset::cardinality-of-delete-when-in
                                   treeset::cardinality-of-diff))))
  :ruler-extenders :all
  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-composite-conditions-3p
    :hints (("Goal" :in-theory (disable type-fix-when-enum)))))

;; Symmetry in the two input types.

(defthm-type/type-list-composite-conditions-3p-flag
  (defthm type-composite-conditions-3p-symmetric
    (equal (type-composite-conditions-3p
             y x composite completions (uid-triple-set-swap assumed) ienv)
           (type-composite-conditions-3p
             x y composite completions assumed ienv))
    :flag type-composite-conditions-3p
    :hints ('(:expand (type-composite-conditions-3p
                        y x composite completions
                        (uid-triple-set-swap assumed) ienv))))
  (defthm type-struni-member-list-composite-conditions-3p-symmetric
    (equal (type-struni-member-list-composite-conditions-3p
             y x composite completions (uid-triple-set-swap assumed) ienv)
           (type-struni-member-list-composite-conditions-3p
             x y composite completions assumed ienv))
    :flag type-struni-member-list-composite-conditions-3p
    :hints ('(:expand (type-struni-member-list-composite-conditions-3p
                        y x composite completions
                        (uid-triple-set-swap assumed) ienv))))
  (defthm type-params-composite-conditions-3p-symmetric
    (equal (type-params-composite-conditions-3p
             y x composite completions (uid-triple-set-swap assumed) ienv)
           (type-params-composite-conditions-3p
             x y composite completions assumed ienv))
    :flag type-params-composite-conditions-3p
    :hints ('(:expand (type-params-composite-conditions-3p
                        y x composite completions
                        (uid-triple-set-swap assumed) ienv))))
  (defthm type-list-composite-conditions-3p-symmetric
    (equal (type-list-composite-conditions-3p
             y x composite completions (uid-triple-set-swap assumed) ienv)
           (type-list-composite-conditions-3p
             x y composite completions assumed ienv))
    :flag type-list-composite-conditions-3p
    :hints ('(:expand (type-list-composite-conditions-3p
                        y x composite completions
                        (uid-triple-set-swap assumed) ienv))))
  :hints (("Goal"
           :in-theory
           (enable type-composite-conditions-3p
                   type-struni-member-list-composite-conditions-3p
                   type-params-composite-conditions-3p
                   type-list-composite-conditions-3p
                   uid-equal
                   type/type-list-composite-conditions-3p-flag))))

;; Reflexivity: a type is never definitely not a composite of itself
;; with itself.

(encapsulate ()
  (local
    (defthm-type/type-list-composite-conditions-3p-flag
      (defthm type-composite-conditions-3p-when-same-lemma
        (implies (and (equal y x)
                      (equal composite x))
                 (iff (type-composite-conditions-3p
                        x y composite completions assumed ienv)
                      t))
        :flag type-composite-conditions-3p)
      (defthm type-struni-member-list-composite-conditions-3p-when-same-lemma
        (implies (and (equal y x)
                      (equal composite x))
                 (iff (type-struni-member-list-composite-conditions-3p
                        x y composite completions assumed ienv)
                      t))
        :flag type-struni-member-list-composite-conditions-3p)
      (defthm type-params-composite-conditions-3p-when-same-lemma
        (implies (and (equal y x)
                      (equal composite x))
                 (iff (type-params-composite-conditions-3p
                        x y composite completions assumed ienv)
                      t))
        :flag type-params-composite-conditions-3p)
      (defthm type-list-composite-conditions-3p-when-same-lemma
        (implies (and (equal y x)
                      (equal composite x))
                 (iff (type-list-composite-conditions-3p
                        x y composite completions assumed ienv)
                      t))
        :flag type-list-composite-conditions-3p)
      :hints (("Goal"
               :in-theory
               (enable 3and
                       3join
                       type-composite-conditions-3p
                       type-struni-member-list-composite-conditions-3p
                       type-params-composite-conditions-3p
                       type-list-composite-conditions-3p
                       type/type-list-composite-conditions-3p-flag)))))

  (defrule type-composite-conditions-3p-under-iff-when-same
    (iff (type-composite-conditions-3p
           x x x completions assumed ienv)
         t))

  (defrule type-struni-member-list-composite-conditions-3p-under-iff-when-same
    (iff (type-struni-member-list-composite-conditions-3p
           x x x completions assumed ienv)
         t))

  (defrule type-params-composite-conditions-3p-under-iff-when-same
    (iff (type-params-composite-conditions-3p
           x x x completions assumed ienv)
         t))

  (defrule type-list-composite-conditions-3p-under-iff-when-same
    (iff (type-list-composite-conditions-3p
           x x x completions assumed ienv)
         t)))

(defrule 3possibly-type-composite-conditions-3p-when-same
  (3possibly (type-composite-conditions-3p
               x x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-struni-member-list-composite-conditions-3p-when-same
  (3possibly (type-struni-member-list-composite-conditions-3p
               x x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-params-composite-conditions-3p-when-same
  (3possibly (type-params-composite-conditions-3p
               x x x completions assumed ienv))
  :enable (3possibly 3equiv))

(defrule 3possibly-type-list-composite-conditions-3p-when-same
  (3possibly (type-list-composite-conditions-3p
               x x x completions assumed ienv))
  :enable (3possibly 3equiv))

;; Monotonicity in the assumed triples.

(defthm-type/type-list-composite-conditions-3p-flag
  (defthm type-composite-conditions-3p-of-union
    (3truth<= (type-composite-conditions-3p
                x y composite completions assumed ienv)
              (type-composite-conditions-3p
                x y composite completions
                (treeset::union (uid-triple-sfix assumed)
                                (uid-triple-sfix extra))
                ienv))
    :flag type-composite-conditions-3p
    :hints ('(:expand
              ((type-composite-conditions-3p
                 x y composite completions assumed ienv)
               (type-composite-conditions-3p
                 x y composite completions
                 (treeset::union (uid-triple-sfix assumed)
                                 (uid-triple-sfix extra))
                 ienv)))))
  (defthm type-struni-member-list-composite-conditions-3p-of-union
    (3truth<= (type-struni-member-list-composite-conditions-3p
                x y composite completions assumed ienv)
              (type-struni-member-list-composite-conditions-3p
                x y composite completions
                (treeset::union (uid-triple-sfix assumed)
                                (uid-triple-sfix extra))
                ienv))
    :flag type-struni-member-list-composite-conditions-3p
    :hints ('(:expand
              ((type-struni-member-list-composite-conditions-3p
                 x y composite completions assumed ienv)
               (type-struni-member-list-composite-conditions-3p
                 x y composite completions
                 (treeset::union (uid-triple-sfix assumed)
                                 (uid-triple-sfix extra))
                 ienv)))))
  (defthm type-params-composite-conditions-3p-of-union
    (3truth<= (type-params-composite-conditions-3p
                x y composite completions assumed ienv)
              (type-params-composite-conditions-3p
                x y composite completions
                (treeset::union (uid-triple-sfix assumed)
                                (uid-triple-sfix extra))
                ienv))
    :flag type-params-composite-conditions-3p
    :hints ('(:expand
              ((type-params-composite-conditions-3p
                 x y composite completions assumed ienv)
               (type-params-composite-conditions-3p
                 x y composite completions
                 (treeset::union (uid-triple-sfix assumed)
                                 (uid-triple-sfix extra))
                 ienv)))))
  (defthm type-list-composite-conditions-3p-of-union
    (3truth<= (type-list-composite-conditions-3p
                x y composite completions assumed ienv)
              (type-list-composite-conditions-3p
                x y composite completions
                (treeset::union (uid-triple-sfix assumed)
                                (uid-triple-sfix extra))
                ienv))
    :flag type-list-composite-conditions-3p
    :hints ('(:expand
              ((type-list-composite-conditions-3p
                 x y composite completions assumed ienv)
               (type-list-composite-conditions-3p
                 x y composite completions
                 (treeset::union (uid-triple-sfix assumed)
                                 (uid-triple-sfix extra))
                 ienv)))))
  :hints (("Goal"
           :in-theory
           (enable type-composite-conditions-3p
                   type-struni-member-list-composite-conditions-3p
                   type-params-composite-conditions-3p
                   type-list-composite-conditions-3p
                   type/type-list-composite-conditions-3p-flag))))

(defrule type-composite-conditions-3p-when-subset
  (implies (treeset::subset (uid-triple-sfix assumed)
                            (uid-triple-sfix assumed2))
           (3truth<= (type-composite-conditions-3p
                       x y composite completions assumed ienv)
                     (type-composite-conditions-3p
                       x y composite completions assumed2 ienv)))
  :use (:instance type-composite-conditions-3p-of-union
                  (extra assumed2))
  :disable type-composite-conditions-3p-of-union)

(defrule type-struni-member-list-composite-conditions-3p-when-subset
  (implies (treeset::subset (uid-triple-sfix assumed)
                            (uid-triple-sfix assumed2))
           (3truth<= (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed ienv)
                     (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed2 ienv)))
  :use (:instance type-struni-member-list-composite-conditions-3p-of-union
                  (extra assumed2))
  :disable type-struni-member-list-composite-conditions-3p-of-union)

(defrule type-params-composite-conditions-3p-when-subset
  (implies (treeset::subset (uid-triple-sfix assumed)
                            (uid-triple-sfix assumed2))
           (3truth<= (type-params-composite-conditions-3p
                       x y composite completions assumed ienv)
                     (type-params-composite-conditions-3p
                       x y composite completions assumed2 ienv)))
  :use (:instance type-params-composite-conditions-3p-of-union
                  (extra assumed2))
  :disable type-params-composite-conditions-3p-of-union)

(defrule type-list-composite-conditions-3p-when-subset
  (implies (treeset::subset (uid-triple-sfix assumed)
                            (uid-triple-sfix assumed2))
           (3truth<= (type-list-composite-conditions-3p
                       x y composite completions assumed ienv)
                     (type-list-composite-conditions-3p
                       x y composite completions assumed2 ienv)))
  :use (:instance type-list-composite-conditions-3p-of-union
                  (extra assumed2))
  :disable type-list-composite-conditions-3p-of-union)

;; The boolean projections of monotonicity,
;; binding the free set either from the projected fact
;; (the -fix versions, with a fixed hypothesis)
;; or from the subset hypothesis.

(defrule 3possibly-type-composite-conditions-3p-when-subset-fix
  (implies (and (3possibly (type-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3possibly (type-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-composite-conditions-3p-when-subset
  :disable type-composite-conditions-3p-when-subset)

(defrule 3possibly-type-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3possibly (type-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3possibly (type-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3possibly-type-composite-conditions-3p-when-subset-fix
  :disable 3possibly-type-composite-conditions-3p-when-subset-fix)

(defrule
  3possibly-type-struni-member-list-composite-conditions-3p-when-subset-fix
  (implies (and (3possibly (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3possibly (type-struni-member-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-struni-member-list-composite-conditions-3p-when-subset
  :disable type-struni-member-list-composite-conditions-3p-when-subset)

(defrule 3possibly-type-struni-member-list-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3possibly (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3possibly (type-struni-member-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3possibly-type-struni-member-list-composite-conditions-3p-when-subset-fix
  :disable
  3possibly-type-struni-member-list-composite-conditions-3p-when-subset-fix)

(defrule 3possibly-type-params-composite-conditions-3p-when-subset-fix
  (implies (and (3possibly (type-params-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3possibly (type-params-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-params-composite-conditions-3p-when-subset
  :disable type-params-composite-conditions-3p-when-subset)

(defrule 3possibly-type-params-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3possibly (type-params-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3possibly (type-params-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3possibly-type-params-composite-conditions-3p-when-subset-fix
  :disable 3possibly-type-params-composite-conditions-3p-when-subset-fix)

(defrule 3possibly-type-list-composite-conditions-3p-when-subset-fix
  (implies (and (3possibly (type-list-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3possibly (type-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-list-composite-conditions-3p-when-subset
  :disable type-list-composite-conditions-3p-when-subset)

(defrule 3possibly-type-list-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3possibly (type-list-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3possibly (type-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3possibly-type-list-composite-conditions-3p-when-subset-fix
  :disable 3possibly-type-list-composite-conditions-3p-when-subset-fix)

(defrule 3definitely-type-composite-conditions-3p-when-subset-fix
  (implies (and (3definitely (type-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3definitely (type-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-composite-conditions-3p-when-subset
  :disable type-composite-conditions-3p-when-subset)

(defrule 3definitely-type-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3definitely (type-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3definitely (type-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3definitely-type-composite-conditions-3p-when-subset-fix
  :disable 3definitely-type-composite-conditions-3p-when-subset-fix)

(defrule
  3definitely-type-struni-member-list-composite-conditions-3p-when-subset-fix
  (implies (and (3definitely (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3definitely (type-struni-member-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-struni-member-list-composite-conditions-3p-when-subset
  :disable type-struni-member-list-composite-conditions-3p-when-subset)

(defrule 3definitely-type-struni-member-list-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3definitely (type-struni-member-list-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3definitely (type-struni-member-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use
  3definitely-type-struni-member-list-composite-conditions-3p-when-subset-fix
  :disable
  3definitely-type-struni-member-list-composite-conditions-3p-when-subset-fix)

(defrule 3definitely-type-params-composite-conditions-3p-when-subset-fix
  (implies (and (3definitely (type-params-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3definitely (type-params-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-params-composite-conditions-3p-when-subset
  :disable type-params-composite-conditions-3p-when-subset)

(defrule 3definitely-type-params-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3definitely (type-params-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3definitely (type-params-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3definitely-type-params-composite-conditions-3p-when-subset-fix
  :disable 3definitely-type-params-composite-conditions-3p-when-subset-fix)

(defrule 3definitely-type-list-composite-conditions-3p-when-subset-fix
  (implies (and (3definitely (type-list-composite-conditions-3p
                       x y composite completions assumed ienv))
                (treeset::subset (uid-triple-sfix assumed)
                                 (uid-triple-sfix assumed2)))
           (3definitely (type-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use type-list-composite-conditions-3p-when-subset
  :disable type-list-composite-conditions-3p-when-subset)

(defrule 3definitely-type-list-composite-conditions-3p-when-subset
  (implies (and (treeset::subset assumed assumed2)
                (uid-triple-setp assumed2)
                (3definitely (type-list-composite-conditions-3p
                       x y composite completions assumed ienv)))
           (3definitely (type-list-composite-conditions-3p
                   x y composite completions assumed2 ienv)))
  :use 3definitely-type-list-composite-conditions-3p-when-subset-fix
  :disable 3definitely-type-list-composite-conditions-3p-when-subset-fix)

;;;;;;;;;;;;;;;;;;;;

(define type-composite-3p ((x typep)
                           (y typep)
                           (composite typep)
                           (completions type-completions-p)
                           (ienv ienvp))
  :returns (3vl 3p)
  :short "Check whether a type is a composite of two types
          [C17:6.2.7/3] [C23:6.2.7/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specification of composite types,
     as opposed to a construction of one such composite.
     The standard allows more than one type to serve as the composite
     of two compatible types [C23:6.2.7/4],
     so this relation accepts any type satisfying the requirements.")
   (xdoc::p
    "The two input types must be compatible,
     and the putative composite must be compatible with both.
     The remaining conditions are checked by
     @(tsee type-composite-conditions-3p)."))
  (3and$ (type-compatible-3p x y completions ienv)
         (type-compatible-3p composite x completions ienv)
         (type-compatible-3p composite y completions ienv)
         (type-composite-conditions-3p
           x y composite completions (treeset::empty) ienv)))

(defrule type-composite-3p-symmetric
  (equal (type-composite-3p y x composite completions ienv)
         (type-composite-3p x y composite completions ienv))
  :enable type-composite-3p
  :use (:instance type-composite-conditions-3p-symmetric
                  (assumed (treeset::empty)))
  :disable type-composite-conditions-3p-symmetric)

(defrule type-composite-3p-under-iff-when-same
  (iff (type-composite-3p x x x completions ienv)
       t)
  :enable (type-composite-3p 3and))

(defrule 3possibly-type-composite-3p-when-same
  (3possibly (type-composite-3p x x x completions ienv))
  :enable (3possibly 3equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-kind-composite ((x type-array-kindp)
                                   (y type-array-kindp))
  :returns (composite type-array-kindp)
  :short "Construct the array kind of a composite array type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input kinds are expected to come from compatible array types.
     The rules for composite array types distinguish
     arrays of known constant size,
     VLAs with specified or unspecified length,
     and incomplete arrays [C17:6.2.7/3] [C23:6.2.7/3].
     Our array kinds retain less information.
     In particular, @(':nonconst-len') does not distinguish
     specified from unspecified size,
     and we do not track whether a size expression is evaluated.")
   (xdoc::p
    "At the level of our abstraction,
     a @(':const-len') kind takes precedence over every other kind.
     When both kinds are @(':const-len'),
     we retain a known length if either has one.
     Otherwise, a complete kind takes precedence over @(':incomplete').")
   (xdoc::p
    "The composite of @(':nonconst-len')
     and @(':unknown-complete') is @(':unknown-complete').
     The latter could represent a @(':const-len') kind,
     which would take precedence under the standard's rules."))
  (type-array-kind-case
    x
    :const-len
    (type-array-kind-case
      y
      :const-len
      (make-type-array-kind-const-len :len (or x.len y.len))
      :otherwise (type-array-kind-fix x))
    :nonconst-len
    (type-array-kind-case
      y
      :const-len (type-array-kind-fix y)
      :nonconst-len (type-array-kind-nonconst-len)
      :unknown-complete (type-array-kind-unknown-complete)
      :incomplete (type-array-kind-nonconst-len))
    :unknown-complete
    (type-array-kind-case
      y
      :const-len (type-array-kind-fix y)
      :otherwise (type-array-kind-unknown-complete))
    :incomplete (type-array-kind-fix y)))

(defrule type-array-kind-composite-reflexive
  (equal (type-array-kind-composite x x)
         (type-array-kind-fix x))
  :enable type-array-kind-composite
  :disable ((:e type-array-kind-const-len)))

(defrule type-array-kind-composite-symmetric
  (implies (3possibly (type-array-kind-compatible-3p x y))
           (equal (type-array-kind-composite y x)
                  (type-array-kind-composite x y)))
  :enable (type-array-kind-compatible-3p
           type-array-kind-composite
           type-array-kind-fix-when-const-len)
  :disable ((:e type-array-kind-const-len)
            type-array-kind-const-len-of-fields))

(defrule
  3possibly-type-array-kind-compatible-3p-of-type-array-kind-composite-left
  (implies (3possibly (type-array-kind-compatible-3p x y))
           (3possibly (type-array-kind-compatible-3p
                        (type-array-kind-composite x y) x)))
  :enable (type-array-kind-compatible-3p
           type-array-kind-composite
           type-array-kind-fix-when-const-len)
  :disable type-array-kind-const-len-of-fields)

(defrule
  3possibly-type-array-kind-compatible-3p-of-type-array-kind-composite-right
  (implies (3possibly (type-array-kind-compatible-3p x y))
           (3possibly (type-array-kind-compatible-3p
                        (type-array-kind-composite x y) y)))
  :enable (type-array-kind-compatible-3p
           type-array-kind-composite
           type-array-kind-fix-when-const-len)
  :disable type-array-kind-const-len-of-fields)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-input-p
  (define type-composite-input-p ((x typep)
                                  (y typep)
                                  (completions type-completions-p)
                                  (assumed uid-pair-setp))
    :returns (mv (yes/no booleanp)
                 (assumed$
                  (and (uid-pair-setp assumed$)
                       (implies (uid-pair-setp assumed)
                                (treeset::subset assumed assumed$)))))
    :short "Check whether the first of two types is the composite
            that @(tsee type-composite-aux) constructs from them,
            in this order."
    :long
    (xdoc::topstring
     (xdoc::p
      "This boolean check follows the construction:
       it holds when the construction returns the first type unchanged.
       The construction uses it at structure types,
       to return an input whose members are already the composites
       instead of building a new structure type,
       which is the common case across translation units.
       For the other kinds of types the construction needs no check,
       because it returns an input that is the composite by itself,
       e.g. a prototype along with an old-style parameter list.")
     (xdoc::p
      "The @('assumed') set contains the pairs of @(see UID)s
       of the structure types whose first type is assumed to be
       the composite of the pair,
       so that a pair reached again, along a cycle or otherwise,
       holds by assumption.
       Unlike the analogous sets of the relations,
       it is threaded through the check and returned,
       so that a pair reached along different paths is checked once;
       this is sound because the check succeeds only as a whole,
       discharging all the assumptions made along the way together."))
    (b* ((x (type-fix x))
         (y (type-fix y))
         (completions (type-completions-fix completions))
         (assumed (uid-pair-sfix assumed))
         ((when (3definitely (type-equal-3p x y)))
          (mv t assumed))
         ;; The more specific of two unknown types is the composite.
         ((when (type-case x :unknown))
          (mv (type-case y :unknown) assumed))
         ((when (type-case y :unknown))
          (mv t assumed))
         ((when (type-case x :unknown-builtin))
          (mv (type-case y :unknown-builtin) assumed))
         ((when (type-case y :unknown-builtin))
          (mv t assumed))
         ((when (type-case x :unknown-scalar))
          (mv (type-case y :unknown-scalar) assumed))
         ((when (type-case y :unknown-scalar))
          (mv t assumed))
         ((when (type-case x :unknown-arithmetic))
          (mv (type-case y :unknown-arithmetic) assumed))
         ((when (type-case y :unknown-arithmetic))
          (mv t assumed)))
      (type-case
        x
        :array
        (type-case
          y
          :array
          (b* (((unless (equal x.kind
                               (type-array-kind-composite x.kind y.kind)))
                (mv nil assumed)))
            (type-composite-input-p x.of y.of completions assumed))
          :otherwise (mv t assumed))
        :pointer
        (type-case
          y
          :pointer (type-composite-input-p x.to y.to completions assumed)
          :otherwise (mv t assumed))
        :function
        (type-case
          y
          :function
          (b* (((mv yes/no assumed1)
                (type-composite-input-p x.ret y.ret completions assumed))
               ((unless yes/no)
                (mv nil assumed))
               (assumed (if (mbt (and (uid-pair-setp assumed1)
                                      (treeset::subset assumed assumed1)))
                            assumed1
                          assumed)))
            (type-params-composite-input-p
              x.params y.params completions assumed))
          :otherwise (mv t assumed))
        :struct
        (type-case
          y
          :struct
          (b* ((kind (type-struni-tag/members-kind x.tag/members))
               ((unless (equal (type-struni-tag/members-kind y.tag/members)
                               kind))
                (mv t assumed)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (b* (((mv x-foundp x-members)
                    (treemap::lookup? x.uid completions))
                   ((mv y-foundp y-members)
                    (treemap::lookup? y.uid completions))
                   ;; A complete input is the composite with an incomplete one,
                   ;; and the first of two incomplete ones.
                   ((unless y-foundp)
                    (mv t assumed))
                   ((unless x-foundp)
                    (mv nil assumed))
                   ;; Both inputs are complete.
                   (pair (make-uid-pair :first x.uid :second y.uid))
                   ((when (treeset::in pair assumed))
                    (mv t assumed)))
                (type-struni-member-list-composite-input-p
                  x-members y-members completions
                  (treeset::insert pair assumed)))
              :untagged
              (type-struni-member-list-composite-input-p
                x.tag/members.members
                (type-struni-tag/members-untagged->members y.tag/members)
                completions
                assumed)))
          :otherwise (mv t assumed))
        :union
        (type-case
          y
          :union
          (type-struni-tag/members-case
            x.tag/members
            :tagged
            ;; A complete input is the composite with an incomplete one,
            ;; and the first of two incomplete or of two complete ones,
            ;; as complete unions are not composed yet.
            (b* (((mv x-foundp &)
                  (treemap::lookup? x.uid completions))
                 ((when x-foundp)
                  (mv t assumed))
                 ((mv y-foundp &)
                  (treemap::lookup? y.uid completions)))
              (mv (not y-foundp) assumed))
            :untagged (mv t assumed))
          :otherwise (mv t assumed))
        :enum (mv t assumed)
        :otherwise (mv (not (type-case y :enum)) assumed)))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (+ (type-count x) (type-count y))))

  (define type-struni-member-list-composite-input-p
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (completions type-completions-p)
     (assumed uid-pair-setp))
    :returns (mv (yes/no booleanp)
                 (assumed$
                  (and (uid-pair-setp assumed$)
                       (implies (uid-pair-setp assumed)
                                (treeset::subset assumed assumed$)))))
    :short "Check whether the first of two lists of members
            consists of the composites that
            @(tsee type-struni-member-list-composite-aux) constructs,
            in this order."
    (b* ((assumed (uid-pair-sfix assumed))
         ((when (endp x))
          (mv t assumed))
         ((when (endp y))
          (mv nil assumed))
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y))
         ((mv yes/no assumed1)
          (type-composite-input-p
            member-x.type member-y.type completions assumed))
         ((unless yes/no)
          (mv nil assumed))
         (assumed (if (mbt (and (uid-pair-setp assumed1)
                                (treeset::subset assumed assumed1)))
                      assumed1
                    assumed)))
      (type-struni-member-list-composite-input-p
        (rest x) (rest y) completions assumed))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (+ (type-struni-member-list-count x)
                 (type-struni-member-list-count y))))

  (define type-params-composite-input-p ((x type-params-p)
                                         (y type-params-p)
                                         (completions type-completions-p)
                                         (assumed uid-pair-setp))
    :returns (mv (yes/no booleanp)
                 (assumed$
                  (and (uid-pair-setp assumed$)
                       (implies (uid-pair-setp assumed)
                                (treeset::subset assumed assumed$)))))
    :short "Check whether the first of two parameter portions
            of function types is the one that
            @(tsee type-params-composite-aux) constructs,
            in this order."
    (b* ((x (type-params-fix x))
         (y (type-params-fix y))
         (assumed (uid-pair-sfix assumed))
         (x-prototypep (type-params-case x :prototype))
         (y-prototypep (type-params-case y :prototype))
         ((when (and x-prototypep y-prototypep))
          (type-list-composite-input-p
            (type-params-prototype->params x)
            (type-params-prototype->params y)
            completions
            assumed))
         ((when x-prototypep)
          (mv t assumed))
         ((when y-prototypep)
          (mv nil assumed)))
      (mv (or (type-params-case x :old-style)
              (not (type-params-case y :old-style)))
          assumed))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (+ (type-params-count x) (type-params-count y))))

  (define type-list-composite-input-p ((x type-listp)
                                       (y type-listp)
                                       (completions type-completions-p)
                                       (assumed uid-pair-setp))
    :returns (mv (yes/no booleanp)
                 (assumed$
                  (and (uid-pair-setp assumed$)
                       (implies (uid-pair-setp assumed)
                                (treeset::subset assumed assumed$)))))
    :short "Check whether the first of two lists of types
            consists of the composites that
            @(tsee type-list-composite-aux) constructs,
            in this order."
    (b* ((assumed (uid-pair-sfix assumed))
         ((when (endp x))
          (mv t assumed))
         ((when (endp y))
          (mv nil assumed))
         ((mv yes/no assumed1)
          (type-composite-input-p (first x) (first y) completions assumed))
         ((unless yes/no)
          (mv nil assumed))
         (assumed (if (mbt (and (uid-pair-setp assumed1)
                                (treeset::subset assumed assumed1)))
                      assumed1
                    assumed)))
      (type-list-composite-input-p (rest x) (rest y) completions assumed))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix completions))))
                    (treeset::product keys keys))
                  (uid-pair-sfix assumed)))
              (+ (type-list-count x) (type-list-count y))))

  :hints (("Goal" :in-theory (e/d (nfix)
                                  (treeset::cardinality-of-delete-when-in
                                   treeset::cardinality-of-diff))))
  :ruler-extenders :all
  :verify-guards :after-returns
  :flag-local nil
  ///

  ;; The struct case calls the member list check on looked-up members,
  ;; which the rewriter does not open by itself.
  (fty::deffixequiv-mutual type/type-list-composite-input-p
    :hints
    (("Goal"
      :in-theory (disable type-fix-when-enum)
      :expand
      ((type-composite-input-p x y completions assumed)
       (type-composite-input-p (type-fix x) y completions assumed)
       (type-composite-input-p x (type-fix y) completions assumed)
       (type-composite-input-p
         x y (type-completions-fix completions) assumed)
       (type-composite-input-p x y completions (uid-pair-sfix assumed)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-aux
  (define type-composite-aux ((x typep)
                              (y typep)
                              (original-completions type-completions-p)
                              (completions type-completions-p)
                              (composites uid-pair-uid-mapp)
                              (next-uid uidp))
    :returns (mv (composite typep)
                 (completions$ type-completions-p)
                 (composites$
                  (and (uid-pair-uid-mapp composites$)
                       (implies (uid-pair-uid-mapp composites)
                                (treemap::submap composites composites$))))
                 (next-uid$ uidp))
    :short "Construct a composite of two compatible types
            [C17:6.2.7/3] [C23:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the constructive counterpart of @(tsee type-composite-3p):
       the intent is that the result satisfies that relation
       with respect to the extended completions map.
       The input types are assumed to be compatible.")
     (xdoc::p
      "The @('original-completions') map
       is the one at the start of the construction;
       it is not changed and it is used for all the lookups,
       since the members of the input types are types
       that predate the construction.
       The completions of the constructed struct types
       are added to @('completions'),
       which the caller initializes with the same map.
       The @('composites') map records the struct types
       constructed so far for each pair of input struct types,
       so that a pair encountered again, along a cycle or otherwise,
       gets the same composite;
       it is threaded through the construction and returned.
       The @('next-uid') is the next fresh @(see UID).")
     (xdoc::p
      "If the two types are definitely the same type,
       according to @(tsee type-equal-3p),
       that type is the composite [C23:6.2.7/3].
       When one input is an unknown type,
       the composite is the more specific input.
       Otherwise, the composite is built by kind:
       the array kind composite via @(tsee type-array-kind-composite)
       with a composite element type;
       a pointer to a composite;
       a function with a composite return type and parameters
       via @(tsee type-params-composite-aux);
       an enumerated type when either input is one,
       as C23 requires [C23:6.2.7/3];
       a structure type from two structure types as follows.
       If just one is complete, that one.
       If both are complete,
       the one recorded in @('composites') for the pair of inputs,
       if it has been composed already;
       otherwise an input whose members are already the composites
       of the corresponding members,
       as checked by @(tsee type-struni-member-list-composite-input-p),
       since the standard allows the composite to be an input
       [C23:6.2.7/4];
       otherwise a new structure type whose members are
       the composites of the corresponding members,
       via @(tsee type-struni-member-list-composite-aux).
       The members of untagged structure types are part of the types,
       and are treated in the same way, without recording the pair.
       A union type is the composite with an incomplete one;
       two complete union types are not composed yet,
       since their members may correspond in any order,
       and the first is returned.
       For the other kinds, an input that is the composite by itself
       is returned without a separate check,
       e.g. a prototype along with an old-style parameter list,
       and an old-style parameter list along with an unspecified one,
       which constrains later declarations more.")
     (xdoc::p
      "The measure counts the pairs of keys of @('original-completions')
       not yet in @('composites'), which grows along the construction;
       since it is threaded, the calls that pass on the map returned by
       a previous call confirm, via @(tsee mbt), that it extends the one
       passed in, which the return type theorems guarantee."))
    (b* ((x (type-fix x))
         (y (type-fix y))
         (original-completions (type-completions-fix original-completions))
         (completions (type-completions-fix completions))
         (composites (uid-pair-uid-mfix composites))
         (next-uid (uid-fix next-uid))
         ;; Two types that are definitely the same type
         ;; have that type as composite.
         ((when (3definitely (type-equal-3p x y)))
          (mv x completions composites next-uid))
         ;; The more specific of two unknown types wins.
         ((when (type-case x :unknown))
          (mv y completions composites next-uid))
         ((when (type-case y :unknown))
          (mv x completions composites next-uid))
         ((when (type-case x :unknown-builtin))
          (mv y completions composites next-uid))
         ((when (type-case y :unknown-builtin))
          (mv x completions composites next-uid))
         ((when (type-case x :unknown-scalar))
          (mv y completions composites next-uid))
         ((when (type-case y :unknown-scalar))
          (mv x completions composites next-uid))
         ((when (type-case x :unknown-arithmetic))
          (mv y completions composites next-uid))
         ((when (type-case y :unknown-arithmetic))
          (mv x completions composites next-uid)))
      (type-case
        x
        :array
        (type-case
          y
          :array
          (b* (((mv of completions composites next-uid)
                (type-composite-aux
                  x.of y.of original-completions completions composites
                  next-uid)))
            (mv (make-type-array
                  :of of
                  :kind (type-array-kind-composite x.kind y.kind))
                completions
                composites
                next-uid))
          :otherwise (mv x completions composites next-uid))
        :pointer
        (type-case
          y
          :pointer
          (b* (((mv to completions composites next-uid)
                (type-composite-aux
                  x.to y.to original-completions completions composites
                  next-uid)))
            (mv (make-type-pointer :to to)
                completions
                composites
                next-uid))
          :otherwise (mv x completions composites next-uid))
        :function
        (type-case
          y
          :function
          (b* (((mv ret completions composites1 next-uid)
                (type-composite-aux
                  x.ret y.ret original-completions completions composites
                  next-uid))
               (composites (if (mbt (and (uid-pair-uid-mapp composites1)
                                         (treemap::submap composites
                                                          composites1)))
                               composites1
                             composites))
               ((mv params completions composites next-uid)
                (type-params-composite-aux
                  x.params y.params original-completions completions composites
                  next-uid)))
            (mv (make-type-function :ret ret :params params)
                completions
                composites
                next-uid))
          :otherwise (mv x completions composites next-uid))
        :struct
        (type-case
          y
          :struct
          (b* ((kind (type-struni-tag/members-kind x.tag/members))
               ((unless (equal (type-struni-tag/members-kind y.tag/members)
                               kind))
                (mv x completions composites next-uid)))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (b* (((mv x-foundp x-members)
                    (treemap::lookup? x.uid original-completions))
                   ((mv y-foundp y-members)
                    (treemap::lookup? y.uid original-completions))
                   ;; A complete input is the composite with an incomplete one,
                   ;; and the first of two incomplete ones.
                   ((unless y-foundp)
                    (mv x completions composites next-uid))
                   ((unless x-foundp)
                    (mv y completions composites next-uid))
                   ;; Both inputs are complete:
                   ;; the composite of the pair, if built already.
                   (pair (make-uid-pair :first x.uid :second y.uid))
                   ((mv foundp composite-uid)
                    (treemap::lookup? pair composites))
                   ((when foundp)
                    (mv (make-type-struct :uid composite-uid
                                          :tunit? nil
                                          :tag/members x.tag/members)
                        completions
                        composites
                        next-uid))
                   ;; An input whose members are the composites
                   ;; is the composite.
                   ((mv x-inputp &)
                    (type-struni-member-list-composite-input-p
                      x-members y-members original-completions
                      (treeset::insert pair (treeset::empty))))
                   ((when x-inputp)
                    (mv x completions composites next-uid))
                   ((mv y-inputp &)
                    (type-struni-member-list-composite-input-p
                      y-members x-members original-completions
                      (treeset::insert (uid-pair-swap pair)
                                       (treeset::empty))))
                   ((when y-inputp)
                    (mv y completions composites next-uid))
                   ;; Otherwise, a new structure type,
                   ;; recorded before its members are composed,
                   ;; so that the pair reached again through them gets it.
                   (composite-uid next-uid)
                   (next-uid (uid-increment next-uid))
                   (composites (treemap::update pair composite-uid composites))
                   ((mv members completions composites next-uid)
                    (type-struni-member-list-composite-aux
                      x-members y-members original-completions completions
                      composites next-uid))
                   (completions
                    (treemap::update composite-uid members completions)))
                (mv (make-type-struct :uid composite-uid
                                      :tunit? nil
                                      :tag/members x.tag/members)
                    completions
                    composites
                    next-uid))
              :untagged
              ;; The members are part of the types:
              ;; an input whose members are the composites is the composite,
              ;; otherwise a new structure type with their composites.
              (b* ((x-members x.tag/members.members)
                   (y-members (type-struni-tag/members-untagged->members
                                y.tag/members))
                   ((mv x-inputp &)
                    (type-struni-member-list-composite-input-p
                      x-members y-members original-completions
                      (treeset::empty)))
                   ((when x-inputp)
                    (mv x completions composites next-uid))
                   ((mv y-inputp &)
                    (type-struni-member-list-composite-input-p
                      y-members x-members original-completions
                      (treeset::empty)))
                   ((when y-inputp)
                    (mv y completions composites next-uid))
                   (composite-uid next-uid)
                   (next-uid (uid-increment next-uid))
                   ((mv members completions composites next-uid)
                    (type-struni-member-list-composite-aux
                      x-members y-members original-completions completions
                      composites next-uid)))
                (mv (make-type-struct
                      :uid composite-uid
                      :tunit? nil
                      :tag/members (type-struni-tag/members-untagged members))
                    completions
                    composites
                    next-uid))))
          :otherwise (mv x completions composites next-uid))
        :union
        (type-case
          y
          :union
          (type-struni-tag/members-case
            x.tag/members
            :tagged
            ;; A complete input is the composite with an incomplete one,
            ;; and the first of two incomplete ones.
            ;; The members of two complete ones may correspond in any order,
            ;; which is not handled yet, and the first is returned.
            (b* (((mv x-foundp &)
                  (treemap::lookup? x.uid original-completions))
                 ((when x-foundp)
                  (mv x completions composites next-uid))
                 ((mv y-foundp &)
                  (treemap::lookup? y.uid original-completions))
                 ((when y-foundp)
                  (mv y completions composites next-uid)))
              (mv x completions composites next-uid))
            ;; The members may correspond in any order,
            ;; which is not handled yet.
            :untagged (mv x completions composites next-uid))
          :otherwise (mv x completions composites next-uid))
        :enum (mv x completions composites next-uid)
        :otherwise
        (if (type-case y :enum)
            (mv y completions composites next-uid)
          (mv x completions composites next-uid))))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix original-completions))))
                    (treeset::product keys keys))
                  (treemap::keys (uid-pair-uid-mfix composites))))
              (+ (type-count x) (type-count y))))

  (define type-struni-member-list-composite-aux
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (original-completions type-completions-p)
     (completions type-completions-p)
     (composites uid-pair-uid-mapp)
     (next-uid uidp))
    :returns (mv (members type-struni-member-listp)
                 (completions$ type-completions-p)
                 (composites$
                  (and (uid-pair-uid-mapp composites$)
                       (implies (uid-pair-uid-mapp composites)
                                (treemap::submap composites composites$))))
                 (next-uid$ uidp))
    :short "Construct the composites of the corresponding members
            of two lists of structure or union members."
    :long
    (xdoc::topstring
     (xdoc::p
      "The lists are assumed to have the same length
       and correspondingly named members,
       as they do when they come from compatible types;
       the names are taken from the first list."))
    (b* ((completions (type-completions-fix completions))
         (composites (uid-pair-uid-mfix composites))
         (next-uid (uid-fix next-uid))
         ((when (or (endp x) (endp y)))
          (mv nil completions composites next-uid))
         ((type-struni-member member-x) (first x))
         ((type-struni-member member-y) (first y))
         ((mv type completions composites1 next-uid)
          (type-composite-aux
            member-x.type member-y.type original-completions completions
            composites next-uid))
         (composites (if (mbt (and (uid-pair-uid-mapp composites1)
                                   (treemap::submap composites composites1)))
                         composites1
                       composites))
         ((mv members completions composites next-uid)
          (type-struni-member-list-composite-aux
            (rest x) (rest y) original-completions completions composites
            next-uid)))
      (mv (cons (make-type-struni-member :name? member-x.name? :type type)
                members)
          completions
          composites
          next-uid))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix original-completions))))
                    (treeset::product keys keys))
                  (treemap::keys (uid-pair-uid-mfix composites))))
              (+ (type-struni-member-list-count x)
                 (type-struni-member-list-count y))))

  (define type-params-composite-aux ((x type-params-p)
                                     (y type-params-p)
                                     (original-completions type-completions-p)
                                     (completions type-completions-p)
                                     (composites uid-pair-uid-mapp)
                                     (next-uid uidp))
    :returns (mv (params type-params-p)
                 (completions$ type-completions-p)
                 (composites$
                  (and (uid-pair-uid-mapp composites$)
                       (implies (uid-pair-uid-mapp composites)
                                (treemap::submap composites composites$))))
                 (next-uid$ uidp))
    :short "Construct the parameter portion of a composite function type
            [C17:6.2.7/3] [C23:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "If both inputs are prototypes, the composite is a prototype
       with composite parameters and the ellipsis terminator of the inputs,
       which agree on it since they are compatible.
       If exactly one input is a prototype, it is the composite.
       If neither is, the standard imposes no requirement,
       and we prefer an old-style one over an unspecified one,
       since it constrains later declarations more."))
    (b* ((x (type-params-fix x))
         (y (type-params-fix y))
         (completions (type-completions-fix completions))
         (composites (uid-pair-uid-mfix composites))
         (next-uid (uid-fix next-uid))
         (x-prototypep (type-params-case x :prototype))
         (y-prototypep (type-params-case y :prototype))
         ((when (and x-prototypep y-prototypep))
          (b* (((type-params-prototype x) x)
               ((type-params-prototype y) y)
               ((mv params completions composites next-uid)
                (type-list-composite-aux
                  x.params y.params original-completions completions composites
                  next-uid)))
            (mv (make-type-params-prototype :params params
                                            :ellipsis x.ellipsis)
                completions
                composites
                next-uid)))
         ((when x-prototypep)
          (mv x completions composites next-uid))
         ((when y-prototypep)
          (mv y completions composites next-uid))
         ((when (type-params-case x :old-style))
          (mv x completions composites next-uid))
         ((when (type-params-case y :old-style))
          (mv y completions composites next-uid)))
      (mv x completions composites next-uid))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix original-completions))))
                    (treeset::product keys keys))
                  (treemap::keys (uid-pair-uid-mfix composites))))
              (+ (type-params-count x) (type-params-count y))))

  (define type-list-composite-aux ((x type-listp)
                                   (y type-listp)
                                   (original-completions type-completions-p)
                                   (completions type-completions-p)
                                   (composites uid-pair-uid-mapp)
                                   (next-uid uidp))
    :returns (mv (types type-listp)
                 (completions$ type-completions-p)
                 (composites$
                  (and (uid-pair-uid-mapp composites$)
                       (implies (uid-pair-uid-mapp composites)
                                (treemap::submap composites composites$))))
                 (next-uid$ uidp))
    :short "Construct the composites of the corresponding elements
            of two lists of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "The lists are assumed to have the same length,
       as they do when they come from compatible types."))
    (b* ((completions (type-completions-fix completions))
         (composites (uid-pair-uid-mfix composites))
         (next-uid (uid-fix next-uid))
         ((when (or (endp x) (endp y)))
          (mv nil completions composites next-uid))
         ((mv type completions composites1 next-uid)
          (type-composite-aux
            (first x) (first y) original-completions completions composites
            next-uid))
         (composites (if (mbt (and (uid-pair-uid-mapp composites1)
                                   (treemap::submap composites composites1)))
                         composites1
                       composites))
         ((mv types completions composites next-uid)
          (type-list-composite-aux
            (rest x) (rest y) original-completions completions composites
            next-uid)))
      (mv (cons type types) completions composites next-uid))
    :measure (two-nats-measure
              (treeset::cardinality
                (treeset::diff
                  (let ((keys (treemap::keys
                                (type-completions-fix original-completions))))
                    (treeset::product keys keys))
                  (treemap::keys (uid-pair-uid-mfix composites))))
              (+ (type-list-count x) (type-list-count y))))

  :hints (("Goal" :in-theory (disable treeset::cardinality-of-delete-when-in
                                      treeset::cardinality-of-diff)))
  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-composite-aux))

;;;;;;;;;;;;;;;;;;;;

(define type-composite ((x typep)
                        (y typep)
                        (completions type-completions-p)
                        (composites uid-pair-uid-mapp)
                        (next-uid uidp))
  :returns (mv (composite typep)
               (completions$ type-completions-p)
               (composites$ uid-pair-uid-mapp)
               (next-uid$ uidp))
  :short "Construct a composite of two compatible types
          [C17:6.2.7/3] [C23:6.2.7/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee type-composite-aux).
     The completions map is extended with the completions
     of the constructed struct types."))
  (type-composite-aux
    x y completions completions composites next-uid))
