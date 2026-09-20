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

(acl2::controlled-configuration)

(local (include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system))
(local (include-book "kestrel/data/treemap/submap" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/product" :dir :system))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(defrulel equal-of-nfix-and-0
  (equal (equal (nfix x) 0)
         (not (posp x)))
  :enable nfix)

;; The fixers of the completions map and of the sets of UIDs
;; map ill-typed values to the empty map or set,
;; which is a submap or subset of anything.

(defrule submap-of-type-completions-fix-when-submap
  (implies (treemap::submap x y)
           (treemap::submap (type-completions-fix x) y))
  :enable type-completions-fix)

(defrule subset-of-uid-pair-sfix-when-subset
  (implies (treeset::subset x y)
           (treeset::subset (uid-pair-sfix x) y))
  :enable uid-pair-sfix)

(defrule subset-of-uid-triple-sfix-when-subset
  (implies (treeset::subset x y)
           (treeset::subset (uid-triple-sfix x) y))
  :enable uid-triple-sfix)

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
                       (:i type/type-list-compatible-3p-aux-flag))))))

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
                              (:i type/type-list-compatible-3p-aux-flag)))))

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
                   (:i type/type-list-compatible-3p-aux-flag)))))

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
                   (:i type/type-list-compatible-3p-aux-flag)))))

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
     See @('type-compatible-3p-aux') and the @('assumed') accumulator.")
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
  (type-compatible-3p-aux x y completions (treeset::empty) ienv)

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
                   (:i type/type-list-composite-conditions-3p-flag)))))

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
                       (:i type/type-list-composite-conditions-3p-flag))))))

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
                   (:i type/type-list-composite-conditions-3p-flag)))))

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
     as opposed to @(tsee type-composite),
     which constructs one such satisfying composite.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-composite-is-input-p-base ((x typep) (y typep))
  :returns (yes/no booleanp)
  :short "The base case for @('type-composite-is-input-p'),
          covering when the two types are not the same kind of derived type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This mirrors the non-recursive cases of @(tsee type-composite-aux):
     when one of the types is an unknown variant,
     the composite is the more specific type,
     and otherwise it is the first type.
     The result for incompatible types is immaterial."))
  (type-case
    x
    :struct (type-case y :unknown t :unknown-builtin t :otherwise nil)
    :union t
    :array (type-case y :unknown t :unknown-builtin t :otherwise nil)
    :pointer (type-case y
                        :unknown t
                        :unknown-builtin t
                        :unknown-scalar t
                        :otherwise nil)
    :function (type-case y :unknown t :unknown-builtin t :otherwise nil)
    :unknown (type-case y :unknown)
    :unknown-builtin (and (type-case y '(:unknown :unknown-builtin)) t)
    :unknown-scalar (and (type-case y '(:unknown
                                        :unknown-builtin
                                        :unknown-scalar))
                         t)
    :unknown-arithmetic (and (type-case y '(:unknown
                                            :unknown-builtin
                                            :unknown-scalar
                                            :unknown-arithmetic))
                             t)
    :otherwise t))

;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-is-input-p
  (define type-composite-is-input-p ((x typep)
                                     (y typep)
                                     (completions type-completions-p)
                                     (visited uid-pair-setp)
                                     (count natp))
    :returns (mv (leftp booleanp)
                 (rightp booleanp)
                 (new-visited uid-pair-setp))
    :short "Check whether either of two @(see type)s is already
            a composite of the two."
    :long
    (xdoc::topstring
     (xdoc::p
      "The first result says whether @('x') satisfies every requirement
       of a composite of @('x') and @('y') [C17:6.2.7/3] [C23:6.2.7/3],
       so that @('x') itself may serve as the composite [C23:6.2.7/4];
       the second result says the same of @('y').
       The case analysis mirrors that of @(tsee type-composite-aux),
       with @(tsee type-composite-is-input-p-base)
       covering the non-recursive cases.")
     (xdoc::p
      "Since the struct types reachable through @('completions')
       may be cyclic,
       the @('visited') set records the pairs of struct @(see UID)s
       already encountered, and a revisited pair is accepted,
       analogously to the assumed pairs in @(tsee type-compatible-3p-aux).
       As in @(tsee type-composite-aux),
       termination is ensured by @('count');
       when it is exhausted, the check fails in both directions,
       which is always safe."))
    (b* ((visited (uid-pair-sfix visited))
         (completions (type-completions-fix completions))
         ((when (= (the unsigned-byte (lnfix count)) 0))
          (mv nil nil visited)))
      (type-case
        x
        :struct
        (type-case
          y
          :struct
          (if (uid-equal x.uid y.uid)
              (mv t t visited)
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* ((pair (make-uid-pair :first x.uid :second y.uid))
                     ((when (treeset::in pair visited))
                      (mv t t visited))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ;; An incomplete type is a composite
                     ;; only if the other is incomplete too;
                     ;; a complete type is a composite
                     ;; if the other is incomplete.
                     ((unless x-foundp)
                      (mv (not y-foundp) t visited))
                     ((unless y-foundp)
                      (mv t nil visited))
                     (visited (treeset::insert pair visited)))
                  (type-struni-member-list-composite-is-input-p
                    x-members
                    y-members
                    completions
                    visited
                    (- (the unsigned-byte count) 1)))
                :untagged (mv t t visited))
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged (mv t t visited)
                :untagged
                (type-struni-member-list-composite-is-input-p
                  x.tag/members.members
                  y.tag/members.members
                  completions
                  visited
                  (- (the unsigned-byte count) 1)))))
          :otherwise (mv (type-composite-is-input-p-base x y)
                         (type-composite-is-input-p-base y x)
                         visited))
        :array
        (type-case
          y
          :array
          (b* ((kind (type-array-kind-composite x.kind y.kind))
               (kind-leftp (equal kind x.kind))
               (kind-rightp (equal kind y.kind))
               ((unless (or kind-leftp kind-rightp))
                (mv nil nil visited))
               ((mv leftp rightp visited)
                (type-composite-is-input-p x.of
                                           y.of
                                           completions
                                           visited
                                           (- (the unsigned-byte count) 1))))
            (mv (and kind-leftp leftp)
                (and kind-rightp rightp)
                visited))
          :otherwise (mv (type-composite-is-input-p-base x y)
                         (type-composite-is-input-p-base y x)
                         visited))
        :pointer
        (type-case
          y
          :pointer (type-composite-is-input-p x.to
                                              y.to
                                              completions
                                              visited
                                              (- (the unsigned-byte count) 1))
          :otherwise (mv (type-composite-is-input-p-base x y)
                         (type-composite-is-input-p-base y x)
                         visited))
        :function
        (type-case
          y
          :function
          (b* (((mv leftp rightp visited)
                (type-composite-is-input-p x.ret
                                           y.ret
                                           completions
                                           visited
                                           (- (the unsigned-byte count) 1)))
               ((unless (or leftp rightp))
                (mv nil nil visited))
               ((mv params-leftp params-rightp visited)
                (type-params-composite-is-input-p
                  x.params
                  y.params
                  completions
                  visited
                  (- (the unsigned-byte count) 1))))
            (mv (and leftp params-leftp)
                (and rightp params-rightp)
                visited))
          :otherwise (mv (type-composite-is-input-p-base x y)
                         (type-composite-is-input-p-base y x)
                         visited))
        :otherwise (mv (type-composite-is-input-p-base x y)
                       (type-composite-is-input-p-base y x)
                       visited)))
    :measure (nfix count))

  (define type-struni-member-list-composite-is-input-p
    ((x type-struni-member-listp)
     (y type-struni-member-listp)
     (completions type-completions-p)
     (visited uid-pair-setp)
     (count natp))
    :returns (mv (leftp booleanp)
                 (rightp booleanp)
                 (new-visited uid-pair-setp))
    :short "Check whether either of two @(tsee type-struni-member-list)s
            is already a composite of the two."
    :long
    (xdoc::topstring
     (xdoc::p
      "The composite member list is as long as the shorter list,
       so a list is a composite only if it is at most as long as the other."))
    (b* ((visited (uid-pair-sfix visited))
         ((when (endp x)) (mv t (endp y) visited))
         ((when (endp y)) (mv nil t visited))
         ((when (= (the unsigned-byte (lnfix count)) 0))
          (mv nil nil visited))
         ((mv leftp rightp visited)
          (type-composite-is-input-p (type-struni-member->type (first x))
                                     (type-struni-member->type (first y))
                                     completions
                                     visited
                                     (- (the unsigned-byte count) 1)))
         ((unless (or leftp rightp)) (mv nil nil visited))
         ((mv rest-leftp rest-rightp visited)
          (type-struni-member-list-composite-is-input-p
            (rest x)
            (rest y)
            completions
            visited
            (- (the unsigned-byte count) 1))))
      (mv (and leftp rest-leftp)
          (and rightp rest-rightp)
          visited))
    :measure (nfix count))

  (define type-params-composite-is-input-p ((x type-params-p)
                                            (y type-params-p)
                                            (completions type-completions-p)
                                            (visited uid-pair-setp)
                                            (count natp))
    :returns (mv (leftp booleanp)
                 (rightp booleanp)
                 (new-visited uid-pair-setp))
    :short "Check whether either of two @(tsee type-params)
            is already a composite of the two."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee type-params-composite-aux) for the composite rules."))
    (b* ((visited (uid-pair-sfix visited))
         ((when (= (the unsigned-byte (lnfix count)) 0))
          (mv nil nil visited)))
      (type-params-case
        x
        :prototype
        (type-params-case
          y
          :prototype (type-list-composite-is-input-p
                       x.params
                       y.params
                       completions
                       visited
                       (- (the unsigned-byte count) 1))
          :otherwise (mv t nil visited))
        :old-style
        (type-params-case
          y
          :prototype (mv nil t visited)
          :old-style (mv t t visited)
          :unspecified (mv t nil visited))
        :unspecified (mv (type-params-case y :unspecified) t visited)))
    :measure (nfix count))

  (define type-list-composite-is-input-p ((x type-listp)
                                           (y type-listp)
                                           (completions type-completions-p)
                                           (visited uid-pair-setp)
                                           (count natp))
    :returns (mv (leftp booleanp)
                 (rightp booleanp)
                 (new-visited uid-pair-setp))
    :short "Check whether either of two @(tsee type-list)s
            is already a composite of the two."
    (b* ((visited (uid-pair-sfix visited))
         ((when (endp x)) (mv t (endp y) visited))
         ((when (endp y)) (mv nil t visited))
         ((when (= (the unsigned-byte (lnfix count)) 0))
          (mv nil nil visited))
         ((mv leftp rightp visited)
          (type-composite-is-input-p (first x)
                                     (first y)
                                     completions
                                     visited
                                     (- (the unsigned-byte count) 1)))
         ((unless (or leftp rightp)) (mv nil nil visited))
         ((mv rest-leftp rest-rightp visited)
          (type-list-composite-is-input-p (rest x)
                                          (rest y)
                                          completions
                                          visited
                                          (- (the unsigned-byte count) 1))))
      (mv (and leftp rest-leftp)
          (and rightp rest-rightp)
          visited))
    :measure (nfix count))

  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-composite-is-input-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-composite-aux
  (define type-composite-aux ((x typep)
                              (y typep)
                              (composites uid-pair-uid-mapp)
                              (completions type-completions-p)
                              (next-uid uidp)
                              (ienv ienvp)
                              (count natp))
    :returns (mv (composite typep)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Auxiliary function for constructing a composite @(see type)
            [C17:6.2.7/3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee type-composite) for a description type composites.")
     (xdoc::p
      "Before the case analysis,
       @(tsee type-composite-is-input-p) checks whether
       either input already satisfies the requirements of the composite,
       in which case that input is returned.
       The case analysis constructs a composite only otherwise,
       and creates a new struct type,
       with a fresh @(see UID) and an entry in the completions map,
       only when two tagged structs with different UIDs are composed.")
     (xdoc::p
      "The @('composites') map associates
       each pair of struct @(see UID)s whose composite is being constructed
       with the fresh UID of that composite,
       so that the pair, when encountered again through cyclic struct types,
       refers to the composite under construction.")
     (xdoc::p
      "The termination argument for this clique is nontrivial.
       A sufficient measure would be the number of
       pairs of @(see UID)s in the @('completions') map below @('next-uid')
       that are not in the @('composites') map.
       For the moment, we simply add a @('count') argument."))
    (b* ((x (type-fix x))
         (y (type-fix y))
         (completions (type-completions-fix completions))
         (next-uid (uid-fix next-uid))
         ((when (= (the unsigned-byte (lnfix count)) 0))
          (mv x completions next-uid))
         ;; An input that already satisfies the requirements
         ;; of the composite is the composite [C23:6.2.7/4].
         ;; A composite is constructed only otherwise.
         ((mv leftp rightp &)
          (type-composite-is-input-p x
                                     y
                                     completions
                                     (treeset::empty)
                                     (- (the unsigned-byte count) 1)))
         ((when leftp)
          (mv x completions next-uid))
         ((when rightp)
          (mv y completions next-uid)))
      (type-case
        x
        :struct
        (type-case
          y
          :struct
          (if (uid-equal x.uid y.uid)
              (mv (type-fix x)
                  (type-completions-fix completions)
                  (uid-fix next-uid))
            (type-struni-tag/members-case
              x.tag/members
              :tagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (b* ((composites (uid-pair-uid-mfix composites))
                     (completions (type-completions-fix completions))
                     (pair (make-uid-pair :first x.uid :second y.uid))
                     ((mv foundp composite-uid)
                      (treemap::lookup? pair composites))
                     ((when foundp)
                      (mv (make-type-struct
                            :uid composite-uid
                            :tunit? nil
                            :tag/members x.tag/members)
                          completions
                          (uid-fix next-uid)))
                     ((mv x-foundp x-members)
                      (treemap::lookup? x.uid completions))
                     ((mv y-foundp y-members)
                      (treemap::lookup? y.uid completions))
                     ((unless x-foundp)
                      (mv (type-fix y)
                          completions
                          (uid-fix next-uid)))
                     ((unless y-foundp)
                      (mv (type-fix x)
                          completions
                          (uid-fix next-uid)))
                     (composite-uid (uid-fix next-uid))
                     (next-uid (uid-increment next-uid))
                     (composites
                       (treemap::update pair composite-uid composites))
                     ((mv members-composite completions next-uid)
                      (type-struni-member-list-composite-aux
                        x-members
                        y-members
                        composites
                        completions
                        next-uid
                        ienv
                        (- (the unsigned-byte count) 1)))
                     (completions (treemap::update composite-uid
                                                   members-composite
                                                   completions)))
                  (mv (make-type-struct
                        :uid composite-uid
                        :tunit? nil
                        :tag/members x.tag/members)
                      completions
                      next-uid))
                :untagged
                (mv (type-fix x)
                    (type-completions-fix completions)
                    (uid-fix next-uid)))
              :untagged
              (type-struni-tag/members-case
                y.tag/members
                :tagged
                (mv (type-fix x)
                    (type-completions-fix completions)
                    (uid-fix next-uid))
                :untagged
                (b* ((composite-uid next-uid)
                     (next-uid (uid-increment next-uid))
                     ((mv members-composite completions next-uid)
                      (type-struni-member-list-composite-aux
                        x.tag/members.members
                        y.tag/members.members
                        composites
                        completions
                        next-uid
                        ienv
                        (- (the unsigned-byte count) 1))))
                  (mv (make-type-struct
                        :uid composite-uid
                        :tunit? nil
                        :tag/members (type-struni-tag/members-untagged
                                       members-composite))
                      completions
                      next-uid)))))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :unknown-builtin (mv (type-fix x)
                               (type-completions-fix completions)
                               (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :union (mv (type-fix x)
                   (type-completions-fix completions)
                   (uid-fix next-uid))
        :array
        (type-case
          y
          :array (b* (((mv of-type completions next-uid)
                       (type-composite-aux x.of
                                           y.of
                                           composites
                                           completions
                                           next-uid
                                           ienv
                                           (- (the unsigned-byte count) 1)))
                      (kind (type-array-kind-composite x.kind y.kind)))
                   (mv (make-type-array :of of-type :kind kind)
                       completions
                       next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :unknown-builtin (mv (type-fix x)
                               (type-completions-fix completions)
                               (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :pointer
        (type-case
          y
          :pointer (b* (((mv to-type completions next-uid)
                         (type-composite-aux x.to
                                             y.to
                                             composites
                                             completions
                                             next-uid
                                             ienv
                                             (- (the unsigned-byte count) 1))))
                     (mv (make-type-pointer :to to-type)
                         completions
                         next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :unknown-builtin (mv (type-fix x)
                               (type-completions-fix completions)
                               (uid-fix next-uid))
          :unknown-scalar (mv (type-fix x)
                              (type-completions-fix completions)
                              (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :function
        (type-case
          y
          :function
          (b* (((mv ret-type completions next-uid)
                (type-composite-aux x.ret
                                    y.ret
                                    composites
                                    completions
                                    next-uid
                                    ienv
                                    (- (the unsigned-byte count) 1)))
               ((mv params completions next-uid)
                (type-params-composite-aux x.params
                                           y.params
                                           composites
                                           completions
                                           next-uid
                                           ienv
                                           (- (the unsigned-byte count) 1))))
            (mv (make-type-function :ret ret-type :params params)
                completions
                next-uid))
          :unknown (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))
          :unknown-builtin (mv (type-fix x)
                               (type-completions-fix completions)
                               (uid-fix next-uid))
          :otherwise (mv (irr-type)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :unknown (mv (type-fix y)
                     (type-completions-fix completions)
                     (uid-fix next-uid))
        :unknown-builtin (mv (if (type-case y :unknown)
                                   (type-fix x)
                                 (type-fix y))
                               (type-completions-fix completions)
                               (uid-fix next-uid))
        :unknown-scalar (mv (if (type-case y '(:unknown :unknown-builtin))
                                (type-fix x)
                              (type-fix y))
                            (type-completions-fix completions)
                            (uid-fix next-uid))
        :unknown-arithmetic (mv (if (type-case y '(:unknown
                                                   :unknown-builtin
                                                   :unknown-scalar))
                                (type-fix x)
                              (type-fix y))
                                (type-completions-fix completions)
                                (uid-fix next-uid))
        :otherwise (mv (type-fix x)
                       (type-completions-fix completions)
                       (uid-fix next-uid))))
    :measure (nfix count))

    (define type-struni-member-list-composite-aux
      ((x type-struni-member-listp)
       (y type-struni-member-listp)
       (composites uid-pair-uid-mapp)
       (completions type-completions-p)
       (next-uid uidp)
       (ienv ienvp)
       (count natp))
    :returns (mv (composite type-struni-member-listp)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite @(tsee type-struni-member-list)."
    (b* (((when (or (endp x) (endp y) (= (the unsigned-byte (lnfix count)) 0)))
          (mv nil (type-completions-fix completions) (uid-fix next-uid)))
         ((mv first-type completions next-uid)
          (type-composite-aux (type-struni-member->type (first x))
                              (type-struni-member->type (first y))
                              composites
                              completions
                              next-uid
                              ienv
                              (- (the unsigned-byte count) 1)))
         (first-member (change-type-struni-member
                         (first x)
                         :type first-type))
         ((mv rest-members completions next-uid)
          (type-struni-member-list-composite-aux
            (rest x)
            (rest y)
            composites
            completions
            next-uid
            ienv
            (- (the unsigned-byte count) 1))))
      (mv (cons first-member rest-members)
          completions
          next-uid))
    :measure (nfix count))

  (define type-params-composite-aux ((x type-params-p)
                                     (y type-params-p)
                                     (composites uid-pair-uid-mapp)
                                     (completions type-completions-p)
                                     (next-uid uidp)
                                     (ienv ienvp)
                                     (count natp))
    :returns (mv (composite type-params-p)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite of the @(tsee type-params) portion of a
            function @(see type)."
    :long
    (xdoc::topstring
     (xdoc::p
      "If both function types are prototypes,
       the result is a prototype whose parameter lists consists of
       the composite type of each parameter [C17:6.2.7/3].")
     (xdoc::p
      "If one function type is a prototype and the other is not,
       the composite is a prototype with the prototype function type's
       parameter types [C17:6.2.7/3].")
     (xdoc::p
      "If neither function type is a prototype,
       the composite is unconstrained except by the general restriction
       that it is compatible with both function types.
       In this case,
       we arbitrarily choose the function type with more information
       (i.e. an old-style function type)."))
    (if (= (the unsigned-byte (lnfix count)) 0)
        (mv (type-params-fix x)
            (type-completions-fix completions)
            (uid-fix next-uid))
      (type-params-case
        x
        :prototype
        (type-params-case
          y
          :prototype
          (b* (((mv param-types completions next-uid)
                (type-list-composite-aux x.params
                                         y.params
                                         composites
                                         completions
                                         next-uid
                                         ienv
                                         (- (the unsigned-byte count) 1))))
            (mv (make-type-params-prototype
                  :params param-types
                  :ellipsis x.ellipsis)
                completions
                next-uid))
          :otherwise (mv (type-params-fix x)
                         (type-completions-fix completions)
                         (uid-fix next-uid)))
        :old-style (mv (type-params-case
                         y
                         :prototype (type-params-fix y)
                         ;; TODO: we could consider creating a better composite when
                         ;; both are :old-style which could resolve some unknowns.
                         :otherwise (type-params-fix x))
                       (type-completions-fix completions)
                       (uid-fix next-uid))
        :unspecified (mv (type-params-fix y)
                         (type-completions-fix completions)
                         (uid-fix next-uid))))
    :measure (nfix count))

  (define type-list-composite-aux ((x type-listp)
                                   (y type-listp)
                                   (composites uid-pair-uid-mapp)
                                   (completions type-completions-p)
                                   (next-uid uidp)
                                   (ienv ienvp)
                                   (count natp))
    :returns (mv (composite type-listp)
                 (new-completions type-completions-p)
                 (new-next-uid uidp))
    :short "Construct a composite @(tsee type-list)."
    (b* (((when (or (endp x) (endp y) (= (the unsigned-byte (lnfix count)) 0)))
          (mv nil (type-completions-fix completions) (uid-fix next-uid)))
         ((mv first-type completions next-uid)
          (type-composite-aux (first x)
                              (first y)
                              composites
                              completions
                              next-uid
                              ienv
                              (- (the unsigned-byte count) 1)))
         ((mv rest-types completions next-uid)
          (type-list-composite-aux (rest x)
                                   (rest y)
                                   composites
                                   completions
                                   next-uid
                                   ienv
                                   (- (the unsigned-byte count) 1))))
      (mv (cons first-type rest-types)
          completions
          next-uid))
    :measure (nfix count))

  :verify-guards :after-returns
  :flag-local nil
  ///

  (fty::deffixequiv-mutual type/type-list-composite-aux))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-composite ((x typep)
                        (y typep)
                        (completions type-completions-p)
                        (next-uid uidp)
                        (ienv ienvp))
  :returns (mv (composite typep)
               (new-completions type-completions-p)
               (new-next-uid uidp))
  :short "Construct a composite @(see type) [C17:6.2.7/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our approximate type system,
     a composite type is a type that is compatible with both input types,
     which must be compatible with each other
     (we plan to add a guard for that).
     For function types, further constraints apply.
     See @(tsee type-params-composite-aux).")
   (xdoc::p
    "When taking the composite of one of the unknown type variants
     with any other type,
     we take the more specific type as the composite.
     This choice is consistent with the general pattern
     of constraints outlined by the standard
     (e.g., when taking the composite of two arrays,
     one of known constant size and the other of unknown size,
     the composite has the known size
     [C17:6.2.7/3] [C23:6.2.7/3]).")
   (xdoc::p
    "Before constructing a composite,
     we check via @(tsee type-composite-is-input-p)
     whether one of the two types
     already satisfies the requirements of the composite,
     in which case that type is the composite [C23:6.2.7/4].
     This matters for tagged struct types with different @(see UID)s
     (which arise across translation units; see @(tsee type-compatible-3p)),
     which are composed member-wise [C23:6.2.7/3]:
     only when neither type is a composite do we create a new struct type,
     with a fresh UID and with the composite of the members
     recorded in the completions map."))
  (type-composite-aux x
                      y
                      (treemap::empty)
                      completions
                      next-uid
                      ienv
                      (the (unsigned-byte 60) (1- (expt 2 60)))))
