; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../types-compatibility")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compatibility

;;;;;;;;;;;;;;;;;;;;

;; Array types

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    nil
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 20))
    nil
    (irr-ienv))
  nil)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len nil))
    nil
    (irr-ienv))
  :unknown)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-nonconst-len))
    nil
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-unknown-complete))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    nil
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    (make-type-array :of (type-uint)
                     :kind (type-array-kind-incomplete))
    nil
    (irr-ienv))
  nil)

;;;;;;;;;;;;;;;;;;;;

;; Function types

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-unknown)))
                                  :ellipsis t))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))
                                  :ellipsis t))
    nil
    (irr-ienv))
  :unknown)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-unknown)))
                                  :ellipsis t))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))
                                  :ellipsis nil))
    nil
    (irr-ienv))
  nil)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-unknown)))
                                  :ellipsis t))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-old-style
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv))
  nil)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    (make-type-function :ret (type-sint)
                        :params (make-type-params-old-style
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-sint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    (make-type-function :ret (type-sint)
                        :params (make-type-params-old-style
                                  :params (list (type-schar)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-slong)
                                                (make-type-pointer
                                                  :to (type-unknown)))))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-old-style
                                  :params (list (type-schar)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv))
  nil)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-sint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    (make-type-function :ret (type-sint)
                        :params (type-params-unspecified))
    nil
    (irr-ienv))
  t)

;;;;;;;;;;;;;;;;;;;;

;; Struct and union types

(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 42)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (make-type-struct :uid (uid 43)
                      :tunit? (filepath "bar.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (treemap::update
      (uid 42)
      (list (make-type-struni-member :name? (ident "x")
                                     :type (type-char))
            (make-type-struni-member :name? (ident "y")
                                     :type (type-ulong)))
      (treemap::update
        (uid 43)
        (list (make-type-struni-member :name? (ident "x")
                                       :type (type-char))
              (make-type-struni-member :name? (ident "y")
                                       :type (type-ulong)))
        nil))
    (irr-ienv))
  t)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 42)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (make-type-struct :uid (uid 43)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (treemap::update
      (uid 42)
      (list (make-type-struni-member :name? (ident "x")
                                     :type (type-char))
            (make-type-struni-member :name? (ident "y")
                                     :type (type-ulong)))
      (treemap::update
        (uid 43)
        (list (make-type-struni-member :name? (ident "x")
                                       :type (type-char))
              (make-type-struni-member :name? (ident "y")
                                       :type (type-ulong)))
        nil))
    (irr-ienv))
  nil)

(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 42)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (make-type-struct :uid (uid 42)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (treemap::update
      (uid 42)
      (list (make-type-struni-member :name? (ident "x")
                                     :type (type-char))
            (make-type-struni-member :name? (ident "y")
                                     :type (type-ulong)))
      (treemap::update
        (uid 43)
        (list (make-type-struni-member :name? (ident "x")
                                       :type (type-char))
              (make-type-struni-member :name? (ident "y")
                                       :type (type-ulong)))
        nil))
    (irr-ienv))
  t)

;; Untagged structs declared in separate translation units
;; are compatible if their members are [C17:6.2.7/1] [C23:6.2.7/1].
(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 1)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-untagged
                                     (list (make-type-struni-member
                                             :name? (ident "x")
                                             :type (type-sint)))))
    (make-type-struct :uid (uid 2)
                      :tunit? (filepath "bar.c")
                      :tag/members (type-struni-tag/members-untagged
                                     (list (make-type-struni-member
                                             :name? (ident "x")
                                             :type (type-sint)))))
    nil
    (irr-ienv))
  t)

;; Untagged structs declared in the same translation unit are distinct types.
(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 1)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-untagged
                                     (list (make-type-struni-member
                                             :name? (ident "x")
                                             :type (type-sint)))))
    (make-type-struct :uid (uid 2)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-untagged
                                     (list (make-type-struni-member
                                             :name? (ident "x")
                                             :type (type-sint)))))
    nil
    (irr-ienv))
  nil)

;; A tagged struct that is incomplete in its translation unit
;; is compatible with a complete one with the same tag.
(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 1)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (make-type-struct :uid (uid 2)
                      :tunit? (filepath "bar.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (treemap::update (uid 1)
                     (list (make-type-struni-member :name? (ident "x")
                                                    :type (type-sint)))
                     nil)
    (irr-ienv))
  t)

;; A member of unknown type makes the answer unknown.
(acl2::assert-equal
  (type-compatible-3p
    (make-type-struct :uid (uid 1)
                      :tunit? (filepath "foo.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (make-type-struct :uid (uid 2)
                      :tunit? (filepath "bar.c")
                      :tag/members (type-struni-tag/members-tagged
                                     (ident "my_struct")))
    (treemap::update (uid 1)
                     (list (make-type-struni-member :name? (ident "x")
                                                    :type (type-sint)))
                     (treemap::update (uid 2)
                                      (list (make-type-struni-member
                                              :name? (ident "x")
                                              :type (type-unknown)))
                                      nil))
    (irr-ienv))
  :unknown)

;; Cyclic struct types across three translation units:
;; the first points to itself, and the second and third point to each other.
;; The pair of the first two is reached again through the members,
;; where it is assumed compatible.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "my_struct")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (baz (make-type-struct :uid (uid 3)
                              :tunit? (filepath "baz.c")
                              :tag/members tag/members))
       (completions
        (treemap::update
          (uid 1)
          (list (make-type-struni-member :name? (ident "p")
                                         :type (make-type-pointer :to foo)))
          (treemap::update
            (uid 2)
            (list (make-type-struni-member :name? (ident "p")
                                           :type (make-type-pointer :to baz)))
            (treemap::update
              (uid 3)
              (list (make-type-struni-member :name? (ident "p")
                                             :type (make-type-pointer :to bar)))
              nil)))))
    (type-compatible-3p foo bar completions (irr-ienv)))
  t)

;; The struct type of one translation unit points to itself,
;; while a block-scope struct type of another translation unit
;; points, through a typedef, to the file-scope struct type with the same tag,
;; whose members differ.
;; The pair of the first and the file-scope type is not the pair being assumed,
;; so it is compared, and found incompatible.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "my_struct")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar-file (make-type-struct :uid (uid 2)
                                   :tunit? (filepath "bar.c")
                                   :tag/members tag/members))
       (bar-block (make-type-struct :uid (uid 3)
                                    :tunit? (filepath "bar.c")
                                    :tag/members tag/members))
       (completions
        (treemap::update
          (uid 1)
          (list (make-type-struni-member :name? (ident "p")
                                         :type (make-type-pointer :to foo)))
          (treemap::update
            (uid 2)
            (list (make-type-struni-member :name? (ident "x")
                                           :type (type-sint)))
            (treemap::update
              (uid 3)
              (list (make-type-struni-member
                      :name? (ident "p")
                      :type (make-type-pointer :to bar-file)))
              nil)))))
    (type-compatible-3p foo bar-block completions (irr-ienv)))
  nil)

;; Complete unions with the same tag in separate translation units
;; are compatible if their members correspond in some order,
;; which is not checked yet.
(acl2::assert-equal
  (type-compatible-3p
    (make-type-union :uid (uid 1)
                     :tunit? (filepath "foo.c")
                     :tag/members (type-struni-tag/members-tagged
                                    (ident "my_union")))
    (make-type-union :uid (uid 2)
                     :tunit? (filepath "bar.c")
                     :tag/members (type-struni-tag/members-tagged
                                    (ident "my_union")))
    (treemap::update (uid 1)
                     (list (make-type-struni-member :name? (ident "x")
                                                    :type (type-sint)))
                     (treemap::update (uid 2)
                                      (list (make-type-struni-member
                                              :name? (ident "x")
                                              :type (type-sint)))
                                      nil))
    (irr-ienv))
  :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Composite relation

;;;;;;;;;;;;;;;;;;;;

;; Array types

;; An array of known size is the composite with an incomplete array.
(acl2::assert-equal
  (type-composite-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    nil
    (irr-ienv))
  t)

;; The incomplete array is not.
(acl2::assert-equal
  (type-composite-3p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    nil
    (irr-ienv))
  nil)

;; A variable length array may have an unevaluated size expression,
;; in which case the behavior is undefined.
(acl2::assert-equal
  (type-composite-3p
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-nonconst-len))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-nonconst-len))
    nil
    (irr-ienv))
  :unknown)

;;;;;;;;;;;;;;;;;;;;

;; Function types

;; The composite with a prototype has that parameter list.
(acl2::assert-equal
  (b* ((proto (make-type-function
                :ret (type-sint)
                :params (make-type-params-prototype
                          :params (list (type-sint))
                          :ellipsis nil)))
       (unspec (make-type-function
                 :ret (type-sint)
                 :params (type-params-unspecified))))
    (list (type-composite-3p proto unspec proto nil (irr-ienv))
          (type-composite-3p proto unspec unspec nil (irr-ienv))))
  (list t nil))

;; Parameters are composed.
(acl2::assert-equal
  (b* ((array-inc (make-type-pointer
                    :to (make-type-array
                          :of (type-sint)
                          :kind (type-array-kind-incomplete))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10))))
       (f-inc (make-type-function
                :ret (type-sint)
                :params (make-type-params-prototype
                          :params (list array-inc)
                          :ellipsis nil)))
       (f-10 (make-type-function
               :ret (type-sint)
               :params (make-type-params-prototype
                         :params (list array-10)
                         :ellipsis nil))))
    (list (type-composite-3p f-inc f-10 f-10 nil (irr-ienv))
          (type-composite-3p f-inc f-10 f-inc nil (irr-ienv))))
  (list t nil))

;; In C23, the composite of a type with itself is that type;
;; C17 requires only compatibility.
(acl2::assert-equal
  (b* ((proto (make-type-function
                :ret (type-sint)
                :params (make-type-params-prototype
                          :params (list (type-sint))
                          :ellipsis nil)))
       (unspec (make-type-function
                 :ret (type-sint)
                 :params (type-params-unspecified)))
       (c23 (change-ienv (irr-ienv)
                         :dialect (c::make-dialect
                                    :std (c::standard-c23)))))
    (list (type-composite-3p unspec unspec proto nil (irr-ienv))
          (type-composite-3p unspec unspec proto nil c23)))
  (list t nil))

;;;;;;;;;;;;;;;;;;;;

;; Enumerated types

;; In C23, two enumerated types compose to an enumerated type;
;; in C17, the composite may also be an integer type,
;; but we cannot tell which.
(acl2::assert-equal
  (b* ((c23 (change-ienv (irr-ienv)
                         :dialect (c::make-dialect
                                    :std (c::standard-c23)))))
    (list (type-composite-3p (type-enum) (type-enum) (type-sint) nil (irr-ienv))
          (type-composite-3p (type-enum) (type-enum) (type-sint) nil c23)))
  (list :unknown nil))

;;;;;;;;;;;;;;;;;;;;

;; Structure and union types

;; Complete structs across translation units compose member-wise;
;; the composite must be complete.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (composite (make-type-struct :uid (uid 3)
                                    :tunit? nil
                                    :tag/members tag/members))
       (member-inc (make-type-struni-member
                     :name? (ident "p")
                     :type (make-type-pointer
                             :to (make-type-array
                                   :of (type-sint)
                                   :kind (type-array-kind-incomplete)))))
       (member-10 (make-type-struni-member
                    :name? (ident "p")
                    :type (make-type-pointer
                            :to (make-type-array
                                  :of (type-sint)
                                  :kind (make-type-array-kind-const-len
                                          :len 10)))))
       (completions (treemap::update (uid 1) (list member-inc)
                                     (treemap::update (uid 2) (list member-10)
                                                      nil))))
    (list (type-composite-3p
            foo bar composite
            (treemap::update (uid 3) (list member-10) completions)
            (irr-ienv))
          (type-composite-3p
            foo bar composite
            (treemap::update (uid 3) (list member-inc) completions)
            (irr-ienv))
          (type-composite-3p foo bar composite completions (irr-ienv))
          ;; The second input already satisfies the conditions.
          (type-composite-3p foo bar bar completions (irr-ienv))
          (type-composite-3p foo bar foo completions (irr-ienv))))
  (list t nil nil t nil))

;; With exactly one complete input, the composite has its members;
;; with none, the composite is incomplete.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (composite (make-type-struct :uid (uid 3)
                                    :tunit? nil
                                    :tag/members tag/members))
       (members (list (make-type-struni-member :name? (ident "x")
                                               :type (type-sint)))))
    (list (type-composite-3p
            foo bar composite
            (treemap::update (uid 1) members
                             (treemap::update (uid 3) members nil))
            (irr-ienv))
          (type-composite-3p
            foo bar composite
            (treemap::update (uid 1) members nil)
            (irr-ienv))
          (type-composite-3p foo bar composite nil (irr-ienv))
          (type-composite-3p
            foo bar composite
            (treemap::update (uid 3) members nil)
            (irr-ienv))))
  (list t nil t nil))

;; Cyclic struct types: the composite may point to itself,
;; and an input may be the composite.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (composite (make-type-struct :uid (uid 3)
                                    :tunit? nil
                                    :tag/members tag/members))
       (completions
        (treemap::update
          (uid 1)
          (list (make-type-struni-member :name? (ident "p")
                                         :type (make-type-pointer :to foo)))
          (treemap::update
            (uid 2)
            (list (make-type-struni-member :name? (ident "p")
                                           :type (make-type-pointer :to bar)))
            (treemap::update
              (uid 3)
              (list (make-type-struni-member
                      :name? (ident "p")
                      :type (make-type-pointer :to composite)))
              nil)))))
    (list (type-composite-3p foo bar composite completions (irr-ienv))
          (type-composite-3p foo bar foo completions (irr-ienv))))
  (list t t))

;; In C23, the composite of a struct type with itself is that type,
;; not another compatible one.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (members (list (make-type-struni-member :name? (ident "x")
                                               :type (type-sint))))
       (completions (treemap::update (uid 1) members
                                     (treemap::update (uid 2) members nil)))
       (c23 (change-ienv (irr-ienv)
                         :dialect (c::make-dialect
                                    :std (c::standard-c23)))))
    (list (type-composite-3p foo foo bar completions (irr-ienv))
          (type-composite-3p foo foo bar completions c23)))
  (list t nil))

;; Complete unions are not matched member-wise yet.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "u")))
       (foo (make-type-union :uid (uid 1)
                             :tunit? (filepath "foo.c")
                             :tag/members tag/members))
       (bar (make-type-union :uid (uid 2)
                             :tunit? (filepath "bar.c")
                             :tag/members tag/members))
       (composite (make-type-union :uid (uid 3)
                                   :tunit? nil
                                   :tag/members tag/members))
       (members (list (make-type-struni-member :name? (ident "x")
                                               :type (type-sint)))))
    (type-composite-3p
      foo bar composite
      (treemap::update (uid 1) members
                       (treemap::update (uid 2) members
                                        (treemap::update (uid 3) members
                                                         nil)))
      (irr-ienv)))
  :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Composites

;;;;;;;;;;;;;;;;;;;;

;; Array kinds

(acl2::assert-equal
  (type-array-kind-composite
    (make-type-array-kind-const-len :len 10)
    (make-type-array-kind-const-len :len nil))
  (make-type-array-kind-const-len :len 10))

(acl2::assert-equal
  (type-array-kind-composite
    (make-type-array-kind-const-len :len 10)
    (type-array-kind-nonconst-len))
  (make-type-array-kind-const-len :len 10))

(acl2::assert-equal
  (type-array-kind-composite
    (make-type-array-kind-const-len :len 10)
    (type-array-kind-unknown-complete))
  (make-type-array-kind-const-len :len 10))

(acl2::assert-equal
  (type-array-kind-composite
    (make-type-array-kind-const-len :len 10)
    (type-array-kind-incomplete))
  (make-type-array-kind-const-len :len 10))

(acl2::assert-equal
  (type-array-kind-composite
    (type-array-kind-nonconst-len)
    (type-array-kind-incomplete))
  (type-array-kind-nonconst-len))

(acl2::assert-equal
  (type-array-kind-composite
    (type-array-kind-nonconst-len)
    (type-array-kind-unknown-complete))
  (type-array-kind-unknown-complete))

(acl2::assert-equal
  (type-array-kind-composite
    (type-array-kind-unknown-complete)
    (type-array-kind-incomplete))
  (type-array-kind-unknown-complete))

(acl2::assert-equal
  (type-array-kind-composite
    (type-array-kind-incomplete)
    (type-array-kind-incomplete))
  (type-array-kind-incomplete))

;;;;;;;;;;;;;;;;;;;;

;; The composite of two types, constructed from an empty composites map,
;; along with the composite relation on it.
(define type-composite-and-relation ((x typep) (y typep) (ienv ienvp))
  (b* (((mv composite completions & &)
        (type-composite x y nil (treemap::empty) (uid 1))))
    (list composite
          (type-composite-3p x y composite completions ienv))))

;;;;;;;;;;;;;;;;;;;;

;; Array types

;; The array of known size is the composite with an incomplete array,
;; in either order.
(acl2::assert-equal
  (b* ((array-10 (make-type-array
                   :of (type-sint)
                   :kind (make-type-array-kind-const-len :len 10)))
       (array-inc (make-type-array
                    :of (type-sint)
                    :kind (type-array-kind-incomplete))))
    (list (type-composite-and-relation array-10 array-inc (irr-ienv))
          (type-composite-and-relation array-inc array-10 (irr-ienv))))
  (let ((array-10 (make-type-array
                    :of (type-sint)
                    :kind (make-type-array-kind-const-len :len 10))))
    (list (list array-10 t)
          (list array-10 t))))

;; A variable length array is the composite with an incomplete array,
;; although the relation cannot tell, as its size may be unevaluated.
(acl2::assert-equal
  (type-composite-and-relation
    (make-type-array :of (type-sint) :kind (type-array-kind-nonconst-len))
    (make-type-array :of (type-sint) :kind (type-array-kind-incomplete))
    (irr-ienv))
  (list (make-type-array :of (type-sint) :kind (type-array-kind-nonconst-len))
        :unknown))

;;;;;;;;;;;;;;;;;;;;

;; Pointer types

;; The referenced types are composed.
(acl2::assert-equal
  (type-composite-and-relation
    (make-type-pointer :to (make-type-array
                             :of (type-sint)
                             :kind (type-array-kind-incomplete)))
    (make-type-pointer :to (make-type-array
                             :of (type-sint)
                             :kind (make-type-array-kind-const-len :len 10)))
    (irr-ienv))
  (list (make-type-pointer :to (make-type-array
                                 :of (type-sint)
                                 :kind (make-type-array-kind-const-len
                                         :len 10)))
        t))

;;;;;;;;;;;;;;;;;;;;

;; Function types

;; The prototype is the composite with an unspecified or old-style
;; parameter list, in either order.
(acl2::assert-equal
  (b* ((proto (make-type-function
                :ret (type-sint)
                :params (make-type-params-prototype
                          :params (list (type-sint))
                          :ellipsis nil)))
       (unspec (make-type-function
                 :ret (type-sint)
                 :params (type-params-unspecified)))
       (old (make-type-function
              :ret (type-sint)
              :params (make-type-params-old-style
                        :params (list (type-sint))))))
    (list (type-composite-and-relation proto unspec (irr-ienv))
          (type-composite-and-relation unspec proto (irr-ienv))
          (type-composite-and-relation proto old (irr-ienv))
          (type-composite-and-relation old proto (irr-ienv))))
  (let ((proto (make-type-function
                 :ret (type-sint)
                 :params (make-type-params-prototype
                           :params (list (type-sint))
                           :ellipsis nil))))
    (list (list proto t)
          (list proto t)
          (list proto t)
          (list proto t))))

;; Either an old-style or an unspecified parameter list is a composite
;; of the two; the old-style list is constructed, as the more specific.
(acl2::assert-equal
  (b* ((unspec (make-type-function
                 :ret (type-sint)
                 :params (type-params-unspecified)))
       (old (make-type-function
              :ret (type-sint)
              :params (make-type-params-old-style
                        :params (list (type-sint))))))
    (list (type-composite-3p old unspec unspec nil (irr-ienv))
          (type-composite-and-relation old unspec (irr-ienv))
          (type-composite-and-relation unspec old (irr-ienv))))
  (let ((old (make-type-function
               :ret (type-sint)
               :params (make-type-params-old-style
                         :params (list (type-sint))))))
    (list t
          (list old t)
          (list old t))))

;; Parameters are composed.
(acl2::assert-equal
  (b* ((array-inc (make-type-pointer
                    :to (make-type-array
                          :of (type-sint)
                          :kind (type-array-kind-incomplete))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10))))
       (f-inc (make-type-function
                :ret (type-sint)
                :params (make-type-params-prototype
                          :params (list array-inc)
                          :ellipsis nil)))
       (f-10 (make-type-function
               :ret (type-sint)
               :params (make-type-params-prototype
                         :params (list array-10)
                         :ellipsis nil))))
    (type-composite-and-relation f-inc f-10 (irr-ienv)))
  (list (make-type-function
          :ret (type-sint)
          :params (make-type-params-prototype
                    :params (list (make-type-pointer
                                    :to (make-type-array
                                          :of (type-sint)
                                          :kind (make-type-array-kind-const-len
                                                  :len 10))))
                    :ellipsis nil))
        t))

;; An unknown parameter type is refined by the other function's;
;; the relation cannot confirm the result.
(acl2::assert-equal
  (type-composite-and-relation
    (make-type-function
      :ret (type-sint)
      :params (make-type-params-prototype
                :params (list (type-unknown) (type-sint))
                :ellipsis nil))
    (make-type-function
      :ret (type-sint)
      :params (make-type-params-prototype
                :params (list (type-sint) (type-unknown))
                :ellipsis nil))
    (irr-ienv))
  (list (make-type-function
          :ret (type-sint)
          :params (make-type-params-prototype
                    :params (list (type-sint) (type-sint))
                    :ellipsis nil))
        :unknown))

;;;;;;;;;;;;;;;;;;;;

;; Enumerated types

;; The enumerated type is the composite with an integer type,
;; in either order; the relation cannot confirm it,
;; as the underlying type is unknown.
(acl2::assert-equal
  (list (type-composite-and-relation (type-enum) (type-sint) (irr-ienv))
        (type-composite-and-relation (type-sint) (type-enum) (irr-ienv)))
  (list (list (type-enum) :unknown)
        (list (type-enum) :unknown)))

;;;;;;;;;;;;;;;;;;;;

;; Unknown types

;; The more specific type is the composite with a less specific unknown type,
;; in either order; the relation cannot confirm it.
(acl2::assert-equal
  (list (type-composite-and-relation
          (type-unknown-scalar) (type-sint) (irr-ienv))
        (type-composite-and-relation
          (type-sint) (type-unknown-scalar) (irr-ienv))
        (type-composite-and-relation
          (type-unknown) (type-unknown-arithmetic) (irr-ienv)))
  (list (list (type-sint) :unknown)
        (list (type-sint) :unknown)
        (list (type-unknown-arithmetic) :unknown)))

;;;;;;;;;;;;;;;;;;;;

;; Structure and union types

;; Complete structs across translation units
;; whose members are not composites of each other
;; compose member-wise into a new structure type,
;; which is completed and recorded for the pair of inputs.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (array-inc (make-type-pointer
                    :to (make-type-array
                          :of (type-sint)
                          :kind (type-array-kind-incomplete))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10))))
       (completions
        (treemap::update
          (uid 1)
          (list (make-type-struni-member :name? (ident "p") :type array-inc)
                (make-type-struni-member :name? (ident "q") :type array-10))
          (treemap::update
            (uid 2)
            (list (make-type-struni-member :name? (ident "p") :type array-10)
                  (make-type-struni-member :name? (ident "q") :type array-inc))
            nil)))
       ((mv composite completions composites next-uid)
        (type-composite foo bar completions (treemap::empty) (uid 3))))
    (list composite
          (treemap::lookup (uid 3) completions)
          (treemap::lookup (make-uid-pair :first (uid 1) :second (uid 2))
                           composites)
          next-uid
          (type-composite-3p foo bar composite completions (irr-ienv))))
  (b* ((array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10)))))
    (list (make-type-struct :uid (uid 3)
                            :tunit? nil
                            :tag/members (type-struni-tag/members-tagged
                                           (ident "s")))
          (list (make-type-struni-member :name? (ident "p") :type array-10)
                (make-type-struni-member :name? (ident "q") :type array-10))
          (uid 3)
          (uid 4)
          t)))

;; An input whose members are the composites is the composite itself,
;; in either order; nothing is built.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (member-inc (make-type-struni-member
                     :name? (ident "p")
                     :type (make-type-pointer
                             :to (make-type-array
                                   :of (type-sint)
                                   :kind (type-array-kind-incomplete)))))
       (member-10 (make-type-struni-member
                    :name? (ident "p")
                    :type (make-type-pointer
                            :to (make-type-array
                                  :of (type-sint)
                                  :kind (make-type-array-kind-const-len
                                          :len 10)))))
       (completions (treemap::update (uid 1) (list member-inc)
                                     (treemap::update (uid 2) (list member-10)
                                                      nil)))
       ((mv composite1 & & next-uid1)
        (type-composite foo bar completions (treemap::empty) (uid 3)))
       ((mv composite2 & & next-uid2)
        (type-composite bar foo completions (treemap::empty) (uid 3))))
    (list composite1 next-uid1 composite2 next-uid2))
  (let ((bar (make-type-struct :uid (uid 2)
                               :tunit? (filepath "bar.c")
                               :tag/members (type-struni-tag/members-tagged
                                              (ident "s")))))
    (list bar (uid 3) bar (uid 3))))

;; With exactly one complete input, the composite is that input.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (member (make-type-struni-member :name? (ident "x") :type (type-sint)))
       (completions (treemap::update (uid 1) (list member) nil))
       ((mv composite1 & & &)
        (type-composite foo bar completions (treemap::empty) (uid 3)))
       ((mv composite2 & & &)
        (type-composite bar foo completions (treemap::empty) (uid 3))))
    (list composite1 composite2))
  (let ((foo (make-type-struct :uid (uid 1)
                               :tunit? (filepath "foo.c")
                               :tag/members (type-struni-tag/members-tagged
                                              (ident "s")))))
    (list foo foo)))

;; The composite of cyclic struct types points to itself:
;; the pair of inputs is recorded before the members are composed,
;; so that it is found when reached again through the members,
;; however many times.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "s")))
       (foo (make-type-struct :uid (uid 1)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 2)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (array-inc (make-type-pointer
                    :to (make-type-array
                          :of (type-sint)
                          :kind (type-array-kind-incomplete))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10))))
       (completions
        (treemap::update
          (uid 1)
          (list (make-type-struni-member :name? (ident "prev")
                                         :type (make-type-pointer :to foo))
                (make-type-struni-member :name? (ident "next")
                                         :type (make-type-pointer :to foo))
                (make-type-struni-member :name? (ident "p") :type array-inc)
                (make-type-struni-member :name? (ident "q") :type array-10))
          (treemap::update
            (uid 2)
            (list (make-type-struni-member :name? (ident "prev")
                                           :type (make-type-pointer :to bar))
                  (make-type-struni-member :name? (ident "next")
                                           :type (make-type-pointer :to bar))
                  (make-type-struni-member :name? (ident "p") :type array-10)
                  (make-type-struni-member :name? (ident "q") :type array-inc))
            nil)))
       ((mv composite completions & next-uid)
        (type-composite foo bar completions (treemap::empty) (uid 3))))
    (list (treemap::lookup (uid 3) completions)
          next-uid
          (type-composite-3p foo bar composite completions (irr-ienv))))
  (b* ((composite (make-type-struct :uid (uid 3)
                                    :tunit? nil
                                    :tag/members
                                    (type-struni-tag/members-tagged
                                      (ident "s"))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10)))))
    (list (list (make-type-struni-member
                  :name? (ident "prev")
                  :type (make-type-pointer :to composite))
                (make-type-struni-member
                  :name? (ident "next")
                  :type (make-type-pointer :to composite))
                (make-type-struni-member :name? (ident "p") :type array-10)
                (make-type-struni-member :name? (ident "q") :type array-10))
          (uid 4)
          t)))

;; Untagged structs across translation units compose
;; into a new untagged structure type with the composite members,
;; which needs no completion.
(acl2::assert-equal
  (b* ((array-inc (make-type-pointer
                    :to (make-type-array
                          :of (type-sint)
                          :kind (type-array-kind-incomplete))))
       (array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10))))
       (foo (make-type-struct
              :uid (uid 1)
              :tunit? (filepath "foo.c")
              :tag/members
              (type-struni-tag/members-untagged
                (list (make-type-struni-member :name? (ident "p")
                                               :type array-inc)
                      (make-type-struni-member :name? (ident "q")
                                               :type array-10)))))
       (bar (make-type-struct
              :uid (uid 2)
              :tunit? (filepath "bar.c")
              :tag/members
              (type-struni-tag/members-untagged
                (list (make-type-struni-member :name? (ident "p")
                                               :type array-10)
                      (make-type-struni-member :name? (ident "q")
                                               :type array-inc)))))
       ((mv composite completions & next-uid)
        (type-composite foo bar nil (treemap::empty) (uid 3))))
    (list composite
          completions
          next-uid
          (type-composite-3p foo bar composite completions (irr-ienv))))
  (b* ((array-10 (make-type-pointer
                   :to (make-type-array
                         :of (type-sint)
                         :kind (make-type-array-kind-const-len :len 10)))))
    (list (make-type-struct
            :uid (uid 3)
            :tunit? nil
            :tag/members
            (type-struni-tag/members-untagged
              (list (make-type-struni-member :name? (ident "p")
                                             :type array-10)
                    (make-type-struni-member :name? (ident "q")
                                             :type array-10))))
          nil
          (uid 4)
          t)))

;; Complete unions are not composed yet, and the first input is returned;
;; with exactly one complete input, the composite is that input.
(acl2::assert-equal
  (b* ((tag/members (type-struni-tag/members-tagged (ident "u")))
       (foo (make-type-union :uid (uid 1)
                             :tunit? (filepath "foo.c")
                             :tag/members tag/members))
       (bar (make-type-union :uid (uid 2)
                             :tunit? (filepath "bar.c")
                             :tag/members tag/members))
       (member-inc (make-type-struni-member
                     :name? (ident "p")
                     :type (make-type-pointer
                             :to (make-type-array
                                   :of (type-sint)
                                   :kind (type-array-kind-incomplete)))))
       (member-10 (make-type-struni-member
                    :name? (ident "p")
                    :type (make-type-pointer
                            :to (make-type-array
                                  :of (type-sint)
                                  :kind (make-type-array-kind-const-len
                                          :len 10)))))
       (completions (treemap::update (uid 1) (list member-inc)
                                     (treemap::update (uid 2) (list member-10)
                                                      nil)))
       ((mv composite1 & & &)
        (type-composite foo bar completions (treemap::empty) (uid 3)))
       ((mv composite2 & & &)
        (type-composite foo bar (treemap::update (uid 2) (list member-10) nil)
                        (treemap::empty) (uid 3))))
    (list composite1
          (type-composite-3p foo bar composite1 completions (irr-ienv))
          composite2))
  (b* ((tag/members (type-struni-tag/members-tagged (ident "u")))
       (foo (make-type-union :uid (uid 1)
                             :tunit? (filepath "foo.c")
                             :tag/members tag/members))
       (bar (make-type-union :uid (uid 2)
                             :tunit? (filepath "bar.c")
                             :tag/members tag/members)))
    (list foo :unknown bar)))

;;;;;;;;;;;;;;;;;;;;

;; Same types

;; A type is the composite with itself,
;; even when the relation cannot tell.
(acl2::assert-equal
  (list (type-composite-and-relation (type-sint) (type-sint) (irr-ienv))
        (type-composite-and-relation
          (make-type-array :of (type-sint)
                           :kind (type-array-kind-nonconst-len))
          (make-type-array :of (type-sint)
                           :kind (type-array-kind-nonconst-len))
          (irr-ienv)))
  (list (list (type-sint) t)
        (list (make-type-array :of (type-sint)
                               :kind (type-array-kind-nonconst-len))
              :unknown)))

;; Without struct or union types, the composites map is unchanged
;; and no UIDs are minted.
(acl2::assert-equal
  (b* (((mv & & composites next-uid)
        (type-composite
          (make-type-array :of (type-sint)
                           :kind (type-array-kind-incomplete))
          (make-type-array :of (type-sint)
                           :kind (make-type-array-kind-const-len :len 10))
          nil (treemap::empty) (uid 1))))
    (list composites next-uid))
  (list (treemap::empty) (uid 1)))
