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

;; Array types

(acl2::assert!
  (mv-let (composite completions next-uid)
          (type-composite
            (make-type-array
              :of (type-unknown)
              :kind (make-type-array-kind-const-len :len nil))
            (make-type-array
              :of (type-sint)
              :kind (make-type-array-kind-const-len :len 10))
            nil
            (uid 42)
            (irr-ienv))
    (and (equal composite
                (make-type-array
                  :of (type-sint)
                  :kind (make-type-array-kind-const-len :len 10)))
         (equal completions nil)
         (equal next-uid (uid 42)))))

;;;;;;;;;;;;;;;;;;;;

;; Struct types

(acl2::assert!
  (mv-let (composite completions next-uid)
          (type-composite
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
            (uid 44)
            (irr-ienv))
    ;; Both types satisfy the requirements of the composite,
    ;; so the first is returned as is, and nothing is created.
    (declare (ignore completions))
    (and (equal composite
                (make-type-struct :uid (uid 42)
                                  :tunit? (filepath "foo.c")
                                  :tag/members (type-struni-tag/members-tagged
                                                 (ident "my_struct"))))
         (equal next-uid
                (uid 44)))))

;; Neither type is a composite of the two
;; (each has a member more specific than the other's),
;; so a new struct type is created with the composite members.
(acl2::assert!
  (mv-let (composite completions next-uid)
          (type-composite
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
              (list (make-type-struni-member
                      :name? (ident "x")
                      :type (make-type-pointer
                              :to (make-type-function
                                    :ret (type-sint)
                                    :params (make-type-params-prototype
                                              :params (list (type-sint))))))
                    (make-type-struni-member
                      :name? (ident "y")
                      :type (make-type-pointer
                              :to (make-type-function
                                    :ret (type-sint)
                                    :params (type-params-unspecified)))))
              (treemap::update
                (uid 43)
                (list (make-type-struni-member
                        :name? (ident "x")
                        :type (make-type-pointer
                                :to (make-type-function
                                      :ret (type-sint)
                                      :params (type-params-unspecified))))
                      (make-type-struni-member
                        :name? (ident "y")
                        :type (make-type-pointer
                                :to (make-type-function
                                      :ret (type-sint)
                                      :params (make-type-params-prototype
                                                :params (list (type-sint)))))))
                nil))
            (uid 44)
            (irr-ienv))
    (and (equal composite
                (make-type-struct :uid (uid 44)
                                  :tunit? nil
                                  :tag/members (type-struni-tag/members-tagged
                                                 (ident "my_struct"))))
         (equal (treemap::lookup (uid 44) completions)
                (list (make-type-struni-member
                        :name? (ident "x")
                        :type (make-type-pointer
                                :to (make-type-function
                                      :ret (type-sint)
                                      :params (make-type-params-prototype
                                                :params (list (type-sint))))))
                      (make-type-struni-member
                        :name? (ident "y")
                        :type (make-type-pointer
                                :to (make-type-function
                                      :ret (type-sint)
                                      :params (make-type-params-prototype
                                                :params (list (type-sint))))))))
         (equal next-uid
                (uid 45)))))

(acl2::assert!
  (mv-let (composite completions next-uid)
          (type-composite
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
            (uid 44)
            (irr-ienv))
    (declare (ignore completions))
    (and (equal composite
                (make-type-struct :uid (uid 42)
                              :tunit? (filepath "foo.c")
                              :tag/members (type-struni-tag/members-tagged
                                             (ident "my_struct"))))
         (equal next-uid
                (uid 44)))))

;; Cyclic struct types across three translation units:
;; the first points to itself, and the second and third point to each other.
;; Composing the first two reaches the pair of the first and third,
;; which reaches the first pair again.
;; Each type is a composite of the two, so the first is returned as is.
(acl2::assert!
  (b* ((tag/members (type-struni-tag/members-tagged (ident "my_struct")))
       (foo (make-type-struct :uid (uid 42)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 43)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (baz (make-type-struct :uid (uid 44)
                              :tunit? (filepath "baz.c")
                              :tag/members tag/members))
       (completions
        (treemap::update
          (uid 42)
          (list (make-type-struni-member :name? (ident "p")
                                         :type (make-type-pointer :to foo)))
          (treemap::update
            (uid 43)
            (list (make-type-struni-member :name? (ident "p")
                                           :type (make-type-pointer :to baz)))
            (treemap::update
              (uid 44)
              (list (make-type-struni-member :name? (ident "p")
                                             :type (make-type-pointer :to bar)))
              nil))))
       ((mv composite & next-uid)
        (type-composite foo bar completions (uid 45) (irr-ienv))))
    (and (equal composite foo)
         (equal next-uid (uid 45)))))

;; As above, but the first two types each have a member
;; more specific than the other's, so neither is a composite of the two:
;; a struct type is created for the first pair,
;; another for the pair of the first and third reached through the members,
;; and the first pair, reached again, refers to its struct type.
(acl2::assert!
  (b* ((tag/members (type-struni-tag/members-tagged (ident "my_struct")))
       (foo (make-type-struct :uid (uid 42)
                              :tunit? (filepath "foo.c")
                              :tag/members tag/members))
       (bar (make-type-struct :uid (uid 43)
                              :tunit? (filepath "bar.c")
                              :tag/members tag/members))
       (baz (make-type-struct :uid (uid 44)
                              :tunit? (filepath "baz.c")
                              :tag/members tag/members))
       (prototype (make-type-pointer
                    :to (make-type-function
                          :ret (type-sint)
                          :params (make-type-params-prototype
                                    :params (list (type-sint))))))
       (unspecified (make-type-pointer
                      :to (make-type-function
                            :ret (type-sint)
                            :params (type-params-unspecified))))
       (f-prototype (make-type-struni-member :name? (ident "f")
                                             :type prototype))
       (f-unspecified (make-type-struni-member :name? (ident "f")
                                               :type unspecified))
       (g-prototype (make-type-struni-member :name? (ident "g")
                                             :type prototype))
       (g-unspecified (make-type-struni-member :name? (ident "g")
                                               :type unspecified))
       (completions
        (treemap::update
          (uid 42)
          (list f-prototype
                g-unspecified
                (make-type-struni-member :name? (ident "p")
                                         :type (make-type-pointer :to foo)))
          (treemap::update
            (uid 43)
            (list f-unspecified
                  g-prototype
                  (make-type-struni-member :name? (ident "p")
                                           :type (make-type-pointer :to baz)))
            (treemap::update
              (uid 44)
              (list f-prototype
                    g-unspecified
                    (make-type-struni-member :name? (ident "p")
                                             :type (make-type-pointer :to bar)))
              nil))))
       ((mv composite completions next-uid)
        (type-composite foo bar completions (uid 45) (irr-ienv)))
       (composite45 (make-type-struct :uid (uid 45)
                                      :tunit? nil
                                      :tag/members tag/members))
       (composite46 (make-type-struct :uid (uid 46)
                                      :tunit? nil
                                      :tag/members tag/members)))
    (and (equal composite composite45)
         (equal (treemap::lookup (uid 45) completions)
                (list f-prototype
                      g-prototype
                      (make-type-struni-member
                        :name? (ident "p")
                        :type (make-type-pointer :to composite46))))
         (equal (treemap::lookup (uid 46) completions)
                (list f-prototype
                      g-unspecified
                      (make-type-struni-member
                        :name? (ident "p")
                        :type (make-type-pointer :to composite45))))
         (equal next-uid (uid 47)))))
