; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../types")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compatibility

;;;;;;;;;;;;;;;;;;;;

;; Array types

(acl2::assert!
  (type-compatible-p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    nil
    (irr-ienv)))

(acl2::assert!
  (not
    (type-compatible-p
      (make-type-array :of (type-sint)
                       :kind (make-type-array-kind-const-len :len 10))
      (make-type-array :of (type-sint)
                       :kind (make-type-array-kind-const-len :len 20))
      nil
      (irr-ienv))))

(acl2::assert!
  (type-compatible-p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len nil))
    nil
    (irr-ienv)))

(acl2::assert!
  (type-compatible-p
    (make-type-array :of (type-sint)
                     :kind (make-type-array-kind-const-len :len 10))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-nonconst-len))
    nil
    (irr-ienv)))

(acl2::assert!
  (type-compatible-p
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-unknown-complete))
    (make-type-array :of (type-sint)
                     :kind (type-array-kind-incomplete))
    nil
    (irr-ienv)))

(acl2::assert!
  (not
    (type-compatible-p
      (make-type-array :of (type-sint)
                       :kind (type-array-kind-incomplete))
      (make-type-array :of (type-uint)
                       :kind (type-array-kind-incomplete))
      nil
      (irr-ienv))))

;;;;;;;;;;;;;;;;;;;;

;; Function types

(acl2::assert!
  (type-compatible-p
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
    (irr-ienv)))

(acl2::assert!
  (not
    (type-compatible-p
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
      (irr-ienv))))

(acl2::assert!
  (not
    (type-compatible-p
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
      (irr-ienv))))

(acl2::assert!
  (type-compatible-p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-unknown)))))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-old-style
                                  :params (list (type-uint)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv)))

(acl2::assert!
  (type-compatible-p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-sint)
                                                (make-type-pointer
                                                  :to (type-unknown)))))
    (make-type-function :ret (type-unknown)
                        :params (make-type-params-old-style
                                  :params (list (type-schar)
                                                (make-type-pointer
                                                  :to (type-ldoublec)))))
    nil
    (irr-ienv)))

(acl2::assert!
  (not
    (type-compatible-p
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
      (irr-ienv))))

(acl2::assert!
  (type-compatible-p
    (make-type-function :ret (type-sint)
                        :params (make-type-params-prototype
                                  :params (list (type-sint)
                                                (make-type-pointer
                                                  :to (type-unknown)))))
    (make-type-function :ret (type-unknown)
                        :params (type-params-unspecified))
    nil
    (irr-ienv)))

;;;;;;;;;;;;;;;;;;;;

;; Struct types

(acl2::assert!
  (type-compatible-p
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
    (irr-ienv)))

(acl2::assert!
  (not
    (type-compatible-p
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
      (irr-ienv))))

(acl2::assert!
  (type-compatible-p
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
    (irr-ienv)))

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
