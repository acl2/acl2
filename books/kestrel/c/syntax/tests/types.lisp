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
    (hons-acons
      (uid 42)
      (list (make-type-struni-member :name? (ident "x")
                                     :type (type-char))
            (make-type-struni-member :name? (ident "y")
                                     :type (type-ulong)))
      (hons-acons
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
      (hons-acons
        (uid 42)
        (list (make-type-struni-member :name? (ident "x")
                                       :type (type-char))
              (make-type-struni-member :name? (ident "y")
                                       :type (type-ulong)))
        (hons-acons
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
    (hons-acons
      (uid 42)
      (list (make-type-struni-member :name? (ident "x")
                                     :type (type-char))
            (make-type-struni-member :name? (ident "y")
                                     :type (type-ulong)))
      (hons-acons
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
            (hons-acons
              (uid 42)
              (list (make-type-struni-member :name? (ident "x")
                                             :type (type-char))
                    (make-type-struni-member :name? (ident "y")
                                             :type (type-ulong)))
              (hons-acons
                (uid 43)
                (list (make-type-struni-member :name? (ident "x")
                                               :type (type-char))
                      (make-type-struni-member :name? (ident "y")
                                               :type (type-ulong)))
                nil))
            (uid 44)
            (irr-ienv))
    (and (equal composite
                (make-type-struct :uid (uid 44)
                                  :tunit? nil
                                  :tag/members (type-struni-tag/members-tagged
                                                 (ident "my_struct"))))
         (equal (cdr (hons-get (uid 44) completions))
                (list (make-type-struni-member :name? (ident "x")
                                               :type (type-char))
                      (make-type-struni-member :name? (ident "y")
                                               :type (type-ulong))))
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
            (hons-acons
              (uid 42)
              (list (make-type-struni-member :name? (ident "x")
                                             :type (type-char))
                    (make-type-struni-member :name? (ident "y")
                                             :type (type-ulong)))
              (hons-acons
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
