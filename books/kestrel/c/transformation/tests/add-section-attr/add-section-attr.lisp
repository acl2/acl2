; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../add-section-attr")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list (cons (external-ident (ident "foo"))
                                       "my_section")))

  (c$::output-files :const *new*
                    :path "new")

  ;; To see the section in the `.o` file, you can do:
  ;;   readelf -S test.o
  (assert-file-contents
    :file "new/test1.c"
    :content "__attribute__ ((section(\"my_section\"))) int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test2.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list (cons (external-ident (ident "foo"))
                                       "my_section")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "__attribute__ ((section(\"my_section\"))) int foo(int y, int z);

__attribute__ ((section(\"my_section\"))) __attribute__ ((noinline)) int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test3.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list (cons (external-ident (ident "bar"))
                                       "my_section")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "typedef int my_fn_t(int y, int z);

my_fn_t foo;

__attribute__ ((section(\"my_section\"))) my_fn_t bar;

my_fn_t baz;

__attribute__ ((section(\"my_section\"))) int bar(int y, int z) {
  int x = 5;
  return x + y - z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("internal-foo.c" "external-foo.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list
                             (cons (qualified-ident (filepath "internal-foo.c")
                                                    (ident "foo"))
                                   "internal_foo_section")
                             (cons (external-ident (ident "foo"))
                                   "external_foo_section")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/internal-foo.c"
    :content "__attribute__ ((section(\"internal_foo_section\"))) static int foo = 0;

int internal_foo(void) {
  return foo;
}

__attribute__ ((section(\"internal_foo_section\"))) extern int foo;
")

(assert-file-contents
    :file "new/external-foo.c"
    :content "__attribute__ ((section(\"external_foo_section\"))) int foo;

int internal_foo(void);

int main(void) {
  foo = 42;
  return internal_foo();
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("internal-foo.c" "external-foo.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list
                             (cons (qualified-ident (filepath "internal-foo.c")
                                                    (ident "foo"))
                                   "internal_foo_section")
                             (cons (qualified-ident (filepath "external-foo.c")
                                                    (ident "foo"))
                                   "external_foo_section")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/internal-foo.c"
    :content "__attribute__ ((section(\"internal_foo_section\"))) static int foo = 0;

int internal_foo(void) {
  return foo;
}

__attribute__ ((section(\"internal_foo_section\"))) extern int foo;
")

(assert-file-contents
    :file "new/external-foo.c"
    :content "__attribute__ ((section(\"external_foo_section\"))) int foo;

int internal_foo(void);

int main(void) {
  foo = 42;
  return internal_foo();
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("internal-foo.c" "external-foo.c")
                   :const *old*
                   :ienv (c$::ienv-default :extensions :gcc))

  (add-section-attr *old*
                    *new*
                    :attrs (list
                             (cons (qualified-ident (filepath "external-foo.c")
                                                    (ident "main"))
                                   "sec0")
                             (cons (qualified-ident (filepath "external-foo.c")
                                                    (ident "internal_foo"))
                                   "sec1")
                             (cons (qualified-ident (filepath "internal-foo.c")
                                                    (ident "foo"))
                                   "sec2")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/internal-foo.c"
    :content "__attribute__ ((section(\"sec2\"))) static int foo = 0;

__attribute__ ((section(\"sec1\"))) int internal_foo(void) {
  return foo;
}

__attribute__ ((section(\"sec2\"))) extern int foo;
")

(assert-file-contents
    :file "new/external-foo.c"
    :content "int foo;

__attribute__ ((section(\"sec1\"))) int internal_foo(void);

__attribute__ ((section(\"sec0\"))) int main(void) {
  foo = 42;
  return internal_foo();
}
")

  :with-output-off nil)
