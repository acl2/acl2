; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../split-fn")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  (defconst *new*
    (b* (((mv er ensemble)
          (split-fn-transunit-ensemble (c$::ident "foo")
                                       (c$::ident "bar")
                                       *old*
                                       1)))
      (if er
          (cw "~@0" er)
        ensemble)))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int bar(int *x, int *y) {
  return (*x) + (*y);
}
int foo(int y) {
  int x = 5;
  return bar(&x, &y);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test2.c")
                   :const *old*)

  (defconst *new*
    (b* (((mv er ensemble)
          (split-fn-transunit-ensemble (c$::ident "add_and_sub_all")
                                       (c$::ident "sub_all")
                                       *old*
                                       2)))
      (if er
          (cw "~@0" er)
        ensemble)))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "unsigned long sub_all(long (*arr)[], unsigned int *len, long *total) {
  for (unsigned int i = 0; i < (*len); i++) {
    (*total) -= (*arr)[i];
  }
  return (unsigned long) (*total);
}
unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  return sub_all(&arr, &len, &total);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test3.c")
                   :process :parse
                   :const *old*)

  (defconst *new*
    (b* (((mv er ensemble)
          (split-fn-transunit-ensemble (c$::ident "foo")
                                       (c$::ident "baz")
                                       *old*
                                       1)))
      (if er
          (cw "~@0" er)
        ensemble)))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "int w = 42;
int baz(int *x, long *y, long *z) {
  (*y) = bar((*x));
  return (*x) + (*y) + (*z);
}
int foo(int x) {
  long y = 0, z = 5;
  return baz(&x, &y, &z);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test4.c")
                   :process :parse
                   :const *old*)

  (defconst *new*
    (b* (((mv er ensemble)
          (split-fn-transunit-ensemble (c$::ident "foo")
                                       (c$::ident "baz")
                                       *old*
                                       1)))
      (if er
          (cw "~@0" er)
        ensemble)))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test4.c"
    :content "int bar(void);
int baz(int (* const (*arr)[])(void)) {
  int ret = (*arr)[0]();
  return ret;
}
int foo(int x) {
  int (* const arr[])(void) = {bar};
  return baz(&arr);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("alias.c")
                   :process :parse
                   :const *old*)

  (defconst *new*
    (b* (((mv er ensemble)
          (split-fn-transunit-ensemble (c$::ident "main")
                                       (c$::ident "main_0")
                                       *old*
                                       2)))
      (if er
          (cw "~@0" er)
        ensemble)))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/alias.c"
    :content "int main_0(int *x, int **y) {
  (*x)++;
  return *(*y);
}
int main(void) {
  int x = 0;
  int *y = &x;
  return main_0(&x, &y);
}
")

  :with-output-off nil)
