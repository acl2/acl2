; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../../simpadd0")

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../utilities")

; (depends-on "old/unary.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files '("unary.c")
                 :path "old"
                 :const *old-code*)

(simpadd0 :const-old *old-code*
          :const-new *new-code*)

(c$::output-files :const *new-code*
                  :path "new")

(assert-file-contents
 :file "new/unary.c"
 :content "int f(int x) {
  return !x;
}
int g(int x) {
  return ~(x = 3);
}
int h(int x) {
  return -(x);
}
void unary_on_int(int x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
}
void unary_on_short(short x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
}
void unary_on_ulong(unsigned long x) {
  unsigned long x1 = +x;
  unsigned long x2 = -x;
  unsigned long x3 = ~x;
  unsigned long x4 = !x;
}
")

(assert-highest-thm-has-exec-fun *new-code*)
