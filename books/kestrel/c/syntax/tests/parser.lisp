; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parser (parse-fn input-string)
  `(assert-event
    (b* ((,(if (eq parse-fn 'parse-external-declaration-list)
               '(mv erp & & & &)
             '(mv erp & & &))
          (,parse-fn (init-parstate (acl2::string=>nats ,input-string)))))
      (if erp
          (cw "~@0" erp) ; CW returns nil, so ASSERT-EVENT fails
        t)))) ; ASSERT-EVENT passes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "struct mystruct
{
   int *val;
};")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "typedef void foo;
struct bar
{
 int val;
};")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int ith(int *a) {
 return a[0];
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int ith(int a[]) {
 return a[0];
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "void foo (int val) {
 printf(\"Val = %d\\n\", val);
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int main() { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int foo (unsigned int v)
{
 return (v >> 1);
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "void encrypt (uint32_t* v) {
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "void encrypt () {
  uint32_t v0=1;
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "void foo () {
  gen_config_t gen_config = {100};
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int A [] = {0,1,2,3};")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int spec_int(unsigned int v)
{
  unsigned int c;
  for (c = 0; v; v >>= 1)
    c += v & 1;
  return c;
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int sum(int a[], int n) {
  int s = 0;
  for (int i = 1; i <= n; ++i)
    s += a[i];
  return s;
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int foo (char x, char y) { return x < y && y < x; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int foo (int x, int y) { return x < y || y < x; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int foo (int x) { int z = 0 ; z &= x; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "void foo () {
  while (x > y) {
    x++;
  }
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int foo () {
  int i = 0;
  i--;
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "int main() {
 int a = 10, b = 5;
 a %= b;
}")
