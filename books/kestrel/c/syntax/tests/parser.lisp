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

; Test messages.

; The (show-msg ...) forms can be entered into the shell to observe the result.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro show-msg (msg)
  `(cw "~@0~%" ,msg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (char-to-msg nil))

(show-msg (char-to-msg 0))

(show-msg (char-to-msg 10))

(show-msg (char-to-msg 32))

(show-msg (char-to-msg 50))

(show-msg (char-to-msg 64))

(show-msg (char-to-msg 65))

(show-msg (char-to-msg 127))

(show-msg (char-to-msg 128))

(show-msg (char-to-msg 200))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (token-to-msg (token-keyword "while")))

(show-msg (token-to-msg (token-ident (ident "a"))))

(show-msg (token-to-msg (token-const
                         (const-int
                          (iconst
                           (dec/oct/hex-const-dec 1)
                           nil)))))

(show-msg (token-to-msg (token-stringlit (stringlit nil nil))))

(show-msg (token-to-msg (token-punctuator "+")))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (position-to-msg (position 1 0)))

(show-msg (position-to-msg (position 98 34)))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (span-to-msg (span (position 1 0) (position 6 90))))

(show-msg (span-to-msg (span (position 5 10) (position 5 15))))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on positions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-init)
        (position 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-column 1 (position 1 0))
        (position 1 1)))

(assert-event
 (equal (position-inc-column 1 (position 7 17))
        (position 7 18)))

(assert-event
 (equal (position-inc-column 8 (position 7 17))
        (position 7 25)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-line 1 (position 1 0))
        (position 2 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 0))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 44))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 10 (position 20 44))
        (position 30 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on spans.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (span-join (span (position 5 13) (position 5 17))
                   (span (position 5 20) (position 5 23)))
        (span (position 5 13) (position 5 23))))

(assert-event
 (equal (span-join (span (position 2 0) (position 2 10))
                   (span (position 4 10) (position 6 29)))
        (span (position 2 0) (position 6 29))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test simple operations on parser states.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-init-parstate (list)
  `(assert-event
    (equal (init-parstate ,list)
           (parstate ,list (position-init) nil nil nil nil nil))))

(test-init-parstate nil)

(test-init-parstate (list 1))

(test-init-parstate (list 1 2 3))

(test-init-parstate (acl2::string=>nats "abc"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (parsize (init-parstate nil)) 0))

(assert-event
 (equal (parsize (init-parstate (list 72 99 21))) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parser (parse-fn input-string)
  `(assert-event
    (b* ((,(if (eq parse-fn 'parse-external-declaration-list)
               '(mv erp & & & &)
             '(mv erp & & &))
          (,parse-fn (init-parstate (acl2::string=>nats ,input-string)))))
      (if erp
          (cw "~@0" erp) ; CW returns nil, so ASSERT-EVENT fails
        t)))) ; ASSERT-EVENT passes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-external-declaration-list
 "char string[] = \"\";")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-parser
 parse-block-item
 "idx = &((char*)session_peak())[i*BUFSIZE];")
