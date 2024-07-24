; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../disambiguator")
(include-book "../parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-dimb (input &key gcc)
  `(assert-event
    (b* ((pstate (init-parstate (acl2::string=>nats ,input) nil))
         ((mv erp1 ast &) (parse-translation-unit pstate))
         (- (cw "~%Input:~%~x0~|" ast))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         (- ))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0" erp2))
            (t (prog2$ (cw "~%Output:~%~x0~|" ast) t))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-dimb
 "int x;
")

(test-dimb
 "enum {a, b, c};
  int x = b;
")

(test-dimb
 "int main(void) {
    return 0;
  }
")

(test-dimb
 "void f();
")

(test-dimb
 "void f() {}
")

(test-dimb
 "int x;
  void f() {
  int y = sizeof(x);
  }
")

(test-dimb
 "typedef char x;
  void f() {
  int y = sizeof(x);
  }
")

(test-dimb
 "int x;
  void f(x) {}
")

(test-dimb
 "typedef char x;
  void f(x);
")

(test-dimb
 "void f(int(x));
")

(test-dimb
 "typedef char x;
  void f(int(x));
")

(test-dimb
 "void f(int *(x));
")

(test-dimb
 "typedef char x;
  void f(int *(x));
")

(test-dimb
 "int a;
  void f() {
  int b;
  a * b;
  }
")

(test-dimb
 "typedef _Bool a;
  void f() {
  int b;
  a * b;
  }
")

(test-dimb
 "void f() {
  int a(int);
  int b;
  int amb = (a)(b);
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)(b);
  }
")

(test-dimb
 "void f() {
  int a(int);
  int b;
  int amb = (a)--++--++(b);
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)--++--++(b);
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int amb = (a)*b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)*b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int amb = (a)+b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)+b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")
