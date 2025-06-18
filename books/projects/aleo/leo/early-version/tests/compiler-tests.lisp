; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

;; No separate /testing/ code yet, add later.
(include-book "../definition/compiler")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.rem_wrapped(b);
}}"
      "[main]
a: i8 = -128i8;
b: i8 = 0i8;
"
      :edwards-bls12)
   (and (reserrp err)
        (equal result
               ""))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.rem_wrapped(b);
}}"
      "[main]
a: i8 = -128i8;
b: i8 = -1i8;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
0i8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.div_wrapped(b);
}}"
      "[main]
a: i8 = -128i8;
b: i8 = -1i8;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
-128i8;

"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; some bitwise op tests

;;;;;;;;;;;;;;;;;;;;
;; and, or, xor, and 'not' on i8

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.and(b);
}}"
      "[main]
a: i8 = 73i8;   // 01001001
b: i8 = -34i8;  // 11011110
       // 'and' is 01001000
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
72i8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.or(b);
}}"
      "[main]
a: i8 =  73i8;  // 01001001
b: i8 = -34i8;  // 11011110
       // 'or' is  11011111
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
-33i8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8, b: i8) -> i8 {
    return a.xor(b);
}}"
      "[main]
a: i8 =  73i8;  // 01001001
b: i8 = -34i8;  // 11011110
       // 'xor' is 10010111
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
-105i8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8) -> i8 {
    return a.not();
}}"
      "[main]
a: i8 =  73i8;  // 01001001
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
-74i8;

"))))

;; different syntax for previous
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8) -> i8 {
    return !a;
}}"
      "[main]
a: i8 =  73i8;  // 01001001
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
-74i8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8) -> i8 {
    return a.not();
}}"
      "[main]
a: i8 = -34i8;  // 11011110
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
33i8;

"))))

;; different syntax for previous, and let's try a parenthesized expression
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: i8) -> i8 {
    return !(a & -1i8);
}}"
      "[main]
a: i8 = -34i8;  // 11011110
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
33i8;

"))))

;;;;;;;;;;;;;;;;;;;;
;; and, or, xor, and 'not' on u8

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8, b: u8) -> u8 {
    return a.and(b);
}}"
      "[main]
a: u8 = 73u8;   // 01001001
b: u8 = 222u8;  // 11011110
       // 'and' is 01001000
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
72u8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8, b: u8) -> u8 {
    return a.or(b);
}}"
      "[main]
a: u8 =  73u8;  // 01001001
b: u8 = 222u8;  // 11011110
       // 'or' is  11011111
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
223u8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8, b: u8) -> u8 {
    return a.xor(b);
}}"
      "[main]
a: u8 =  73u8;  // 01001001
b: u8 = 222u8;  // 11011110
       // 'xor' is 10010111
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
151u8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8) -> u8 {
    return a.not();
}}"
      "[main]
a: u8 =  73u8;  // 01001001
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
182u8;

"))))

;; different syntax for previous
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8) -> u8 {
    return !a;
}}"
      "[main]
a: u8 =  73u8;  // 01001001
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
182u8;

"))))

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8) -> u8 {
    return a.not();
}}"
      "[main]
a: u8 = 222u8;  // 11011110
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
33u8;

"))))

;; different syntax for previous, and let's try a parenthesized expression
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: u8) -> u8 {
    return !(a & 255u8);
}}"
      "[main]
a: u8 = 222u8;  // 11011110
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
33u8;

"))))


;;;;;;;;;;;;;;;;;;;;
;; 'and', &, and && on boolean.

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: bool) -> bool {
    return a.and(b);
}}"
      "[main]
a: bool = false;
b: bool = true;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
false;

"))))

;; different syntax for previous
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: bool) -> bool {
    return a & b;
}}"
      "[main]
a: bool = false;
b: bool = true;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
false;

"))))

;; Test unconditional-evaluation property of 'and'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: u8) -> bool {
    return a.and(3u8 / b == 0u8);
}}"
      "[main]
a: bool = false;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (reserrp err)
        (equal result ""))))

;; different syntax for previous
;; Test unconditional-evaluation property of 'and'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: u8) -> bool {
    return a & (3u8 / b == 0u8);
}}"
      "[main]
a: bool = false;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (reserrp err)
        (equal result ""))))

;; Doesn't work yet
#||
;; Test conditional-evaluation property of '&&'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "function main(a: bool, b: u8) -> bool {
    return a && (3u8 / b == 0u8);
}"
      "[main]
a: bool = false;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
false;

"))))
||#

;;;;;;;;;;;;;;;;;;;;
;; 'or', |, and || on boolean.

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: bool) -> bool {
    return a.or(b);
}}"
      "[main]
a: bool = true;
b: bool = false;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
true;

"))))

;; different syntax for previous
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: bool) -> bool {
    return a | b;
}}"
      "[main]
a: bool = true;
b: bool = false;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
true;

"))))

;; Test unconditional-evaluation property of 'or'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: u8) -> bool {
    return a.or(3u8 / b == 0u8);
}}"
      "[main]
a: bool = true;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (reserrp err)
        (equal result ""))))

;; different syntax for previous
;; Test unconditional-evaluation property of 'or'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool, b: u8) -> bool {
    return a | (3u8 / b == 0u8);
}}"
      "[main]
a: bool = false;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (reserrp err)
        (equal result ""))))

;; Doesn't work yet
#||
;; Test conditional-evaluation property of '&&'
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "function main(a: bool, b: u8) -> bool {
    return a || (3u8 / b == 0u8);
}"
      "[main]
a: bool = true;
b: u8 = 0u8;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
true;

"))))
||#


;;;;;;;;;;;;;;;;;;;;
;; 'not' and '!' on boolean.

(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool) -> bool {
    return a.not();
}}"
      "[main]
a: bool =  true;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
false;

"))))

;; different syntax for previous, but invert test
(assert-event
 (mv-let (err result)
     (COMPILE-PROGRAM-AND-INPUT-STRINGS-TO-STRING
      "program a.b {
       function main(a: bool) -> bool {
    return !a;
}}"
      "[main]
a: bool =  false;
"
      :edwards-bls12)
   (and (null err)
        (equal result
               "[output]
true;

"))))
