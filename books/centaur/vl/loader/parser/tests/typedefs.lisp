; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "base")
(include-book "../blockitems")

(encapsulate nil
  (local (in-theory (enable vl-lookahead-is-token?
                            vl-is-token?)))
  (defparser-top vl-parse-type-declaration
    :guard (and (vl-atts-p atts)
                (vl-lookahead-is-token? :vl-kwd-typedef tokens))))

(defmacro test-parse-typedef (&key input (successp 't)
                                   atts
                                   expect)
  `(with-output
     :off summary
     (assert! (b* ((tokens (make-test-tokens ,input))
                   (pstate (make-vl-parsestate :warnings nil))
                   (config *vl-default-loadconfig*)
                   ((mv erp val ?tokens ?pstate) (vl-parse-type-declaration-top ,atts))
                   (pretty    (and (not erp)
                                   (vl-pretty-type-declaration val)))
                   (- (cw "ERP ~x0.~%" erp))
                   (- (cw "VAL ~x0.~%" val))
                   (- (cw "Pretty val: ~x0.~%" pretty))
                   (- (cw "Expect    : ~x0.~%" ',expect))
                   ;(- (cw "TOKENS ~x0.~%" tokens))
                   ;(- (cw "WARNINGS ~x0.~%" warnings))
                   ((when ,successp)
                    (and (not erp)
                         (or (vl-fwdtypedef-p val)
                             (vl-typedef-p val))
                         (equal ',expect pretty))))
                ;; Otherwise we expect it to fail
                erp))))

(test-parse-typedef :input "typedef" :successp nil)
(test-parse-typedef :input "typedef ;" :successp nil)
(test-parse-typedef :input "typedef foo;" :successp nil)

;; very basic forward type declarations...

(test-parse-typedef :input "typedef struct foo;"
                    :expect (fwdtypedef :vl-struct "foo"))

(test-parse-typedef :input "typedef struct \foo ;"
                    :expect (fwdtypedef :vl-struct "foo"))

(test-parse-typedef :input "typedef enum foo ;"
                    :expect (fwdtypedef :vl-enum "foo"))

(test-parse-typedef :input "typedef union foo ;"
                    :expect (fwdtypedef :vl-union "foo"))

(test-parse-typedef :input "typedef class foo ;"
                    :expect (fwdtypedef :vl-class "foo"))

(test-parse-typedef :input "typedef interface class foo ;"
                    :expect (fwdtypedef :vl-interfaceclass "foo"))


;; some other stupid, invalid forward declarations...

(test-parse-typedef :input "typedef struct" :successp nil)
(test-parse-typedef :input "typedef struct;" :successp nil)
(test-parse-typedef :input "typedef struct foo" :successp nil) ; no semi
(test-parse-typedef :input "typedef struct foo " :successp nil)
(test-parse-typedef :input "typedef struct struct;" :successp nil)
(test-parse-typedef :input "typedef struct foo, bar;" :successp nil)
(test-parse-typedef :input "typedef struct foo [3];" :successp nil)
(test-parse-typedef :input "typedef struct foo [3:0];" :successp nil)
(test-parse-typedef :input "typedef struct [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef struct.enum foo;" :successp nil)



; void isn't valid as a top-level typedef

(test-parse-typedef :input "typedef void foo;" :successp nil)


; special keywords: string, chandle, event --------------------------------------------

;; signedness here doesn't make any sense but it's fine

(test-parse-typedef :input "typedef string foo;"
                    :expect (:vl-typedef "foo" (:vl-string unsigned)))

(test-parse-typedef :input "typedef chandle foo;"
                    :expect (:vl-typedef "foo" (:vl-chandle unsigned)))

(test-parse-typedef :input "typedef event foo;"
                    :expect (:vl-typedef "foo" (:vl-event unsigned)))


(test-parse-typedef :input "typedef string unsigned foo;" :successp nil)
(test-parse-typedef :input "typedef chandle signed foo;" :successp nil)
(test-parse-typedef :input "typedef event unsigned foo;" :successp nil)


; integer vector types: bit, logic, reg -----------------------------------------------

; these should be unsigned by default

(test-parse-typedef :input "typedef bit foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned)))

(test-parse-typedef :input "typedef bit [3:0] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 3 0))))

(test-parse-typedef :input "typedef bit signed [0:3] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit signed (:range 0 3))))

(test-parse-typedef :input "typedef bit unsigned [5:5] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 5 5))))

(test-parse-typedef :input "typedef bit signed [3:0] [7:4] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit signed (:range 3 0) (:range 7 4))))

(test-parse-typedef :input "typedef bit unsigned [3:0] [7:4] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 3 0) (:range 7 4))))

(test-parse-typedef :input "typedef bit unsigned [3:0] [7:4] [10:0] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 3 0) (:range 7 4) (:range 10 0))))

(test-parse-typedef :input "typedef bit unsigned [] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned :vl-unsized-dimension)))

(test-parse-typedef :input "typedef bit unsigned [3:0][] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 3 0) :vl-unsized-dimension)))

(test-parse-typedef :input "typedef bit unsigned [3:0][][10:0] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit unsigned (:range 3 0) :vl-unsized-dimension (:range 10 0))))

(test-parse-typedef :input "typedef bit signed [3:0][10:0][] foo;"
                    :expect (:vl-typedef "foo" (:vl-bit signed (:range 3 0) (:range 10 0) :vl-unsized-dimension)))

(test-parse-typedef :input "typedef bit [5] foo;" :successp nil)
(test-parse-typedef :input "typedef bit [$] foo;" :successp nil)
(test-parse-typedef :input "typedef bit {} foo;" :successp nil)




(test-parse-typedef :input "typedef logic foo;"
                    :expect (:vl-typedef "foo" (:vl-logic unsigned)))

(test-parse-typedef :input "typedef logic [3:0] foo;"
                    :expect (:vl-typedef "foo" (:vl-logic unsigned (:range 3 0))))

(test-parse-typedef :input "typedef logic signed [0:3] foo;"
                    :expect (:vl-typedef "foo" (:vl-logic signed (:range 0 3))))

(test-parse-typedef :input "typedef logic unsigned [5:5] foo;"
                    :expect (:vl-typedef "foo" (:vl-logic unsigned (:range 5 5))))

(test-parse-typedef :input "typedef logic signed [3:0] [7:4] foo;"
                    :expect (:vl-typedef "foo" (:vl-logic signed (:range 3 0) (:range 7 4))))


(test-parse-typedef :input "typedef reg foo;"
                    :expect (:vl-typedef "foo" (:vl-reg unsigned)))

(test-parse-typedef :input "typedef reg [3:0] foo;"
                    :expect (:vl-typedef "foo" (:vl-reg unsigned (:range 3 0))))

(test-parse-typedef :input "typedef reg signed [0:3] foo;"
                    :expect (:vl-typedef "foo" (:vl-reg signed (:range 0 3))))

(test-parse-typedef :input "typedef reg unsigned [5:5] foo;"
                    :expect (:vl-typedef "foo" (:vl-reg unsigned (:range 5 5))))

(test-parse-typedef :input "typedef reg signed [3:0] [7:4] foo;"
                    :expect (:vl-typedef "foo" (:vl-reg signed (:range 3 0) (:range 7 4))))


; integer atom types -----------------------------------------------------------
; byte. shortint, int, longint, integer, time

; these are signed by default except for time
; and unlike the above, they do NOT allow dimensions

(test-parse-typedef :input "typedef time foo;"
                    :expect (:vl-typedef "foo" (:vl-time unsigned)))

(test-parse-typedef :input "typedef time signed foo;"
                    :expect (:vl-typedef "foo" (:vl-time signed)))

(test-parse-typedef :input "typedef time unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-time unsigned)))

(test-parse-typedef :input "typedef time [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef time signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef time signed [] foo;" :successp nil)


;; the others are signed by default

(test-parse-typedef :input "typedef byte foo;"
                    :expect (:vl-typedef "foo" (:vl-byte signed)))

(test-parse-typedef :input "typedef byte signed foo;"
                    :expect (:vl-typedef "foo" (:vl-byte signed)))

(test-parse-typedef :input "typedef byte unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-byte unsigned)))

(test-parse-typedef :input "typedef byte [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef byte signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef byte signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef shortint foo;"
                    :expect (:vl-typedef "foo" (:vl-shortint signed)))

(test-parse-typedef :input "typedef shortint signed foo;"
                    :expect (:vl-typedef "foo" (:vl-shortint signed)))

(test-parse-typedef :input "typedef shortint unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-shortint unsigned)))

(test-parse-typedef :input "typedef shortint [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef shortint signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef shortint signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef int foo;"
                    :expect (:vl-typedef "foo" (:vl-int signed)))

(test-parse-typedef :input "typedef int signed foo;"
                    :expect (:vl-typedef "foo" (:vl-int signed)))

(test-parse-typedef :input "typedef int unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-int unsigned)))

(test-parse-typedef :input "typedef int [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef int signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef int signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef longint foo;"
                    :expect (:vl-typedef "foo" (:vl-longint signed)))

(test-parse-typedef :input "typedef longint signed foo;"
                    :expect (:vl-typedef "foo" (:vl-longint signed)))

(test-parse-typedef :input "typedef longint unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-longint unsigned)))

(test-parse-typedef :input "typedef longint [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef longint signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef longint signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef integer foo;"
                    :expect (:vl-typedef "foo" (:vl-integer signed)))

(test-parse-typedef :input "typedef integer signed foo;"
                    :expect (:vl-typedef "foo" (:vl-integer signed)))

(test-parse-typedef :input "typedef integer unsigned foo;"
                    :expect (:vl-typedef "foo" (:vl-integer unsigned)))

(test-parse-typedef :input "typedef integer [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef integer signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef integer signed [] foo;" :successp nil)




;; non-integer types: shortreal, real, realtime --------------------------------------

;; these don't have any signing or packed dimensions

;; the "unsigned" stuff here is nonsensical but okay -- it's just not
;; applicable to these types

(test-parse-typedef :input "typedef shortreal foo;"
                    :expect (:vl-typedef "foo" (:vl-shortreal unsigned)))

(test-parse-typedef :input "typedef shortreal signed foo;"
                    :successp nil)

(test-parse-typedef :input "typedef shortreal unsigned foo;"
                    :successp nil)

(test-parse-typedef :input "typedef shortreal [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef shortreal signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef shortreal signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef real foo;"
                    :expect (:vl-typedef "foo" (:vl-real unsigned)))

(test-parse-typedef :input "typedef real signed foo;"
                    :successp nil)

(test-parse-typedef :input "typedef real unsigned foo;"
                    :successp nil)

(test-parse-typedef :input "typedef real [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef real signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef real signed [] foo;" :successp nil)



(test-parse-typedef :input "typedef realtime foo;"
                    :expect (:vl-typedef "foo" (:vl-realtime unsigned)))

(test-parse-typedef :input "typedef realtime signed foo;"
                    :successp nil)

(test-parse-typedef :input "typedef realtime unsigned foo;"
                    :successp nil)

(test-parse-typedef :input "typedef realtime [3:0] foo;" :successp nil)
(test-parse-typedef :input "typedef realtime signed [0:3] foo;" :successp nil)
(test-parse-typedef :input "typedef realtime signed [] foo;" :successp nil)



;; enums --------------------------------------------------------------------

(test-parse-typedef :input "typedef enum foo;"      ;; valid forward reference
                    :expect (fwdtypedef :vl-enum "foo"))

(test-parse-typedef :input "typedef enum int foo;"  ;; invalid: no base type on forward reference
                    :successp nil)

(test-parse-typedef :input "typedef enum {} foo;"  ;; need at least one member
                    :successp nil)

;; default type for enum is int
;; default signedness for int is signed

(test-parse-typedef :input "typedef enum {a} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a"))))

(test-parse-typedef :input "typedef enum {a,} foo;" :successp nil)
(test-parse-typedef :input "typedef enum {a} byte;" :successp nil)
(test-parse-typedef :input "typedef enum {a," :successp nil)
(test-parse-typedef :input "typedef enum {," :successp nil)
(test-parse-typedef :input "typedef enum {a}" :successp nil)
(test-parse-typedef :input "typedef enum {a};" :successp nil)

(test-parse-typedef :input "typedef enum {a, b} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-enum :vl-int signed
                              ("a")
                              ("b"))))

; valid enum base types:
;  - integer_atom_types (byte, shortint, int, longint, integer, time) with signing
;  - integer_vector_types (bit, logic, reg) with signing and packed dimensions
;  - other type identifiers with packed dimensions

(test-parse-typedef :input "typedef enum byte {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-byte signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum byte signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-byte signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum byte unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-byte unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum byte unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum byte unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum byte [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum byte [3:0] {a, b} foo;"
                    :successp nil)



(test-parse-typedef :input "typedef enum shortint {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-shortint signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum shortint signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-shortint signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum shortint unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-shortint unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum shortint unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum shortint unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum shortint [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum shortint [3:0] {a, b} foo;"
                    :successp nil)



(test-parse-typedef :input "typedef enum int {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum int signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum int unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum int unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum int unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum int [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum int [3:0] {a, b} foo;"
                    :successp nil)



(test-parse-typedef :input "typedef enum longint {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-longint signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum longint signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-longint signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum longint unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-longint unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum longint unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum longint unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum longint [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum longint [3:0] {a, b} foo;"
                    :successp nil)



(test-parse-typedef :input "typedef enum integer {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-integer signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum integer signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-integer signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum integer unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-integer unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum integer unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum integer unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum integer [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum integer [3:0] {a, b} foo;"
                    :successp nil)



;; time is special because it's unsigned by default

(test-parse-typedef :input "typedef enum time {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-time unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum time signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-time signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum time unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-time unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum time unsigned [3:0] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum time unsigned [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum time [] {a, b} foo;"
                    :successp nil)

(test-parse-typedef :input "typedef enum time [3:0] {a, b} foo;"
                    :successp nil)



; --- vector types: reg, bit, logic
; these are unsigned by default
; and can include signedness and packed dimensions

(test-parse-typedef :input "typedef enum logic {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic unsigned [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned (:range 3 0)
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic unsigned [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic unsigned [3:0][7:4] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum logic unsigned [3:0][] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum logic [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum logic [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-logic unsigned (:range 3 0)
                                                ("a") ("b"))))



(test-parse-typedef :input "typedef enum reg {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg unsigned [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned (:range 3 0)
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg unsigned [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg unsigned [3:0][7:4] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum reg unsigned [3:0][] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum reg [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum reg [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-reg unsigned (:range 3 0)
                                                ("a") ("b"))))


(test-parse-typedef :input "typedef enum bit {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit signed {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit unsigned {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit unsigned [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned (:range 3 0)
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit unsigned [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit unsigned [3:0][7:4] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum bit unsigned [3:0][] {a, b} foo;"
                    :successp nil)  ;; only one packed dimension is allowed!

(test-parse-typedef :input "typedef enum bit [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum bit [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-bit unsigned (:range 3 0)
                                                ("a") ("b"))))


; enums of other arbitrary base types

; these don't really have a signedness, they'll all look unsigned but that's just nonsense

(test-parse-typedef :input "typedef enum bar_t {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-usertype "bar_t" ("a") ("b"))))

(test-parse-typedef :input "typedef enum bar_t {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-usertype "bar_t" ("a") ("b"))))

(test-parse-typedef :input "typedef enum bar_t [] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-usertype "bar_t"
                                                :dims :vl-unsized-dimension
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum bar_t [3:0] {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-usertype "bar_t"
                                                :dims (:range 3 0)
                                                ("a") ("b"))))

(test-parse-typedef :input "typedef enum bar_t [3:0][4:0] {a, b} foo;"
                    :successp nil)  ;; not allowed to have multiple dimensions

(test-parse-typedef :input "typedef enum bar_t [3:0][] {a, b} foo;"
                    :successp nil)  ;; not allowed to have multiple dimensions

(test-parse-typedef :input "typedef enum bar_t [][] {a, b} foo;"
                    :successp nil)  ;; not allowed to have multiple dimensions

(test-parse-typedef :input "typedef enum bar_t [][3:0] {a, b} foo;"
                    :successp nil)  ;; not allowed to have multiple dimensions


;; that covers the base types, now how about member stuff
(test-parse-typedef :input "typedef enum {a, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a") ("b"))))

(test-parse-typedef :input "typedef enum {a = 1, b} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a" = 1) ("b"))))

(test-parse-typedef :input "typedef enum {a = 1, b = 2} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a" = 1) ("b" = 2))))

(test-parse-typedef :input "typedef enum {a[3] = 1, b = 2} foo;" ;; subtle, a[3] means a[0:2]!!!
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed ("a" (:range 0 2) = 1) ("b" = 2))))

(test-parse-typedef :input "typedef enum {a[3:0] = 1, b[1:2] = 2} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed
                                                ("a" (:range 3 0) = 1)
                                                ("b" (:range 1 2) = 2))))

(test-parse-typedef :input "typedef enum {a[3:0] = 1, b[1:2] = 2+3} foo;"
                    :expect (:vl-typedef "foo" (:vl-enum :vl-int signed
                                                ("a" (:range 3 0) = 1)
                                                ("b" (:range 1 2) = (:vl-binary-plus nil 2 3)))))



(test-parse-typedef :input "typedef enum {a[3+1:0] = 1, b[1:2] = 2+3} foo;"
                    ;; must fail, only integral numbers are allowed in these indices
                    :successp nil)

(test-parse-typedef :input "typedef enum {a[3:2'b0] = 1, b[1:2] = 2+3} foo;"
                    ;; must fail, only integral numbers are allowed in these indices
                    :successp nil)

(test-parse-typedef :input "typedef enum {a[1'bx] = 1, b[1:2] = 2+3} foo;"
                    ;; must fail, only integral numbers are allowed in these indices
                    :successp nil)

(test-parse-typedef :input "typedef enum {a[x] = 1, b[1:2] = 2+3} foo;"
                    ;; must fail, only integral numbers are allowed in these indices
                    :successp nil)

(test-parse-typedef :input "typedef enum void {a, b} foo;" ;; void not an ok base type
                    :successp nil)




;; structs --------------------------------------------------------------------


(test-parse-typedef :input "typedef struct" :successp nil)
(test-parse-typedef :input "typedef struct {}" :successp nil)
(test-parse-typedef :input "typedef struct {} foo;" :successp nil) ;; need at least one member
(test-parse-typedef :input "typedef struct {a} foo;" :successp nil) ;; member needs data type, etc
(test-parse-typedef :input "typedef struct {int a} foo;" :successp nil) ;; member needs semicolon

(test-parse-typedef :input "typedef struct {int a;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-int signed))))

(test-parse-typedef :input "typedef struct tagged {int a;} foo;" ;; only unions are tagged
                    :successp nil)

(test-parse-typedef :input "typedef struct {rand int a; randc byte b;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-rand :vl-int signed)
                                         ("b" :vl-randc :vl-byte signed))))

(test-parse-typedef :input "typedef struct {rand int a; randc byte b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-rand :vl-int signed)
                                         ("b" :vl-randc :vl-byte signed)
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct {rand int a; randc byte b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-rand :vl-int signed)
                                         ("b" :vl-randc :vl-byte signed)
                                         ("c" :vl-logic unsigned))))


(test-parse-typedef :input "typedef struct packed signed {rand int a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct packed signed
                              ("a" :vl-rand :vl-int signed)
                              ("b" :vl-rand :vl-int signed)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct packed {rand int unsigned a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct packed
                              ("a" :vl-rand :vl-int unsigned)
                              ("b" :vl-rand :vl-int unsigned)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct signed {rand int unsigned a, b; logic c;} foo;"
                    ;; can't be signed without being packed
                    :successp nil)

(test-parse-typedef :input "typedef struct packed unsigned {rand int signed a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct packed ;; structure unsigned doesn't show up in pretty display
                              ("a" :vl-rand :vl-int signed)
                              ("b" :vl-rand :vl-int signed)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct {rand int unsigned [3:0] a, b; logic c;} foo;"
                    ;; int isn't a vector type
                    :successp nil)

(test-parse-typedef :input "typedef struct {rand reg unsigned [3:0] a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-rand :vl-reg unsigned (:range 3 0))
                                         ("b" :vl-rand :vl-reg unsigned (:range 3 0))
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct {reg signed [3:0][] a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef struct {reg signed [3:0][] a, b; void c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("c" :vl-void unsigned))))

(test-parse-typedef :input "typedef struct {reg signed [3:0][] a, b;
                                            struct { int i1, i2; } blob; }
                                    foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-struct ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("blob" :vl-struct ("i1" :vl-int signed) ("i2" :vl-int signed)))))








(test-parse-typedef :input "typedef union" :successp nil)
(test-parse-typedef :input "typedef union {}" :successp nil)
(test-parse-typedef :input "typedef union {} foo;" :successp nil) ;; need at least one member
(test-parse-typedef :input "typedef union {a} foo;" :successp nil) ;; member needs data type, etc
(test-parse-typedef :input "typedef union {int a} foo;" :successp nil) ;; member needs semicolon

(test-parse-typedef :input "typedef union {int a;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-int signed))))

(test-parse-typedef :input "typedef union tagged {int a;} foo;" ;; only unions are tagged
                    :expect (:vl-typedef "foo"
                             (:vl-union tagged ("a" :vl-int signed))))

(test-parse-typedef :input "typedef union {rand int a; randc byte b;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-rand :vl-int signed)
                              ("b" :vl-randc :vl-byte signed))))

(test-parse-typedef :input "typedef union {rand int a; randc byte b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-rand :vl-int signed)
                                         ("b" :vl-randc :vl-byte signed)
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union {rand int a; randc byte b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-rand :vl-int signed)
                                         ("b" :vl-randc :vl-byte signed)
                                         ("c" :vl-logic unsigned))))


(test-parse-typedef :input "typedef union packed signed {rand int a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union packed signed
                              ("a" :vl-rand :vl-int signed)
                              ("b" :vl-rand :vl-int signed)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union packed {rand int unsigned a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union packed
                              ("a" :vl-rand :vl-int unsigned)
                              ("b" :vl-rand :vl-int unsigned)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union signed {rand int unsigned a, b; logic c;} foo;"
                    ;; can't be signed without being packed
                    :successp nil)

(test-parse-typedef :input "typedef union packed unsigned {rand int signed a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union packed ;; unionure unsigned doesn't show up in pretty display
                              ("a" :vl-rand :vl-int signed)
                              ("b" :vl-rand :vl-int signed)
                              ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union {rand int unsigned [3:0] a, b; logic c;} foo;"
                    ;; int isn't a vector type
                    :successp nil)

(test-parse-typedef :input "typedef union {rand reg unsigned [3:0] a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-rand :vl-reg unsigned (:range 3 0))
                                         ("b" :vl-rand :vl-reg unsigned (:range 3 0))
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union {reg signed [3:0][] a, b; logic c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("c" :vl-logic unsigned))))

(test-parse-typedef :input "typedef union {reg signed [3:0][] a, b; void c;} foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("c" :vl-void unsigned))))

(test-parse-typedef :input "typedef union {reg signed [3:0][] a, b;
                                            union { int i1, i2; } blob; }
                                    foo;"
                    :expect (:vl-typedef "foo"
                             (:vl-union ("a" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("b" :vl-reg signed (:range 3 0) :vl-unsized-dimension)
                                         ("blob" :vl-union ("i1" :vl-int signed) ("i2" :vl-int signed)))))





