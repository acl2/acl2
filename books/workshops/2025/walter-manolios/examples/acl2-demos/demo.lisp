;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(include-book "acl2s-z3")

;; Scopes
(z3-init)

(z3-assert
 (x y z a b :int)
 (and (> x -100) (< x 100)
      (> y -100) (< y 100)
      (> z -100) (< z 100)
      (> a -100) (< a 100)
      (> b -100) (< b 100)
      (> (+ x y z a b) 100)))
(check-sat)
(get-model-as-assignment)
;; That's a boring assignment... too many 0s! Let's ask that they're
;; all distinct.
;; Note that we can elide the variable names and sorts now, as they
;; are retained from the last z3-assert call!
(z3-assert
 (distinct x y z a b))
(check-sat)
(get-model-as-assignment)
;; That's better. Maybe I want to check whether this is possible if a = 0.
;; I'll place a "checkpoint" here using z3-push
(z3-push)
(z3-assert (= a 0))
(check-sat)
(get-model-as-assignment)
;; Cool, that works. I now want to remove that constraint. I can go back to
;; the checkpoint I just created with z3-pop
(z3-pop)
(z3-assert (> a 50))
(check-sat)
(get-model-as-assignment)
;; Note that we get something back with a = 0 - the previous assignment is still valid

;; Note that z3-query is not provided by the Z3 FFI.
;; It's just a convenient function I wrote that does (z3-init), (z3-assert ...), and (check-sat)
;; Bitvectors
(z3-query
 (v (_ :bitvec 4))
 (= (bvadd v (int2bv 4 -1)) (int2bv 4 7)))
;; Note that we interpret any bitvectors that Z3 produces in a model
;; as unsigned integers. This is a choice of our interface.

;; Sequences
(z3-query
 (x (:seq :int) y (:seq :int))
 (= (seq.++ x y) (seq 1 2 3 4 5)))

(z3-query
 (x (:seq :int))
 (and
  (>= (seq.len x) 3)
  (distinct (seq-nth x 0) (seq-nth x 1) (seq-nth x 2))
  (= (seq-nth x 2) (+ (seq-nth x 0) (seq-nth x 1)))))

;; Tuples
(z3-init)
(z3-register-tuple-sort :foo
                        ((a . :int) (b . :bool)))
(z3-push)
(z3-assert
 (r :foo)
 (and (= (tuple-get :foo a r) 5)
      (tuple-get :foo b r)))
(check-sat)
(get-model-as-assignment)
(z3-pop)

;; tuple-val is a constructor for a tuple
;;
(z3-assert
 (a :int b :bool)
 (= (tuple-val :foo 123 nil)
    (tuple-val :foo a b)))
(check-sat)
(get-model-as-assignment)

;; Strings
(z3-query
 (a :string b :string c :string)
 (and (= (str.++ a b) "abcd")
      (= (str.++ b c) "cdef")
      (not (= b ""))))

;; Regexes
(z3-query
 (x :string)
 (and (> (seq-length x) 3)
      (seq.in.re x (re.+ (re.union (re.range "a" "b") (re.range "d" "e"))))))

;; Uninterpeted Functions
(z3-query (f (:fn (:int) :int))
          ;; Unintepreted function are called just like interpreted
          ;; functions.
          (and (= (f 0) 3)
               (= (f 1) 8)))

(z3-query (f (:fn (:int) :string)
           g (:fn (:string) (_ :bitvec 4))
           h (:fn ((_ :bitvec 4)) :int))
          (and (= (h (g (f 3))) 5)
               (= (h (g (f 1))) 20)
               (= (f 1) "hello")
               (= (f 2) "world!")))
;; We can also get some statistics from Z3
(z3-get-solver-stats)

;; Tactics
(z3-init)
(z3-set-solver-from-tactic "sat")
(z3-assert (x :bool y :int)
           (and x (>= y 5)))
;; This returns UNKNOWN because the SAT tactic can't reason about y,
;; and it is neccesary to do so to produce a model containing y.
(check-sat)
;; If we add another assertion such we can show that the conjunction
;; of this and the previous assertion is UNSAT without needing to
;; reason about y, the SAT tactic is able to determine UNSAT.
(z3-assert (x :bool y :int)
           (not x))
(check-sat)

(z3-set-solver-from-tactic "smt")
(z3-assert (x :bool y :int)
           (and x (>= y 5)))
(check-sat)
