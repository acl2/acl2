; Tests for theory-hints.lisp.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "theory-hints")
(include-book "tools/rulesets" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;; Tests with starp=nil.
(assert-equal (enable-items-in-theory-expression nil '(a b (:r c)) nil) ''(a b (:r c)))
(assert-equal (enable-items-in-theory-expression '(enable foo bar) '(a b (:r c)) nil) '(enable foo bar a b (:r c)))
(assert-equal (enable-items-in-theory-expression '(enable* foo bar) '(a b (:r c)) nil) '(enable* foo bar a b (:r c)))
(assert-equal (enable-items-in-theory-expression '(disable foo bar) '(a b (:r c)) nil) '(e/d nil (foo bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(disable* foo bar) '(a b (:r c)) nil) '(e/d* nil (foo bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression ''(foo bar) '(a b (:r c)) nil) ''(foo bar a b (:r c)))

(assert-equal (enable-items-in-theory-expression '(e/d) '(a b (:r c)) nil) '(enable a b (:r c))) ; no args (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d ()) '(a b (:r c)) nil) '(enable a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d (foo)) '(a b (:r c)) nil) '(enable foo a b (:r c))) ; one arg (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d (foo) ()) '(a b (:r c)) nil) '(enable foo a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar)) '(a b (:r c)) nil) '(e/d (foo) (bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar) (baz)) '(a b (:r c)) nil) '(e/d (foo) (bar) (baz a b (:r c)))) ; merge into last item
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar) (baz b)) '(a b (:r c)) nil) '(e/d (foo) (bar) (baz b a (:r c)))) ; removes dups

(assert-equal (enable-items-in-theory-expression '(e/d*) '(a b (:r c)) nil) '(enable* a b (:r c))) ; no args (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d* ()) '(a b (:r c)) nil) '(enable* a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d* (foo)) '(a b (:r c)) nil) '(enable* foo a b (:r c))) ; one arg (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) ()) '(a b (:r c)) nil) '(enable* foo a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar)) '(a b (:r c)) nil) '(e/d* (foo) (bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar) (baz)) '(a b (:r c)) nil) '(e/d* (foo) (bar) (baz a b (:r c)))) ; merge into last item
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar) (baz b)) '(a b (:r c)) nil) '(e/d* (foo) (bar) (baz b a (:r c)))) ; removes dups

;; Tests with starp=t.
(assert-equal (enable-items-in-theory-expression nil '(a b (:r c)) t) '(expand-ruleset '(a b (:r c)) world))
(assert-equal (enable-items-in-theory-expression '(enable foo bar) '(a b (:r c)) t) '(enable* foo bar a b (:r c)))
(assert-equal (enable-items-in-theory-expression '(enable* foo bar) '(a b (:r c)) t) '(enable* foo bar a b (:r c)))
(assert-equal (enable-items-in-theory-expression '(disable foo bar) '(a b (:r c)) t) '(e/d* nil (foo bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(disable* foo bar) '(a b (:r c)) t) '(e/d* nil (foo bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression ''(foo bar) '(a b (:r c)) t) '(union-theories '(foo bar) (expand-ruleset '(a b (:r c)) world)))

(assert-equal (enable-items-in-theory-expression '(e/d) '(a b (:r c)) t) '(enable* a b (:r c))) ; no args (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d ()) '(a b (:r c)) t) '(enable* a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d (foo)) '(a b (:r c)) t) '(enable* foo a b (:r c))) ; one arg (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d (foo) ()) '(a b (:r c)) t) '(enable* foo a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar)) '(a b (:r c)) t) '(e/d* (foo) (bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar) (baz)) '(a b (:r c)) t) '(e/d* (foo) (bar) (baz a b (:r c)))) ; merge into last item
(assert-equal (enable-items-in-theory-expression '(e/d (foo) (bar) (baz b)) '(a b (:r c)) t) '(e/d* (foo) (bar) (baz b a (:r c)))) ; removes dups

(assert-equal (enable-items-in-theory-expression '(e/d*) '(a b (:r c)) t) '(enable* a b (:r c))) ; no args (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d* ()) '(a b (:r c)) t) '(enable* a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d* (foo)) '(a b (:r c)) t) '(enable* foo a b (:r c))) ; one arg (unusual)
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) ()) '(a b (:r c)) t) '(enable* foo a b (:r c))) ; trailing empty list
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar)) '(a b (:r c)) t) '(e/d* (foo) (bar) (a b (:r c))))
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar) (baz)) '(a b (:r c)) t) '(e/d* (foo) (bar) (baz a b (:r c)))) ; merge into last item
(assert-equal (enable-items-in-theory-expression '(e/d* (foo) (bar) (baz b)) '(a b (:r c)) t) '(e/d* (foo) (bar) (baz b a (:r c)))) ; removes dups

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests with starp=nil.
(assert-equal (disable-items-in-theory-expression nil '(a b (:r c)) nil) 'nil)
(assert-equal (disable-items-in-theory-expression '(enable foo bar) '(a b (:r c)) nil) '(e/d (foo bar) (a b (:r c))))
(assert-equal (disable-items-in-theory-expression '(enable* foo bar) '(a b (:r c)) nil) '(e/d* (foo bar) (a b (:r c))))
(assert-equal (disable-items-in-theory-expression '(disable foo bar) '(a b (:r c)) nil) '(disable foo bar a b (:r c)))
(assert-equal (disable-items-in-theory-expression '(disable* foo bar) '(a b (:r c)) nil) '(disable* foo bar a b (:r c)))
(assert-equal (disable-items-in-theory-expression ''(foo bar) '(a b (:r c)) nil) '(set-difference-theories '(foo bar) '(a b (:r c))))
(assert-equal (disable-items-in-hint '("Goal" :use foo :in-theory (enable bar)) '(baz baz2) nil) '("Goal" :use foo :in-theory (e/d (bar) (baz baz2))))
(assert-equal (disable-items-in-hint '("Goal" :use foo) '(baz baz2) nil) '("Goal" :use foo :in-theory (disable baz baz2)))
(assert-equal (disable-items-in-hints '(("Goal" :use foo)) '(baz baz2) nil) '(("Goal" :use foo :in-theory (disable baz baz2))))
(assert-equal (disable-items-in-hints '(("Subgoal 1" :use foo)) '(baz baz2) nil) '(("Goal" :in-theory (disable baz baz2)) ("Subgoal 1" :use foo :in-theory (disable baz baz2))))
(assert-equal (disable-items-in-hints nil '(baz baz2) nil) '(("Goal" :in-theory (disable baz baz2))))

;; Tests with starp=t.
(assert-equal (disable-items-in-theory-expression nil '(a b (:r c)) t) 'nil)
(assert-equal (disable-items-in-theory-expression '(enable foo bar) '(a b (:r c)) t) '(e/d* (foo bar) (a b (:r c))))
(assert-equal (disable-items-in-theory-expression '(enable* foo bar) '(a b (:r c)) t) '(e/d* (foo bar) (a b (:r c))))
(assert-equal (disable-items-in-theory-expression '(disable foo bar) '(a b (:r c)) t) '(disable* foo bar a b (:r c)))
(assert-equal (disable-items-in-theory-expression '(disable* foo bar) '(a b (:r c)) t) '(disable* foo bar a b (:r c)))
(assert-equal (disable-items-in-theory-expression ''(foo bar) '(a b (:r c)) t) '(set-difference-theories '(foo bar) (expand-ruleset '(a b (:r c)) world)))
(assert-equal (disable-items-in-hint '("Goal" :use foo :in-theory (enable bar)) '(baz baz2) t) '("Goal" :use foo :in-theory (e/d* (bar) (baz baz2))))
(assert-equal (disable-items-in-hint '("Goal" :use foo) '(baz baz2) t) '("Goal" :use foo :in-theory (disable* baz baz2)))
(assert-equal (disable-items-in-hints '(("Goal" :use foo)) '(baz baz2) t) '(("Goal" :use foo :in-theory (disable* baz baz2))))
(assert-equal (disable-items-in-hints '(("Subgoal 1" :use foo)) '(baz baz2) t) '(("Goal" :in-theory (disable* baz baz2)) ("Subgoal 1" :use foo :in-theory (disable* baz baz2))))
(assert-equal (disable-items-in-hints nil '(baz baz2) t) '(("Goal" :in-theory (disable* baz baz2))))

;; (assert-equal
;;  (enable-runes-in-hints '(("Goal" :use blah)) '(f2))
;;  '(("Goal" :use blah :in-theory (enable f2))))

;; (assert-equal
;;  (enable-runes-in-hints '(("Goal" :in-theory (enable f1))) '(f2))
;;  '(("Goal" :in-theory (enable f1 f2))))

;; ;; TODO: Not right if f1 is a theory that includes f2.
;; (assert-equal
;;  (enable-runes-in-hints '(("Goal" :in-theory (disable f1))) '(f2))
;;  '(("Goal" :in-theory (e/d (f2) (f1)))))

;; ;; TODO: Not right if f2 is a theory that includes f3.
;; (assert-equal
;;  (enable-runes-in-hints '(("Goal" :in-theory (e/d (f1) (f2)))) '(f3))
;;  '(("Goal" :in-theory (e/d (f1 f3) (f2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (assert-equal
;;  (disable-runes-in-hints '(("Goal" :use blah)) '(f2))
;;  '(("Goal" :use blah :in-theory (disable f2))))

;; (assert-equal
;;  (disable-runes-in-hints '(("Goal" :in-theory (enable f1))) '(f2))
;;  '(("Goal" :in-theory (e/d (f1) (f2)))))

;; (assert-equal
;;  (disable-runes-in-hints '(("Goal" :in-theory (disable f1))) '(f2))
;;  '(("Goal" :in-theory (disable f1 f2))))

;; (assert-equal
;;  (disable-runes-in-hints '(("Goal" :in-theory (e/d (f1) (f2)))) '(f3))
;;  '(("Goal" :in-theory (e/d (f1) (f2 f3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (assert-equal
;;  (e/d-runes-in-hints '(("Goal" :use blah)) '(f1) '(f2))
;;  '(("Goal" :use blah :in-theory (e/d (f1) (f2)))))

;; (assert-equal
;;  (e/d-runes-in-hints '(("Goal" :in-theory (enable f1))) '(f2) '(f3))
;;  '(("Goal" :in-theory (e/d (f1 f2) (f3)))))

;; ;; TODO: May not be right if f2 is a theory that includes f1
;; (assert-equal
;;  (e/d-runes-in-hints '(("Goal" :in-theory (disable f1))) '(f2) '(f3))
;;  '(("Goal" :in-theory (e/d (f2) (f1 f3)))))

;; ;; TODO: May not be right if f3 is a theory that includes f2
;; (assert-equal
;;  (e/d-runes-in-hints '(("Goal" :in-theory (e/d (f1) (f2)))) '(f3) '(f4))
;;  '(("Goal" :in-theory (e/d (f1 f3) (f2 f4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ruleset foo '(posp endp))
(def-ruleset bar '(natp))

;; (assert-equal
;;  (add-enable*/disable*-to-hints '(("Goal" :in-theory (enable remove-duplicates-equal)))
;;                                 '(foo natp)
;;                                 '(bar len))
;;  '(("Goal"
;;     :in-theory
;;     (set-difference-theories (union-theories (expand-ruleset '(foo natp) world)
;;                                              (enable remove-duplicates-equal))
;;                              (expand-ruleset '(bar len) world)))))

;; ;; test with no existing hint for Goal
;; (assert-equal
;;  (add-enable*/disable*-to-hints nil
;;                                 '(foo natp)
;;                                 '(bar len))
;;  '(("Goal" :in-theory (e/d* (foo natp) (bar len)))))
