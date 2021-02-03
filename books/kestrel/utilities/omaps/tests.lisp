; Ordered Maps (Omaps) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "core")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (omap::mapp nil))

(assert! (omap::mapp '(("key" . #\v))))

(assert! (omap::mapp '((a . 1) (b . 2) (c . 3))))

(assert! (not (omap::mapp "ab")))

(assert! (not (omap::mapp '(1 2 3))))

(assert! (not (omap::mapp '((2 . 4/5) (1 . 4/5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::mfix nil)
              nil)

(assert-equal (omap::mfix '(("key" . #\v)))
              '(("key" . #\v)))

(assert-equal (omap::mfix '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(defthm mfix-test1
  (equal (omap::mfix "ab") nil))

(defthm mfix-test2
  (equal (omap::mfix '(1 2 3)) nil))

(defthm mfix-test3
  (equal (omap::mfix '((2 . 4/5) (1 . 4/5))) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (omap::empty nil))

(assert! (not (omap::empty '(("key" . #\v)))))

(assert! (not (omap::empty '((a . 1) (b . 2) (c . 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (omap::head '(("key" . #\v))))
              '("key" #\v))

(assert-equal (mv-list 2 (omap::head '((a . 1) (b . 2) (c . 3))))
              '(a 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::tail '(("key" . #\v)))
              nil)

(assert-equal (omap::tail '((a . 1) (b . 2) (c . 3)))
              '((b . 2) (c . 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::update '(8 8) 'x nil)
              '(((8 8) . x)))

(assert-equal (omap::update "loop" 0 '(("key" . #\v)))
              '(("key" . #\v) ("loop" . 0)))

(assert-equal (omap::update "abc" 0 '(("key" . #\v)))
              '(("abc" . 0) ("key" . #\v)))

(assert-equal (omap::update 'aa -15 '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (aa . -15) (b . 2) (c . 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::update* nil '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(assert-equal (omap::update* '((d . 4)) '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3) (d . 4)))

(assert-equal (omap::update* '((a . 10) (d . 4)) '((a . 1) (b . 2) (c . 3)))
              '((a . 10) (b . 2) (c . 3) (d . 4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::delete '(8 8) nil)
              nil)

(assert-equal (omap::delete '(8 8) '(("key" . #\v)))
              '(("key" . #\v)))

(assert-equal (omap::delete "key" '(("key" . #\v)))
              nil)

(assert-equal (omap::delete "key" '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(assert-equal (omap::delete 'a '((a . 1) (b . 2) (c . 3)))
              '((b . 2) (c . 3)))

(assert-equal (omap::delete 'b '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (c . 3)))

(assert-equal (omap::delete 'c '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2)))

(assert-equal (omap::delete 'd '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::delete* '((8 8)) nil)
              nil)

(assert-equal (omap::delete* '((8 8)) '(("key" . #\v)))
              '(("key" . #\v)))

(assert-equal (omap::delete* '("key") '(("key" . #\v)))
              nil)

(assert-equal (omap::delete* '("key") '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(assert-equal (omap::delete* '(#\g "key") '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(assert-equal (omap::delete* '(a) '((a . 1) (b . 2) (c . 3)))
              '((b . 2) (c . 3)))

(assert-equal (omap::delete* '(b) '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (c . 3)))

(assert-equal (omap::delete* '(c) '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2)))

(assert-equal (omap::delete* '(d) '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (b . 2) (c . 3)))

(assert-equal (omap::delete* '(a b) '((a . 1) (b . 2) (c . 3)))
              '((c . 3)))

(assert-equal (omap::delete* '(a b) '((a . 1) (b . 2) (c . 3) (d . 4)))
              '((c . 3) (d . 4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::in #\a nil)
              nil)

(assert-equal (omap::in #\a '(("key" . #\v)))
              nil)

(assert-equal (omap::in "key" '(("key" . #\v)))
              '("key" . #\v))

(assert-equal (omap::in "key" '((a . 1) (b . 2) (c . 3)))
              nil)

(assert-equal (omap::in 'a '((a . 1) (b . 2) (c . 3)))
              '(a . 1))

(assert-equal (omap::in 'b '((a . 1) (b . 2) (c . 3)))
              '(b . 2))

(assert-equal (omap::in 'c '((a . 1) (b . 2) (c . 3)))
              '(c . 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (omap::in* '(#\a) nil)))

(assert! (not (omap::in* '(#\a) '(("key" . #\v)))))

(assert! (omap::in* '("key") '(("key" . #\v))))

(assert! (not (omap::in* '("key") '((a . 1) (b . 2) (c . 3)))))

(assert! (omap::in* '(a) '((a . 1) (b . 2) (c . 3))))

(assert! (omap::in* '(b) '((a . 1) (b . 2) (c . 3))))

(assert! (omap::in* '(c) '((a . 1) (b . 2) (c . 3))))

(assert! (omap::in* '(a b) '((a . 1) (b . 2) (c . 3))))

(assert! (not (omap::in* '("key" a) '((a . 1) (b . 2) (c . 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::lookup "key" '(("key" . #\v)))
              #\v)

(assert-equal (omap::lookup 'a '((a . 1) (b . 2) (c . 3)))
              1)

(assert-equal (omap::lookup 'b '((a . 1) (b . 2) (c . 3)))
              2)

(assert-equal (omap::lookup 'c '((a . 1) (b . 2) (c . 3)))
              3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::lookup* '("key") '(("key" . #\v)))
              '(#\v))

(assert-equal (omap::lookup* '(a) '((a . 1) (b . 2) (c . 3)))
              '(1))

(assert-equal (omap::lookup* '(b) '((a . 1) (b . 2) (c . 3)))
              '(2))

(assert-equal (omap::lookup* '(c) '((a . 1) (b . 2) (c . 3)))
              '(3))

(assert-equal (omap::lookup* nil '((a . 1) (b . 2) (c . 3)))
              nil)

(assert-equal (omap::lookup* '(a b) '((a . 1) (b . 2) (c . 3)))
              '(1 2))

(assert-equal (omap::lookup* '(b c) '((a . 1) (b . 2) (c . 3)))
              '(2 3))

(assert-equal (omap::lookup* '(a c) '((a . 1) (b . 2) (c . 3)))
              '(1 3))

(assert-equal (omap::lookup* '(a b c) '((a . 1) (b . 2) (c . 3)))
              '(1 2 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::rlookup #\v '(("key" . #\v)))
              '("key"))

(assert-equal (omap::rlookup 10 '((a . 1) (b . 2) (c . 1)))
              nil)

(assert-equal (omap::rlookup 1 '((a . 1) (b . 2) (c . 1)))
              '(a c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::rlookup* '(#\v) '(("key" . #\v)))
              '("key"))

(assert-equal (omap::rlookup* '(10) '((a . 1) (b . 2) (c . 1)))
              nil)

(assert-equal (omap::rlookup* '(1) '((a . 1) (b . 2) (c . 1)))
              '(a c))

(assert-equal (omap::rlookup* '(1 2) '((a . 1) (b . 2) (c . 1)))
              '(a b c))

(assert-equal (omap::rlookup* '(1 2 3) '((a . 1) (b . 2) (c . 1)))
              '(a b c))

(assert-equal (omap::rlookup* '(1 2 3) '((a . 1) (b . 2) (c . 3)))
              '(a b c))

(assert-equal (omap::rlookup* '(1 2 3 "y") '((a . 1) (b . 2) (c . 3)))
              '(a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::restrict nil '((a . 1) (b . 2) (c . 3)))
              nil)

(assert-equal (omap::restrict '("x") '((a . 1) (b . 2) (c . 3)))
              nil)

(assert-equal (omap::restrict '(a c) '((a . 1) (b . 2) (c . 3)))
              '((a . 1) (c . 3)))

(assert-equal (omap::restrict '(c) '((a . 1) (b . 2) (c . 3)))
              '((c . 3)))

(assert-equal (omap::restrict '(c (1 2)) '((a . 1) (b . 2) (c . 3)))
              '((c . 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::keys nil)
              nil)

(assert-equal (omap::keys '(("key" . #\v)))
              '("key"))

(assert-equal (omap::keys '((a . 1) (b . 2) (c . 3)))
              '(a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::values nil)
              nil)

(assert-equal (omap::values '(("key" . #\v)))
              '(#\v))

(assert-equal (omap::values '((a . 1) (b . 2) (c . 3)))
              '(1 2 3))

(assert-equal (omap::values '((a . 30) (b . 20) (c . 25)))
              '(20 25 30))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (omap::compatiblep nil nil))

(assert! (omap::compatiblep nil '((a . 1) (b . 2) (c . 3))))

(assert! (omap::compatiblep '((a . 1) (b . 2) (c . 3)) nil))

(assert! (omap::compatiblep '((a . 1) (b . 2)) '((c . 3))))

(assert! (omap::compatiblep '((a . 1) (b . 2)) '((a . 1) (c . 3))))

(assert! (not (omap::compatiblep '((a . 1) (b . 2)) '((a . 2) (c . 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (omap::submap nil nil))

(assert! (omap::submap '((a . 1)) '((a . 1) (b . 55))))

(assert! (not (omap::submap '((#\k . #\v)) nil)))

(assert! (omap::submap '((a . 1) (c . 3)) '((a . 1) (b . 2) (c . 3))))

(assert! (not (omap::submap '((a . 2) (c . 3)) '((a . 1) (b . 2) (c . 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::size nil) 0)

(assert-equal (omap::size '((a . 1))) 1)

(assert-equal (omap::size '((a . 1) (b . 2) (c . 3))) 3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (omap::from-lists nil nil) nil)

(assert-equal (omap::from-lists '(a b) '(1 2)) '((a . 1) (b . 2)))

(assert-equal (omap::from-lists '(b a) '(2 1)) '((a . 1) (b . 2)))

(assert-equal (omap::from-lists '(a a) '(1 2)) '((a . 1)))
