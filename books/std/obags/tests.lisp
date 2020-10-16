; Ordered Bags (Obags) Library
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

(assert! (obag::bagp nil))

(assert! (obag::bagp '(4/5)))

(assert! (obag::bagp '(5 68)))

(assert! (obag::bagp '(x x)))

(assert! (obag::bagp '(5 5 5 68)))

(assert! (obag::bagp '("a" "bb" "c" "c")))

(assert! (not (obag::bagp 44)))

(assert! (not (obag::bagp '(2 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::bfix nil)
              nil)

(assert-equal (obag::bfix '(4/5))
              '(4/5))

(assert-equal (obag::bfix '(5 68))
              '(5 68))

(assert-equal (obag::bfix '(x x))
              '(x x))

(assert-equal (obag::bfix '(5 5 5 68))
              '(5 5 5 68))

(assert-equal (obag::bfix '("a" "bb" "c" "c"))
              '("a" "bb" "c" "c"))

(defthm bfix-test1
  (equal (obag::bfix 44) nil))

(defthm bfix-test2
  (equal (obag::bfix '(2 1)) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (obag::empty nil))

(assert! (not (obag::empty '(4/5))))

(assert! (not (obag::empty '(5 68))))

(assert! (not (obag::empty '(x x))))

(assert! (not (obag::empty '(5 5 5 68))))

(assert! (not (obag::empty '("a" "bb" "c" "c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::head '(4/5))
              4/5)

(assert-equal (obag::head '(5 68))
              5)

(assert-equal (obag::head '(x x))
              'x)

(assert-equal (obag::head '(5 5 5 68))
              5)

(assert-equal (obag::head '("a" "bb" "c" "c"))
              "a")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::tail '(4/5))
              nil)

(assert-equal (obag::tail '(5 68))
              '(68))

(assert-equal (obag::tail '(x x))
              '(x))

(assert-equal (obag::tail '(5 5 5 68))
              '(5 5 68))

(assert-equal (obag::tail '("a" "bb" "c" "c"))
              '("bb" "c" "c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::insert #\a nil)
              '(#\a))

(assert-equal (obag::insert 0 '(4/5))
              '(0 4/5))

(assert-equal (obag::insert 2 '(4/5))
              '(4/5 2))

(assert-equal (obag::insert 1 '(5 68))
              '(1 5 68))

(assert-equal (obag::insert 5 '(5 68))
              '(5 5 68))

(assert-equal (obag::insert 68 '(5 68))
              '(5 68 68))

(assert-equal (obag::insert 'xx '(x x))
              '(x x xx))

(assert-equal (obag::insert "a" '(5 5 5 68))
              '(5 5 5 68 "a"))

(assert-equal (obag::insert "bbb" '("a" "bb" "c" "c"))
              '("a" "bb" "bbb" "c" "c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::delete #\a nil)
              nil)

(assert-equal (obag::delete 0 '(4/5))
              '(4/5))

(assert-equal (obag::delete 4/5 '(4/5))
              nil)

(assert-equal (obag::delete 1 '(5 68))
              '(5 68))

(assert-equal (obag::delete 5 '(5 68))
              '(68))

(assert-equal (obag::delete 68 '(5 68))
              '(5))

(assert-equal (obag::delete 'xx '(x x))
              '(x x))

(assert-equal (obag::delete "a" '(5 5 5 68))
              '(5 5 5 68))

(assert-equal (obag::delete 5 '(5 5 5 68))
              '(5 5 68))

(assert-equal (obag::delete "bbb" '("a" "bb" "c" "c"))
              '("a" "bb" "c" "c"))

(assert-equal (obag::delete "c" '("a" "bb" "c" "c"))
              '("a" "bb" "c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (obag::in '(7 3) nil)))

(assert! (not (obag::in '(7 3) '(4/5))))

(assert! (obag::in 4/5 '(4/5)))

(assert! (not (obag::in 33 '(5 68))))

(assert! (obag::in 5 '(5 68)))

(assert! (obag::in 68 '(5 68)))

(assert! (not (obag::in 'y '(x x))))

(assert! (obag::in 'x '(x x)))

(assert! (not (obag::in 6 '(5 5 5 68))))

(assert! (obag::in 5 '(5 5 5 68)))

(assert! (obag::in 68 '(5 5 5 68)))

(assert! (obag::in "c" '("a" "bb" "c" "c")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::occs '(7 3) nil)
              0)

(assert-equal (obag::occs '(7 3) '(4/5))
              0)

(assert-equal (obag::occs 4/5 '(4/5))
              1)

(assert-equal (obag::occs 33 '(5 68))
              0)

(assert-equal (obag::occs 5 '(5 68))
              1)

(assert-equal (obag::occs 68 '(5 68))
              1)

(assert-equal (obag::occs 'y '(x x))
              0)

(assert-equal (obag::occs 'x '(x x))
              2)

(assert-equal (obag::occs 6 '(5 5 5 68))
              0)

(assert-equal (obag::occs 5 '(5 5 5 68))
              3)

(assert-equal (obag::occs 68 '(5 5 5 68))
              1)

(assert-equal (obag::occs "c" '("a" "bb" "c" "c"))
              2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::cardinality nil)
              0)

(assert-equal (obag::cardinality '(4/5))
              1)

(assert-equal (obag::cardinality '(5 68))
              2)

(assert-equal (obag::cardinality '(x x))
              2)

(assert-equal (obag::cardinality '(5 5 5 68))
              4)

(assert-equal (obag::cardinality '("a" "bb" "c" "c"))
              4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (obag::subbag nil nil))

(assert! (obag::subbag nil '(4/5)))

(assert! (not (obag::subbag '(4/5) nil)))

(assert! (obag::subbag '(4/5) '(4/5)))

(assert! (obag::subbag '(1 2 3) '(1 2 2 3)))

(assert! (not (obag::subbag '(1 2 2 3) '(1 2 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::union nil '(a b))
              '(a b))

(assert-equal (obag::union '(a b) nil)
              '(a b))

(assert-equal (obag::union '(a b) '(c c d))
              '(a b c c d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::intersect nil '(a b))
              nil)

(assert-equal (obag::intersect '(a b) nil)
              nil)

(assert-equal (obag::intersect '(a b) '(c c d))
              nil)

(assert-equal (obag::intersect '(a b) '(b b c c d))
              '(b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (obag::difference nil '(a b))
              nil)

(assert-equal (obag::difference '(a b) nil)
              '(a b))

(assert-equal (obag::difference '(a b) '(c c d))
              '(a b))

(assert-equal (obag::difference '(a b) '(b b c c d))
              '(a))
