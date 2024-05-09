; Tests of combining hints
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "combine-hints")

;; TODO: Add more tests.

(assert-equal (desugar-use-hint 'nil) nil)
(assert-equal (desugar-use-hint 'foo) '(foo))
(assert-equal (desugar-use-hint '(:instance foo)) '((:instance foo)))
(assert-equal (desugar-use-hint '(:rewrite foo)) '((:rewrite foo)))
(assert-equal (desugar-use-hint '(foo bar)) '(foo bar))

(assert-equal (merge-hint-setting-into-goal-hint :use 'foo '(("Goal" :in-theory (enable natp))))
              '(("Goal" :in-theory (enable natp) :use foo)))

(assert-equal (merge-hint-setting-into-goal-hint :use 'foo '(("Goal" :use (bar))))
              '(("Goal" :use (foo bar))))

;; TODO: Could make an e/d.
(assert-equal (merge-hint-setting-into-goal-hint :in-theory '(disable foo) '(("Goal" :in-theory (enable natp))))
              '(("Goal" :in-theory (set-difference-theories (enable natp)
                                                            '(foo)))))

;; TODO: Could add to the existing enable.
(assert-equal (merge-hint-setting-into-goal-hint :in-theory '(enable foo) '(("Goal" :in-theory (enable natp))))
              '(("Goal" :in-theory (union-theories '(foo)
                                                   (enable natp)))))

(assert-equal (merge-hint-setting-into-goal-hint :expand '(foo x) '(("Goal" :in-theory (enable natp))))
              '(("Goal" :in-theory (enable natp) :expand (foo x))))

(assert-equal (merge-hint-setting-into-goal-hint :expand '(foo x) '(("Goal" :expand ((bar y)))))
              '(("Goal" :expand ((foo x) (bar y)))))
