; Tests of the advice tool
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "advice") ; todo: or advice-code-only?
(include-book "kestrel/utilities/deftest" :dir :system)

;; A simple test, with extensive guard checking
(deftest
  (defthm-advice test (equal x x) :rule-classes nil
    :models '(:enable :history) ; don't contact the server (todo: allow :non-ml and :ml)
    )
  )

(deftest
  (in-theory (disable append)) ; prevent proof of test2 with no hints
  (defthm-advice test2
    (equal (len (append x y))
           (+ (len x) (len y)))
    :models '(:enable :history) ; don't contact the server
    )
  )
