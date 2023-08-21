; Tests of the advice tool
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Matt K. mod to prevent stack overflow (in test2, from *1* function
; world-since-boot-strap, even after (comp t)) -- I think Allegro CL is failing
; to eliminate tail recursion inside the LABELS form generated for the
; executable-counterpart (*1*) function.

; cert_param: (non-allegro)

(include-book "advice") ; todo: or advice-code-only?
(include-book "kestrel/utilities/deftest" :dir :system)

;; A simple test, with extensive guard checking
(deftest
  (defthm-advice test (equal x x) :rule-classes nil
    :models '(:enable-fns-body :history) ; don't contact the server (todo: allow :non-ml :ml)
    )
  )

(deftest ; this turns on extensive guard checking and so is very slow
  (in-theory (disable append)) ; prevent proof of test2 with no hints
  (defthm-advice test2
    (equal (len (append x y))
           (+ (len x) (len y)))
    :models :non-ml ; don't contact the servers
    )
  )

;; TODO: How can I test (advice) in a book, given that it requires a failed theorem in the command history?
;; ;; Check for issues like guard violations:
;; ;(deftest
;; (set-guard-checking :all)
;; (must-fail (defthm mod-test (implies (natp x) (< (mod x 8) 200))))
;; (advice :models nil ; don't contact the server
;;         )
;; ;)
