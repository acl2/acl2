;; Install all the deps
(ql:quickload "alexandria/tests")

;; Run the tests!
(asdf:test-system "alexandria")
