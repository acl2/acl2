; System Utilities -- Numbered Names -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "numbered-names")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (get-numbered-name-index-start (w state))
              *default-numbered-name-index-start*)

(must-succeed*
 (set-numbered-name-index-start "{{")
 (assert-equal (get-numbered-name-index-start (w state)) "{{"))

(must-succeed*
 (set-numbered-name-index-start "$")
 (assert-equal (get-numbered-name-index-start (w state)) "$"))

(must-fail (set-numbered-name-index-start ""))

(must-fail (set-numbered-name-index-start "$1"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (get-numbered-name-index-end (w state))
              *default-numbered-name-index-end*)

(must-succeed*
 (set-numbered-name-index-end "}}")
 (assert-equal (get-numbered-name-index-end (w state))
               "}}"))

(must-succeed*
 (set-numbered-name-index-end "")
 (assert-equal (get-numbered-name-index-end (w state))
               ""))

(must-fail (set-numbered-name-index-end "2@"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (get-numbered-name-index-wildcard (w state))
              *default-numbered-name-index-wildcard*)

(must-succeed*
 (set-numbered-name-index-wildcard "?")
 (assert-equal (get-numbered-name-index-wildcard (w state))
               "?"))

(must-fail (set-numbered-name-index-wildcard ""))

(must-fail (set-numbered-name-index-wildcard "0"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (mv-list 3 (check-numbered-name 'none (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f{} (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f{q} (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f{**} (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f{43} (w state)))
               '(t f 43))

 (assert-equal (mv-list 3 (check-numbered-name 'f{*} (w state)))
               '(t f 0)))

(must-succeed*

 (set-numbered-name-index-start "$")
 (set-numbered-name-index-end "")
 (set-numbered-name-index-wildcard "?")

 (assert-equal (mv-list 3 (check-numbered-name 'none (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f$ (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f$q (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f$?? (w state)))
               '(nil nil nil))

 (assert-equal (mv-list 3 (check-numbered-name 'f$43 (w state)))
               '(t f 43))

 (assert-equal (mv-list 3 (check-numbered-name 'f$? (w state)))
               '(t f 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (make-numbered-name 'gg 61 (w state))
               'gg{61})

 (assert-equal (make-numbered-name 'h 2 (w state))
               'h{2}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (set-numbered-name-index 'abc 4 (w state))
               'abc{4})

 (assert-equal (set-numbered-name-index 'bar{2} 4 (w state))
               'bar{4}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (add-numbered-name-in-use fn{4})
 (add-numbered-name-in-use fn{1})
 (assert-equal (max-numbered-name-index-in-use 'fn (w state))
               4)

 (add-numbered-name-in-use fn{3})
 (assert-equal (max-numbered-name-index-in-use 'fn (w state))
               4)

 (add-numbered-name-in-use fn{9})
 (assert-equal (max-numbered-name-index-in-use 'fn (w state))
               9)

 (add-numbered-name-in-use ffn{12})
 (assert-equal (max-numbered-name-index-in-use 'fn (w state))
               9)

 (add-numbered-name-in-use g)
 (assert-equal (max-numbered-name-index-in-use 'fn (w state))
               9))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (resolve-numbered-name-wildcard 'f (w state))
               'f)

 (assert-equal (resolve-numbered-name-wildcard 'f{3} (w state))
               'f{3})

 (add-numbered-name-in-use f{2})
 (add-numbered-name-in-use f{5})
 (assert-equal (resolve-numbered-name-wildcard 'f{*} (w state))
               'f{5}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (next-numbered-name 'g (w state))
               'g{1})

 (assert-equal (next-numbered-name 'g{44} (w state))
               'g{45})

 (defun g{5} (x) x)
 (defun g{6} (x) x)
 (assert-equal (next-numbered-name 'g{4} (w state))
               'g{7})

 (defun g{1} (x) x)
 (assert-equal (next-numbered-name 'g (w state))
               'g{2}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-equal (get-global-numbered-name-index (w state))
               1)
 (assert-equal (set-numbered-name-index-to-global 'h (w state))
               'h{1})
 (assert-equal (set-numbered-name-index-to-global 'h{55} (w state))
               'h{1})

 (increment-global-numbered-name-index)
 (increment-global-numbered-name-index)
 (assert-equal (get-global-numbered-name-index (w state))
               3)
 (assert-equal (set-numbered-name-index-to-global 'h (w state))
               'h{3})
 (assert-equal (set-numbered-name-index-to-global 'h{55} (w state))
               'h{3})

 (reset-global-numbered-name-index)
 (assert-equal (get-global-numbered-name-index (w state))
               1)
 (assert-equal (set-numbered-name-index-to-global 'h (w state))
               'h{1})
 (assert-equal (set-numbered-name-index-to-global 'h{55} (w state))
               'h{1}))
