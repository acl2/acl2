; FTY -- Fixed-Length List Fixtype Generator -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "deflist-of-len")

(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test successful calls with default options:

(must-succeed*
 (fty::deflist-of-len nat-list10 :list-type nat-list :length 10)
 (assert! (function-symbolp 'nat-list10-p (w state)))
 (assert! (function-symbolp 'nat-list10-fix (w state)))
 (assert! (function-symbolp 'nat-list10-equiv$inline (w state))))

(must-succeed*
 (fty::deflist-of-len symbol-list32 :list-type symbol-list :length 32)
 (assert! (function-symbolp 'symbol-list32-p (w state)))
 (assert! (function-symbolp 'symbol-list32-fix (w state)))
 (assert! (function-symbolp 'symbol-list32-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the TYPE input:

(must-fail (fty::deflist-of-len "nat-list10" :list-type nat-list :length 10))

(must-succeed*
 (fty::deflist-of-len something :list-type boolean-list :length 80)
 (assert! (function-symbolp 'something-p (w state)))
 (assert! (function-symbolp 'something-fix (w state)))
 (assert! (function-symbolp 'something-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LIST-TYPE input:

(must-fail (fty::deflist-of-len mylist :list-type #\c :length 20))

(must-fail (fty::deflist-of-len mylist :list-type not-a-fixtype :length 20))

(must-succeed*
 (fty::deflist-of-len mylist :list-type nat-list :length 5)
 (assert! (not (mylist-p nil)))
 (assert! (not (mylist-p '(1 2 3 4))))
 (assert! (mylist-p '(1 2 3 4 5)))
 (assert! (not (mylist-p '(1 2 3 4 5 6 7 8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LENGTH input:

(must-fail (fty::deflist-of-len mylist :list-type nat-list :length "10"))

(must-fail (fty::deflist-of-len mylist :list-type nat-list :length #\6))

(must-fail (fty::deflist-of-len mylist :list-type nat-list :length -19))

(must-succeed*
 (fty::deflist-of-len mylist :list-type nat-list :length 1)
 (assert! (not (mylist-p nil)))
 (assert! (mylist-p '(1)))
 (assert! (not (mylist-p '(1 2 3 4 5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRED input:

(must-fail
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :pred 4/5))

(must-succeed*
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :pred mylistp)
 (assert! (function-symbolp 'mylistp (w state)))
 (assert! (function-symbolp 'mylist-fix (w state)))
 (assert! (function-symbolp 'mylist-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :FIX input:

(must-fail
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :fix "FIX"))

(must-succeed*
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :fix mylistfix)
 (assert! (function-symbolp 'mylist-p (w state)))
 (assert! (function-symbolp 'mylistfix (w state)))
 (assert! (function-symbolp 'mylist-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :EQUIV input:

(must-fail
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :equiv #\=))

(must-succeed*
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :equiv mylist=)
 (assert! (function-symbolp 'mylist-p (w state)))
 (assert! (function-symbolp 'mylist-fix (w state)))
 (assert! (function-symbolp 'mylist=$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PARENTS input:

(must-fail
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :parents one))

(must-succeed
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :parents nil))

(must-succeed
 (fty::deflist-of-len mylist
                      :list-type nat-list :length 10 :parents (this that)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SHORT input:

(must-fail
 (fty::deflist-of-len mylist :list-type nat-list :length 10 :short #\s))

(must-succeed
 (fty::deflist-of-len mylist
                      :list-type nat-list :length 10 :short "Short doc."))

(must-succeed
 (fty::deflist-of-len mylist
                      :list-type nat-list
                      :length 10
                      :short (concatenate 'string "Short" " " "doc.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :LONG input:

(must-fail
 (fty::deflist-of-len mylist
                      :list-type nat-list
                      :length 10
                      :long (#\t #\o #\p #\i #\c)))

(must-succeed
 (fty::deflist-of-len mylist
                      :list-type nat-list
                      :length 10
                      :long "<p>More doc.</p>"))

(must-succeed
 (fty::deflist-of-len mylist
                      :list-type nat-list
                      :length 10
                      :long (xdoc::topstring-p "More doc.")))
