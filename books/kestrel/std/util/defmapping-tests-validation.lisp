; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Input validation tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions (move):

; show an easily searchable title of a test:

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unary and binary domains and conversions.

(defstub dom (*) => *)

(defstub dom2 (* *) => *)

(defun id (x) (declare (xargs :guard t)) x)

(defun id2 (x y) (declare (xargs :guard t)) (mv x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "NAME input validation.")

;; not a symbol:
(must-succeed*
 (must-fail (defmapping 379 dom dom id id))
 (must-fail (defmapping "map" dom dom id id)))

;; a keyword
(must-fail (defmapping :map dom dom id id))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "DOMA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defmapping map "dom" dom id id))
 (must-fail (defmapping map fffffffff dom id id))
 (must-fail (defmapping map car-cdr-elim dom id id))
 (must-fail (defmapping map (lambda (x)) dom id id))
 (must-fail (defmapping map (lambda (x &y) x) dom id id))
 (must-fail (defmapping map (lambda (x x) x) dom id id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defmapping map p dom id id)))

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map p dom id id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defmapping map p dom id id)))

;; lambda expression in program mode:
(must-fail
 (defmapping map (lambda (x) (digit-char-p x)) dom id id))

;; non-closed lambda expression:
(must-fail (defmapping map (lambda (x) (+ x y)) dom id id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map (lambda (state) (g state)) dom id id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defmapping map (lambda (x) (cons (g x) (g x))) dom id id)))

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defmapping map digit-char-p dom id id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defmapping map m dom id id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defmapping map m dom id id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defmapping map m dom id id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "DOMB input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defmapping map dom "dom" id id))
 (must-fail (defmapping map dom fffffffff id id))
 (must-fail (defmapping map dom car-cdr-elim id id))
 (must-fail (defmapping map dom (lambda (x)) id id))
 (must-fail (defmapping map dom (lambda (x &y) x) id id))
 (must-fail (defmapping map dom (lambda (x x) x) id id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defmapping map dom p id id)))

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom p id id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defmapping map dom p id id)))

;; lambda expression in program mode:
(must-fail
 (defmapping map dom (lambda (x) (digit-char-p x)) id id))

;; non-closed lambda expression:
(must-fail (defmapping map dom (lambda (x) (+ x y)) id id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom (lambda (state) (g state)) id id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defmapping map dom (lambda (x) (cons (g x) (g x))) id id)))

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defmapping map dom digit-char-p id id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defmapping map dom m id id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defmapping map dom m id id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defmapping map dom m id id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "ALPHA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defmapping map dom dom "id" id))
 (must-fail (defmapping map dom dom fffffffff id))
 (must-fail (defmapping map dom dom car-cdr-elim id))
 (must-fail (defmapping map dom dom (lambda (x)) id))
 (must-fail (defmapping map dom dom (lambda (x &y) x) id))
 (must-fail (defmapping map dom dom (lambda (x x) x) id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defmapping map dom dom p id)))

;; wrong arity:
(must-succeed*
 (must-fail (defmapping map dom dom2 id2 id) :with-output-off nil)
 (must-fail (defmapping map dom2 dom id id2) :with-output-off nil)
 :with-output-off nil)

;; wrong number of results:
(must-succeed*
 (must-fail (defmapping map dom2 dom id2 id) :with-output-off nil)
 (must-fail (defmapping map dom dom2 id id2) :with-output-off nil)
 :with-output-off nil)

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom dom p id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defmapping map dom dom p id)))

;; lambda expression in program mode:
(must-fail
 (defmapping map dom dom (lambda (x) (digit-char-p x)) id))

;; lambda expression with the wrong arity:
(must-succeed*
 (must-fail (defmapping map dom dom (lambda (x y) (+ x y)) id))
 (must-fail (defmapping map dom2 dom2 (lambda (x) x) id2)))

;; lambda expression with the wrong number of results:
(must-succeed*
 (must-fail (defmapping map dom dom (lambda (x) (mv x y)) id))
 (must-fail (defmapping map dom2 dom2 (lambda (x y) (+ x y)) id2)))

;; non-closed lambda expression:
(must-fail (defmapping map dom dom (lambda (x) (+ x y)) id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom dom (lambda (state) (g state)) id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defmapping map dom dom (lambda (x) (cons (g x) (g x))) id)))

;; macro that abbreviates a lambda expression with the wrong arity:
(must-succeed*
 (defmacro mac (x y) `(cons ,x ,y))
 (must-fail (defmapping map dom dom mac id) :with-output-off nil)
 (defmacro nac (x) `(mv ,x ,x))
 (must-fail (defmapping map dom2 dom2 nac id2) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression with the wrong number of results:
(must-succeed*
 (defmacro mac (x) `(mv ,x ,x))
 (must-fail (defmapping map dom dom mac id) :with-output-off nil)
 (defmacro nac (x y) `(cons ,x ,y))
 (must-fail (defmapping map dom2 dom2 nac id2) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defmapping map dom dom digit-char-p id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defmapping map dom dom m id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defmapping map dom dom m id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defmapping map dom dom m id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "BETA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defmapping map dom dom id "id"))
 (must-fail (defmapping map dom dom id fffffffff))
 (must-fail (defmapping map dom dom id car-cdr-elim))
 (must-fail (defmapping map dom dom id (lambda (x))))
 (must-fail (defmapping map dom dom id (lambda (x &y) x)))
 (must-fail (defmapping map dom dom id (lambda (x x) x))))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defmapping map dom dom id p)))

;; wrong arity:
(must-succeed*
 (defun f (x y) (declare (xargs :guard t)) (cons x y))
 (must-fail (defmapping map dom dom id f) :with-output-off nil)
 (defun g (x) (declare (xargs :guard t)) (mv x x))
 (must-fail (defmapping map dom2 dom2 id2 g) :with-output-off nil)
 :with-output-off nil)

;; wrong number of results:
(must-succeed*
 (defun f (x) (declare (xargs :guard t)) (mv x x))
 (must-fail (defmapping map dom dom id f) :with-output-off nil)
 (defun g (x y) (declare (xargs :guard t)) (cons x y))
 (must-fail (defmapping map dom2 dom2 id2 g) :with-output-off nil)
 :with-output-off nil)

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom dom id p)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defmapping map dom dom id p)))

;; lambda expression in program mode:
(must-fail
 (defmapping map dom dom id (lambda (x) (digit-char-p x))))

;; lambda expression with the wrong arity:
(must-succeed*
 (must-fail (defmapping map dom dom id (lambda (x y) (+ x y)))
            :with-output-off nil)
 (must-fail (defmapping map dom2 dom2 id2 (lambda (x) (mv x x)))
            :with-output-off nil)
 :with-output-off nil)

;; lambda expression with the wrong number of results:
(must-succeed*
 (must-fail (defmapping map dom dom id (lambda (x) (mv x x)))
            :with-output-off nil)
 (must-fail (defmapping map dom2 dom2 id2 (lambda (x y) (cons x y)))
            :with-output-off nil)
 :with-output-off nil)

;; non-closed lambda expression:
(must-fail (defmapping map dom dom id (lambda (x) (+ x y))))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defmapping map dom dom id (lambda (state) (g state)))))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defmapping map dom dom id (lambda (x) (cons (g x) (g x))))))

;; macro that abbreviates a lambda expression with the wrong arity:
(must-succeed*
 (defmacro mac (x y) `(cons ,x ,y))
 (must-fail (defmapping map dom dom id mac) :with-output-off nil)
 (defmacro nac (x) `(mv ,x ,x))
 (must-fail (defmapping map dom2 dom2 id2 nac) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression with the wrong number of results:
(must-succeed*
 (defmacro mac (x) `(mv ,x ,x))
 (must-fail (defmapping map dom dom id mac) :with-output-off nil)
 (defmacro nac (x y) `(cons ,x ,y))
 (must-fail (defmapping map dom2 dom2 id2 nac) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defmapping map dom dom id digit-char-p))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defmapping map dom dom id m)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defmapping map dom dom id m)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defmapping map dom dom id m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":BETA-OF-ALPHA-THM input validation.")

;; not a boolean
(must-succeed*
 (must-fail (defmapping map dom dom id id :beta-of-alpha-thm "yes"))
 (must-fail (defmapping map dom dom id id :beta-of-alpha-thm :true)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":ALPHA-OF-BETA-THM input validation.")

;; not a boolean
(must-succeed*
 (must-fail (defmapping map dom dom id id :alpha-of-beta-thm "T"))
 (must-fail (defmapping map dom dom id id :alpha-of-beta-thm 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":GUARD-THMS input validation.")

;; not a boolean:
(must-succeed*
 (must-fail (defmapping map dom dom id id :guard-thms #\n))
 (must-fail (defmapping map dom dom id id :guard-thms '(1 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":UNCONDITIONAL input validation.")

;; present without :BETA-OF-ALPHA-THM or :ALPHA-OF-BETA-THM:
(must-fail (defmapping map dom dom id id :unconditional t))

;; not a boolean:
(must-succeed*
 (must-fail
  (defmapping map dom dom id id :alpha-of-beta-thm t :unconditional "nil"))
 (must-fail
  (defmapping map dom dom id id :alpha-of-beta-thm t :unconditional #\t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":THM-NAMES input validation.")

;; not a keyword-value list:
(must-succeed*
 (must-fail (defmapping map dom dom id id :thm-names #\a))
 (must-fail (defmapping map dom dom id id :thm-names (1 2 3)))
 (must-fail (defmapping map dom dom id id :thm-names (:alpha-image))))

;; wrong theorem keywords:
(must-succeed*
 (must-fail (defmapping map dom dom id id :thm-names (:image3 th)))
 (must-fail
  (defmapping map dom dom id id :thm-names (:alpha-image th :abc thh))))

;; disallowed theorem keywords:
(must-succeed*
 (must-fail (defmapping map dom dom id id
              :guard-thms nil :thm-names (:doma-guard th)))
 (must-fail (defmapping map dom dom id id
              :guard-thms nil :thm-names (:alpha-image th :doma-guard thh))))

;; bad theorem names:
(must-succeed*
 (must-fail (defmapping map dom dom id id :thm-names (:alpha-image 33)))
 (must-fail (defmapping map dom dom id id :thm-names (:alpha-injective nil)))
 (must-fail (defmapping map dom dom id id :thm-names (:alpha-of-beta len)))
 (must-fail
  (defmapping map dom dom id id :thm-names (:alpha-of-beta len :beta-image th))))

;; duplicate theorem names:
(must-fail
 (defmapping map dom dom id id :thm-names (:alpha-image th :beta-image th)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":HINTS input validation.")

;; not a keyword-value list or a true list:
(must-succeed*
 (must-fail (defmapping map dom dom id id :hints #\a))
 (must-fail (defmapping map dom dom id id :hints (1 2 3 . 4)))
 (must-fail (defmapping map dom dom id id :hints :alpha-image)))

;; wrong theorem keywords:
(must-succeed*
 (must-fail (defmapping map dom dom id id
              :hints (:image3 (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :hints (:alpha-image (("Goal" :in-theory nil))
                      :abc (("Goal" :in-theory nil))))))

;; disallowed theorem keywords:
(must-succeed*
 (must-fail (defmapping map dom dom id id
              :hints (:alpha-injective (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :hints (:beta-injective (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :guard-thms nil
              :hints (:doma-guard (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :guard-thms nil
              :hints (:domb-guard (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :guard-thms nil
              :hints (:alpha-guard (("Goal" :in-theory nil)))))
 (must-fail (defmapping map dom dom id id
              :guard-thms nil
              :hints (:beta-guard (("Goal" :in-theory nil))))))

;; bad hints:
(must-succeed*
 (must-fail (defmapping map dom dom id id :hints (:alpha-image 33)))
 (must-fail (defmapping map dom dom id id
              :hints (:alpha-image (("Goal" :in-theory (enable aaaaaaaa))))))
 (must-fail (defmapping map dom dom id id
              :hints (:alpha-image (("Goal" :in-theory nil))
                      :beta-image (("Goal" :in-theory (enable aaaaaaaa)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":PRINT input validation.")

;; not NIL, :ERROR, :RESULT, :INFO, or :ALL:
(must-succeed*
 (must-fail (defmapping map dom dom id id :print 77))
 (must-fail (defmapping map dom dom id id :print :nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":SHOW-ONLY input validation.")

;; not a boolean:
(must-succeed*
 (must-fail (defmapping map dom dom id id :show-only 77))
 (must-fail (defmapping map dom dom id id :show-only :nil)))
