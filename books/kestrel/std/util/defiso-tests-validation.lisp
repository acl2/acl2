; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defiso")
(include-book "defiso-templates")

(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Input validation tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions (move):

; show an easily searchable title of a test:

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unary and binary domains and isomorphisms.

(defstub dom (*) => *)

(defstub dom2 (* *) => *)

(defun id (x) (declare (xargs :guard t)) x)

(defun id2 (x y) (declare (xargs :guard t)) (mv x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "NAME input validation.")

;; not a symbol:
(must-succeed*
 (must-fail (defiso 379 dom dom id id))
 (must-fail (defiso "iso" dom dom id id)))

;; a keyword
(must-fail (defiso :iso dom dom id id))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "DOMA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defiso iso "dom" dom id id))
 (must-fail (defiso iso fffffffff dom id id))
 (must-fail (defiso iso car-cdr-elim dom id id))
 (must-fail (defiso iso (lambda (x)) dom id id))
 (must-fail (defiso iso (lambda (x &y) x) dom id id))
 (must-fail (defiso iso (lambda (x x) x) dom id id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defiso iso p dom id id)))

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso p dom id id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defiso iso p dom id id)))

;; lambda expression in program mode:
(must-fail
 (defiso iso (lambda (x) (assert-event x)) dom id id))

;; non-closed lambda expression:
(must-fail (defiso iso (lambda (x) (+ x y)) dom id id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso (lambda (state) (g state)) dom id id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defiso iso (lambda (x) (cons (g x) (g x))) dom id id)))

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defiso iso assert-event dom id id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defiso iso m dom id id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defiso iso m dom id id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defiso iso m dom id id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "DOMB input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defiso iso dom "dom" id id))
 (must-fail (defiso iso dom fffffffff id id))
 (must-fail (defiso iso dom car-cdr-elim id id))
 (must-fail (defiso iso dom (lambda (x)) id id))
 (must-fail (defiso iso dom (lambda (x &y) x) id id))
 (must-fail (defiso iso dom (lambda (x x) x) id id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defiso iso dom p id id)))

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom p id id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defiso iso dom p id id)))

;; lambda expression in program mode:
(must-fail
 (defiso iso dom (lambda (x) (assert-event x)) id id))

;; non-closed lambda expression:
(must-fail (defiso iso dom (lambda (x) (+ x y)) id id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom (lambda (state) (g state)) id id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defiso iso dom (lambda (x) (cons (g x) (g x))) id id)))

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defiso iso dom assert-event id id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defiso iso dom m id id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defiso iso dom m id id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defiso iso dom m id id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "ALPHA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defiso iso dom dom "id" id))
 (must-fail (defiso iso dom dom fffffffff id))
 (must-fail (defiso iso dom dom car-cdr-elim id))
 (must-fail (defiso iso dom dom (lambda (x)) id))
 (must-fail (defiso iso dom dom (lambda (x &y) x) id))
 (must-fail (defiso iso dom dom (lambda (x x) x) id)))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defiso iso dom dom p id)))

;; wrong arity:
(must-succeed*
 (must-fail (defiso iso dom dom2 id2 id) :with-output-off nil)
 (must-fail (defiso iso dom2 dom id id2) :with-output-off nil)
 :with-output-off nil)

;; wrong number of results:
(must-succeed*
 (must-fail (defiso iso dom2 dom id2 id) :with-output-off nil)
 (must-fail (defiso iso dom dom2 id id2) :with-output-off nil)
 :with-output-off nil)

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom dom p id)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defiso iso dom dom p id)))

;; lambda expression in program mode:
(must-fail
 (defiso iso dom dom (lambda (x) (assert-event x)) id))

;; lambda expression with the wrong arity:
(must-succeed*
 (must-fail (defiso iso dom dom (lambda (x y) (+ x y)) id))
 (must-fail (defiso iso dom2 dom2 (lambda (x) x) id2)))

;; lambda expression with the wrong number of results:
(must-succeed*
 (must-fail (defiso iso dom dom (lambda (x) (- x)) id))
 (must-fail (defiso iso dom2 dom2 (lambda (x y) (mv x y)) id2)))

;; non-closed lambda expression:
(must-fail (defiso iso dom dom (lambda (x) (+ x y)) id))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom dom (lambda (state) (g state)) id)))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defiso iso dom dom (lambda (x) (cons (g x) (g x))) id)))

;; macro that abbreviates a lambda expression with the wrong arity:
(must-succeed*
 (defmacro mac (x y) `(cons ,x ,y))
 (must-fail (defiso iso dom dom mac id) :with-output-off nil)
 (defmacro nac (x) `(mv ,x ,x))
 (must-fail (defiso iso dom2 dom2 nac id2) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression with the wrong number of results:
(must-succeed*
 (defmacro mac (x) `(mv ,x ,x))
 (must-fail (defiso iso dom dom mac id) :with-output-off nil)
 (defmacro nac (x y) `(cons ,x ,y))
 (must-fail (defiso iso dom2 dom2 nac id2) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defiso iso dom dom assert-event id))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defiso iso dom dom m id)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defiso iso dom dom m id)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defiso iso dom dom m id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "BETA input validation.")

;; not function name, macro name, or lambda expression:
(must-succeed*
 (must-fail (defiso iso dom dom id "id"))
 (must-fail (defiso iso dom dom id fffffffff))
 (must-fail (defiso iso dom dom id car-cdr-elim))
 (must-fail (defiso iso dom dom id (lambda (x))))
 (must-fail (defiso iso dom dom id (lambda (x &y) x)))
 (must-fail (defiso iso dom dom id (lambda (x x) x))))

;; function in program mode:
(must-succeed*
 (defun p (x) (declare (xargs :mode :program)) x)
 (must-fail (defiso iso dom dom id p)))

;; wrong arity:
(must-succeed*
 (defun f (x y) (declare (xargs :guard t)) (cons x y))
 (must-fail (defiso iso dom dom id f) :with-output-off nil)
 (defun g (x) (declare (xargs :guard t)) (mv x x))
 (must-fail (defiso iso dom2 dom2 id2 g) :with-output-off nil)
 :with-output-off nil)

;; wrong number of results:
(must-succeed*
 (defun f (x) (declare (xargs :guard t)) (mv x x))
 (must-fail (defiso iso dom dom id f) :with-output-off nil)
 (defun g (x y) (declare (xargs :guard t)) (cons x y))
 (must-fail (defiso iso dom2 dom2 id2 g) :with-output-off nil)
 :with-output-off nil)

;; function with stobjs:
(must-succeed*
 (defun p (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom dom id p)))

;; non-guard-verified function:
(must-succeed*
 (defun p (x) (declare (xargs :verify-guards nil)) x)
 (must-fail (defiso iso dom dom id p)))

;; lambda expression in program mode:
(must-fail
 (defiso iso dom dom id (lambda (x) (assert-event x))))

;; lambda expression with the wrong arity:
(must-succeed*
 (must-fail (defiso iso dom dom id (lambda (x y) (+ x y)))
            :with-output-off nil)
 (must-fail (defiso iso dom2 dom2 id2 (lambda (x) (mv x x)))
            :with-output-off nil)
 :with-output-off nil)

;; lambda expression with the wrong number of results:
(must-succeed*
 (must-fail (defiso iso dom dom id (lambda (x) (mv x x)))
            :with-output-off nil)
 (must-fail (defiso iso dom2 dom2 id2 (lambda (x y) (cons x y)))
            :with-output-off nil)
 :with-output-off nil)

;; non-closed lambda expression:
(must-fail (defiso iso dom dom id (lambda (x) (+ x y))))

;; lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) state)
 (must-fail (defiso iso dom dom id (lambda (state) (g state)))))

;; lambda expression with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (defiso iso dom dom id (lambda (x) (cons (g x) (g x))))))


;; macro that abbreviates a lambda expression with the wrong arity:
(must-succeed*
 (defmacro mac (x y) `(cons ,x ,y))
 (must-fail (defiso iso dom dom id mac) :with-output-off nil)
 (defmacro nac (x) `(mv ,x ,x))
 (must-fail (defiso iso dom2 dom2 id2 nac) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression with the wrong number of results:
(must-succeed*
 (defmacro mac (x) `(mv ,x ,x))
 (must-fail (defiso iso dom dom id mac) :with-output-off nil)
 (defmacro nac (x y) `(cons ,x ,y))
 (must-fail (defiso iso dom2 dom2 id2 nac) :with-output-off nil)
 :with-output-off nil)

;; macro that abbreviates a lambda expression in program mode:
(must-fail (defiso iso dom dom id assert-event))

;; macro that abbreviates a lambda expression with stobjs:
(must-succeed*
 (defun g (state) (declare (xargs :stobjs state)) (declare (ignore state)) nil)
 (defmacro m (state) `(g ,state))
 (must-fail (defiso iso dom dom id m)))

;; macro that abbreviates a non-closed lambda expression:
(must-succeed*
 (defmacro m (x) `(+ ,x y))
 (must-fail (defiso iso dom dom id m)))

;; macro that abbreviates a lambda expression
;; with non-guard-verified functions:
(must-succeed*
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defmacro m (x) `(g ,x))
 (must-fail (defiso iso dom dom id m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":UNCONDITIONAL input validation.")

;; not a boolean:
(must-succeed*
 (must-fail (defiso iso dom dom id id :unconditional "nil"))
 (must-fail (defiso iso dom dom id id :unconditional #\t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":GUARD-THMS input validation.")

;; not a boolean:
(must-succeed*
 (must-fail (defiso iso dom dom id id :guard-thms #\n))
 (must-fail (defiso iso dom dom id id :guard-thms '(1 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":THM-NAMES input validation.")

;; not a keyword-value list:
(must-succeed*
 (must-fail (defiso iso dom dom id id :thm-names #\a))
 (must-fail (defiso iso dom dom id id :thm-names (1 2 3)))
 (must-fail (defiso iso dom dom id id :thm-names (:alpha-image))))

;; wrong theorem keywords:
(must-succeed*
 (must-fail (defiso iso dom dom id id :thm-names (:image3 th)))
 (must-fail
  (defiso iso dom dom id id :thm-names (:alpha-image th :abc thh))))

;; disallowed theorem keywords:
(must-succeed*
 (must-fail (defiso iso dom dom id id
              :guard-thms nil :thm-names (:doma-guard th)))
 (must-fail (defiso iso dom dom id id
              :guard-thms nil :thm-names (:alpha-image th :doma-guard thh))))

;; bad theorem names:
(must-succeed*
 (must-fail (defiso iso dom dom id id :thm-names (:alpha-image 33)))
 (must-fail (defiso iso dom dom id id :thm-names (:alpha-injective nil)))
 (must-fail (defiso iso dom dom id id :thm-names (:alpha-of-beta len)))
 (must-fail
  (defiso iso dom dom id id :thm-names (:alpha-of-beta len :beta-image th))))

;; duplicate theorem names:
(must-fail
 (defiso iso dom dom id id :thm-names (:alpha-image th :beta-image th)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":HINTS input validation.")

;; not a keyword-value list or a true list:
(must-succeed*
 (must-fail (defiso iso dom dom id id :hints #\a))
 (must-fail (defiso iso dom dom id id :hints (1 2 3 . 4)))
 (must-fail (defiso iso dom dom id id :hints :alpha-image)))

;; wrong theorem keywords:
(must-succeed*
 (must-fail (defiso iso dom dom id id
              :hints (:image3 (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :hints (:alpha-image (("Goal" :in-theory nil))
                      :abc (("Goal" :in-theory nil))))))

;; disallowed theorem keywords:
(must-succeed*
 (must-fail (defiso iso dom dom id id
              :hints (:alpha-injective (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :hints (:beta-injective (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :guard-thms nil
              :hints (:doma-guard (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :guard-thms nil
              :hints (:domb-guard (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :guard-thms nil
              :hints (:alpha-guard (("Goal" :in-theory nil)))))
 (must-fail (defiso iso dom dom id id
              :guard-thms nil
              :hints (:beta-guard (("Goal" :in-theory nil))))))

;; bad hints:
(must-succeed*
 (must-fail (defiso iso dom dom id id :hints (:alpha-image 33)))
 (must-fail (defiso iso dom dom id id
              :hints (:alpha-image (("Goal" :in-theory (enable aaaaaaaa))))))
 (must-fail (defiso iso dom dom id id
              :hints (:alpha-image (("Goal" :in-theory nil))
                      :beta-image (("Goal" :in-theory (enable aaaaaaaa)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":PRINT input validation.")

;; not NIL, :ERROR, :RESULT, :INFO, or :ALL:
(must-succeed*
 (must-fail (defiso iso dom dom id id :print 77))
 (must-fail (defiso iso dom dom id id :print :nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title ":SHOW-ONLY input validation.")

;; not a boolean:
(must-succeed*
 (must-fail (defiso iso dom dom id id :show-only 77))
 (must-fail (defiso iso dom dom id id :show-only :nil)))
