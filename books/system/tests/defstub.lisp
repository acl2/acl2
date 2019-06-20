; System Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "misc/assert" :dir :system)
(include-book "misc/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for DEFSTUB and related system code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; construction of witness body with old style:

(assert! (equal (defstub-body-new '*) nil))

(assert! (equal (defstub-body-new 's) 's))

(assert! (equal (defstub-body-new 'state) 'state))

(assert! (equal (defstub-body-new '(mv * *)) '(mv nil nil)))

(assert! (equal (defstub-body-new '(mv * s)) '(mv nil s)))

(assert! (equal (defstub-body-new '(mv state * *)) '(mv state nil nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; construction of witness body with new style:

(assert! (equal (defstub-body-old 'x '(state s)) nil))

(assert! (equal (defstub-body-old t '(state s)) nil))

(assert! (equal (defstub-body-old 's '(state s)) 's))

(assert! (equal (defstub-body-old 'state '(state s)) 'state))

(assert! (equal (defstub-body-old '(mv x y) '(state s)) '(mv nil nil)))

(assert! (equal (defstub-body-old '(mv t t t) '(state s)) '(mv nil nil nil)))

(assert! (equal (defstub-body-old '(mv state t) '(state s)) '(mv state nil)))

(assert! (equal (defstub-body-old '(mv t s) '(state ss)) '(mv nil nil)))

(assert! (equal (defstub-body-old 's '(state ss)) nil))

(assert! (equal (defstub-body-old 's '(s)) 's))

(assert! (equal (defstub-body-old '(mv s r) '(s state)) '(mv s nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; old style, no stobjs:

(must-succeed*

 (defstub f (x) t)
 (assert! (and (equal (stobjs-in 'f (w state)) '(nil))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (x y) z)
 (assert! (and (equal (stobjs-in 'g (w state)) '(nil nil))
               (equal (stobjs-out 'g (w state)) '(nil))))

 (defstub h (a b c) (mv d e))
 (assert! (and (equal (stobjs-in 'h (w state)) '(nil nil nil))
               (equal (stobjs-out 'h (w state)) '(nil nil))))

 (defstub k (w) (mv t t))
 (assert! (and (equal (stobjs-in 'k (w state)) '(nil))
               (equal (stobjs-out 'k (w state)) '(nil nil))))

 (defstub l (a x) (mv t y))
 (assert! (and (equal (stobjs-in 'l (w state)) '(nil nil))
               (equal (stobjs-out 'l (w state)) '(nil nil))))

 (defstub m () t)
 (assert! (and (equal (stobjs-in 'm (w state)) '())
               (equal (stobjs-out 'm (w state)) '(nil))))

 (defstub n (x y) =>) ; here => is just the output variable name
 (assert! (and (equal (stobjs-in 'n (w state)) '(nil nil))
               (equal (stobjs-out 'n (w state)) '(nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; old style, implicit state stobj:

(must-succeed*

 (defstub f (state) t)
 (assert! (and (equal (stobjs-in 'f (w state)) '(state))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (state) (mv state t))
 (assert! (and (equal (stobjs-in 'g (w state)) '(state))
               (equal (stobjs-out 'g (w state)) '(state nil))))

 (defstub h (x y state) z)
 (assert! (and (equal (stobjs-in 'h (w state)) '(nil nil state))
               (equal (stobjs-out 'h (w state)) '(nil))))

 (defstub k (state u) (mv a b state c d))
 (assert! (and (equal (stobjs-in 'k (w state)) '(state nil))
               (equal (stobjs-out 'k (w state)) '(nil nil state nil nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; old style, user-defined stobjs:

(must-succeed*

 (defstobj s)
 (defstobj r)

 (defstub f (s x y) t) ; s not stobj here because not declared
 (assert! (and (equal (stobjs-in 'f (w state)) '(nil nil nil))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (s x y) t :stobjs s)
 (assert! (and (equal (stobjs-in 'g (w state)) '(s nil nil))
               (equal (stobjs-out 'g (w state)) '(nil))))

 (defstub h (s) s :stobjs (s))
 (assert! (and (equal (stobjs-in 'h (w state)) '(s))
               (equal (stobjs-out 'h (w state)) '(s))))

 (defstub k (x s y r) (mv r t) :stobjs (r s))
 (assert! (and (equal (stobjs-in 'k (w state)) '(nil s nil r))
               (equal (stobjs-out 'k (w state)) '(r nil))))

 (defstub l (s state) t :stobjs s)
 (assert! (and (equal (stobjs-in 'l (w state)) '(s state))
               (equal (stobjs-out 'l (w state)) '(nil))))

 (defstub m (r state) (mv state x) :stobjs (r state))
 (assert! (and (equal (stobjs-in 'm (w state)) '(r state))
               (equal (stobjs-out 'm (w state)) '(state nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; old style, guards:

(must-succeed*

 (defstub f (x) t :guard (natp x))
 (assert! (equal (guard 'f nil (w state))
                 '(natp x)))

 (defstub g (a b) (mv c d e) :guard (and (integerp a) (integerp b) (< a b)))
 (assert! (equal (guard 'g nil (w state))
                 '(if (integerp a) (if (integerp b) (< a b) 'nil) 'nil)))

 (defstub h (state x) t :guard (stringp x))
 (assert! (and (equal (guard 'h t (w state))
                      '(stringp x))
               (equal (guard 'h nil (w state))
                      '(if (state-p state) (stringp x) 'nil))))

 (defstub k (state x) y :guard t)
 (assert! (and (equal (guard 'k t (w state))
                      *t*)
               (equal (guard 'k nil (w state))
                      '(state-p state))))

 (defstobj s)
 (defstub l (s x) t :stobjs s :guard (consp x))
 (assert! (and (equal (guard 'l t (w state))
                      '(consp x))
               (equal (guard 'l nil (w state))
                      '(if (sp s) (consp x) 'nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; new style, no stobjs:

(must-succeed*

 (defstub f (*) => *)
 (assert! (and (equal (stobjs-in 'f (w state)) '(nil))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (* *) => *)
 (assert! (and (equal (stobjs-in 'g (w state)) '(nil nil))
               (equal (stobjs-out 'g (w state)) '(nil))))

 (defstub h (* * *) => (mv * *))
 (assert! (and (equal (stobjs-in 'h (w state)) '(nil nil nil))
               (equal (stobjs-out 'h (w state)) '(nil nil))))

 (defstub k (*) => (mv * *))
 (assert! (and (equal (stobjs-in 'k (w state)) '(nil))
               (equal (stobjs-out 'k (w state)) '(nil nil))))

 (defstub l (* *) => (mv * *))
 (assert! (and (equal (stobjs-in 'l (w state)) '(nil nil))
               (equal (stobjs-out 'l (w state)) '(nil nil))))

 (defstub m () => *)
 (assert! (and (equal (stobjs-in 'm (w state)) '())
               (equal (stobjs-out 'm (w state)) '(nil))))

; check for insertion of (logic) at start of generated encapsulate events

 (program)
 (defstub p (*) => *)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; new style, implicit state stobj:

(must-succeed*

 (defstub f (state) t)
 (assert! (and (equal (stobjs-in 'f (w state)) '(state))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (state) (mv state t))
 (assert! (and (equal (stobjs-in 'g (w state)) '(state))
               (equal (stobjs-out 'g (w state)) '(state nil))))

 (defstub h (x y state) z)
 (assert! (and (equal (stobjs-in 'h (w state)) '(nil nil state))
               (equal (stobjs-out 'h (w state)) '(nil))))

 (defstub k (state u) (mv a b state c d))
 (assert! (and (equal (stobjs-in 'k (w state)) '(state nil))
               (equal (stobjs-out 'k (w state)) '(nil nil state nil nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; new style, user-defined stobjs:

(must-succeed*

 (defstobj s)
 (defstobj r)

 (defstub f (s * *) => *)
 (assert! (and (equal (stobjs-in 'f (w state)) '(s nil nil))
               (equal (stobjs-out 'f (w state)) '(nil))))

 (defstub g (r * *) => *)
 (assert! (and (equal (stobjs-in 'g (w state)) '(r nil nil))
               (equal (stobjs-out 'g (w state)) '(nil))))

 (defstub h (s) => s)
 (assert! (and (equal (stobjs-in 'h (w state)) '(s))
               (equal (stobjs-out 'h (w state)) '(s))))

 (defstub k (* s * r) => (mv r *))
 (assert! (and (equal (stobjs-in 'k (w state)) '(nil s nil r))
               (equal (stobjs-out 'k (w state)) '(r nil))))

 (defstub l (s state) => *)
 (assert! (and (equal (stobjs-in 'l (w state)) '(s state))
               (equal (stobjs-out 'l (w state)) '(nil))))

 (defstub m (r state) => (mv state *))
 (assert! (and (equal (stobjs-in 'm (w state)) '(r state))
               (equal (stobjs-out 'm (w state)) '(state nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; new style, guards:

(must-succeed*

 (defstub f (*) => * :formals (x) :guard (natp x))
 (assert! (equal (guard 'f nil (w state))
                 '(natp x)))

 (defstub g (* *) => (mv * * *) :formals (a b) :guard (and (integerp a)
                                                           (integerp b)
                                                           (< a b)))
 (assert! (equal (guard 'g nil (w state))
                 '(if (integerp a) (if (integerp b) (< a b) 'nil) 'nil)))

 (defstub h (state *) => * :formals (state x) :guard (stringp x))
 (assert! (and (equal (guard 'h t (w state))
                      '(stringp x))
               (equal (guard 'h nil (w state))
                      '(if (state-p state) (stringp x) 'nil))))

 (defstub k (state *) => * :formals (state x) :guard t)
 (assert! (and (equal (guard 'k t (w state))
                      *t*)
               (equal (guard 'k nil (w state))
                      '(state-p state))))

 (defstobj s)
 (defstub l (s *) => * :formals (s x) :guard (consp x))
 (assert! (and (equal (guard 'l t (w state))
                      '(consp x))
               (equal (guard 'l nil (w state))
                      '(if (sp s) (consp x) 'nil))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; less than two arguments for defstub after the name argument:

(must-fail
 (defstub f)
 :with-output-off nil)

(must-fail
 (defstub f (x))
 :with-output-off nil)
