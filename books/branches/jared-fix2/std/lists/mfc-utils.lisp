; MFC Utilities
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; mfc-utils.lisp -- some generally useful syntaxp/metafunction stuff
;
; Original author: Jared Davis <jared@centtech.com>
;                  Sol Swords <sswords@centtech.com>


; BOZO probably belongs in std/ks, but, surprise surprise, circular dependencies
; would arise, so we're putting it in lists.


(in-package "ACL2")
(program)

; REWRITING-POSITIVE-LITERAL
;
; Recall that an ACL2 goal like (IMPLIES (AND HYP1 ... HYPN) CONCL) is really
; represented as a clause, e.g.,
;
;      (NOT HYP1) \/ (NOT HYP2) \/ ... \/ (NOT HYPN) \/ CONCL
;
; In this representation, ordinarily the hyps are "negative" literals and the
; conclusion is a "positive" literal.  Of course, thanks to eliminating
; double-negatives, a hypothesis like (NOT (EQUAL X Y)) is also a positive
; literal.
;
; Sometimes we want a rewrite rule only to apply when we are rewriting a
; positive literal.
;
; A classic example is:
;
;  - If the CONCL is (EQUAL X Y), and we know that X and Y are sets, then we
;    might want to do something drastic like replace (EQUAL X Y) with (EQUAL
;    (MEMBER A X) (MEMBER A Y)) for some new fresh variable A.
;
;  - But if a HYP is (EQUAL X Y), we probably do not want to apply this same
;    rewrite, because knowing that (MEMBER A X) = (MEMBER A Y) is a much weaker
;    hypothesis than knowing (EQUAL X Y).
;
; Given a rewrite rule such as:
;
;    (implies (and hyp1 ... hypN) (equiv (foo x y z) rhs))
;
; We can restrict the rule to only apply to positive literals by adding a new
; hyp like this:
;
;    (rewriting-positive-literal `(foo ,x ,y ,z))
;
; This expands to a syntaxp hypothesis that looks at the MFC to decide if we
; are currently rewriting a positive literal of the specified form.

(defun mfc-rcnst (mfc state)
  (declare (xargs :stobjs state)
           (ignore state))
  (access metafunction-context mfc :rcnst))

(defun mfc-current-literal (mfc state)
  (declare (xargs :stobjs state))
  (let ((rcnst (mfc-rcnst mfc state)))
    (access rewrite-constant rcnst :current-literal)))

(defun rewriting-positive-literal-fn (term mfc state)
  (declare (xargs :stobjs state))
  (and (or (equal (mfc-current-literal mfc state)
                  (cons nil term)))
       (or (null (mfc-ancestors mfc)))))

(defmacro rewriting-positive-literal (term)
  `(syntaxp (rewriting-positive-literal-fn ,term mfc state)))


(defun rewriting-negative-literal-fn (term mfc state)
  (declare (xargs :stobjs state))
  (and (or (equal (mfc-current-literal mfc state)
                  (cons t term)))
       (or (null (mfc-ancestors mfc)))))

(defmacro rewriting-negative-literal (term)
  `(syntaxp (rewriting-negative-literal-fn ,term mfc state)))

(defun print-mfc (name mfc state)
  (declare (xargs :stobjs state)
           (ignore state))
  (cw "~x0 mfc: ~X12~%" name
      mfc
      (evisc-tuple
       nil nil
       `((,(access metafunction-context mfc :wrld) . "<world>")
         (,(access rewrite-constant
                   (access metafunction-context mfc :rcnst)
                   :current-enabled-structure) "<ens>")) nil)))

;; Arrgh, I'm not really sure how to craft theorems with must-fail/etc that
;; will ensure this is working properly, in case ACL2's MFC representation
;; changes.

;; (logic)

;; (encapsulate
;;   (((hyp *) => *)
;;    ((foo * * *) => *))
;;   (local (defun hyp (x) (declare (ignore x)) nil))
;;   (local (defun foo (x y z) (declare (ignore x y z)) t))
;;   (defthmd constraint
;;     (implies (hyp x) (foo x y z))))

;; (defthm rule1
;;   (implies (and (rewriting-positive-literal `(foo ,x ,y ,z))
;;                 (hyp x))
;;            (foo x y z))
;;   :hints(("Goal" :in-theory (enable constraint))))

;; (defthm test1
;;   (implies (and (posp z)
;;                 (consp y)
;;                 (hyp x)
;;                 (foo x y z))
;;            x)
;;   :rule-classes nil))


;; (defthm test1
;;   (implies (hyp x)
;;            (foo x y z))
;;   :rule-classes nil))

;; (defthm test2
;;   (implies (hyp x)
;;            (not (foo x y z)))
;;   :rule-classes nil))




