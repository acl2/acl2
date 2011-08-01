; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
;
; July 2011, Jared added some documentation and merged in the
; faig-op-commutativity theorems.

(in-package "ACL2")

(include-book "base")
(include-book "tools/bstar" :dir :system)
(include-book "tools/rulesets" :dir :system)

(defconst *4x* (hons t t))
(defconst *4z* (hons nil nil))
(defconst *4t* (hons t nil))
(defconst *4f* (hons nil t))


(def-b*-binder faig
  ":doc-section B*-BINDERS
Binds two variables to the onset and offset, respectively, of the faig-fix
of the given expression.~/~/~/"
  (declare (xargs :guard (and (true-listp args)
                              (equal (len args) 2)
                              (true-listp forms)
                              (equal (len forms) 1))))
  `(b* (((mv ,(first args) ,(second args))
         (let ((x (faig-fix ,(car forms))))
           (mv (car x) (cdr x)))))
     ,rest-expr))


(defxdoc faig-constructors
  :parents (faig)
  :short "Low-level functions for constructing FAIGs."

  :long "<p>In many cases, it is possible to more efficiently construct FAIGs
when it is known that the input FAIGs cannot evaluate to Z.  This is something
that holds of the outputs of most logic gates, e.g., a NOT gate might produce
an X, but it will never produce a Z.</p>

<p>Because of this, we have two versions of most of our FAIG constructors.  The
<tt>t-aig-*</tt> functions make the assumption that their inputs are
non-floating and can never evaluate to Z, and are more efficient.  The
<tt>f-aig-*</tt> functions do not make this assumption and can operate on any
FAIG inputs, but are not as efficient and yield larger FAIGs.</p>")




; Macro to prove the FAIG constructors commute over FAIG-EVAL.

(defun pfoc-faig-eval-args (args)
  (if (atom args)
      nil
    (cons (list 'faig-eval (car args) 'env)
          (pfoc-faig-eval-args (cdr args)))))

(defun pfoc-arg-casesplit-list (args)
  (if (atom args)
      nil
    (list* `(and stable-under-simplificationp
                 '(:cases ((aig-eval (car ,(car args)) env))))
           `(and stable-under-simplificationp
                 '(:cases ((aig-eval (cdr ,(car args)) env))))
           (pfoc-arg-casesplit-list (cdr args)))))

(defmacro prove-faig-op-commutes (op args)
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string "FAIG-EVAL-OF-" (symbol-name op))
             op)
     (equal (faig-eval (,op . ,args) env)
            (,op . ,(pfoc-faig-eval-args args)))
     :hints ,(pfoc-arg-casesplit-list args)))





(defsection t-aig-fix
  ;; BOZO should probably rename this to f-aig-unfloat
  :parents (faig-constructors)
  :short "Unfloat operation, converts floating (Z) values to unknown (X)
values."
  :long "<p>See also @(see 4v-unfloat); this is the analagous function for
FAIGs.</p>"

  (defn t-aig-fix (a)
    (b* (((faig a1 a0) a))
      (cons (aig-not (aig-and a0 (aig-not a1)))
            (aig-not (aig-and a1 (aig-not a0))))))

  (prove-faig-op-commutes t-aig-fix (a)))



(defsection t-aig-not
  :parents (faig-constructors)
  :short "@(call t-aig-not) negates the FAIG <tt>a</tt>, assuming that it
cannot evaluate to Z."

  (defn t-aig-not (a)
    (b* (((faig a1 a0) a))
      (cons a0 a1)))

  (prove-faig-op-commutes t-aig-not (a)))


(defsection f-aig-not
  :parents (faig-constructors)
  :short "@(call f-aig-not) negates the FAIG <tt>a</tt>."

  (defn f-aig-not (a)
    (b* (((faig a1 a0) a))
      (cons (aig-not (aig-and a1 (aig-not a0)))
            (aig-not (aig-and a0 (aig-not a1))))))

  (prove-faig-op-commutes f-aig-not (a)))




(defsection t-aig-and
  :parents (faig-constructors)
  :short "@(call t-aig-and) <i>and</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>, assuming they cannot evaluate to Z."

  (defn t-aig-and (a b)
    (b* (((faig a1 a0) a)
         ((faig b1 b0) b))
      (cons (aig-and a1 b1)
            (aig-or  a0 b0))))

  (prove-faig-op-commutes t-aig-and (a b)))

(defsection f-aig-and
  :parents (faig-constructors)
  :short "@(call f-aig-and) <i>and</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>."

  (defn f-aig-and (a b)
    (let ((a (t-aig-fix a))
          (b (t-aig-fix b)))
      (t-aig-and a b)))

  (prove-faig-op-commutes f-aig-and (a b)))




(defsection t-aig-or
  :parents (faig-constructors)
  :short "@(call t-aig-or) <i>or</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>, assuming they cannot evaluate to Z."

  (defn t-aig-or (a b)
    (b* (((faig a1 a0) a)
         ((faig b1 b0) b))
      (cons (aig-or  a1 b1)
            (aig-and a0 b0))))

  (prove-faig-op-commutes t-aig-or (a b)))

(defsection f-aig-or
  :parents (faig-constructors)
  :short "@(call f-aig-or) <i>or</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>."

  (defn f-aig-or (a b)
    (let ((a (t-aig-fix a))
          (b (t-aig-fix b)))
      (t-aig-or a b)))

  (prove-faig-op-commutes f-aig-or (a b)))



(defsection t-aig-xor
  :parents (faig-constructors)
  :short "@(call t-aig-xor) <i>xor</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>, assuming they cannot evaluate to Z."

  (defn t-aig-xor (a b)
    (t-aig-or (t-aig-and a (t-aig-not b))
              (t-aig-and (t-aig-not a) b)))

  (prove-faig-op-commutes t-aig-xor (a b)))

(defsection f-aig-xor
  :parents (faig-constructors)
  :short "@(call f-aig-xor) <i>xor</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>."

  (defn f-aig-xor (a b)
    (let ((a (t-aig-fix a))
          (b (t-aig-fix b)))
      (t-aig-xor a b)))

  (prove-faig-op-commutes f-aig-xor (a b)))



(defsection t-aig-iff
  :parents (faig-constructors)
  :short "@(call t-aig-iff) <i>iff</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>, assuming they cannot evaluate to Z."

  (defn t-aig-iff (a b)
    (t-aig-or (t-aig-and a b)
              (t-aig-and (t-aig-not a) (t-aig-not b))))

  (prove-faig-op-commutes t-aig-iff (a b)))


(defsection f-aig-iff
  :parents (faig-constructors)
  :short "@(call f-aig-iff) <i>iff</i>s together the FAIGs <tt>a</tt> and
<tt>b</tt>."

  (defn f-aig-iff (a b)
    (let ((a (t-aig-fix a))
          (b (t-aig-fix b)))
      (t-aig-iff a b)))

  (prove-faig-op-commutes f-aig-iff (a b)))




(defsection t-aig-ite
  :parents (faig-constructors)
  :short "@(call t-aig-ite) constructs a (less conservative) FAIG representing
<tt>(if c a b)</tt>, assuming these input FAIGs cannot evaluate to Z."

  :long "<p>This is a less-conservative version of @(see t-aig-ite*) that emits
<tt>a</tt> in the case that <tt>c</tt> is unknown but <tt>a = b</tt>.  See
@(see 4v-ite) for discussion related to this issue.</p>"

  (defn t-aig-ite (c a b)
    (b* (((faig a1 a0) a)
         ((faig b1 b0) b)
         ((faig c1 c0) c))
      (cons (aig-or (aig-and c1 a1)
                    (aig-and c0 b1))
            (aig-or (aig-and c1 a0)
                    (aig-and c0 b0)))))

  (prove-faig-op-commutes t-aig-ite (c a b)))

(defsection f-aig-ite
  :parents (faig-constructors)
  :short "@(call f-aig-ite) constructs a (less conservative) FAIG representing
<tt>(if c a b)</tt>."

  :long "<p>This is a less-conservative version of @(see f-aig-ite*) that emits
<tt>a</tt> in the case that <tt>c</tt> is unknown but <tt>a = b</tt>.  See
@(see 4v-ite) for discussion related to this issue.</p>"

  (defn f-aig-ite (c a b)
    (let* ((c (t-aig-fix c))
           (a (t-aig-fix a))
           (b (t-aig-fix b)))
      (t-aig-ite c a b)))

  (prove-faig-op-commutes f-aig-ite (c a b)))



(defsection t-aig-ite*
  :parents (faig-constructors)
  :short "@(call t-aig-ite*) constructs a (more conservative) FAIG representing
<tt>(if c a b)</tt>, assuming these input FAIGs cannot evaluate to Z."

  :long "<p>This is a more-conservative version of @(see t-aig-ite) that emits
<tt>X</tt> in the case that <tt>c</tt> is unknown, even when <tt>a = b</tt>.
See @(see 4v-ite) for discussion related to this issue.</p>"

  (defn t-aig-ite* (c a b)
    (b* (((faig a1 a0) a)
         ((faig b1 b0) b)
         ((faig c1 c0) c)
         (x (aig-and c1 c0)))
      (cons (aig-or x (aig-or (aig-and c1 a1)
                              (aig-and c0 b1)))
            (aig-or x (aig-or (aig-and c1 a0)
                              (aig-and c0 b0))))))

  (prove-faig-op-commutes t-aig-ite* (c a b)))

(defsection f-aig-ite*
  :parents (faig-constructors)
  :short "@(call f-aig-ite*) constructs a (more conservative) FAIG representing
<tt>(if c a b)</tt>, assuming these input FAIGs cannot evaluate to Z."

  :long "<p>This is a more-conservative version of @(see f-aig-ite) that emits
<tt>X</tt> in the case that <tt>c</tt> is unknown, even when <tt>a = b</tt>.
See @(see 4v-ite) for discussion related to this issue.</p>"

  (defn f-aig-ite* (c a b)
    (let* ((c (t-aig-fix c))
           (a (t-aig-fix a))
           (b (t-aig-fix b)))
      (t-aig-ite* c a b)))

  (prove-faig-op-commutes f-aig-ite* (c a b)))




(defn f-aig-res (x y)
  (b* (((faig x1 x0) x)
       ((faig y1 y0) y))
    (cons (aig-or x1 y1)
          (aig-or x0 y0))))

(prove-faig-op-commutes f-aig-res (a b))

(defn f-aig-wire (a b)
  (f-aig-res a b))





;; Theorem: no T-AIG-FIX needed around the answer of f-aig-ite.
;; (thm
;;      (and
;;       (iff (aig-eval (car (t-aig-fix (t-aig-ite (t-aig-fix c)
;;                                                 (t-aig-fix a)
;;                                                 (t-aig-fix b))))
;;                      al)
;;            (aig-eval (car (t-aig-ite (t-aig-fix c)
;;                                      (t-aig-fix a)
;;                                      (t-aig-fix b)))
;;                      al))
;;       (iff (aig-eval (cdr (t-aig-fix (t-aig-ite (t-aig-fix c)
;;                                                 (t-aig-fix a)
;;                                                 (t-aig-fix b))))
;;                      al)
;;            (aig-eval (cdr (t-aig-ite (t-aig-fix c)
;;                                      (t-aig-fix a)
;;                                      (t-aig-fix b)))
;;                      al))))
     

(defn t-aig-buf (c a)
  ;; onset  of output is (not (or (and (not con) coff) (and con (not coff) (not aon) aoff)))
  ;; offset of output is (not (or (and (not con) coff) (and con (not coff) aoff (not aon))))
  (b* (((faig a1 a0) a)
       ((faig c1 c0) c)
       (float (aig-and (aig-not c1) c0))
       (set   (aig-and c1 (aig-not c0)))
       (on    (aig-and (aig-not a0) a1))
       (off   (aig-and (aig-not a1) a0)))
    (cons (aig-and (aig-not float) (aig-not (aig-and set off)))
          (aig-and (aig-not float) (aig-not (aig-and set on))))))

(prove-faig-op-commutes t-aig-buf (c a))


(defn f-aig-pullup (a)
  (b* (((faig a1 a0) a)
       (a-not-aig-floating (aig-or a1 a0))
       (a-floating (aig-not a-not-aig-floating)))
    (cons (aig-or a-floating a1) a0)))

(prove-faig-op-commutes f-aig-pullup (a))


(defn f-aig-bi-buf (cntl in bus)
  (f-aig-wire (t-aig-buf cntl in) bus))

(prove-faig-op-commutes f-aig-bi-buf (c a b))

(def-ruleset f-aig-defs
  '(t-aig-fix f-aig-not f-aig-and f-aig-or f-aig-xor f-aig-iff
              f-aig-res f-aig-ite f-aig-ite*
              t-aig-buf f-aig-pullup f-aig-bi-buf))

(def-ruleset t-aig-defs
  '(t-aig-and t-aig-iff t-aig-ite t-aig-ite* t-aig-not t-aig-or t-aig-xor))













;; VUAIG: Pairs of AIGs of the form <value, undef>, encoding 1/0/X/F as
;; follows:
;;  V   U   |  meaning
;; ---------|----------
;;  t  nil  |    1
;; nil nil  |    0
;;  t   t   |    X
;; nil  t   |    F

;; fix to three-valued, i.e. coerce F to X
(defn vuaig-tfix (x)
  (b* (((faig v u) x))
    (cons (aig-or v u) u)))

(defn vuaig-not (x)
  (b* (((faig v u) x))
    (cons (aig-or (aig-not v) u) u)))

(defn vuaig-and (x y)
  (b* (((faig vx ux) x)
       ((faig vy uy) y))
    (let ((x (aig-or (aig-and ux uy)
                     (aig-or (aig-and ux vy)
                             (aig-and uy vx)))))
      (cons (aig-or (aig-and vx vy) x) x))))


(defn vuaig-or (x y)
  (b* (((faig vx ux) x)
       ((faig vy uy) y))
    (let ((x (aig-or (aig-and ux uy)
                     (aig-or (aig-and ux (aig-not vy))
                             (aig-and uy (aig-not vx))))))
      (cons (aig-or (aig-or vx vy) x) x))))

(defn vuaig-xor (x y)
  (b* (((faig vx ux) x)
       ((faig vy uy) y))
    (let ((x (aig-or ux uy)))
      (cons (aig-or (aig-xor vx vy) x) x))))

(defn vuaig-iff (x y)
  (b* (((faig vx ux) x)
       ((faig vy uy) y))
    (let ((x (aig-or ux uy)))
      (cons (aig-or (aig-iff vx vy) x) x))))

(defn vuaig-res (x y)
  (b* (((faig vx ux) x)
       ((faig vy uy) y))
    (cons (aig-or vx vy)
          (aig-or (aig-or (aig-and (aig-not (aig-or ux uy))
                                   (aig-xor vx vy))
                          (aig-and ux uy))
                  (aig-or (aig-and ux vx)
                          (aig-and uy vy))))))


(defn vuaig-ite (c a b)
  (b* (((faig va ua) a)
       ((faig vb ub) b)
       ((faig vc uc) c))
    (let* ((x (aig-or (aig-or (aig-and uc ua)
                              (aig-and uc ub))
                      (aig-or (aig-and uc (aig-xor va vb))
                              (aig-ite vc ua ub)))))
      (cons (aig-or (aig-ite vc va vb) x) x))))


(defn vuaig-tbuf (c a)
  (b* (((faig va ua) a)
       ((faig vc uc) c))
    (let* ((float (aig-and (aig-not vc) (aig-not uc)))
           (x     (aig-or uc (aig-and ua (aig-not float)))))
      (cons (aig-or (aig-and va (aig-not float)) x)
            (aig-or uc (aig-or (aig-not vc) ua))))))

(defn vuaig-pullup (a)
  (b* (((faig va ua) a)
       (floating (aig-and (aig-not va) ua)))
    (cons (aig-or va floating)
          (aig-and ua (aig-not floating)))))


(defn vuaig-bi-buf (cntl in bus)
  (vuaig-res (vuaig-tbuf cntl in) bus))

(defun to-vu (code)
  (case code
    (1 '(t   . nil))
    (0 '(nil . nil))
    (x '(t   . t))
    (z '(nil . t))))

(defun from-vu (vu)
  (cond ((equal vu '(t   . nil)) 1)
        ((equal vu '(nil . nil)) 0)
        ((equal vu '(t   . t))   'x)
        ((equal vu '(nil . t))   'z)))

(defun to-fv (code)
  (case code
    (1 '(t   . nil))
    (0 '(nil . t))
    (x '(t   . t))
    (z '(nil . nil))))

(defun from-fv (vu)
  (cond ((equal vu '(t   . nil)) 1)
        ((equal vu '(nil . nil)) 'z)
        ((equal vu '(t   . t))   'x)
        ((equal vu '(nil . t))   0)))








(defn vxz (v x z)
  (cons v (and (or z x) (cons x z))))

(defmacro patbind-vxz (args forms rest-expr)
  `(b* ((,(car args) (ec-call (car ,(car forms))))
        (patbind-vxz-xz-do-not-use (ec-call (cdr ,(car forms))))
        (,(cadr args) (ec-call (car patbind-vxz-xz-do-not-use)))
        (,(caddr args) (ec-call (cdr patbind-vxz-xz-do-not-use))))
     (check-vars-not-free
      (patbind-vxz-xz-do-not-use)
      ,rest-expr)))


(defn vxzaig-tfix (a)
  (b* (((vxz v x z) a))
    (vxz v (aig-or z x) nil)))

(defn vxzaig-not (a)
  (b* (((vxz v x z) a))
    (vxz (aig-not v) (aig-or z x) nil)))

(defn vxzaig-and (a b)
  (b* (((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (xa (aig-or za xa))
       (xb (aig-or zb xb))
       (x (aig-or (aig-and xa xb)
                  (aig-or (aig-and xa vb)
                          (aig-and xb va)))))
    (vxz (aig-and va vb) x nil)))


(defn vxzaig-or (a b)
  (b* (((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (xa (aig-or za xa))
       (xb (aig-or zb xb))
       (x (aig-or (aig-and xa xb)
                  (aig-or (aig-and xa (aig-not vb))
                          (aig-and xb (aig-not va))))))
    (vxz (aig-or va vb) x nil)))

(defn vxzaig-xor (a b)
  (b* (((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (xa (aig-or za xa))
       (xb (aig-or zb xb))
       (x (aig-or xa xb)))
    (vxz (aig-xor va vb) x nil)))

(defn vxzaig-iff (a b)
  (b* (((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (xa (aig-or za xa))
       (xb (aig-or zb xb))
       (x (aig-or xa xb)))
    (vxz (aig-iff va vb) x nil)))

(defn vxzaig-res (a b)
  (b* (((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (za (aig-and za (aig-not xa)))
       (zb (aig-and zb (aig-not xb)))
       (z (aig-and za zb)))
    (vxz (aig-ite za vb va)
         (aig-or (aig-or xa xb)
                   (aig-and (aig-not (aig-or za zb))
                            (aig-xor va vb))) z)))

(defn vxzaig-ite (c a b)
  (b* (((vxz vc xc zc) c)
       ((vxz va xa za) a)
       ((vxz vb xb zb) b)
       (- (cw "~x0 ~x1 ~x2 ~x3 ~x4 ~x5 ~x6 ~x7 ~x8~%"
              vc xc zc va xa za vb xb zb))
       (xc (aig-or zc xc))
       (xa (aig-or za xa))
       (xb (aig-or zb xb)))
    (vxz (aig-ite vc va vb)
         (aig-ite xc (aig-or (aig-or xa xb)
                             (aig-xor va vb))
                  (aig-ite vc xa xb))
         nil)))

(defn vxzaig-tbuf (c a)
  (b* (((vxz vc xc zc) c)
       ((vxz va xa za) a)
       (xc (aig-or zc xc))
       (xa (aig-or za xa)))
    (vxz va (aig-or xc (aig-and vc xa))
         (aig-ite xc
                     (aig-not xa)
                     (aig-not vc)))))



(defun from-vxz (a)
  (b* (((vxz v x z) a))
    (if x 'x (if z 'z (if v 1 0)))))





(defconst *vu1* (hons t nil))   ; *4t*
(defconst *vu0* (hons nil nil)) ; *4u*


(defconst *vuT* *vu1*)
(defconst *vuF* *vu0*)
(defconst *vuX* (hons t t))     ; *4x*
(defconst *vuZ* (hons nil t))   ; *4f*
(defconst *vuU* (hons nil t))   ; *4f*
