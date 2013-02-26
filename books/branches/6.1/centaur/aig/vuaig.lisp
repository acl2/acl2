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

(in-package "ACL2")
(include-book "three-four")

; vuaig.lisp -- Jared split this out of three-four.lisp; I don't think we're
; actually using this stuff...


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





