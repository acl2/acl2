

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

(defn t-aig-fix (a)
  ;; Converts floating or u values to x values.
  (b* (((faig a1 a0) a))
    (cons (aig-not (aig-and a0 (aig-not a1)))
          (aig-not (aig-and a1 (aig-not a0))))))



(defn t-aig-not (a)
  (b* (((faig a1 a0) a))
    (cons a0 a1)))



(defn f-aig-not (a)
  (b* (((faig a1 a0) a))
    (cons (aig-not (aig-and a1 (aig-not a0)))
          (aig-not (aig-and a0 (aig-not a1))))))


(defn t-aig-and (a b)
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b))
    (cons (aig-and a1 b1)
          (aig-or  a0 b0))))


(defn f-aig-and (a b)
  (let ((a (t-aig-fix a))
        (b (t-aig-fix b)))
    (t-aig-and a b)))



(defn t-aig-or (a b)
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b))
    (cons (aig-or  a1 b1)
          (aig-and a0 b0))))



(defn f-aig-or (a b)
  (let ((a (t-aig-fix a))
        (b (t-aig-fix b)))
    (t-aig-or a b)))



(defn t-aig-xor (a b)
  (t-aig-or (t-aig-and a (t-aig-not b))
            (t-aig-and (t-aig-not a) b)))

(defn t-aig-iff (a b)
  (t-aig-or (t-aig-and a b)
            (t-aig-and (t-aig-not a) (t-aig-not b))))



(defn f-aig-res (x y)
  (b* (((faig x1 x0) x)
       ((faig y1 y0) y))
    (cons (aig-or x1 y1)
          (aig-or x0 y0))))

(defn f-aig-wire (a b)
  (f-aig-res a b))


(defn f-aig-xor (a b)
  (let ((a (t-aig-fix a))
        (b (t-aig-fix b)))
    (t-aig-xor a b)))

(defn f-aig-iff (a b)
  (let ((a (t-aig-fix a))
        (b (t-aig-fix b)))
    (t-aig-iff a b)))



(defn t-aig-ite (c a b)
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b)
       ((faig c1 c0) c))
    (cons (aig-or (aig-and c1 a1)
                  (aig-and c0 b1))
          (aig-or (aig-and c1 a0)
                  (aig-and c0 b0)))))



(defn f-aig-ite (c a b)  ;;  Even if C is unknown, when A=B, then A
  (let* ((c (t-aig-fix c))
         (a (t-aig-fix a))
         (b (t-aig-fix b)))
    (t-aig-ite c a b)))


(defn t-aig-ite* (c a b)
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b)
       ((faig c1 c0) c)
       (x (aig-and c1 c0)))
    (cons (aig-or x (aig-or (aig-and c1 a1)
                            (aig-and c0 b1)))
          (aig-or x (aig-or (aig-and c1 a0)
                            (aig-and c0 b0))))))



(defn f-aig-ite* (c a b) ;;  Even if C is unknown, when A=B, then A
  (let* ((c (t-aig-fix c))
         (a (t-aig-fix a))
         (b (t-aig-fix b)))
    (t-aig-ite* c a b)))


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



(defn f-aig-pullup (a)
  (b* (((faig a1 a0) a)
       (a-not-aig-floating (aig-or a1 a0))
       (a-floating (aig-not a-not-aig-floating)))
    (cons (aig-or a-floating a1) a0)))


(defn f-aig-bi-buf (cntl in bus)
  (f-aig-wire (t-aig-buf cntl in) bus))


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
