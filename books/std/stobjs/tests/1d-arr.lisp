; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../1d-arr")


(encapsulate nil
  (defund widgp (x)
    (declare (xargs :guard t))
    (eq x 'the-default-widg))

  (defund widg-fix (x)
    (declare (Xargs :guard t))
    (if (widgp x)
        x
      'the-default-widg))

  (local (in-theory (enable widg-fix)))

  (defthm widgp-of-widg-fix
    (widgp (widg-fix x)))

  (defthm widg-fix-when-widgp
    (implies (widgp x)
             (equal (widg-fix x) x))))


;; test
(def-1d-arr widgarr
  :slotname widg
  :pred widgp
  :fix widg-fix
  :type-decl (satisfies widgp)
  :default-val the-default-widg)


(encapsulate nil
  (defund swidgp (x)
    (declare (xargs :guard t))
    (symbolp x))

  (defund swidg-fix (x)
    (declare (Xargs :guard t))
    (if (swidgp x)
        x
      'the-default-swidg))

  (local (in-theory (enable swidg-fix)))

  ;; (defthm swidgp-of-swidg-fix
  ;;   (swidgp (swidg-fix x)))

  (defthm swidg-fix-when-swidgp
    (implies (swidgp x)
             (equal (swidg-fix x) x))))


;; test
(def-1d-arr swidgarr
  :slotname swidg
  :pred swidgp
  :fix swidg-fix
  :type-decl (and symbol (satisfies swidgp))
  :pkg-sym xdoc::asdfs
  :default-val the-default-swidg)

;; default-val is not value to which we fix
(def-1d-arr swidgarr2
  :slotname swidg2
  :pred swidgp
  :fix swidg-fix
  :type-decl (and symbol (satisfies swidgp))
  :pkg-sym xdoc::asdfs
  :default-val the-default-swidg2)

(def-1d-arr objarr
  :slotname obj
  :default-val asdfa)

(def-1d-arr swidgarr3
  :slotname swidg3
  :pred swidgp
  :type-decl (and symbol (satisfies swidgp))
  :pkg-sym xdoc::asdfs
  :default-val the-default-swidg2)


#||


(def-universal-equiv widg-equiv
  :equiv-terms ((equal (widg-fix x))))


(def-universal-equiv widgs-equiv
  :qvars (i)
  :equiv-terms ((widg-equiv (nth i x))))

(defcong widgs-equiv widg-equiv (nth i x) 2
  :hints(("Goal" :in-theory (e/d (widgs-equiv-necc)
                                 (widg-equiv)))))

(defcong widgs-equiv widgs-equiv (update-nth i v x) 3
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defcong widg-equiv widgs-equiv (update-nth i v x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))


(defstobj widgarr$c
  (widgs$c :type (array (satisfies widgp) (0))
           :initially the-default-widg
           :resizable t)
  :inline t)


(defthm widgp-nth-of-widgs$cp
  (implies (and (widgs$cp x)
                (< (nfix n) (len x)))
           (widgp (nth n x))))

(defthm widgs$cp-of-update-nth
  (implies (and (widgs$cp x)
                (widgp v)
                (<= (nfix n) (len x)))
           (widgs$cp (update-nth n v x))))

(defthm widgs$cp-of-resize-list
  (implies (and (widgs$cp x)
                (widgp default))
           (widgs$cp (resize-list x n default))))

(defun widgarr$ap (widgarr$a)
  (declare (xargs :guard t)
           (ignorable widgarr$a))
  t)

(defun create-widgarr$a ()
  (declare (xargs :guard t))
  nil)

(defun widgs$a-length (widgarr$a)
  (declare (xargs :guard (widgarr$ap widgarr$a)
                  :verify-guards t))
  (len widgarr$a))

(defun resize-widgs$a (i widgarr$a)
  (declare (xargs :guard (widgarr$ap widgarr$a)))
  (resize-list widgarr$a i 'the-default-widg))

(defun widgs$ai (i widgarr$a)
  (declare (xargs :guard (and (widgarr$ap widgarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (widgs$a-length widgarr$a)))
                  :verify-guards t))
  (widg-fix (ec-call (nth i widgarr$a))))

(defun update-widgs$ai (i v widgarr$a)
  (declare (xargs :guard (and (widgarr$ap widgarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (widgs$a-length widgarr$a))
                              (widgp v))
                  :verify-guards t))
  (ec-call (update-nth i (widg-fix v) widgarr$a)))

(defun-nx widgarr$corr (widgarr$c widgarr$a)
  (and (widgarr$cp widgarr$c)
       (equal (len widgarr$a) (len (nth 0 widgarr$c)))
       (widgs-equiv widgarr$a (nth 0 widgarr$c))))

(local (in-theory (disable nth resize-list
                           (widgarr$corr))))

(local (set-default-hints
        '((and stable-under-simplificationp
               (let ((lit (car (last clause))))
                 (and (consp lit)
                      (eq (car lit) 'widgs-equiv)
                      `(:expand (,lit))))))))

(local (defthm nths-equal-by-widgs-equiv
         (implies (and (widgs-equiv x y)
                       (widgs$cp x)
                       (< (nfix i) (len x)))
                  (equal (equal (nth i x) (widg-fix (nth i y)))
                         t))
         :hints (("goal" :use widgs-equiv-necc
                  :in-theory (e/d (widg-equiv)
                                  (widgs-equiv-necc
                                   widgs-equiv-implies-widg-equiv-nth-2))
                  :do-not-induct t))))

(local (in-theory (enable nth-of-resize-list-split)))

(defabsstobj-events widgarr
  :exports ((widgs-length :exec widgs$c-length :logic widgs$a-length)
            (get-widg :exec widgs$ci :logic widgs$ai)
            (set-widg :exec update-widgs$ci :logic update-widgs$ai)
            resize-widgs))
||#
