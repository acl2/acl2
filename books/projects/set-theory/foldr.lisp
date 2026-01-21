; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many of the examples below were inspired by community book
; books/projects/apply/report.lisp.

(in-package "ZF")

(include-book "zify")

(defun foldr (lst fn init)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      init
    (apply fn
           (list (car lst)
                 (foldr (cdr lst) fn init)))))

(extend-zfc-table foldr-prop zify-prop v$prop acl2$prop)

(zify* zbinary-* binary-* 2)

(thmz (implies (and (acl2p x)
                    (acl2p y))
               (equal (apply (zbinary-*) (list x y))
                      (* x y)))
      :props (foldr-prop zbinary-*$prop))

(defun timeslist (x)
  (declare (xargs :guard (acl2-number-listp x)))
  (cond ((endp x) 1)
        (t (* (car x)
              (timeslist (cdr x))))))

(thmz (implies (acl2p lst)
               (equal (foldr lst (zbinary-*) 1)
                      (timeslist lst)))
      :props (foldr-prop zbinary-*$prop acl2$prop))

; Execution test:

(thmz (implies (acl2p lst)
               (equal (foldr '(2 3 5) (zbinary-*) 1)
                      30))
      :props (foldr-prop zbinary-*$prop acl2$prop))

(zify* zcons* cons 2)

(thmz (implies (and (acl2p lst)
                    (acl2p init))
               (equal (foldr lst (zcons*) init)
                      (append lst init)))
      :props (foldr-prop zcons*$prop))

(zify* zmax* max 2)

(defthmz acl2p-foldr-zmax*
  (implies (and (acl2p lst)
                (acl2p init))
           (acl2p (foldr lst (zmax*) init)))
  :props (foldr-prop zmax*$prop))

(thmz (implies (and (acl2p lst)
                    (acl2p init))
               (>= (foldr lst (zmax*) init)
                   init))
      :props (foldr-prop zmax*$prop))

(thmz (implies (and (acl2p lst)
                    (acl2p init)
                    (member x lst))
               (>= (foldr lst (zmax*) init)
                   x))
      :props (foldr-prop zmax*$prop))

(thmz (implies (and (acl2p lst)
                    (acl2p init))
               (or (equal (foldr lst (zmax*) init)
                          init)
                   (member (foldr lst (zmax*) init)
                           lst)))
      :props (foldr-prop zmax*$prop))

(defthm rational-listp-implies-acl2p
  (implies (rational-listp x)
           (acl2p x)))

(thmz (implies (and (rational-listp lst)
                    (rationalp init))
               (or (equal (foldr lst (zmax*) init)
                          init)
                   (member (foldr lst (zmax*) init)
                           lst)))
      :props (foldr-prop zmax*$prop))

(zify* zand* and 2
; The following avoids a name conflict.
       :fn* zf::and*)

(defthm member-preserves-acl2p
  (implies (and (member x lst)
                (acl2p lst))
           (acl2p x))
  :rule-classes (:rewrite :forward-chaining))

(defthmz acl2p-foldr-zand*
  (implies (acl2p lst)
           (acl2p (foldr lst (zand*) t)))
  :props (foldr-prop zand*$prop))

(thmz (implies (acl2p lst)
               (implies (foldr lst (zand*) t)
                        (implies (member x lst)
                                 x)))
      :props (foldr-prop zand*$prop))

(thmz (implies (acl2p lst)
               (implies (not (foldr lst (zand*) t))
                        (member nil lst)))
      :props (foldr-prop zand*$prop))

;;; Some of the events below will probably change -- see the comment in front
;;; of the last one.

(defun cons-fn (x y fn)
  (declare (xargs :guard t))
  (cons (apply fn x)
        y))

(defthm nth-expand
  (implies (and (syntaxp (quotep n))
                (posp n))
           (equal (nth n x)
                  (nth (1- n) (cdr x)))))

(defthmz in-apply
  (implies (and (subset fn (prod2 s1 s2))
                (in x s1)
                (in 0 s2))
           (in (apply fn x)
                s2))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable apply))))

(defthmz acl2p-apply
  (implies (and (subset fn (prod2 s1 (acl2)))
                (in x s1))
           (acl2p (apply fn x)))
  :props (foldr-prop)
  :hints (("Goal" :in-theory (enable apply))))

(defthmz acl2p-apply-acl2p
  (implies (and (subset fn (prod2 (acl2) (acl2)))
                (in x (acl2)))
           (acl2p (apply fn x)))
  :props (foldr-prop)
  :hints (("Goal" :in-theory (enable apply))))

(defthmz acl2p-map ; based on prove-acl2p
  (implies (and (subset f (prod2 (acl2) (acl2)))
                (acl2p lst))
           (acl2p (map f lst)))
  :props (foldr-prop))

(zify* zcons-fn* cons-fn 2
; A function from A to B is a set of ordered pairs <a,b> where a \in A and b
; \in B, hence a subset of A X B.
       :dom (prodn (acl2) (acl2))
       :params (fn)
       :props (v$prop acl2$prop)
       :xhyps ((subset fn (prod2 (acl2) (acl2)))))

(thmz (implies (and (subset f (prod2 (acl2) (acl2)))
                    (acl2p lst))
               (equal (foldr lst (zcons-fn* f) nil)
                      (map f lst)))
      :props (foldr-prop zcons-fn*$prop))

(defun filter (fn lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((apply fn (car lst))
         (cons (car lst) (filter fn (cdr lst))))
        (t (filter fn (cdr lst)))))

(defthmz acl2p-filter ; based on prove-acl2p
  (implies (acl2p lst)
           (acl2p (filter f lst))))

(defun cons-when-fn (x y fn)
  (declare (xargs :guard t))
  (if (apply fn x)
      (cons x y)
    y))

(zify* zcons-when-fn* cons-when-fn 2
; A function from A to B is a set of ordered pairs <a,b> where a \in A and b
; \in B, hence a subset of A X B.
       :dom (prodn (acl2) (acl2))
       :params (fn)
       :props (v$prop acl2$prop))

(thmz (implies (acl2p lst)
               (equal (foldr lst (zcons-when-fn* f) nil)
                      (filter f lst)))
      :props (foldr-prop zcons-fn*$prop zcons-when-fn*$prop))

; A computation example.

(zify zevenp evenp)

(thmz (equal (foldr '(1 4 9 16 25 36 100)
                     (zcons-when-fn* (zevenp))
                     nil)
             '(4 16 36 100))
      :props (foldr-prop zcons-when-fn*$prop zevenp$prop))

; A general property:

(defthm foldr-append
  (equal (foldr (append x y) f root)
         (foldr x f (foldr y f root))))
