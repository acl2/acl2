; A lightweight book about the built-in function resize-list
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Resize list is used by stobjs that have resizable array fields.

(local (include-book "nth"))
(local (include-book "len"))

(in-theory (disable resize-list))

;; param names match std
(defthm len-of-resize-list
  (equal (len (resize-list lst n default))
         (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm consp-of-resize-list
  (equal (consp (resize-list lst n default))
         (posp n))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm car-of-resize-list
  (implies (natp n)
           (equal (car (resize-list lst n default))
                  (if (< 0 n)
                      (if (consp lst)
                          (car lst)
                        default)
                    nil)))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm resize-list-of-0
  (equal (RESIZE-LIST LST 0 DEFAULT)
         nil)
  :hints (("Goal" :in-theory (enable resize-list))))

(local
 (defun cdr-sub1-sub1-induct (m n x)
   (if (or (zp m)
           ;(endp x)
           )
       (list m n x)
     (cdr-sub1-sub1-induct (+ -1 m) (+ -1 n) (cdr x)))))

(defthm resize-list-when-not-consp
  (implies (and (syntaxp (not (equal lst ''nil)))
                (not (consp lst)))
           (equal (resize-list lst new-len default)
                  (resize-list nil new-len default)))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm nth-of-resize-list-2 ; avoid name clash with std
  (equal (nth n (resize-list lst new-len default))
         (if (< (nfix n) (nfix new-len))
             (if (< (nfix n) (len lst))
                 (nth (nfix n) lst)
               default)
           nil))
  :hints (("Goal" :expand ((resize-list nil new-len default)
                           (resize-list lst new-len default))
           :induct (cdr-sub1-sub1-induct n new-len lst))))

(defthm resize-list-of-update-nth
  (implies (< (nfix n) (len lst)) ; the update-nth was in bounds
           (equal (resize-list (update-nth n val lst) new-len default)
                  (if (< (nfix n) (nfix new-len))
                      (update-nth n val (resize-list lst new-len default))
                    (resize-list lst new-len default))))
  :hints (("Goal" :induct (cdr-sub1-sub1-induct n new-len lst)
           :in-theory (e/d (resize-list)
                           (nth-of-cdr)))))
