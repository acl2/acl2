; Getting all defuns and defthms from the world.
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world-triplep")

;; Another way to do this would be to look at the event-landmarks (see books/kestrel/built-ins/collect.lisp).

;; Returns (mv defun-names defthm-names).  In the result, older defuns/defthms come first.
(defund defuns-and-defthms-in-world (world
                                     triple-to-stop-at ; may be nil
                                     whole-world defuns-acc defthms-acc)
  (declare (xargs :guard (and (plist-worldp world)
                              (plist-worldp whole-world)
                              (or (null triple-to-stop-at)
                                  (world-triplep triple-to-stop-at))
                              (true-listp defuns-acc)
                              (true-listp defthms-acc))))
  (if (endp world)
      (mv defuns-acc defthms-acc)
    (let ((triple (first world)))
      (if (equal triple triple-to-stop-at)
          (mv defuns-acc defthms-acc)
        (let ((symb (car triple))
              (prop (cadr triple)))
          (if (and (eq prop 'unnormalized-body)
                   ;; We assume anything with an 'unnormalized-body property is a defun:
                   (let ((still-definedp (fgetprop symb 'unnormalized-body nil whole-world))) ;todo: hack: make sure the function is still defined (why does this sometimes fail?)
                     (if (not still-definedp)
                         (prog2$ (cw "Note: ~x0 seems to no longer be defined." symb)
                                 nil)
                       t)))
              (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world (cons symb defuns-acc) defthms-acc)
            (if (eq prop 'theorem)
                ;; We assume anything with an 'theorem property is a defthm/defaxiom:
                (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world defuns-acc (cons symb defthms-acc))
              (defuns-and-defthms-in-world (rest world) triple-to-stop-at whole-world defuns-acc defthms-acc))))))))

(defthm symbol-listp-of-mv-nth-0-of-defuns-and-defthms-in-world
  (implies (and (plist-worldp world)
                (symbol-listp defuns-acc))
           (symbol-listp (mv-nth 0 (defuns-and-defthms-in-world world triple-to-stop-at whole-world defuns-acc defthms-acc))))
  :hints (("Goal" :in-theory (enable defuns-and-defthms-in-world))))

(defthm symbol-listp-of-mv-nth-1-of-defuns-and-defthms-in-world
  (implies (and (plist-worldp world)
                (symbol-listp defthms-acc))
           (symbol-listp (mv-nth 1 (defuns-and-defthms-in-world world triple-to-stop-at whole-world defuns-acc defthms-acc))))
  :hints (("Goal" :in-theory (enable defuns-and-defthms-in-world))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of all the names of defthms in the world.
;; TODO: This includes axiom names as well!
(defund defthms-in-world (world)
  (declare (xargs :guard (plist-worldp world)))
  (mv-let (defun-names defthm-names)
    (defuns-and-defthms-in-world world nil world nil nil)
    (declare (ignore defun-names))
    defthm-names))

(defthm symbol-listp-of-defthms-in-world
  (implies (plist-worldp world)
           (symbol-listp (defthms-in-world world)))
  :hints (("Goal" :in-theory (enable defthms-in-world))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of all the names of defuns in the world.
;; TODO: What about the primitives?  Should we use the 'formals property?
(defund defuns-in-world (world)
  (declare (xargs :guard (plist-worldp world)))
  (mv-let (defun-names defthm-names)
    (defuns-and-defthms-in-world world nil world nil nil)
    (declare (ignore defthm-names))
    defun-names))

(defthm symbol-listp-of-defuns-in-world
  (implies (plist-worldp world)
           (symbol-listp (defuns-in-world world)))
  :hints (("Goal" :in-theory (e/d (defuns-in-world) (mv-nth)))))
