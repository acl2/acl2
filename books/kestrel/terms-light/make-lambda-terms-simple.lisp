; Making a list of lambda terms
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-lambda-term-simple")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(include-book "kestrel/evaluators/empty-eval" :dir :system)
;tood: reduce:
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))
(local (include-book "../lists-light/subsetp-equal"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; For each of the TERMS, wraps it in a lambda that binds the formals to the args
(defund make-lambda-terms-simple (lambda-formals args terms)
  (if (endp terms)
      nil
    (cons (make-lambda-term-simple lambda-formals args (first terms))
          (make-lambda-terms-simple lambda-formals args (rest terms)))))

(defthm make-lambda-terms-simple-of-nil
  (equal (make-lambda-terms-simple lambda-formals args nil)
         nil)
  :hints (("Goal" :in-theory (enable make-lambda-terms-simple))))

;move?
(defthm empty-eval-of-make-lambda-term-simple-when-symbolp
  (implies (and (symbolp var)
;                (symbol-listp lambda-formals)
;                (pseudo-term-listp args)
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (make-lambda-term-simple lambda-formals args var) a)
                  (if (equal var nil) ; gross exception in defevaluator
                      nil
                    (if (member-equal var lambda-formals)
                        (empty-eval (cdr (assoc-equal var (pairlis$ lambda-formals args))) ; todo: use lookup-equal?
                                     a)
                      (empty-eval var a)))))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple
                                     ;;assoc-equal-iff-member-equal-of-strip-cars
                                     empty-eval-of-cdr-of-assoc-equal
                                     lookup-equal))))

(defthm empty-eval-of-make-lambda-term-simple-when-symbolp
  (implies (and (symbolp var)
;                (symbol-listp lambda-formals)
;                (pseudo-term-listp args)
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (make-lambda-term-simple lambda-formals args var) a)
                  (if (equal var nil) ; gross exception in defevaluator
                      nil
                    (if (member-equal var lambda-formals)
                        (empty-eval (cdr (assoc-equal var (pairlis$ lambda-formals args))) ; todo: use lookup-equal?
                                     a)
                      (empty-eval var a)))))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple
                                     ;;assoc-equal-iff-member-equal-of-strip-cars
                                     empty-eval-of-cdr-of-assoc-equal
                                     lookup-equal))))

;; In case car-of-assoc-equal-strong is too strong?
;; (defthm equal-of-car-of-assoc-equal-same
;;   (implies (alistp alist)
;;            (iff (equal key (car (assoc-equal key alist)))
;;                 (or (equal key nil)
;;                     (assoc-equal key alist)))))

;; (defun cdr-remove-caar-induct-2 (x y)
;;   (if (or (endp x)
;;           (endp y))
;;       (list x y)
;;     (cdr-remove-caar-induct-2 (cdr x) (remove-equal (caar x) y))))

(local
 (defthm assoc-equal-of-pairlis$-of-map-lookup-equal-same
  (implies (alistp alist)
           (equal (assoc-equal key (pairlis$ keys (map-lookup-equal keys alist)))
                  (if (member-equal key keys)
                      (cons key (cdr (assoc-equal key alist)))
                    nil)))
  :hints (("Goal" :in-theory (enable assoc-equal map-lookup-equal pairlis$ LOOKUP-EQUAL)))))

(local
 (defthm alists-equiv-on-of-pairlis$-of-map-lookup-equal-same
  (alists-equiv-on keys
                   (pairlis$ keys (map-lookup-equal keys a))
                   a)
  :hints (("Goal" :expand (ALISTS-EQUIV-ON KEYS
                                           (PAIRLIS$ KEYS (MAP-LOOKUP-EQUAL KEYS A))
                                           A)
           :induct t
           ;;:induct (ALISTS-EQUIV-ON KEYS a a)
           :in-theory (enable pairlis$ lookup-equal
                              map-lookup-equal
                              assoc-equal-iff-member-equal-of-strip-cars
                              (:I len))))))

;; term may have free vars not among the lambda formals
(defthm empty-eval-of-make-lambda-term-simple
  (implies (and (pseudo-termp term)
                (not (member-equal nil (free-vars-in-term term))) ;drop? may need the notion of alists agreeing on a set of keys not involving nil
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (make-lambda-term-simple lambda-formals args term) a)
                  (empty-eval term
                               (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                       a))))
  :hints (("Goal" :in-theory (e/d (make-lambda-term-simple) ((:i len)
                                                             ;; why these?:
                                                             alists-equiv-on-of-append-arg1
                                                             alists-equiv-on-of-append-arg2)))))


;todo: split out
(defthm empty-eval-list-of-make-lambda-terms-simple
  (implies (and (pseudo-term-listp terms)
                (not (member-equal nil (free-vars-in-terms terms))) ;drop?
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval-list (make-lambda-terms-simple lambda-formals args terms) a)
                  (empty-eval-list terms
                                    (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                            a))))
  :hints (("Goal" :in-theory (enable make-lambda-terms-simple map-lookup-equal))))
