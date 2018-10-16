;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "poly-proofs")
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "coi/defung/defung" :dir :system)

(defthm set-upper-bound-equiv-subset-p-rewrite
  (implies
   (and
    (subset-p target result)
    (syntaxp (not (equal target result))))
   (set-upper-bound-equiv target result)))

(defthm tru-dat
  (implies
   (and
    (subset-p list zed)
    (not (list::memberp a zed)))
   (not (list::memberp a list))))

(defthm try-this
  (implies
   (and
    (subset-p x y)
    (force (>-all varid y)))
   (>-all varid x))
  :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY))))

(defthm chaining-on-varid
  (implies
   (and
    (varid-p varid1)
    (>-all varid2 list)
    (varid-p varid2)
    (> varid1 varid2))
   (>-ALL varid1 list))
  :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY))))

(defthm empty-trapezoid-p
  (implies
   (not (consp zoid))
   (iff (trapezoid-p zoid)
        (null zoid))))

(defthm open-trapezoid-p
  (implies
   (consp zoid)
   (equal (trapezoid-p zoid)
          (let ((list zoid))
            (LET ((BV (CAR LIST)))
                 (AND (NORMALIZED-VARIABLEBOUND-P BV)
                      (VARIABLEBOUND-LISTP (CDR LIST))
                      (>-ALL (BOUND-VARID BV)
                             (ALL-BOUND-LIST-VARIABLES (CDR LIST)))
                      (TRAPEZOID-P (CDR LIST))))))))

(in-theory 
 (disable 
  trapezoid-p
  ;;variableBound-implication 
  ;;variableRelation-implication 
  <=-O-FIRST-EXPT-<=
  ))

(encapsulate
    ()

  (local
   (defthm >-all-from->->=all
     (IMPLIES (AND (>=ALL X LIST)              
                   (< X VARID)
                   (varid-p x)
                   (varid-p varid)
                   (varid-listp list))
              (>-ALL VARID LIST))))

  (defthm <-largest-varid-to-<-all
    (implies
     (and
      (consp list)
      (varid-p varid)
      (varid-listp list))
     (iff (< (largest-varid list) varid)
          (>-all varid list)))
    :hints (("Goal" ;; :induct (>-all varid list)
             :do-not-induct t
             :do-not '(generalize)
             :use largest-varid-is-largest
             :in-theory (e/d () (OPEN->=ALL-ON-MEMBERP
                                 OPEN-LARGEST-VARID-ON-MEMBERP
                                 largest-varid-is-largest)))))

  (defthm <=largest-varid-to-<=all
    (implies
     (and
      (consp list)
      (varid-p varid)
      (varid-listp list))
     (iff (< varid (largest-varid list))
          (not (>=all varid list))))
    :hints (("Goal" ;; :induct (>-all varid list)
             :do-not-induct t
             :do-not '(generalize)
             :use largest-varid-is-largest
             :in-theory (e/d () (OPEN->=ALL-ON-MEMBERP
                                 OPEN-LARGEST-VARID-ON-MEMBERP
                                 largest-varid-is-largest)))))

  )

(defthm consp-bound-varid-list
  (iff (consp (bound-varid-list list))
       (consp list)))

(in-theory (disable largest-varid))

(defthm equal-if->=all
  (implies
   (and
    (varid-p varid)
    (varid-listp list)
    (list::memberp varid list)
    (>=all varid list))
   (iff (equal varid (largest-varid list)) t))
  :hints (("Goal" :induct (largest-varid list)
           :expand (varid-listp list)
           :in-theory (e/d (largest-varid) (OPEN->=ALL-ON-MEMBERP)))))

;; ---------------------------------------------------------------------------------

(defmacro intersect-var-macro (var res cex)
  `(intersect :var ,var ,res ,cex))

(defmacro intersect-list-macro (list res cex)
  `(intersect :list ,list ,res ,cex))

(defmacro intersect-var-body (var res cex)
  `(let ((var ,var)
         (res ,res)
         (cex ,cex))
     (if (not (consp res)) (list var)
       (if (< (bound-varid (car res)) (bound-varid var)) (cons var res)
         (if (< (bound-varid var) (bound-varid (car res)))
             (cons (car res) (intersect-var-macro var (cdr res) cex))
           (metlist ((z zres) (andTrue-variableBound-variableBound var (car res) cex))
             (let ((res (intersect-list-macro zres (cdr res) cex)))
               (cons z res))))))))

(defmacro intersect-list-body (list res cex)
  `(let ((list ,list)
         (res  ,res)
         (cex  ,cex))
     (if (not (consp list)) res
       (let ((res (intersect-var-macro (car list) res cex)))
         (intersect-list-macro (cdr list) res cex)))))

;; ---------------------------------------------------------------------------------

(def::ung intersect (key arg res cex)
  (declare (xargs :default-value nil
                  :signature ((t (lambda (x) (if (equal key :var) (variableBound-p x) (variableBound-listp x))) variableBound-listp env-p) variableBound-listp)
                  :guard-hints (("Goal" :do-not-induct t)
                                (and stable-under-simplificationp
                                     '(:expand ((INTERSECT-0-DOMAIN KEY ARG RES CEX)
                                                (INTERSECT-0-DOMAIN :VAR ARG RES CEX)))))))
  (if (equal key :var)
      (intersect-var-body arg res cex)
    (intersect-list-body arg res cex)))

(defthm trapezoid-p-intersect
  (implies
   (and
    (if (equal key :var) (normalized-variableBound-p arg) (normalized-variableBound-listp arg))
    (trapezoid-p res)
    (env-p cex))
   (and
    (trapezoid-p (intersect key arg res cex))
    (subset-p (all-bound-list-variables (intersect key arg res cex))
              (append 
               (if (equal key :var) (all-bound-variables arg) (all-bound-list-variables arg))
               (all-bound-list-variables res)))))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :induct (intersect key arg res cex))))

(defthm set-upper-bound-equiv-all-bound-list-variables-intersect
  (implies
   (and
    (if (equal key :var) (normalized-variableBound-p arg) (normalized-variableBound-listp arg))
    (trapezoid-p res)
    (env-p cex))
   (set-upper-bound-equiv (all-bound-list-variables (intersect key arg res cex))
                          (append 
                           (if (equal key :var) (all-bound-variables arg) (all-bound-list-variables arg))
                           (all-bound-list-variables res))))
  :hints (("Goal" :in-theory (disable trapezoid-p-intersect)
           :use trapezoid-p-intersect)))

;; ---------------------------------------------------------------------------------

(defun intersection-measure (key arg res cex)
  (declare (ignore cex))
  (llist (if (equal key :var) (bound-varid arg) (if (consp arg) (largest-varid (bound-varid-list arg)) 0))
         (if (equal key :var) 0 (len arg))
         (len res)))

(def::total intersect (key arg res cex)
  (declare (xargs :measure (intersection-measure key arg res cex)
                  :hints (("Goal" :do-not-induct t))
                  :well-founded-relation l<))
  (and
   (if (equal key :var) (normalized-variableBound-p arg) (normalized-variableBound-listp arg))
   (trapezoid-p res)
   (env-p cex)))

(encapsulate
    ()
  
  (local
   (defthm eval-ineq-list-from-conjoinResults-helper
     (iff (eval-ineq (conjoinResults x list) env)
          (and (eval-ineq-list list env)
               (eval-ineq x env)))))

  (defthm eval-ineq-from-conjoinResults
    (implies
     (eval-ineq (conjoinResults (val 0 fn) (val 1 fn)) env)
     (and (eval-ineq-list (val 1 fn) env)
          (eval-ineq (val 0 fn) env))))
  
  (defthm not-eval-ineq-from-conjoinResults
    (implies
     (and
      (syntaxp (equal any 'any))
      (eval-ineq-list (val 1 fn) any)
      (not (eval-ineq (conjoinResults (val 0 fn) (val 1 fn)) any))
      )
     (not (eval-ineq (val 0 fn) any))))
  
  (defthm not-eval-ineq-list-from-conjoinResults
    (implies
     (and
      (syntaxp (equal any 'any))
      (eval-ineq (val 0 fn) any)
      (not (eval-ineq (conjoinResults (val 0 fn) (val 1 fn)) any)))
     (not (eval-ineq-list (val 1 fn) any))))
  
  )
  
(defthm inv1-intersect
  (implies
   (and
    (if (equal key :var) (normalized-variableBound-p arg) (normalized-variableBound-listp arg))
    (trapezoid-p res)
    (env-p cex)
    (eval-ineq-list res cex)
    (if (equal key :var) (eval-ineq arg cex) (eval-ineq-list arg cex)))
   (eval-ineq-list (intersect key arg res cex) cex)))

(defthm inv2-intersect
  (implies
   (and
    (if (equal key :var) (normalized-variableBound-p arg) (normalized-variableBound-listp arg))
    (trapezoid-p res)
    (env-p cex)
    (eval-ineq-list res cex)
    (if (equal key :var) (eval-ineq arg cex) (eval-ineq-list arg cex))
    (not (and (if (equal key :var) (eval-ineq arg any) (eval-ineq-list arg any))
              (eval-ineq-list res any))))
   (not (eval-ineq-list (intersect key arg res cex) any))))

;; ---------------------------------------------------------------------------------

(def::un intersect-var (var res cex)
  (declare (xargs :signature ((variableBound-p variableBound-listp env-p) variableBound-listp)))
  (intersect-var-macro var res cex))

(def::signature intersect-var (normalized-variableBound-p trapezoid-p env-p) trapezoid-p)

(def::un intersect-list (list res cex)
  (declare (xargs :signature ((variableBound-listp variableBound-listp env-p) variableBound-listp)))
  (intersect-list-macro list res cex))

(def::signature intersect-list (normalized-variableBound-listp trapezoid-p env-p) trapezoid-p)

(defthm set-upper-bound-equiv-all-bound-list-variables-intersect-list
  (implies
   (and
    (normalized-variableBound-listp arg)
    (trapezoid-p res)
    (env-p cex))
   (set-upper-bound-equiv (all-bound-list-variables (intersect-list arg res cex))
                          (double-rewrite (append 
                                           (all-bound-list-variables arg)
                                           (all-bound-list-variables res))))))

(defthm inv1-intersect-list
  (implies
   (and
    (normalized-variableBound-listp arg)
    (trapezoid-p res)
    (env-p cex)
    (eval-ineq-list res cex)
    (eval-ineq-list arg cex))
   (eval-ineq-list (intersect-list arg res cex) cex)))

(defthm inv2-intersect-list
  (implies
   (and
    (normalized-variableBound-listp arg)
    (trapezoid-p res)
    (env-p cex)
    (eval-ineq-list res cex)
    (eval-ineq-list arg cex)
    (not (and (eval-ineq-list arg any)
              (eval-ineq-list res any))))
   (not (eval-ineq-list (intersect-list arg res cex) any))))

(in-theory (disable intersect-var intersect-list))

;; ---------------------------------------------------------------------------------

(defmacro and-zoid-macro (xlist ylist env)
  `(let ((xlist ,xlist)
         (ylist ,ylist)
         (env   ,env))
     (if (and (consp xlist) (consp ylist))
         (and-zoid-rec (car xlist) (cdr xlist) (car ylist) (cdr ylist) env)
       (if (not (consp xlist)) ylist
         xlist))))

(def::ung and-zoid-rec (x xlist y ylist env)
  (declare (xargs :default-value nil
                  :signature ((variableBound-p variableBound-listp variableBound-p variableBound-listp env-p) variableBound-listp)
                  :guard-hints (("Goal" :do-not-induct t)
                                (and stable-under-simplificationp
                                     '(:expand ((AND-ZOID-REC-0-DOMAIN X NIL Y YLIST ENV)
                                                (AND-ZOID-REC-0-DOMAIN X XLIST Y NIL ENV)))))))
  (if (equal (bound-varid x) (bound-varid y))
      (let ((res (and-zoid-macro xlist ylist env)))
        (metlist ((z zres) (andTrue-variableBound-variableBound x y env))
          (cons z (intersect-list zres res env))))
    (if (< (bound-varid x) (bound-varid y))
        (cons y (if (not (consp ylist)) (cons x xlist)
                  (and-zoid-rec x xlist (car ylist) (cdr ylist) env)))
      (cons x (if (not (consp xlist)) (cons y ylist)
                (and-zoid-rec (car xlist) (cdr xlist) y ylist env))))))

(defthm trapezoid-p-and-zoid-rec
  (implies
   (and
    (normalized-variableBound-p x)
    (trapezoid-p xlist)
    (>-all (bound-varid x) (all-bound-list-variables xlist))
    (normalized-variableBound-p y)
    (trapezoid-p ylist)
    (>-all (bound-varid y) (all-bound-list-variables ylist))
    (env-p env))
   (and
    (trapezoid-p (and-zoid-rec x xlist y ylist env))
    (subset-p (all-bound-list-variables (and-zoid-rec x xlist y ylist env))
              (append
               (all-bound-variables x)
               (all-bound-variables y)
               (all-bound-list-variables xlist)
               (all-bound-list-variables ylist)))))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :induct (and-zoid-rec x xlist y ylist env))))

(defthm set-upper-bound-equiv-all-bound-list-variables-and-zoid-rec
  (implies
   (and
    (normalized-variableBound-p x)
    (trapezoid-p xlist)
    (>-all (bound-varid x) (all-bound-list-variables xlist))
    (normalized-variableBound-p y)
    (trapezoid-p ylist)
    (>-all (bound-varid y) (all-bound-list-variables ylist))
    (env-p env))
   (set-upper-bound-equiv (all-bound-list-variables (and-zoid-rec x xlist y ylist env))
                          (append
                           (all-bound-variables x)
                           (all-bound-variables y)
                           (all-bound-list-variables xlist)
                           (all-bound-list-variables ylist))))
  :hints (("Goal" :in-theory (disable trapezoid-p-and-zoid-rec)
           :use trapezoid-p-and-zoid-rec)))

(def::total and-zoid-rec (x xlist y ylist env)
  (declare (xargs :measure (max (bound-varid x) (bound-varid y))
                  :hints (("Goal" :do-not-induct t))))
  (and
   (normalized-variableBound-p x)
   (trapezoid-p xlist)
   (>-all (bound-varid x) (all-bound-list-variables xlist))
   (normalized-variableBound-p y)
   (trapezoid-p ylist)
   (>-all (bound-varid y) (all-bound-list-variables ylist))
   (env-p env)))

(defthm inv1-and-zoid-rec
  (implies
   (and
    (and
     (normalized-variableBound-p x)
     (trapezoid-p xlist)
     (>-all (bound-varid x) (all-bound-list-variables xlist))
     (normalized-variableBound-p y)
     (trapezoid-p ylist)
     (>-all (bound-varid y) (all-bound-list-variables ylist))
     (env-p cex))
    (and
     (eval-ineq x cex)
     (eval-ineq y cex)
     (eval-ineq-list xlist cex)
     (eval-ineq-list ylist cex)))
   (eval-ineq-list (and-zoid-rec x xlist y ylist cex) cex)))

(defthm inv2-and-zoid-rec
  (implies
   (and
    (and
     (normalized-variableBound-p x)
     (trapezoid-p xlist)
     (>-all (bound-varid x) (all-bound-list-variables xlist))
     (normalized-variableBound-p y)
     (trapezoid-p ylist)
     (>-all (bound-varid y) (all-bound-list-variables ylist))
     (env-p cex))
    (and
     (eval-ineq x cex)
     (eval-ineq y cex)
     (eval-ineq-list xlist cex)
     (eval-ineq-list ylist cex))
    (not
     (and
     (eval-ineq x any)
     (eval-ineq y any)
     (eval-ineq-list xlist any)
     (eval-ineq-list ylist any)))
    )
   (not (eval-ineq-list (and-zoid-rec x xlist y ylist cex) any))))

;; ---------------------------------------------------------------------------------

(def::un and-zoid (xlist ylist env)
  (declare (xargs :signature ((trapezoid-p trapezoid-p env-p) trapezoid-p)))
  (and-zoid-macro xlist ylist env))

(defthm inv1-and-zoid
  (implies
   (and
    (and
     (trapezoid-p xlist)
     (trapezoid-p ylist)
     (env-p cex))
    (and
     (eval-ineq-list xlist cex)
     (eval-ineq-list ylist cex)))
   (eval-ineq-list (and-zoid xlist ylist cex) cex)))

(defthm inv2-and-zoid
  (implies
   (and
    (and
     (trapezoid-p xlist)
     (trapezoid-p ylist)
     (env-p cex))
    (and
     (eval-ineq-list xlist cex)
     (eval-ineq-list ylist cex))
    (not
     (and
      (eval-ineq-list xlist any)
      (eval-ineq-list ylist any))))
   (not (eval-ineq-list (and-zoid xlist ylist cex) any))))

(in-theory (disable and-zoid))
