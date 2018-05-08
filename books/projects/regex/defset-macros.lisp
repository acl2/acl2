; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note: this book doesn't appear to be used anywhere.  Consider deleting it.
(in-package "ACL2")





(defmacro elem-guards (param)
  `(if equiv-guard
       `(,equiv-guard ,,param)
     t))

(defmacro set-guards (param)
  `(if equiv-guard
       `(,equivable-setp ,,param)
     t))

(defmacro thm-hints (thm-name other)
  `(if use-f-i
       `(:hints (("Goal"
                  :use (:functional-instance ,(makesym ,thm-name orig-sym)
                                             ,@subs)
                  :do-not-induct t
                  :in-theory (disable ,(makesym ,thm-name orig-sym)))))
     ,other))

(defmacro makesym (&rest l)
  `(intern-in-package-of-symbol
    (coerce (packn1 (list ,@l)) 'string)
    pkg-sym))

(defmacro makename (prefix)
  `(makesym ,prefix equiv))


(defmacro defun-equivable-setp ()
  ``(defun ,equivable-setp (x)
      (declare (xargs :guard t))
      (if (atom x)
          (equal x nil)
        (and ,(elem-guards '(car x))
             (,equivable-setp (cdr x))))))

(defmacro defun-set-member ()
  ``(defun ,set-member (e s)
      (declare (xargs :guard (and ,(elem-guards 'e)
                                  ,(set-guards 's))
                      :measure (acl2-count s)))
      (if (atom s)
          nil
        (or (,equiv e (car s))
            (,set-member e (cdr s))))))

(defmacro defun-set-subset ()
  ``(defun ,set-subset (r s)
      (declare (xargs :guard (and ,(set-guards 's)
                                  ,(set-guards 'r))
                      :measure (acl2-count r)))
      (if (atom r)
          t
        (and (,set-member (car r) s)
             (,set-subset (cdr r) s)))))



(defmacro defun-set-equiv ()
  ``(defun ,set-equiv (r s)
      (declare (xargs :guard (and ,(set-guards 'r)
                                  ,(set-guards 's))))
      (and (,set-subset r s)
           (,set-subset s r))))

(defmacro defun-set-insert ()
  ``(defun ,set-insert (e s)
      (declare (xargs :guard (and ,(elem-guards 'e)
                                  ,(set-guards 's))))
      (if (,set-member e s)
          s
        (cons e s))))

(defmacro defun-set-delete ()
  ``(defun ,set-delete (e s)
      (declare (xargs :guard (and ,(elem-guards 'e)
                                  ,(set-guards 's))))
      (if (atom s)
          nil
        (if (,equiv e (car s))
            (,set-delete e (cdr s))
          (cons (car s) (,set-delete e (cdr s)))))))


(defmacro defun-set-union ()
  ``(defun ,set-union (r s)
      (declare (xargs :guard (and ,(set-guards 'r)
                                  ,(set-guards 's))
                      :measure (acl2-count r)))
      (if (atom r)
          s
        (,set-union (cdr r) (,set-insert (car r) s)))))
;;         (if (,set-member (car r) s)
;;             (,set-union (cdr r) s)
;;           (cons (car r)
;;                 (,set-union (cdr r) s))))))
;;                     (,set-insert (car r) s)))))

(defmacro defthm-set-insert-setp ()
  ``(defthm ,(makename 'set-insert-setp-)
      (implies (and ,(elem-guards 'e)
                    ,(set-guards 's))
               ,(set-guards `(,set-insert e s)))
      ,@(thm-hints 'set-insert-setp- nil)))

(defmacro defthm-set-delete-setp ()
  ``(defthm ,(makename 'set-delete-setp-)
      (implies ,(set-guards 's)
               ,(set-guards `(,set-delete e s)))
      ,@(thm-hints 'set-delete-setp- nil)))

(defmacro defthm-set-union-setp ()
  ``(defthm ,(makename 'set-union-setp-)
      (implies (and ,(set-guards 'r)
                    ,(set-guards 's))
               ,(set-guards `(,set-union r s)))
      ,@(thm-hints 'set-union-setp- nil)))




(defmacro defthm-set-member-car ()
  ``(defthm ,(makename 'set-member-car-)
      (implies (consp s)
               (,set-member (car s) s))
      ,@(thm-hints 'set-member-car- nil)))

(defmacro defthm-set-member-cons ()
  ``(defthm ,(makename 'set-member-cons-)
      (implies (,set-member x s)
               (consp s))
      :rule-classes :forward-chaining))

(defmacro defcong-set-member-1 ()
  ``(defcong ,equiv iff (,set-member e s) 1
      ,@(thm-hints 'set-member-congruence-1- nil)
      :event-name ,(makename 'set-member-congruence-1-)))


(defmacro defthm-cons-subset ()
  ``(defthm ,(makename 'cons-set-subset-)
      (implies (,set-subset r s)
               (,set-subset r (cons e s)))
      ,@(thm-hints 'cons-set-subset- nil)))


(defmacro defthm-subset-reflexive ()
  ``(defthm ,(makename 'set-subset-reflexive-)
      (,set-subset s s)
      ,@(thm-hints 'set-subset-reflexive- nil)))


(defmacro defthm-subset-member ()
  ``(defthm ,(makename 'set-subset-member-)
      (implies (and (,set-member e r)
                    (,set-subset r s))
               (,set-member e s))
      ,@(thm-hints 'set-subset-member- nil)))

(defmacro defthm-subset-transitive ()
  ``(defthm ,(makename 'set-subset-transitive-)
      (implies (and (,set-subset q r)
                    (,set-subset r s))
               (,set-subset q s))
      ,@(thm-hints 'set-subset-transitive- nil)))

(defmacro defequiv-set-equiv ()
  ``(defequiv ,set-equiv
      ,@(thm-hints 'equivalence-set-equiv- nil)
      :event-name ,(makename 'equivalence-set-equiv-)))

(defmacro defcong-set-member-2 ()
  ``(defcong ,set-equiv iff (,set-member e s) 2
      ,@(thm-hints 'set-member-congruence-2- nil)
      :event-name ,(makename 'set-member-congruence-2-)))

(defmacro defcong-consp ()
  ``(defcong ,set-equiv iff (consp x) 1
      ,@(thm-hints 'consp-set-congruence-1- nil)
      :event-name ,(makename 'consp-set-congruence-1-)))

(defmacro defcong-subset-1 ()
  ``(defcong ,set-equiv iff (,set-subset r s) 1
      ,@(thm-hints 'set-subset-congruence-1- nil)
      :event-name ,(makename 'set-subset-congruence-1-)))

(defmacro defcong-subset-2 ()
  ``(defcong ,set-equiv iff (,set-subset r s) 2
      ,@(thm-hints 'set-subset-congruence-2- nil)
      :event-name ,(makename 'set-subset-congruence-2-)))

(defmacro defcong-set-insert-1 ()
``(defcong ,equiv ,set-equiv (,set-insert e s) 1
    ,@(thm-hints 'set-insert-congruence-1- nil)
    :event-name ,(makename 'set-insert-congruence-1-)))

(defmacro defcong-set-insert-2 ()
``(defcong ,set-equiv ,set-equiv (,set-insert e s) 2
    ,@(thm-hints
       'set-insert-congruence-2-
       nil)
    :event-name ,(makename 'set-insert-congruence-2-)))


(defmacro defcong-set-delete-1 ()
``(defcong ,equiv ,set-equiv (,set-delete e s) 1
    ,@(thm-hints 'set-delete-congruence-1- nil)
    :event-name ,(makename 'set-delete-congruence-1-)))

(defmacro defthm-set-insert-cons ()
``(defthm ,(makename 'set-insert-cons-)
    (consp (,set-insert x s))))

(defmacro defthm-set-member-delete-1 ()
``(defthm ,(makename 'set-member-delete-1-)
    (implies (and (not (,equiv e f))
                  (,set-member e s))
             (,set-member e (,set-delete f s)))
    ,@(thm-hints 'set-member-delete-1- nil)))

(defmacro defthm-subset-delete-subset ()
``(defthm ,(makename 'set-subset-delete-subset-)
    (implies (,set-subset r s)
             (,set-subset (,set-delete e r)
                          (,set-delete e s)))
    ,@(thm-hints 'set-subset-delete-subset- nil)))

(defmacro defcong-set-delete-2 ()
``(defcong ,set-equiv ,set-equiv (,set-delete e s) 2
    ,@(thm-hints 'set-delete-congruence-2- nil)
    :event-name ,(makename 'set-delete-congruence-2-)))


(defmacro defthm-set-union-member1 ()
``(defthm ,(makename 'set-union-member1-)
    (implies (,set-member e s)
             (,set-member e (,set-union r s)))
    ,@(thm-hints 'set-union-member1- nil)))

(defmacro defthm-set-union-member2 ()
``(defthm ,(makename 'set-union-member2-)
    (implies (,set-member e s)
             (,set-member e (,set-union s r)))
    ,@(thm-hints 'set-union-member2- nil)))

(defmacro defthm-set-union-subset1-1 ()
``(defthm ,(makename 'set-union-subset1-1-)
    (implies (,set-subset r s)
             (,set-subset r (,set-union q s)))
    ,@(thm-hints 'set-union-subset1-1- nil)))

(defmacro defthm-set-union-subset1-2 ()
``(defthm ,(makename 'set-union-subset1-2-)
    (implies (,set-subset r s)
             (,set-subset r (,set-union s q)))
    ,@(thm-hints 'set-union-subset1-2- nil)))


(defmacro defthm-set-union-subset2 ()
``(defthm ,(makename 'set-union-subset2-)
    (implies (and (,set-subset q s)
                  (,set-subset r s))
             (,set-subset (,set-union q r) s))
    ,@(thm-hints 'set-union-subset2- nil)))

(defmacro defcong-set-union-1 ()
``(defcong ,set-equiv ,set-equiv (,set-union r s) 1
    ,@(thm-hints 'set-union-congruence-1- nil)
    :event-name ,(makename 'set-union-congruence-1-)))

(defmacro defcong-set-union-2 ()
``(defcong ,set-equiv ,set-equiv (,set-union r s) 2
    ,@(thm-hints 'set-union-congruence-2- nil)
    :event-name ,(makename 'set-union-congruence-2-)))

(defmacro defthm-set-union-commutative ()
``(defthm ,(makename 'set-union-commutative-)
    (,set-equiv (,set-union r s) (,set-union s r))
    ,@(thm-hints 'set-union-commutative- nil)))

(defmacro defthm-set-union-member3 ()
``(defthm ,(makename 'set-union-member3-)
    (implies (and (,set-member e (,set-union r s))
                  (not (,set-member e r)))
             (,set-member e s))
    ,@(thm-hints 'set-union-member3- nil)))


(defmacro defthm-set-delete-len ()
  ``(defthm ,(makename 'set-delete-len-)
      (implies (,set-member e s)
               (< (len (,set-delete e s))
                  (len s)))
      :rule-classes (:rewrite :linear)
      ,@(thm-hints 'set-delete-len- nil)))



;; This should be used to define a set where elements are distinguished
;; by the equivalence relation equiv.  equiv-guard should be the guard
;; of the equiv function or else nil;  if you wish to further restrict
;; possible set elements then subsequently use def-typed-set.

(defmacro def-set-equiv (equiv &key (equiv-guard 'nil) (pkg-sym 'ACL2::asdf)
                               (prove-elem-congruences 't) (use-f-i 't))
  (let* ((orig-sym 'defset-element-equiv)
         (before-label (makesym 'before-def-set- equiv))
         (theory-name (makesym equiv '-based-set-theory))
         (disabled-theory-name (makesym equiv '-set-theory-disabled-fns))
         (equivable-setp (makesym equiv '-setp))
         (set-member (makename 'set-member-))
         (set-subset (makename 'set-subset-))
         (set-equiv (makename 'set-equiv-))
         (set-insert (makename 'set-insert-))
         (set-delete (makename 'set-delete-))
         (set-union (makename 'set-union-))
         (subs
          `((defset-element-equiv ,equiv)
            ,@(if equiv-guard `((defset-element-equiv-setp ,equivable-setp)) nil)
            (set-member-defset-element-equiv ,set-member)
            (set-subset-defset-element-equiv ,set-subset)
            (set-equiv-defset-element-equiv ,set-equiv)
            (set-insert-defset-element-equiv ,set-insert)
            (set-delete-defset-element-equiv ,set-delete)
            (set-union-defset-element-equiv ,set-union))))

    `(progn

      ,@(if use-f-i
            `((deflabel ,before-label))
          nil)
      ,@(if equiv-guard `(,(defun-equivable-setp)) nil)
      ,(defun-set-member)
      ,(defun-set-subset)
      ,(defun-set-equiv)
      ,(defun-set-insert)
      ,(defun-set-delete)
      ,(defun-set-union)
      ,@(if equiv-guard `(,(defthm-set-insert-setp)
                          ,(defthm-set-delete-setp)
                          ,(defthm-set-union-setp))
          nil)
      ,(defthm-set-member-car)
      ,(defthm-set-member-cons)
      ,@(if prove-elem-congruences `(,(defcong-set-member-1)) nil)
      ,(defthm-cons-subset)
      ,(defthm-subset-reflexive)
      ,(defthm-subset-member)
      ,(defthm-subset-transitive)
      ,(defequiv-set-equiv)
      ,(defcong-set-member-2)
      ,(defcong-consp)
      ,(defcong-subset-1)
      ,(defcong-subset-2)
      ,@(if prove-elem-congruences `(,(defcong-set-insert-1)) nil)
      ,(defcong-set-insert-2)
      ,@(if prove-elem-congruences `(,(defcong-set-delete-1)) nil)
      ,(defthm-set-insert-cons)
      ,(defthm-set-member-delete-1)
      ,(defthm-subset-delete-subset)
      ,(defcong-set-delete-2)
      ,(defthm-set-union-member1)
      ,(defthm-set-union-member2)
      ,(defthm-set-union-subset1-1)
      ,(defthm-set-union-subset1-2)
      ,(defthm-set-union-subset2)
      ,(defcong-set-union-1)
      ,(defcong-set-union-2)
      ,(defthm-set-union-commutative)
      ,(defthm-set-union-member3)
      ,(defthm-set-delete-len)
      (in-theory (disable ,set-equiv ,set-insert))
      ,@(if use-f-i
            `((deftheory ,theory-name
               (set-difference-theories
                (current-theory :here)
                (current-theory ',before-label))))
          nil)
      ,@(if use-f-i
            `((deftheory ,disabled-theory-name
               (set-difference-theories
                (set-difference-theories
                 (universal-theory :here)
                 (universal-theory (quote ,before-label)))
                (theory (quote ,theory-name)))))
          nil))))






(defmacro thm-hints2 (thm-name-base other)
  `(if use-f-i
       `(:hints (("Goal"
                  :use (:functional-instance
                        ,(makesym ,thm-name-base orig-equiv '- orig-sym)
                        ,@subs)
                  :do-not-induct t
                  :in-theory
                  (disable ,(makesym ,thm-name-base orig-equiv '- orig-sym)))))
     ,other))


(defmacro elemp-args (param)
`(if additional-param
     `(,,param p)
   `(,,param)))

(defmacro make-guard (guard &rest param)
`(if ,guard
     (list ,guard . ,param)
   t))

(defmacro defun-setp ()
``(defun ,setp ,(elemp-args 'x)
    (declare (xargs :guard (and ,(make-guard setp-guard 'x)
                                ,(make-guard param-guard 'p))))
    (if (atom x)
        t
      (and (,elemp ,@(elemp-args '(car x)))
           (,setp ,@(elemp-args '(cdr x)))))))

(defmacro defthm-member-equal-elemp ()
``(defthm ,(makesym set-member '- typename)
    (implies (and (,setp ,@(elemp-args 's))
                  (,set-member x s))
             (,elemp ,@(elemp-args 'x)))
    ,@(thm-hints2 'set-member- nil)))

(defmacro defthm-nil-setp ()
``(defthm ,(makesym 'nil- typename)
    (,setp ,@(elemp-args 'nil))))

;; (defmacro defthm-setp-true-listp ()
;; ``(defthm ,(makesym 'true-listp- typename)
;;     (implies (,setp ,@(elemp-args 's))
;;              (true-listp s))
;;     ,@(thm-hints 'true-listp- nil)))

(defmacro defthm-insert-setp ()
``(defthm ,(makesym set-insert '-  typename)
    (implies (and (,elemp ,@(elemp-args 'x))
                  (,setp ,@(elemp-args 's)))
             (,setp ,@(elemp-args `(,set-insert x s))))
    ,@(thm-hints2 'set-insert- nil)))

(defmacro defthm-insert-not-setp1 ()
``(defthm ,(makesym 'not-1- set-insert '- typename)
    (implies (not (,elemp ,@(elemp-args 'x)))
             (not (,setp ,@(elemp-args `(,set-insert x s)))))
    ,@(thm-hints2 'not-1-set-insert- nil)))

(defmacro defthm-insert-not-setp2 ()
``(defthm ,(makesym 'not-2- set-insert '- typename)
    (implies (not (,setp ,@(elemp-args 's)))
             (not (,setp ,@(elemp-args `(,set-insert x s)))))
    ,@(thm-hints2 'not-2-set-insert- nil)))

(defmacro defthm-delete-setp ()
``(defthm ,(makesym set-delete '-  typename)
    (implies (and (,elemp ,@(elemp-args 'x))
                  (,setp ,@(elemp-args 's)))
             (,setp ,@(elemp-args `(,set-delete x s))))
    ,@(thm-hints2 'set-delete- nil)))

(defmacro defthm-subset-setp ()
  ``(defthm ,(makesym set-subset '- typename)
      (implies (and (,set-subset r s)
                    (,setp ,@(elemp-args 's)))
               (,setp ,@(elemp-args 'r)))
      ,@(thm-hints2 'set-subset- nil)))

(defmacro defthm-subset-not-setp ()
  ``(defthm ,(makesym 'not- set-subset '- typename)
      (implies (and (,set-subset r s)
                    (not (,setp ,@(elemp-args 'r))))
               (not (,setp ,@(elemp-args 's))))
      ,@(thm-hints2 'not-set-subset- nil)))

(defmacro defthm-union-setp ()
``(defthm ,(makesym set-union '-  typename)
    (implies (and (,setp ,@(elemp-args 'r))
                  (,setp ,@(elemp-args 's)))
             (,setp ,@(elemp-args `(,set-union r s))))
    ,@(thm-hints2 'set-union- nil)))

(defmacro defthm-union-not-setp ()
``(defthm ,(makesym 'not- set-union '- typename)
    (implies (or (and (consp r)
                      (not (,setp ,@(elemp-args 'r))))
                 (and (consp s)
                      (not (,setp ,@(elemp-args 's)))))
             (not (,setp ,@(elemp-args `(,set-union r s)))))
       ,@(thm-hints2 'not-set-union- nil)))
;;                    `(:hints (("Goal"  ||#
;;                             :in-theory (disable equiv-set-theory-disabled-fns))))))) ||#

;; (defmacro defthm-union-not-setp2 () ||#
;;   ``(defthm ,(makesym set-union '-not-1- typename) ||#
;;       (implies (not (,setp ,@(elemp-args 's))) ||#
;;                (not (,setp ,@(elemp-args `(,set-union r s))))) ||#
;;       ,@(thm-hints 'set-union-equiv-not-2- nil))) ||#


(defmacro defthm-revappend-setp ()
``(defthm ,(makesym 'revappend- typename)
    (implies (and (,setp ,@(elemp-args 'r))
                  (,setp ,@(elemp-args 's)))
             (,setp ,@(elemp-args '(revappend r s))))
    ,@(thm-hints 'revappend- nil)))


(defmacro def-typed-set (elemp typename &key (additional-param 'nil)
                               (param-guard 'nil)
                               (setp-guard 'nil)
                               (def-setp 't) (equiv 'equal)
                               (pkg-sym 'ACL2::asdf) (use-f-i 't))
  (let* ((orig-sym (if additional-param 'deftypedset-set-type-1
                     'deftypedset-set-type-0))
         (orig-equiv (if additional-param 'deftypedset-element-equiv1
                       'deftypedset-element-equiv0))
         (before-label (makesym 'before-def-typed-set- typename))
         (theory-name (makesym typename '-typed-set-theory))
         ;;(equiv-set-theory (makesym equiv '-based-set-theory))
         (equiv-disabled-fns (makesym equiv '-set-theory-disabled-fns))
         (setp (makesym typename 'p))
         (set-member (makename 'set-member-))
         (set-insert (makename 'set-insert-))
         (set-delete (makename 'set-delete-))
         (set-subset (makename 'set-subset-))
         (set-union (makename 'set-union-))
         (subs (if additional-param
                   `((deftypedset-element-p1 ,elemp)
                     (deftypedset-element-equiv1 ,equiv)
                     (deftypedset-set-type-1p ,setp)
                     (set-member-deftypedset-element-equiv1 ,set-member)
                     (set-insert-deftypedset-element-equiv1 ,set-insert)
                     (set-delete-deftypedset-element-equiv1 ,set-delete)
                     (set-subset-deftypedset-element-equiv1 ,set-subset)
                     (set-union-deftypedset-element-equiv1 ,set-union))
                 `((deftypedset-element-p0 ,elemp)
                   (deftypedset-element-equiv0 ,equiv)
                   (deftypedset-set-type-0p ,setp)
                   (set-member-deftypedset-element-equiv0 ,set-member)
                   (set-insert-deftypedset-element-equiv0 ,set-insert)
                   (set-delete-deftypedset-element-equiv0 ,set-delete)
                   (set-subset-deftypedset-element-equiv0 ,set-subset)
                   (set-union-deftypedset-element-equiv0 ,set-union)))))

    `(encapsulate
      ()
      (in-theory (enable ,equiv-disabled-fns))
      ,@(if use-f-i `((deflabel ,before-label)) nil)
      ,@(if def-setp `(,(defun-setp)) nil)
      ,(defthm-nil-setp)
      ,(defthm-member-equal-elemp)
      ,(defthm-insert-setp)
      ,(defthm-insert-not-setp1)
      ,(defthm-insert-not-setp2)
      ,(defthm-delete-setp)
      ,(defthm-union-setp)
      ,(defthm-union-not-setp)
      ,(defthm-subset-setp)
      ,(defthm-subset-not-setp)
      ;;      ,(defthm-union-not-setp2)
      ,(defthm-revappend-setp)
      ,@(if use-f-i
            `((deftheory ,theory-name
                (set-difference-theories
                 (universal-theory :here)
                 (universal-theory ',before-label))))
         nil)
      ,@(if use-f-i
            `((in-theory (disable ,equiv-disabled-fns)))
          nil))))

































(defmacro f-args (param)
  `(if additional-param
       `(,,param p)
     `(,,param)))

(defmacro make-guard2 (guard par)
  `(if ,guard
       (if additional-param
           `(,,guard ,,par p)
         `(,,guard ,,par))
     t))

(defmacro make-hard-guard2 (guard par)
  `(if hard-guard
       (if ,guard
           (if additional-param
               `(,,guard ,,par p)
             `(,,guard ,,par))
         t)
     t))

(defmacro defun-f-on-set ()
  ``(defun ,f-on-set ,(f-args 's)
      (declare (xargs :guard ,(make-guard2 set-guard 's)
                      :verify-guards nil))
      (if (mbt (iff t ,(make-hard-guard2 set-guard 's)))
          (if (atom s)
              nil
            (,set-union (,f ,@(f-args '(car s)))
                        (,f-on-set ,@(f-args '(cdr s)))))
        (,bad-input-fn))))

;; (defmacro defthm-f-on-set-truelist ()
;;   ``(defthm ,(makesym 'function-on-set-true-listp f)
;;       (true-listp (,f-on-set ,@(f-args 's)))))

(defmacro defthm-f-on-set-member ()
  ``(defthm ,(makesym 'function-on-set-member- f)
      (implies (and (case-split ,(make-hard-guard2 set-guard 's))
                    (,set-member x s))
               (,set-subset (,f ,@(f-args 'x))
                            (,f-on-set ,@(f-args 's))))
      ,@(thm-hints 'function-on-set-member- nil)))

(defmacro defthm-f-on-set-subset ()
  ``(defthm ,(makesym 'function-on-set-subset- f)
      (implies (and (case-split ,(make-hard-guard2 set-guard 's))
                    (case-split ,(make-hard-guard2 set-guard 'r))
                    (,set-subset r s))
               (,set-subset (,f-on-set ,@(f-args 'r))
                            (,f-on-set ,@(f-args 's))))
      ,@(thm-hints 'function-on-set-subset- nil)))

(defmacro defthm-f-on-set-bad-guard ()
  ``(defthm ,(makesym 'function-on-set-bad-guard- f)
      (implies (case-split (not ,(make-hard-guard2 set-guard 's)))
               (equal (,f-on-set ,@(f-args 's)) (,bad-input-fn)))
      ,@(thm-hints 'function-on-set-bad-guard- nil)))


(defmacro defcong-f-on-set-1 ()
  ``(defcong ,set-equiv ,set-equiv (,f-on-set ,@(f-args 's)) 1
      :event-name ,(makesym 'congruence-on-set- f)
      ,@(thm-hints 'congruence-on-set- nil)))


(defmacro defthm-f-on-set-insert ()
  ``(defthm ,(makesym 'function-on-set-insert- f)
      (implies (and (case-split ,(make-hard-guard2 set-guard 's))
                    (case-split ,(make-hard-guard2 set-guard `(,set-insert x s))))
               (,set-equiv (,f-on-set ,@(f-args `(,set-insert x s)))
                           (,set-union (,f ,@(f-args 'x))
                                       (,f-on-set ,@(f-args 's)))))
      ,@(thm-hints 'function-on-set-insert- nil)))

(defmacro defthm-f-on-set-union ()
  ``(defthm ,(makesym 'function-on-set-union- f)
      (implies (and (case-split ,(make-hard-guard2 set-guard 'r))
                    (case-split ,(make-hard-guard2 set-guard 's)))
               (,set-equiv (,f-on-set ,@(f-args `(,set-union r s)))
                           (,set-union (,f-on-set ,@(f-args 'r))
                                       (,f-on-set ,@(f-args 's)))))
      ,@(thm-hints 'function-on-set-union- nil)))


(defun bad-input-default ()
  (declare (xargs :guard t))
  nil)

(defmacro prove-set-congruence-of-f (f &key
                                       (f-on-set 'nil f-set-given)
                                       (additional-param 'nil)
                                       (elem-guard 'nil)
                                       (set-guard 'nil)
                                       (hard-guard 't)
                                       (equiv 'equal)
                                       (pkg-sym 'ACL2::asdf)
                                       (use-f-i 't)
                                       (bad-input-fn 'bad-input-default))
  "prove-set-congruence-of-f

;; Let f be some function which takes some element and a possible parameter
;; and returns a list of values.
;; Given f, prove-set-congruence-of-f
;; produces a theorem about a (possibly new) function, f-on-set.

;; F-on-set is a function which takes a set and a parameter (if f gets a
;; parameter) which runs f on every element of a set and returns the union of all
;; values returned by f.

;; The theorem proved is the congruence relation which says that
;; (f-on-set x) is set-equal to (f-on-set y) if x is set-equal to y.

;; The only required argument of prove-set-congruences-of-f is f, the function
;; on elements of the set. Optional (keyword) arguments are

;; f-on-set, if already defined (otherwise it will be defined),

;; additional-param, should be nonnil if f takes a parameter in addition to the
;; set element.  Default nil (each funciton takes only one argument.)

;; elem-guard: A predefined function of the same arguments as f.
;; If set-guard is not given, it will be defined using (def-typed-set
;; elem-guard).

;; set-guard: A (predefined) function of the same arguments as f-on-set.
;; If given, 1) if f-on-set is not predefined, this will be set as its guard, and
;; 2) unless hard-guard is explicitly set to nil, acts as an exception to the
;; usual behavior of f-on-set by forcing it to return (bad-input-fn)
;;  if this guard is not
;; met.  I.e., if set-guard is defined then the automatically-defined f-on-set
;; will be (or the predefined f-on-set should be)
;; (defun f-on-set (s and maybe p)
;;   (declare (xargs :guard (set-guard s and maybe p)))
;;   (if (mbt (set-guard s and maybe p))
;;       (.. execute normally ..)
;;     nil))
;; Default: no function, substitute t for every call of set-guard above.

;; hard-guard: If set to nil, this removes the (if (mbt (set-guard ...))
;; in the above definition.  Should be set to nil if a) you have predefined
;; f-on-set to execute normally even if the guard is not satisfied, or b)
;; you want f-on-set to be defined as such.
;; Default t.

;; pkg-sym: A symbol in the package in which various symbols will be defined.
;; Default ACL2::asdf.

;; use-f-i: Use functional instantiation to prove the theorems, which should work.
;; If there are cases where defset-encapsulates is included and this doesn't work,
;; I'd like to know.
"

  (let* ((orig-sym (if additional-param 'set-union-op-f1 'set-union-op-f0))
         (before-label (makesym 'before-def-set-union-op- f))
         (theory-name (makesym f '-set-union-op))
         ;;(equiv-set-theory (makesym equiv '-based-set-theory))
         (equiv-disabled-fns (makesym equiv '-set-theory-disabled-fns))
         (f-on-set (if f-set-given
                       f-on-set
                     (makesym f '-on-set)))
         (set-member (makename 'set-member-))
         (set-insert (makename 'set-insert-))
         (set-delete (makename 'set-delete-))
         (set-subset (makename 'set-subset-))
         (set-union (makename 'set-union-))
         (set-equiv (makename 'set-equiv-))
         (subs (if additional-param
                   `((set-union-op-f1 ,f)
                     (set-union-op-equiv1 ,equiv)
                     (set-equiv-set-union-op-equiv1 ,set-equiv)
                     (set-union-op-f1-on-set ,f-on-set)
                     (guard1-okp ,(if set-guard set-guard
                                    (if elem-guard
                                        (makesym elem-guard '-setp)
                                      'true-fun1)))
                     (elt-guard1 ,(if elem-guard elem-guard
                                    'true-fun1))
                     (set-insert-set-union-op-equiv1 ,set-insert)
                     (set-subset-set-union-op-equiv1 ,set-subset)
                     (set-delete-set-union-op-equiv1 ,set-delete)
                     (set-member-set-union-op-equiv1 ,set-member)
                     (set-union-set-union-op-equiv1 ,set-union)
                     (bad-input-fn1 ,bad-input-fn))
                 `((set-union-op-f0 ,f)
                     (set-union-op-equiv0 ,equiv)
                     (set-equiv-set-union-op-equiv0 ,set-equiv)
                     (set-union-op-f0-on-set ,f-on-set)
                     (guard0-okp ,(if set-guard set-guard
                                    (if elem-guard
                                        (makesym elem-guard '-setp)
                                    'true-fun0)))
                     (elt-guard0 ,(if elem-guard elem-guard
                                    'true-fun0))
                     (set-insert-set-union-op-equiv0 ,set-insert)
                     (set-subset-set-union-op-equiv0 ,set-subset)
                     (set-delete-set-union-op-equiv0 ,set-delete)
                     (set-member-set-union-op-equiv0 ,set-member)
                     (set-union-set-union-op-equiv0 ,set-union)
                     (bad-input-fn0 ,bad-input-fn)))))

    `(progn

      (in-theory (enable ,equiv-disabled-fns))
      ,@(if use-f-i `((deflabel ,before-label)) nil)
      ,@(if set-guard nil
          (if elem-guard
              `((def-typed-set elem-guard (makesym elem-guard '-set)))
            nil))
      ,@(if (not f-set-given) `(,(defun-f-on-set)) nil)
;      ,(defthm-f-on-set-truelist)
      ,@(if (not f-set-given) `((verify-guards ,f-on-set)) nil)
      ,(defthm-f-on-set-member)
      ,(defthm-f-on-set-subset)
      ,(defcong-f-on-set-1)
      ,(defthm-f-on-set-insert)
      ,(defthm-f-on-set-union)
      ,@(if (and set-guard hard-guard)
            `(,(defthm-f-on-set-bad-guard))
          nil)
      ,@(if use-f-i
            `((deftheory ,theory-name
                (set-difference-theories
                 (universal-theory :here)
                 (universal-theory ',before-label))))
          nil)
      ,@(if use-f-i
            `((in-theory (disable ,equiv-disabled-fns)))
          nil))))
