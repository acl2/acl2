; Utilities for combining hints
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also books/hints/merge-hint.lisp

;; Desugar an argument to :use.  Turns a single item into a singleton list.
(defun desugar-use-hint (form)
  (declare (xargs :guard t))
  (if (null form) ; empty list of things to :use
      nil
    (if (symbolp form) ; a single symbol
        (list form)
      (if (not (and (consp form)
                    (true-listp form)))
          (er hard? 'desugar-use-hint "Bad :use hint: ~x0." form)
        (if (keywordp (car form)) ; recognize a single rune or lemma-instance
            (list form)
          form ; must already be a list
          )))))

;; Desugar an argument to :expand.  Turns a single item into a singleton list.
(defun desugar-expand-hint (form)
  (declare (xargs :guard t))
  (if (null form) ; empty list of things to :expand
      nil
    (if (eq :lambdas form)
        (list :lambdas)
      (if (not (and (consp form)
                    (true-listp form)))
          (er hard? 'desugar-expand-hint "Bad :expand hint: ~x0." form)
        (if (and (symbolp (car form)) ; recognize a term or let or :free or :with
                 (not (eq :lambdas (car form))))
            (list form)
          form ; must already be a list
          )))))

(defun merge-use-hints (form1 form2)
  (declare (xargs :guard t))
  (union-equal (desugar-use-hint form1)
               (desugar-use-hint form2)))

(defun merge-expand-hints (form1 form2)
  (declare (xargs :guard t))
  (union-equal (desugar-expand-hint form1)
               (desugar-expand-hint form2)))

(defun incompatible-hint-settings (key1 key2)
  (declare (xargs :guard (and (keywordp key1)
                              (keywordp key2)
                              (not (equal key1 key2)))))
  (and (member-eq key1 '(:use :cases :by :induct :bdd :clause-processor :or))
       (member-eq key2 '(:use :cases :by :induct :bdd :clause-processor :or))
       (not (or (and (eq key1 :use)
                     (eq key2 :cases))
                (and (eq key1 :cases)
                     (eq key2 :use))))))

(defun merge-in-theory-hints (form1 form2)
  (declare (xargs :guard t))
  (if (null form1)
      nil ; empty theory, since form1 says so
    (if (not (consp form1))
        (er hard? 'merge-in-theory-hints "Bad :in-theory: ~x0." form1)
      (case (car form1)
        (disable `(set-difference-theories ,form2 '(,@(cdr form1))))
        (enable `(union-theories '(,@(cdr form1)) ,form2))
        (t (er hard? 'merge-in-theory-hints "Can't merge :in-theory ~x0." form1))))))

;; Note that the forms get evaluated.
;; TODO: Do better if both forms are quoted lists
(defun merge-do-not-hints (form1 form2)
  (declare (xargs :guard t))
  `(union-eq ,form1 ,form2))

;; Returns a new value to be used for KEY.
;; val1 can override all or part of val2 if needed.
(defun merge-hint-vals (key val1 val2)
  (declare (xargs :guard (keywordp key)))
  (case key
    (:use (merge-use-hints val1 val2))
    (:expand (merge-expand-hints val1 val2))
    (:in-theory (merge-in-theory-hints val1 val2))
    (:do-not (merge-do-not-hints val1 val2))
    (:by val1) ; can't really merge, so just use val1
    (:cases val1) ; can't really merge, so just use val1
    (:induct val1) ; can't really merge, so just use val1
    (:nonlinearp val1) ; can't really merge, so just use val1
    (t (er hard? 'merge-hint-vals "Merging of ~x0 hints not yet supported." key))))

;; Returns a keyword-value-list.  Overwrites whatever is needed to support binding KEY to VAL.
(defun merge-hint-setting-into-hint-settings (key val hint-settings)
  (declare (xargs :guard (and (keywordp key)
                              ;; what to say about val?
                              (keyword-value-listp hint-settings))))
  (if (endp hint-settings)
      (list key val) ; no existing hint-setting for the keyword
    (let ((this-key (first hint-settings))
          (this-val (second hint-settings)))
      (if (eq key this-key)
          (cons this-key (cons (merge-hint-vals key val this-val) (rest (rest hint-settings))))
        (if (incompatible-hint-settings key this-key)
            ;; Must remove this hint-setting.  Then keep going.
            (merge-hint-setting-into-hint-settings key val (rest (rest hint-settings)))
          (cons this-key (cons this-val (merge-hint-setting-into-hint-settings key val (rest (rest hint-settings))))))))))

;; (defun merge-hint-setting-into-hint (keyword val hint)
;;   (if (not (and (consp hint)
;;                 (stringp (car hint)) ; a goal name
;;                 ))
;;       :error ; can't merge.  Maybe it's a computed hint
;;     `(,(car hint) ; goal name
;;       ,@(merge-hint-setting-into-hint-settings keyword val (cdr hint)))))

;; Merge the hint-setting of val for key into the hint for goal-spec.
(defun merge-hint-setting-into-hint (key val goal-spec hints)
  (declare (xargs :guard (and (keywordp key)
                              ;; what to say about val?
                              (stringp goal-spec)
                              (standard-string-p goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      (list (list goal-spec key val)) ; no hint already present, so make one
    (let ((hint (first hints)))
      (if (and (consp hint)
               (stringp (car hint))
               (standard-string-p (car hint))
               (string-equal goal-spec (car hint)))
          (if (not (keyword-value-listp (cdr hint)))
              (er hard? 'merge-hint-setting-into-hint "Bad hint: ~x0." hint)
            (cons `(,(car hint) ,@(merge-hint-setting-into-hint-settings key val (cdr hint)))
                  (rest hints)))
        (cons hint
              (merge-hint-setting-into-hint key val goal-spec (rest hints)))))))

;; Merge the hint-setting of VAL for KEY into the hint for "Goal".
(defun merge-hint-setting-into-goal-hint (key val hints)
  (declare (xargs :guard (and (keywordp key)
                              ;; what to say about val?
                              (true-listp hints))))
  (merge-hint-setting-into-hint key val "Goal" hints))
