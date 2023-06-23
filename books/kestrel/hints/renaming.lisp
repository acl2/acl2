; A library about manipulating :hints
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A library about manipulating :hints (e.g., applying a renaming to symbols
;; mentioned in hints).

;; STATUS: Working but needs to be generalized to support more kinds of hints.

(include-book "kestrel/untranslated-terms/untranslated-terms-old" :dir :system) ;; TODO: Use newer utils

;; todo: factor these out:

(defun use-hint-instancep (val)
  (declare (xargs :guard t))
  (or (symbolp val) ;just a lemma name
      (and (true-listp val) ;; ex: (:instance foo (x (bar y)) (y (baz z)))
           (consp val)
           (member (ffn-symb val) '(:instance :functional-instance))
           (<= 1 (len (fargs val)))
           (use-hint-instancep (farg1 val)) ; nested instance
           (var-untranslated-term-pairsp (cdr (fargs val))))))

(defun use-hint-instance-listp (vals)
  (declare (xargs :guard t))
  (if (atom vals)
      (null vals)
    (and (use-hint-instancep (first vals))
         (use-hint-instance-listp (rest vals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaves SYM unchanged if it has no entry in RENAMING-ALIST.
(defun apply-renaming-to-symbol (sym renaming-alist)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-alistp renaming-alist))))
  (let ((res (assoc-eq sym renaming-alist)))
    (if res
        (cdr res)
      sym)))

(defun apply-renaming-to-symbols (syms renaming-alist)
  (declare (xargs :guard (and (symbol-listp syms)
                              (symbol-alistp renaming-alist))))
  (if (endp syms)
      nil
    (cons (apply-renaming-to-symbol (first syms) renaming-alist)
          (apply-renaming-to-symbols (rest syms) renaming-alist))))

(defun apply-renaming-to-symbol-or-rune (item renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (symbolp item)
      (apply-renaming-to-symbol item renaming-alist)
    ;; must be a rune:
    (if (not (and (= 2 (len item))
                  (symbolp (cadr item))))
        (er hard? 'apply-renaming-to-symbol-or-rune "Unexpected item: ~x0." item)
      (list* (car item)
             (apply-renaming-to-symbol (cadr item) renaming-alist)
             (cddr item)))))

(defun apply-renaming-to-symbols-or-runes (items renaming-alist)
  (declare (xargs :guard (and (true-listp items)
                              (symbol-alistp renaming-alist))))
  (if (endp items)
      nil
    (cons (apply-renaming-to-symbol-or-rune (first items) renaming-alist)
          (apply-renaming-to-symbols-or-runes (rest items) renaming-alist))))

(defun apply-renaming-to-use-hint-instance (val renaming-alist)
  (declare (xargs :guard (and (use-hint-instancep val)
                              (symbol-alistp renaming-alist))))
  (if (symbolp val)
      (apply-renaming-to-symbol val renaming-alist)
    (and (consp val)
         (let* ((instance-type (car val))
                (lemma-ref (cadr val))
                (subst (cddr val)))
           `(,instance-type
             ,(apply-renaming-to-use-hint-instance lemma-ref renaming-alist)
             ,@(make-doublets (strip-cars subst)
                              (rename-fns-in-untranslated-term-list (strip-cadrs subst)
                                                                    renaming-alist)))))))

(defun apply-renaming-to-use-hint-instances (vals renaming-alist)
  (declare (xargs :guard (and (use-hint-instance-listp vals)
                              (symbol-alistp renaming-alist))))
  (if (endp vals)
      nil
    (cons (apply-renaming-to-use-hint-instance (first vals) renaming-alist)
          (apply-renaming-to-use-hint-instances (rest vals) renaming-alist))))

;; Also used for :by hints.
(defun apply-renaming-to-use-hint (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (symbolp val)
      (apply-renaming-to-symbol val renaming-alist)
    (if (not (consp val))
        (er hard? 'apply-renaming-to-use-hint "Unsupported :use hint: ~x0." val)
      (if (use-hint-instancep val)
          (apply-renaming-to-use-hint-instance val renaming-alist)
        (if (use-hint-instance-listp val)
            (apply-renaming-to-use-hint-instances val renaming-alist)
          (er hard? 'apply-renaming-to-use-hint "Unsupported :use hint: ~x0." val))))))

(defun apply-renaming-to-induct-hint (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (eq t val)
      val
    (if (untranslated-termp val) ;TODO: Generalize this?
        (rename-fns-in-untranslated-term val renaming-alist)
      (er hard? 'apply-renaming-to-induct-hint "Unsupported :induct hint: ~x0." val))))

(defun apply-renaming-to-expand-hint-top-term (term renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (atom term)
      (er hard? 'apply-renaming-to-expand-hint-top-term "Unexpected :expand hint: ~x0." term)
    (case (ffn-symb term)
      (:free (if (not (= 2 (len (fargs term))))
                 (er hard? 'apply-renaming-to-expand-hint-top-term "Unexpected :expand hint: ~x0." term)
               `(:free ,(farg1 term) ,(apply-renaming-to-expand-hint-top-term (farg2 term) renaming-alist))))
      (:with (if (not (= 2 (len (fargs term))))
                 (er hard? 'apply-renaming-to-expand-hint-top-term "Unexpected :expand hint: ~x0." term)
               `(:with ,(apply-renaming-to-symbol-or-rune (farg1 term) renaming-alist)
                       ,(apply-renaming-to-expand-hint-top-term (farg2 term) renaming-alist))))
      (otherwise
       (if (not (and (untranslated-termp term) ; todo: call a more modern util and drop this?
                     (all-symbol-or-untranslated-lambda-exprp (strip-cdrs renaming-alist)) ; todo: move the guards of callers
                     ))
           (prog2$ (cw "NOTE: Unsupported term in apply-renaming-to-expand-hint-top-term (~x0). Not renaming it.~%" term)
                   term)
         (rename-fns-and-expand-lambdas-in-untranslated-term term renaming-alist))))))

(defun apply-renaming-to-expand-hint-top-terms (terms renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (not (consp terms))
      nil
    (cons (apply-renaming-to-expand-hint-top-term (first terms) renaming-alist)
          (apply-renaming-to-expand-hint-top-terms (rest terms) renaming-alist))))

(defun apply-renaming-to-expand-hint (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (eq :lambdas val)
      val
    (if (atom val)
        (er hard? 'apply-renaming-to-expand-hint "Unexpected :expand hint: ~x0." val)
      ;; It's either a term to be expanded, or a list of such terms:
      (if (symbolp (car val))
          ;; Single term:
          (apply-renaming-to-expand-hint-top-term val renaming-alist)
        ;; List of terms:
        (apply-renaming-to-expand-hint-top-terms val renaming-alist)))))

(defun apply-renaming-to-computed-theory (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (not (consp val))
      (er hard? 'apply-renaming-to-computed-theory "Unsupported theory term: ~x0." val)
    (let ((fn (ffn-symb val)))
      (if (and (eq fn 'quote)
               (consp (fargs val))
               (true-listp (farg1 val)))
          `'(,@(apply-renaming-to-symbols-or-runes (farg1 val) renaming-alist))
        (if (member-eq fn '(theory universal-theory current-theory))
            val
          (if (and (member-eq fn '(union-theories set-difference-theories intersection-theories
                                                  append ; TODO: handle n-ary case
                                                  function-theory executable-counterpart-theory)) ; not sure about these 2
                   (eql 2 (len (fargs val))))
              `(,fn ,(apply-renaming-to-computed-theory (farg1 val) renaming-alist)
                    ,(apply-renaming-to-computed-theory (farg2 val) renaming-alist))
            (er hard? 'apply-renaming-to-computed-theory "Unsupported theory in hint: ~x0." val)))))))

(defun apply-renaming-to-in-theory-hint (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (null val)                 ; nil is apparently legal
      val
    (if (not (consp val))
        (er hard? 'apply-renaming-to-in-theory-hint "Unsupported :in-theory hint: ~x0." val)
      (let ((fn (ffn-symb val)))
        (if (and (member-eq fn '(enable disable enable* disable*))
                 (true-listp (fargs val)))
            `(,fn ,@(apply-renaming-to-symbols-or-runes (fargs val) renaming-alist))
          (if (and (member-eq fn '(e/d e/d*))
                   (consp (cdr val))
                   (listp (cddr val))
                   (symbol-listp (farg1 val))
                   (symbol-listp (farg2 val)))
              `(,fn ,(apply-renaming-to-symbols-or-runes (farg1 val) renaming-alist)
                    ,(apply-renaming-to-symbols-or-runes (farg2 val) renaming-alist))
            (if (member-eq fn '(quote append union-theories set-difference-theories intersection-theories
                                      function-theory executable-counterpart-theory theory universal-theory current-theory))
                (apply-renaming-to-computed-theory val renaming-alist)
              (er hard? 'apply-renaming-to-in-theory-hint "Unsupported :in-theory hint: ~x0." val))))))))

;; Returns the new value that should be used for hint keyword KEY.
;; TODO: Handle more types of key
(defun apply-renaming-to-hint-value (key val renaming-alist)
  (declare (xargs :guard (and (keywordp key)
                              (symbol-alistp renaming-alist))))
  (if (or (eq :use key) (eq :by key))
      (apply-renaming-to-use-hint val renaming-alist)
    (if (eq :induct key)
        (apply-renaming-to-induct-hint val renaming-alist)
      (if (eq :do-not-induct key)
          val ;don't need to rename this (it may be a symbol used in names of lemmas generated by the prover in the case of proof failure)
        (if (eq :in-theory key)
            (apply-renaming-to-in-theory-hint val renaming-alist)
          (if (eq :expand key)
              (apply-renaming-to-expand-hint val renaming-alist)
            (prog2$ (cw "NOTE: Unsupported hint (~x0 ~x1). Not renaming it.~%" key val)
                    val)))))))

(defund apply-renaming-to-hint-keyword-value-list (keyword-value-list renaming-alist)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (symbol-alistp renaming-alist))
                  :guard-hints (("Goal" :in-theory (enable KEYWORD-VALUE-LISTP)))
                  ))
  (if (endp keyword-value-list)
      nil
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list))
           (renamed-val (apply-renaming-to-hint-value key val renaming-alist)))
      (cons key (cons renamed-val (apply-renaming-to-hint-keyword-value-list (rest (rest keyword-value-list)) renaming-alist))))))

(mutual-recursion
 ;; TODO: Handle more kinds of term
 ;; TERM is an untranslated term that returns a keyword-value-list, possibly as part of an error-triple
 (defun apply-renaming-to-computed-hint-term (term renaming-alist)
   (declare (xargs :guard (symbol-alistp renaming-alist)))
   (if (atom term)
       term ; could be one of the 7 allowed vars, or a constant
     (if (not (true-listp term))
         (er hard? 'apply-renaming-to-computed-hint-term "Unexpected hint: ~x0." term)
       (case (ffn-symb term)
         (quote (if (not (keyword-value-listp (unquote term)))
                    (er hard? 'apply-renaming-to-computed-hint-term "Unexpected hint: ~x0." term) ;; (cw "NOTE: Unsupported hint: ~x0. Not renaming it.~%" term) ; could it be quoted and return an error triple?
                  `(quote ,(apply-renaming-to-hint-keyword-value-list (unquote term) renaming-alist))))
         (and `(and ,@(apply-renaming-to-computed-hint-terms (fargs term) renaming-alist)))
         (if `(if ,@(apply-renaming-to-computed-hint-terms (fargs term) renaming-alist)))
         (std::returnspec-default-default-hint ; for now handle in an ad-hoc manner
          (if (not (= 3 (len (fargs term))))
              (er hard? 'apply-renaming-to-computed-hint-term "Unexpected hint: ~x0." term)
            (let ((fnname (farg1 term)))
              (if (not (myquotep fnname))
                  (er hard? 'apply-renaming-to-computed-hint-term "Unexpected hint: ~x0." term)
                (let ((unquoted-fnname (unquote fnname)))
                  (if (not (symbolp unquoted-fnname))
                      (er hard? 'apply-renaming-to-computed-hint-term "Unexpected hint: ~x0." term)
                    `(std::returnspec-default-default-hint ',(apply-renaming-to-symbol unquoted-fnname renaming-alist) ,(farg2 term) ,(farg3 term))))))))
         (otherwise (prog2$ (cw "NOTE: Unsupported hint: ~x0. Not renaming it.~%" term)
                            term))))))

 (defun apply-renaming-to-computed-hint-terms (terms renaming-alist)
   (declare (xargs :guard (symbol-alistp renaming-alist)))
   (if (not (consp terms))
       nil
     (cons (apply-renaming-to-computed-hint-term (first terms) renaming-alist)
           (apply-renaming-to-computed-hint-terms (rest terms) renaming-alist)))))

(defun apply-renaming-to-computed-hint (hint renaming-alist)
   (declare (xargs :guard (symbol-alistp renaming-alist)))
   (if (symbolp hint)
       hint ; abbreviation for a function call on 3, 4, or 7 args (todo: should we apply the renaming?)
     (apply-renaming-to-computed-hint-term hint renaming-alist)))

;; Renames functions mentioned in HINT.
(defun apply-renaming-to-hint (hint renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp (rest hint)))
            (er hard? 'apply-renaming-to-hint "Bad hint: ~x0." hint)
          (cons goal-spec (apply-renaming-to-hint-keyword-value-list keyword-value-list renaming-alist))))
    ;; computed hint:
    (apply-renaming-to-computed-hint hint renaming-alist)))

(defund apply-renaming-to-hints (hints renaming-alist)
  (declare (xargs :guard (and (true-listp hints)
                              (symbol-alistp renaming-alist))))
  (if (endp hints)
      nil
    (cons (apply-renaming-to-hint (first hints) renaming-alist)
          (apply-renaming-to-hints (rest hints) renaming-alist))))

(defund apply-renaming-to-hints-in-keyword-value-list (kv renaming-alist)
  (declare (xargs :guard (and (keyword-value-listp kv)
                              (symbol-alistp renaming-alist))))
  (if (endp kv)
      nil
    (if (endp (cdr kv))
        (er hard? 'apply-renaming-to-hints-in-keyword-value-list "Odd-length keyword-value list encountered")
      (let* ((key (first kv))
             (val (second kv))
             (val (if (eq key :hints)
                      (if (not (true-listp val)) ;strengthen check here?
                          (er hard? 'apply-renaming-to-hints-in-keyword-value-list "Ill-formed hints: ~x0" val)
                        (apply-renaming-to-hints val renaming-alist))
                    val)))
        (cons key
              (cons val
                    (apply-renaming-to-hints-in-keyword-value-list (cddr kv) renaming-alist)))))))

(defund apply-renaming-to-guard-hints-in-keyword-value-list (kv renaming-alist)
  (declare (xargs :guard (and (keyword-value-listp kv)
                              (symbol-alistp renaming-alist))))
  (if (endp kv)
      nil
    (if (endp (cdr kv))
        (er hard? 'apply-renaming-to-guard-hints-in-keyword-value-list "Odd-length keyword-value list encountered")
      (let* ((key (first kv))
             (val (second kv))
             (val (if (eq key :guard-hints)
                      (if (not (true-listp val)) ;strengthen check here?
                          (er hard? 'apply-renaming-to-guard-hints-in-keyword-value-list "Ill-formed hints: ~x0" val)
                        (apply-renaming-to-hints val renaming-alist))
                    val)))
        (cons key
              (cons val
                    (apply-renaming-to-hints-in-keyword-value-list (cddr kv) renaming-alist)))))))
