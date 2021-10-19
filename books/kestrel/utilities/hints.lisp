; A library about manipulating :hints
;
; Copyright (C) 2017-2020 Kestrel Institute
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

(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)
;(include-book "kestrel/utilities/keyword-value-lists2" :dir :system)

(defun apply-renaming-to-symbol (sym renaming-alist)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-alistp renaming-alist))))
  (if (assoc-eq sym renaming-alist)
      (lookup-eq sym renaming-alist)
    sym))

(defun apply-renaming-to-symbols (syms renaming-alist)
  (declare (xargs :guard (and (symbol-listp syms)
                              (symbol-alistp renaming-alist))))
  (if (endp syms)
      nil
    (cons (apply-renaming-to-symbol (first syms) renaming-alist)
          (apply-renaming-to-symbols (rest syms) renaming-alist))))

(defun apply-renaming-to-rune (rune renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (symbolp rune)
      (apply-renaming-to-symbol rune renaming-alist)
    (if (consp rune)
        (cons (car rune) (sublis renaming-alist (cdr rune)))
      rune)))

(defun apply-renaming-to-runes (runes renaming-alist)
  (declare (xargs :guard (and (true-listp runes)
                              (symbol-alistp renaming-alist))))
  (if (endp runes)
      nil
    (cons (apply-renaming-to-rune (first runes) renaming-alist)
          (apply-renaming-to-runes (rest runes) renaming-alist))))

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
             ,@(rename-fns-in-var-untranslated-term-pairs subst renaming-alist))))))

(defun apply-renaming-to-use-hint-instances (vals renaming-alist)
  (declare (xargs :guard (and (use-hint-instance-listp vals)
                              (symbol-alistp renaming-alist))))
  (if (endp vals)
      nil
    (cons (apply-renaming-to-use-hint-instance (first vals) renaming-alist)
          (apply-renaming-to-use-hint-instances (rest vals) renaming-alist))))

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

(defun apply-renaming-to-computed-theory (val renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (not (consp val))
      (er hard? 'apply-renaming-to-computed-theory "Unsupported theory term: ~x0." val)
    (let ((fn (ffn-symb val)))
      (if (and (eq fn 'quote)
               (consp (fargs val))
               (true-listp (farg1 val)))
          `'(,@(apply-renaming-to-runes (farg1 val) renaming-alist))
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
            `(,fn ,@(apply-renaming-to-runes (fargs val) renaming-alist))
          (if (and (member-eq fn '(e/d e/d*))
                   (consp (cdr val))
                   (listp (cddr val))
                   (symbol-listp (farg1 val))
                   (symbol-listp (farg2 val)))
              `(,fn ,(apply-renaming-to-runes (farg1 val) renaming-alist)
                    ,(apply-renaming-to-runes (farg2 val) renaming-alist))
            (if (member-eq fn '(quote append union-theories set-difference-theories intersection-theories
                                      function-theory executable-counterpart-theory theory universal-theory current-theory))
                (apply-renaming-to-computed-theory val renaming-alist)
              (er hard? 'apply-renaming-to-in-theory-hint "Unsupported :in-theory hint: ~x0." val))))))))

;; Returns the new value that should be used for hint keyword KEY.
;; TODO: Handle more types of hint
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
          (prog2$ (cw "NOTE: Unsupported hint (~x0 ~x1). Not renaming it.~%" key val)
                  val))))))

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

;; TODO: Handle computed hints
(defun apply-renaming-to-hint (hint renaming-alist)
  (declare (xargs :guard (symbol-alistp renaming-alist)))
  (if (and (consp hint)
           (stringp (first hint))
           (keyword-value-listp (rest hint)))
      (let ((goal-name (first hint))
            (keyword-value-list (rest hint)))
        (cons goal-name (apply-renaming-to-hint-keyword-value-list keyword-value-list renaming-alist)))
    (case-match hint
      (('std::returnspec-default-default-hint ('quote fn-name) arg2 arg3)  ; for now handle in an ad-hoc manner
       `(std::returnspec-default-default-hint ',(apply-renaming-to-symbol (and (symbolp fn-name) fn-name)
                                                                          renaming-alist)
                                              ,arg2 ,arg3))
      (('and c1 c2)
       `(and ,(apply-renaming-to-hint c1 renaming-alist)
             ,(apply-renaming-to-hint c2 renaming-alist)))
      (('quote l)
       `(quote ,(apply-renaming-to-hint l renaming-alist)))
      (& (prog2$ (cw "NOTE: Unsupported hint: ~x0. Not renaming it.~%" hint)
                 hint)))))

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

;; enable-disable-runes-in-hints

(defun e/d-runes-in-theory-hint (val enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp val)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (null val)                        ; nil is apparently legal
      val
    (if (not (consp val))
        (er hard? 'e/d-runes-in-theory-hint "Unsupported :in-theory hint: ~x0." val)
      (let ((fn (ffn-symb val)))
        (if (member fn '(enable disable e/d enable* disable* e/d*))
            (b* (((mv old-enabled old-disabled star-p)
                  (case-match val
                    (('enable . enabled)
                     (mv enabled nil nil))
                    (('enable* . enabled)
                     (mv enabled nil t))
                    (('disable . disabled)
                     (mv nil disabled nil))
                    (('disable* . disabled)
                     (mv nil disabled t))
                    (('e/d enabled . disabledl) ; can the disabled list be omitted?
                     (if (and (true-listp enabled)
                              (true-listp (car disabledl)))
                         (mv enabled (car disabledl) nil)
                       (prog2$ (er hard? 'e/d-runes-in-theory-hint "Illegal ~x0: ~x1" fn val)
                               (mv nil nil nil))))
                    (('e/d* enabled . disabledl) ; can the disabled list be omitted?
                     (if (and (true-listp enabled)
                              (true-listp (car disabledl)))
                         (mv enabled (car disabledl) t)
                       (prog2$ (er hard? 'e/d-runes-in-theory-hint "Illegal ~x0: ~x1" fn val)
                               (mv nil nil nil))))
                    (& (prog2$ (er hard? 'e/d-runes-in-theory-hint "Illegal ~x0: ~x1" fn val)
                               (mv nil nil nil)))))
                 (new-enabled (append old-enabled enable-runes))
                 (new-disabled (append old-disabled disable-runes)))
              (if (null new-disabled)
                  `(,(if star-p 'enable* 'enable) ,@new-enabled)
                (if (null new-enabled)
                    `(,(if star-p 'disable* 'disable) ,@new-disabled)
                  `(,(if star-p 'e/d* 'e/d) ,new-enabled ,new-disabled))))
          (if (equal fn 'quote)
              (if (true-listp (second val))
                  `(quote ,(union-equal (set-difference-equal (second val) disable-runes)
                                        enable-runes))
                (er hard? 'e/d-runes-in-theory-hint "Illegal in-theory expression: ~x0" val))
           (if (and (eq fn 'append)
                    (null disable-runes)
                    (consp (second val))
                    (eq (car (second val)) 'quote)
                    (true-listp (second val)))
               `(append ,(e/d-runes-in-theory-hint (second val) enable-runes ())
                        ,@(cddr val))
             (let* ((enable-term (if enable-runes
                                        `(union-theories ,val ',enable-runes)
                                      val)))
                  (if disable-runes
                      `(set-difference-theories ,enable-term ',disable-runes)
                    enable-term)))))))))

(defun e/d-runes-in-hint-value (key val enable-runes disable-runes)
  (declare (xargs :guard (and (keywordp key)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (and (eq :in-theory key)
           (true-listp val))
      (e/d-runes-in-theory-hint val enable-runes disable-runes)
    val))

(defund e/d-runes-in-hint-keyword-value-list (keyword-value-list enable-runes disable-runes)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp enable-runes)
                              (true-listp disable-runes))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list)
      nil
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list))
           (new-val (e/d-runes-in-hint-value key val enable-runes disable-runes)))
      (cons key (cons new-val (e/d-runes-in-hint-keyword-value-list (rest (rest keyword-value-list)) enable-runes disable-runes))))))

(defun e/d-runes-in-hint (hint enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (and (consp hint)
           (stringp (first hint))
           (keyword-value-listp (rest hint)))
      (let ((goal-name (first hint))
            (keyword-value-list (rest hint)))
        (cons goal-name (e/d-runes-in-hint-keyword-value-list keyword-value-list enable-runes disable-runes)))
    hint))

(defund e/d-runes-in-hints-aux (hints enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (endp hints)
      nil
    (cons (e/d-runes-in-hint (first hints) enable-runes disable-runes)
          (e/d-runes-in-hints-aux (rest hints) enable-runes disable-runes))))

(defun enable-runes-in-hints (hints enable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-runes))))
  (if (endp hints)                      ; No hints given
      `(("Goal" :in-theory (enable ,@enable-runes)))
    (e/d-runes-in-hints-aux hints enable-runes ())))

(defun disable-runes-in-hints (hints disable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable-runes))))
  (if (endp hints)                      ; No hints given
      `(("Goal" :in-theory (disable ,@disable-runes)))
    (e/d-runes-in-hints-aux hints () disable-runes)))

(defun e/d-runes-in-hints (hints enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (endp hints)                      ; No hints given
      `(("Goal" :in-theory (e/d ,@enable-runes ,@disable-runes)))
    (e/d-runes-in-hints-aux hints () disable-runes)))

(defun parse-enable-disable-e/d (e/d-term)
  (declare (xargs :guard (true-listp e/d-term)))
  (case-match e/d-term
    (('enable . enabled)
     (mv enabled nil))
    (('disable . disabled)
     (mv nil disabled))
    (('e/d enabled . disabledl)         ; can the disabled list be omitted?
     (mv enabled (car disabledl)))
    (& (mv nil nil))))

(defun enable-disable-runes-in-hints (hints e/d-term)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp e/d-term))))
  (if (endp e/d-term)
      hints
    (b* (((mv enable-runes disable-runes)
          (parse-enable-disable-e/d e/d-term)))
      (if (and (true-listp enable-runes)
               (true-listp disable-runes))
          (e/d-runes-in-hints-aux (or hints
                                      '(("Goal" :in-theory (enable))))
                                  enable-runes disable-runes)
        (er hard? 'e/d-term "Illegal enabling/disabling term: ~x0" e/d-term)))))
