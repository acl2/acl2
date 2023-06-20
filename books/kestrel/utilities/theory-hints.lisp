; A library about manipulating theory :hints
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system) ; todo: maybe drop?
(include-book "kestrel/hints/goal-specs" :dir :system)
; (include-book "tools/rulesets" :dir :system) ; not strictly needed

(defun union-equal-at-end (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (let ((new-items (set-difference-equal y x)))
    (append x new-items)))

;; todo: use this below:
(defun enable-items-in-theory-expression (expr enable-items)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp enable-items))))
  (if (eq 'nil expr)
      (kwote enable-items)
    (if (not (consp expr))
        (er hard? 'enable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
      (let ((fn (ffn-symb expr)))
        (case fn
          ((enable enable*)
           (let ((old-items (fargs expr)))
             (if (not (true-listp old-items))
                 (er hard? 'enable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
               (let ((new-enable-args (union-equal-at-end old-items enable-items)))
                 `(,fn ,@new-enable-args)))))
          (disable
           ;; can't tell if there is overlap (existing items might be theories),
           ;; so arrange to have the enable done after the disable:
           `(e/d () ,(fargs expr) ,enable-items))
          (disable*
           ;; can't tell if there is overlap (existing items might be theories),
           ;; so arrange to have the enable done after the disable:
           `(e/d* () ,(fargs expr) ,enable-items))
          (e/d
           `(union-theories ,expr ',enable-items) ;todo: do better
           )
          (e/d*
           `(union-theories ,expr ',enable-items) ;todo: do better
           )
          (quote (if (true-listp (unquote expr))
                     `(quote ,(union-equal-at-end (unquote expr) enable-items))
                   (er hard? 'enable-items-in-theory-expression "Illegal in-theory expression: ~x0" expr)))
          (append
           `(union-theories ,expr ',enable-items) ;todo: do better
           ;; (if (and (eq fn 'append)
           ;;          (null disable-runes)
           ;;          (consp (second expr))
           ;;          (eq (car (second expr)) 'quote)
           ;;          (true-listp (second expr)))
           ;;     `(append ,(enable-items-in-theory-expression (second expr) enable-items ())
           ;;              ,@(cddr expr))
           ;;   ..))
           )
          (otherwise `(union-theories ,expr ',enable-items)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun disable-items-in-theory-expression (expr disable-items)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp disable-items))))
  (if (eq 'nil expr)
      nil ; disabling in the empty theory just gives the empty theory
    (if (not (consp expr))
        (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
      (let ((fn (ffn-symb expr)))
        (case fn
          (enable
           `(e/d ,(fargs expr) ,disable-items))
          (enable*
           `(e/d* ,(fargs expr) ,disable-items))
          ((disable disable*)
           (let ((old-items (fargs expr)))
             (if (not (true-listp old-items))
                 (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
               (let ((new-disable-args (union-equal-at-end old-items disable-items)))
                 `(,fn ,@new-disable-args)))))
          (e/d
           ;; (let ((old-items (farg2 expr)))
           ;;   (if (not (true-listp old-items))
           ;;       (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
           ;;     (let ((new-disable-args (union-equal-at-end old-items disable-items)))
           ;;       `(e/d ,fn ,@new-disable-args))))
           `(set-difference-theories ,expr ',disable-items) ;todo: do better
           )
          (e/d*
           `(set-difference-theories ,expr ',disable-items) ;todo: do better
           )
          (quote `(set-difference-theories ,expr ',disable-items))
          (append `(set-difference-theories ,expr ',disable-items))
          (otherwise `(set-difference-theories ,expr ',disable-items)))))))

;; Returns a keyword-value-list
(defund disable-items-in-hint-keyword-value-list (keyword-value-list disable-items)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp disable-items))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list) ; no :in-theory found
      `(:in-theory (disable ,@disable-items))
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (disable-items-in-hint-keyword-value-list (rest (rest keyword-value-list)) disable-items)))
        (if (not (true-listp val))
            (er hard? 'disable-items-in-hint-keyword-value-list "Bad theory expression: ~x0." val)
          (cons key
                (cons (disable-items-in-theory-expression val disable-items)
                      (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                      )))))))

;; Returns a hint, such as ("Goal" :in-theory (disable fo)).
(defund disable-items-in-hint (hint disable-items)
  (declare (xargs :guard (true-listp disable-items)))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp keyword-value-list))
            (er hard? 'disable-items-in-hint "Bad hint: ~x0." hint)
          `(,goal-spec ,@(disable-items-in-hint-keyword-value-list keyword-value-list disable-items))))
    ;; computed hint:
    hint ; todo
    ))

;; Returns a list of hints.
(defund disable-items-in-hints-aux (hints disable-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable-items))))
  (if (endp hints)
      nil
    (cons (disable-items-in-hint (first hints) disable-items)
          (disable-items-in-hints-aux (rest hints) disable-items))))

(defun disable-items-in-hints (hints disable-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable-items))))
  (if (endp hints) ; No hints given, so add one to do the disable (TODO: What if only subgoal hints are given?)
      `(("Goal" :in-theory (disable ,@disable-items)))
    (disable-items-in-hints-aux hints disable-items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun e/d-runes-in-theory-expression (expr enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (null expr) ; nil is apparently legal
      expr
    (if (not (consp expr))
        (er hard? 'e/d-runes-in-theory-expression "Unsupported :in-theory hint: ~x0." expr)
      (let ((fn (ffn-symb expr)))
        (if (member fn '(enable disable e/d enable* disable* e/d*))
            (b* (((mv old-enabled old-disabled star-p)
                  (case-match expr
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
                       (prog2$ (er hard? 'e/d-runes-in-theory-expression "Illegal ~x0: ~x1" fn expr)
                               (mv nil nil nil))))
                    (('e/d* enabled . disabledl) ; can the disabled list be omitted?
                     (if (and (true-listp enabled)
                              (true-listp (car disabledl)))
                         (mv enabled (car disabledl) t)
                       (prog2$ (er hard? 'e/d-runes-in-theory-expression "Illegal ~x0: ~x1" fn expr)
                               (mv nil nil nil))))
                    (& (prog2$ (er hard? 'e/d-runes-in-theory-expression "Illegal ~x0: ~x1" fn expr)
                               (mv nil nil nil)))))
                 (new-enabled (append old-enabled enable-runes))
                 (new-disabled (append old-disabled disable-runes)))
              (if (null new-disabled)
                  `(,(if star-p 'enable* 'enable) ,@new-enabled)
                (if (null new-enabled)
                    `(,(if star-p 'disable* 'disable) ,@new-disabled)
                  `(,(if star-p 'e/d* 'e/d) ,new-enabled ,new-disabled))))
          (if (equal fn 'quote)
              (if (true-listp (second expr))
                  `(quote ,(union-equal (set-difference-equal (second expr) disable-runes)
                                        enable-runes))
                (er hard? 'e/d-runes-in-theory-expression "Illegal in-theory expression: ~x0" expr))
            (if (and (eq fn 'append)
                     (null disable-runes)
                     (consp (second expr))
                     (eq (car (second expr)) 'quote)
                     (true-listp (second expr)))
                `(append ,(e/d-runes-in-theory-expression (second expr) enable-runes ())
                         ,@(cddr expr))
              (let* ((enable-term (if enable-runes
                                      `(union-theories ,expr ',enable-runes)
                                    expr)))
                (if disable-runes
                    `(set-difference-theories ,enable-term ',disable-runes)
                  enable-term)))))))))

(defund e/d-runes-in-hint-keyword-value-list (keyword-value-list enable-runes disable-runes)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp enable-runes)
                              (true-listp disable-runes))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list)
      nil
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (e/d-runes-in-hint-keyword-value-list (rest (rest keyword-value-list)) enable-runes disable-runes)))
        (if (not (true-listp val))
            (er hard? 'e/d-runes-in-hint-keyword-value-list "Bad theory expression: ~x0." val)
          (cons key
                (cons (e/d-runes-in-theory-expression val enable-runes disable-runes)
                      (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                      )))))))

;; can the enable-items and disable-items both be empty?
(defun make-in-theory-hint-setting (enable-items disable-items)
  (declare (xargs :guard (and (true-listp enable-items)
                              (true-listp disable-items))))
  (if (null enable-items)
      `(disable ,@disable-items) ; might not be any disable-items
    (if (null disable-items)
        `(enable ,@enable-items)
      `(e/d ,enable-items ,disable-items))))

;; Enable and disable the given items in HINT.
;; TODO: Rename in analogy with add-enable*/disable*-to-hint
(defun e/d-runes-in-hint (hint enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp keyword-value-list))
            (er hard? 'e/d-runes-in-hint "Bad hint: ~x0." hint)
          (let ((in-theory (assoc-keyword :in-theory keyword-value-list)))
            (if (not in-theory)
                `(,goal-spec ,@keyword-value-list :in-theory ,(make-in-theory-hint-setting enable-runes disable-runes))
              `(,goal-spec ,@(e/d-runes-in-hint-keyword-value-list keyword-value-list enable-runes disable-runes))))))
    ;; computed hint:
    hint ; todo
    ))

(defund e/d-runes-in-hints-aux (hints enable-runes disable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-runes)
                              (true-listp disable-runes))))
  (if (endp hints)
      nil
    (cons (e/d-runes-in-hint (first hints) enable-runes disable-runes)
          (e/d-runes-in-hints-aux (rest hints) enable-runes disable-runes))))

;; TODO: These are not necessarily runes.
(defun enable-runes-in-hints (hints enable-runes)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-runes))))
  (if (endp hints)                      ; No hints given
      `(("Goal" :in-theory (enable ,@enable-runes)))
    (e/d-runes-in-hints-aux hints enable-runes ())))

;; (defun disable-runes-in-hints (hints disable-runes)
;;   (declare (xargs :guard (and (true-listp hints)
;;                               (true-listp disable-runes))))
;;   (if (endp hints)                      ; No hints given
;;       `(("Goal" :in-theory (disable ,@disable-runes)))
;;     (e/d-runes-in-hints-aux hints () disable-runes)))

;; (defun e/d-runes-in-hints (hints enable-runes disable-runes)
;;   (declare (xargs :guard (and (true-listp hints)
;;                               (true-listp enable-runes)
;;                               (true-listp disable-runes))))
;;   (if (endp hints)                      ; No hints given
;;       `(("Goal" :in-theory (e/d ,@enable-runes ,@disable-runes)))
;;     (e/d-runes-in-hints-aux hints enable-runes disable-runes)))

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

;; TODO: These are not necessarily runes.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Changes EXPR, which is a theory-expression suitable for use with :in-theory,
;; to enable/disable the ENABLE*-ITEMS/DISABLE*-ITEMS, which are suitable for
;; passing to enable*/disable*.
;; Note that the enabling is done first, then the disabling.
;;TODO: Do better in common cases (calls to enable, enable*, disable, disable*,
;; e/d, e/d*)!
(defund add-enable*/disable*-to-theory-expression (expr enable*-items disable*-items)
  (declare (xargs :guard (and ;; expr
                          (true-listp enable*-items)
                          (true-listp disable*-items))))
  `(set-difference-theories
    (union-theories (expand-ruleset ',enable*-items world)
                    ,expr)
    (expand-ruleset ',disable*-items world)))

;; Ensures that the ENABLE*-ITEMS/DISABLE*-ITEMS, which are suitable for
;; passing to ENABLE*/DISABLE*, are enabled/disabled in the KEYWORD-VALUE-LIST.
;; Note that the enabling is done first, then the disabling.
(defund add-enable*/disable*-to-hint-keyword-value-list (keyword-value-list enable*-items disable*-items)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp enable*-items)
                              (true-listp disable*-items))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list)
      nil
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (add-enable*/disable*-to-hint-keyword-value-list (rest (rest keyword-value-list)) enable*-items disable*-items)))
        (cons key
              (cons (add-enable*/disable*-to-theory-expression val enable*-items disable*-items)
                    (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                    ))))))

;; can the enable-items and disable-items both be empty?
(defun make-in-theory-hint-setting* (enable*-items disable*-items)
  (declare (xargs :guard (and (true-listp enable*-items)
                              (true-listp disable*-items))))
  (if (null enable*-items)
      `(disable* ,@disable*-items) ; might not be any disable-items
    (if (null disable*-items)
        `(enable* ,@enable*-items)
      `(e/d* ,enable*-items ,disable*-items))))

;; Ensures that the ENABLE*-ITEMS/DISABLE*-ITEMS, which are suitable for
;; passing to ENABLE*/DISABLE*, are enabled/disabled in the HINT (TODO: except
;; for computed hints?).  Note that the enabling is done first, then the
;; disabling.
(defun add-enable*/disable*-to-hint (hint enable*-items disable*-items)
  (declare (xargs :guard (and ;; (true-listp hint)
                          (true-listp enable*-items)
                          (true-listp disable*-items))))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp keyword-value-list))
            (er hard? 'add-enable*/disable*-to-hint "Bad hint: ~x0." hint)
          (let ((in-theory (assoc-keyword :in-theory keyword-value-list)))
            (if (not in-theory)
                `(,goal-spec ,@keyword-value-list :in-theory ,(make-in-theory-hint-setting* enable*-items disable*-items))
              `(,goal-spec ,@(add-enable*/disable*-to-hint-keyword-value-list keyword-value-list enable*-items disable*-items))))))
    ;; computed hint:
    hint ; todo
    ))

;; Ensures that the ENABLE*-ITEMS/DISABLE*-ITEMS, which are suitable for
;; passing to ENABLE*/DISABLE*, are enabled/disabled in the HINTS (TODO: except
;; for computed hints?).
(defun add-enable*/disable*-to-all-hints (hints enable*-items disable*-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable*-items)
                              (true-listp disable*-items))))
  (if (endp hints)
      nil
    (cons (add-enable*/disable*-to-hint (first hints) enable*-items disable*-items)
          (add-enable*/disable*-to-all-hints (rest hints) enable*-items disable*-items))))

;; Ensures that the ENABLE*-ITEMS/DISABLE*-ITEMS, which are suitable for
;; passing to ENABLE*/DISABLE*, are enabled/disabled in the HINTS (TODO: except
;; for computed hints?).
(defun add-enable*/disable*-to-hints (hints enable*-items disable*-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable*-items)
                              (true-listp disable*-items))))
  (let ((new-hints (add-enable*/disable*-to-all-hints hints enable*-items disable*-items)))
    (if (hint-keyword-value-list-for-goal-spec "Goal" new-hints)
        ;; usual case (hints for "Goal" were present):
        new-hints
      ;; no hint on Goal, so make one:
      (cons `("Goal" :in-theory (e/d* (,@enable*-items) (,@disable*-items))) ; todo: make nicer
            new-hints))))

;; Ensures that the ENABLE*-ITEMS, which are suitable for passing to
;; ENABLE*, are enabled in the HINTS (TODO: except for computed hints?).
(defun add-enable*-to-hints (hints enable*-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable*-items))))
  (add-enable*/disable*-to-hints hints enable*-items nil))

;; Ensures that the DISABLE*-ITEMS, which are suitable for passing to
;; DISABLE*, are disabled in the HINTS (TODO: except for computed hints?).
(defun add-disable*-to-hints (hints disable*-items)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable*-items))))
  (add-enable*/disable*-to-hints hints nil disable*-items))
