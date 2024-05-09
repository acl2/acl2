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
(local (include-book "kestrel/lists-light/reverse" :dir :system)) ; overkill?
(local (include-book "kestrel/typed-lists-light/true-list-listp" :dir :system))
; (include-book "tools/rulesets" :dir :system) ; not strictly needed

(defund union-equal-at-end (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (let ((new-items (set-difference-equal y x)))
    (append x new-items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General technique that should always work but is not as nice as the special
;; cases.
(defund enable-items-in-theory-expression-gen (expr enable-items starp)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp enable-items)
                              (booleanp starp))))
  (if starp
      `(union-theories ,expr (expand-ruleset ',enable-items world))
    `(union-theories ,expr ',enable-items)))

(defund strip-leading-nils (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      items
    (if (equal nil (first items))
        (strip-leading-nils (rest items))
      items)))

(defthm true-listp-of-strip-leading-nils
  (implies (true-listp items)
           (true-listp (strip-leading-nils items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-leading-nils))))

(defthm true-list-listp-of-strip-leading-nils
  (implies (true-list-listp items)
           (true-list-listp (strip-leading-nils items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-leading-nils))))

(defund strip-trailing-nils (items)
  (declare (xargs :guard (true-listp items)))
  (reverse (strip-leading-nils (reverse items))))

(defthm true-listp-of-strip-trailing-nils
  (implies (true-listp items)
           (true-listp (strip-trailing-nils items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-trailing-nils))))

(defthm true-list-listp-of-strip-trailing-nils
  (implies (true-list-listp items)
           (true-list-listp (strip-trailing-nils items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-trailing-nils))))

(defun add-items-to-enable-expression (old-enable-args new-enable-args starp)
  (declare (xargs :guard (and (true-listp old-enable-args)
                              (true-listp new-enable-args)
                              (booleanp starp))))
  (let ((enable-args (union-equal-at-end old-enable-args new-enable-args)))
    (if starp
        `(enable* ,@enable-args)
      `(enable ,@enable-args))))

(defun enable-items-in-e/d-expression (e/d-args enable-items starp)
  (declare (xargs :guard (and (true-list-listp e/d-args)
                              (true-listp enable-items)
                              (booleanp starp))
                  :guard-hints (("Goal" :in-theory (enable true-listp-of-car-when-true-list-listp
                                                           true-listp-of-car-of-last-when-true-list-listp)))))
  (let* ((e/d-args (strip-trailing-nils e/d-args))) ; any trailing empty lists do nothing
    (if (endp e/d-args)
        ;; no e/d args are left, so just make a regular enable:
        (if starp
            `(enable* ,@enable-items)
          `(enable ,@enable-items))
      (if (endp (rest e/d-args))
          ;; special case: only a single e/d arg is left, so it is just like an enable:
          (add-items-to-enable-expression (first e/d-args) enable-items starp)
        ;; there are at least 2 e/d args:
        (if (evenp (len e/d-args))
            ;; add the new items as a final arg to e/d (even length so far ensures they will be enabled, not disabled)
            (let ((final-e/d-args (append e/d-args (list enable-items))))
              (if starp
                  `(e/d* ,@final-e/d-args)
                `(e/d ,@final-e/d-args)))
          ;; odd number of existing args, so the final one is an enable, so merge into it:
          (let* ((non-final-args (butlast e/d-args 1))
                 (final-arg (car (last e/d-args)))
                 (new-final-arg (union-equal-at-end final-arg enable-items))
                 (final-e/d-args (append non-final-args (list new-final-arg))))
            (if starp
                `(e/d* ,@final-e/d-args)
              `(e/d ,@final-e/d-args))))))))

(defund enable-items-in-theory-expression (expr enable-items starp)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp enable-items)
                              (booleanp starp))))
  (if (eq 'nil expr)
      (if starp
          `(expand-ruleset ',enable-items world)
        (kwote enable-items))
    (if (not (consp expr))
        (er hard? 'enable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
      (let ((fn (ffn-symb expr)))
        (case fn
          (enable
           (add-items-to-enable-expression (fargs expr) enable-items starp))
          (enable*
           (add-items-to-enable-expression (fargs expr) enable-items t))
          (disable
           ;; can't tell if there is overlap (existing items might be theories),
           ;; so arrange to have the enable done after the disable:
           (if starp
               `(e/d* () ,(fargs expr) ,enable-items)
             `(e/d () ,(fargs expr) ,enable-items)))
          (disable*
           ;; can't tell if there is overlap (existing items might be theories),
           ;; so arrange to have the enable done after the disable:
           `(e/d* () ,(fargs expr) ,enable-items))
          (e/d
           (if (not (true-list-listp (fargs expr)))
               (er hard? 'enable-items-in-theory-expression "Illegal e/d expression: ~x0" expr)
             (enable-items-in-e/d-expression (fargs expr) enable-items starp)))
          (e/d*
           (if (not (true-list-listp (fargs expr)))
               (er hard? 'enable-items-in-theory-expression "Illegal e/d* expression: ~x0" expr)
             (enable-items-in-e/d-expression (fargs expr) enable-items t)))
          (quote (if starp
                     (enable-items-in-theory-expression-gen expr enable-items starp) ; will test starp again
                   (if (true-listp (unquote expr))
                       `(quote ,(union-equal-at-end (unquote expr) enable-items))
                     (er hard? 'enable-items-in-theory-expression "Illegal theory expression: ~x0" expr))))
          (append
           (enable-items-in-theory-expression-gen expr enable-items starp) ;todo: do better
           ;; (if (and (eq fn 'append)
           ;;          (null disable-runes)
           ;;          (consp (second expr))
           ;;          (eq (car (second expr)) 'quote)
           ;;          (true-listp (second expr)))
           ;;     `(append ,(enable-items-in-theory-expression (second expr) enable-items ())
           ;;              ,@(cddr expr))
           ;;   ..))
           )
          (otherwise (enable-items-in-theory-expression-gen expr enable-items starp)))))))

;; Returns a keyword-value-list.
(defund enable-items-in-hint-keyword-value-list (keyword-value-list enable-items starp)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp enable-items)
                              (booleanp starp))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list) ; no :in-theory found
      (if starp
          `(:in-theory (enable* ,@enable-items))
        `(:in-theory (enable ,@enable-items)))
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (enable-items-in-hint-keyword-value-list (rest (rest keyword-value-list)) enable-items starp)))
        (if (not (true-listp val))
            (er hard? 'enable-items-in-hint-keyword-value-list "Bad theory expression: ~x0." val)
          (cons key
                (cons (enable-items-in-theory-expression val enable-items starp)
                      (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                      )))))))

;; Returns a hint, such as ("Goal" :in-theory (enable foo)).
(defund enable-items-in-hint (hint enable-items starp)
  (declare (xargs :guard (and (true-listp enable-items)
                              (booleanp starp))))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp keyword-value-list))
            (er hard? 'enable-items-in-hint "Bad hint: ~x0." hint)
          `(,goal-spec ,@(enable-items-in-hint-keyword-value-list keyword-value-list enable-items starp))))
    ;; computed hint:
    hint ; todo
    ))

;; Returns a list of hints.
(defund enable-items-in-hints-aux (hints enable-items starp)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-items)
                              (booleanp starp))))
  (if (endp hints)
      nil
    (cons (enable-items-in-hint (first hints) enable-items starp)
          (enable-items-in-hints-aux (rest hints) enable-items starp))))

;; Changes the HINTS so that the ENABLE-ITEMS are always enabled.
;; (TODO: except for computed hints?).
;; todo: switch param order?
(defund enable-items-in-hints (hints enable-items starp)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp enable-items)
                              (booleanp starp))))
  (let ((new-hints (enable-items-in-hints-aux hints enable-items starp)))
    (if (some-hint-has-goal-specp hints "Goal")
        new-hints
      ;; If there is no hint on Goal, we need to add one, to ensure that the
      ;; enable-items are in fact enabled for the whole proof (this includes
      ;; the case of no hints at all):
      (cons (if starp
                `("Goal" :in-theory (enable* ,@enable-items))
              `("Goal" :in-theory (enable ,@enable-items)))
            new-hints))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General technique that should always work but is not as nice as the special
;; cases.
(defund disable-items-in-theory-expression-gen (expr disable-items starp)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp disable-items)
                              (booleanp starp))))
  (if starp
      `(set-difference-theories ,expr (expand-ruleset ',disable-items world))
    `(set-difference-theories ,expr ',disable-items)))

(defund disable-items-in-theory-expression (expr disable-items starp)
  (declare (xargs :guard (and (true-listp expr)
                              (true-listp disable-items)
                              (booleanp starp))))
  (if (eq 'nil expr)
      nil ; disabling in the empty theory just gives the empty theory
    (if (not (consp expr))
        (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
      (let ((fn (ffn-symb expr)))
        (case fn
          (enable
           (if starp
               `(e/d* ,(fargs expr) ,disable-items)
             `(e/d ,(fargs expr) ,disable-items)))
          (enable*
           `(e/d* ,(fargs expr) ,disable-items))
          ((disable disable*)
           (let ((old-items (fargs expr)))
             (if (not (true-listp old-items))
                 (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
               (let ((new-disable-args (union-equal-at-end old-items disable-items))
                     (disable-variant (if (or starp (eq fn 'disable*))
                                          'disable*
                                        'disable)))
                 `(,disable-variant ,@new-disable-args)))))
          (e/d
           ;; (let ((old-items (farg2 expr)))
           ;;   (if (not (true-listp old-items))
           ;;       (er hard? 'disable-items-in-theory-expression "Unsupported theory expression: ~x0." expr)
           ;;     (let ((new-disable-args (union-equal-at-end old-items disable-items)))
           ;;       `(e/d ,fn ,@new-disable-args))))
           (disable-items-in-theory-expression-gen expr disable-items starp) ;todo: do better
           )
          (e/d*
           (disable-items-in-theory-expression-gen expr disable-items starp) ;todo: do better
           )
          ;; (quote (disable-items-in-theory-expression-gen expr disable-items starp))
          ;; (append (disable-items-in-theory-expression-gen expr disable-items starp))
          (otherwise (disable-items-in-theory-expression-gen expr disable-items starp)))))))

;; Returns a keyword-value-list
(defund disable-items-in-hint-keyword-value-list (keyword-value-list disable-items starp)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp disable-items)
                              (booleanp starp))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list) ; no :in-theory found
      (if starp
          `(:in-theory (disable* ,@disable-items))
        `(:in-theory (disable ,@disable-items)))
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (disable-items-in-hint-keyword-value-list (rest (rest keyword-value-list)) disable-items starp)))
        (if (not (true-listp val))
            (er hard? 'disable-items-in-hint-keyword-value-list "Bad theory expression: ~x0." val)
          (cons key
                (cons (disable-items-in-theory-expression val disable-items starp)
                      (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                      )))))))

;; Returns a hint, such as ("Goal" :in-theory (disable foo)).
(defund disable-items-in-hint (hint disable-items starp)
  (declare (xargs :guard (and (true-listp disable-items)
                              (booleanp starp))))
  (if (and (consp hint)
           (stringp (first hint)))
      ;; common hint:
      (let ((goal-spec (first hint))
            (keyword-value-list (rest hint)))
        (if (not (keyword-value-listp keyword-value-list))
            (er hard? 'disable-items-in-hint "Bad hint: ~x0." hint)
          `(,goal-spec ,@(disable-items-in-hint-keyword-value-list keyword-value-list disable-items starp))))
    ;; computed hint:
    hint ; todo
    ))

;; Returns a list of hints.
(defund disable-items-in-hints-aux (hints disable-items starp)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable-items)
                              (booleanp starp))))
  (if (endp hints)
      nil
    (cons (disable-items-in-hint (first hints) disable-items starp)
          (disable-items-in-hints-aux (rest hints) disable-items starp))))

;; Changes the HINTS so that the DISABLE-ITEMS are always disabled.
;; (TODO: except for computed hints?).
;; todo: switch param order?
(defund disable-items-in-hints (hints disable-items starp)
  (declare (xargs :guard (and (true-listp hints)
                              (true-listp disable-items)
                              (booleanp starp))))
  (let ((new-hints (disable-items-in-hints-aux hints disable-items starp)))
    (if (some-hint-has-goal-specp hints "Goal")
        new-hints
      ;; If there is no hint on Goal, we need to add one, to ensure that the
      ;; disable-items are in fact disabled for the whole proof (this includes
      ;; the case of no hints at all):
      (cons (if starp
                `("Goal" :in-theory (disable* ,@disable-items))
              `("Goal" :in-theory (disable ,@disable-items)))
            new-hints))))

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
                (er hard? 'e/d-runes-in-theory-expression "Illegal theory expression: ~x0" expr))
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
;; TODO: The e/d-term may be an enable or a disable.
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
