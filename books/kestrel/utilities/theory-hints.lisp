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
; (include-book "tools/rulesets" :dir :system) ; not strictly needed

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
    (e/d-runes-in-hints-aux hints enable-runes disable-runes)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; move these?

(defund hint-has-goal-specp (hint target-goal-spec)
  (declare (xargs :guard (and (stringp target-goal-spec)
                              (standard-string-p target-goal-spec))))
  (and (consp hint) ; if not, it's a computed hint function
       (let ((goal-spec (car hint)))
         (and (stringp goal-spec) ; if not, we've got a computed hint
              (if (standard-string-p goal-spec) ; lets us call string-equal
                  t
                (er hard? 'hint-has-goal-specp "Unexpected goal spec: ~x0." goal-spec))
              ;; case-insensitive:
              (string-equal goal-spec target-goal-spec)))))

(defthm hint-has-goal-specp-forward-to-consp
  (implies (hint-has-goal-specp hint target-goal-spec)
           (consp hint))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hint-has-goal-specp))))

;; Gets the hint settings (a keyword-value-list) for the given goal-spec (e.g., "Goal").
(defund hint-settings-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (standard-string-p goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (hint-has-goal-specp hint goal-spec)
          (cdr hint) ; everything but the goal-spec
        (hint-settings-for-goal-spec goal-spec (rest hints))))))

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
(defund add-enable*/disable*-to-hint-settings (keyword-value-list enable*-items disable*-items)
  (declare (xargs :guard (and (keyword-value-listp keyword-value-list)
                              (true-listp enable*-items)
                              (true-listp disable*-items))
                  :guard-hints (("Goal" :in-theory (enable keyword-value-listp)))))
  (if (endp keyword-value-list)
      nil
    (let* ((key (first keyword-value-list))
           (val (second keyword-value-list)))
      (if (not (eq :in-theory key))
          (cons key (cons val (add-enable*/disable*-to-hint-settings (rest (rest keyword-value-list)) enable*-items disable*-items)))
        (cons key
              (cons (add-enable*/disable*-to-theory-expression val enable*-items disable*-items)
                    (rest (rest keyword-value-list)) ; don't recur, since duplicate hint keywords are prohibited
                    ))))))

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
        (if (not (keyword-value-listp (rest hint)))
            (er hard? 'add-enable*/disable*-to-hint "Bad hint: ~x0." hint)
          (cons goal-spec (add-enable*/disable*-to-hint-settings keyword-value-list enable*-items disable*-items))))
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
    (if (hint-settings-for-goal-spec "Goal" new-hints)
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
