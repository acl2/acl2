; A library about manipulating theory :hints
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system) ; todo: maybe drop?

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
