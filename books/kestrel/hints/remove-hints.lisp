; Utilities for removing hints and parts of hints
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/hints/combine-hints" :dir :system)
(include-book "kestrel/hints/goal-specs" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(include-book "kestrel/lists-light/remove-nth" :dir :system)

(defund remove-hints-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (standard-string-p goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (hint-has-goal-specp hint goal-spec)
          ;; Keep going, as there may be more matches:
          (remove-hints-for-goal-spec goal-spec (rest hints))
        (cons hint (remove-hints-for-goal-spec goal-spec (rest hints)))))))

;; TODO: Replace "break" in these names with "remove"?
;; WARNING: Keep this in sync with break-hint-setting-in-nth-way.
(defun num-ways-to-break-hint-setting (keyword val)
  (declare (xargs :guard (keywordp keyword)))
  (case keyword
    (:by 1) ; can only remove the whole thing
    (:cases 1) ; can only remove the whole thing (todo: well, we could remove one case?)
    (:induct 1) ; can only remove the whole thing
    (:nonlinearp 1) ; can only remove the whole thing
    (:do-not (if (and (quotep val)
                      (consp (cdr val)))
                 ;; can remove each thing in the list:
                 (len (unquote val))
               1 ; can only remove the whole thing
               ))
    (:expand (len (acl2::desugar-expand-hint val)))
    (:use (len (acl2::desugar-use-hint val)))
    (:in-theory (if (or (call-of 'acl2::enable val)
                        (call-of 'acl2::disable val))
                    (len (fargs val))
                  (if (call-of 'acl2::e/d val)
                      (let ((lists (fargs val)))
                        ;; Only mess with the first 2:
                        (+ (if (< 0 (len lists)) (len (first lists)) 0)
                           (if (< 1 (len lists)) (len (second lists)) 0)))
                    ;; TODO: Handle enable*, disable*, and e/d*:
                    1 ; can only remove the whole thing
                    )))
    (otherwise 0)))

;; n is 0-based and is known to be less than the number of ways to break the hint-setting.
;; Returns (mv breakage-type result), where RESULT is a list (possibly nil) to be spliced into the hint settings, replacing the KEYWORD and VAL.
;; WARNING: Keep this in sync with num-ways-to-break-hint-setting.
;; WANRING: Keep this in sync with decode-breakage-type.
(defun break-hint-setting-in-nth-way (n keyword val)
  (declare (xargs :guard (and (natp n)
                              (keywordp keyword)
                              (< n (num-ways-to-break-hint-setting keyword val)))
                  :guard-hints (("Goal" :in-theory (enable natp)))))
  (case keyword
    (:by (mv `(:remove-by ,val) nil))                 ; can only remove the whole thing
    (:cases (mv `(:remove-cases ,val) nil))           ; can only remove the whole thing
    (:induct (mv `(:remove-induct ,val) nil))         ; can only remove the whole thing
    (:nonlinearp (mv `(:remove-nonlinearp ,val) nil)) ; can only remove the whole thing
    (:do-not (if (and (quotep val)
                      (consp (cdr val))
                      (true-listp (unquote val))
                      )
                 ;; remove one thing in the list:
                 (mv `(:remove-do-not-item ,(nth n (unquote val)))
                     (list :do-not (kwote (remove-nth n (unquote val)))))
               (mv `(:remove-do-not ,val) nil) ; can only remove the whole thing
               ))
    (:expand (let ((desugared-val (acl2::desugar-expand-hint val)))
               (mv `(:remove-expand-item ,(nth n desugared-val))
                   (list :expand (remove-nth n desugared-val)))))
    (:use (let ((desugared-val (acl2::desugar-use-hint val)))
            (mv `(:remove-use-item ,(nth n desugared-val))
                (list :use (remove-nth n desugared-val)))))
    (:in-theory (if (and (call-of 'acl2::enable val)
                         (true-listp (cdr val)))
                    (mv `(:remove-enable-item ,(nth n (fargs val)))
                        (list :in-theory `(,(ffn-symb val) ,@(remove-nth n (fargs val)))))
                  (if (and (call-of 'acl2::disable val)
                           (true-listp (cdr val)))
                      (mv `(:remove-disable-item ,(nth n (fargs val)))
                          (list :in-theory `(,(ffn-symb val) ,@(remove-nth n (fargs val)))))
                    (if (and (call-of 'acl2::e/d val)
                             (true-list-listp (cdr val)))
                        (let ((lists (fargs val)))
                          (if (< n (len (first lists)))
                              (mv `(:remove-enable-item ,(nth n (first lists))) ; or we could indicate it was in an e/d
                                  (list :in-theory `(e/d ,(remove-nth n (first lists)) ,@(rest lists))))
                            ;; Only mess with the first 2, so it must be in the second one:
                            (mv `(:remove-disable-item ,(nth (- n (len (first lists))) (second lists))) ; or we could indicate it was in an e/d
                                (list :in-theory `(e/d ,(first lists)
                                                       ,(remove-nth (- n (len (first lists))) (second lists))
                                                       ,@(rest (rest lists)))))))
                      ;; TODO: Handle enable*, disable*, and e/d*:
                      (mv `(:remove-in-theory ,val)
                          nil) ; can only remove the whole thing
                      ))))
    (otherwise (mv :error (er hard 'break-hint-setting-in-nth-way "Unhandled case")))))

(defun num-ways-to-break-hint-keyword-value-list (hint-keyword-value-list)
  (declare (xargs :guard (keyword-value-listp hint-keyword-value-list)))
  (if (endp hint-keyword-value-list)
      0
    (let ((keyword (car hint-keyword-value-list))
          (val (cadr hint-keyword-value-list)))
      (+ (num-ways-to-break-hint-setting keyword val) ;; todo: generalize num-ways-to-break-hint-setting but filter here for hints the models know about.
         (num-ways-to-break-hint-keyword-value-list (cddr hint-keyword-value-list))))))

;; Returns (mv breakage-type hint-keyword-value-list).
; n is 0-based
(defun break-hint-keyword-value-list-in-nth-way (n hint-keyword-value-list)
  (declare (xargs :guard (and (natp n)
                              (keyword-value-listp hint-keyword-value-list)
                              (< n (num-ways-to-break-hint-keyword-value-list hint-keyword-value-list)))
                  :measure (len hint-keyword-value-list)))
  (if (endp hint-keyword-value-list)
      (mv :error (er hard? 'break-hint-keyword-value-list-in-nth-way "Ran out of hint settings!"))
    (let ((keyword (car hint-keyword-value-list))
          (val (cadr hint-keyword-value-list)))
      (let ((ways (num-ways-to-break-hint-setting keyword val)))
        (if (< n ways)
            (mv-let (breakage-type result)
              (break-hint-setting-in-nth-way n keyword val)
              (mv breakage-type
                  (append result (cddr hint-keyword-value-list))))
          (mv-let (breakage-type new-cddr)
            (break-hint-keyword-value-list-in-nth-way (- n ways) (cddr hint-keyword-value-list))
            (mv breakage-type
                (cons keyword (cons val new-cddr)))))))))
