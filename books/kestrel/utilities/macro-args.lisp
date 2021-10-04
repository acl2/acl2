; Recognizers for macro args (formals, etc.)
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "quote")

(local (in-theory (disable mv-nth)))

(defund macro-argp (arg)
  (declare (xargs :guard t))
  (or (symbolp arg) ; regular formal or &whole, &optional, etc.
      (and (true-listp arg)
           (or (and (= 1 (len arg)) ; (arg)
                    (symbolp (first arg)))
               (and (= 2 (len arg)) ; (arg 'init)
                    (symbolp (first arg))
                    (myquotep (second arg)))
               (and (= 3 (len arg)) ; (arg 'init supplied-p)
                    (symbolp (first arg))
                    (myquotep (second arg))
                    (symbolp (third arg)))))))

(defund macro-arg-listp (args)
  (declare (xargs :guard t))
  (if (atom args)
      (null args)
    (and (macro-argp (first args))
         (macro-arg-listp (rest args)))))

(defthm macro-argp-of-car
  (implies (macro-arg-listp macro-args)
           (macro-argp (car macro-args)))
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

(defthm macro-arg-listp-of-cdr
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (cdr macro-args)))
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

(defthm macro-arg-listp-of-cons
  (equal (macro-arg-listp (cons macro-arg macro-args))
         (and (macro-argp macro-arg)
              (macro-arg-listp macro-args)))
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

(defthm macro-arg-listp-forward-to-true-listp
  (implies (macro-arg-listp macro-args)
           (true-listp macro-args))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable macro-arg-listp))))

;;;
;;; handling macro args
;;;

;; Returns (mv name default).
;; TODO: Would we ever want the optional third thing, suppliedp?
(defund keyword-or-optional-arg-name-and-default (macro-arg)
  (declare (xargs :guard (macro-argp macro-arg)
                  :guard-hints (("Goal" :in-theory (enable macro-argp)))))
  (if (symbolp macro-arg)
      (mv macro-arg nil)
    (if (< (len macro-arg) 2)
        (mv (first macro-arg) nil) ; no default given, so nil
      (mv (first macro-arg) (unquote (second macro-arg))))))

;; Skip an initial use of &whole, if present.
(defund maybe-skip-whole-arg (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (if (and (consp macro-args)
           (eq '&whole (first macro-args)))
      (cddr macro-args)
    macro-args))

(defthm macro-arg-listp-of-maybe-skip-whole-arg
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (maybe-skip-whole-arg macro-args)))
  :hints (("Goal" :in-theory (enable maybe-skip-whole-arg))))

(defund remove-rest-and-body-from-macro-args (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (if (endp macro-args)
      nil
    (let ((arg (first macro-args)))
      (if (or (eq '&rest arg)
              (eq '&body arg))
          (remove-rest-and-body-from-macro-args (rest (rest macro-args))) ;skip the &rest/&body and its var
        (cons arg (remove-rest-and-body-from-macro-args (rest macro-args)))))))

(defthm macro-arg-listp-of-remove-rest-and-body-from-macro-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (remove-rest-and-body-from-macro-args macro-args)))
  :hints (("Goal" :in-theory (enable remove-rest-and-body-from-macro-args))))

;; This remove &allow-other-keys anywhere it appears, though it actually can only appear at the end.
(defund remove-allow-other-keys-from-macro-args (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (if (endp macro-args)
      nil
    (let ((arg (first macro-args)))
      (if (eq '&allow-other-keys arg)
          (remove-allow-other-keys-from-macro-args (rest macro-args))
        (cons arg (remove-allow-other-keys-from-macro-args (rest macro-args)))))))

(defthm macro-arg-listp-of-remove-allow-other-keys-from-macro-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (remove-allow-other-keys-from-macro-args macro-args)))
  :hints (("Goal" :in-theory (enable remove-allow-other-keys-from-macro-args))))

;; See :doc macro-args
(defun lambda-list-keywordp (macro-arg)
  (declare (xargs :guard t))
  (member-eq macro-arg '(&whole &optional &rest &body &key &allow-other-keys)))

;; Returns (mv args-before remaining-args)
(defund split-args-at-lambda-list-keyword (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (if (endp macro-args)
      (mv nil nil)
    (let ((macro-arg (first macro-args)))
      (if (lambda-list-keywordp macro-arg)
          (mv nil macro-args)
        (mv-let (args-before remaining-args)
          (split-args-at-lambda-list-keyword (rest macro-args))
          (mv (cons macro-arg args-before)
              remaining-args))))))

(defthm macro-arg-listp-of-mv-nth-0-of-split-args-at-lambda-list-keyword
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 0 (split-args-at-lambda-list-keyword macro-args))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-args-at-lambda-list-keyword))))

(defthm true-listp-of-mv-nth-1-of-split-args-at-lambda-list-keyword
  (implies (true-listp macro-args)
           (true-listp (mv-nth 1 (split-args-at-lambda-list-keyword macro-args))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-args-at-lambda-list-keyword))))

(defthm macro-arg-listp-of-mv-nth-1-of-split-args-at-lambda-list-keyword
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 1 (split-args-at-lambda-list-keyword macro-args))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-args-at-lambda-list-keyword))))

;; Returns (mv required-args optional-args keyword-args).
;; The expected input is (...remaining-args... &optional ...optional-args... &key ...keyword-args...)
(defun split-macro-args (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (mv-let (required-args remaining-args)
    (split-args-at-lambda-list-keyword macro-args)
    (if (not (symbol-listp required-args))
        (prog2$ (er hard? 'split-macro-args "Found a non-symbol required arg among: ~x0." required-args)
                (mv nil nil nil))
      (if (endp remaining-args)
          (mv required-args nil nil)
        (mv-let (optional-args remaining-args)
          (if (eq '&optional (first remaining-args))
              (split-args-at-lambda-list-keyword (rest remaining-args))
            (mv nil remaining-args))
          (if (endp remaining-args)
              (mv required-args optional-args nil)
            (if (eq '&key (first remaining-args))
                (mv required-args optional-args (rest remaining-args))
              (prog2$ (er hard? 'split-macro-args "Unexpected lambda-list-keyword: ~x0." (first remaining-args))
                      (mv nil nil nil)))))))))

(defthm symbol-listp-of-mv-nth-0-of-split-macro-args
  (implies (macro-arg-listp macro-args)
           (symbol-listp (mv-nth 0 (split-macro-args macro-args))))
  :hints (("Goal" :in-theory (enable split-macro-args))))

(defthm macro-arg-listp-of-mv-nth-1-of-split-macro-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 1 (split-macro-args macro-args))))
  :hints (("Goal" :in-theory (enable split-macro-args))))

(defthm macro-arg-listp-of-mv-nth-2-of-split-macro-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 2 (split-macro-args macro-args))))
  :hints (("Goal" :in-theory (enable split-macro-args))))

;; test: (SPLIT-MACRO-ARGS '(foo bar &key baz (baz2 'nil)))

(defun keyword-or-optional-arg-names (keyword-args ; symbols or doublets with default values
                          )
  (declare (xargs :guard (macro-arg-listp keyword-args)
                  :guard-hints (("Goal" :in-theory (enable macro-arg-listp MACRO-ARGP)))))
  (if (atom keyword-args)
      nil
    (let ((arg (first keyword-args)))
      (cons (if (symbolp arg) arg (car arg))
            (keyword-or-optional-arg-names (rest keyword-args))))))

;; Returns (mv required-args optional-args keyword-args).
;; TODO: Should we do something better with whole, rest, body, etc?
(defund extract-required-and-optional-and-keyword-args (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (let* ((macro-args (maybe-skip-whole-arg macro-args)) ;skips &whole
         (macro-args (remove-rest-and-body-from-macro-args macro-args)) ; gets rid of &rest and &body
         (macro-args (remove-allow-other-keys-from-macro-args macro-args)) ; gets rid of &allow-other-keys
         )
    (split-macro-args macro-args)))

(defthm symbol-listp-of-mv-nth-0-of-extract-required-and-optional-and-keyword-args
  (implies (macro-arg-listp macro-args)
           (symbol-listp (mv-nth 0 (extract-required-and-optional-and-keyword-args macro-args))))
  :hints (("Goal" :in-theory (enable extract-required-and-optional-and-keyword-args))))

(defthm macro-arg-listp-of-mv-nth-1-of-extract-required-and-optional-and-keyword-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 1 (extract-required-and-optional-and-keyword-args macro-args))))
  :hints (("Goal" :in-theory (enable extract-required-and-optional-and-keyword-args))))

(defthm macro-arg-listp-of-mv-nth-2-of-extract-required-and-optional-and-keyword-args
  (implies (macro-arg-listp macro-args)
           (macro-arg-listp (mv-nth 2 (extract-required-and-optional-and-keyword-args macro-args))))
  :hints (("Goal" :in-theory (enable extract-required-and-optional-and-keyword-args))))

;; gets rid of things like &key and &whole
;; todo: handle the rest of the & things
(defund macro-arg-names (macro-args)
  (declare (xargs :guard (macro-arg-listp macro-args)))
  (mv-let (required-args optional-args keyword-args)
    (extract-required-and-optional-and-keyword-args macro-args)
    (append required-args
            (keyword-or-optional-arg-names optional-args)
            (keyword-or-optional-arg-names keyword-args))))
