; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "remove-runes-entry")
(include-book "book-runes-alist")

(program)
(set-state-ok t)

(defun book-of-rune (rune wrld)

; Returns nil if the given rune is a fake rune or is from the book under
; certification.  Otherwise, returns the book in which rune was introduced.

  (let ((name (base-symbol rune)))
    (cond
     ((null name) ; fake rune, presumably
      nil)
     (t
      (let ((ev-wrld (decode-logical-name name wrld)))
        (cond
         ((null ev-wrld) ; odd error
          nil)
         (t (car (global-val 'include-book-path ev-wrld)))))))))

(defun partition-runes-by-book (runes wrld alist)

; Returns an alist with entries (book . runes-in-book).

  (cond
   ((consp runes)
    (let* ((rune (car runes))
           (book (book-of-rune rune wrld))
           (alist (if book
                      (put-assoc-equal
                       book
                       (cons rune (cdr (assoc-equal book alist)))
                       alist)
                    alist)))
      (partition-runes-by-book (cdr runes) wrld alist)))
   (t alist)))

(defun remove-book-runes-checkpoints-1 (alist term pspv hints time-limit ens
                                              wrld ctx state)
  (cond
   ((endp alist) (value nil))
   (t
    (let* ((pair (car alist))
           (book (car pair))
           (augmented-runes (cdr pair)))
      (er-let* ((entry (remove-runes-entry augmented-runes term pspv hints
                                           time-limit book ens wrld ctx
                                           state))
                (val (remove-book-runes-checkpoints-1
                      (cdr alist) term pspv hints time-limit ens wrld ctx
                      state)))
        (value (cons entry val)))))))

(defun intersectp-equal-strip-cdrs (lst pairs)
  (cond ((endp lst) nil)
        ((rassoc-equal (car lst) pairs) t)
        (t (intersectp-equal-strip-cdrs (cdr lst) pairs))))

(defun restrict-book-runes-alist-to-runes (alist runes)
  (cond ((endp alist) nil)
        ((intersectp-equal-strip-cdrs runes (cdar alist))
         (cons (car alist)
               (restrict-book-runes-alist-to-runes (cdr alist) runes)))
        (t (restrict-book-runes-alist-to-runes (cdr alist) runes))))

(defun remove-book-runes-checkpoints (term pspv runes hints time-limit ens wrld
                                           ctx state)
  (cond
   ((or (null time-limit)
        (ld-skip-proofsp state))
    (value nil))
   (t
    (let ((alist (restrict-book-runes-alist-to-runes (book-runes-alist wrld)
                                                     runes)))
      (cond
       ((null alist) (value nil)) ; fail
       (t
        (mv-let
          (erp val state)
          (with-output!
            :off :all
            :gag-mode nil
            (state-global-let*
             ((abort-soft nil)) ; interrupts abort immediately to the top level
             (remove-book-runes-checkpoints-1
              alist term pspv hints time-limit ens wrld ctx state)))
          (value (and (null erp) val)))))))))
