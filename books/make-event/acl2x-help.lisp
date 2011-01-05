; acl2x-help.lisp

; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

; Author: Sol Swords (Centaur Technology), <sswords@centtech.com>
; Based on a similar utility by Matt Kaufmann.

(in-package "ACL2")

;; Utility to allow different events in the first and second passes of two-pass
;; certifications.  Example usage is in acl2x-replace-test.lisp.

;; The idea is that pass 1 is a special case where there might be all kinds of
;; shenanigans going on, and we may want different behavior there than in pass
;; 2, or in non-acl2x certification, or in the top-level loop.

(include-book "misc/hons-help" :dir :system)



;; (ACL2X-REPLACE PASS1 PASS2) runs the event PASS2 unless we are in the first
;; pass of a two-pass certification.  If we are in that first pass, it runs
;; PASS1, but leaves it in a specially-formed wrapper so that in
;; postprocessing, the recorded version in the produced .acl2x file will
;; actually be PASS2.

;; Note that a certain function must be attached to acl2x-expansion-alist in
;; order for this to work.  We perform this attachment in this book, but it may
;; be undone.  You may use (use-acl2x-replace) to ensure that this attachment
;; is in place locally, or (use-acl2x-replace!) to put it in place globally.
;; (no-acl2x-replace) removes this attachment.

;; We actually deal with four possibly-distinct events, respectively for:
;;  - pass 1 of two-pass certification
;;  - pass 2 of two-pass certification
;;  - single-pass certification
;;  - outside certification.
;; But by default (with no keyword arguments) we take pass2 to be the thing we
;; want to execute in all except the first case above.

(defun acl2x-replace-fn (pass1 pass2 single-pass outside-certification)
  `(make-event
    (cond ((not (f-get-global 'certify-book-info state))
           ',outside-certification)
          ((not (f-get-global 'write-acl2x state))
           ',single-pass)
          (t '(progn (value-triple '(:acl2x-pass2 ,pass2))
                     ,pass1)))))

(defmacro acl2x-replace (pass1 pass2
                               &key
                               (single-pass 'nil single-p)
                               (outside-certification 'nil outside-p))
  (acl2x-replace-fn pass1 pass2
                    (if single-p single-pass pass2)
                    (if outside-p outside-certification pass2)))


;; Use acl2x-replace to make this a no-op except on the first pass :-)
(defmacro use-acl2x-replace ()
  '(acl2x-replace
    (defattach acl2x-expansion-alist acl2x-expansion-alist-replacement)
    (value-triple :invisible)))

(defmacro use-acl2x-replace! ()
  '(defattach acl2x-expansion-alist acl2x-expansion-alist-replacement))

(defmacro no-acl2x-replace ()
  '(defattach acl2x-expansion-alist hons-copy))

(defmacro no-acl2x-replace! ()
  '(defattach acl2x-expansion-alist hons-copy))

;; Use of acl2x-replace that skips the proofs of form in the first pass, but
;; not the second.  
(defmacro maybe-skip-proofs (form)
  `(acl2x-replace (skip-proofs ,form)
                  ,form
                  :single-pass ,form
                  ;; Is this what we want?
                  :outside-certification (skip-proofs ,form)))



;; The rest of this file defines acl2x-expansion-alist-replacement, which is
;; what allows the special wrapper placed by acl2x-replace to be replaced by
;; the pass2 form.

(defmacro with-guard1 (guard form)

; Wart: This macro only works if form returns a single, non-stobj value (hence
; the "1" suffix in the name of this macro).

  `(cond (,guard ,form)
         (t (er hard? 'with-guard1
                "Unexpected with-guard1 failure, ~x0"
                ',guard))))

(mutual-recursion

(defun acl2x-expansion-alist-replacement2 (form)
  (declare (xargs :guard t))
  (case-match form
    (('record-expansion & y)
     ;; Gets rid of record-expansion forms, replacing them by just their
     ;; expansions.  What difference does this make?
     (acl2x-expansion-alist-replacement2 y))
    (('progn . x)
     (case-match x
       ((('value-triple ('quote (':acl2x-pass2 form)))
         &)
        ;; Special syntax produced by acl2x-replace.  Ignore the form that was
        ;; run in pass 1 (the "&" above) and recur on the pass2 form.
        (acl2x-expansion-alist-replacement2 form))
       (& (with-guard1
           (true-listp x)
           (hons 'progn
                 (acl2x-expansion-alist-replacement2-lst x))))))
    (('encapsulate sigs . x)
     (with-guard1
      (true-listp x)
      (hons 'encapsulate
            (hons sigs
                  (acl2x-expansion-alist-replacement2-lst x)))))
    (('local x)
     (hons-list 'local
                (acl2x-expansion-alist-replacement2 x)))
    (('skip-proofs x)
     (hons-list 'skip-proofs
                (acl2x-expansion-alist-replacement2 x)))
    (('with-output . x)
     (with-guard1
      (true-listp x)
      (hons 'with-output
            (hons-append (butlast x 1)
                         (hons-list
                          (acl2x-expansion-alist-replacement2
                           (car (last x))))))))
    (& form)))

(defun acl2x-expansion-alist-replacement2-lst (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (hons (acl2x-expansion-alist-replacement2 (car x))
                 (acl2x-expansion-alist-replacement2-lst (cdr x))))))

)

(defun acl2x-expansion-alist-replacement1 (alist acc)
  (declare (xargs :guard (and (alistp alist)
                              (alistp acc))))
  (cond ((endp alist)
         (hons-copy (reverse acc)))
        (t (acl2x-expansion-alist-replacement1
            (cdr alist)
            (acons (caar alist)
                   (acl2x-expansion-alist-replacement2 (cdar alist))
                   acc)))))

(defun acl2x-expansion-alist-replacement (alist)
  (declare (xargs :guard t))
  (with-guard1 (alistp alist)
               (acl2x-expansion-alist-replacement1 alist nil)))


(use-acl2x-replace!)
