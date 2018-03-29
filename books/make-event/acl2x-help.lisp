; ACL2X Help
; Copyright (C) 2010-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>
;
; Based on a similar utility by Matt Kaufmann.

(in-package "ACL2")
(set-state-ok t)

;; Utility to allow different events in the first and second passes of two-pass
;; certifications.  Example usage is in acl2x-replace-test.lisp.

;; The idea is that pass 1 is a special case where there might be all kinds of
;; shenanigans going on, and we may want different behavior there than in pass
;; 2, or in non-acl2x certification, or in the top-level loop.

; (include-book "misc/hons-help" :dir :system)



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
    (defattach (acl2x-expansion-alist acl2x-expansion-alist-replacement)
      :system-ok t)
    (value-triple :invisible)))

(defmacro use-acl2x-replace! ()
  '(defattach (acl2x-expansion-alist acl2x-expansion-alist-replacement)
     :system-ok t))


(verify-termination hons-copy-with-state)
(verify-guards hons-copy-with-state)

(defmacro no-acl2x-replace ()
  '(defattach (acl2x-expansion-alist hons-copy-with-state)
     :system-ok t))

(defmacro no-acl2x-replace! ()
  '(defattach (acl2x-expansion-alist hons-copy-with-state)
     :system-ok t))

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

(local (defthm true-listp-of-revappend
         (implies (true-listp x)
                  (true-listp (revappend y x)))))
(local (defthm true-listp-of-first-n-ac
         (implies (true-listp x)
                  (true-listp (first-n-ac i l x)))))

(mutual-recursion

(defun acl2x-expansion-alist-replacement2 (form state)
  (declare (xargs :guard t
                  :stobjs state))
  (case-match form
    (('record-expansion & y)
     ;; Gets rid of record-expansion forms, replacing them by just their
     ;; expansions.  What difference does this make?
     (acl2x-expansion-alist-replacement2 y state))
    (('progn . x)
     (case-match x
       ((('value-triple ('quote (':acl2x-pass2 form)))
         &)
        ;; Special syntax produced by acl2x-replace.  Ignore the form that was
        ;; run in pass 1 (the "&" above) and recur on the pass2 form.
        (acl2x-expansion-alist-replacement2 form state))
       ((('value-triple ('quote (':acl2x-load-state-global symbol)))
         &)
        ;; Special syntax produced by acl2x-replace.  Ignore the form that was
        ;; run in pass 1 (the "&" above) and replace it with the form currently
        ;; stored in the given state global.  We don't recur on this because
        ;; then we might not terminate.
        (if (and (symbolp symbol)
                 (boundp-global symbol state))
            (f-get-global symbol state)
          (er hard? 'acl2x-expansion-alist-replacement2
              "Found an acl2x-load-state-global form with an unbound variable~%")))
       (& (with-guard1
           (true-listp x)
           (hons 'progn
                 (acl2x-expansion-alist-replacement2-lst x state))))))
    (('encapsulate sigs . x)
     (with-guard1
      (true-listp x)
      (hons 'encapsulate
            (hons sigs
                  (acl2x-expansion-alist-replacement2-lst x state)))))
    (('local x)
     (hons-copy (list 'local
                      (acl2x-expansion-alist-replacement2 x state))))
    (('skip-proofs x)
     (hons-copy (list 'skip-proofs
                      (acl2x-expansion-alist-replacement2 x state))))
    (('with-output . x)
     (with-guard1
      (true-listp x)
      (hons 'with-output
            (append (butlast x 1)
                    (list
                     (acl2x-expansion-alist-replacement2
                      (car (last x)) state))))))
    (& form)))

(defun acl2x-expansion-alist-replacement2-lst (x state)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (hons (acl2x-expansion-alist-replacement2 (car x) state)
                 (acl2x-expansion-alist-replacement2-lst (cdr x) state)))))

)

(defun acl2x-expansion-alist-replacement1 (alist acc state)
  (declare (xargs :guard (and (alistp alist)
                              (alistp acc))
                  :stobjs state))
  (cond ((endp alist)
         (hons-copy (reverse acc)))
        (t (acl2x-expansion-alist-replacement1
            (cdr alist)
            (acons (caar alist)
                   (acl2x-expansion-alist-replacement2 (cdar alist) state)
                   acc) state))))

(defun acl2x-expansion-alist-replacement (alist state)
  (declare (xargs :guard t :stobjs state)
           (ignorable state))
  (with-guard1 (alistp alist)
               (acl2x-expansion-alist-replacement1 alist nil state)))


(use-acl2x-replace!)

