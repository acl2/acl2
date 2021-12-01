; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "lock")
(include-book "io")
(local (include-book "std/typed-lists/rational-listp" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(define sidekick-eventdata-push (data)
  (declare (ignorable data))
  (er hard? 'sidekick-eventdata-push "raw lisp definition not installed?"))

(define float.2 ((x rationalp))
  ;; Convert rational to float, two digits of precision
  (let* ((sign     (if (< x 0) "-" ""))
         (x        (abs x))
         (ipart    (truncate x 1))
         (fpart    (- x ipart))
         (100fpart (* fpart 100))
         (chop     (truncate 100fpart 1)))
    (cat sign
         (nat-to-dec-string ipart)
         "."
         (if (< chop 10)
             (cat "0" (nat-to-dec-string chop))
           (nat-to-dec-string chop)))))

;; (local (defthm acl2-numberp-when-rationalp
;;          (implies (rationalp x)
;;                   (acl2-numberp x))))

(defun sidekick-finalize-event-user (ctx body state)
  (declare (xargs :stobjs state))
  (b* ((evdata (and (acl2::f-boundp-global 'acl2::last-event-data state)
                    (acl2::f-get-global 'acl2::last-event-data state)))
       ((unless evdata)
        ;; Uh, okay, nothing to do, I guess.
        state)
       ((unless (alistp evdata))
        (er hard? 'sidekick-finalize-event-user
            "Expected an alist, got ~x0." evdata)
        state)
       (times (cdr (assoc 'acl2::time evdata)))
       ((unless (and (rational-listp times)
                     (equal (len times) 4)))
        (er hard? 'sidekick-finalize-event-user
            "Expected four rational-valued times.  Found ~x0.  X is ~x1" times evdata)
        state)
       ;; Allegedly the format is: (prove print proof-tree other)
       (prove-time-f      (float.2 (first times)))
       (print-time-f      (float.2 (second times)))
       (proof-tree-time-f (float.2 (third times)))
       (other-time-f      (float.2 (fourth times)))
       (total-time        (+ (the rational (first times))
                             (the rational (second times))
                             (the rational (third times))
                             (the rational (fourth times))))
       (total-time-f      (float.2 total-time))
       (alist (list* (cons :ctx               ctx)
                     (cons :body              body)
                     (cons :total-time        total-time)
                     (cons :total-time-f      total-time-f)
                     (cons :prove-time-f      prove-time-f)
                     (cons :print-time-f      print-time-f)
                     (cons :proof-tree-time-f proof-tree-time-f)
                     (cons :other-time-f      other-time-f)
                     evdata)))
    (with-sidekick-lock
      (sidekick-eventdata-push alist))
    state))

(define sidekick-get-all-event-data ()
  ;; BOZO completely unsound
  (er hard? 'sidekick-get-all-event-data "raw lisp definition not installed?"))

(defttag :sidekick)
; (depends-on "eventdata-raw.lsp")
(include-raw "eventdata-raw.lsp")

(defattach (acl2::finalize-event-user sidekick-finalize-event-user)
  :system-ok t)

(define eventdata->namex ((x alistp))
  (let ((look (assoc 'acl2::namex x)))
    (and look
         (cdr look))))

(define eventdata->total-time ((x alistp))
  (let ((times (cdr (assoc 'acl2::time x))))
    (if (and (equal (len times) 4)
             (rational-listp times))
        ;; Allegedly the format is: (prove print proof-tree other)
        (+ (first times)
           (second times)
           (third times)
           (fourth times))
      nil)))

(define find-eventdata (name all-event-data)
  :verify-guards nil
  (b* (((when (atom all-event-data))
        nil)
       (namex1 (eventdata->namex (car all-event-data)))
       ((when (and namex1
                   (or (eq namex1 name)
                       (and (symbol-listp namex1)
                            (member name namex1)))))
        (car all-event-data)))
    (find-eventdata name (cdr all-event-data))))

(define sk-get-eventdata ((name stringp) state)
  :returns (mv json-eventdata state)
  :mode :program
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in eventdata: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in eventdata: not a symbol: ~a~%" name)
            state))
       (data (find-eventdata (car objs) (sidekick-get-all-event-data)))
       (ans  (bridge::json-encode (list (cons :error nil)
                                   (cons :val data)))))
    (mv ans state)))

#||

(defun f (x) x)

(find-eventdata 'f (sidekick-get-all-event-data))))

(chop-to-hundreths
 (eventdata->total-time
(find-eventdata 'vl::vl-exprlist->finalwidths (sidekick-get-all-event-data))))

||#

;; Good deal.  So, what remains --
;;
;;  - figure out how to grab all events from a command block
;;  - simple sum up their total times, etc.
;;  - implement top-level command-block-time command.
