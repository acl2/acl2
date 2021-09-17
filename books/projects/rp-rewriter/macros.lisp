; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "std/strings/decimal" :dir :system)
;(include-book "aux-functions")
;(local (include-book "proofs/useful-lemmas"))
(include-book "tools/flag" :dir :system)

(encapsulate
  nil

  (define strlist-to-str
    ((lst (string-listp lst)))
    (if (atom lst)
        ""
      (string-append (car lst)
                     (strlist-to-str (cdr lst)))))

  (define
    sym-app-fnc (args)
    (if (atom args)
        ""
      (string-append
       (string-append
        (b* ((e (car args)))
          (if (string-listp e)
              (strlist-to-str e)
            (if (symbolp e)
                (symbol-name (car args))
              (if (stringp e)
                  e
                (str::intstr (ifix e))))))
        (if (and (consp (cdr args))
                 (not (stringp (car args)))
                 (not (string-listp (car args))))
            "_"
          ""))
       (sym-app-fnc (cdr args)))))

  (defmacro sa (&rest args)
    `(intern$
      (sym-app-fnc (list ,@args))
      "RP"))

  (define sa-lst (lst e)
    :guard t
    (if (atom lst)
        nil
      (cons (sa (car lst) e)
            (sa-lst (cdr lst) e))))

  (define get-digit-count
    ((n (natp n)))
    :prepwork
    ((local
      (include-book "arithmetic-5/top" :dir :system)))
    (if (zp n)
        0
      (+ 1
         (get-digit-count (floor (nfix n) 10)))))

  (defun sas-fnc (s start-idx count)
    (declare (xargs :guard (and (symbolp s)
                                (natp start-idx)
                                (natp count))))
    (if (zp count)
        nil
      (cons (sa s start-idx)
            (sas-fnc s (1+ start-idx)
                     (1- count)))))

  (defun sas-fnc-zp (s start-idx count max)
    (declare (xargs :guard (and (symbolp s)
                                (natp start-idx)
                                (natp count)
                                (natp max))))
    (if (zp count)
        nil
      (cons (b* ((zeros
                  (- (get-digit-count max)
                     (get-digit-count start-idx)))
                 (zeros (nfix (if (equal start-idx 0) (1- zeros) zeros))))
              (sa s (repeat zeros "0") start-idx))
            (sas-fnc-zp s
                        (1+ start-idx)
                        (1- count)
                        max))))

  (defmacro sas (s start-idx count &optional zero-pad)
    (if zero-pad
        `(sas-fnc-zp ,s ,start-idx ,count ,count)
      `(sas-fnc ,s ,start-idx ,count)))

  (defun sas2 (sym start count)
    (declare (ignorable start))
    (if (zp count)
        nil
      (cons (sa (symbol-name sym) "-" start)
            (sas2 sym (1+ start) (1- count))))))

(encapsulate
  nil
  (defun create-ex-cp-fnc-aux (cnt)
    (if (zp cnt)
        nil
      (append (create-ex-cp-fnc-aux (1- cnt))
              (list `(unquote (nth ,cnt term))))))

  (defun create-ex-cp-fnc (fns)
    (if (atom fns)
        nil
      (cons
       (list (caar fns) `(list 'quote (,(caar fns) ,@(create-ex-cp-fnc-aux (cdar fns)))))
       (create-ex-cp-fnc (cdr fns)))))

  (defmacro create-ex-counterpart-cases (fns)
    `(let ((fn-name (car term)))
       (case fn-name
         ,@(append
            (create-ex-cp-fnc fns)
            '((t term)))))))

;;(rp-ex-cp-fnc '(binary-* '3 '3))
;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;

(mutual-recursion

 (defun clear-rp-wrappers (term)

   (if (atom term)
       term
     (if (quotep term)
         term
       (case-match term
         (('rp & x)
          (clear-rp-wrappers x))
         (& (cons (car term)
                  (clear-rp-wrappers-subterms (cdr term))))))))

 (defun clear-rp-wrappers-subterms (subterms)

   (if (atom subterms)
       nil
     (cons (clear-rp-wrappers (car subterms))
           (clear-rp-wrappers-subterms (cdr subterms))))))

;;;

(encapsulate
  nil

  (mutual-recursion
   (defun get-vars-aux (q acc)
     (declare (xargs :guard (and (true-listp acc)
                                 (pseudo-termp q))
                     :verify-guards nil))
     (if (quotep q)
         acc
       (if (atom q)
           (if (member q acc) acc (cons q acc))
         (get-vars-aux-subterms (cdr q) acc))))

   (defun get-vars-aux-subterms (subterms acc)
     (declare (xargs :guard (and (true-listp acc)
                                 (pseudo-term-listp subterms))
                     :verify-guards nil))
     (if (atom subterms)
         acc
       (get-vars-aux-subterms (cdr subterms)
                              (get-vars-aux (car subterms) acc)))))

  (make-flag get-vars-aux :defthm-macro-name defthm-get-vars-aux)

  (defthm-get-vars-aux
    (defthm true-listp-get-vars-aux
      (implies (true-listp acc)
               (true-listp (get-vars-aux q acc)))
      :flag get-vars-aux)
    (defthm true-listp-get-vars-aux-subterms
      (implies (true-listp acc)
               (true-listp (get-vars-aux-subterms subterms acc)))
      :flag get-vars-aux-subterms))

  (verify-guards get-vars-aux)

  (defun get-all-vars (term)
    (declare (xargs :guard (pseudo-termp term)))
    (get-vars-aux term nil))

  (defun clear-irrelevant-hyp (p vars)
    ;; p is a list of terms
    ;; get the variables if each element in p
    ;; if it is not a subset of vars
    ;; then discard it
    (if (atom p)
        nil
      (let* ((pcar (car p))
             (pvars (get-vars-aux pcar nil)))
        (if (subsetp pvars vars)
            (cons pcar
                  (clear-irrelevant-hyp (cdr p) vars))
          (clear-irrelevant-hyp (cdr p) vars)))))

  #|(mutual-recursion

   (defun rp-defthm-get-props (term)
     (if (atom term)
         nil
       (case-match term
         (('rp type x)
          (cons (clear-rp-wrappers (list (unquote type) x))
                (rp-defthm-get-props x)))
         (& (rp-defthm-get-props-subterms (cdr term))))))

   (defun rp-defthm-get-props-subterms (subterms)
     (if (atom subterms)
         nil
       (let ((cur (rp-defthm-get-props (car subterms))))
         (if cur
             (append cur
                     (rp-defthm-get-props-subterms (cdr subterms)))
           (rp-defthm-get-props-subterms (cdr subterms)))))))||#

  #|(defun rp-defthm-fnc (term)
    (if (atom term)
        term
      (case-match term
        (('implies ('and . p) q)
         (b* ((props (rp-defthm-get-props q))
              ((when (not props)) nil)
              (newp (clear-irrelevant-hyp p (get-vars-aux-subterms props nil))))
           (if newp
               `(implies
                 (and . ,newp)
                 ,(cons 'and props))
             (cons 'and props))))
        (('implies p q)
         (b* ((props (rp-defthm-get-props q))
               ((when (not props)) nil)
               (newp (clear-irrelevant-hyp (list p) (get-vars-aux-subterms props nil))))
           (if newp
               `(implies
                 ,(car newp)
                 ,(cons 'and props))
             (cons 'and props))))
        (& (cons 'and (rp-defthm-get-props term))))))||#

  #|(defmacro defthm-rp2 (name &rest args)
    ;;; NOT USED ANYMORE!!!!
    "Submits the given theorem with another defthm for side conditions"
    `(progn
       (defthm
         ,(sa (symbol-name name) '-rp-side-cond)
         ,(rp-defthm-fnc (car args))
         . ,(cdr args))
       (defthm ,name . ,args)))||#)



(encapsulate
  nil

  (defun fetch-new-theory-step1 (event)
    `(make-event
      (b* ((?current-theory (let ((world (w state))) (current-theory :here))))
        `(progn ,',event

                (table fetch-new-theory 'a ',current-theory)))))

  (defun fetch-new-theory-step2 (macro-name)
    `(make-event
      (b* ((new-current-theory (let ((world (w state))) (current-theory :here)))
           (old-current-theory (cdr (assoc-equal 'a (table-alist
                                                     'fetch-new-theory
                                                     (w state)))))
           (- (cw "Scanning for newly added event ..."))
           (added-theory (set-difference$ new-current-theory
                                          old-current-theory
                                          :test 'equal))
           (- (cw "Scanning for disabled theory ..."))
           (removed-theory (set-difference$ old-current-theory
                                            new-current-theory
                                            :test 'equal)))
        (if (and (not removed-theory)
                 (not added-theory))
            `(value-triple (cw "~%Event did not change current theory, not ~
    creating macro ~p0. ~%" ',',macro-name))
          `(defmacro ,',macro-name (use)
             (if use
                 `(in-theory (e/d ,',added-theory
                                  ,',removed-theory))
               `(in-theory (e/d ,',removed-theory
                                ,',added-theory))))))))

  (defmacro fetch-new-theory (event macro-name &key (disabled 'nil) )
    `(with-output
       :off (warning event  prove  observation)
       :gag-mode :goals
       (progn
         ,(fetch-new-theory-step1 event)
         ,(fetch-new-theory-step2 macro-name)
         ,@(if disabled
               `((,macro-name nil))
             nil)))))


(defmacro fetch-new-events (&rest rst)
  `(fetch-new-theory ,@rst))

(xdoc::defxdoc
 fetch-new-theory
 :short "A macro that detects the changes in the theory when a book is
 included, and creates a macro to enable users to enable and disable the new theory."
 :parents (rp-utilities)
 :long "<p>Gives users the ability to undo and redo the changes an event, such
 as include-book, makes to current theory.

<code>
@('
 (fetch-new-theory
  <event>               ;; e.g., (include-book \"arithmetic-5\" :dir :system)
  <macro-name>          ;; e.g., use-aritmetic-5
  ;;optional key
  :disabled <disabled> ;; When non-nil, the event does not change the current
  theory. Default: nil.
  )
')
</code>
</p>

<p>
After including the arithmetic library as given below, users can enable and
disable the library as given.

<code>
@('
 (fetch-new-theory
  (include-book \"arithmetic-5\" :dir :system)
  use-aritmetic-5)
')
</code>

<code>
(use-aritmetic-5 t)
</code>

<code>
(use-aritmetic-5 nil)
</code>

</p>

<p>
Note that when current theory contains many items, this utility may work very
slowly. If you do not wish to generate a macro, you may also use @(see
rp::preserve-current-theory). This utility will work with current theory of any size.
</p>
"
 )



(encapsulate
  nil

  (defun preserve-current-theory-step1 (event)
    `(make-event
      (b* ((?current-theory (let ((world (w state))) (current-theory :here))))
        `(progn ,',event
                (table preserve-current-theory 'a ',current-theory)))))

  (defun preserve-current-theory-step2 ()
    `(make-event
      (b* ((old-current-theory (cdr (assoc-equal 'a (table-alist
                                                     'preserve-current-theory
                                                     (w state))))))
        `(in-theory ',old-current-theory))))

  (defmacro preserve-current-theory (event)
    `(with-output
       :off (warning event  prove  observation)
       :gag-mode :goals
       (progn
         ,(preserve-current-theory-step1 event)
         ,(preserve-current-theory-step2)))))

(xdoc::defxdoc
 preserve-current-theory
 :short "A macro that detects the changes in the theory when a book is
 included, and retains the current theory"
 :parents (rp-utilities)
 :long "See @(see rp::fetch-new-events)"
 )
