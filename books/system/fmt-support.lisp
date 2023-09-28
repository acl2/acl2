; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore, July-August 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Re-enable functions that were disabled in the boot-strap after this book was
; developed.
#-acl2-devel
(local (in-theory (enable error-fms
                          error-fms-channel
                          error1
                          error1-state-p
                          fms
                          fmt
                          fmt-abbrev1
                          fmt-ppr
                          fmt0
                          fmt1
                          fmt1!
                          ppr
                          ppr1
                          ppr2)))

(make-event
 (er-progn (set-gag-mode-evisc-tuple t state)
           (value '(value-triple nil))))

(defthm natp-+f!-fn2
  (implies (force (and (natp i) (natp j)))
           (natp (+f!-fn2 i j)))
  :rule-classes :type-prescription)

(defthm natp-+f!-fn3
  (implies (force (and (natp i) (natp j) (natp k)))
           (natp (+f!-fn3 i j k)))
  :rule-classes :type-prescription)

(defthm +f!-fn2-bound-1
  (<= (+f!-fn2 i j)
      (fixnum-bound))
  :rule-classes :linear)

(defthm +f!-fn2-bound-2
  (<= (+f!-fn2 i j)
      (+ i j))
  :rule-classes :linear)

(defthm +f!-fn2-elim
  (implies (<= b (fixnum-bound))
           (equal (< (+f!-fn2 i j) b)
                  (< (+ i j) b))))

(defthm +f!-fn3-bound-1
  (<= (+f!-fn3 i j k)
      (fixnum-bound))
  :rule-classes :linear)

(defthm +f!-fn3-bound-2
  (<= (+f!-fn3 i j k)
      (+ i j k))
  :rule-classes :linear)

(defthm +f!-fn3-elim
  (implies (<= b (fixnum-bound))
           (equal (< (+f!-fn3 i j k) b)
                  (< (+ i j k) b))))

(in-theory (disable +f!-fn2 +f!-fn3))

; Several events that follow were originally in books/system/fmx-cw.lisp.

(verify-termination fmt-char) ; and guards
(verify-termination fmt-var) ; and guards

; Start termination and guards for find-alternative-skip.

(verify-termination find-alternative-skip
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-skip-increases-1
  (implies (not (equal 0 (find-alternative-skip s i maximum quiet)))
           (< i (find-alternative-skip s i maximum quiet)))
  :rule-classes (:linear :rewrite))

(defthm find-alternative-skip-bound
  (implies (natp maximum)
           (<= (find-alternative-skip s i maximum quiet)
               maximum))
  :rule-classes (:linear :rewrite))

(defthm natp-find-alternative-skip
  (implies (force (natp maximum))
           (natp (find-alternative-skip s i maximum quiet)))
  :rule-classes :type-prescription)

(local (in-theory (disable nth)))

(verify-guards find-alternative-skip)

; Start termination and guards for find-alternative-start1, based on events
; above for find-alternative-skip, and then find-alternative-start.

(verify-termination zero-one-or-more) ; and guards

(verify-termination find-alternative-start1
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-start1-increases-1
  (let ((index (find-alternative-start1 x s i maximum quiet)))
    (implies (not (equal 0 index))
             (<= i index)))
  :rule-classes (:linear :rewrite))

(defthm find-alternative-start1-bound
  (implies (and (natp i)
                (<= i maximum))
           (<= (find-alternative-start1 x s i maximum quiet)
               maximum))
  :rule-classes (:linear :rewrite))

(defthm natp-find-alternative-start1
  (implies (and (force (natp i))
                (force (natp maximum)))
           (natp (find-alternative-start1 x s i maximum quiet)))
  :rule-classes :type-prescription)

(defthm find-alternative-skip-bound-alt
  (implies (and (natp maximum)
                (not (equal (find-alternative-skip s i maximum quiet)
                            0)))
           (<= (find-alternative-skip s i maximum quiet)
               maximum))
  :rule-classes (:linear :rewrite))

(verify-guards find-alternative-start1)

(verify-termination find-alternative-start) ; and guards

; Start termination and guards for find-alternative-stop, based on events above
; for find-alternative-skip.

(verify-termination find-alternative-stop
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-stop-increases-1
  (implies (not (equal 0 (find-alternative-stop s i maximum quiet)))
           (<= i (find-alternative-stop s i maximum quiet)))
  :rule-classes (:linear :rewrite))

(defthm find-alternative-stop-bound
  (implies (and (integerp i) (natp maximum))
           (<= (find-alternative-stop s i maximum quiet)
               maximum))
  :rule-classes (:linear :rewrite))

(defthm natp-find-alternative-stop
  (implies (force (natp i))
           (natp (find-alternative-stop s i maximum quiet)))
  :rule-classes :type-prescription)

(defthm find-alternative-stop-bound-2
  (implies (<= maximum (fixnum-bound))
           (<= (find-alternative-stop s i maximum quiet)
               (fixnum-bound)))
  :rule-classes (:linear :rewrite))

(verify-guards find-alternative-stop)

(in-theory (enable all-boundp-initial-global-table))

(include-book "eviscerate-top")

(defthm fmt-state-p-guard-helper
  (implies (eviscerate-top-state-p state)
           (array1p 'iprint-ar (f-get-global 'iprint-ar state)))
  :rule-classes nil)

(in-theory (disable (:d eviscerate-top-state-p)
                    (:t eviscerate-top-state-p)
                    (:e eviscerate-top-state-p)))

(verify-termination symbol-to-fixnat-alistp) ; and guards

(defthm symbol-to-fixnat-alistp-forward-to-alistp
  (implies (symbol-to-fixnat-alistp x)
           (alistp x))
  :rule-classes :forward-chaining)

(verify-termination fmt-state-p ; and guards
  (declare (xargs :guard-hints (("Goal" :use fmt-state-p-guard-helper)))))

(in-theory (disable princ$))

(encapsulate
  ()
  (local (include-book "kestrel/file-io-light/princ-dollar" :dir :system))

; Redundant with the include-book above:
  (defthm state-p1-of-princ$-gen
    (implies (and (state-p1 state)
                  (open-output-channel-p1 channel :character state))
             (state-p1 (princ$ x channel state)))))

(defthm assoc-equal-nth-2-princ$
  (equal (assoc-equal sym (nth 2 (princ$ x channel state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable princ$))))

(defthm princ$-preserves-eviscerate-top-state-p
  (implies (and (eviscerate-top-state-p state)
                (open-output-channel-p1 channel :character state))
           (eviscerate-top-state-p (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable eviscerate-top-state-p))))

(defthm princ$-preserves-fmt-state-p
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (princ$ x channel state))))

(defthm fmt-state-p-forward
  (implies (fmt-state-p state)
           (and (state-p1 state)
                (natp (cdr (assoc-equal 'fmt-hard-right-margin
                                        (nth 2 state))))
                (<= (cdr (assoc-equal 'fmt-hard-right-margin
                                      (nth 2 state)))
                    *small-hi*)
                (natp (cdr (assoc-equal 'fmt-soft-right-margin
                                        (nth 2 state))))
                (<= (cdr (assoc-equal 'fmt-soft-right-margin
                                      (nth 2 state)))
                    *small-hi*)
                (print-base-p (cdr (assoc-equal 'print-base (nth 2 state))))
                (natp (cdr (assoc-equal 'print-base (nth 2 state))))
                (<= (cdr (assoc-equal 'print-base (nth 2 state)))
                    16)
                (alistp (table-alist 'evisc-table
                                     (cdr (assoc-equal 'current-acl2-world
                                                       (nth 2 state)))))
                (eviscerate-top-state-p state)
; See comment in fmt-state-p.  But probably this conjunct won't be useful in
; forward-chaining (unless array-order, header, and get-global are disabled).
                (equal (array-order (header 'iprint-ar
                                            (f-get-global 'iprint-ar state)))
                       nil)
; Additions for ppr1 and ppr1-lst:
                (natp (cdr (assoc-equal 'ppr-flat-right-margin
                                        (nth 2 state))))
                (<= (cdr (assoc-equal 'ppr-flat-right-margin
                                      (nth 2 state)))
                    *small-hi*)
                (symbol-to-fixnat-alistp
                 (table-alist 'ppr-special-syms
                              (cdr (assoc-equal 'current-acl2-world
                                                (nth 2 state)))))
                (not (assoc-eq
                      'quote
                      (table-alist 'ppr-special-syms
                                   (cdr (assoc-equal 'current-acl2-world
                                                     (nth 2 state))))))))
  :rule-classes :forward-chaining)

(defthm natp-fmt-hard-right-margin
  (implies (fmt-state-p state) ; prevent fmt-state-p-princ$ failure
           (natp (cdr (assoc-equal 'fmt-hard-right-margin
                                   (nth 2 state)))))
  :rule-classes :type-prescription)

(defthm natp-fmt-soft-right-margin
  (implies (fmt-state-p state) ; prevent fmt-state-p-princ$ failure
           (natp (cdr (assoc-equal 'fmt-soft-right-margin
                                   (nth 2 state)))))
  :rule-classes :type-prescription)

(in-theory (disable fmt-state-p))

(verify-termination punctp (declare (xargs :guard t)))

(verify-termination fmt-soft-right-margin) ; and guards
(verify-termination fmt-hard-right-margin) ; and guards

(local (include-book "arithmetic/top-with-meta" :dir :system))

(verify-termination scan-past-whitespace
  (declare (xargs :verify-guards nil)))

(defthm scan-past-whitespace-lower-bound
  (implies (<= i maximum)
           (<= i (scan-past-whitespace s i maximum) ))
  :rule-classes (:linear :rewrite))

(defthm scan-past-whitespace-upper-bound
  (<= (scan-past-whitespace s i maximum)
      maximum)
  :rule-classes (:linear :rewrite))

(defthm natp-scan-past-whitespace
  (implies (and (force (natp i))
                (force (natp maximum)))
           (natp (scan-past-whitespace s i maximum)))
  :rule-classes :type-prescription)

(verify-guards scan-past-whitespace)

(defthm open-output-channel-p1-princ$
  (implies (open-output-channel-p1 chan1 typ state)
           (open-output-channel-p1 chan1 typ
                                   (princ$ x chan2 state)))
  :hints (("Goal" :in-theory (enable princ$))))

(include-book "tools/rulesets" :dir :system)

(def-ruleset open-output-channel-diff nil)

(defun defthm-od-defthmd (fn hints mv-nth)
  (declare (xargs :guard (symbolp fn)))
  (let* ((old (packn (list 'open-output-channel-p1- fn)))
         (new (packn (list old '-diff)))
         (call (cons fn 'defthm-od-formals))
         (call (if mv-nth
                   `(mv-nth ,mv-nth ,call)
                 call)))
    `(defthmd ,new
       (implies
        (not (equal chan1 channel))
        (equal (open-output-channel-p1 chan1 typ ,call)
               (open-output-channel-p1 chan1 typ state)))
       ,@(and hints `(:hints ,hints)))))

(defun defthm-od-1 (fn form wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (let ((formals (formals fn wrld)))
    (assert$?
     (and (true-listp formals)
          (member-eq 'channel formals)) ; else change (equal chan1 channel)
     (sublis (acons 'defthm-od-formals
                    (sublis '((state-state . state))
                            formals)
                    nil)
             form))))

(defmacro defthm-od (fn &key hints mv-nth)
; (defthm open-output-channel-p1-xxx-diff ...) etc.
  (let* ((defthmd-form (defthm-od-defthmd fn hints mv-nth))
         (new-name (cadr defthmd-form)))
    `(make-event
      (let ((defthmd-form-fixed (defthm-od-1 ',fn ',defthmd-form (w state)))
            (new-rules '(,new-name)))
        `(encapsulate
           ()
           (local (in-theory (enable* open-output-channel-diff)))
           ,defthmd-form-fixed
           (add-to-ruleset open-output-channel-diff ',new-rules))))))

(defun defthm-od-defthmd-lst (fn-lst mv-nth)
  (declare (xargs :guard (symbol-listp fn-lst)))
  (cond ((endp fn-lst) nil)
        (t (cons (let* ((fn (car fn-lst))
                        (form (defthm-od-defthmd fn nil mv-nth)))
                   (append form
                           (list :flag fn)))
                 (defthm-od-defthmd-lst (cdr fn-lst) mv-nth)))))

(defun defthm-flag-od-1 (fn-lst defthmd-form-lst wrld)
  (declare (xargs :guard (and (symbol-listp fn-lst)
                              (true-listp defthmd-form-lst)
                              (plist-worldp wrld))))
  (cond ((endp fn-lst)  nil)
        (t (cons (defthm-od-1 (car fn-lst) (car defthmd-form-lst) wrld)
                 (defthm-flag-od-1 (cdr fn-lst) (cdr defthmd-form-lst) wrld)))))

(defmacro defthm-flag-od (fn-lst &key hints mv-nth)

; Flag version of defthm-od.

  (declare (xargs :guard (and (symbol-listp fn-lst)
                              (consp fn-lst))))
  (let* ((defthmd-form-lst (defthm-od-defthmd-lst fn-lst mv-nth))
         (new-name-lst (strip-cadrs defthmd-form-lst)))
    `(make-event
      (let ((defthmd-form-lst-fixed
              (defthm-flag-od-1 ',fn-lst ',defthmd-form-lst (w state)))
            (defthm-flag-symbol
              (packn (list 'defthm-flag- ',(car fn-lst))))
            (new-rules ',new-name-lst)
            (hints-postfix ',(and hints
                                  `(:hints ,hints))))
        `(encapsulate
           ()
           (local (in-theory (enable* open-output-channel-diff)))
           (,defthm-flag-symbol
             ,@defthmd-form-lst-fixed
             ,@hints-postfix)
           (add-to-ruleset open-output-channel-diff ',new-rules))))))

(defthm-od princ$
  :hints (("Goal" :in-theory (enable princ$))))

(in-theory (disable open-output-channel-p1))

(verify-termination write-for-read) ; and guards

(verify-termination newline) ; and guards

(verify-termination fmt-tilde-s1
  (declare (xargs :verify-guards nil)))

(defthm car-fmt-tilde-s1-bound
  (implies (fixnat-guard col)
           (<= (car (fmt-tilde-s1 s i maximum col channel state))
               (fixnum-bound)))
  :hints (("Goal"
           :expand ((:free (col)
                           (fmt-tilde-s1 s i (+ 1 i) col channel state)))))
  :rule-classes (:rewrite :linear))

(defthm natp-car-fmt-tilde-s1
  (natp (car (fmt-tilde-s1 s i maximum col channel state)))
  :hints (("Goal"
           :expand ((:free (col)
                           (fmt-tilde-s1 s i (+ 1 i) col channel state)))))
  :rule-classes :type-prescription)

(verify-guards fmt-tilde-s1)

(verify-termination fmt-tilde-cap-s1
  (declare (xargs :verify-guards nil)))

(defthm car-fmt-tilde-cap-s1-bound
  (<= (car (fmt-tilde-cap-s1 s i maximum col channel state))
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(defthm natp-fmt-tilde-cap-s1-bound
  (natp (car (fmt-tilde-cap-s1 s i maximum col channel state)))
  :hints (("Goal" :expand ((fmt-tilde-cap-s1 s i (+ 1 i) col channel state))))
  :rule-classes :type-prescription)

(verify-guards fmt-tilde-cap-s1)

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (in-theory (disable functional-commutativity-of-minus-*-left)))
  (verify-termination flsz-integer
    (declare (xargs :verify-guards nil))))

(defthm flsz-integer-upper-bound
  (<= (flsz-integer x print-base acc)
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(verify-guards flsz-integer)

(in-theory (disable needs-slashes)) ; for efficiency

(verify-termination flsz-atom) ; and guards

(verify-termination spaces1 ; and guards
  (declare (xargs :guard-hints ; for efficiency:
                  (("Goal" :in-theory (disable aref1))))))
(verify-termination spaces) ; and guards

(defthm open-output-channel-p1-spaces1
  (implies (open-output-channel-p1 chan1 type state)
           (open-output-channel-p1 chan1 type
                                   (spaces1 n col hard-right-margin chan2
                                            state))))

(defthm-od spaces1)

(in-theory (disable aref1)) ; for speed

(defthm open-output-channel-p1-spaces
  (implies (open-output-channel-p1 chan1 type state)
           (open-output-channel-p1 chan1 type (spaces n col chan2 state))))

(defthm-od spaces)

(in-theory (disable spaces))

(defthm flsz-atom-bound
  (<= (flsz-atom x print-base print-radix acc state)
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(defthm natp-flsz-atom
  (natp (flsz-atom x print-base print-radix acc state))
  :rule-classes :type-prescription)

(in-theory (disable aref1)) ; for efficiency

(verify-termination splat-atom) ; and guards

(verify-termination splat-atom!)

(defthm state-p1-spaces1
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :character state))
           (state-p1 (spaces1 n col hard-right-margin channel state))))

(defthm state-p1-spaces
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :character state))
           (state-p1 (spaces n col channel state)))
  :hints (("Goal" :in-theory (enable spaces))))

(verify-termination splat-string)

(verify-termination splat
  (declare (xargs :verify-guards nil)))

(defthm car-splat-string-bound
  (<= (car (splat-string x indent col channel state))
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(defthm natp-car-splat-string
  (implies (and (force (natp col))
                (force (natp indent)))
           (natp (car (splat-string x indent col channel state))))
  :rule-classes :type-prescription)

(in-theory (disable splat-string symbol-in-current-package-p flsz-atom))

(defthm car-splat-atom-bound
  (<= (car (splat-atom x print-base print-radix indent col channel state))
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(defthm natp-car-splat-atom
  (implies (and (force (natp col))
                (force (natp indent)))
           (natp (car (splat-atom x print-base print-radix indent col channel
                                  state))))
  :rule-classes :type-prescription)

(in-theory (disable splat-atom))

(include-book "tools/flag" :dir :system)

(make-flag flag-splat splat
           :ruler-extenders (:lambdas))

(defthm-flag-splat

(defthm car-splat-bound
  (<= (car (splat x print-base print-radix indent eviscp col channel state))
      (fixnum-bound))
  :rule-classes (:linear :rewrite)
  :flag splat)

(defthm car-splat1-bound
  (<= (car (splat1 x print-base print-radix indent eviscp col channel state))
      (fixnum-bound))
  :rule-classes (:linear :rewrite)
  :flag splat1)
)

(defthm-flag-splat

(defthm natp-car-splat
  (implies (and (force (natp col))
                (force (natp indent)))
           (natp (car (splat x print-base print-radix indent eviscp col channel
                             state))))
  :rule-classes :type-prescription
  :flag splat)

(defthm natp-car-splat1
  (implies (and (force (natp col))
                (force (natp indent)))
           (natp (car (splat1 x print-base print-radix indent eviscp col
                              channel state))))
  :rule-classes :type-prescription
  :flag splat1)
)

(defthm open-output-channel-p1-splat-string
  (implies (force (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1
            chan1
            :character
            (mv-nth 1 (splat-string x indent col chan2 state))))
  :hints (("Goal" :in-theory (enable splat-string))))

(defthm-od splat-string
  :mv-nth 1
  :hints (("Goal" :in-theory (enable splat-string))))

(defthm state-p1-mv-nth-1-splat-string
  (implies (and (force (state-p1 state))
                (force (open-output-channel-p1 channel :character state)))
           (state-p1
            (mv-nth 1 (splat-string x indent col channel state))))
  :hints (("Goal" :in-theory (enable splat-string))))

(encapsulate
  ()

  (local (include-book "kestrel/file-io-light/prin1-with-slashes" :dir :system))

  (defthm state-p1-of-prin1-with-slashes
    (implies (and (state-p1 state)
                  (open-output-channel-p channel :character state))
             (state-p1 (prin1-with-slashes s slash-char channel state))))

  (defthm open-output-channel-p1-of-prin1-with-slashes
    (implies (open-output-channel-p1 channel typ state)
             (open-output-channel-p1 channel typ
                                     (prin1-with-slashes s slash-char channel2
                                                         state))))

  (defthm-od prin1-with-slashes1)

  (defthm-od prin1-with-slashes
    :hints (("Goal" :in-theory (enable prin1-with-slashes)))))

(in-theory (disable prin1-with-slashes))

(defthm open-output-channel-p1-splat-atom
  (implies (force (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1
            chan1
            :character
            (mv-nth 1 (splat-atom x print-base print-radix indent col chan2
                                  state))))
  :hints (("Goal" :in-theory (enable splat-atom))))

(defthm-od splat-atom
  :mv-nth 1
  :hints (("Goal" :in-theory (enable splat-atom))))

(defthm-flag-splat

(defthm open-output-channel-p1-mv-nth-1-splat
  (implies (force (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1
            chan1
            :character
            (mv-nth 1 (splat x print-base print-radix indent eviscp col channel
                             state))))
  :flag splat)

(defthm open-output-channel-p1-mv-nth-1-splat1
  (implies (force (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1
            chan1
            :character
            (mv-nth 1 (splat1 x print-base print-radix indent eviscp col channel
                              state))))
  :flag splat1)
)

(defthm-flag-od (splat splat1)
  :mv-nth 1)

(defthm state-p1-mv-nth-1-splat-atom
  (implies (and (force (state-p1 state))
                (force (open-output-channel-p1 channel :character state)))
           (state-p1
            (mv-nth 1 (splat-atom x print-base print-radix indent col channel
                                  state))))
  :hints (("Goal" :in-theory (enable splat-atom))))

(defthm-flag-splat

(defthm state-p1-mv-nth-1-splat
  (implies (and (force (state-p1 state))
                (force (open-output-channel-p1 channel :character state)))
           (state-p1
            (mv-nth 1 (splat x print-base print-radix indent eviscp col channel
                             state))))
  :flag splat)

(defthm state-p1-mv-nth-1-splat1
  (implies (and (force (state-p1 state))
                (force (open-output-channel-p1 channel :character state)))
           (state-p1
            (mv-nth 1 (splat1 x print-base print-radix indent eviscp col
                              channel state))))
  :flag splat1)
)

(defthm fmt-state-p-princ$
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable fmt-state-p))))

(defthm fmt-state-p-spaces1
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p (spaces1 n col hard-right-margin channel state))))

(defthm fmt-state-p-spaces
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p (spaces n col channel state)))
  :hints (("Goal" :in-theory (enable spaces))))

(defthm fmt-state-p-mv-nth-1-splat-string
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p
            (mv-nth 1 (splat-string x indent col channel state))))
  :hints (("Goal" :in-theory (enable splat-string))))

(defthm fmt-state-p-prin1-with-slashes1
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p (prin1-with-slashes1 l slash-char channel state))))

(defthm fmt-state-p-prin1-with-slashes
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p (prin1-with-slashes s slash-char channel state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes))))

(defthm fmt-state-p-mv-nth-1-splat-atom
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p
            (mv-nth 1 (splat-atom x print-base print-radix indent col channel
                                  state))))
  :hints (("Goal" :in-theory (enable splat-atom))))

(defthm-flag-splat

(defthm fmt-state-p-mv-nth-1-splat
  (implies (and (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p
            (mv-nth 1 (splat x print-base print-radix indent eviscp col channel
                             state))))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((splat x print-base print-radix indent eviscp col channel
                          state))))
  :flag splat)

(defthm fmt-state-p-mv-nth-1-splat1
  (implies (and (consp x)
                (force (fmt-state-p state))
                (force (open-output-channel-p1 channel :character state)))
           (fmt-state-p
            (mv-nth 1 (splat1 x print-base print-radix indent eviscp col
                              channel state))))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((splat1 x print-base print-radix indent eviscp col
                           channel state))))
  :flag splat1)
)

(verify-guards splat)

(local (in-theory (disable functional-commutativity-of-minus-*-left)))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (verify-termination number-of-digits
    (declare (xargs :verify-guards nil)))

  (defthm natp-number-of-digits
; Even though ACL2 deduces this lemma when verify-termination admits
; number-of-digits just above, this lemma needs to be here explicitly when
; #-acl2-devel, because that verify-termination is redundant in that case.
    (natp (number-of-digits n print-base print-radix))
    :rule-classes :type-prescription))

(defthm number-of-digits-bound
  (<= (number-of-digits n print-base print-radix)
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(in-theory (disable number-of-digits floor))

(verify-guards number-of-digits
  :otf-flg t)

(verify-termination left-pad-with-blanks
  (declare (xargs :guard-hints (("Goal" :in-theory (enable fmt-state-p))))))

(verify-termination evisc-tuple ; and guards
  (declare (xargs :verify-guards t)))

(verify-termination term-evisc-tuple ; and guards
  (declare (xargs :verify-guards t)))

(verify-termination gag-mode-evisc-tuple ; and guards
  (declare (xargs :verify-guards t)))

(in-theory (disable find-alternative-start fmt-char))

(verify-termination scan-past-empty-fmt-directives1
  (declare (xargs :verify-guards nil)))

(defthm scan-past-empty-fmt-directives1-bound
  (<= (scan-past-empty-fmt-directives1 s alist i maximum clk)
      (fixnum-bound))
  :rule-classes (:linear :rewrite))

(in-theory (disable scan-past-empty-fmt-directives1))

(defthm characterp-fmt-char
  (implies (and (stringp s)
                (<= maximum (length s))
                (natp i)
                (<= maximum (fixnum-bound))
                (posp j))
           (characterp (fmt-char s i j maximum err-flg)))
  :hints (("Goal" :in-theory (enable fmt-char)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-find-alternative-start
  (implies (and (force (natp i))
                (force (natp maximum)))
           (natp (find-alternative-start x s i maximum quiet)))
  :hints (("Goal" :in-theory (enable find-alternative-start)))
  :rule-classes :type-prescription)

(defthm fixnump-find-alternative-start
  (implies (and (natp i)
                (< i maximum)
                (<= maximum (fixnum-bound)))
           (<= (find-alternative-start1 x s i maximum quiet)
               (fixnum-bound)))
  :rule-classes (:linear :rewrite))

(defthm find-alternative-start-bound
  (implies (and (natp i)
                (natp maximum)
                (<= i maximum))
           (<= (find-alternative-start x s i maximum quiet)
               maximum))
  :hints (("Goal" :in-theory (enable find-alternative-start)))
  :rule-classes (:linear :rewrite))

(defthm character-alistp-append
  (implies (character-alistp x)
           (equal (character-alistp (append x y))
                  (character-alistp y))))

(verify-guards scan-past-empty-fmt-directives1)

(verify-termination scan-past-empty-fmt-directives)

(defthm-od prin1$
  :hints (("Goal" :in-theory (enable prin1$))))

(verify-termination flpr1) ; also flpr11, but not guards

(make-flag flag-flpr1 flpr1)

(defthm-flag-flpr1
  (defthm state-p1-and-open-output-channel-p1-flpr1
    (implies
     (and (state-p1 state)
          (open-output-channel-p1 channel :character state))
     (and (state-p1 (flpr1 x channel state eviscp))
          (open-output-channel-p1 channel :character (flpr1 x channel state eviscp))))
    :flag flpr1)
  (defthm state-p1-and-open-output-channel-p1-flpr11
    (implies
     (and (state-p1 state)
          (open-output-channel-p1 channel :character state))
     (and (state-p1 (flpr11 x channel state eviscp))
          (open-output-channel-p1 channel :character (flpr11 x channel state eviscp))))
    :flag flpr11))

(in-theory (disable prin1$))

(verify-termination out-of-time-the2s) ; and guards

(verify-termination char?) ; and guards

(defthm characterp-char?
  (implies (force (stringp s))
           (characterp (char? s i)))
  :rule-classes :type-prescription)

(in-theory (disable char? fmt-tilde-s1 fmt-tilde-cap-s1))

(verify-termination min-fixnat$inline) ; and guards

(defthm-flag-od (flpr1 flpr11)
  :hints (("Goal"
           :in-theory
           (enable open-output-channel-p1-princ$-diff
                   open-output-channel-p1-prin1$-diff
                   open-output-channel-p1-prin1-with-slashes-diff))))

(defthm open-output-channel-p1-flpr1-strong
  (implies
   (and (state-p1 state)
        (open-output-channel-p1 chan1 :character state))
   (open-output-channel-p1 chan1
                           :character
                           (flpr1 x channel state eviscp)))
  :hints (("Goal"
           :in-theory (enable open-output-channel-p1-flpr1-diff)
           :cases ((equal chan1 channel)))))

(defthm open-output-channel-p1-flpr11-strong
  (implies
   (and (state-p1 state)
        (open-output-channel-p1 chan1 :character state))
   (open-output-channel-p1 chan1
                           :character
                           (flpr11 x channel state eviscp)))
  :hints (("Goal"
           :in-theory (enable open-output-channel-p1-flpr11-diff)
           :cases ((equal chan1 channel)))))

(verify-guards flpr1) ; also flpr11

(verify-termination flpr) ; and guards

(defthm fmt-state-p-prin1$ ; force might not be necessary below
  (implies
   (and (force (fmt-state-p state))
        (force (open-output-channel-p1 channel :character state)))
   (fmt-state-p (prin1$ x channel state)))
  :hints (("goal" :in-theory (enable fmt-state-p prin1$))))

(encapsulate
  ()
  (local (include-book "kestrel/file-io-light/prin1-dollar" :dir :system))

; Redundant with the include-book above:
  (defthm state-p1-of-prin1$
    (implies (and (open-output-channel-p channel :character state)
                  (state-p1 state))
             (state-p1 (prin1$ x channel state)))))

(defthm open-output-channel-p1-prin1$
  (implies (open-output-channel-p1 chan1 typ state)
           (open-output-channel-p1 chan1 typ
                                   (prin1$ x chan2 state)))
  :hints (("Goal" :in-theory (enable prin1$))))

(defthm-flag-flpr1
  (defthm fmt-state-p-flpr1
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (fmt-state-p (flpr1 x channel state eviscp)))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((flpr1 x channel state eviscp))))
    :flag flpr1)
  (defthm fmt-state-p-flpr11
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (fmt-state-p (flpr11 x channel state eviscp)))
    :flag flpr11)
  :hints (("Goal"
           :in-theory
           (e/d* (flpr1 flpr11 fmt-state-p
                        open-output-channel-diff)
                 ((:definition fmt-var) ; trivial impact on performance
                  (:definition member-equal)
                  (:definition spaces1) ; trivial impact on performance
                  (:definition standard-evisc-tuplep)
                  (:definition scan-past-whitespace) ; trivial impact on perf.
                  )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ppr
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; -----------------------------------------------------------------
; Signed- and Unsigned-byte-p Rules

; Note that the :forward-chaining version of the rule below only applies to
; bits = 30.

(defthm unsigned-byte-p-implies-signed-byte-p
  (implies (and (natp bits)
                (< 0 bits)
                (unsigned-byte-p (- bits 1) x))
           (signed-byte-p bits x))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :corollary
    (implies (unsigned-byte-p #.*fixnat-bits* x)
             (signed-byte-p 30 x)))))

; The tau system can prove
; (implies (and (integerp x)
;               (<= 0 x)
;               (<= x (fixnum-bound)))
;          (unsigned-byte-p #.*fixnat-bits* x))
; even when unsigned-byte-p is disabled.  So we won't prove that.

; We already know, via the built-in forward-chaining rule
; UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP, that unsigned-byte-p implies
; natp.  So we just need:

(defthm signed-byte-p-30-t
  (implies (and (integerp x)
                (<= (- (+ 1 (fixnum-bound))) x)
                (<= x (fixnum-bound)))
           (signed-byte-p 30 x)))

; The built-in rule SIGNED-BYTE-P-FORWARD-TO-INTEGERP tells us
; the obvious.  But we need:
(defthm signed-byte-p-lower-bound
  (implies (signed-byte-p 30 x)
           (<= (- (+ 1 (fixnum-bound))) x))
  :rule-classes :forward-chaining)

(defthm signed-byte-p-upper-bound
  (implies (signed-byte-p 30 x)
           (<= x (fixnum-bound)))
  :rule-classes :forward-chaining)

(defthm small-nat-upper-bound
  (implies (unsigned-byte-p #.*small-nat-bits* x)
           (<= x *small-hi*))
  :rule-classes :forward-chaining)

(defthm signed-byte-p-27-t
  (implies (and (integerp x)
                (<= *small-lo* x)
                (<= x *small-hi*))
           (signed-byte-p *small-bits* x)))

(defthm signed-byte-p-small-nil
  (signed-byte-p *small-bits* (round-to-small nil x)))

(defthm signed-byte-p-small-t
  (unsigned-byte-p *small-nat-bits* (round-to-small t x)))

(in-theory (disable round-to-small round-to-small$inline))

(defthm sums-of-smalls
  (and (implies (signed-byte-p *small-bits* x)
                (signed-byte-p 30 x))
       (implies (and (signed-byte-p *small-bits* x)
                     (signed-byte-p *small-bits* y))
                (signed-byte-p 30 (+ x y)))
       (implies (and (signed-byte-p *small-bits* x)
                     (signed-byte-p *small-bits* y)
                     (signed-byte-p *small-bits* z))
                (signed-byte-p 30 (+ x y z)))
       (implies (and (signed-byte-p *small-bits* x)
                     (signed-byte-p *small-bits* y)
                     (signed-byte-p *small-bits* z)
                     (signed-byte-p *small-bits* u))
                (signed-byte-p 30 (+ x y z u)))
       (implies (and (signed-byte-p *small-bits* x)
                     (signed-byte-p *small-bits* y)
                     (signed-byte-p *small-bits* z)
                     (signed-byte-p *small-bits* u)
                     (signed-byte-p *small-bits* v))
                (signed-byte-p 30 (+ x y z u v)))))

(defthm small-nat-implies-fixnum
  (implies (unsigned-byte-p *small-nat-bits* x)
           (signed-byte-p *fixnum-bits* x))
  :rule-classes
  (:rewrite :forward-chaining))

; This lemma may not be needed if flsz-atom had a guard of small-nat instead of
; fixnat

(defthm small-nat-implies-fixnat
  (implies (unsigned-byte-p *small-nat-bits* x)
           (unsigned-byte-p *fixnat-bits* x))
  :rule-classes
  (:rewrite :forward-chaining))

(defthm small-implies-fixnum
  (implies (signed-byte-p *small-bits* x)
           (signed-byte-p *fixnum-bits* x))
  :rule-classes
  (:rewrite :forward-chaining))

(in-theory (disable signed-byte-p unsigned-byte-p))

; -----------------------------------------------------------------
; Min and Max

(defthm unsigned-byte-p-min
  (implies (and (unsigned-byte-p bits x)
                (unsigned-byte-p bits y))
           (unsigned-byte-p bits (min x y))))

(defthm signed-byte-p-min
  (implies (and (signed-byte-p bits x)
                (signed-byte-p bits y))
           (signed-byte-p bits (min x y))))

(defthm unsigned-byte-p-max
  (implies (and (unsigned-byte-p bits x)
                (unsigned-byte-p bits y))
           (unsigned-byte-p bits (max x y))))

(defthm signed-byte-p-max
  (implies (and (signed-byte-p bits x)
                (signed-byte-p bits y))
           (signed-byte-p bits (max x y))))

(in-theory (disable min max))

(verify-termination ppr2-flat)

(in-theory (disable print-base-p))

(verify-termination flsz1)

(defthm flsz1-bound
  (implies (and (unsigned-byte-p #.*small-nat-bits* j)
                (integerp maximum))
           (unsigned-byte-p #.*small-nat-bits*
                            (flsz1 x print-base print-radix j maximum state eviscp))))

(verify-guards flsz1
  :hints (("Goal" :in-theory (enable min))))

(in-theory (disable flsz1))

; Now we begin work on ppr1.  The output is characterized by ppr-tuple-p and
; ppr-tuple-lst-p.

(verify-termination ppr-tuple-p) ; and guards

(defthm ppr-tuple-p-implies-true-listp
  (implies (ppr-tuple-lst-p lst)
           (true-listp lst))
  :rule-classes :forward-chaining)

(defthm ppr-tuple-p-small-cadr
  (implies (ppr-tuple-p x)
           (unsigned-byte-p #.*small-nat-bits* (cadr x)))
  :rule-classes (:forward-chaining))

(defthm ppr-tuple-lst-p-small-cadr-car
  (implies (and (ppr-tuple-lst-p lst)
                (consp lst))
           (unsigned-byte-p #.*small-nat-bits* (cadr (car lst))))
  :rule-classes (:forward-chaining))

(verify-termination max-width) ; and guards

(defthm general-type-of-max-width
  (implies (and (ppr-tuple-lst-p lst)
                (signed-byte-p #.*small-bits* maximum))
           (if (consp lst)
               (unsigned-byte-p #.*small-nat-bits* (max-width lst maximum))
               (equal (max-width lst maximum) maximum)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p)))
  :rule-classes nil)

(defthm small-natp-max-width-lemma-1
  (implies (and (ppr-tuple-lst-p lst)
                (signed-byte-p #.*small-bits* maximum)
                (consp lst))
           (unsigned-byte-p #.*small-nat-bits* (max-width lst maximum)))
  :hints (("Goal" :use general-type-of-max-width))
  :rule-classes :forward-chaining)

(defthm small-natp-max-width-lemma-2
  (implies (and (ppr-tuple-lst-p lst)
                (unsigned-byte-p #.*small-nat-bits* maximum))
           (unsigned-byte-p #.*small-nat-bits* (max-width lst maximum)))
  :hints (("Goal" :use general-type-of-max-width))
  :rule-classes :forward-chaining)

(defthm max-width-opener
  (implies (not (consp lst))
           (equal (max-width lst maximum) maximum)))

(defthm small-natp-max-width-lemma-3
  (implies (and (ppr-tuple-lst-p lst)
                (signed-byte-p #.*small-bits* maximum))
           (equal (unsigned-byte-p #.*small-nat-bits* (max-width lst maximum))
                  (if (consp lst)
                      t
                      (unsigned-byte-p #.*small-nat-bits* maximum)))))

(defthm small-natp-max-width-lemma-4
  (implies (and (ppr-tuple-lst-p lst)
                (signed-byte-p #.*small-bits* maximum))
           (signed-byte-p #.*small-bits* (max-width lst maximum)))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable max-width))

(verify-termination keyword-param-valuep) ; and guards

(verify-termination cons-ppr1-guardp) ; and guards

(verify-termination cons-ppr1) ; and guards

; Note: The reason we don't need the small natural arithmetic restrictions on
; column and width below is that cons-ppr1 uses +g! arithmetic, which means is
; coerces all quantities to small naturals.

(defthm ppr-tuple-lst-p-cons-ppr1
  (implies (and (ppr-tuple-p x)
                (ppr-tuple-lst-p column))
           (ppr-tuple-lst-p
            (cons-ppr1 x column width ppr-flat-right-margin
                       pair-keywords-p eviscp))))

(in-theory (disable cons-ppr1))

(defthm symbol-to-fixnat-alistp-implies-symbol-alistp
  (implies (symbol-to-fixnat-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

(defthm fixnat-cdr-assoc-symbol-to-fixnat-alistp
  (implies (and (symbol-to-fixnat-alistp alist)
                (assoc sym alist))
           (unsigned-byte-p #.*fixnat-bits* (cdr (assoc-equal sym alist))))
  :rule-classes
  ((:type-prescription :corollary
                       (implies (and (symbol-to-fixnat-alistp alist)
                                     (assoc-equal sym alist))
                                (natp (cdr (assoc-equal sym alist)))))
   (:linear :corollary
            (implies (and (symbol-to-fixnat-alistp alist)
                          (assoc-equal sym alist))
                     (<= (cdr (assoc-equal sym alist)) (fixnum-bound))))))

(verify-termination special-term-num) ; and guards

; These lemmas are necessary for the termination of ppr1 and ppr1-lst.

(defthm nthcdr-nil
  (implies (atom x)
           (equal (nthcdr n x)
                  (if (zp n) x nil))))

(defthm acl2-count-nthcdr
  (implies (and (natp n)
                (consp x)
                (<= n (len x)))
           (< (acl2-count (cdr (nthcdr n x)))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-take
  (implies (and (force (natp n))
                (force (consp x))          ; <--- added force
                (force (< n (len x)))      ; <--- added force
                )
           (< (acl2-count (take n x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm take-len
  (equal (take (len x) x)
         (append x nil)))

(defthm acl2-count-append
  (<= (acl2-count (append x nil))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-car-take
  (implies (and (natp n)
                (consp x) ;(force )
                (force (< n (len x))))
           (< (acl2-count (car (take n x)))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-cdr-take
  (implies (and (natp n)
                (consp x) ; (force )
                (force (< n (len x))))
           (< (acl2-count (cdr (take n x)))
              (acl2-count x)))
  :rule-classes :linear)

(verify-termination ppr1)

(make-flag flag-ppr1 ppr1
; Eliminates nearly 2/3 of the time for flag-lemma-for-ppr-tuple-p-ppr1:
           :ruler-extenders (:lambdas))

; I now develop a computed hint for this the theorem that ppr1/ppr1-lst
; produces ppr-tuple-ps.

(mutual-recursion
 (defun find-all-calls (fn term ans)
   (cond ((variablep term) ans)
         ((fquotep term) ans)
         ((eq (ffn-symb term) fn)
          (cond ((member-equal term ans) ans)
                (t (find-all-calls-lst fn (fargs term) (cons term ans)))))
         (t (find-all-calls-lst fn (fargs term) ans))))
 (defun find-all-calls-lst (fn lst ans)
   (cond ((endp lst) ans)
         (t (find-all-calls fn (car lst)
                            (find-all-calls-lst fn (cdr lst) ans))))))

(set-state-ok t)

(verify-termination ffnnamep) ; and guards

(defun when-stable-open-concl-and-later-enable
    (opened-conclp enabledp clause stable-under-simplificationp state)

; The idea here is that we'll start with ppr1/ppr1-lst disabled.  The flagged
; induction will produce a bunch of hideous induction steps which we'll simplify
; without expanding any ppr1/ppr1-lst terms.  When the subgoal becomes stable,
; we'll explicitly :expand only the ppr1/ppr1-lst in the concluding literal.
; If it becomes stable again and ppr1/ppr1-lst still occur in the subgoal,
; we'll enable them and let the prover just do its job.

; The first two args are flags that indicate whether we've expanded the
; ppr1/ppr1-lst call in the concl and whether after reaching stability (again)
; we've enabled ppr1/ppr1-lst.

  (cond
   (stable-under-simplificationp
    (cond
     ((not opened-conclp)
      (let ((ppr1-lst-calls-in-concl (find-all-calls-lst 'ppr1-lst (car (last clause)) nil))
            (ppr1-calls-in-concl (find-all-calls-lst 'ppr1 (car (last clause)) nil)))
        (cond ((and ppr1-lst-calls-in-concl
                    (null (cdr ppr1-lst-calls-in-concl)))
               (value
                `(:computed-hint-replacement
                  ((when-stable-open-concl-and-later-enable
                    t ,enabledp clause stable-under-simplificationp state))
                  :expand ,ppr1-lst-calls-in-concl
                  :in-theory (disable ppr1 ppr1-lst fix))))
              ((and ppr1-calls-in-concl
                    (null (cdr ppr1-calls-in-concl)))
               (value
                `(:computed-hint-replacement
                  ((when-stable-open-concl-and-later-enable
                    t ,enabledp clause stable-under-simplificationp state))
                  :expand ,ppr1-calls-in-concl
                  :in-theory (disable ppr1 ppr1-lst fix))))
              ((not enabledp)
               (cond ((or (ffnnamep-lst 'ppr1 clause)
                          (ffnnamep-lst 'ppr1-lst clause))
                      (value `(:computed-hint-replacement
                               ((when-stable-open-concl-and-later-enable
                                 t t clause stable-under-simplificationp state))
                               :in-theory (e/d (ppr1 ppr1-lst)
                                               (fix)))))
                     (t (value nil))))
              (t (value nil)))))
     ((not enabledp)
      (cond ((or (ffnnamep-lst 'ppr1 clause)
                 (ffnnamep-lst 'ppr1-lst clause))
             (value `(:computed-hint-replacement
                      ((when-stable-open-concl-and-later-enable
                        t t clause stable-under-simplificationp state))
                      :in-theory (e/d (ppr1 ppr1-lst)
                                      (fix)))))
            (t (value nil))))
     (t (value nil))))
   (t (value nil))))

(defthm-flag-ppr1
  (defthm ppr-tuple-p-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1)
  (defthm ppr-tuple-lst-p-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst)
  :hints ((when-stable-open-concl-and-later-enable
           nil nil clause stable-under-simplificationp state)
          ("Goal"
           :in-theory (disable fix ppr1 ppr1-lst)
           :do-not-induct t) ; to stop on first checkpoint
          ))
; Time:  252.77 seconds (prove: 252.02, print: 0.74, other: 0.01)
; Prover steps counted:  14787547

; The above theorem has an interesting history.  The first tolerable proof of
; this theorem took about 1500 + 2500 seconds, a little over an hour.  In that
; proof, ppr1 was doing fixnum based arithmetic with +f!.  But the fundamental
; problem with proving things about ppr1 is not the arithmetic but the long
; list of let* bindings, most of which contain IFs.  The composition of these
; bindings, which feed into recursive calls of ppr1/ppr1-lst, produce a lot of
; case splits which in turn produce a lot of induction hypotheses.  The flagged
; induction scheme has 76 cases, three of which are base cases and the rest are
; induction steps.  The average number of induction hypotheses in those
; induction steps is 4 and some steps have as many as 9 induction hyps.  Of
; course, each of these hypotheses introduces an instance of ppr1/ppr1-lst
; which can easily expand.

; To deal with that I defined an alternative version of ppr1/ppr1-lst, called
; abc1/abc1-lst, in which all the non-essential IFs were hidden in 20 helper
; functions.  Of course, that required proving that abc1 is actually ppr1,
; which took 1500 seconds, and also proving the ppr-tuple-p theorem here, for
; abc1, which took 2500 seconds and involved dozens of lemmas about abc1 helper
; functions.

; My description of the proof was:

;   The proof goes into flagged induction and generates 14 cases.  Cases
;   Subgoal *1/14 through Subgoal *1/5 are all proved using the 28
;   abc1-helper-lemmas above.  But Subgoal *1/4'' was so messy I couldn't see
;   any more abc1-helper-lemmas and decided to just let it rip.

;   Subgoal *1/4'', shown below, split 224 ways by expanding splitters:
;   ((:DEFINITION INTEGER-RANGE-P)
;    (:DEFINITION MAX)
;    (:DEFINITION UNSIGNED-BYTE-P))

;   before the clause became stable (which would have fired the
;   when-stable-then hint).  Those 224 cases split further, some generating
;   subgoals like: Subgoal *1/4.224.5.11.114.101.102.55.  In all, a total of
;   238,555 were generated in the proof of *1/4.  The when-stable-then hint
;   fired 315 times.  The subsequent cases were similar but simpler.  Subgoal
;   *1/3 split 97 ways on the same splitters above and then the
;   when-stable-then hint fired on six of those cases to finish the proof.
;   *1/2 was similar but only split 9 ways.  *1/1 was simple.

; I then decided to change the arithmetic from fixnum based to small number
; based, with +g coercing (``rounding'') the final fixnum to a small num so
; that now we know +g always produced a small num regardless of what small
; numbers are summed (but we do have to prove that the small numbers sum to a
; fixnum, which is generally easy).  Because I thought that might solve my case
; explosion problem, I decided to abandon the abc1/abc1-lst approach and deal
; directly with ppr1/ppr1-lst.

; I managed to succeed that way, but the proof of the ppr-tuple-p theorem for
; ppr1/ppr1-lst took 8361.77 seconds or over 2 hours.

; I noticed that FIX was causing some splits and since FIX is not involved I
; investigated and learned that it is introduced into the proof by the axiom
; UNICITY-OF-0.  Just disabling FIX saved, perhaps, a thousand seconds.  I
; tried various versions of the hint and got times still in the 6000 second
; range, such as the proof below:

; (set-state-ok t)

; (defun when-stable-then (hints new-computed-hint clause stable-under-simplificationp state)
;   (declare (ignore clause))
;   (cond
;    (stable-under-simplificationp
;     (prog2$
;      (cw "Stable: adding ~x0 and ~x1~%"
;          hints new-computed-hint)
;      (value (cond ((null new-computed-hint) hints)
;                   (t `(:computed-hint-replacement
;                        (,new-computed-hint)
;                        ,@hints))))))
;    (t (value nil))))

; In the following version fix, ppr1, and ppr1-lst are initially disabled.
; Upon reaching stability we enable ppr1 and ppr1-lst (keeping fix disabled)
; and :expand the occurrences of ppr1 and ppr1-lst on the controlling variables
; x and lst respectively.

; (defthm-flag-ppr1
;   (defthm ppr-tuple-p-ppr1
;     (implies (and
;               (unsigned-byte-p #.*fixsmnat-bits* width)
;               (unsigned-byte-p #.*fixsmnat-bits* rpc)
;               (symbol-to-fixnat-alistp
;                (table-alist 'ppr-special-syms (w state))))
;              (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
;     :flag ppr1)
;   (defthm ppr-tuple-lst-p-ppr1-lst
;     (implies (and
;               (unsigned-byte-p #.*fixsmnat-bits* width)
;               (unsigned-byte-p #.*fixsmnat-bits* rpc)
;               (symbol-to-fixnat-alistp
;                (table-alist 'ppr-special-syms (w state))))
;              (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
;                                         pair-keywords-p state eviscp)))
;     :flag ppr1-lst)
;   :hints (
;           (when-stable-then
;            '(:in-theory
;              (e/d (ppr1 ppr1-lst)
;                   (fix))
;              :expand
;              ((:free (print-base print-radix width rpc state eviscp)
;                      (ppr1 x print-base print-radix width rpc state eviscp))
;               (:free (print-base print-radix width rpc
;                                  pair-keywords-p state eviscp)
;                      (ppr1-lst lst print-base print-radix width rpc
;                                pair-keywords-p state eviscp))))
;            nil
;            clause stable-under-simplificationp state)
;           ("Goal"
;            :in-theory (disable fix ppr1 ppr1-lst)
;            :do-not-induct t) ; to stop on first checkpoint
;           ))
; Time:  6033.33 seconds (prove: 6032.56, print: 0.76, other: 0.02)
; Prover steps counted:  52090526

; After further experiments I got the proof down to 252 seconds (about 4
; minutes) using the strategy above.  But it took a lot of experimenting.

(defthm integerp-max-width
  (implies (and (ppr-tuple-lst-p lst)
                (integerp ac))
           (integerp (max-width lst ac)))
  :hints (("Goal" :in-theory (enable max-width)))
  :rule-classes (:rewrite :type-prescription))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defthm difference-of-smalls
  (implies (and (signed-byte-p *small-bits* x)
                (signed-byte-p *small-bits* y))
           (signed-byte-p 30 (+ x (- y))))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defun make-use-lst (calls lemma-name lemma-vars)
  (cond
   ((endp calls) nil)
   (t (cons (list* :instance lemma-name
                   (pairlis$ lemma-vars
                             (pairlis-x2 (fargs (car calls)) nil)))
            (make-use-lst (cdr calls) lemma-name lemma-vars)))))

(defun verify-guards-ppr1/ppr1-lst-strategy
    (ppr-tuple-lemmas-used ppr-tuple-defs-enabled clause stable-under-simplificationp state)
; The first two args are flags that indicate whether we've used the ppr-tuple-p
; lemmas and whether we've enabled min, max, and integer-range-p.

  (cond
   (stable-under-simplificationp
    (cond
     ((not ppr-tuple-lemmas-used)
      (let* ((ppr1-lst-calls (find-all-calls-lst 'ppr1-lst clause nil))
             (ppr1-calls (find-all-calls-lst 'ppr1 clause nil))
             (ppr1-uses (make-use-lst ppr1-calls
                                      'ppr-tuple-p-ppr1
                                      '(x print-base print-radix width rpc state eviscp)))
             (ppr1-lst-uses (make-use-lst ppr1-lst-calls
                                          'ppr-tuple-lst-p-ppr1-lst
                                          '(lst print-base print-radix width rpc
                                                pair-keywords-p state eviscp)))
             (enables (if ppr1-calls
                          (if ppr1-lst-calls
                              '(ppr-tuple-p ppr-tuple-lst-p)
                              '(ppr-tuple-p))
                          '(ppr-tuple-lst-p)))
             (disables (if ppr1-calls
                           (if ppr1-lst-calls
                               '(ppr-tuple-p-ppr1 ppr-tuple-lst-p-ppr1-lst)
                               '(ppr-tuple-p-ppr1))
                           '(ppr-tuple-lst-p-ppr1-lst))))
        (cond ((or ppr1-calls ppr1-lst-calls)
               (prog2$
                (cw "Stable: using ~x0 instances of ~&1.~%"
                    (+ (len ppr1-calls)
                       (len ppr1-lst-calls))
                    disables)

; We replace the hint to indicate that we've used the ppr-tuple lemmas, we
; enable ppr-tuple-p and/or ppr-tuple-lst-p so the newly added hypotheses can
; expand if appropriate, and disable the two lemmas themselves (as usual when
; :using a rule).  We rely on the global environment to keep min, max, and
; integer-range-p disabled.

                (value
                 `(:computed-hint-replacement
                   ((verify-guards-ppr1/ppr1-lst-strategy
                     t ,ppr-tuple-defs-enabled clause stable-under-simplificationp state))
                   :in-theory (e/d ,enables
                                   ,disables)
                   :use ,(append ppr1-uses ppr1-lst-uses)))))
              ((not ppr-tuple-defs-enabled)
               (cond ((or (ffnnamep-lst 'ppr-tuple-p clause)
                          (ffnnamep-lst 'ppr-tuple-lst-p clause))
                      (prog2$
                       (cw "Stable: enabling ppr-tuple-p and ppr-tuple-lst-p.~%")

; The ppr-tuple lemmas have not been used but there's no opportunity to do so
; because there are no ppr1/ppr1-lst calls in the clause.  The clause has
; settled down with some calls of min, max, and integer-range-p in it.  We
; replace the hint (in the event that ppr1/ppr1-lst somehow enter the clause)
; to record that we've enabled the splitters.  We enable min, max, and
; integer-range-p but we keep the ppr-tuple lemmas disabled.  This is probably
; unnecessary here (since neither ppr1 nor ppr1-lst are in the clause) but is
; important in the case below (where the lemmas have been used) and we want to
; keep the two situations identical just for sanity.

                       (value `(:computed-hint-replacement
                                ((verify-guards-ppr1/ppr1-lst-strategy
                                  ,ppr-tuple-lemmas-used t clause stable-under-simplificationp state))
                                :in-theory (e/d (ppr-tuple-p ppr-tuple-lst-p)
                                                (ppr-tuple-p-ppr1 ppr-tuple-lst-p-ppr1-lst))))))
                     (t (value nil))))
              (t (value nil)))))
     ((not ppr-tuple-defs-enabled)
      (cond ((or (ffnnamep-lst 'ppr-tuple-p clause)
                 (ffnnamep-lst 'ppr-tuple-lst-p clause))
             (prog2$
              (cw "Stable: enabling ppr-tuple-p and ppr-tuple-lst-p.~%")
              (value `(:computed-hint-replacement
                       ((verify-guards-ppr1/ppr1-lst-strategy
                         ,ppr-tuple-lemmas-used t clause stable-under-simplificationp state))
                       :in-theory (e/d (ppr-tuple-p ppr-tuple-lst-p)
                                       (ppr-tuple-p-ppr1 ppr-tuple-lst-p-ppr1-lst))))))
            (t (value nil))))
     (t (value nil))))
   (t (value nil))))

(defthm ppr11-never-dot
  (not
   (equal (car (ppr1 x print-base print-radix width rpc state eviscp))
          'dot))
  :hints (("Goal"
           :expand
           ((ppr1 x print-base print-radix width rpc state eviscp)))))

(defthm ppr-tuple-lst-p-list-list
  (implies (and (unsigned-byte-p #.*small-nat-bits* width)
                (consp lst))
           (ppr-tuple-lst-p (list (list 'flat width lst)))))

(defthm consp-cddr-ppr1
  (implies (symbol-to-fixnat-alistp
            (table-alist 'ppr-special-syms (w state)))
           (CONSP (CDDR (PPR1 x PRINT-BASE PRINT-RADIX WIDTH rpc STATE eviscp))))
  :hints (("Goal" :expand ((PPR1 x PRINT-BASE PRINT-RADIX WIDTH rpc STATE eviscp)
                           (PPR1 (CADR X)
                                 PRINT-BASE
                                 PRINT-RADIX (ROUND-TO-SMALL T (+ -1 WIDTH))
                                 RPC STATE EVISCP)
                           (PPR1 (CADR X)
                                 PRINT-BASE
                                 PRINT-RADIX (ROUND-TO-SMALL T (+ -1 WIDTH))
                                 RPC STATE NIL)))))

(defthm small-nat-max-difference-0
  (implies (and (unsigned-byte-p #.*small-nat-bits* x)
                (unsigned-byte-p #.*small-nat-bits* y))
           (unsigned-byte-p #.*small-nat-bits*
                            (max (+ x (- y)) 0)))
   :hints (("Goal" :in-theory (enable max unsigned-byte-p))))

(defthm not-cdddr-ppr1-flat-nil
  (implies (EQUAL (CAR (PPR1 x
                             PRINT-BASE
                             PRINT-RADIX WIDTH RPC STATE NIL))
                  'FLAT)
           (NOT (CDDDR (PPR1 x
                             PRINT-BASE
                             PRINT-RADIX WIDTH RPC STATE NIL))))
  :hints (("Goal" :expand ((PPR1 x
                                 PRINT-BASE
                                 PRINT-RADIX WIDTH RPC STATE NIL)))))

(defthm not-cdddr-ppr1-flat-not-evisceration-mark
  (implies (and (NOT (EQUAL x :EVISCERATION-MARK))
                (EQUAL (CAR (PPR1 x
                                  PRINT-BASE
                                  PRINT-RADIX WIDTH RPC STATE eviscp))
                       'FLAT))
           (NOT (CDDDR (PPR1 x
                             PRINT-BASE
                             PRINT-RADIX WIDTH RPC STATE eviscp))))
  :hints (("Goal" :expand ((PPR1 x
                                 PRINT-BASE
                                 PRINT-RADIX WIDTH RPC STATE eviscp)))))

(verify-guards ppr1
  :hints ((verify-guards-ppr1/ppr1-lst-strategy nil nil clause stable-under-simplificationp state)
          ("Goal" :in-theory (disable ppr-tuple-p ppr-tuple-lst-p))))

; -----------------------------------------------------------------
; Now we do ppr2

(verify-termination ppr2-flat) ; and guards???

(local (in-theory (enable prin1$)))

(defthm open-output-channel-p-prin1$
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel
                                        :character state))
           (open-output-channel-p1 channel :character
                                   (prin1$ x channel state))))

(in-theory (disable prin1$))

(defthm fmt-state-p-ppr2-flat
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (ppr2-flat x channel state eviscp))))

(defthm open-output-channel-p-ppr2-flat ; ``weak''
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character
                                   (ppr2-flat x channel state eviscp))))

; We can prove the strong version of the above:

; (implies (and (fmt-state-p state)
;               (open-output-channel-p1 chan1 :character state)
;               (open-output-channel-p1 channel :character state))
;          (open-output-channel-p1 chan1 :character
;                                  (ppr2-flat x channel state eviscp)))

; But it requires two open-output-channel-p1 hyps, so until we see the need for
; it we'll stick with the weak version.

; The following theorems about newline are trivially provable already, so
; we don't bother.

; (defthm state-p1-newline
;   (implies (and (state-p1 state)
;                 (open-output-channel-p1 channel :character state))
;            (state-p1 (newline channel state))))

; (defthm open-output-channel-p-newline
;   (implies (and (state-p1 state)
;                 (open-output-channel-p1 channel :character state))
;            (open-output-channel-p1 channel :character
;                                    (newline channel state))))

(verify-termination ppr2)

(make-flag flag-ppr2 ppr2)

(defthm-flag-ppr2
  (defthm fmt-state-p-and-open-output-channel-p1-ppr2-column
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (and (fmt-state-p (ppr2-column lst loc col channel state eviscp))
                  (open-output-channel-p1 channel
                                          :character
                                          (ppr2-column lst loc col channel state eviscp))))
    :flag ppr2-column)
  (defthm fmt-state-p-and-open-output-channel-p1-ppr2
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (and (fmt-state-p (ppr2 x col channel state eviscp))
                  (open-output-channel-p1 channel
                                          :character
                                          (ppr2 x col channel state eviscp))))
    :flag ppr2)
  :hints (("Goal" :in-theory (disable fix))))

; In ppr2 we see ppr2-column producing a state that is subsequently fed to
; princ$.  Princ$ requires state-p1 in its guard.  So we set up a backchaining
; rule to get that from fmt-state-p.

(defthm fmt-state-p-implies-state-p1-ppr2-column
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (state-p (ppr2-column lst loc col channel state eviscp))))

(defthm fmt-state-p-implies-state-p1-ppr2
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (state-p (ppr2 lst col channel state eviscp))))

(set-state-ok t)

(defun when-stable-expand-ppr-tuple (clause stable-under-simplificationp state)
  (cond
   (stable-under-simplificationp
    (let* ((call1 (member-equal '(not (ppr-tuple-p x)) clause))
           (call2 (member-equal '(not (ppr-tuple-lst-p lst)) clause))
           (calls (if call1
                      (if call2
                          '((ppr-tuple-p x)
                            (ppr-tuple-lst-p lst))
                          '((ppr-tuple-p x)))
                      (if call2
                          '((ppr-tuple-lst-p lst))
                          nil))))
      (if calls
          (prog2$
           (cw "Stable: added ~x0.~%"
               (list :expand calls))
           (value `(:expand ,calls)))
          (value nil))))
   (t (value nil))))

(verify-guards ppr2
  :hints ((when-stable-expand-ppr-tuple clause stable-under-simplificationp state)))
; Time:  6.14 seconds (prove: 6.04, print: 0.06, other: 0.05)
; Prover steps counted:  497673

; For what it's worth: the hint fired 45 times, each time expanding
; (ppr-tuple-p x).

; -----------------------------------------------------------------
; And finally, ppr...

(defthm fmt-state-p-implies-unsigned-byte-p-print-base
  (implies (fmt-state-p state)
           (unsigned-byte-p 5
                            (cdr (assoc-equal 'print-base
                                              (nth 2 state)))))
  :hints (("Goal" :in-theory (enable print-base-p fmt-state-p))))

(verify-termination ppr
; Hints weren't needed here during development of this book, but we
; subsequently cleaned up the guard for ppr to eliminate conjuncts that follow
; from fmt-state-p; so now we simply enable fmt-state-p to deal with that.
  (declare (xargs :guard-hints (("Goal" :in-theory (enable fmt-state-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Returning to work towards fmt etc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable ppr1))

(make-event
 (er-progn (set-gag-mode-evisc-tuple t state)
           (value '(value-triple nil))))

(in-theory (disable flsz1))

(verify-termination flsz ; and guards
  (declare (xargs :guard-hints (("Goal" :in-theory (enable fmt-state-p
                                                           print-base-p))))))

(in-theory (disable table-alist))

(verify-termination fmt-ppr ; and guards
  (declare (xargs :verify-guards t
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p))))))

(in-theory (disable
            (:d fmt-ppr) (:t fmt-ppr) (:e fmt-ppr)
            (:d eviscerate-top) (:t eviscerate-top) (:e eviscerate-top)))

(verify-termination fmt0
  (declare (xargs :verify-guards nil)))

(verify-termination fmt1
  (declare (xargs :verify-guards nil)))

(defthm characterp-nth-with-forcing
  (implies (and (character-listp x)
                (force (<= 0 i))
                (force (< i (len x))))
           (characterp (nth i x))))

; Start proof for (verify-guards fmt0 ...).

(defthm standard-evisc-tuplep-forward
  (implies (standard-evisc-tuplep x)
           (and (true-listp x)
                (alistp (car x))
                (or (null (cadr x))
                    (integerp (cadr x)))
                (or (null (caddr x))
                    (integerp (caddr x)))
                (symbol-listp (cadddr x))))
  :hints (("Goal" :in-theory (enable standard-evisc-tuplep)))
  :rule-classes :forward-chaining)

(defthm state-p1-put-global-1
  (implies (and (state-p1 state1)
                (state-p1 state2)
                (symbolp sym)
                (not (equal sym 'timer-alist))
                (not (equal sym 'current-acl2-world)))
           (state-p1 (update-nth 2
                                 (add-pair sym val (nth 2 state2))
                                 state1)))
; hints taken from state-p1-update-main-timer in axioms.lisp:
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable state-p1 global-table)
                              '(true-listp
                                ordered-symbol-alistp
                                assoc
                                sgetprop
                                integer-listp
                                rational-listp
                                true-list-listp
                                open-channels-p
                                all-boundp
                                plist-worldp
                                timer-alistp
                                known-package-alistp
                                file-clock-p
                                readable-files-p
                                written-files-p
                                read-files-p
                                writeable-files-p)))))

(defthm true-listp-update-nth-elim
  (implies (< (nfix n) (len x))
           (equal (true-listp (update-nth n val x))
                  (true-listp x))))

(defthm state-p1-put-global-2
  (implies (and (state-p1 (update-nth 2 alist state1))
                (symbolp sym)
                (not (equal sym 'timer-alist))
                (not (equal sym 'current-acl2-world)))
           (state-p1 (update-nth 2
                                 (add-pair sym val alist)
                                 state1)))
; hints taken from state-p1-update-main-timer in axioms.lisp:
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable state-p1 global-table max)
                              '(true-listp
                                ordered-symbol-alistp
                                assoc
                                sgetprop
                                integer-listp
                                rational-listp
                                true-list-listp
                                open-channels-p
                                all-boundp
                                plist-worldp
                                timer-alistp
                                known-package-alistp
                                file-clock-p
                                readable-files-p
                                written-files-p
                                read-files-p
                                writeable-files-p)))))

(defthm state-p1-iprint-oracle-updates
  (implies (state-p1 state)
           (state-p1 (iprint-oracle-updates state)))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates))))

; Start proof of state-global-unchanged-by-eviscerate-top

(defthm state-global-unchanged-by-read-acl2-oracle
  (equal (assoc-equal sym
                      (nth 2 (mv-nth 2 (read-acl2-oracle state))))
         (assoc-equal sym
                      (nth 2 state)))
  :hints (("Goal" :in-theory (enable read-acl2-oracle
                                     update-acl2-oracle))))

(defthm state-global-unchanged-by-iprint-oracle-updates
  (implies (and (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar))
                (not (equal sym 'iprint-soft-bound))
                (not (equal sym 'iprint-hard-bound)))
           (equal (assoc-equal
                   sym
                   (nth 2 (iprint-oracle-updates STATE)))
                  (assoc-equal
                   sym
                   (nth 2 state))))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates))))

(defthm state-global-unchanged-by-update-iprint-ar-fal
  (implies (and (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar)))
           (equal (assoc-equal sym
                               (nth 2 (update-iprint-ar-fal
                                       iprint-alist iprint-fal-new
                                       iprint-fal-old state)))
                  (assoc-equal sym (nth 2 state)))))

(defthm state-global-unchanged-by-brr-evisc-tuple-oracle-update
  (implies (not (equal sym 'brr-evisc-tuple))
           (equal (assoc-equal
                   sym
                   (nth 2 (brr-evisc-tuple-oracle-update state)))
                  (assoc-equal sym (nth 2 state))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable brr-evisc-tuple-oracle-update))))

(defthm state-global-unchanged-by-iprint-oracle-updates?
  (implies (and (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar))
                (not (equal sym 'iprint-soft-bound))
                (not (equal sym 'iprint-hard-bound))
                (not (equal sym 'brr-evisc-tuple))
                (not (equal sym 'evisc-hitp-without-iprint)))
           (equal (assoc-equal
                   sym
                   (nth 2 (iprint-oracle-updates? state)))
                  (assoc-equal sym (nth 2 state))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable iprint-oracle-updates?
                                     iprint-oracle-updates))))

(defthm state-global-unchanged-by-eviscerate-top
  (implies (and (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar))
                (not (equal sym 'iprint-soft-bound))
                (not (equal sym 'iprint-hard-bound))
                (not (equal sym 'brr-evisc-tuple))
                (not (equal sym 'evisc-hitp-without-iprint)))
           (equal (assoc-equal
                   sym
                   (nth
                    2
                    (mv-nth 1
                            (eviscerate-top x print-level print-length alist
                                            evisc-table hiding-cars state))))
                  (assoc-equal sym (nth 2 state))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (eviscerate-top)
                                  (eviscerate
                                   update-iprint-ar-fal
                                   BRR-EVISC-TUPLE-ORACLE-UPDATE
                                   IPRINT-ORACLE-UPDATES?)))))

; Start proof of eviscerate-top-preserves-all-boundp-lemma

(defthm iprint-oracle-updates-preserves-all-boundp-lemma
  (implies (assoc sym (nth 2 state))
           (assoc sym (nth 2 (iprint-oracle-updates state))))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates))))

(defthm brr-evisc-tuple-oracle-update-preserves-all-boundp-lemma
  (implies (assoc sym (nth 2 state))
           (assoc sym (nth 2 (brr-evisc-tuple-oracle-update state))))
  :hints (("Goal" :in-theory (enable brr-evisc-tuple-oracle-update))))

(defthm iprint-oracle-updates?-preserves-all-boundp-lemma
  (implies (assoc sym (nth 2 state))
           (assoc sym (nth 2 (iprint-oracle-updates? state))))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates?))))

(defthm update-iprint-ar-fal-preserves-all-boundp-lemma
  (implies (assoc sym (nth 2 state))
           (assoc sym (nth 2 (update-iprint-ar-fal iprint-alist iprint-fal-new
                                                   iprint-fal-old state))))
  :hints (("Goal" :in-theory (enable update-iprint-ar-fal))))

(defthm eviscerate-top-preserves-all-boundp-lemma
  (implies (assoc sym (nth 2 state))
           (assoc
            sym
            (nth 2
                 (mv-nth 1
                         (eviscerate-top x print-level print-length
                                         alist evisc-table hiding-cars
                                         state)))))
  :hints (("Goal"
           :in-theory
           (union-theories '(eviscerate-top
                             put-global
                             update-global-table
                             global-table)
                           (set-difference-theories
                            (current-theory :here)
                            (function-theory :here))))))

(defthm eviscerate-top-preserves-all-boundp
  (implies (all-boundp alist (nth 2 state))
           (all-boundp
            alist
            (nth 2
                 (mv-nth 1
                         (eviscerate-top x print-level print-length
                                         alist2 evisc-table hiding-cars
                                         state)))))
  :hints (("Goal" :in-theory (enable all-boundp))))

; Start proof of open-output-channel-p1-mv-nth-1-eviscerate-top

(defthm open-output-channel-p1-update-global-table
  (equal (open-output-channel-p1 channel type (update-nth 2 val state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(defthm open-output-channel-p1-read-acl2-oracle
  (equal (open-output-channel-p1 channel type
                                 (mv-nth 2 (read-acl2-oracle state)))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable open-output-channel-p1
                                     read-acl2-oracle
                                     update-acl2-oracle))))

(defthm open-output-channel-p1-iprint-oracle-updates
  (equal (open-output-channel-p1 channel type (iprint-oracle-updates state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates))))

(defthm open-output-channel-p1-iprint-oracle-updates?
  (equal (open-output-channel-p1 channel type (iprint-oracle-updates? state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable iprint-oracle-updates?))))

(defthm open-output-channel-p1-update-iprint-ar-fal
  (equal (open-output-channel-p1
          channel type
          (update-iprint-ar-fal iprint-alist iprint-fal-new iprint-fal-old state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable update-iprint-ar-fal))))

(defthm open-output-channel-p1-brr-evisc-tuple-oracle-update
  (equal (open-output-channel-p1
          channel type (brr-evisc-tuple-oracle-update state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable brr-evisc-tuple-oracle-update))))

(defthm open-output-channel-p1-mv-nth-1-eviscerate-top
  (equal (open-output-channel-p1
          channel
          type
          (mv-nth 1
                  (eviscerate-top x print-level print-length alist
                                  evisc-table hiding-cars state)))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (e/d (eviscerate-top)
                                  ((:DEFINITION ARRAY-ORDER)
                                   (:DEFINITION ASET1)
                                   (:DEFINITION ASET1-LST)
                                   (:DEFINITION ASSOC-EQUAL)
                                   (:DEFINITION BINARY-APPEND)
                                   (:DEFINITION BRR-EVISC-TUPLE-ORACLE-UPDATE)
                                   (:DEFINITION COMPRESS1)
                                   (:DEFINITION EVISCERATE)
                                   (:DEFINITION EVISCERATE1)
                                   (:DEFINITION EVISCERATE1P)
                                   (:DEFINITION GET-SHARP-ATSIGN)
                                   (:DEFINITION IPRINT-BLOCKEDP)
                                   (:DEFINITION IPRINT-FAL-NAME)
                                   (:DEFINITION IPRINT-ORACLE-UPDATES?)
                                   (:DEFINITION LEN)
                                   (:DEFINITION LENGTH)
                                   (:DEFINITION MAX)
                                   (:DEFINITION MV-NTH)
                                   (:DEFINITION REVERSE)
                                   (:DEFINITION ROLLOVER-IPRINT-AR)
                                   (:DEFINITION STANDARD-EVISC-TUPLEP)
                                   (:DEFINITION STRING-APPEND-LST)
                                   (:DEFINITION UPDATE-IPRINT-ALIST-FAL)
                                   (:DEFINITION UPDATE-IPRINT-AR-FAL)
                                   (:DEFINITION UPDATE-IPRINT-FAL))))))

(defthm open-output-channel-p1-mv-nth-1-eviscerate-top-forward
  (implies (open-output-channel-p1 channel type state)
           (open-output-channel-p1
            channel
            type
            (mv-nth 1
                    (eviscerate-top x print-level print-length alist
                                    evisc-table hiding-cars state))))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((mv-nth 1
                           (eviscerate-top x print-level print-length alist
                                           evisc-table hiding-cars state))))))

(defthm open-output-channel-p1-fmt-ppr-same
; Immediate from fmt-state-p-and-open-output-channel-p1-ppr2
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1
            channel
            :character
            (fmt-ppr x width rpc col channel state eviscp)))
  :hints (("Goal" :in-theory (enable fmt-ppr)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((fmt-ppr x width rpc col channel state eviscp)))))

(defthm-od ppr2-flat)

(defthm-flag-ppr2
  (defthm open-output-channel-p1-ppr2-column-diff
    (implies (not (equal chan1 channel))
             (equal (open-output-channel-p1
                     chan1
                     typ
                     (ppr2-column lst loc col channel state eviscp))
                    (open-output-channel-p1 chan1 typ state)))
    :flag ppr2-column)
  (defthm open-output-channel-p1-ppr2-diff
    (implies (not (equal chan1 channel))
             (equal (open-output-channel-p1
                     chan1
                     typ
                     (ppr2 x col channel state eviscp))
                    (open-output-channel-p1 chan1 typ state)))
    :flag ppr2)
  :hints (("Goal" :in-theory (enable* open-output-channel-diff))))

(defthm-od fmt-ppr
  :hints (("Goal" :in-theory (enable fmt-ppr))))

(defthm open-output-channel-p1-fmt-ppr
; Immediate from fmt-state-p-and-open-output-channel-p1-ppr2
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1
            chan1
            :character
            (fmt-ppr x width rpc col channel state eviscp)))
  :hints (("Goal"
           :cases ((equal chan1 channel))
           :in-theory (enable* open-output-channel-diff)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((fmt-ppr x width rpc col channel state eviscp)))))

(defthm assoc-equal-nth-2-prin1-with-slashes1
  (equal (assoc-equal sym (nth 2 (prin1-with-slashes1 x slash-char channel
                                                      state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes1))))

(defthm assoc-equal-nth-2-prin1-with-slashes
  (equal (assoc-equal sym (nth 2 (prin1-with-slashes s slash-char channel
                                                     state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes))))

(defthm assoc-equal-nth-2-prin1$
  (equal (assoc-equal sym (nth 2 (prin1$ x channel state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable prin1$))))

(defthm prin1$-preserves-eviscerate-top-state-p
  (implies (and (eviscerate-top-state-p state)
                (open-output-channel-p1 channel :character state))
           (eviscerate-top-state-p (prin1$ x channel state)))
  :hints (("Goal" :in-theory (enable eviscerate-top-state-p))))

; !! The following may be necessary at some point.
#|
(defthm state-p1-ppr2
  (implies (state-p1 state)
           (state-p1 (ppr2 x col channel state eviscp)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((ppr2 x col channel state eviscp)))))
|#

(defthm fmt-state-p-implies-state-p1-fmt-ppr
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (state-p1 (fmt-ppr x width rpc col channel state eviscp)))
  :hints (("Goal" :in-theory (enable fmt-ppr)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((fmt-ppr x width rpc col channel state eviscp)))))

(defthm characterp-fmt-char-type-prescription-forced
  (implies (and (force (stringp s))
                (force (<= maximum (length s)))
                (force (natp i))
                (force (<= maximum (fixnum-bound)))
                (force (natp j)))
           (characterp (fmt-char s i j maximum err-flg)))
  :hints (("Goal" :in-theory (enable fmt-char)))
  :rule-classes :type-prescription)

(defthm fmt-char-when-out-of-bounds
  (implies (and (natp i)
                (natp j)
                (natp maximum)
                (<= maximum (+ i j))
                (<= maximum (fixnum-bound)))
           (equal (fmt-char s i j maximum err-flg)
                  *null-char*))
  :hints (("Goal" :in-theory (enable fmt-char))))

(defthm global-table-read-acl2-oracle
  (equal (assoc-equal sym (nth 2 (mv-nth 2 (read-acl2-oracle state))))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable read-acl2-oracle update-acl2-oracle))))

(defthm state-p1-mv-nth-1-update-iprint-ar-fal
  (implies (state-p1 state)
           (state-p1
            (update-iprint-ar-fal iprint-alist iprint-fal-new iprint-fal-old
                                  state))))


(in-theory (disable (:definition array-order)
                    (:definition aset1)
                    (:definition aset1-lst)
                    (:definition compress1)
                    (:definition reverse)
                    (:definition rollover-iprint-ar)
                    (:definition update-iprint-ar-fal)
                    get-sharp-atsign
                    eviscerate
                    eviscerate1p
                    standard-evisc-tuplep
                    iprint-blockedp
                    iprint-fal-name
                    ))

(defthm state-p1-mv-nth-1-eviscerate-top
  (implies (state-p1 state)
           (state-p1
            (mv-nth 1
                    (eviscerate-top x print-level print-length alist
                                    evisc-table hiding-cars state))))
  :hints (("Goal" :in-theory (enable eviscerate-top)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((mv-nth 1
                           (eviscerate-top x print-level print-length alist
                                           evisc-table hiding-cars state))))))

(with-output
  :off :all
  :on summary
  (make-flag flag-fmt0 fmt0
             :ruler-extenders (:lambdas)

; Note: A large :hints argument, much like the one for fmt-state-p-fmt0*,
; didn't speed things up much here: 28.80 seconds down to 28.33 seconds.
; There's just a lot of case splitting!  So we keep the :hints simple here.

             :hints (("Goal" :in-theory
                      (disable fmt-var
                               member-equal
                               spaces1
                               standard-evisc-tuplep
                               scan-past-whitespace
                               princ$
                               punctp
                               mv-nth)))))

(defthm mv-nth-open
  (implies (and (posp n)
                (syntaxp (quotep n)))
           (equal (mv-nth n (cons x y))
                  (mv-nth (1- n) y))))

(defthm min-fixnat-linear
  (and (<= (min-fixnat x y) x)
       (<= (min-fixnat x y) y))
  :rule-classes :linear)

(in-theory (enable max min))

(defthm min-linear
  (and (<= (min x y) x)
       (<= (min x y) y))
  :rule-classes :linear)

(defthm fix-identity
  (implies (acl2-numberp x)
           (equal (fix x) x)))

(defthm state-global-unchanged-by-fmt-tilde-cap-s1
  (equal (assoc-equal
          sym
          (nth
           2
           (mv-nth 1
                   (fmt-tilde-cap-s1 s i maximum col channel
                                     state))))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable fmt-tilde-cap-s1))))

(defthm open-output-channel-fmt-tilde-cap-s1
  (implies (open-output-channel-p1 channel type state)
           (open-output-channel-p1
            channel
            type
            (mv-nth 1
                    (fmt-tilde-cap-s1 s i maximum col channel
                                      state))))
  :hints (("Goal" :in-theory (enable fmt-tilde-cap-s1)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((mv-nth 1
                           (fmt-tilde-cap-s1 s i maximum col channel
                                             state))))))

(defthm-od fmt-tilde-cap-s1
  :mv-nth 1
  :hints (("Goal" :in-theory (enable fmt-tilde-cap-s1))))

(defthm state-global-unchanged-by-fmt-tilde-s1
  (equal (assoc-equal
          sym
          (nth
           2
           (mv-nth 1
                   (fmt-tilde-s1 s i maximum col channel state))))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal"
           :in-theory (enable fmt-tilde-s1)
           :expand ((fmt-tilde-s1 s i (+ 1 i) 536870911 channel state)))))

(defthm open-output-channel-fmt-tilde-s1
  (implies (open-output-channel-p1 channel :character state)
           (open-output-channel-p1
            channel
            :character
            (mv-nth 1
                    (fmt-tilde-s1 s i maximum col channel state))))
  :hints (("Goal"
           :in-theory (enable fmt-tilde-s1)
           :expand ((:free (maximum col channel state)
                           (fmt-tilde-s1 s i maximum col channel state)))))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((mv-nth 1
                           (fmt-tilde-s1 s i maximum col channel state))))))

(defthm-od fmt-tilde-s1
  :mv-nth 1
  :hints (("Goal"
           :in-theory (enable fmt-tilde-s1)
           :expand ((:free (col)
                           (fmt-tilde-s1 s i maximum col channel state))))))

(defthm fmt-state-p-mv-nth-1-fmt-tilde-cap-s1
  (implies (fmt-state-p state)
           (fmt-state-p (mv-nth 1
                                (fmt-tilde-cap-s1 s i maximum col channel
                                                  state))))
  :hints (("Goal" :in-theory (enable fmt-tilde-cap-s1))))

(defthm fmt-state-p-mv-nth-1-fmt-tilde-s1
  (implies (fmt-state-p state)
           (fmt-state-p (mv-nth 1
                                (fmt-tilde-s1 s i maximum col channel state))))
  :hints (("Goal"
           :in-theory (enable fmt-tilde-s1)
           :expand ((:free (maximum col channel state)
                           (fmt-tilde-s1 s i maximum col channel state))))))

(defthm fmt-state-p-fmt-ppr
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (fmt-ppr x width rpc col channel state eviscp)))
  :hints (("Goal" :in-theory (enable fmt-ppr))))

; Start proof of eviscerate-top-state-p-eviscerate-top (to complete proof of
; fmt-state-p-mv-nth-1-eviscerate-top)

(encapsulate
  ()

(local (include-book "system/eviscerate-top-support" :dir :system))

(local (in-theory (disable dimensions)))

(local
 (defthm eviscerate-top-state-p-forward
   (implies (eviscerate-top-state-p state)
            (and (natp (cdr (assoc-equal 'iprint-hard-bound (nth 2 state))))
                 (iprint-falp (cdr (assoc-equal 'iprint-fal (nth 2 state))))
                 (array1p 'iprint-ar
                          (cdr (assoc-equal 'iprint-ar (nth 2 state))))
                 (consp (cdr (assoc-equal 'iprint-ar (nth 2 state))))
                 (natp (iprint-last-index state))
                 (iprint-array-p
                  (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                  (1+ (iprint-last-index state)))
                 (<= (* 4
                        (1+ (cdr (assoc-equal 'iprint-hard-bound
                                              (nth 2 state)))))
                     *maximum-positive-32-bit-integer*)
                 (< (cdr (assoc-equal 'iprint-hard-bound
                                      (nth 2 state)))
                    (car (dimensions 'iprint-ar
                                     (cdr (assoc-equal 'iprint-ar
                                                       (nth 2 state))))))
                 (< (cdr (assoc-equal 'iprint-hard-bound
                                      (nth 2 state)))
                    (car (dimensions 'iprint-ar
                                     (cdr (assoc-equal 'iprint-ar
                                                       (nth 2 state))))))
                 (= (maximum-length 'iprint-ar
                                    (cdr (assoc-equal 'iprint-ar
                                                      (nth 2 state))))
                    (* 4 (car (dimensions
                               'iprint-ar
                               (cdr (assoc-equal 'iprint-ar
                                                 (nth 2 state)))))))))
   :hints (("goal" :in-theory (enable eviscerate-top-state-p
                                      get-global
                                      put-global
                                      global-table)))
   :rule-classes :forward-chaining))

(local
 (defthm natp-iprint-hard-bound-composed-oracle-updates-alt
   (implies (natp (cdr (assoc-equal 'iprint-hard-bound
                                    (nth 2 state))))
            (natp (cdr (assoc-equal 'iprint-hard-bound
                                    (nth 2 (composed-oracle-updates state))))))
   :hints (("goal"
            :use natp-iprint-hard-bound-composed-oracle-updates
            :in-theory (enable get-global put-global)))))

(local
 (defthm iprint-falp-get-global-iprint-fal-composed-oracle-updates-alt
   (implies (iprint-falp
             (cdr (assoc-equal 'iprint-fal
                               (nth 2 state))))
            (iprint-falp
             (cdr (assoc-equal 'iprint-fal
                               (nth 2 (composed-oracle-updates state))))))
   :hints (("Goal"
            :use iprint-falp-get-global-iprint-fal-composed-oracle-updates
            :in-theory (enable get-global put-global)))))

(local
 (defthm array1p-iprint-ar-composed-oracle-updates-alt
   (implies (array1p 'iprint-ar
                     (cdr (assoc-equal 'iprint-ar (nth 2 state))))
            (array1p 'iprint-ar
                     (cdr (assoc-equal 'iprint-ar
                                       (nth 2 (composed-oracle-updates
                                               state))))))
   :hints (("Goal"
            :use array1p-iprint-ar-composed-oracle-updates
            :in-theory (enable get-global put-global)))))

; Start proof of consp-iprint-ar-composed-oracle-updates

(local
 (defthm consp-iprint-ar-iprint-oracle-updates?
   (implies (consp (cdr (assoc-equal 'iprint-ar (nth 2 state))))
            (consp (cdr (assoc-equal 'iprint-ar
                                     (nth 2 (iprint-oracle-updates?
                                             state))))))
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm consp-iprint-ar-brr-evisc-tuple-oracle-update
   (implies (consp (cdr (assoc-equal 'iprint-ar (nth 2 state))))
            (consp (cdr (assoc-equal 'iprint-ar
                                     (nth 2 (brr-evisc-tuple-oracle-update
                                             state))))))
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm consp-iprint-ar-composed-oracle-updates
   (implies (consp (cdr (assoc-equal 'iprint-ar (nth 2 state))))
            (consp (cdr (assoc-equal 'iprint-ar
                                     (nth 2 (composed-oracle-updates
                                             state))))))
   :hints (("Goal" :in-theory (e/d (composed-oracle-updates)
                                   (fold-into-composed-oracle-updates
                                    iprint-oracle-updates?
                                    brr-evisc-tuple-oracle-update))))))

(local
 (defthm iprint-last-index-update-nth-2-add-pair
   (implies (not (equal sym 'iprint-ar))
            (equal (iprint-last-index
                    (update-nth 2
                                (add-pair sym val (nth 2 state))
                                state))
                   (iprint-last-index state)))
   :hints (("Goal" :in-theory (enable get-global
                                      iprint-last-index
                                      iprint-last-index*)))))

(local
 (defthm composed-oracle-updates-preserves-natp-iprint-last-index-rewrite
  (implies (natp (iprint-last-index state))
           (natp (iprint-last-index (composed-oracle-updates state))))))

(local
 (defthm iprint-array-p-preserved-by-eviscerate-and-composed-oracle-updates-lemma-alt
   (implies (iprint-array-p (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                            (1+ (iprint-last-index state)))
            (iprint-array-p
             (cdr (assoc-equal 'iprint-ar
                               (nth 2 (composed-oracle-updates state))))
             (+ 1 (iprint-last-index (composed-oracle-updates state)))))
   :hints (("Goal"
            :use
            iprint-array-p-preserved-by-eviscerate-and-composed-oracle-updates-lemma
            :in-theory (enable get-global)))))

(local
 (defthm iprint-hard-bound-inequality-preserved-by-iprint-oracle-updates?-alt
   (implies (<= (+ 4
                   (* 4
                      (cdr (assoc-equal 'iprint-hard-bound
                                        (nth 2 state)))))
                *maximum-positive-32-bit-integer*)
            (<= (+ 4
                   (* 4
                      (cdr (assoc-equal 'iprint-hard-bound
                                        (nth 2 (composed-oracle-updates
                                                state))))))
                *maximum-positive-32-bit-integer*))
   :hints (("Goal"
            :use iprint-hard-bound-inequality-preserved-by-iprint-oracle-updates?
            :in-theory (enable get-global)))))

(local
 (defthm one-more-lemma-alt
   (implies (< (cdr (assoc-equal 'iprint-hard-bound (nth 2 state)))
               (car (dimensions 'iprint-ar
                                (cdr (assoc-equal 'iprint-ar
                                                  (nth 2 state))))))
            (< (cdr (assoc-equal 'iprint-hard-bound
                                 (nth 2 (composed-oracle-updates state))))
               (car (dimensions 'iprint-ar
                                (cdr (assoc-equal
                                      'iprint-ar
                                      (nth 2 (composed-oracle-updates
                                              state))))))))
   :hints (("Goal"
            :use one-more-lemma
            :in-theory (enable get-global)))))

(local
 (defthm lemma-1
   (implies (equal (maximum-length
                    'iprint-ar
                    (cdr (assoc-equal 'iprint-ar
                                      (nth 2 state))))
                   (* 4
                      (car (dimensions
                            'iprint-ar
                            (cdr (assoc-equal 'iprint-ar (nth 2 state)))))))
            (equal (maximum-length
                    'iprint-ar
                    (cdr (assoc-equal 'iprint-ar
                                      (nth 2 (composed-oracle-updates
                                              state)))))
                   (* 4
                      (car (dimensions
                            'iprint-ar
                            (cdr (assoc-equal 'iprint-ar
                                              (nth 2
                                                   (composed-oracle-updates
                                                    state)))))))))
   :hints (("Goal" :in-theory (e/d (composed-oracle-updates
                                    get-global
                                    put-global)
                                   (fold-into-composed-oracle-updates))))))

; At this point I still had 7 subgoals for
; eviscerate-top-state-p-eviscerate-top when I used the theory shown just
; below, and they looked complicated.  So instead I modified that theorem with
; eviscerate-top-state-p disabled.  That produced five subgoals, four of which
; are dealt with easily below.  So I shifted my focus to proving that other
; one, which is |Subgoal-2.1'|.

(local (in-theory
        (union-theories '(eviscerate-top-state-p
                          eviscerate-top
                          put-global
                          get-global
                          global-table
                          update-global-table)
                        (set-difference-theories
                         (current-theory :here)
                         (function-theory :here)))))

(local
 (defthm put-global-preserves-eviscerate-top-state-p
   (implies (and (eviscerate-top-state-p state)
                 (not (member-equal sym ; maybe true for these too
                                    '(iprint-hard-bound
                                      iprint-fal
                                      iprint-ar))))
            (eviscerate-top-state-p
             (update-nth 2
                         (add-pair sym val (nth 2 state))
                         state)))
   :hints (("Goal" :in-theory (enable iprint-last-index)))))

(local
 (defthm eviscerate-top-state-p-composed-oracle-updates
   (implies (fmt-state-p state)
            (eviscerate-top-state-p (composed-oracle-updates state)))))

; Start proof of fmt-state-p-composed-oracle-updates

; The following two events were originally in a local encapsulate, but we
; need them later.

(defthmd fmt-state-p-iprint-oracle-updates
  (implies (fmt-state-p state)
           (fmt-state-p (iprint-oracle-updates state)))
  :hints (("Goal" :in-theory (enable state-p
                                     w
                                     iprint-last-index
                                     fmt-state-p
                                     iprint-oracle-updates))))

(defthmd fmt-state-p-brr-evisc-tuple-oracle-update
  (implies (fmt-state-p state)
           (fmt-state-p (brr-evisc-tuple-oracle-update state)))
  :hints (("Goal" :in-theory (enable state-p
                                     w
                                     iprint-last-index
                                     fmt-state-p
                                     brr-evisc-tuple-oracle-update))))

(local
 (defthm fmt-state-p-composed-oracle-updates
   (implies (fmt-state-p state)
            (fmt-state-p (composed-oracle-updates state)))
   :hints (("Goal" :in-theory (e/d (iprint-oracle-updates?
                                    composed-oracle-updates
                                    fmt-state-p-iprint-oracle-updates
                                    fmt-state-p-brr-evisc-tuple-oracle-update)
                                   (fold-into-composed-oracle-updates))))))

; Start proof of main-1

; Start proof of main-1-2 (supporting main-1)

(local
 (defun factor-fn (iprint-alist iprint-fal-new iprint-fal-old state)
   (declare (xargs :verify-guards nil ; for reasoning only
                   :stobjs state))

; This is equivalent to the conjunction of eviscerate-top-state-p and the guard
; for update-iprint-ar-fal.

   (and (eviscerate-top-state-p state)
        (iprint-alistp1 iprint-alist)
        (consp iprint-alist)
        (equal iprint-fal-old (f-get-global 'iprint-fal state))
        (iprint-falp iprint-fal-old)
        ;; (array1p 'iprint-ar (f-get-global 'iprint-ar state)) ; top
        (iprint-array-p (f-get-global 'iprint-ar state)
                        (caar iprint-alist))
        ;; (natp (f-get-global 'iprint-hard-bound state)) ; top
        ;; (< (f-get-global 'iprint-hard-bound state) ...) ; top
        ;; (<= (* 4 (1+ (f-get-global 'iprint-hard-bound state))) ...) ; top
        (iprint-falp iprint-fal-new)
; See comment about array-order in fmt-state-p.
        (equal (array-order (header 'iprint-ar
                                    (f-get-global 'iprint-ar state)))
               nil))))

(local (include-book "data-structures/array1" :dir :system))

(local
 (defthm iprint-falp-iprint-fal-name
   (implies (iprint-falp x)
            (iprint-falp (iprint-fal-name x)))
   :hints (("Goal" :in-theory (enable iprint-falp iprint-fal-name last)))))

(local
 (defthm dimensions-special-case
   (equal (dimensions name
                      (cons (list* :header :dimensions dims rest1)
                            rest2))
          dims)
   :hints (("Goal" :in-theory (enable dimensions header assoc-keyword
                                      assoc-equal)))))

(local
 (defthm get-global-rollover-iprint-ar
   (implies (not (member-equal sym '(iprint-fal iprint-ar)))
            (equal (assoc-equal
                    sym
                    (nth 2 (rollover-iprint-ar iprint-alist last-index state)))
                   (assoc-equal sym (nth 2 state))))
   :hints (("Goal" :in-theory (enable rollover-iprint-ar init-iprint-fal)))))

(local
 (defthm maximum-length-rollover-iprint-ar
   (equal (maximum-length 'iprint-ar
                          (cdr (assoc-equal
                                'iprint-ar
                                (nth 2 (rollover-iprint-ar
                                        iprint-alist last-index state)))))
          (let ((new-max-len (* 4 (1+ (max (iprint-hard-bound state)
                                           last-index)))))
            (if (< *maximum-positive-32-bit-integer*
                   new-max-len)
                (maximum-length 'iprint-ar
                                (cdr (assoc-equal 'iprint-ar (nth 2 state))))
              new-max-len)))
   :hints
   (("Goal"
     :in-theory (enable rollover-iprint-ar init-iprint-fal maximum-length
                        header compress1 max assoc-equal assoc-keyword
                        iprint-hard-bound)))))

(local
 (defthm rollover-iprint-ar-preserves-iprint-falp
   (implies (iprint-falp (cdr (assoc-equal 'iprint-fal (nth 2 state))))
            (iprint-falp
             (cdr
              (assoc-equal 'iprint-fal
                           (nth 2
                                (rollover-iprint-ar
                                 iprint-alist last-index state))))))
   :hints (("Goal" :in-theory (enable rollover-iprint-ar
                                      iprint-falp
                                      init-iprint-fal)))))

(local
 (defthm iprint-array-p-compress1
   (implies (equal (array-order (header name ar)) nil)
            (equal (compress1 name ar)
                   ar))
   :hints (("Goal" :in-theory (enable compress1)))))

(local
 (defthm array-order-hack
   (equal (array-order
           (header name
                   (CONS (LIST* :HEADER :DIMENSIONS dims
                                :MAXIMUM-LENGTH len
                                :DEFAULT def
                                '(:NAME IPRINT-AR :ORDER :NONE))
                         rest)))
          nil)
   :hints (("Goal" :in-theory (enable header array-order assoc-equal
                                      assoc-keyword)))))

(local
 (defthm iprint-array-p-cons-header
   (iprint-array-p (cons (cons :header h) rest) max)
   :hints (("Goal" :in-theory (enable iprint-array-p)))))

(local
 (defthm rollover-iprint-ar-iprint-array-p
   (implies (iprint-array-p (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                            (+ 1 (iprint-last-index state)))
            (iprint-array-p
             (cdr
              (assoc-equal 'iprint-ar
                           (nth 2
                                (rollover-iprint-ar
                                 iprint-alist
                                 (car (car iprint-alist))
                                 state))))
             (+ 1
                (iprint-last-index
                 (rollover-iprint-ar iprint-alist (car (car iprint-alist))
                                     state)))))
   :otf-flg t
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (enable rollover-iprint-ar init-iprint-fal
                        iprint-last-index iprint-last-index*)))))

(local
 (defthm iprint-last-index-rollover-iprint-ar
   (equal (iprint-last-index (rollover-iprint-ar
                              iprint-alist (caar iprint-alist) state))
          (if (<= (* 4 (1+ (max (iprint-hard-bound state) (caar iprint-alist))))
                  *maximum-positive-32-bit-integer*)
              0
            (iprint-last-index state)))
   :hints (("Goal" :in-theory (enable aref1 assoc-equal acons
                                      iprint-last-index
                                      iprint-last-index*
                                      rollover-iprint-ar)))))
(local
 (defthm rollover-iprint-ar-preserves-array1p
   (let ((iprint-ar (cdr (assoc-equal 'iprint-ar (nth 2 state)))))
     (implies (and (array1p 'iprint-ar iprint-ar)
                   (natp (caar iprint-alist))
                   (natp (iprint-hard-bound state))
                   (iprint-alistp iprint-alist)
                   (iprint-array-p iprint-ar (caar iprint-alist)))
              (array1p 'iprint-ar
                       (cdr (assoc-equal 'iprint-ar
                                         (nth 2 (rollover-iprint-ar
                                                 iprint-alist
                                                 (caar iprint-alist)
                                                 state)))))))
   :hints
   (("Goal"
     :in-theory (enable rollover-iprint-ar array1p keyword-value-listp
                        assoc-keyword assoc-equal max iprint-alistp
                        bounded-integer-alistp length len alistp acons)))))

(local
 (defthm iprint-alistp1-forward-to-natp-caar
   (implies (and (iprint-alistp1 x)
                 (consp x))
            (natp (caar x)))
   :hints (("Goal" :in-theory (enable iprint-alistp1)))
   :rule-classes :forward-chaining))

(local
 (defthm rollover-iprint-ar-preserves-consp-iprint-ar
   (implies (consp (cdr (assoc-equal 'iprint-ar (nth 2 state))))
            (consp (cdr (assoc-equal 'iprint-ar
                                     (nth 2 (rollover-iprint-ar
                                             iprint-alist n state))))))
   :hints (("Goal" :in-theory (enable rollover-iprint-ar)))))

(local
 (defthm dimensions-after-rollover-iprint-ar
   (equal (dimensions
           'iprint-ar
           (cdr (assoc-equal
                 'iprint-ar
                 (nth 2
                      (rollover-iprint-ar iprint-alist (car (car iprint-alist))
                                          state)))))
          (let* ((new-dim (1+ (max (iprint-hard-bound state)
                                   (car (car iprint-alist)))))
                 (new-max-len (* 4 new-dim)))
            (if (< *maximum-positive-32-bit-integer* new-max-len)
                (dimensions 'iprint-ar
                            (cdr (assoc-equal 'iprint-ar (nth 2 state))))
              (list new-dim))))
   :hints
   (("Goal"
     :in-theory (enable rollover-iprint-ar dimensions header compress1
                        assoc-keyword assoc-equal)))))

(local
 (defthm rollover-iprint-ar-iprint-array-p-alt
   (implies (and (iprint-array-p (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                                 (+ 1 (iprint-last-index state)))
                 (equal state2
                        (nth 2
                             (rollover-iprint-ar iprint-alist
                                                 (car (car iprint-alist))
                                                 state)))
                 (case-split (equal max (+ 1 (iprint-last-index state)))))
            (iprint-array-p (cdr (assoc-equal 'iprint-ar state2))
                            max))
   :otf-flg t
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (enable rollover-iprint-ar init-iprint-fal
                        iprint-last-index iprint-last-index*)))))

(local
 (defthm rollover-iprint-ar-iprint-array-p-max-1
   (implies
    (and (<= (+ 4 (* 4 (car (car iprint-alist))))
             2147483647)
         (< (cdr (assoc-equal 'iprint-hard-bound
                              (nth 2 state)))
            (car (car iprint-alist))))
    (iprint-array-p
     (cdr (assoc-equal
           'iprint-ar
           (nth 2
                (rollover-iprint-ar iprint-alist (car (car iprint-alist))
                                    state))))
     1))
   :hints (("Goal" :in-theory (enable rollover-iprint-ar iprint-hard-bound
                                      max)))))

; Start proof of array1p-of-aset1-lst

(local
 (defthm header-cons
   (implies (natp n)
            (equal (array-order (assoc-equal :header (cons (cons n val) ar)))
                   (array-order (assoc-equal :header ar))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(local
 (defthm header-aset1-order-nil
   (implies (and (natp n)
                 (equal (array-order (assoc-equal :header ar))
                        nil))
            (equal (assoc-equal :header (aset1 name ar n val))
                   (assoc-equal :header ar)))
   :hints (("Goal" :in-theory (enable aset1 assoc-equal header)))))

; Start proof of dimensions-aset1 (towards array1p-of-aset1-lst)

; This is needed after the encapsulate, so we make it non-local here.
(defthm header-compress1-order-nil
  (implies (equal (array-order (assoc-equal :header ar))
                  nil)
           (equal (assoc-equal :header (compress1 name ar))
                  (assoc-equal :header ar)))
  :hints (("Goal" :in-theory (enable assoc-equal header compress1))))

(local
 (defthm dimensions-aset1
   (implies (and (natp n)
                 (equal (array-order (assoc-equal :header ar))
                        nil))
            (equal (assoc-keyword
                    :dimensions
                    (cdr (assoc-equal :header (aset1 name ar n val))))
                   (assoc-keyword :dimensions (cdr (assoc-equal :header ar)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable aset1 assoc-equal header)))))

(local
 (defthm array1p-of-aset1-lst
   (implies (and (iprint-alistp iprint-alist)
                 (< (car (car iprint-alist))
                    (car (dimensions name ar)))
                 (array1p name ar)
                 (equal (array-order (assoc-equal :header ar))
                        nil))
            (array1p name (aset1-lst name iprint-alist ar)))
   :hints (("Goal"
            :in-theory
            (enable aset1-lst iprint-alistp iprint-alistp1 alistp
                    dimensions header maximum-length assoc-keyword
                    assoc-equal)))))

(local
 (defthm iprint-falp-update-iprint-fal-rec
   (implies
    (and (iprint-falp iprint-fal-old)
         (iprint-falp iprint-fal-new))
    (iprint-falp (update-iprint-fal-rec iprint-fal-new iprint-fal-old)))
   :hints (("Goal" :in-theory (enable update-iprint-fal-rec
                                      iprint-falp
                                      hons-acons)))))

; Continuing toward main-1-2:

(local
 (defthm array1p-of-aset1-lst-acons
   (implies (and (iprint-alistp iprint-alist)
                 (< (car (car iprint-alist))
                    (car (dimensions name ar)))
                 (array1p name ar)
                 (equal (array-order (assoc-equal :header ar))
                        nil))
            (array1p name
                     (aset1-lst name
                                (acons 0 (car (car iprint-alist)) iprint-alist)
                                ar)))
   :hints (("Goal"
            :expand ((aset1-lst name
                                (cons (cons 0 (car (car iprint-alist)))
                                      iprint-alist)
                                ar))
            :in-theory (enable acons)))))

(local
 (defthm main-1-2-1-1
   (implies (and (iprint-alistp1 iprint-alist)
                 (not (array-order (header 'iprint-ar iprint-ar))))
            (equal (aref1 'iprint-ar
                          (aset1-lst 'iprint-ar iprint-alist iprint-ar)
                          0)
                   (aref1 'iprint-ar
                          iprint-ar
                          0)))
   :hints (("Goal" :in-theory (enable iprint-alistp1 aset1-lst aset1 aref1
                                      assoc-equal)))))

(local
 (defthm main-1-2-1
   (implies (and (iprint-alistp1 iprint-alist)
                 (atom x)
                 (not (array-order (header 'iprint-ar iprint-ar))))
            (equal (aref1 'iprint-ar
                          (aset1-lst 'iprint-ar
                                     (acons 0 x iprint-alist)
                                     iprint-ar)
                          0)
                   x))
   :hints (("Goal" :in-theory (enable  aset1-lst aset1 acons aref1
                                       assoc-equal)))))

(local
 (defthm main-1-2-2-1
   (implies (and (iprint-alistp1 iprint-alist)
                 (atom x)
                 (not (array-order (header 'iprint-ar iprint-ar))))
            (equal (assoc-equal :header (aset1-lst 'iprint-ar
                                                   iprint-alist
                                                   iprint-ar))
                   (assoc-equal :header iprint-ar)))
   :hints (("Goal"
            :in-theory (enable aset1-lst aset1 acons aref1 assoc-equal
                               header iprint-alistp1)))))

(local
 (defthm main-1-2-2
   (implies (and (iprint-alistp1 iprint-alist)
                 (atom x)
                 (not (array-order (header 'iprint-ar iprint-ar))))
            (equal (assoc-equal :header (aset1-lst 'iprint-ar
                                                   (acons 0 x iprint-alist)
                                                   iprint-ar))
                   (assoc-equal :header iprint-ar)))
   :hints (("Goal"
            :in-theory (enable aset1-lst acons assoc-equal aset1)))))

(local
 (defthm iprint-array-p-aset1-lst
   (implies (and (iprint-array-p ar max)
                 (iprint-alistp1 iprint-alist)
                 (< (caar iprint-alist) max)
                 (not (array-order (header name ar))))
            (iprint-array-p (aset1-lst name iprint-alist ar)
                            max))
   :hints (("Goal" :in-theory (enable aset1-lst aset1 iprint-alistp1
                                      iprint-array-p)))))
(local
 (defthm main-1-2-3
   (implies (and (iprint-array-p ar max)
                 (iprint-alistp1 iprint-alist)
                 (< (caar iprint-alist) max)
                 (not (array-order (header 'iprint-ar ar))))
            (iprint-array-p (aset1-lst name
                                       (acons 0 x iprint-alist)
                                       ar)
                            max))
   :hints (("Goal"
            :expand ((aset1-lst name
                                (cons (cons 0 x) iprint-alist)
                                ar))
            :in-theory (enable acons aset1 header iprint-array-p)))))

(local
 (defthm main-1-2
   (implies (factor-fn iprint-alist iprint-fal-new iprint-fal-old state)
            (eviscerate-top-state-p
             (update-iprint-ar-fal iprint-alist iprint-fal-new iprint-fal-old
                                   state)))
   :otf-flg t
   :hints (("Goal"
            :restrict
            ((rollover-iprint-ar-iprint-array-p-alt
              ((state state) (iprint-alist iprint-alist))))
            :do-not-induct t
            :in-theory (enable update-iprint-ar-fal iprint-hard-bound
                               update-iprint-fal
                               iprint-alistp max header iprint-last-index
                               iprint-last-index* dimensions
                               maximum-length)))))

(local
 (defthm iprint-alistp1-mv-nth-1-eviscerate-case-split
   (let ((result
          (mv-nth
           1
           (eviscerate x print-level print-length alist evisc-table hiding-cars
                       iprint-alist iprint-fal-new iprint-fal-old eager-p))))
     (implies (and (case-split (iprint-alistp iprint-alist))
                   (not (eq result t))
                   (not (natp result)))
              (iprint-alistp1 result)))))

(local
 (defthm main-1-1-1
   (implies (fmt-state-p state)
            (not (array-order (header 'iprint-ar
                                      (cdr (assoc-equal 'iprint-ar
                                                        (nth 2 state)))))))
   :hints (("Goal" :in-theory (enable fmt-state-p)))))

(local
 (defthm main-1-1-2-1
   (implies (fmt-state-p state)
            (iprint-array-p (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                            (1+ (iprint-last-index state))))))

(local
 (defthm main-1-1-2-2
   (let ((evisc (eviscerate x print-level
                            print-length alist evisc-table
                            hiding-cars (iprint-last-index state)
                            nil
                            (cdr (assoc-equal 'iprint-fal (nth 2 state)))
                            (iprint-eager-p (cdr (assoc-equal 'iprint-fal
                                                              (nth 2 state)))))))
     (implies (and (fmt-state-p state)
                   (iprint-enabledp state)
                   (consp (mv-nth 1 evisc)))
              (<= (+ 1 (iprint-last-index state))
                  (car (car (mv-nth 1 evisc))))))
   :hints (("Goal"
            :use ((:instance eviscerate-adds-bigger-index-main
                             (iprint-last-index (iprint-last-index state))
                             (iprint-fal-new nil)
                             (iprint-fal-old
                              (cdr (assoc-equal 'iprint-fal (nth 2 state))))
                             (eager-p (iprint-eager-p
                                       (cdr (assoc-equal 'iprint-fal
                                                         (nth 2 state)))))))
            :in-theory (enable eviscerate)))
   :rule-classes :linear))

(local
 (defthm main-1-1-2
   (let* ((iprint-fal (cdr (assoc-equal 'iprint-fal (nth 2 state))))
          (evisc (eviscerate
                  x print-level print-length alist evisc-table hiding-cars
                  (iprint-last-index state)
                  nil
                  iprint-fal
                  (iprint-eager-p iprint-fal))))
     (implies (and (fmt-state-p state)
                   (iprint-enabledp state)
                   (consp (mv-nth 1 evisc)))
              (iprint-array-p
               (cdr (assoc-equal 'iprint-ar (nth 2 state)))
               (car (car (mv-nth 1 evisc))))))))

(local
 (defthm main-1-1
   (let* ((iprint-fal (cdr (assoc-equal 'iprint-fal (nth 2 state))))
          (evisc (eviscerate
                  x print-level print-length alist evisc-table hiding-cars
                  (iprint-last-index state)
                  nil
                  iprint-fal
                  (iprint-eager-p iprint-fal)))
          (iprint-alist (mv-nth 1 evisc))
          (iprint-fal-new (mv-nth 2 evisc)))
     (implies (and (fmt-state-p state)
                   (iprint-enabledp state)
                   (consp (mv-nth 1 evisc)))
              (factor-fn iprint-alist iprint-fal-new iprint-fal state)))))

(local
 (defthm main-1
   (let* ((iprint-fal (cdr (assoc-equal 'iprint-fal (nth 2 state))))
          (evisc (eviscerate
                  x print-level print-length alist evisc-table hiding-cars
                  (iprint-last-index state)
                  nil
                  iprint-fal
                  (iprint-eager-p iprint-fal))))
     (implies (and (fmt-state-p state)
                   (iprint-enabledp state)
                   (consp (mv-nth 1 evisc)))
              (eviscerate-top-state-p
               (update-iprint-ar-fal (mv-nth 1 evisc)
                                     (mv-nth 2 evisc)
                                     iprint-fal
                                     state))))))

(local
 (defthm |Subgoal-2.1'|
   (implies
    (and
     (fmt-state-p state)
     (iprint-enabledp (composed-oracle-updates state))
     (consp
      (mv-nth
       1
       (eviscerate
        x print-level print-length
        alist evisc-table hiding-cars
        (iprint-last-index (composed-oracle-updates state))
        nil
        (cdr (assoc-equal 'iprint-fal
                          (nth 2 (composed-oracle-updates state))))
        (iprint-eager-p
         (cdr (assoc-equal 'iprint-fal
                           (nth 2
                                (composed-oracle-updates state)))))))))
    (eviscerate-top-state-p
     (update-iprint-ar-fal
      (mv-nth
       1
       (eviscerate
        x print-level print-length
        alist evisc-table hiding-cars
        (iprint-last-index (composed-oracle-updates state))
        nil
        (cdr (assoc-equal 'iprint-fal
                          (nth 2 (composed-oracle-updates state))))
        (iprint-eager-p
         (cdr (assoc-equal 'iprint-fal
                           (nth 2 (composed-oracle-updates state)))))))
      (mv-nth
       2
       (eviscerate
        x print-level print-length
        alist evisc-table hiding-cars
        (iprint-last-index (composed-oracle-updates state))
        nil
        (cdr (assoc-equal 'iprint-fal
                          (nth 2 (composed-oracle-updates state))))
        (iprint-eager-p
         (cdr (assoc-equal 'iprint-fal
                           (nth 2 (composed-oracle-updates state)))))))
      (cdr (assoc-equal 'iprint-fal
                        (nth 2 (composed-oracle-updates state))))
      (composed-oracle-updates state))))))

(defthm eviscerate-top-state-p-eviscerate-top
  (implies (fmt-state-p state)
           (eviscerate-top-state-p
            (mv-nth 1
                    (eviscerate-top x print-level print-length
                                    alist evisc-table hiding-cars state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory
           (union-theories '(eviscerate-top put-global get-global global-table
                                            update-global-table)
                           (set-difference-theories
                            (current-theory :here)
                            (function-theory :here))))))
)

; Start proof of array-order-iprint-ar-eviscerate-top

(defthm array-order-iprint-ar-iprint-oracle-updates?
  (implies
   (fmt-state-p state)
   (equal (array-order
           (assoc-equal
            :header
            (cdr (assoc-equal
                  'iprint-ar
                  (nth 2 (iprint-oracle-updates? state))))))
          nil))
  :hints (("Goal" :in-theory (e/d (iprint-oracle-updates?
                                   iprint-oracle-updates
                                   array-order
                                   fmt-state-p)
                                  (array1p all-boundp member-equal nfix)))))

; Start proof of array-order-iprint-ar-update-iprint-ar-fal (toward
; array-order-iprint-ar-eviscerate-top)

(defthm array-order-iprint-ar-rollover-iprint-ar
  (implies
   (fmt-state-p state)
   (equal (array-order
           (assoc-equal
            :header
            (cdr (assoc-equal
                  'iprint-ar
                  (nth 2 (rollover-iprint-ar iprint-alist last-index
                                             state))))))
          nil))
  :hints (("Goal" :in-theory (e/d (rollover-iprint-ar
                                   array-order
                                   fmt-state-p)
                                  (init-iprint-fal
                                   iprint-hard-bound
                                   array1p all-boundp member-equal nfix)))))

(local
 (defthm array-order-iprint-ar-update-iprint-fal-1
   (implies
    (fmt-state-p state)
    (equal (array-order
            (assoc-equal
             :header
             (cdr (assoc-equal
                   'iprint-ar
                   (nth 2 (f-put-global 'iprint-fal
                                        (update-iprint-fal-rec
                                         iprint-fal-new
                                         (f-get-global 'iprint-fal state))
                                        state))))))
           nil))
   :hints (("Goal" :in-theory (enable fmt-state-p)))))

(defthm array-order-iprint-ar-fal-1

; This was originally a lemma about update-iprint-fal, but since that function
; is untouchable we prove this lemma about its expansion.

  (implies
   (fmt-state-p state)
   (equal (array-order
           (assoc-equal
            :header
            (cdr (assoc-equal
                  'iprint-ar
                  (nth 2 (f-put-global 'iprint-fal
                                       (update-iprint-fal-rec
                                        iprint-fal-new
                                        (f-get-global 'iprint-fal state))
                                       state))))))
          nil))
  :hints (("Goal" :in-theory (enable fmt-state-p))))

(defthm array-order-iprint-ar-update-iprint-fal-2

; The lemma array-order-iprint-ar-fal-1 above isn't sufficient for the proof of
; array-order-iprint-ar-update-iprint-ar-fal (see also comment about
; array-order-iprint-ar-fal-1 above), but this lemma makes up for that.

  (implies
   (fmt-state-p state)
   (equal (array-order
           (assoc-equal
            :header
            (aset1 'iprint-ar
                   (cdr (assoc-equal 'iprint-ar (nth 2 state)))
                   0
                   (car (car iprint-alist)))))
          nil))
  :hints (("Goal" :in-theory (enable fmt-state-p aset1))))

(defthm array-order-aset1
  (implies (and (natp n)
                (equal (array-order (assoc-equal :header ar))
                       nil))
           (equal (array-order (assoc-equal :header (aset1 name ar n val)))
                  nil))
  :hints (("Goal" :in-theory (enable aset1 array-order))))

(defthm array-order-aset1-lst
  (implies (and (equal (array-order (assoc-equal :header ar))
                       nil)
                (iprint-alistp alist))
           (equal (array-order (assoc-equal :header (aset1-lst name alist ar)))
                  nil))
  :hints (("Goal" :in-theory (enable aset1-lst))))

(defthm array-order-iprint-ar-update-iprint-ar-fal
  (implies
   (and (fmt-state-p state)
        (force (iprint-alistp1 iprint-alist))
        (force (consp iprint-alist)))
   (equal (array-order
           (assoc-equal
            :header
            (cdr (assoc-equal
                  'iprint-ar
                  (nth 2 (update-iprint-ar-fal iprint-alist iprint-fal-new
                                               iprint-fal-old state))))))
          nil))
  :hints (("Goal"
           :in-theory
           (e/d (update-iprint-ar-fal aset1-lst)
                (rollover-iprint-ar array-order iprint-hard-bound array1p
                                    all-boundp member-equal nfix)))))

(defthm fmt-state-p-iprint-oracle-updates?
  (implies (fmt-state-p state)
           (fmt-state-p (iprint-oracle-updates? state)))
  :hints (("Goal" :in-theory (e/d (fmt-state-p-iprint-oracle-updates
                                   iprint-oracle-updates?)
                                  (iprint-oracle-updates)))))

(encapsulate

  ()

  (local (include-book "system/eviscerate-top-support" :dir :system))

  (defthm iprint-alistp1-mv-nth-1-eviscerate
    (let ((result
           (mv-nth
            1
            (eviscerate x print-level print-length alist evisc-table hiding-cars
                        iprint-alist iprint-fal-new iprint-fal-old eager-p))))
      (implies (and (iprint-alistp iprint-alist)
                    (not (eq result t))
                    (not (natp result)))
               (iprint-alistp1 result)))))

(defthm array-order-iprint-ar-eviscerate-top
  (implies
   (fmt-state-p state)
   (equal (array-order
           (header
            'iprint-ar
            (cdr (assoc-equal
                  'iprint-ar
                  (nth 2
                       (mv-nth 1
                               (eviscerate-top x print-level print-length alist
                                               evisc-table hiding-cars
                                               state)))))))
          nil))
  :hints (("Goal" :in-theory (e/d (eviscerate-top
                                   fmt-state-p-iprint-oracle-updates
                                   fmt-state-p-brr-evisc-tuple-oracle-update)
                                  (eviscerate
                                   update-iprint-ar-fal
                                   brr-evisc-tuple-oracle-update
                                   iprint-oracle-updates?)))))

(defthm fmt-state-p-mv-nth-1-eviscerate-top
  (implies (fmt-state-p state)
           (fmt-state-p
            (mv-nth 1
                    (eviscerate-top x print-level print-length alist
                                    evisc-table hiding-cars state))))
  :hints (("Goal"
           :in-theory
           (union-theories '(fmt-state-p state-p w get-global global-table)
                           (set-difference-theories
                            (current-theory :here)
                            (function-theory :here)))))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((mv-nth 1
                           (eviscerate-top x print-level print-length alist
                                           evisc-table hiding-cars state))))))

(defthm fmt-state-p-left-pad-with-blanks
  (implies
   (and (force (fmt-state-p state))
        (force (open-output-channel-p1 channel :character state)))
   (fmt-state-p (mv-nth 1 (left-pad-with-blanks n width col channel state))))
  :hints (("goal" :in-theory (enable fmt-state-p))))

(defthm open-output-channel-p1-left-pad-with-blanks
  (implies (open-output-channel-p1 chan1 typ state)
           (open-output-channel-p1 chan1 typ
                                   (mv-nth 1 (left-pad-with-blanks n width col
                                                                   channel
                                                                   state))))
  :hints (("Goal" :in-theory (enable left-pad-with-blanks))))

(defthm-od left-pad-with-blanks
  :mv-nth 1)

(defmacro defthm-flag-fmt0-theory ()
  '(disable splat
            fmt0* fmt0&v spell-number fmt-tilde-s fmt-tilde-cap-s fmt0
            punctp
            characterp-fmt-char-type-prescription-forced
            characterp-fmt-char
            find-alternative-skip
            find-alternative-stop
            natp-find-alternative-stop
            find-alternative-stop
            flsz1-bound
            cancel_times-equal-correct
            cancel_plus-equal-correct
            fold-consts-in-+
            rationalp-implies-acl2-numberp
            assoc-equal
            natp-find-alternative-skip
            mv-nth
            fmt-var
            spaces1
            standard-evisc-tuplep
            scan-past-whitespace
            princ$
            fmt-state-p
            min-fixnat$inline
            min
            fix
            member-equal
            integer-range-p unsigned-byte-p min
            left-pad-with-blanks
            len msgp length keywordp
            ))

(defthm-flag-fmt0

  (defthm fmt-state-p-fmt0*
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2 (mv-nth 1
                                   (fmt0* str0 str1 str2 str3 lst alist col
                                          channel state evisc-tuple clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((fmt0* str0 str1 str2 str3 lst alist col channel state
                            evisc-tuple clk))))
    :flag fmt0*)

  (defthm fmt-state-p-fmt0&v
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2
                    (mv-nth 1
                            (fmt0&v flg lst punct col channel state evisc-tuple
                                    clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((fmt0&v flg lst punct col channel state evisc-tuple
                             clk))))
    :flag fmt0&v)

  (defthm fmt-state-p-spell-number
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2
                    (mv-nth 1
                            (spell-number n cap col channel state evisc-tuple
                                          clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((spell-number n cap col channel state evisc-tuple clk))))
    :flag spell-number)

  (defthm fmt-state-p-fmt-tilde-s
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2
                    (mv-nth
                     1
                     (fmt-tilde-s s col channel state clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((fmt-tilde-s s col channel state clk))))
    :flag fmt-tilde-s)

  (defthm fmt-state-p-fmt-tilde-cap-s
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2
                    (mv-nth
                     1
                     (fmt-tilde-cap-s s col channel state clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((fmt-tilde-cap-s s col channel state clk))))
    :flag fmt-tilde-cap-s)

  (defthm fmt-state-p-fmt0
    (implies (and (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (let ((state2
                    (mv-nth
                     1
                     (fmt0 s alist i maximum col pn channel state
                           evisc-tuple clk))))
               (and (fmt-state-p state2)
                    (open-output-channel-p1 channel :character state2))))
    :rule-classes (:rewrite
                   (:forward-chaining
                    :trigger-terms
                    ((fmt0 s alist i maximum col pn channel state
                           evisc-tuple clk))))
    :flag fmt0)
  :hints (("Goal"
           :expand
           ((:free (str0 str1 str2 str3 lst alist col channel state)
                   (fmt0* str0 str1 str2 str3 lst alist col channel state
                          evisc-tuple clk))
            (:free (flg lst punct col channel state evisc-tuple)
                   (fmt0&v flg lst punct col channel state evisc-tuple clk))
            (:free (n cap col channel state evisc-tuple)
                   (spell-number n cap col channel state evisc-tuple clk))
            (:free (col channel state)
                   (fmt-tilde-s s col channel state clk))
            (:free (col channel state)
                   (fmt-tilde-cap-s s col channel state clk))
            (:free (alist i maximum col pn channel state evisc-tuple)
                   (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk)))
           :in-theory (defthm-flag-fmt0-theory))))

(defthm-flag-od (fmt0 fmt0* fmt0&v spell-number fmt-tilde-s fmt-tilde-cap-s)
  :mv-nth 1
  :hints (("Goal"
           :expand
           ((:free (str0 str1 str2 str3 lst alist col channel state)
                   (fmt0* str0 str1 str2 str3 lst alist col channel state
                          evisc-tuple clk))
            (:free (flg lst punct col channel state evisc-tuple)
                   (fmt0&v flg lst punct col channel state evisc-tuple clk))
            (:free (n cap col channel state evisc-tuple)
                   (spell-number n cap col channel state evisc-tuple clk))
            (:free (col channel state)
                   (fmt-tilde-s s col channel state clk))
            (:free (col channel state)
                   (fmt-tilde-cap-s s col channel state clk))
            (:free (alist i maximum col pn channel state evisc-tuple)
                   (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk)))
           :in-theory (union-theories (ruleset 'open-output-channel-diff)
                                      (defthm-flag-fmt0-theory)))))

(defthm mv-nth-0
; So that (verify-guards fmt0 ...) can take advantage of rules above about (car
; ...).
  (equal (mv-nth 0 x)
         (car x)))

(defthm natp-round-to-small-t
  (natp (round-to-small t x))
  :hints (("Goal" :in-theory (enable round-to-small)))
  :rule-classes :type-prescription)

(defthm integerp-round-to-small-nil
  (integerp (round-to-small nil x))
  :hints (("Goal" :in-theory (enable round-to-small)))
  :rule-classes :type-prescription)

(defthm natp-flsz
  (implies (and (force (natp j))
                (force (natp maximum)))
           (natp (flsz1 x print-base print-radix j maximum state eviscp)))
  :hints (("Goal" :in-theory (enable flsz1)))
  :rule-classes :type-prescription)

(defthm natp-car-left-pad-with-blanks
  (implies (and (force (natp width))
                (force (natp col)))
           (natp (car (left-pad-with-blanks n width col channel state))))
  :hints (("Goal" :in-theory (enable flsz1)))
  :rule-classes :type-prescription)

(defthm-flag-fmt0

  (defthm natp-fmt0*
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (fmt0* str0 str1 str2 str3 lst alist col channel state
                           evisc-tuple clk))))
    :rule-classes :type-prescription
    :flag fmt0*)

  (defthm natp-fmt0&v
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (fmt0&v flg lst punct col channel state evisc-tuple
                            clk))))
    :rule-classes :type-prescription
    :flag fmt0&v)

  (defthm natp-spell-number
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (spell-number n cap col channel state evisc-tuple
                                  clk))))
    :rule-classes :type-prescription
    :flag spell-number)

  (defthm natp-fmt-tilde-s
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (fmt-tilde-s s col channel state clk))))
    :rule-classes :type-prescription
    :flag fmt-tilde-s)

  (defthm natp-fmt-tilde-cap-s
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (fmt-tilde-cap-s s col channel state clk))))
    :rule-classes :type-prescription
    :flag fmt-tilde-cap-s)

  (defthm natp-fmt0
    (implies (force (and (natp col)
                         (fmt-state-p state)
                         (open-output-channel-p1 channel :character state)))
             (natp (car
                    (fmt0 s alist i maximum col pn channel state
                          evisc-tuple clk))))
    :rule-classes :type-prescription
    :flag fmt0)

  :hints (("Goal"
           :expand
           ((:free (str0 str1 str2 str3 lst alist col channel state)
                   (fmt0* str0 str1 str2 str3 lst alist col channel state
                          evisc-tuple clk))
            (:free (flg lst punct col channel state evisc-tuple)
                   (fmt0&v flg lst punct col channel state evisc-tuple clk))
            (:free (n cap col channel state evisc-tuple)
                   (spell-number n cap col channel state evisc-tuple clk))
            (:free (col channel state)
                   (fmt-tilde-s s col channel state clk))
            (:free (col channel state)
                   (fmt-tilde-cap-s s col channel state clk))
            (:free (alist i maximum col pn channel state evisc-tuple)
                   (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk)))
           :in-theory (defthm-flag-fmt0-theory)))
  )

(defthm unsigned-byte-p-29-forward
  (implies (unsigned-byte-p 29 x)
           (and (natp x)
                (<= x (fixnum-bound))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)))
  :rule-classes :forward-chaining)

(defthm-flag-fmt0

  (defthm fmt0*-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (fmt0* str0 str1 str2 str3 lst alist col channel state
                         evisc-tuple clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag fmt0*)

  (defthm fmt0&v-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (fmt0&v flg lst punct col channel state evisc-tuple clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag fmt0&v)

  (defthm spell-number-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (spell-number n cap col channel state evisc-tuple
                                clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag spell-number)

  (defthm fmt-tilde-s-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (fmt-tilde-s s col channel state clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag fmt-tilde-s)

  (defthm fmt-tilde-cap-s-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (fmt-tilde-cap-s s col channel state clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag fmt-tilde-cap-s)

  (defthm fmt0-bound
    (implies (and (force (natp col))
                  (fmt-state-p state)
                  (open-output-channel-p1 channel :character state))
             (<= (car
                  (fmt0 s alist i maximum col pn channel state
                        evisc-tuple clk))
                 (fixnum-bound)))
    :rule-classes :linear
    :flag fmt0)

  :hints (("Goal"
           :expand
           ((:free (str0 str1 str2 str3 lst alist col channel state)
                   (fmt0* str0 str1 str2 str3 lst alist col channel state
                          evisc-tuple clk))
            (:free (flg lst punct col channel state evisc-tuple)
                   (fmt0&v flg lst punct col channel state evisc-tuple clk))
            (:free (n cap col channel state evisc-tuple)
                   (spell-number n cap col channel state evisc-tuple clk))
            (:free (col channel state)
                   (fmt-tilde-s s col channel state clk))
            (:free (col channel state)
                   (fmt-tilde-cap-s s col channel state clk))
            (:free (alist i maximum col pn channel state evisc-tuple)
                   (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk)))
           :in-theory (defthm-flag-fmt0-theory)))
  )

(defthm nth-character-listp
  (implies (character-listp x)
           (or (equal (nth n x) nil)
               (characterp (nth n x))))
  :hints (("Goal" :in-theory (e/d (nth)
                                  (characterp-nth-with-forcing))))
  :rule-classes :type-prescription)

(defthm nth-coerce-s-list
  (implies (stringp s)
           (or (equal (nth n (coerce s 'list)) nil)
               (characterp (nth n (coerce s 'list)))))
  :hints (("Goal" :in-theory (disable characterp-nth-with-forcing)))
  :rule-classes :type-prescription)

(defthm natp-left-pad-with-blanks
  (implies (and (force (natp col))
                (force (natp width)))
           (natp (car (left-pad-with-blanks n width col channel state))))
  :rule-classes :type-prescription)

(defthm left-pad-with-blanks-bound
  (<= (car (left-pad-with-blanks n width col channel state))
      (fixnum-bound))
  :rule-classes :linear)

(encapsulate
  ()

; We change the theory here, instead of in :hints, so that it applies to the
; forcing rounds.  We started developing this theory before introducing the
; macro, defthm-flag-fmt0-theory.  We don't bother updating to use that macro,
; though there is a lot of overlap.

  (local (in-theory (e/d
                     (unsigned-byte-p signed-byte-p)
                     (splat
                      fmt0* fmt0&v spell-number fmt-tilde-s fmt-tilde-cap-s fmt0
                      characterp-fmt-char
                      find-alternative-skip
                      find-alternative-stop
                      natp-find-alternative-stop
                      find-alternative-stop
                      cancel_times-equal-correct
                      cancel_plus-equal-correct
                      fold-consts-in-+
                      rationalp-implies-acl2-numberp
                      assoc-equal
                      natp-find-alternative-skip
                      mv-nth
                      fmt-var
                      spaces1
                      standard-evisc-tuplep
                      scan-past-whitespace
                      princ$
                      fmt-state-p
                      min-fixnat$inline
                      min
                      member-equal
                      print-base-p
                      atom
                      left-pad-with-blanks
                      punctp
                      true-listp
                      nth-character-listp
                      character-listp
                      (:e tau-system) ; saves about 11 seconds
; Found with accumulated-persistence:
                      fixnat-cdr-assoc-symbol-to-fixnat-alistp
                      symbol-to-fixnat-alistp
                      all-boundp
                      sums-of-smalls
                      unsigned-byte-p-implies-signed-byte-p
                      ))))

  (verify-guards fmt0
    :otf-flg t
    :hints
    (("Goal" :do-not-induct t))))

(in-theory (disable fmt0))

(in-theory (enable unsigned-byte-p signed-byte-p))

(verify-guards fmt1
  :hints (("Goal" :in-theory (disable mv-nth))))

(verify-termination fmt) ; and guards

(verify-termination fms) ; and guards

(defthm fmt-state-p-put-global
  (implies (and (fmt-state-p state)
                (symbolp sym)
                (not (equal sym 'timer-alist))
                (not (equal sym 'current-acl2-world))
                (not (equal sym 'fmt-hard-right-margin))
                (not (equal sym 'fmt-soft-right-margin))
                (not (equal sym 'print-base))
                (not (equal sym 'ppr-flat-right-margin))
                (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar))
                (not (equal sym 'iprint-soft-bound))
                (not (equal sym 'iprint-hard-bound))
                (not (equal sym 'brr-evisc-tuple)))
           (fmt-state-p (update-nth 2
                                    (add-pair sym val (nth 2 state))
                                    state)))
  :hints (("Goal" :in-theory (enable fmt-state-p eviscerate-top-state-p))))

(defthm fmt0-bound-rewrite

; A slightly less general version of this lemma is proved above as fmt0-bound.

  (implies (and (force (natp col))
                (fmt-state-p state)
                (open-output-channel-p1 channel :character state)
                (natp bound)
                (< (fixnum-bound) bound))
           (< (car (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk))
              bound)))

(defthm open-output-channel-p1-put-global
  (equal (open-output-channel-p1
          channel type
          (update-nth 2 (add-pair sym val (nth 2 state)) state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(in-theory (disable mv-nth))

(defthm state-p-fmt0
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt0 s alist i maximum col pn channel state
                         evisc-tuple clk))))
             (state-p state2)))
  :hints (("Goal"
           :use fmt-state-p-fmt0
           :in-theory '(fmt-state-p))))

(verify-termination fmt1!) ; and guards
(verify-termination fmt!) ; and guards
(verify-termination fms!) ; and guards
