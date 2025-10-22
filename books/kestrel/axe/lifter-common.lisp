; Utilities used by multiple lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-size")
(include-book "dag-to-term")
(include-book "count-branches")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prints as a term if the term is not too big.
;; todo: respect the print-base?
(defund print-dag-nicely (dag)
  (declare (xargs :guard (pseudo-dagp dag)))
  (if (dag-or-quotep-size-less-than dag 1000)
      (cw "~X01" (dag-to-term dag) nil) ; todo: untranslate (see below)
    (cw "~X01" dag nil)))

;; Returns state.
;; restores the print-base to 10 (do better?)
(defund print-dag-nicely-with-base (dag descriptor untranslatep print-base state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (stringp descriptor)
                              (booleanp untranslatep)
                              (member print-base '(10 16)))
                  :stobjs state))
  (if (dag-or-quotep-size-less-than dag 1000) ; todo: drop the "-or-quotep"
      (b* ((- (cw "(Term ~x0:~%" descriptor))
           (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                      (set-print-base-radix print-base state)
                    state))
           (term (dag-to-term dag))
           (term (if untranslatep (acl2::untranslate$ term nil state) term))
           (- (cw "~X01" term nil))
           (state (set-print-base-radix 10 state)) ;make-event sets it to 10
           (- (cw ")~%"))) ; matches "(Term after"
        state)
    (b* ((- (cw "(DAG ~x0:~%" descriptor))
         (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                    (set-print-base-radix print-base state)
                  state))
         (- (cw "~X01" dag nil))
         (state (set-print-base-radix 10 state))
         (- (cw "(DAG has ~x0 IF-branches.)~%" (acl2::count-top-level-if-branches-in-dag dag))) ; todo: if 1, say "no ifs"
         (- (cw ")~%"))) ; matches "(DAG after"
      state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: move this util

;; Recognizes an alist from functions to boolean-lists representing which arguments to print.
(defun elision-spec-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (symbolp (car entry))
           (boolean-listp (cdr entry))
           (elision-spec-alistp (rest alist))))))

(defthm elision-spec-alistp-forward-to-alistp
    (implies (elision-spec-alistp alist)
             (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable elision-spec-alistp alistp))))

;; Replace with :elided any large constant list arg that corresponds with nil in the bools.
;; todo: clarify the sense of t and nil (nil means maybe don't print)
(defun apply-elision-spec (args bools)
  (declare (xargs :guard (and (true-listp args)
                              (boolean-listp bools))))
  (if (endp args)
      nil
    (cons (if (and (not (first bools))
                   (let ((arg (first args)))
                     (and (myquotep arg)
                          (consp (unquote arg)) ; checks for a fairly long list
                          (<= 100 (len (unquote arg))))))
              :elided
            (first args))
          (apply-elision-spec (rest args) (rest bools)))))

(defund print-term-elided (term firstp elision-specs)
  (declare (xargs :guard (elision-spec-alistp elision-specs)))
  (let ((elision-spec (and (consp term)
                           (lookup-eq (car term) elision-specs))))
    (if elision-spec
        ;; eliding:
        (if (not (true-listp term))
            (er hard? 'print-term-elided "Bad term.")
          (if (not (= (len (rest term)) (len elision-spec))) ; todo: optimize via same-lengthp
              (er hard? 'print-term-elided "Length mismatch in elision spec, ~x0, for ~x1." elision-spec (car term))
            (let ((elided-term (cons (car term) (apply-elision-spec (rest term) elision-spec))))
              (if firstp
                  (cw "(~y0" elided-term)
                (cw " ~y0" elided-term)))))
      ;; not eliding (todo: share code with the above):
      (if firstp
          (cw "(~y0" term)
        (cw " ~y0" term)))))

;; Prints each of the TERMS, each starting with a space and ending with a newline.
;tail recursive, to support printing a large list
(defund print-terms-elided-aux (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (atom terms)
      nil
    (prog2$ (print-term-elided (first terms) nil elision-specs)
            (print-terms-elided-aux (rest terms) elision-specs))))

(defund print-terms-elided (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (consp terms)
      (prog2$ (print-term-elided (first terms) t elision-specs) ;print the first element separately to put in an open paren
              (prog2$ (print-terms-elided-aux (rest terms) elision-specs)
                      (cw ")")))
    (cw "nil") ; or could do ()
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removes all of the TERMS that are calls of one of the FNS-TO-REMOVE, or
;; negations of such calls.
(defund remove-assumptions-about (fns-to-remove terms)
  (declare (xargs :guard (and (symbol-listp fns-to-remove)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let* ((term (first terms))
           ;; strip a NOT if present:
           (core-term (if (and (consp term)
                               (eq 'not (ffn-symb term))
                               (= 1 (len (fargs term))))
                          (farg1 term)
                        term)))
      (if (and (consp core-term)
               (member-eq (ffn-symb core-term) fns-to-remove))
          (remove-assumptions-about fns-to-remove (rest terms))
        (cons term (remove-assumptions-about fns-to-remove (rest terms)))))))

;; Sanity check:
(thm
  (subsetp-equal (remove-assumptions-about fns-to-remove terms)
                 terms)
  :hints (("Goal" :in-theory (enable remove-assumptions-about))))

(defthm pseudo-term-listp-of-remove-assumptions-about
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (remove-assumptions-about fns-to-remove terms)))
  :hints (("Goal" :in-theory (enable remove-assumptions-about))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These assumptions get removed during pruning (unlikely to help and lead to
;; messages about non-known-boolean literals being dropped)
;; TODO: Add more?
;; TODO: Include IF?
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline
    program-at
    separate
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    app-view))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A lifter target is either a numeric offset, the name of a subroutine (a string), or the symbol :entry-point.
(defun lifter-targetp (target)
  (declare (xargs :guard t))
  (or (natp target)
      (stringp target)
      (eq :entry-point target)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a symbol-list.
(defund maybe-add-debug-rules (debug-rules monitor)
  (declare (xargs :guard (and (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (symbol-listp debug-rules))))
  (if (eq :debug monitor)
      debug-rules
    (if (member-eq :debug monitor)
        ;; replace :debug in the list with all the debug-rules:
        (union-eq debug-rules (remove-eq :debug monitor))
      ;; no special treatment:
      monitor)))
