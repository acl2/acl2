; Copyright (C) Intel Corporation
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

(in-package "SV")

(include-book "svtv-to-sva-types")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/strings/substrp" :dir :System)

;; svtv-run mapping to directories where we store SVAs

(define parse-define-stub-inputs ((stub-ins true-listp)
                                  (formals true-listp)
                                  (guards true-listp))
  (if (atom stub-ins)
      (mv (reverse formals) (reverse guards))
    (b* ((stub-in (car stub-ins))
         ((when (symbolp stub-in))
          (parse-define-stub-inputs (cdr stub-ins) (cons stub-in formals)
                                    (cons t guards)))
         ((when (and (consp stub-in)
                     (symbolp (car stub-in))
                     (consp (cdr stub-in))
                     (symbolp (cadr stub-in))))
          (parse-define-stub-inputs (cdr stub-ins) (cons (car stub-in) formals)
                                    (cons (cadr stub-in) guards)))
         )
      (mv (raise "Error: unrecognized syntax for define-stub formals: ~x0"
                 stub-in)
          nil))))

(define make-define-stub-guard-lst (formals guards-lst)
  (if (or (atom formals)
          (atom guards-lst))
      nil
    (b* ((formal (car formals))
         (guard  (car guards-lst)))
      (if (equal guard 't)
          (make-define-stub-guard-lst (cdr formals) (cdr guards-lst))
        (cons (list guard formal)
              (make-define-stub-guard-lst (cdr formals) (cdr guards-lst)))))))

(defmacro define-stub (fn-name inputs
                               &key
                               (returns 'nil)
                               (short   'nil)
                               )
  "Very simple enhancement of defstub that allows a return theorem"
  (b* (((mv formals guard-from-inputs) (parse-define-stub-inputs inputs nil nil))
       (formals-as-sig (make-list (len formals) :initial-element '*))
       (guard-lst (make-define-stub-guard-lst formals guard-from-inputs))
       (guard (if guard-lst (cons 'and guard-lst) t))
       (signature (list (cons fn-name formals-as-sig) '=> '* :formals formals :guard guard))
       ((unless (or (null returns)
                    (and (consp returns)
                         (symbolp (car returns))
                         (consp (cdr returns))
                         (symbolp (cadr returns)))))
        (cw "define-stub only supports one return-value~%"))
       (return-type  (and returns (cadr returns)))
       (return-thm   (if returns
                         `((defthm ,(intern-in-package-of-symbol
                                     (str::cat (symbol-name fn-name)
                                               "-RETURN-VALUE")
                                     'pkg)
                             (,return-type ,(cons fn-name formals))))
                       nil))
       (body (if (null returns)
                 nil
               (case return-type
                 (stringp "")
                 (integerp 0)
                 (t nil))))
       (doc-string
        (if short (list short) nil))
       )
    `(encapsulate
       (,signature)
       (set-irrelevant-formals-ok t)
       (set-ignore-ok t)
       (local (defun ,fn-name ,formals
                ,@doc-string
                ,body))
       ,@return-thm
       )))

;;;;

; Each of the following function stubs will need a corresponding "defattach"
; event that indicates project-specific information. These functions will need
; executable bodies to run svtv-to-sva.

(define-stub sva-run-dut-name ((x symbolp))
  :short "Return the DUT to which the input SVTV belongs."
  :returns (r stringp))

(define-stub sva-run-top-module-name ((x symbolp))
  :short "If the input SVTV was produced from an instance of a module, return the module name."
  :returns (r stringp))

(define-stub sva-run-mod-dir ((x symbolp))
  :short "Return the name of the directory under which the input SVTV's SVAs will be
  stored."
  :returns (r stringp))

(define-stub sva-run-sv-dir ((x symbolp))
  :short "Return the parent directory for the input SVTV under which its
sva-run-mod-dir will be stored."
  :returns (r stringp))

(define-stub sva-run-sv-file ((x symbolp) (cfg svtv-sva-cfg-p))
  :short "Given an input SVTV and CFG, return the full path name for the file
  where the SVTV's SVAs will be saved."
  :returns (r stringp))

(define-stub sva-tmp-sv-dir ((cfg svtv-sva-cfg-p))
  :short "Return the directory where the latest generated SVA by svtv-to-sva can also
  be saved for convenience."
  :returns (r stringp))

(define-stub sva-run-make-cmd ((x symbolp))
  :short "Return an SVTV-specific make command that will be printed to the ACL2
  shell for user convenience -- this can be helpful for interacting with tools
  like JasperGold."
  :returns (r stringp))

(define-stub sva-run-cp-cmd ((x symbolp) (cfg svtv-sva-cfg-p))
  :short "Return an SVTV-specific cp command that will be printed to the ACL2
  shell for user convenience -- this can be helpful for interacting with tools
  like JasperGold."
  :returns (r stringp))

(define-stub sva-run-clk ((x symbolp))
  :short "Return the name of the clk signal for the input SVTV."
  :returns (r stringp))

(define-stub sva-run-rst ((x symbolp))
  :short "Return the name of the rst signal for the input SVTV."
  :returns (r stringp))

(define-stub sva-run-modify-assumes ((a string-list-list-p) (x symbolp))
  :short "Return a modified the set of assumptions given a list of lists of assumptions (at each clock) and the name of
  an SVTV."
  :returns (r string-list-list-p))

(define-stub sva-run-modify-concludes ((c string-listp) (x symbolp))
  :short "Return a modified set of conclusions given a list of conclusions and the name of an SVTV."
  :returns (r string-listp))

;;;;

; Some helper functions that can help define some stubbed functions.

(define matches-str-in-list ((x string-listp) (e stringp))
  (and (consp x)
       (or (str::substrp (first x) e)
           (matches-str-in-list (rest x) e))))

(define remove-var-matches ((x string-listp)
                            (r string-listp))
  :returns (r string-listp :hyp :guard)
  (cond ((endp x) ())
        ((matches-str-in-list r (first x))
         (remove-var-matches (rest x) r))
        (t (cons (first x)
                 (remove-var-matches (rest x) r)))))

(define remove-vtrms-with-vars ((a string-list-list-p)
                                (r string-listp))
  :returns (r string-list-list-p :hyp :guard)
  (if (endp a) ()
    (cons (remove-var-matches (first a) r)
          (remove-vtrms-with-vars (rest a) r))))

(define add-vtrms-to-each ((a string-list-list-p)
                           (x string-listp))
  :returns (r string-list-list-p :hyp :guard)
  (if (endp a) ()
    (cons (append (first a) x)
          (add-vtrms-to-each (rest a) x))))
