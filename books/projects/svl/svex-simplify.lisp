; SVL - Listener-based Hierachical Verilog Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

;; A tool to apply existing rewrite rules about 4vec functions to simplify sv
;; expresions by wrappaing them with "svex-eval" and an environment with all
;; the variables in svex pointing to some automatically created free variables.

(in-package "SVL")

(include-book "meta/top")

(in-theory (disable bitp natp))

(progn
  (defun merge-sets (set1 set2)
    (declare (xargs :mode :program))
    (if (atom set1)
        set2
      (merge-sets
       (cdr set1)
       (add-to-set (car set1) set2 :test 'equal))))

  ;; returns a list of variables in an svex
  (mutual-recursion
   (defun get-svex-vars (svex)
     (declare (xargs :mode :program))
     (let* ((svex.kind (svex-kind svex)))
       (case svex.kind
         (:quote nil)
         (:var (list svex))
         (otherwise
          (get-svex-vars-lst (cdr svex))))))
   (defun get-svex-vars-lst (lst)
     (if (atom lst)
         nil
       (merge-sets (get-svex-vars (car lst))
                   (get-svex-vars-lst (cdr lst)))))))

(mutual-recursion
 (defun to-string (val)
   (declare (xargs :mode :program))
   (cond
    ((symbolp val)
     (if (keywordp val)
         (string-append ":" (symbol-name val))
       (symbol-name val)))
    ((stringp val)
     (string-append "\"" (string-append val "\"")))
    ((consp val)
     (string-append "(" (string-append (to-string-lst val) ")")))
    (t
     (str::intstr (ifix val)))))
 (defun to-string-lst (lst)
   (if (atom lst)
       (if (equal lst nil)
           ""
         (string-append " . " (to-string lst)))

     (string-append
      (to-string (car lst))
      (string-append
       (if (consp (cdr lst)) " " "")
       (to-string-lst (cdr lst)))))))

(defun to-symbol (val)
  (declare (xargs :mode :program))
  (intern$ (to-string val) *PACKAGE-NAME*))

(progn
  ;; creates a dummy environment with all the variables in svex binding them to
  ;; a unique symbol.
  (define create-dummy-svex-env-aux (vars)
    (declare (xargs :mode :program))
    (if (atom vars)
        (mv ''nil nil nil)
      (b* (((mv rest-term rest-falist rest-reverselist)
            (create-dummy-svex-env-aux (cdr vars)))
           (cur-symbol (to-symbol (car vars))))
        (mv `(cons (cons ',(car vars) (rp '4vec-p ,cur-symbol))
                   ,rest-term)
            (hons-acons (car vars) `(rp '4vec-p ,cur-symbol)
                        rest-falist)
            (hons-acons cur-symbol (car vars)
                        rest-reverselist)))))

  (defun create-dummy-svex-env (vars)
    (declare (xargs :mode :program))
    (b* (((mv term falist reverse-env)
          (create-dummy-svex-env-aux vars)))
      (mv `(rp 'svex-env-p (falist ',falist ,term))
          reverse-env))))

(define svex-rw-create-rules (&key (runes 'nil)
                                   (state 'state))
  ;; you need to remember to run fat-alist-free for  rules-alist
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((world (w state))
       (runes (if runes runes (current-theory :here)))
       (enabled-exec-rules (rp::get-enabled-exec-rules runes))
       (rules-alist (rp::get-rules runes state)))
    (cons rules-alist enabled-exec-rules)))

(define rw-svex-to-4vec (svex
                         &KEY
                         (state 'state)
                         (rp::rp-state 'rp::rp-state)
                         (hyp ''t) ;; "Have more context for variables."
                         (runes 'nil) ;; "if need to work with only certain rules other than current-theory"
                         (created-rules 'nil) ;; Non-nil overrides rule
                         ;; structure  creation for the rewriter. This value
                         ;; can be created with svex-rw-create-rules
                         )
  (declare (xargs :mode :program
                  :stobjs (state
                           rp::rp-state)))
  (b* ((world (w state))
       (- (if (svex-p svex) nil
            (hard-error 'rw-svex-to-4vec  "Input is not an svex" nil)))
       ;; this indirectly checks that all the meta rules added are also proved.
       (- (rp::check-if-clause-processor-up-to-date world))
       ;; find the variables in the svex
       (vars (get-svex-vars svex))
       ;; create the env and reverse-env (same as env but keys and vals swapped)
       ((mv env-term reverse-env) (create-dummy-svex-env vars))
       ;; get the list of runes/rule names
       (runes (if runes runes (current-theory :here)))
       (enabled-exec-rules (if created-rules
                               (cdr created-rules)
                             (rp::get-enabled-exec-rules runes)))
       (rules-alist (if created-rules (car created-rules) (rp::get-rules runes state)))
       (meta-rules (make-fast-alist
                    (cdr (assoc-equal 'rp::meta-rules-list
                                      (table-alist 'rp::rp-rw (w state))))))
       (old-not-simplified-action (rp::not-simplified-action rp::rp-state))
       (rp::rp-state (rp::update-not-simplified-action :none rp::rp-state))
       ;; CREATE THE TERM TO BE REWRITTEN
       (term `(implies ,hyp (svex-eval ',svex ,env-term)))
       ((mv rw rp::rp-state)
        (rp::rp-rw-aux term
                       rules-alist
                       enabled-exec-rules
                       meta-rules
                       rp::rp-state
                       state))
       ;; restore rp-state setting
       (rp::rp-state (rp::update-not-simplified-action
                      old-not-simplified-action rp::rp-state))
       (- (if created-rules nil (fast-alist-free rules-alist)))
       (- (fast-alist-free meta-rules))
       (- (fast-alist-free (cadr (cadr (caddr env-term))))))
    (mv rw reverse-env rp::rp-state)))

(defun to-svex-fnc (term)
  (declare (xargs :mode :program))
  (case-match term
    (('svl::bits & & &)         (cons 'sv::partsel  (cdr term)))
    (('svl::sbits & & & &)      (cons 'sv::partinst (cdr term)))
    (('svl::4vec-concat$ & & &) (cons 'sv::concat   (cdr term)))
    (('svl::4vec-bitnot$ size x) `(partsel 0 ,size (sv::bitnot ,x)))

    (('sv::4vec-fix &) (cons 'id (cdr term)))
    (('sv::4vec-bit-extract & &) (cons 'sv::bitsel (cdr term)))
    (('SV::3VEC-FIX &)           (cons 'SV::UNFLOAT  (cdr term)))
    (('4VEC-BITNOT &)            (cons 'sv::BITNOT   (cdr term)))
    (('4VEC-BITAND & &)          (cons 'sv::BITAND   (cdr term)))
    (('4VEC-BITOR & &)           (cons 'SV::BITOR    (cdr term)))
    (('SV::4VEC-BITXOR & &)      (cons 'SV::BITXOR   (cdr term)))
    (('SV::4VEC-RES & &)         (cons 'SV::RES      (cdr term)))
    (('SV::4VEC-RESAND & &)      (cons 'SV::RESAND   (cdr term)))
    (('SV::4VEC-RESOR & &)       (cons 'SV::RESOR    (cdr term)))
    (('SV::4VEC-OVERRIDE & &)    (cons 'SV::OVERRIDE (cdr term)))
    (('SV::4VEC-ONSET &)         (cons 'SV::ONP      (cdr term)))
    (('SV::4VEC-OFFSET &)        (cons 'SV::OFFP     (cdr term)))
    (('SV::4VEC-REDUCTION-AND &) (cons 'SV::UAND     (cdr term)))
    (('SV::4VEC-REDUCTION-OR &)  (cons 'SV::UOR      (cdr term)))
    (('4VEC-PARITY &)            (cons 'SV::UXOR     (cdr term)))
    (('4VEC-ZERO-EXT & &)        (cons 'sv::ZEROX    (cdr term)))
    (('SV::4VEC-SIGN-EXT & &)    (cons 'SV::SIGNX    (cdr term)))
    (('4VEC-CONCAT & & &)        (cons 'CONCAT       (cdr term)))
    (('SV::4VEC-REV-BLOCKS & & &)(cons 'sv::BLKREV   (cdr term)))
    (('4VEC-RSH & &)             (cons 'sv::RSH      (cdr term)))
    (('4VEC-LSH & &)             (cons 'sv::lsh      (cdr term)))
    (('4VEC-PLUS & &)            (cons '+            (cdr term)))
    (('SV::4VEC-MINUS & &)       (cons 'SV::B-       (cdr term)))
    (('SV::4VEC-UMINUS & &)      (cons 'SV::U-       (cdr term)))
    (('SV::4VEC-TIMES & &)       (cons '*            (cdr term)))
    (('SV::4VEC-QUOTIENT & &)    (cons '/            (cdr term)))
    (('SV::4VEC-REMAINDER & &)   (cons 'SV::%        (cdr term)))
    (('SV::4VEC-XDET &)          (cons 'SV::XDET     (cdr term)))
    (('SV::4VEC-COUNTONES &)     (cons 'SV::COUNTONES(cdr term)))
    (('SV::4VEC-ONEHOT &)        (cons 'SV::ONEHOT   (cdr term)))
    (('SV::4VEC-ONEHOT0 &)       (cons 'SV::ONEHOT0  (cdr term)))
    (('SV::4VEC-< & &)           (cons '<            (cdr term)))
    (('4VEC-== & &)              (cons 'SV::==       (cdr term)))
    (('SV::4VEC-=== & &)         (cons 'SV::===      (cdr term)))
    (('SV::4VEC-WILDEQ & &)      (cons 'SV::==?      (cdr term)))
    (('SV::4VEC-WILDEQ-SAFE & &) (cons 'SV::SAFER-==?(cdr term)))
    (('SV::4VEC-SYMWILDEQ & &)   (cons 'SV::==??     (cdr term)))
    (('SV::4VEC-CLOG2 &)         (cons 'SV::CLOG2    (cdr term)))
    (('SV::4VEC-POW & &)         (cons 'SV::POW      (cdr term)))
    (('4VEC-? & & &)             (cons 'SV::?        (cdr term)))
    (('4VEC-?* & & &)            (cons 'SV::?*       (cdr term)))
    (('SV::4VEC-BIT? & & &)      (cons 'SV::BIT?     (cdr term)))
    (('4VEC-PART-SELECT & & &)   (cons 'PARTSEL      (cdr term)))
    (('4VEC-PART-INSTALL & & & &)(cons 'SV::PARTINST (cdr term)))
    (& (hard-error '4vec-to-svex "Cannot match ~p0 with ~p1 arguments to any ~
  svex function. If you think this is a bug, consider changing ~
  svl::get-svex-fnc. ~%"
                   (list (cons #\0 (car term))
                         (cons #\1 (len (cdr term))))))))

(mutual-recursion
 (defun 4vec-to-svex (term reverse-env)
   (declare (xargs :mode :program))
   (b* ((term (rp::ex-from-rp term)))
     (cond ((atom term)
            (cdr (hons-get term reverse-env)))
           ((quotep term)
            (unquote term))
           (t (b* ((fnc (car term))
                   (args (4vec-to-svex-lst (cdr term)
                                           reverse-env)))
                (to-svex-fnc (cons fnc args)))))))
 (defun 4vec-to-svex-lst (lst reverse-env)
   (declare (xargs :mode :program))
   (if (atom lst)
       nil
     (cons (4vec-to-svex (car lst) reverse-env)
           (4vec-to-svex-lst (cdr lst) reverse-env)))))


(define svex-simplify (svex
                       &KEY
                       (state 'state)
                       (rp::rp-state 'rp::rp-state)
                       (hyp ''t) ;; "Have more context for variables."
                       (runes 'nil) ;; "if need to work with only certain rules other than current-theory"
                       (created-rules 'nil) ;; Non-nil overrides rule
                       ;; structure  creation for the rewriter. This value
                       ;; can be created with svex-rw-create-rules
                       )
  (declare (xargs :mode :program
                  :stobjs (state
                           rp::rp-state)))
  (b* (((mv rw reverse-env rp::rp-state)
        (rw-svex-to-4vec svex
                         :state state
                         :hyp hyp
                         :runes runes
                         :created-rules created-rules))
       (svex-res (case-match rw
                   (('implies & term) (4vec-to-svex term
                                                    reverse-env))
                   (& (4vec-to-svex rw reverse-env)))))
    (mv svex-res rp::rp-state)))

#|
 
;; Example use:

(defconst *test-svex*
  '(partsel
    0 2
    (SV::?
     (SV::BITOR (SV::UOR (BITAND (BITNOT (:VAR "Clock" . 1))
                                 (CONCAT 1 "Clock" 0)))
                (SV::UOR (BITAND (BITNOT "Reset")
                                 (CONCAT 1 (:VAR "Reset" . 1) 0))))
     (CONCAT
      32
      (SV::?*
       (CONCAT 1
               (BITNOT (SV::? (SV::BITSEL 0 "Reset")
                              (:VAR "Reset" . 1)
                              "Reset"))
               0)
       0
       (SV::?*
        (CONCAT 1 (BITNOT (:VAR "Enable" . 1))
                0)
        (SV::?*
         (CONCAT 1 (BITNOT (:VAR "Load" . 1)) 0)
         (:VAR "Data" . 1)
         (SV::?*
          (SV::BITOR
           (BITAND (CONCAT 1
                           (BITNOT (CONCAT 1 (:VAR "Mode" . 1) 0))
                           0)
                   (BITNOT (SV::== (CONCAT 32 (:VAR "Count" . 1) 0)
                                   15)))
           (BITAND (CONCAT 1 (:VAR "Mode" . 1) 0)
                   (BITNOT (SV::== (CONCAT 32 (:VAR "Count" . 1) 0)
                                   9))))
          (+ (CONCAT 32 (:VAR "Count" . 1) 0) 1)
          0))
        (:VAR "Count" . 1)))
      (CONCAT
       32
       (SV::?*
        (CONCAT 1
                (BITNOT (SV::? (SV::BITSEL 0 "Reset")
                               (:VAR "Reset" . 1)
                               "Reset"))
                0)
        0
        (SV::?*
         (CONCAT 1 (BITNOT (:VAR "Enable" . 1))
                 0)
         (SV::?*
          (CONCAT 1 (BITNOT (:VAR "Load" . 1)) 0)
          (RSH 32 (:VAR "Data" . 1))
          (SV::?*
           (SV::BITOR
            (BITAND (CONCAT 1
                            (BITNOT (CONCAT 1 (:VAR "Mode" . 1) 0))
                            0)
                    (BITNOT (SV::== (CONCAT 32 (:VAR "Count" . 1) 0)
                                    15)))
            (BITAND (CONCAT 1 (:VAR "Mode" . 1) 0)
                    (BITNOT (SV::== (CONCAT 32 (:VAR "Count" . 1) 0)
                                    9))))
           (RSH 32 (:VAR "Count" . 1))
           (SV::?*
            (SV::BITOR
             (BITAND (CONCAT 1
                             (BITNOT (CONCAT 1 (:VAR "Mode" . 1) 0))
                             0)
                     (BITNOT (SV::== (PARTSEL 32 32 (:VAR "Count" . 1))
                                     15)))
             (BITAND (CONCAT 1 (:VAR "Mode" . 1) 0)
                     (BITNOT (SV::== (PARTSEL 32 32 (:VAR "Count" . 1))
                                     9))))
            (+ (CONCAT 32 (RSH 32 (:VAR "Count" . 1))
                       0)
               1)
            0)))
         (RSH 32 (:VAR "Count" . 1))))
       (RSH 64 (:VAR "Count" . 1))))
     (:VAR "Count" . 1))))

(RW-SVEX-TO-4VEC *test-svex* :hyp '(integerp |(:VAR Count . 1)|))

(svex-simplify *test-svex*)||#
