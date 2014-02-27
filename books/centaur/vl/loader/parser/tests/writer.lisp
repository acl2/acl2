; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "base")
(include-book "expressions")
(include-book "../../../mlib/writer")

(define run-writer-test ((test exprtest-p)
                         &key
                         ((config vl-loadconfig-p) '*vl-default-loadconfig*))

  ;; This is a cheap way to test the writer.  We can just reuse our parser
  ;; tests.
  (b* (((exprtest test) test)
       (- (cw "Running test ~x0; edition ~s1, strict ~x2~%" test
              (vl-loadconfig->edition config)
              (vl-loadconfig->strictp config)))

       (echars (vl-echarlist-from-str test.input))
       ((mv successp tokens warnings)
        (vl-lex echars
                :config config
                :warnings nil))
       ((unless successp)
        ;; Fine, we don't care, we just want to test the writer, if this
        ;; input doesn't even parse, that's fine.
        t)

       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
       ((mv errmsg? val & &)
        (vl-parse-expression :tokens tokens
                             :warnings warnings
                             :config config))
       ((when errmsg?)
        ;; Fine, don't care
        t)

       ;; Else, VAL is the initial expression we're going to check.
       (val-pp (with-local-ps (vl-pp-expr val)))
       (- (cw "VAL-PP is ~x0.~%" val-pp))

       (echars (vl-echarlist-from-str test.input))
       ((mv successp tokens warnings)
        (vl-lex echars
                :config config
                :warnings nil))
       ((unless successp)
        (raise "Failed to successfully lex val-pp: ~x0.~%" val-pp))

       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
       ((mv errmsg? new-val & &)
        (vl-parse-expression :tokens tokens
                             :warnings warnings
                             :config config))
       ((when errmsg?)
        (raise "Parsing failed for val-pp: ~x0.  ~x1" val-pp errmsg?))

       ((unless (equal val new-val))
        (raise "Failed to get the same value out.~x0~%"
               (list :input test.input
                     :val val
                     :val-pp val-pp
                     :new-val new-val))))
    t))

(define run-writer-tests ((x exprtestlist-p)
                          &key
                          ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  (if (atom x)
      t
    (and (run-writer-test (car x) :config config)
         (run-writer-tests (cdr x) :config config))))

(defconst *all-writer-tests*
  (append *all-basic-tests*
          *sysv-diff-tests*
          *verilog-diff-tests*
          *sysv-only-tests*))

(make-event
 (and
  (run-writer-tests *all-writer-tests*
                    :config (make-vl-loadconfig :edition :system-verilog-2012
                                                :strictp nil))
  (run-writer-tests *all-writer-tests*
                    :config (make-vl-loadconfig :edition :system-verilog-2012
                                                :strictp t))
  (run-writer-tests *all-writer-tests*
                    :config (make-vl-loadconfig :edition :verilog-2005
                                                :strictp nil))
  (run-writer-tests *all-writer-tests*
                    :config (make-vl-loadconfig :edition :verilog-2005
                                                :strictp t))
  '(value-triple :success)))

