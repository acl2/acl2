; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "../vl/top")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)
(include-book "../svtv/debug")
(include-book "oslib/file-types" :dir :system)
(include-book "std/bitsets/bignum-extract-opt" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
#||
# fool dependency scanner, really included in make-cosim.lsp
(include-book "oslib/top" :dir :system)
||#

(local (in-theory (disable len nth)))

#!VL
(define vl-load-svex ((topmod stringp)
                      (loadconfig vl-loadconfig-p)
                      &key
                      ((simpconfig vl-simpconfig-p) '(make-vl-simpconfig))
                      (state 'state))
  (b* (((mv loadresult state)
        (vl-load (vl-loadconfig-fix loadconfig)))
       (design (vl-loadresult->design loadresult))
       ((mv err svex-design good bad)
        (vl-design->svex-design (string-fix topmod) design
                                (vl-simpconfig-fix simpconfig)))
       ((when err)
        (cw "Failed: ~@0" err)
        (mv nil design state)))
    (cw "Module names (good): ~x0~%" (vl-modulelist->names (vl-design->mods good)))
    (cw "Module names (bad): ~x0~%" (vl-modulelist->names (vl-design->mods bad)))
    (cw "Reportcard for good mods:~%")
    (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard good)))
    (cw "Reportcard for bad mods:~%")
    (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard bad)))
    (mv svex-design design state)))

#||
(defconst *testname* "gates")

(defconsts (*svex-design* state)
  (vl-load-svex "spec"
                (make-vl-loadconfig
                 :start-files (list (cat *testname* "/spec.sv")))))

(defconsts (*input-lines* state)
  (acl2::read-file-lines (cat *testname* "/inputs.data") state))
||#



(define str->4vec-aux ((x stringp)
                       (len natp)
                       (idx natp)
                       (hi-acc integerp)
                       (lo-acc integerp))
  :guard (and (<= len (length x))
              (<= idx len))
  :measure (nfix (- (nfix len) (nfix idx)))
  :returns (mv (hi integerp :rule-classes :type-prescription)
               (lo integerp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (disable acl2::member-of-cons
                                        member nth
                                        ;; acl2::nfix-when-not-natp
                                        (tau-system)
                                        logior ash))))
  :hooks ((:fix :hints (("Goal" :in-theory (disable (:d str->4vec-aux))
                         :expand ((:free (x len hi-acc lo-acc)
                                   (str->4vec-aux x len idx hi-acc lo-acc))
                                  (str->4vec-aux x len (nfix idx) hi-acc lo-acc))
                         :induct (str->4vec-aux x len idx hi-acc lo-acc)))))
  (b* (((when (mbe :logic (zp (- (nfix len) (nfix idx)))
                   :exec (eql idx len)))
        (mv (lifix hi-acc) (lifix lo-acc)))
       (char (char x idx))
       (idx (lnfix idx)) (len (lnfix len))
       ((unless (member char '(#\1 #\0 #\x #\X #\z #\Z)))
        ;; End early in case lines have newline or whitespace at end
        (mv (ash hi-acc (- idx len)) (ash lo-acc (- idx len))))
       (idx (1+ idx))
       (len (lnfix len))
       ;; (- (cw "char: ~x0~%" char))
       (hi-acc (if (member char '(#\1 #\x #\X))
                   (logior hi-acc (ash 1 (- len idx)))
                 hi-acc))
       (lo-acc (if (member char '(#\1 #\z #\Z))
                   (logior lo-acc (ash 1 (- len idx)))
                 lo-acc)))
    (str->4vec-aux x len idx hi-acc lo-acc)))


;; Note: might optimize the above by splitting into fixnum-sized chunks.
(define str->4vec ((x stringp))
  :returns (4vec 4vec-p)
  (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
       ((mv hi lo) (str->4vec-aux x (length x) 0 0 0)))
    (4vec hi lo)))


#||

(sv::defstv impl-stv
  :mod *svex-design*
  :inputs `(("input" input))
  :outputs ("output" output))

||#


(define cosim-compare-stv ((input-line stringp)
                           (output-line stringp)
                           (exactp)
                           (stv sv::svtv-p))
  :returns (ok "spec and implementation results were equal")
  :guard (member 'output (svtv->outs stv))
  (b* (((when (equal (vl::string-fix input-line) "")) t)
       (input-4vec (str->4vec input-line))
       (output-spec (str->4vec output-line))
       (res (sv::stv-run stv `((input . ,input-4vec))))
       (- (clear-memoize-table 'svex-eval))
       (output-impl (cdr (assoc 'output res))))
    (or (if exactp
            (equal output-spec output-impl)
          (4vec-<<= output-impl output-spec))
        (cw "Test failed: input:~%~s0~%output (spec):~%~s1~%output (vl/sv):~%~s2~%~x3~%~x4~%"
            input-line output-line
            (let* ((str (sv::vcd-4vec-bitstr output-impl (length output-line)))
                   (padlen (nfix (- 128 (length str))))
                   (pad (coerce (make-list padlen :initial-element #\0) 'string)))
              ;; gross hack to make it 128 bits
              (cat pad str))
            output-spec output-impl))))

(define cosims-compare-stv ((input-lines string-listp)
                            (output-lines string-listp)
                            (exactp)
                            (stv sv::svtv-p))
  :guard (and (eql (len input-lines) (len output-lines))
              (member 'output (svtv->outs stv)))
  :prepwork ((local (in-theory (disable vl::string-listp-when-no-nils-in-vl-maybe-string-listp
                                        string-listp
                                        member))))
  :guard-hints (("goal" :expand ((string-listp input-lines)
                                 (string-listp output-lines))))
  :hooks ((:fix :hints(("Goal" :expand ((str::string-list-fix input-lines)
                                        (str::string-list-fix output-lines))))))
  (b* (((when (atom input-lines)) t)
       (test1 (cosim-compare-stv (car input-lines) (car output-lines) exactp stv))
       (rest (cosims-compare-stv (cdr input-lines) (cdr output-lines) exactp stv)))
    (and test1 rest)))




(define cosims-compare-cycle ((input-line stringp)
                              (output-line stringp)
                              (exactp)
                              (updates svex-alist-p)
                              (nextstates svex-alist-p)
                              (currst svex-env-p)
                              (reset  bitp))
  :returns (mv (ok "spec and implementation results were equal")
               (nextst svex-env-p))
  :guard (svex-lookup "out" updates)
  (b* ((currst (svex-env-fix currst))
       (reset (lbfix reset))
       ((when (equal (vl::string-fix input-line) "")) (mv t currst))
       (input-4vec (str->4vec input-line))
       (output-spec (str->4vec output-line))
       (eval-alist0 `(("in" . ,input-4vec) ("clk" . 0) ("reset" . ,reset) . ,currst))
       (nextst0 (with-fast-alist eval-alist0 (svex-alist-eval nextstates eval-alist0)))
       (- (clear-memoize-table 'svex-eval))
       (eval-alist1 `(("in" . ,input-4vec) ("clk" . 1) ("reset" . 0) . ,nextst0))
       ((with-fast eval-alist1))
       (output-impl (4vec-zero-ext 128 (svex-eval (svex-lookup "out" updates) eval-alist1)))
       (nextst (svex-alist-eval nextstates eval-alist1))
       (- (clear-memoize-table 'svex-eval))
       (ok
        (or (if exactp
                (equal output-spec output-impl)
              (4vec-<<= output-impl output-spec))
            (cw "Test failed: input:~%~s0~%output (spec):~%~s1~%output (vl/sv):~%~s2~%~x3~%~x4~%"
                input-line output-line
                (let* ((str (sv::vcd-4vec-bitstr output-impl (length output-line)))
                       (padlen (nfix (- 128 (length str))))
                       (pad (coerce (make-list padlen :initial-element #\0) 'string)))
                  ;; gross hack to make it 128 bits
                  (cat pad str))
                output-spec output-impl))))
    (and ok (cw "Test passed: input:~%~s0~%output:~%~s1~%" input-line output-line))
    (mv ok nextst)))


(define cosims-compare-cycles ((input-lines string-listp)
                               (output-lines string-listp)
                               (exactp)
                               (updates svex-alist-p)
                               (nextstates svex-alist-p)
                               (currst svex-env-p)
                               (reset bitp))
  :guard (and (eql (len input-lines) (len output-lines))
              (svex-lookup "out" updates))
  (b* (((when (atom input-lines)) t)
       ((mv ok1 nextst) (cosims-compare-cycle (car input-lines) (car output-lines)
                                              exactp updates nextstates currst reset)))
    (and (cosims-compare-cycles (cdr input-lines) (cdr output-lines) exactp updates nextstates nextst 0)
         ok1)))

(define cosims-compare ((input-lines string-listp)
                        (output-lines string-listp)
                        (exactp)
                        (updates svex-alist-p)
                        (nextstates svex-alist-p))
  :guard (and (eql (len input-lines) (len output-lines))
              (svex-lookup "out" updates))
  :prepwork ((local (in-theory (disable vl::string-listp-when-no-nils-in-vl-maybe-string-listp
                                        string-listp
                                        member))))
  :guard-hints (("goal" :expand ((string-listp input-lines)
                                 (string-listp output-lines))))
  :hooks ((:fix :hints(("Goal" :expand ((str::string-list-fix input-lines)
                                        (str::string-list-fix output-lines))))))
  (cosims-compare-cycles input-lines output-lines exactp updates nextstates nil 1))






#||

;; Generate inputs:

(progn
  ;; some all-Boolean examples
  (loop for i from 0 to 511 do
        (loop for j from 0 to 127 do
              (let ((rand (random 4)))
                (cond ((< rand 2) (format t "1"))
                      (t          (format t "0")))))
        (format t "~%"))
  ;; some with Xes
  (loop for i from 0 to 255 do
        (loop for j from 0 to 127 do
              (let ((rand (random 5)))
                (cond ((< rand 2) (format t "1"))
                      ((< rand 4) (format t "0"))
                      (t          (format t "X")))))
        (format t "~%"))
  ;; some with Xes and Zs
  (loop for i from 0 to 255 do
        (loop for j from 0 to 127 do
              (let ((rand (random 6)))
                (cond ((< rand 2) (format t "1"))
                      ((< rand 4) (format t "0"))
                      ((< rand 5) (format t "X"))
                      (t          (format t "Z")))))
        (format t "~%")))



||#
