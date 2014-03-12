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
(include-book "flopcode-prog")
(include-book "../../mlib/context")
(local (include-book "../../util/arithmetic"))

; Debugger to figure out why a statement isn't a valid flopcode program

(define vl-flopcodeassign-debug ((x vl-assignstmt-p)
                                 (elem vl-modelement-p))
  :returns (warning? (and (equal (vl-warning-p warning?)
                                 (not (vl-flopcodeassign-p x)))
                          (iff warning?
                               (not (vl-flopcodeassign-p x)))))
  :parents (flopcode vl-flopcodeassign-p)
  :prepwork ((local (in-theory (enable vl-flopcodeassign-p))))
  (b* (((vl-assignstmt x) x)
       ((unless (eq x.type :vl-nonblocking))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected only ~
               non-blocking assignments (i.e., a <= b), but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((unless (vl-idexpr-p x.lvalue))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected all ~
               left-hand sides to be single identifiers, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((unless (or (not x.ctrl)
                    (and (mbe :logic (vl-delaycontrol-p x.ctrl)
                              :exec (eq (tag x.ctrl) :vl-delaycontrol))
                         (vl-simpledelaycontrol-p x.ctrl))))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected only ~
               delay-free or simply delayed (e.g., #5) assignments, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((unless (and (posp (vl-expr->finalwidth x.lvalue))
                     (posp (vl-expr->finalwidth x.expr))
                     (int= (vl-expr->finalwidth x.lvalue)
                           (vl-expr->finalwidth x.expr))))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected sizes ~
               to be compatible in assignments, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((unless (and (vl-expr-welltyped-p x.lvalue)
                     (vl-expr-welltyped-p x.expr)))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected ~
               well-typed expressions, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__)))
    nil))


(define vl-flopcodestmt-debug ((x vl-stmt-p)
                               (elem vl-modelement-p))
  :returns (warning? (and (equal (vl-warning-p warning?)
                                 (not (vl-flopcodestmt-p x)))
                          (iff warning?
                               (not (vl-flopcodestmt-p x)))))
  :parents (flopcode vl-flopcodestmt-p)
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p))))
  (b* (((when (vl-fast-atomicstmt-p x))
        (if (vl-fast-assignstmt-p x)
            (vl-flopcodeassign-debug x elem)
          (make-vl-warning
           :type :vl-flopcode-fail
           :msg "~a0: statement is too complex to synthesize.  Expected only ~
                 assignments but found ~a1."
           :args (list elem x)
           :fatalp nil
           :fn __function__)))
       ((unless (vl-ifstmt-p x))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected no ~
               compound statements other than if-statements, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((vl-ifstmt x) x)
       ((unless (vl-assignstmt-p x.truebranch))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected ifs to ~
               have a single assignment for their true branch, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       (warning (vl-flopcodeassign-debug x.truebranch elem))
       ((when warning)
        warning)
       ((unless (vl-nullstmt-p x.falsebranch))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected no else ~
               branches, but found ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__))
       ((unless (and (vl-expr-welltyped-p x.condition)
                     (vl-expr->finaltype x.condition)
                     (eql (vl-expr->finalwidth x.condition) 1)))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected sizes ~
               to be computed on if statement conditions, but this is not the ~
               case for ~a1."
         :args (list elem x)
         :fatalp nil
         :fn __function__)))
    nil))


(define vl-flopcodestmtlist-debug ((x vl-stmtlist-p)
                                   (elem vl-modelement-p))
  :returns (warning? (and (equal (vl-warning-p warning?)
                                 (not (vl-flopcodestmtlist-p x)))
                          (iff warning?
                               (not (vl-flopcodestmtlist-p x)))))
  :parents (flopcode vl-flopcodestmtlist-p)
  (if (atom x)
      nil
    (or (vl-flopcodestmt-debug (car x) elem)
        (vl-flopcodestmtlist-debug (cdr x) elem))))


(define vl-flopcodeprog-debug ((x vl-stmtlist-p)
                               (elem vl-modelement-p))
  :returns (warning? (and (equal (vl-warning-p warning?)
                                 (not (vl-flopcodeprog-p x)))
                          (iff warning?
                               (not (vl-flopcodeprog-p x)))))
  :parents (flopcode vl-flopcodeprog-p)
  :prepwork ((local (in-theory (enable vl-flopcodeprog-p))))
  (b* ((w (vl-flopcodestmtlist-debug x elem))
       ((when w)
        w)

       (lhses (vl-flopcodestmtlist->lhses x))
       ((unless lhses)
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected ~
               non-empty statement list."
         :args (list elem)
         :fatalp nil
         :fn __function__))

       (lhs1   (car lhses))
       (name1  (vl-idexpr->name lhs1))
       (width1 (vl-expr->finalwidth lhs1))

       ((unless (all-equalp name1 (vl-idexprlist->names lhses)))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected all ~
               lhses to deal with the same register, but found writes to ~&1."
         :args (list elem (mergesort (vl-idexprlist->names lhses)))
         :fatalp nil
         :fn __function__))

       ((unless (all-equalp width1 (vl-exprlist->finalwidths lhses)))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected all ~
               lhses to have the same width, but found writes with widths ~&1."
         :args (list elem (mergesort (vl-exprlist->finalwidths lhses)))
         :fatalp nil
         :fn __function__))

       (delays (vl-flopcodestmtlist->delays x))
       (delay1 (car delays))
       ((unless (all-equalp delay1 delays))
        (make-vl-warning
         :type :vl-flopcode-fail
         :msg "~a0: statement is too complex to synthesize.  Expected all ~
               assignments to ~w1 to have the same delay, but found delays ~
               of ~&2."
         :args (list elem name1 delays)
         :fatalp nil
         :fn __function__)))

    nil))
