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
(include-book "../mods/lhs")
(include-book "../svex/select")
(include-book "std/util/defmapappend" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


 ;; stmt ::= (assign lhs rhs)
 ;;             ;; lhs is an svex expression
 ;;             ;; rhs is an svex expression
 ;;        || (if cond stmts stmts)
 ;;             ;; cond is an svex expression

 ;; got rid of this for now:
 ;;        || (block name locals stmts)

 ;; stmts ::= stmt list

(defxdoc svstmt.lisp :parents (svstmt))
(local (xdoc::set-default-parents svstmt.lisp))

(defenum svjump-p (:break :continue :return))

(defprod svstmt-write
  ((lhs svex-select-p)
   (rhs svex))
  :layout :tree)

(deflist svstmt-writelist :elt-type svstmt-write)

(deftypes svstmt
  (fty::deftagsum svstmt
    :parents (sv)
    :short "An @(see svex)-based representation for procedural statement blocks"
    (:assign
     ((writes svstmt-writelist)
      (blockingp booleanp :default t))
     :layout :tree)
    (:if
     ((cond svex)
      (then svstmtlist)
      (else svstmtlist))
     :layout :tree)
    (:xcond
     ((cond svex)
      (body svstmtlist)))
    (:while
     ((cond svex)
      (body svstmtlist)
      (next svstmtlist
            "Increment of a for loop.  When running a while loop we always check
             the condition, then run the body, then run the next, then recur. 
             But if there is a continue statement, we need to jump to after the
             body but before the next, because in a for loop the increment still
             happens after a continue.")))
    (:constraints
     ((constraints constraintlist-p)))
    (:scope
     ((locals svarlist)
      (body svstmtlist)))
    ;; Note: 'return foo' gets translated as 'assign fnname = foo; return'
    (:jump 
     ((type svjump-p
            :rule-classes
            (:rewrite
             (:forward-chaining :trigger-terms ((svstmt-jump->type x))))))))
  (deflist svstmtlist :elt-type svstmt :true-listp nil :elementp-of-nil nil))


(local (defthm svarlist-p-of-remove-equal
         (implies (svarlist-p x)
                  (svarlist-p (remove-equal k x)))))

(define svstmt-write-vars ((x svstmt-write-p))
  :returns (vars svarlist-p)
  (b* (((svstmt-write x)))
    (append-without-guard (svex-select-vars x.lhs)
                          (svex-vars x.rhs))))

(define svstmt-writelist-vars ((x svstmt-writelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append-without-guard (svstmt-write-vars (car x))
                          (svstmt-writelist-vars (cdr x)))))


(defines svstmt-vars
  (define svstmt-vars ((x svstmt-p))
    :verify-guards nil
    :returns (vars svarlist-p)
    :measure (svstmt-count x)
    (svstmt-case x
      :assign (svstmt-writelist-vars x.writes)
      :if (append-without-guard
           (svex-vars x.cond)
           (svstmtlist-vars x.then)
           (svstmtlist-vars x.else))
      :while (append-without-guard
              (svex-vars x.cond)
              (svstmtlist-vars x.body)
              (svstmtlist-vars x.next))
      :xcond (append-without-guard
              (svex-vars x.cond)
              (svstmtlist-vars x.body))
      :constraints (constraintlist-vars x.constraints)
      :scope (append-without-guard
              (svarlist-fix x.locals)
              (svstmtlist-vars x.body))
      :otherwise nil))
  (define svstmtlist-vars ((x svstmtlist-p))
    :returns (vars svarlist-p)
    :measure (svstmtlist-count x)
    (if (atom x)
        nil
      (append-without-guard
       (svstmt-vars (car x))
       (svstmtlist-vars (cdr x)))))
  ///
  (verify-guards svstmt-vars)
  (deffixequiv-mutual svstmt-vars)

  (std::defmapappend svstmtlist-vars (x)
    :guard (svsmtlist-p x)
    (svstmt-vars x)
    :already-definedp t)

  (defthm svstmt-vars-of-assign
    (equal (svstmt-vars (svstmt-assign writes blockingp))
           (svstmt-writelist-vars writes)))

  (defthm svstmt-vars-of-if
    (equal (svstmt-vars (svstmt-if cond then else))
           (append (svex-vars cond)
                   (svstmtlist-vars then)
                   (svstmtlist-vars else)))
    :hints (("goal" :expand ((svstmt-vars (svstmt-if cond then else))))))

  (defthm svstmt-vars-of-while
    (equal (svstmt-vars (svstmt-while cond body next))
           (append (svex-vars cond)
                   (svstmtlist-vars body)
                   (svstmtlist-vars next)))
    :hints (("goal" :expand ((svstmt-vars (svstmt-while cond body next))))))

  (defthm svstmt-vars-of-xcond
    (equal (svstmt-vars (svstmt-xcond cond body))
           (append (svex-vars cond)
                   (svstmtlist-vars body)))
    :hints (("goal" :expand ((svstmt-vars (svstmt-xcond cond body))))))

  (defthm svstmt-vars-of-constraint
    (equal (svstmt-vars (svstmt-constraints constraints))
           (constraintlist-vars constraints))
    :hints (("goal" :expand ((svstmt-vars (svstmt-constraints constraints))))))

  (defthm svstmt-vars-of-scope
    (equal (svstmt-vars (svstmt-scope locals body))
           (append (svarlist-fix locals)
                   (svstmtlist-vars body)))
    :hints (("goal" :expand ((svstmt-vars (svstmt-scope locals body)))))))

