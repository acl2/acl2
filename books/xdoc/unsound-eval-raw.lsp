; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "ACL2")

(defun unsound-eval-fn (sexpr state)
  (unless (live-state-p state)
    ;; I think we don't want to trap this one; if we get called in logic mode
    ;; on a fake state, we really should cause an error.
    (error "Unsound-eval requires a live state."))
  (handler-case
   (b* (#+lispworks
        ;; (Mod by Matt K., 12/2013:)
        ;; LispWorks 6.1.1 has a bug that can prevent catching stack overflow
        ;; errors when system::*stack-overflow-behaviour* is nil, as it is in
        ;; ACL2.  We work around that bug as follows.
        (system::*stack-overflow-behaviour* t)
        ((mv err val state)
         ;; This with-guard-checking form seems necessary because otherwise, it
         ;; seems, trans-eval will just do whatever the default guard checking
         ;; mode is.  And, in some make-events, it appears that guard checking
         ;; gets disabled somehow.
         (with-guard-checking t
                              (trans-eval sexpr 'unsound-eval state t)))
        ((when err)
         (mv (msg "Failed to evaluate ~x0; trans eval failed? ~x1." sexpr err)
             nil state))
        ((unless (and (consp val)
                      (true-listp (car val))))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned unexpected value ~x1." sexpr val)
             nil state))
        (stobjs-out  (car val))
        (num-returns (length stobjs-out))
        ((unless (posp num-returns))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned malformed stobjs-out ~x1."
                  sexpr stobjs-out)
             nil state))
        ;; Trans-eval has a really weird interface.  In the singleton return
        ;; value case, it doesn't seem to wrap the return values in a list...
        (return-vals (if (eql num-returns 1)
                         (list (cdr val))
                       (cdr val)))
        ((unless (equal (len return-vals)
                        (len stobjs-out)))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned incoherent return values ~x1."
                  (list :stobjs-out stobjs-out
                        :return-vals return-vals))
             nil state)))
     (mv nil (unsound-eval-elide stobjs-out return-vals) state))
   (error
    (condition)
    (let ((condition-str (format nil "~S" condition)))
      (mv (msg "Failed to evaluate ~x0; ~s1" sexpr condition-str)
          nil state)))
   (storage-condition
    (condition)
    (let ((condition-str (format nil "~S" condition)))
      (mv (msg "Failed to evaluate ~x0; ~s1" sexpr condition-str)
          nil state)))))
