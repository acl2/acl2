; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file represents work towards converting ACL2 source function
; remove-guard-holders from :program mode to guard-verified :logic mode.  Note
; that :logic mode ACL2 source functions must be guard-verified.

; Anyone is welcome to complete this work, BUT: first inform Matt Kaufmann,
; matthew.j.kaufmann@gmail.com, both to avoid potential duplication of effort
; and to ensure that Matt is available to complete integration of this work
; into ACL2.  The latter is especially important if you just ship Matt this and
; modified files, rather than going through the full process described in :doc
; verify-guards-for-system-functions and then either (a) sending Matt a tarball
; with the new and changed files and suitable instructions, or (b) going
; through the additional process described in :doc
; developers-guide-contributing.

; As of 12/23/2021 it was possible to LD this file successfully.  It's possible
; that the bulk of the work is done already, but there could be "gotchas" that
; surface when attempting to complete it.

; Each of the following functions calls the one just under it.  This isn't a
; complete call tree, but it gives some idea of where this work needs to go.

#|
remove-guard-holders
possibly-clean-up-dirty-lambda-objects
clean-up-dirty-lambda-objects
well-formed-lambda-objectp
well-formed-lambda-objectp1
executable-tamep [guard-verified below modulo skip-proofs, as noted below]
executable-badge [guard-verified below]
get-badge [guard-verified below]
|#

; I have left a couple of skip-proofs forms in this file in support of guard
; verification for executable-tamep.  They can be removed, I'm pretty sure, if
; we strengthen guards that call weak-badge-userfn-structure-alistp to call
; badge-userfn-structure-alistp instead.  That function will need to be
; defined, but it's trivial: just take the definition of
; weak-badge-userfn-structure-alistp and insist that the apply$-badge fields
; :arity and :out-arity are natps and the :ilks field is either t or a
; symbol-listp.  Perhaps it would make sense then to eliminate
; weak-badge-userfn-structure-alistp entirely and use the new
; badge-userfn-structure-alistp instead -- but existing books would then need t
; o be modified, notably books/system/remove-guard-holders-lemmas.lisp and
; books/system/remove-guard-holders.lisp.  Those may need to be modified
; regardless -- in fact books/system/remove-guard-holders.lisp should be
; renamed to books/system/remove-guard-holders-weak.lisp and then this file,
; remove-guard-holders-strong.lsp, should be made into a certified book named
; remove-guard-holders.lisp

(redef+)

(defun executable-badge (fn wrld)

; Find the badge, if any, for any fn in wrld; else return nil.  Aside from
; primitives and the apply$ boot functions, all badges are stored in the
; badge-table entry :badge-userfn-structure.

; Note: The word ``executable'' in the name means this function is executable,
; unlike its namesake, badge, which is just constrained.

; Aside: The apply$ primitives have badges stored in the *badge-prim-falist*.
; The apply$ boot functions have built-in badges as specified below.  All other
; badged functions are in the :badge-userfn-structure of the badge-table.  The
; apply$ primitives and boot functions do not have warrants and don't need
; them.  The functions in :badge-userfn-structure may or may not have warrants,
; depending on the warrantp flag of the entry for fn in the structure.  See the
; Essay on the Badge-Table.

; There's nothing wrong with putting this in logic mode but we don't need it in
; logic mode here.  This function is only used by defwarrant, to analyze and
; determine the badge, if any, of a newly submitted function, and in translate,
; to determine if a lambda body is legal.  (To be accurate, this function is
; called from several places, but all of them are in support of those two
; issues.)  Of course, the badge computed by a non-erroneous (defwarrant fn)
; is then built into the defun of APPLY$-WARRANT-fn and thus participates in
; logical reasoning; so the results computed by this function are used in
; proofs.

  (declare (xargs :mode :program
                  :guard (ilks-plist-worldp wrld)))
  (cond
   ((and (global-val 'boot-strap-flg wrld)
         (or (not (getpropc '*badge-prim-falist* 'const nil wrld))
             (not (getpropc 'badge-table 'table-guard nil wrld))))
    (er hard? 'executable-badge
        "It is illegal to call this function during boot strapping because ~
         primitives have not yet been identified and badges not yet ~
         computed!"))
   ((symbolp fn)
    (let* ((badge-prim-falist ; *badge-prim-falist* is not yet defined!
            (getpropc '*badge-prim-falist* 'const nil wrld))
           (temp (and (consp badge-prim-falist)       ; for guard verification
                      (consp (cdr badge-prim-falist)) ; for guard verification
                      (hons-get fn
                                (unquote badge-prim-falist)))))
      (cond
       ((consp temp) (cdr temp))
       ((eq fn 'BADGE) *generic-tame-badge-1*)
       ((eq fn 'TAMEP) *generic-tame-badge-1*)
       ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
       ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
       ((eq fn 'APPLY$) *apply$-badge*)
       ((eq fn 'EV$) *ev$-badge*)
       (t (get-badge fn wrld)))))
   (t nil)))

(redef-)

(defthm ilks-plist-worldp-implies-plist-worldp
  (implies (ilks-plist-worldp w)
           (plist-worldp w)))

(defthm alistp-badge-userfn-structure
  (implies
   (ilks-plist-worldp wrld)
   (and (alistp (fgetprop 'badge-table 'table-alist nil wrld))
        (alistp (cdr (assoc-equal :badge-userfn-structure
                                  (fgetprop 'badge-table 'table-alist nil
                                            wrld)))))))

(defthm weak-badge-userfn-structure-alistp-implies-consp-cdr-assoc-equal
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (cdr (assoc-equal fn alist)))
           (consp (cdr (assoc-equal fn alist)))))

(defthm weak-badge-userfn-structure-alistp-implies-alistp
  (implies (weak-badge-userfn-structure-alistp alist)
           (alistp alist)))

(defthm consp-assoc-equal-forced
  (implies (and (force (alistp l))
                (assoc-equal name l))
           (consp (assoc-equal name l))))

(defthm weak-badge-userfn-structure-alistp-implies-consp-cddr-assoc-equal
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (cddr (assoc-equal fn alist)))
           (consp (cddr (assoc-equal fn alist)))))

(verify-termination executable-badge ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

(defun apply$-badge-alistp (x)
  (declare (xargs :mode :logic :guard t))
  (cond ((atom x) (null x))
        (t (let ((pair (car x)))
             (and (consp pair)
                  (symbolp (car pair))
                  (apply$-badgep (cdr pair))
                  (apply$-badge-alistp (cdr x)))))))

(memoize 'apply$-badge-alistp) ; for efficiency

(defun good-badge-prim-falist-p (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((x (getpropc '*badge-prim-falist* 'const nil wrld)))
    (and (consp x)
         (consp (cdr x))
         (null (cddr x))
         (eq (car x) 'quote)
         (apply$-badge-alistp (cadr x)))))

(redef+)

(mutual-recursion

(defun executable-tamep (x wrld)
  (declare (xargs :mode :program
                  :measure (acl2-count x)
                  :guard (and (ilks-plist-worldp wrld)
                              (good-badge-prim-falist-p wrld))))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((bdg (executable-badge (car x) wrld)))
           (cond
            ((null bdg) nil)
            ((eq (access apply$-badge bdg :ilks) t)
             (executable-suitably-tamep-listp
              (access apply$-badge bdg :arity)
              nil
              (cdr x)
              wrld))
            (t (executable-suitably-tamep-listp
                (access apply$-badge bdg :arity)
                (access apply$-badge bdg :ilks)
                (cdr x)
                wrld)))))
        ((consp (car x))
         (let ((fn (car x)))
           (and (executable-tamep-lambdap fn wrld)
                (executable-suitably-tamep-listp (length (cadr fn))
; Given (tamep-lambdap fn), (cadr fn) = (lambda-object-formals fn).
                                                 nil
                                                 (cdr x)
                                                 wrld))))
        (t nil)))

(defun executable-tamep-functionp (fn wrld)
  (declare (xargs :mode :program
                  :measure (acl2-count fn)
                  :guard (and (ilks-plist-worldp wrld)
                              (good-badge-prim-falist-p wrld))))
  (if (symbolp fn)
      (let ((bdg (executable-badge fn wrld)))
        (and bdg
             (eq (access apply$-badge bdg :ilks)
                 t)))
    (and (consp fn)
         (executable-tamep-lambdap fn wrld))))

(defun executable-suitably-tamep-listp (n flags args wrld)
  (declare (xargs :mode :program
                  :measure (acl2-count args)
                  :guard (and (natp n)
                              (true-listp flags)
                              (ilks-plist-worldp wrld)
                              (good-badge-prim-falist-p wrld))))
  (cond
   ((zp n) (null args))
   ((atom args) nil)
   (t (and
       (let ((arg (car args)))
         (case (car flags)
           (:FN
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (executable-tamep-functionp (cadr arg) wrld)))
           (:EXPR
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (executable-tamep (cadr arg) wrld)))
           (otherwise
            (executable-tamep arg wrld))))
       (executable-suitably-tamep-listp (- n 1) (cdr flags) (cdr args) wrld)))))
)

(redef-)

(defthm executable-tamep-1
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cdr (hons-assoc-equal fn bpf)))
           (consp (cdr (hons-assoc-equal fn bpf)))))

(defthm executable-tamep-2
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cddr (hons-assoc-equal fn bpf)))
           (consp (cddr (hons-assoc-equal fn bpf)))))

(defthm executable-tamep-3
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cdddr (hons-assoc-equal fn bpf)))
           (consp (cdddr (hons-assoc-equal fn bpf)))))

(defthm executable-tamep-4
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (caddr (assoc-equal fn alist)))
           (consp (caddr (assoc-equal fn alist)))))

(defthm executable-tamep-5
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (cdr (caddr (assoc-equal fn alist))))
           (consp (cdr (caddr (assoc-equal fn alist))))))

(defthm executable-tamep-6
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (cddr (caddr (assoc-equal fn alist))))
           (consp (cddr (caddr (assoc-equal fn alist))))))

(defthm executable-tamep-7
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cdr (hons-assoc-equal fn bpf)))
           (integerp (caddr (hons-assoc-equal fn bpf)))))

(defthm executable-tamep-8
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cdr (hons-assoc-equal fn bpf)))
           (<= 0 (caddr (hons-assoc-equal fn bpf)))))

(defthm executable-tamep-9
; bpf is *badge-prim-falist* value
  (implies (and (apply$-badge-alistp bpf)
                (cdr (hons-assoc-equal fn bpf))
                (not (equal (cddddr (hons-assoc-equal fn bpf))
                            t)))
           (true-listp (cddddr (hons-assoc-equal fn bpf)))))

(skip-proofs ; need to strengthen weak-badge-userfn-structure-alistp
(defthm executable-tamep-10
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (caddr (assoc-equal fn alist)))
           (and (integerp (cadr (caddr (assoc-equal fn alist))))
                (<= 0 (cadr (caddr (assoc-equal fn alist)))))))
)

(skip-proofs ; need to strengthen weak-badge-userfn-structure-alistp
(defthm executable-tamep-11
  (implies (and (weak-badge-userfn-structure-alistp alist)
                (not (equal (cdddr (caddr (assoc-equal fn alist)))
                            t)))
           (true-listp (cdddr (caddr (assoc-equal fn alist))))))
)

(verify-termination executable-tamep ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))
