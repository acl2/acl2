; Hard error patch to ACL2, written by Matt Kaufmann

(in-package "ACL2")

; --------------- TEMPORARY ------- Patch to ACL2's error handling ------------

; new
(defvar *hard-error-is-error* nil)

; modified from ACL2 sources
(defun hard-error (ctx str alist)

; Logically, this function just returns nil.  The implementation
; usually signals a hard error, which is sound since it is akin to
; running out of stack or some other resource problem.

; But if this function is called as part of a proof, e.g.,
; (thm (equal (car (cons (hard-error 'ctx "Test" nil) y)) nil))
; we do not want to cause an error!  (Note:  the simpler example
; (thm (equal (hard-error 'ctx "Test" nil) nil)) can be proved
; without any special handling of the executable counterpart of
; hard-error, because we know its type-set is *ts-nil*.  So to cause
; an error, you have to have the hard-error term used in a place
; where type-reasoning alone won't do the job.)

; Sometimes hard-error is used in the guard of a function, e.g.,
; illegal.  Generally evaluating that guard is to signal an error.
; But if guard-checking-on is nil, then we want to cause no error and
; just let the guard return nil.  We evaluate the guard even when
; guard-checking-on is nil (though not for user-defined functions when
; it is :none) so we know whether to call the raw Lisp version or the
; ACL2_*1*_ACL2 version of a function.

; Logically speaking the two behaviors of hard-error, nil or error,
; are indistinguishable.  So we can choose which behavior we want
; without soundness concerns.  Therefore, we have a raw Lisp special
; variable, named *hard-error-returns-nilp*, and if it is true, we
; return nil.  It is up to the environment to somehow set that special
; variable.

; In ev-fncall we provide the argument hard-error-returns-nilp which
; is used as the binding of *hard-error-returns-nil* when we invoke
; the raw code.  This also infects ev and the other functions in the
; ev-fncall clique, namely ev-lst and ev-acl2-unwind-protect.  It is
; up to the user of ev-fncall to specify which behavior is desired.
; Generally speaking, that argument of ev-fncall is set to t in those
; calls of ev-fncall that are from within the theorem prover and on
; terms from the conjecture being proved.  Secondly, (up to
; Version_2.5) in oneify-cltl-code and oneify-cltl-code, when we
; generated the ACL2_*1*_ACL2 code for a function, we laid down a
; binding for *hard-error-returns-nil*.  That binding is in effect
; just when we evaluate the guard of the function.  The binding is t
; if either it was already (meaning somebody above us has asked for
; hard-error to be treated this way) or if guard checking is turned
; off.

; See the comment after ILLEGAL (below) for a discussion of an
; earlier, inadequate handling of these issues.

  (declare (xargs :guard t))
  #-acl2-loop-only
  (when (not *hard-error-returns-nilp*)

; We are going to ``cause an error.''  We print an error message with error-fms
; even though we do not have state.  To do that, we must bind *wormholep* to
; nil so we don't try to push undo information (or, in the case of error-fms,
; cause an error for illegal state changes).  If error-fms could evaluate arbitrary
; forms, e.g., to make legal state changes while in wormholes, then this would be
; a BAD IDEA.  But error-fms only prints stuff that was created earlier (and passed
; in via alist).

    (cond
     (*hard-error-is-error* (error "ACL2 hard-error: ~s"
                                   (list ctx str alist)))
     (t
      (cond ((fboundp 'acl2::error-fms)               ;;; Print a msg
             (let ((*standard-output* *error-output*) ;;; one way ...
                   (*wormholep* nil)
                   (fn 'acl2::error-fms))
               (funcall fn t ctx str alist *the-live-state*)))
            (t (print (list ctx str alist) *error-output*))) ;;; or another.

; Once upon a time hard-error took a throw-flg argument and did the
; following throw-raw-ev-fncall only if the throw-flg was t.  Otherwise,
; it signalled an interface-er.  Note that in either case it behaved like
; an error -- interface-er's are rougher because they do not leave you in
; the ACL2 command loop.  I think this aspect of the old code was a vestige
; of the pre-*ld-level* days when we didn't know if we could throw or not.

      (throw-raw-ev-fncall 'illegal))))
  #+acl2-loop-only
  (declare (ignore ctx str alist))
  nil)


