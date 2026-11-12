; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; Proof of NIL: memoize-partial's raw definition also captures recursive calls
; inside LOOP$ bodies.
;
; The Essay on Memoization with Partial Functions (other-events.lisp) runs the
; memoized F as the body of F-LIMIT with the limit bound to 0, inside an FLET
; that redirects every call of F-LIMIT to F.  Its Key Claim needs every call of
; F-LIMIT in the body to have the limit variable as last argument, and the table
; guard checks this on the translated body (free-exactly-in-last-arg-of-calls).
; But that check treats quoted constants as opaque, so a recursive call inside
; a LOOP$ body (translated into a quoted LAMBDA for COLLECT$) is not checked.
; In raw Lisp with *aokp* t (the top level), LOOP$ expands into a CL LOOP that
; is lexically inside the FLET, so (f-limit 0 e) runs (f 0) = 'zero, whereas
; logically (and in the evaluation theory, with the warrant) it is
; (f-limit 0 0) = 'base.  So (f 1) evaluates to '(zero (zero)) at the top level
; although even with the warrant it is '(zero (base)).
;
; That value reaches proofs through F's memo table (default :aokp nil): the
; CL LOOP path calls no warranted function and no attachment (only the FLET-local
; function), so nothing marks the value as attachment- or warrant-dependent and
; it is stored; the prover later reads it.  (S-8's further evidence is the
; related case of a raw LOOP$ calling warranted functions; here the stored value
; is wrong even in the evaluation theory.)
;
; Each encapsulate below does this with a LOCAL F-LIMIT whose N=0 value is
; 'zero or 'other, and exports what this says about the quoted LAMBDA of the
; LOOP$ (which mentions F-LIMIT only as data); the two exports contradict.
;
; Verified on master 21aaad6 with SBCL and CCL (ld); also certifies as a book
; (SBCL), and NIL follows from the included book.
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)
(defconst *lam*
; The quoted lambda of the loop$ below, as it occurs in the stored body of
; F-LIMIT (both local definitions of F-LIMIT below produce the same one).
  '(LAMBDA (LOOP$-IVAR)
     (RETURN-LAST 'PROGN
                  '(LAMBDA$ (LOOP$-IVAR)
                     (DECLARE (TYPE (INTEGER 0 *) LOOP$-IVAR))
                     (LET ((E LOOP$-IVAR))
                       (DECLARE (IGNORABLE E))
                       (F-LIMIT 0 E)))
                  ((LAMBDA (E) (F-LIMIT '0 E))
                   LOOP$-IVAR))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  ()
  (local
   (defun f-limit (n limit)
     (declare (type (integer 0 *) limit))
     (declare (xargs :guard (natp n) :measure (nfix limit) :loop$-recursion t
                     :verify-guards nil))
     (if (zp limit)
         'base
       (let ((limit (1- limit)))
         (if (zp n)
             'zero
           (list (f-limit (1- n) limit)
                 (loop$ for e of-type (integer 0 *) in '(0)
                        collect (f-limit 0 e))))))))
  (local (defwarrant f-limit))
  (local (verify-guards f-limit))

  (must-fail ; This must-fail wrapper was added by Matt K.
  (local (memoize-partial ((f f-limit))))
  )

; The following were commented out by Matt K. since the event just above now
; fails.
#|
; Top-level evaluation runs the raw definition of F, in which the flet that
; redirects recursive calls of F-LIMIT to F also captures the call inside the
; loop$ body, although its last argument is E, not the limit.
  (local (value-triple (f 1)))
  (local (defthm f-1 (equal (f 1) '(zero (zero))) :rule-classes nil))
  (local (defthm f-def
           (equal (f 1) (f-limit 1 (f-limit-stable 1)))
           :hints (("Goal" :in-theory (disable (:e f)) :expand ((f 1))))
           :rule-classes nil))
  (local (defthm f-limit-zp
           (implies (zp s) (equal (f-limit 1 s) 'base))
           :hints (("Goal" :expand ((f-limit 1 s))))
           :rule-classes nil))
  (local (defthm cadr-f-limit
           (implies (not (zp s))
                    (equal (cadr (f-limit 1 s)) (collect$ *lam* '(0))))
           :hints (("Goal" :expand ((f-limit 1 s))
                    :in-theory (disable collect$ (:e collect$) collect$-singleton apply$-f-limit (:e rewrite-lambda-modep))))
           :rule-classes nil))
  (defthm thm-a (equal (collect$ *lam* '(0)) '(zero))
    :hints (("Goal" :use (f-1 f-def
                          (:instance f-limit-zp (s (f-limit-stable 1)))
                          (:instance cadr-f-limit (s (f-limit-stable 1))))
             :in-theory (disable f (:e f) f-limit (:e f-limit)
                                 collect$ (:e collect$) apply$-f-limit (:e rewrite-lambda-modep))))
    :rule-classes nil)
|#
  )

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(encapsulate
  ()
  (local
   (defun f-limit (n limit)
     (declare (type (integer 0 *) limit))
     (declare (xargs :guard (natp n) :measure (nfix limit) :loop$-recursion t
                     :verify-guards nil))
     (if (zp limit)
         'base
       (let ((limit (1- limit)))
         (if (zp n)
             'other
           (list (f-limit (1- n) limit)
                 (loop$ for e of-type (integer 0 *) in '(0)
                        collect (f-limit 0 e))))))))
  (local (defwarrant f-limit))
  (local (verify-guards f-limit))
  (local (memoize-partial ((f f-limit))))
; Top-level evaluation runs the raw definition of F, in which the flet that
; redirects recursive calls of F-LIMIT to F also captures the call inside the
; loop$ body, although its last argument is E, not the limit.
  (local (value-triple (f 1)))
  (local (defthm f-1 (equal (f 1) '(other (other))) :rule-classes nil))
  (local (defthm f-def
           (equal (f 1) (f-limit 1 (f-limit-stable 1)))
           :hints (("Goal" :in-theory (disable (:e f)) :expand ((f 1))))
           :rule-classes nil))
  (local (defthm f-limit-zp
           (implies (zp s) (equal (f-limit 1 s) 'base))
           :hints (("Goal" :expand ((f-limit 1 s))))
           :rule-classes nil))
  (local (defthm cadr-f-limit
           (implies (not (zp s))
                    (equal (cadr (f-limit 1 s)) (collect$ *lam* '(0))))
           :hints (("Goal" :expand ((f-limit 1 s))
                    :in-theory (disable collect$ (:e collect$) collect$-singleton apply$-f-limit (:e rewrite-lambda-modep))))
           :rule-classes nil))
  (defthm thm-b (equal (collect$ *lam* '(0)) '(other))
    :hints (("Goal" :use (f-1 f-def
                          (:instance f-limit-zp (s (f-limit-stable 1)))
                          (:instance cadr-f-limit (s (f-limit-stable 1))))
             :in-theory (disable f (:e f) f-limit (:e f-limit)
                                 collect$ (:e collect$) apply$-f-limit (:e rewrite-lambda-modep))))
    :rule-classes nil))

(defthm contradiction nil
  :hints (("Goal" :use (thm-a thm-b)))
  :rule-classes nil)
(value-triple (cw "~%NIL-PROVED~%"))
|#
