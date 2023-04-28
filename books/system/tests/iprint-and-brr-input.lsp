; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; There are some calls of acl2-query that read from *standard-oi*.  So we
; redefine that input channel to be the current value of 'standard-oi.  There
; is also output printed to the comment window.  So we redirect that output to
; the current value of 'standard-co.

(defconst *old-standard-oi* *standard-oi*)
(redef+)
(make-event `(defconst *standard-oi* ',(standard-oi state)))
(make-event `(defconst *standard-co* ',(standard-co state)))
(redef-)

;;;;;;;;;;

(monitor! 'len t)
(set-evisc-tuple (evisc-tuple 5 6 nil nil) :iprint :same :sites :all)
(mv-let (step-limit term ttree)
  (rewrite '(len (cons a b))
            nil 1 20 100 nil '? nil nil (w state)
            state nil nil nil nil
            (make-rcnst (ens state) (w state) state
                        :force-info t)
            nil nil)
  (declare (ignore step-limit term ttree))
  (make-list 10))
(set-iprint t)
(cw "~X01" (make-list 8) (evisc-tuple 5 6 nil nil))
:go
:go ; exits the break-rewrite loop, creating #@2#
; NOTE: At this point, both in Version 8.5 and after a fix on 2/25/2023
; (git commit 69912ed4ef),
; then instead of
; (NIL NIL NIL NIL NIL NIL . #@2#)
; being printed at this point, we got:
; (NIL NIL NIL NIL NIL NIL . #@2#)

; creates #@3#:
(assert-event (equal '(NIL NIL NIL NIL NIL NIL . #@1#)
                     (make-list 8)))
; creates #@4#:
(assert-event (equal '(NIL NIL NIL NIL NIL NIL . #@2#)
                     (make-list 10)))

;;;;;;;;;;

(set-iprint t) ; should be no-op

; creates #@5#:
(mv-let (step-limit term ttree)
  (rewrite '(len (cons a b))
            nil 1 20 100 nil '? nil nil (w state)
            state nil nil nil nil
            (make-rcnst (ens state) (w state) state
                        :force-info t)
            nil nil)
  (declare (ignore step-limit term ttree))
  (make-list 10))
; creates #@6#:
(cw "~X01" (make-list 8) (evisc-tuple 5 6 nil nil))
:go
:go ; exits the break-rewrite loop, creating #@7#
; NOTE: In Version 8.5, at this point, the iprint index that appears here
; already appeared in the break-rewrite loop above.  (That problem didn't occur
; with the fix made on 2/25/2023 (git commit 69912ed4ef.)

; creates #@8#:
(assert-event (equal '(NIL NIL NIL NIL NIL NIL . #@6#)
                     (make-list 8)))

; creates #@9#:
(assert-event (equal '(NIL NIL NIL NIL NIL NIL . #@7#)
                     (make-list 10)))

;;;;;;;;;;

(redef+)
(defconst *standard-oi* *old-standard-oi*)
(redef-)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
