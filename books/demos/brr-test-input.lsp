; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; There are some calls of acl2-query that read from *standard-oi*.  So we
; redefine that input channel to be the current value of 'standard-oi.  There
; is also output printed to the comment window.  So we redirect that output to
; the current value of 'standard-co.  We also redefine set-ld-prompt so that it
; sets ld-pre-eval-print to t (in brr) so that brr commands that are read are
; printed out.

(defconst *old-standard-oi* *standard-oi*)
(redef+)
(make-event `(defconst *standard-oi* ',(standard-oi state)))
(make-event `(defconst *standard-co* ',(standard-co state)))

(defun set-ld-prompt (val state)
  (er-progn
   (chk-ld-prompt val 'set-ld-prompt state)
   (if (eq val 'brr-prompt)
       (set-ld-pre-eval-print t state)
     (value nil))
   (pprogn
    (f-put-global 'ld-prompt val state)
    (value val))))

(redef-)

; Each scenario below tests interactions with break-rewrite.  They are
; separated by a line of hyphens.  We can't test the brr abort command :a! with
; run-script.

; -----------------------------------------------------------------
; Setup

; We first set up these tests by arranging for four rules to chain together
; to prove

; (efn x) -> (afn x)

; by proving

; (efn x) -> (dfn x) -> (cfn x) -> (bfn x) -> (afn x)

; This is in fact the encapsulate displayed in the Sample Script discussed in
; the Essay on Break-Rewrite.

(encapsulate ((afn (x) t)
              (bfn (x) t)
              (cfn (x) t)
              (dfn (x) t)
              (efn (x) t))
  (local (defun afn (x) (declare (ignore x)) t))
  (local (defun bfn (x) (declare (ignore x)) t))
  (local (defun cfn (x) (declare (ignore x)) t))
  (local (defun dfn (x) (declare (ignore x)) t))
  (local (defun efn (x) (declare (ignore x)) t))
  (defthm a (implies (bfn x)(afn x)))
  (defthm b (implies (cfn x)(bfn x)))
  (defthm c (implies (dfn x)(cfn x)))
  (defthm d (implies (efn x)(dfn x)))
  )

(brr t)

; Do not undo this encapsulate or this (brr t)!  The various scenarios do not
; necessarily use all or even any of these rules!  But it is important that
; these rules remain in place because some tests use them and others don't!

; Otherwise, we start every scenario with a ``standard reset'' in which we
; unmonitor all rules, set all the evisc tuples appropriately for the coming
; test, and :reset the iprint to nil.  The idea is that except for the
; existence of the rules introduced by this encapsulate and the enabling of
; brr, the initial state of every scenario is explicitly set at the beginning
; of each scenario.

; -----------------------------------------------------------------
(quote (scenario 1))
; The Scenario in the Essay on Break-Rewrite

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

; This next function checks that the brr wormhole is coherent, i.e., when in
; the brr wormhole, the status found in the hidden memory is equal to the
; status found in the ``cache.''  See :doc wormhole-programming-tips.  The brr
; wormhole is always coherent.  The only reason we define this function is to
; show you what we mean by ``memory'' and ``cache'' in this context.
 
(defun brr-coherentp (state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (eq (f-get-global 'wormhole-name state) 'brr)
      (er-let* 
          ((persistent-whs (get-persistent-whs 'brr state))
           (ephemeral-whs (value (f-get-global 'wormhole-status state))))
        (value (equal persistent-whs ephemeral-whs)))
      (value t)))

; We now install a monitor on rule A.
(monitor 'a t)

; Here is the test of the Sample Scenario from the Essay on Break-Rewrite.  The
; calls of print-brr-status and brr-coherentp are completely unnecessary from
; the perspective of using break-rewrite.  We just include them to help teach
; you about the implementation.  The Essay on Break-Rewrite contains a
; commentary describing what is happening, line by line.  Unfortunately, the
; line numbers aren't printed in the output file.

(thm (implies (efn x) (afn x))) ; [ 0]
:target                         ; [ 1]
:path                           ; [ 2]
(print-brr-status t)            ; [ 3]
(brr-coherentp state)           ; [ 4]
(monitor 'b t)                  ; [ 5]
(print-brr-status t)            ; [ 6]
(monitored-runes)               ; [ 7]
:eval                           ; [ 8]
(print-brr-status t)            ; [ 9]
:ok                             ; [10]
(print-brr-status t)            ; [11]
:ok                             ; [12]
(print-brr-status t)            ; [13]

; -----------------------------------------------------------------
(quote (scenario 2))
; Exploring coherence with a user wormhole

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

(defun demo-wormhole-coherentp (state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (eq (f-get-global 'wormhole-name state) 'demo)
      (er-let* 
          ((persistent-whs (get-persistent-whs 'demo state))
           (ephemeral-whs (value (f-get-global 'wormhole-status state))))
        (value (equal persistent-whs ephemeral-whs)))
      (value t)))

(wormhole-eval 'demo '(lambda () '(:enter . 0)) nil)
(wormhole 'demo '(lambda (whs) whs) nil '(quote (welcome to demo wormhole)))
(demo-wormhole-coherentp state)
(wormhole-eval 'demo '(lambda () '(:enter . 1)) nil) ; renders demo incoherent
(demo-wormhole-coherentp state)
(f-get-global 'wormhole-status state)
(get-persistent-whs 'demo state)
(value :q) ; moves cached wormhole-status to memory
(wormhole 'demo '(lambda (whs) whs) nil '(quote (welcome back to demo wormhole)))
(f-get-global 'wormhole-status state) ; (:enter . 0), not (:enter . 1)
(demo-wormhole-coherentp state)
(set-persistent-whs-and-ephemeral-whs 'demo '(:enter . 2) state) ; preserves coherence
(demo-wormhole-coherentp state)
(f-get-global 'wormhole-status state)
(get-persistent-whs 'demo state)
(value :q)

; -----------------------------------------------------------------
(quote (scenario 3))

; Testing go$ and eval$

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

:monitor a t
(thm (implies (efn x) (afn x)))
:go$ b
:target
:eval$ c
:target
:ok$ d
:target
:monitored-runes
:ok
:monitored-runes
:ok
:monitored-runes

; -----------------------------------------------------------------
(quote (scenario 4))
; Testing go!

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)


:monitor a t
(thm (implies (efn x) (afn x)))
:monitor b t
:monitor c t
:monitor d t
:go!
:monitored-runes

; -----------------------------------------------------------------
(quote (scenario 5))

; Testing re-entrant calls of break-rewrite (once upon a time, this
; test caused brr depth to be wrong -- so the prompt was wrong -- and the test
; also lost track of :monitored-runes)

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

:monitor a t
(thm (implies (efn x) (afn x)))
:monitor b t
:unmonitor a
(thm (and (implies (efn y) (afn y)) (implies (efn z) (afn z))))
:monitored-runes
:go! ; from Subgoal 2 of interior thm
:monitored-runes
:go! ; from Subgoal 1 of interior thm
:monitored-runes
:go! ; from original thm
:monitored-runes

; -----------------------------------------------------------------
(quote (scenario 6))

; Testing brr-evisc-tuple with re-entrant calls of break-rewrite

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

:monitor a t
(defconst *tenx* '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))
(defconst *teny* '(y1 y2 y3 y4 y5 y6 y7 y8 y9 y10))
(defconst *tenz* '(z1 z2 z3 z4 z5 z6 z7 z8 z9 z10))
(set-evisc-tuple (evisc-tuple nil 9 nil nil) :sites :brr :iprint :same)
; The above brr evisc-tuple will cause the constants above to be printed fully
; up through the 9th (1 based) element.  So you can look at the quoted values
; and tell what evisc tuple is being used as we reset brr-evisc-tuple.
(thm (implies (efn *tenx*) (afn *tenx*)))
(thm (and (implies (efn *teny*) (afn *teny*)) (implies (efn *tenz*) (afn *tenz*))))
(set-evisc-tuple (evisc-tuple nil 7 nil nil) :sites :brr :iprint :same)
:go! ; from Subgoal 2 of interior thm
(set-evisc-tuple (evisc-tuple nil 5 nil nil) :sites :brr :iprint :same)
:go! ; from Subgoal 1 of interior thm
:target
:go! ; from original thm
(thm (implies (efn *tenx*) (afn *tenx*)))
:go!

; -----------------------------------------------------------------
(quote (scenario 7))

; This test exposes failure to track iprint correctly!

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

(monitor 'len t)
(set-evisc-tuple (evisc-tuple nil 10 nil nil) :sites :all :iprint :reset)
(iprint-enabledp state)
(f-get-global 'iprint-ar state)
(mv-let (step-limit term ttree)
  (rewrite '(len (cons a b))
           nil 1 20 100 nil '? nil nil (w state)
           state nil nil nil nil
           (make-rcnst (ens state) (w state) state
                       :force-info t)
           nil nil)
  (declare (ignore step-limit term ttree))
  (make-list 10))
(set-evisc-tuple (evisc-tuple 1 2 nil nil) :sites :all :iprint t) ; IPRINT on!
:go!
(make-list 10)

; -----------------------------------------------------------------
(quote (scenario 8)) ; A test similar to scenario 7, but using thm

; Standard Reset:
(unmonitor :all)
(set-evisc-tuple :default :sites :all :iprint :reset)

(monitor 'len t)
(set-evisc-tuple (evisc-tuple nil 10 nil nil) :sites :all :iprint :reset)
(iprint-enabledp state)
(f-get-global 'iprint-ar state)
(er-progn
 (thm (equal (len (cons a b)) (+ 1 (len b))))
 (value (make-list 10)))
(set-evisc-tuple (evisc-tuple 1 2 nil nil) :sites :all :iprint t) ; IPRINT on!
:go!
(make-list 10)
:ok
(make-list 10)

;;;;;;;;;;

(redef+)
(defconst *standard-oi* *old-standard-oi*)
(redef-)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
