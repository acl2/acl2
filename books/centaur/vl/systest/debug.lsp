; This is just a convenient place to write debugging code.

; fvq bash
; ../bin/vl shell

(lp)
(redef!)
(set-ld-skip-proofsp t state)

(defconst *edgesynth-debug* t)

(defconst *loadconfig*
  (make-vl-loadconfig
   :start-files (list "async1/spec.v")
   ))

(defconsts (*loadresult* state)
  (vl-load *loadconfig*))

(defconsts *simpconfig*
  (make-vl-simpconfig))

(defconsts (*good* *bad* &)
  (vl-simplify (vl-loadresult->design *loadresult*) *simpconfig*))

(top-level
 (with-local-ps
  (let* ((all-mods (append (vl-design->mods *good*)
                           (vl-design->mods *bad*)))
         (mwalist (vl-origname-modwarningalist all-mods)))
    (vl-print-modwarningalist mwalist))))






