; This is just a convenient place to write debugging code.

; fvq bash
; ../bin/vl shell

(lp)
(redef!)
(set-ld-skip-proofsp t state)

(defconst *edgesynth-debug* t)

(defconst *loadconfig*
  (make-vl-loadconfig
   :start-files (list "fns2/spec.v")
   ))

(defconsts (*loadresult* state)
  (vl-load *loadconfig*))

(defconsts *simpconfig*
  (make-vl-simpconfig))




(def-vl-resolve-indexing vl-fundecl-resolve-indexing
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x)

       (- (vl-cw-ps-seq
           (vl-cw "------------------------~%Function: ~a0.~%~%" x)))

       ;; This is tricky because the function can have its own declarations.
       ((mv regdecls vardecls eventdecls paramdecls)
        (vl-filter-blockitems x.decls))

       ;; Remove any locally declared names from the global arrfal/wirefal
       ;; we've been given.  In practice, shadowed-names should be short
       ;; because most functions are pretty simple and don't have more than a
       ;; few variables.  So, I'm not worried about just using
       ;; set-difference-equal calls, here.
       (shadowed-names
        (mergesort (append (vl-regdecllist->names regdecls)
                           (vl-vardecllist->names vardecls)
                           (vl-eventdecllist->names eventdecls)
                           (vl-paramdecllist->names paramdecls))))
       (- (vl-cw-ps-seq
           (vl-cw "shadowed names: ~x0.~%" shadowed-names)))

       (visible-global-arrnames
        (set-difference-equal (alist-keys arrfal) shadowed-names))
       (visible-global-wirenames
        (set-difference-equal (alist-keys wirefal) shadowed-names))

       ;; It would probably be safe to turn indexing operations that are
       ;; selecting from most parameters and variables into bitselects.  But
       ;; for now we'll play it safe, and only really try to deal with
       ;; registers here.
       ((mv reg-arrays reg-wires)
        (vl-regdecllist-filter-arrays regdecls nil nil))

       ;; The function's inputs are also okay to turn into bit selects, because
       ;; they can't be arrays.
       (innames         (vl-taskportlist->names x.inputs))

       (local-arrnames  (append-without-guard reg-arrays
                                              visible-global-arrnames))
       (local-wirenames (append-without-guard reg-wires
                                              innames
                                              visible-global-wirenames))
       (local-arrfal    (make-lookup-alist local-arrnames))
       (local-wirefal   (make-lookup-alist local-wirenames))

       (- (cw "visible global arrnames: ~x0.~%" visible-global-arrnames))
       (- (cw "visible global wirenames: ~x0.~%" visible-global-wirenames))
       (- (cw "local arrnames: ~x0.~%" local-arrnames))
       (- (cw "local wirenames: ~x0.~%" local-wirenames))
       (- (cw "local arrfal: ~x0.~%" local-arrfal))
       (- (cw "local wirefal: ~x0.~%" local-wirefal))

       ((mv warnings new-body)
        (vl-stmt-resolve-indexing x.body local-arrfal local-wirefal warnings))
       (- (fast-alist-free local-arrfal))
       (- (fast-alist-free local-wirefal))
       (new-x (change-vl-fundecl x :body new-body)))
    (mv warnings new-x)))


(defconsts (*good* *bad* &)
  (vl-simplify (vl-loadresult->design *loadresult*) *simpconfig*))

(top-level
 (with-local-ps
  (let* ((all-mods (append (vl-design->mods *good*)
                           (vl-design->mods *bad*)))
         (mwalist (vl-origname-modwarningalist all-mods)))
    (vl-print-modwarningalist mwalist))))






