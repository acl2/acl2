; This is just a convenient place to write debugging code.

; fvq bash
; ../bin/vl shell

(lp)
(redef!)
(set-ld-skip-proofsp t state)

(defmacro trace-parser (fn)
  `(trace$ (,fn
            :entry (list ',fn
                         ;;:tokens (vl-tokenlist->string-with-spaces tokens)
                         ;;:warnings (len warnings)
                         )
            :exit (list :errmsg (first values)
                        :val (second values)
                        ;; :remainder (vl-tokenlist->string-with-spaces
                        ;;             (third values))
                        ;; :next-token (and (consp (third values))
                        ;;                  (vl-token->type (car (third values))))
                        ;; :warnings (len (fourth values))
                        ))))
(untrace$)

(trace-parser vl-parse-port-declaration-noatts-fn)
(trace-parser vl-parse-port-declaration-atts-fn)
(trace-parser vl-parse-basic-port-declaration-tail)


(defconst *edgesynth-debug* t)
(defconst *vl-unparam-debug* t)

(defconst *loadconfig*
  (make-vl-loadconfig
   :start-files (list "param2/spec.v")
   :search-path (list "param2/")
   ))

(defconst *loadconfig*
  (make-vl-loadconfig
   :start-files (list "gates/spec.v")
   ))

(defconsts (*loadresult* state)
  (vl-load *loadconfig*))



(top-level
 (with-local-ps
   (vl-pp-modulelist (vl-design->mods (vl-loadresult->design *loadresult*)))))



(untrace$)
(trace$ (vl-parse-port-declaration-noatts-fn
         :entry nil
         :exit (list (second acl2::values))))


(defconsts *simpconfig*
  (make-vl-simpconfig))

(defconsts (*good* *bad* &)
  (vl-simplify (vl-loadresult->design *loadresult*) *simpconfig*))

(top-level
 (with-local-ps
   (vl-print-reportcard (vl-design-reportcard *good*))))

(top-level
 (with-local-ps
   (vl-print-reportcard (vl-design-reportcard *bad*))))

(car (vl-design->mods *bad*))


(vl-pps-modulelist
 (vl-design->mods (vl-annotate-design (vl-loadresult->design *loadresult*))))

(vl-pps-modulelist
 (vl-design->mods *good*))

(vl-pps-modulelist
 (vl-design->mods *bad*))

(defconsts (*pre* state)
  (sneaky-load :pre-unparam state))

(vl-pps-modulelist (vl-design->mods *pre*))


(define vl-design-unparameterize
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (;; Throw out modules that have problems with shadowed parameters.
       (- (sneaky-save :pre-unparam x))
       ((vl-design x) (vl-design-unparam-check x))
       ((unless (uniquep (vl-modulelist->names x.mods)))
        (raise "Programming error: module names are not unique.")
        x)
       (new-mods (vl-modulelist-unparameterize x.mods 1000))

       ;; Just to be absolutely certain this can't happen:
       ((unless (mbt (uniquep (vl-modulelist->names new-mods))))
        (impossible)
        x)

       (- (clear-memoize-table 'vl-create-unparameterized-module))
       (- (cw "; vl-unparameterize: ~x0 => ~x1 modules.~%" (len x.mods) (len new-mods)))
       (ans (change-vl-design x :mods new-mods))
       (- (sneaky-save :post-unparam ans)))
    ans))






(define vl-design-caseelim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (- (sneaky-save :pre-caseelim x))
       (ans (change-vl-design x :mods (vl-modulelist-caseelim x.mods)))
       (- (sneaky-save :post-caseelim ans)))
    ans))

(define vl-design-elim-unused-vars
  :short "Top-level @(see elim-unused-vars) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (- (sneaky-save :pre-unused x))
       (ans (change-vl-design x
                              :mods (vl-modulelist-elim-unused-vars x.mods)))
       (- (sneaky-save :post-unused x)))
    ans))

(defconsts (*pre-un* state) (sneaky-load :pre-unused state))
(defconsts (*post-un* state) (sneaky-load :post-unused state))

(vl-pps-modulelist (vl-design->mods *pre-un*))


(defconsts (*des* state)
  (sneaky-load :post-caseelim state))

(vl-pps-modulelist (vl-design->mods *des*))
(vl-pps-modulelist (vl-design->mods *bad*))











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


