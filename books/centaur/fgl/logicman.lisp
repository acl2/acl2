 ; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

;; Critpath: include aignet/semantics and move logic-building functions to separate book
(include-book "centaur/aignet/construction" :dir :system)
;; Critpath: factor out sat-lits stobj definition from aignet/cnf and include that + ipasir-logic instead
(include-book "centaur/aignet/ipasir" :dir :system)
;; (include-book "bvar-db")
(include-book "bfr")
(include-book "arith-base")
(include-book "syntax-bind")
;; (include-book "pathcond-stobj")
(include-book "defapply")
(include-book "std/stobjs/nicestobj" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(local (include-book "theory"))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/util/termhints" :dir :system))

(acl2::defstobj-clone u32arr aignet::u32arr :pkg fgl-fgl)
(acl2::defstobj-clone ipasir ipasir::ipasir :pkg fgl-fgl)
(acl2::defstobj-clone sat-lits aignet::sat-lits :pkg fgl-fgl)
(acl2::defstobj-clone strash aignet::strash :pkg fgl-fgl)

(stobjs::defnicestobj logicman
  (aignet :type aignet)
  (strash :type strash)
  (ipasir :type (array ipasir (0)) :resizable t)
  (sat-lits :type (array sat-lits (0)) :resizable t)
  (mode :type (satisfies bfr-mode-p) :pred bfr-mode-p :fix bfr-mode-fix :initially 0)
  (aignet-refcounts :type u32arr)
  (refcounts-index :type (integer 0 *) :pred natp :fix nfix :initially 0))

(local (in-theory (disable aignet::aignetp
                           aignet::strashp
                           ipasir::ipasirp
                           aignet::sat-litsp
                           aignet::u32arrp)))


(defthmd logicman->ipasiri-of-resize
  (equal (logicman->ipasiri n (resize-logicman->ipasir size logicman))
         (cond ((and (< (nfix n) (logicman->ipasir-length logicman))
                     (< (nfix n) (nfix size)))
                (logicman->ipasiri n logicman))
               ((< (nfix n) (nfix size))
                (ipasir::create-ipasir))
               (t nil)))
  :hints(("Goal" :in-theory (enable logicman->ipasiri
                                    resize-logicman->ipasir
                                    logicman->ipasir-length))))

(defthmd logicman->sat-litsi-of-resize
  (equal (logicman->sat-litsi n (resize-logicman->sat-lits size logicman))
         (cond ((and (< (nfix n) (logicman->sat-lits-length logicman))
                     (< (nfix n) (nfix size)))
                (logicman->sat-litsi n logicman))
               ((< (nfix n) (nfix size))
                (aignet::create-sat-lits))
               (t nil)))
  :hints(("Goal" :in-theory (enable logicman->sat-litsi
                                    resize-logicman->sat-lits
                                    logicman->sat-lits-length))))


;; (defconst *logicman-fields*
;;   '((aignet :type aignet::aignet)
;;     (strash :type aignet::strash)
;;     (ipasir :type ipasir::ipasir)
;;     (sat-lits :type aignet::sat-lits)
;;     ;; (pathcond :type pathcond)
;;     ;; (bvar-db :type bvar-db)
;;     ;; (prof :type interp-profiler)
;;     (mode :type (satisfies bfr-mode-p) :initially 0)
;;     (aignet-refcounts :type aignet::aignet-refcounts)
;;     ;; refcounts are up to date up to this aignet ID
;;     (refcounts-index :type (integer 0 *) :initially 0)))


              

;; (local (defun logicman-fields-to-templates (fields)
;;          (declare (xargs :mode :program))
;;          (if (atom fields)
;;              nil
;;            (cons (acl2::make-tmplsubst :atoms `((<field> . ,(caar fields))
;;                                                 (:<field> . ,(intern$ (symbol-name (caar fields)) "KEYWORD"))
;;                                                 (:<fieldcase> . ,(if (atom (cdr fields))
;;                                                                      t
;;                                                                    (intern$ (symbol-name (caar fields)) "KEYWORD")))
;;                                                 (<type> . ,(third (car fields)))
;;                                                 (<rest> . ,(cdddr (car fields))))
;;                                        :strs `(("<FIELD>" . ,(symbol-name (caar fields))))
;;                                        :pkg-sym 'fgl::foo)
;;                  (logicman-fields-to-templates (cdr fields))))))

;; (make-event
;;  `(defconst *logicman-field-templates*
;;     ',(logicman-fields-to-templates *logicman-fields*)))
  

;; (make-event
;;  (acl2::template-subst
;;   '(defstobj logicman
;;      (:@proj fields (logicman-><field> :type <type> . <rest>)))
;;   :subsubsts `((fields . ,*logicman-field-templates*))))

;; (defthm logicmanp-implies-aignetp
;;   (implies (logicmanp logicman)
;;            (aignet::node-listp (logicman->aignet logicman))))

;; (defthm logicmanp-implies-bfr-mode-p
;;   (implies (logicmanp logicman)
;;            (bfr-mode-p (logicman->mode logicman))))


;; (defthm logicmanp-implies-pathcondp
;;   (implies (logicmanp logicman)
;;            (pathcondp (logicman->pathcond logicman))))

;; (in-theory (disable logicmanp))

;; (make-event
;;  (acl2::template-subst
;;   '(std::defenum logicman-field-p ((:@proj fields :<field>)))
;;   :subsubsts `((fields . ,*logicman-field-templates*))))

;; (make-event
;;  (acl2::template-subst
;;   '(define logicman-get ((key logicman-field-p) &optional (logicman 'logicman))
;;      ;; bozo define doesn't correctly support :non-executable t with macro args
;;      (declare (xargs :non-executable t))
;;      :no-function t
;;      :prepwork ((local (in-theory (enable logicman-field-fix))))
;;      (prog2$ (acl2::throw-nonexec-error 'logicman-get-fn (list key logicman))
;;              (case key
;;                (:@proj fields (:<fieldcase> (logicman-><field> logicman))))))
;;   :subsubsts `((fields . ,*logicman-field-templates*))))

;; (make-event
;;  (acl2::template-subst
;;   '(defsection logicman-field-basics
;;      (local (in-theory (enable logicman-get
;;                                logicman-field-fix)))
;;      (:@append fields
;;       (def-updater-independence-thm logicman-><field>-updater-independence
;;         (implies (equal (logicman-get :<field> new)
;;                         (logicman-get :<field> old))
;;                  (equal (logicman-><field> new)
;;                         (logicman-><field> old))))

;;       (defthm update-logicman-><field>-preserves-others
;;         (implies (not (equal (logicman-field-fix i) :<field>))
;;                  (equal (logicman-get i (update-logicman-><field> x logicman))
;;                         (logicman-get i logicman))))

;;       (defthm update-logicman-><field>-self-preserves-logicman
;;         (implies (logicmanp logicman)
;;                  (equal (update-logicman-><field>
;;                          (logicman-><field> logicman)
;;                          logicman)
;;                         logicman))
;;         :hints(("Goal" :in-theory (enable logicmanp
;;                                           aignet::redundant-update-nth))))

;;       (defthm logicman-><field>-of-update-logicman-><field>
;;         (equal (logicman-><field> (update-logicman-><field> x logicman))
;;                x)))

;;      (:@proj fields
;;       (in-theory (disable logicman-><field>
;;                           update-logicman-><field>)))

;;      (local (in-theory (disable logicman-get
;;                                 logicman-field-fix)))

;;      ;; test:
;;      (local 
;;       (defthm logicman-test-updater-independence
;;         (b* ((logicman1 (update-logicman->strash strash logicman))
;;              (logicman2 (update-logicman->ipasir ipasir logicman)))
;;           (and (equal (logicman->mode logicman2) (logicman->mode logicman))
;;                (equal (logicman->mode logicman1) (logicman->mode logicman)))))))
  
;;   :subsubsts `((fields . ,*logicman-field-templates*))))

(define sat-lits-init (sat-lits)
  :enabled t
  :guard-hints (("goal" :in-theory (enable aignet::resize-aignet->sat
                                           aignet::create-sat-lits
                                           aignet::sat-litsp
                                           update-nth nth len
                                           resize-list)
                 :do-not-induct t))
  :prepwork ((local (defthm equal-of-plus-const
                      (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                                    (acl2-numberp c2))
                               (equal (equal (+ c1 x) c2)
                                      (equal (fix x) (- c2 (fix c1)))))))
             (local (defthm len-equal-0
                      (equal (equal (len x) 0)
                             (not (consp x))))))
  (mbe :logic (non-exec (aignet::create-sat-lits))
       :exec (b* ((sat-lits (aignet::update-sat-next-var$ 1 sat-lits))
                  (sat-lits (aignet::resize-aignet->sat 0 sat-lits))
                  (sat-lits (aignet::resize-sat->aignet 1 sat-lits)))
               (aignet::update-sat->aigneti 0 0 sat-lits))))

                    
(define ipasir-maybe-release (ipasir)
  :returns (new-ipasir)
  (if (eq (ipasir::ipasir-get-status ipasir) :undef)
      ipasir
    (ipasir-release ipasir))
  ///
  (defret status-of-ipasir-maybe-release
    (equal (ipasir::ipasir$a->status new-ipasir) :undef)))

(fty::deffixcong acl2::nat-equiv equal (logicman->ipasiri n logicman) n
  :hints(("Goal" :in-theory (enable logicman->ipasiri))))
(fty::deffixcong acl2::nat-equiv equal (update-logicman->ipasiri n val logicman) n
  :hints(("Goal" :in-theory (enable update-logicman->ipasiri))))

(fty::deffixcong acl2::nat-equiv equal (logicman->sat-litsi n logicman) n
  :hints(("Goal" :in-theory (enable logicman->sat-litsi))))
(fty::deffixcong acl2::nat-equiv equal (update-logicman->sat-litsi n val logicman) n
  :hints(("Goal" :in-theory (enable update-logicman->sat-litsi))))

(define logicman-release-ipasirs ((n natp) logicman)
  :measure (nfix (- (logicman->ipasir-length logicman) (nfix n)))
  :guard (<= n (logicman->ipasir-length logicman))
  :returns (new-logicman)
  (if (mbe :logic (zp (- (logicman->ipasir-length logicman) (nfix n)))
           :exec (eql n (logicman->ipasir-length logicman)))
      logicman
    (stobj-let ((ipasir (logicman->ipasiri n logicman)))
               (ipasir)
               (ipasir-maybe-release ipasir)
               (logicman-release-ipasirs (1+ (lnfix n)) logicman)))
  ///
  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix k) :ipasir))
             (equal (logicman-get k new-logicman)
                    (logicman-get k logicman)))))


(define logicman-init (&key
                       (logicman 'logicman)
                       ((max-ins natp) '0)
                       ((max-nodes posp) '1))
  :returns new-logicman
  :enabled t
  :prepwork ((local (defthm equal-of-plus-const
                      (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                                    (acl2-numberp c2))
                               (equal (equal (+ c1 x) c2)
                                      (equal (fix x) (- c2 (fix c1)))))))
             (local (defthm len-equal-const
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (if (zp n)
                                          (and (not (consp x))
                                               (equal n 0))
                                        (and (consp x)
                                             (equal (len (cdr x)) (+ -1 n))))))))
             (local (in-theory (e/d* (logicman-defs
                                       aignet::strashp
                                       update-nth len)
                                    (cons-equal))))
             (local (defthmd update-nth-same
                      (equal (update-nth n val (update-nth n val1 x))
                             (update-nth n val x))
                      :hints(("Goal" :in-theory (enable update-nth)))))
             (local (defthm update-nth-of-logicman-release-ipasirs
                      (equal (update-nth *logicman->ipasiri* val (logicman-release-ipasirs n logicman))
                             (update-nth *logicman->ipasiri* val logicman))
                      :hints(("Goal" :in-theory (enable logicman-release-ipasirs
                                                        update-nth-same))))))
  :guard-hints (("goal" :do-not-induct t))
  (mbe :logic (non-exec (create-logicman))
       :exec (stobj-let ((aignet (logicman->aignet logicman))
                         (strash (logicman->strash logicman))
                         (u32arr (logicman->aignet-refcounts logicman)))
                        (aignet strash u32arr)
                        (b* ((aignet (aignet::aignet-init 0 0 max-ins max-nodes aignet))
                             (strash (strashtab-clear strash))
                             (u32arr (resize-u32 0 u32arr)))
                          (mv aignet strash u32arr))
                        (b* ((logicman (update-logicman->mode 0 logicman))
                             (logicman (logicman-release-ipasirs 0 logicman))
                             (logicman (resize-logicman->ipasir 0 logicman))
                             (logicman (resize-logicman->sat-lits 0 logicman)))
                          (update-logicman->refcounts-index 0 logicman)))))

(defmacro lbfr-mode (&optional (logicman 'logicman))
  `(logicman->mode ,logicman))

(defsection lbfr-case
  :parents (bfr)
  :short "Choose behavior based on the current @(see bfr) mode of a logicman."
  :long "<p>Same as @(see bfr-mode-case), but implicitly uses the bfr mode
setting of a logicman stobj.  If no logicman is given as the first
argument (i.e., the first argument is a keyword), the variable named
@('logicman') is implicitly used.</p>"

  (defun lbfr-case-fn (args)
    (if (keywordp (car args))
        `(bfr-mode-case (lbfr-mode) . ,args)
      `(bfr-mode-case (lbfr-mode ,(car args)) . ,(cdr args))))

  (defmacro lbfr-case (&rest args)
    (lbfr-case-fn args)))

(defsection lbfr-mode-is
  :parents (bfr)
  :short "Check the current bfr-mode of a logicman stobj"
  :long "<p>Same as @(see bfr-mode-is), but gets the bfr mode object from a
logicman stobj.  If no logicman argument is supplied, the variable named
@('logicman') is implicitly used.</p>"
  (defun lbfr-mode-is-fn (key lman)
    `(bfr-mode-is ,key (lbfr-mode ,lman)))
  
  (defmacro lbfr-mode-is (key &optional (logicman 'logicman))
    (lbfr-mode-is-fn key logicman)))
  



(define logicman->bfrstate (&optional (logicman 'logicman))
  :returns (bfrstate bfrstate-p)
  (b* ((bfr-mode (lbfr-mode)))
    (bfr-mode-case
      :aignet (stobj-let ((aignet (logicman->aignet logicman)))
                         (bfrstate)
                         (bfrstate bfr-mode (1- (aignet::num-fanins aignet)))
                         bfrstate)
      :otherwise (stobj-let ((aignet (logicman->aignet logicman)))
                            (bfrstate)
                            (bfrstate bfr-mode (aignet::num-ins aignet))
                            bfrstate)))
  ///
  (def-updater-independence-thm logicman->bfrstate-updater-independence
    (implies (and (equal (logicman->aignet new)
                         (logicman->aignet old))
                  (equal (logicman->mode new)
                         (logicman->mode old)))
             (equal (logicman->bfrstate new)
                    (logicman->bfrstate old))))

  (defret bfrstate->mode-of-logicman->bfrstate
    (equal (bfrstate->mode bfrstate)
           (bfr-mode-fix (lbfr-mode))))

  (defret bfrstate->bound-of-logicman->bfrstate-aignet
    (implies (lbfr-mode-is :aignet)
             (equal (bfrstate->bound bfrstate)
                    (aignet::fanin-count (logicman->aignet logicman)))))

  (defthm aignet-litp-of-bfr->aignet-lit
    (b* ((bfrstate (logicman->bfrstate)))
      (implies (lbfr-mode-is :aignet)
               (aignet::aignet-litp (bfr->aignet-lit x)
                                    (logicman->aignet logicman))))
    :hints(("Goal" :in-theory (enable logicman->bfrstate
                                      bfr->aignet-lit
                                      bfr-fix
                                      aignet-lit->bfr
                                      bounded-lit-fix
                                      aignet::aignet-idp)))))

;; Include pathcond? parametrization hyp?

(define logicman-extension-p (new old)
  :non-executable t
  :verify-guards nil
  (and (aignet::aignet-extension-p (logicman->aignet new)
                                   (logicman->aignet old))
       (equal (aignet::num-regs (logicman->aignet new))
              (aignet::num-regs (logicman->aignet old)))
       ;; (bvar-db-extension-p (logicman->bvar-db new)
       ;;                      (logicman->bvar-db old))
       (equal (logicman->mode new) (logicman->mode old))
       ;; (equal (logicman->ipasir new) (logicman->ipasir old))
       ;; (equal (logicman->sat-lits new) (logicman->sat-lits old))
       ;; (equal (logicman->aignet-refcounts new) (logicman->aignet-refcounts old))
       ;; (equal (logicman->refcounts-index new) (logicman->refcounts-index old))
       )
  ///
  ;; (def-updater-independence-thm logicman-extension-p-updater-independence-1
  ;;   (implies (and (equal (logicman-get :aignet new)
  ;;                        (logicman-get :aignet old))
  ;;                 ;; (equal (logicman-get :bvar-db new)
  ;;                 ;;        (logicman-get :bvar-db old))
  ;;                 (equal (logicman-get :mode new)
  ;;                        (logicman-get :mode old))
  ;;                 (logicman-extension-p old other))
  ;;            (logicman-extension-p new other)))

  ;; (def-updater-independence-thm logicman-extension-p-updater-independence-2
  ;;   (implies (and (equal (logicman-get :aignet new)
  ;;                        (logicman-get :aignet old))
  ;;                 ;; (equal (logicman-get :bvar-db new)
  ;;                 ;;        (logicman-get :bvar-db old))
  ;;                 (equal (logicman-get :mode new)
  ;;                        (logicman-get :mode old))
  ;;                 (logicman-extension-p other old))
  ;;            (logicman-extension-p other new)))

  ;; (def-updater-independence-thm logicman-extension-p-updater-independence-2
  ;;   (implies (and (equal (logicman-get :aignet new)
  ;;                        (logicman-get :aignet old))
  ;;                 ;; (equal (logicman-get :bvar-db new)
  ;;                 ;;        (logicman-get :bvar-db old))
  ;;                 (equal (logicman-get :mode new)
  ;;                        (logicman-get :mode old))
  ;;                 (logicman-extension-p other old))
  ;;            (logicman-extension-p other new)))

  ;; (in-theory (disable logicman-extension-p-updater-independence-1
  ;;                     logicman-extension-p-updater-independence-2))

  (defmacro bind-logicman-extension (new old-var)
    `(and (bind-free (acl2::prev-stobj-binding ,new ',old-var mfc state))
          (logicman-extension-p ,new ,old-var)))

  (defthm logicman-extension-self
    (logicman-extension-p x x))

  (def-updater-independence-thm logicman-extension-of-update-1
    (implies (and (equal (logicman->aignet new)
                         (logicman->aignet old))
                  (equal (logicman->mode new)
                         (logicman->mode old)))
             (equal (logicman-extension-p new logicman)
                    (logicman-extension-p old logicman))))

  (def-updater-independence-thm logicman-extension-of-update-2
    (implies (and (equal (logicman->aignet new)
                         (logicman->aignet old))
                  (equal (logicman->mode new)
                         (logicman->mode old)))
             (equal (logicman-extension-p logicman new)
                    (logicman-extension-p logicman old))))
    

  (defthm aignet-extension-when-logicman-extension
    (implies (logicman-extension-p new old)
             (aignet::aignet-extension-p (logicman->aignet new)
                                         (logicman->aignet old))))

  (defthm logicman-extension-p-transitive
    (implies (and (bind-logicman-extension x y)
                  (logicman-extension-p y z))
             (logicman-extension-p x z)))

  ;; (defthm logicman-extension-when-same
  ;;   (implies (and (equal (logicman-get :aignet new)
  ;;                        (logicman-get :aignet old))
  ;;                 ;; (equal (logicman-get :bvar-db new)
  ;;                 ;;        (logicman-get :bvar-db old))
  ;;                 (equal (logicman-get :mode new)
  ;;                        (logicman-get :mode old)))
  ;;            (logicman-extension-p new old)))

  (defthm logicman->mode-of-extension
    (implies (bind-logicman-extension x y)
             (equal (logicman->mode x)
                    (logicman->mode y))))

  (defthm bfrstate>=-when-logicman-extension
    (implies (logicman-extension-p new old)
             (bfrstate>= (logicman->bfrstate new)
                         (logicman->bfrstate old)))
    :hints(("Goal" :in-theory (enable logicman->bfrstate
                                      bfrstate>=))))

  (local (in-theory (disable bfrstate>=-when-logicman-extension
                             logicman-extension-p)))

  (defthm bfr-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x (logicman->bfrstate old)))
             (bfr-p x (logicman->bfrstate new)))
    :hints (("goal" :use bfrstate>=-when-logicman-extension)))

  (defthm bfr-fix-when-bfr-p-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x (logicman->bfrstate old)))
             (equal (bfr-fix x (logicman->bfrstate new)) x))
    :hints (("Goal" :use ((:instance bfr-p-when-logicman-extension))
             :in-theory (disable bfr-p-when-logicman-extension))))

  (defthm bfr->aignet-lit-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x (logicman->bfrstate old)))
             (equal (bfr->aignet-lit x (logicman->bfrstate new))
                    (bfr->aignet-lit x (logicman->bfrstate old))))
    :hints(("Goal" :in-theory (enable bfr->aignet-lit))))

  (defthm bfr-listp-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-listp x (logicman->bfrstate old)))
             (bfr-listp x (logicman->bfrstate new)))
    :hints (("goal" :use bfrstate>=-when-logicman-extension)))

  (defthm fgl-bfr-object-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (fgl-bfr-object-p x (logicman->bfrstate old)))
             (fgl-bfr-object-p x (logicman->bfrstate new)))
    :hints (("goal" :use bfrstate>=-when-logicman-extension
             :in-theory (disable fgl-bfr-object-p-when-fgl-object-p))))

  (defthm fgl-bfr-objectlist-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (fgl-bfr-objectlist-p x (logicman->bfrstate old)))
             (fgl-bfr-objectlist-p x (logicman->bfrstate new)))
    :hints (("goal" :use bfrstate>=-when-logicman-extension
             :in-theory (disable fgl-bfr-objectlist-p-when-fgl-objectlist-p))))

  (defthm fgl-bfr-object-alist-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (fgl-bfr-object-alist-p x (logicman->bfrstate old)))
             (fgl-bfr-object-alist-p x (logicman->bfrstate new)))
    :hints (("goal" :use bfrstate>=-when-logicman-extension
             :in-theory (disable fgl-bfr-object-alist-p-when-fgl-object-alist-p)))))








;; (define bfr-p (x &optional (logicman 'logicman))
;;   (bfr-case
;;     :aig (aig-p x)
;;     :bdd (acl2::ubddp x)
;;     :aignet
;;     (or (booleanp x)
;;         (and (satlink::litp x)
;;              (not (eql x 0))
;;              (not (eql x 1))
;;              (stobj-let
;;               ((aignet (logicman->aignet logicman)))
;;               (ans)
;;               (aignet::fanin-litp x aignet)
;;               ans))))
;;   ///
;;   (defthm bfr-p-of-constants
;;     (and (bfr-p t)
;;          (bfr-p nil)))

;;   (def-updater-independence-thm bfr-p-updater-independence
;;     (implies (and (equal (logicman-get :aignet new)
;;                          (logicman-get :aignet old))
;;                   (equal (logicman-get :mode new)
;;                          (logicman-get :mode old)))
;;              (equal (bfr-p x new) (bfr-p x old))))

;;   (defthm bfr-p-when-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (bfr-p x old))
;;              (bfr-p x new))
;;     :hints(("Goal" :in-theory (enable logicman-extension-p)))))

;; (std::deflist bfr-listp$ (x logicman)
;;   (bfr-p x)
;;   :true-listp t
;;   ///
;;   (defthm bfr-listp-when-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (bfr-listp$ x old))
;;              (bfr-listp$ x new))))

;; (defmacro bfr-listp (x &optional (logicman 'logicman))
;;   `(bfr-listp$ ,x ,logicman))

;; (add-macro-alias bfr-listp bfr-listp$)



;; (define aignet-lit->bfr ((x satlink::litp) &optional (logicman 'logicman))
;;   :guard (stobj-let ((aignet (logicman->aignet logicman)))
;;                     (ans)
;;                     (aignet::fanin-litp x aignet)
;;                     ans)
;;   :returns (bfr bfr-p :hyp (eq (lbfr-mode) :aignet)
;;                 :hints(("Goal" :in-theory (enable bfr-p))))
;;   (b* ((x (mbe :logic (non-exec (aignet::aignet-lit-fix x (logicman->aignet logicman)))
;;                :exec x)))
;;     (case x
;;       (0 nil)
;;       (1 t)
;;       (t x)))
;;   ///
  
;;   (defthm aignet-lit->bfr-of-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (aignet::aignet-litp x (logicman->aignet old)))
;;              (equal (aignet-lit->bfr x new)
;;                     (aignet-lit->bfr x old)))
;;     :hints(("Goal" :in-theory (enable logicman-extension-p)))))


;; (define bfr-fix ((x bfr-p) &optional (logicman 'logicman))
;;   :returns (new-x bfr-p)
;;   :prepwork ((local (in-theory (enable bfr-p aignet-lit->bfr))))
;;   (mbe :logic (bfr-case
;;                 :aig (aig-fix x)
;;                 :bdd (acl2::ubdd-fix x)
;;                 :aignet
;;                 (if (booleanp x)
;;                     x
;;                   (aignet-lit->bfr x)))
;;        :exec x)
;;   ///
;;   (std::defret bfr-fix-when-bfr-p
;;     (implies (bfr-p x)
;;              (equal new-x x))))

;; (define bfr-list-fix ((x bfr-listp) &optional (logicman 'logicman))
;;   :returns (new-x bfr-listp)
;;   (if (atom x)
;;       nil
;;     (cons (bfr-fix (car x))
;;           (bfr-list-fix (cdr x))))
;;   ///
;;   (defret bfr-list-fix-when-bfr-listp
;;     (implies (bfr-listp x)
;;              (equal (bfr-list-fix x) x)))

;;   (defret car-of-bfr-list-fix
;;     (implies (consp x)
;;              (equal (car (bfr-list-fix x))
;;                     (bfr-fix (car x)))))

;;   (defret cdr-of-bfr-list-fix
;;     (implies (consp x)
;;              (equal (cdr (bfr-list-fix x))
;;                     (bfr-list-fix (cdr x)))))

;;   (defret consp-of-bfr-list-fix
;;     (equal (consp (bfr-list-fix x))
;;            (consp x)))

;;   (defret len-of-bfr-list-fix
;;     (equal (len (bfr-list-fix x))
;;            (len x))))

;; (define bfr->aignet-lit ((x bfr-p) &optional (logicman 'logicman))
;;   :guard (eq (lbfr-mode) :aignet)
;;   :returns (lit (implies (eq (lbfr-mode) :aignet)
;;                          (aignet::aignet-litp lit (logicman->aignet logicman))))
;;   :prepwork ((local (in-theory (enable bfr-fix aignet-lit->bfr bfr-p))))
;;   (b* ((x (bfr-fix x)))
;;     (case x
;;       ((nil) 0)
;;       ((t) 1)
;;       (t (satlink::lit-fix x))))
;;   ///
;;   (defthm bfr->aignet-lit-of-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (bfr-p x old))
;;              (equal (bfr->aignet-lit x new)
;;                     (bfr->aignet-lit x old))))

;;   (defthm bfr->aignet-lit-of-aignet-lit->bfr
;;     (implies (equal (lbfr-mode) :aignet)
;;              (equal (bfr->aignet-lit (aignet-lit->bfr x))
;;                     (aignet::aignet-lit-fix x (logicman->aignet logicman))))
;;     :hints(("Goal" :in-theory (enable aignet-lit->bfr))))

;;   (defthm aignet-lit->bfr-of-bfr->aignet-lit
;;     (implies (equal (lbfr-mode) :aignet)
;;              (equal (aignet-lit->bfr (bfr->aignet-lit x))
;;                     (bfr-fix x)))
;;     :hints(("Goal" :in-theory (enable aignet-lit->bfr bfr-fix))))

;;   (defthm bfr->aignet-lit-of-bfr-fix
;;     (equal (bfr->aignet-lit (bfr-fix x))
;;            (bfr->aignet-lit x))
;;     :hints(("Goal" :in-theory (enable bfr-fix)))))



(define bools-to-bits ((x true-listp))
  :returns (bits aignet::bit-listp)
  (if (atom x)
      nil
    (cons (bool->bit (car x))
          (bools-to-bits (cdr x))))
  ///
  (std::defret len-of-<fn>
    (equal (len bits) (len x)))
  (std::defret nth-of-<fn>
    (acl2::bit-equiv (nth n bits) (bool->bit (nth n x)))
    :hints(("Goal" :in-theory (enable nth)))))



(define list-to-bits-aux ((n natp)
                          (x true-listp)
                          (acl2::bitarr))
  :guard (<= (+ (nfix n) (len x)) (acl2::bits-length acl2::bitarr))
  :returns (new-bitarr)
  (b* (((when (atom x)) (mbe :logic (non-exec (aignet::bit-list-fix acl2::bitarr))
                             :exec acl2::bitarr))
       (acl2::bitarr (acl2::set-bit (lnfix n) (bool->bit (car x)) acl2::bitarr)))
    (list-to-bits-aux (1+ (lnfix n)) (cdr x) acl2::bitarr))
  ///
  (std::defret len-of-<fn>
    (implies (<= (+ (nfix n) (len x)) (len acl2::bitarr))
             (equal (len new-bitarr) (len acl2::bitarr))))
  ;; (std::defret nth-of-<fn>
  ;;   (implies (<= (+ (nfix n) (len x)) (len acl2::bitarr))
  ;;            (equal (nth k new-bitarr)
  ;;                   (if (and (<= (nfix n) (nfix k))
  ;;                            (< (nfix k) (+ (nfix n) (len x))))
  ;;                       (bool->bit (nth (- (nfix k) (nfix n)) x))
  ;;                     (nth k (aignet::bit-list-fix acl2::bitarr)))))
  ;;   :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthm nthcdr-greater-of-update-nth
           (implies (< (nfix m) (nfix n))
                    (equal (nthcdr n (update-nth m val x))
                           (nthcdr n x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (local (defthm bit-list-fix-of-update-nth
           (implies (<= (nfix n) (len x))
                    (equal (aignet::bit-list-fix (update-nth n v x))
                           (update-nth n (bfix v) (aignet::bit-list-fix x))))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (local (defthm append-take-nthcdr
           (implies (<= (nfix n) (len x))
                    (equal (append (take n x) (nthcdr n x))
                           x))))
                    
  (local (defthm take-of-update-nth
           (equal (take (+ 1 (nfix n)) (update-nth n v x))
                  (append (take n x) (list v)))
           :hints(("Goal" :in-theory (enable update-nth)))))


  (std::defret list-to-bits-aux-redef
    (implies (<= (+ (nfix n) (len x)) (len acl2::bitarr))
             (equal new-bitarr
                    (append (take n (aignet::bit-list-fix acl2::bitarr))
                            (bools-to-bits x)
                            (nthcdr (+ (nfix n) (len x)) (aignet::bit-list-fix acl2::bitarr)))))
    :hints(("Goal" :in-theory (e/d (bools-to-bits)
                                   (acl2::append-of-cons
                                    take))
            :induct (list-to-bits-aux n x acl2::bitarr)))))

;;(local (include-book "std/lists/resize-list" :dir :system))

(define list-to-bits ((x true-listp)
                      (acl2::bitarr))
  :enabled t
  :prepwork ((local (defthm nthcdr-of-nil
                      (equal (nthcdr n nil) nil)))
             (local (defthm nthcdr-by-len
                      (implies (and (>= (nfix n) (len x))
                                    (true-listp x))
                               (equal (nthcdr n x) nil))
                      :hints (("goal" :induct (nthcdr n x)))))
             (local (in-theory (disable nthcdr aignet::bit-list-fix-of-cons resize-list))))
  (mbe :logic (non-exec (bools-to-bits x))
       :exec (b* ((acl2::bitarr (acl2::resize-bits (len x) acl2::bitarr)))
               (list-to-bits-aux 0 x acl2::bitarr))))


(define alist-to-bitarr-aux ((n natp)
                             (alist)
                             (acl2::bitarr))
  :measure (nfix (- (acl2::bits-length acl2::bitarr) (nfix n)))
  :guard (<= n (acl2::bits-length acl2::bitarr))
  :returns (new-bitarr)
  (b* (((when (mbe :logic (zp (- (acl2::bits-length acl2::bitarr) (nfix n)))
                   :exec (eql n (acl2::bits-length acl2::bitarr))))
        acl2::bitarr)
       (acl2::bitarr (acl2::set-bit n (bool->bit (cdr (hons-get (lnfix n) alist))) acl2::bitarr)))
    (alist-to-bitarr-aux (1+ (lnfix n)) alist acl2::bitarr))
  ///
  (defret len-of-alist-to-bitarr-aux
    (equal (len new-bitarr) (len acl2::bitarr)))

  (defret nth-of-alist-to-bitarr-aux
    (equal (nth k new-bitarr)
           (if (and (<= (nfix n) (nfix k))
                    (< (nfix k) (len acl2::bitarr)))
               (bool->bit (cdr (hons-assoc-equal (nfix k) alist)))
             (nth k acl2::bitarr))))

  (defret true-listp-of-<fn>
    (implies (true-listp acl2::bitarr)
             (true-listp new-bitarr))))



(define alist-to-bitarr ((max natp)
                         (alist)
                         (acl2::bitarr))
  :returns (new-bitarr)
  (b* ((acl2::bitarr (acl2::resize-bits max acl2::bitarr)))
    (alist-to-bitarr-aux 0 alist acl2::bitarr))
  ///
  (defret len-of-<fn>
    (equal (len new-bitarr) (nfix max)))

  (defret nth-of-<fn>
    (acl2::bit-equiv (nth k new-bitarr)
                     (bool->bit
                      (and (< (nfix k) (nfix max))
                           (cdr (hons-assoc-equal (nfix k) alist))))))

  (defthm alist-to-bitarr-normalize
    (implies (syntaxp (not (equal bitarr ''nil)))
             (equal (alist-to-bitarr max alist bitarr)
                    (alist-to-bitarr max alist nil)))
    :hints ((acl2::equal-by-nths-hint)))


  (local (in-theory (disable alist-to-bitarr)))
  #!aignet
  (defthm id-eval-of-alist-to-bitarr-aignet-extension
    (implies (and (syntaxp (not (equal new old)))
                  (aignet-extension-p new old)
                  ;; (aignet-idp x old)
                  )
             (equal (id-eval x (fgl::alist-to-bitarr (stype-count :pi new) env bitarr) regvals old)
                    (id-eval x (fgl::alist-to-bitarr (stype-count :pi old) env bitarr) regvals old)))
    :hints (("goal" :induct (id-eval-ind x old)
             :expand ((:free (invals regvals)
                       (id-eval x invals regvals old)))
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

  #!aignet
  (defthm lit-eval-of-alist-to-bitarr-aignet-extension
    (implies (and (syntaxp (not (equal new old)))
                  (aignet-extension-p new old)
                  ;; (aignet-litp x old)
                  )
             (equal (lit-eval x (fgl::alist-to-bitarr (stype-count :pi new) env bitarr) regvals old)
                    (lit-eval x (fgl::alist-to-bitarr (stype-count :pi old) env bitarr) regvals old)))
    :hints (("goal" 
             :expand ((:free (invals regvals)
                       (lit-eval x invals regvals old)))
             :in-theory (enable aignet-idp)))))


(defmacro lbfr-p (x &optional (logicman 'logicman))
  `(bfr-p ,x (logicman->bfrstate ,logicman)))
(defmacro lbfr-listp (x &optional (logicman 'logicman))
  `(bfr-listp ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-p (x &optional (logicman 'logicman))
  `(fgl-bfr-object-p ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-objectlist-p (x &optional (logicman 'logicman))
  `(fgl-bfr-objectlist-p ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-alist-p (x &optional (logicman 'logicman))
  `(fgl-bfr-object-alist-p ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-bindings-p (x &optional (logicman 'logicman))
  `(fgl-bfr-object-bindings-p ,x (logicman->bfrstate ,logicman)))

(defmacro lbfr-fix (x &optional (logicman 'logicman))
  `(bfr-fix ,x (logicman->bfrstate ,logicman)))
(defmacro lbfr-list-fix (x &optional (logicman 'logicman))
  `(bfr-list-fix ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-fix (x &optional (logicman 'logicman))
  `(fgl-bfr-object-fix ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-objectlist-fix (x &optional (logicman 'logicman))
  `(fgl-bfr-objectlist-fix ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-alist-fix (x &optional (logicman 'logicman))
  `(fgl-bfr-object-alist-fix ,x (logicman->bfrstate ,logicman)))
(defmacro lgl-bfr-object-bindings-fix (x &optional (logicman 'logicman))
  `(fgl-bfr-object-bindings-fix ,x (logicman->bfrstate ,logicman)))



(define bfr-eval ((x lbfr-p "A Boolean function object")
                  (env "The (Boolean) evaluation environment")
                  &optional ((logicman "The logic manager") 'logicman))
  :parents (bfr)
  :short "Evaluate a BFR under an appropriate BDD/AIG environment."
  :long "<p>@('Bfr-eval') is the evaluator for Boolean function objects in FGL.</p>

<p>Boolean function objects in FGL may be <see topic='@(url acl2::ubdds)'>UBDDs</see>,
<see topic='@(url acl2::aig)'>hons-AIGs</see>, or <see topic='@(url acl2::aignet)'>
aignet</see> literals (represented as natural numbers).  The @(see bfr-mode) of
the logic manager (accessed as @('(logicman->mode logicman)')) determines how
the objects are interpreted.  Furthermore, in the aignet mode, literals must be
evaluated relative to an aignet, which is also stored in the logic manager as a
nested stobj, accessed using @('(logicman->aignet logicman)').</p>

<p>The @('env') input determines the values of Boolean variables, but its form
also depends on the BFR mode.  In UBDD mode, it is an ordered list of Boolean
values, where @('(nth n env)') is the value of Boolean variable @('n').
Otherwise, it is a fast alist mapping natural numbers to Boolean values, and
the value of the nth Boolean variable is @('(cdr (hons-get n env))').  In
aignet mode, the Boolean variable numbers map to primary inputs of the AIG --
registers are not used.</p>"
  :returns (bool t)
  :prepwork (;; (local (include-book "std/lists/nth" :dir :system))
             (local (defthm alist-to-bits-of-nil-under-bits-equiv
                      (aignet::bits-equiv (alist-to-bitarr max nil bitarr)
                                          nil)
                      :hints(("Goal" :in-theory (enable aignet::bits-equiv)))))
             )
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet::aignet-idp bfr-p ;; logicman->bfrstate
                                          ))))
  (b* ((bfrstate (logicman->bfrstate)))
    (bfrstate-case
      :bdd (acl2::eval-bdd (bfr-fix x) env)
      :aig (acl2::aig-eval (bfr-fix x) env)
      :aignet (mbe :logic (non-exec
                           (acl2::bit->bool
                            (aignet::lit-eval (bfr->aignet-lit x)
                                              (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman)) env nil)
                                              nil
                                              (logicman->aignet logicman))))
                   :Exec
                   (b* ((x (bfr->aignet-lit x))
                        ((acl2::local-stobjs aignet::invals aignet::regvals)
                         (mv ans aignet::invals aignet::regvals)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman)))
                      (ans aignet::invals aignet::regvals)
                      (b* ((aignet::invals (alist-to-bitarr (aignet::num-ins aignet) env aignet::invals))
                           (aignet::regvals (alist-to-bitarr (aignet::num-regs aignet) nil aignet::regvals)))
                        (mv (acl2::bit->bool
                             (aignet::lit-eval x aignet::invals aignet::regvals aignet::aignet))
                            aignet::invals aignet::regvals))
                      (mv ans aignet::invals aignet::regvals))))))
  ///
  (defthm bfr-eval-consts
    (and (equal (bfr-eval t env) t)
         (equal (bfr-eval nil env) nil))
    :hints(("Goal" :in-theory (enable bfr->aignet-lit))))

  (defthm bfr-eval-of-bfr-fix
    (b* ((bfrstate (logicman->bfrstate logicman)))
      (equal (bfr-eval (bfr-fix x) env)
             (bfr-eval x env)))
    :hints((acl2::use-termhint
            (b* ((bfrstate (logicman->bfrstate old-logicman)))
              (bfrstate-case
                :aignet '(:in-theory (enable aignet::lit-eval-of-aignet-lit-fix))
                :otherwise '(:in-theory (enable bfr-fix ;; logicman->bfrstate
                                                ))))))
    :otf-flg t)

  (defthm bfr-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-p x old))
             (equal (bfr-eval x env new)
                    (bfr-eval x env old)))
    :hints((acl2::use-termhint
            (b* ((bfrstate (logicman->bfrstate old)))
              (bfrstate-case
                :aignet (acl2::termhint-seq '(:in-theory (enable aignet::lit-eval-of-aignet-lit-fix))
                                            '(:in-theory (enable logicman-extension-p)))
                :otherwise '(:in-theory (enable bfr-fix ;; logicman->bfrstate
                                                ))))))))


(define bfr-list-eval ((x lbfr-listp) env &optional (logicman 'logicman))
  :returns bools
  (if (atom x)
      nil
    (cons (bfr-eval (car x) env)
          (bfr-list-eval (cdr x) env)))
  ///
  (defthm bfr-list-eval-of-bfr-list-fix
    (equal (bfr-list-eval (lbfr-list-fix x) env)
           (bfr-list-eval x env)))

  (defthm bfr-list-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp x old))
             (equal (bfr-list-eval x env new)
                    (bfr-list-eval x env old))))

  (defthm bfr-list-eval-of-true-list-fix
    (equal (bfr-list-eval (true-list-fix x) env)
           (bfr-list-eval x env))
    :hints(("Goal" :in-theory (enable bfr-list-eval)))))




;; (define logicman-nvars-ok (&optional (logicman 'logicman))
;;   (lbfr-case
;;     :bdd t
;;     :aig t
;;     :aignet
;;     (stobj-let
;;      ((aignet (logicman->aignet logicman))
;;       (bvar-db (logicman->bvar-db logicman)))
;;      (ok)
;;      (equal (next-bvar bvar-db)
;;             (aignet::num-ins aignet))
;;      ok))
;;   ///
;;   (def-updater-independence-thm logicman-nvars-ok-updater-independence
;;     (implies (and (equal (logicman->mode new)
;;                          (logicman->mode old))
;;                   (equal (next-bvar (logicman->bvar-db new))
;;                          (next-bvar (logicman->bvar-db old)))
;;                   (equal (aignet::num-ins (logicman->aignet new))
;;                          (aignet::num-ins (logicman->aignet old))))
;;              (equal (logicman-nvars-ok new)
;;                     (logicman-nvars-ok old)))))


(define bfr-nvars (&optional (logicman 'logicman))
  ;; :guard (logicman-nvars-ok)
;;  :prepwork ((local (in-theory (enable logicman-nvars-ok))))
  (mbe :logic (non-exec (aignet::num-ins (logicman->aignet logicman)))
       :exec (stobj-let
              ((aignet (logicman->aignet logicman)))
              (nvars)
              (aignet::num-ins aignet)
              nvars))
  ///
  (def-updater-independence-thm bfr-nvars-updater-independence
    (implies (and (equal (aignet::num-ins (logicman->aignet new))
                         (aignet::num-ins (logicman->aignet old)))
                  (equal (lbfr-mode new) (lbfr-mode old)))
             (equal (bfr-nvars new) (bfr-nvars old))))

  (defthm bfr-nvars-of-logicman-extension
    (implies (bind-logicman-extension new old)
             (<= (bfr-nvars old) (bfr-nvars new)))
    :hints(("Goal" :in-theory (enable logicman-extension-p)))
    :rule-classes ((:linear :trigger-terms ((bfr-nvars new)))))

  (defthm bfrstate->bound-of-logicman->bfrstate-non-aignet
    (implies (not (lbfr-mode-is :aignet))
             (equal (bfrstate->bound (logicman->bfrstate))
                    (bfr-nvars logicman)))
    :hints(("Goal" :in-theory (enable logicman->bfrstate))))

  ;; (defthm logicman-nvars-ok-implies
  ;;   (implies (and (logicman-nvars-ok)
  ;;                 (lbfr-mode-is :aignet))
  ;;            (equal (aignet::stype-count :pi (logicman->aignet logicman))
  ;;                   (bfr-nvars))))
  )

   

(define logicman-add-var (;; (obj fgl-object-p)
                          &optional (logicman 'logicman))
  :returns (new-logicman)
  (stobj-let
   ((aignet (logicman->aignet logicman)))
   (aignet)
   (aignet::aignet-add-in aignet)
   logicman)
  ///
  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (+ 1 (bfr-nvars logicman)))
    :hints(("Goal" :in-theory (enable bfr-nvars))))

  (defret logicman-get-of-logicman-add-var
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p)))))




(define bfr-varname-p ((x natp) &optional (logicman 'logicman))
  ;; :guard (logicman-nvars-ok)
  ;; :guard-hints (("goal" :in-theory (enable logicman-nvars-ok bfr-nvars)))
  ;;; (and (natp x)
       ;; (< x (bfr-nvars))
  (< (lnfix x) (bfr-nvars))
                ;; (non-exec (< x (aignet::num-ins (logicman->aignet logicman)))))))
  ///
  ;; (def-updater-independence-thm bfr-varname-p-updater-independence
  ;;   (implies (and (bfr-varname-p x old)
  ;;                 (equal (next-bvar (logicman->bvar-db new))
  ;;                        (next-bvar (logicman->bvar-db old)))
  ;;                 (equal (aignet::num-ins (logicman->aignet new))
  ;;                        (aignet::num-ins (logicman->aignet old))))
  ;;            (bfr-varname-p x new)))

  ;; (defthm bfr-varname-p-implies-natp
  ;;   (implies (bfr-varname-p x)
  ;;            (natp x))
  ;;   :rule-classes :forward-chaining)

  (defthm bfr-varname-p-of-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p x old))
             (bfr-varname-p x new))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable logicman-extension-p)))))

  (defthm bfr-varname-p-nvars-of-logicman-add-var
    (bfr-varname-p (bfr-nvars logicman)
                   (logicman-add-var logicman))
    :hints(("Goal" :in-theory (enable bfr-nvars logicman-add-var)))))

;; (define logicman-check-nvars ((n natp) &optional (logicman 'logicman))
;;   (or (not (lbfr-mode-is :aignet))
;;       (equal (bfr-nvars) (lnfix n)))
;;   ///
;;   (defthm bfr-varname-p-when-logicman-check-nvars
;;     (implies (and (logicman-check-nvars n)
;;                   (< (nfix v) (nfix n)))
;;              (bfr-varname-p v))
;;     :hints(("Goal" :in-theory (enable bfr-varname-p)))))


;; (define bfr-varname-p (x)
;;   (natp x)
;;   ///
;;   (defthm bfr-varname-p-compound-recognizer
;;     (equal (bfr-varname-p x)
;;            (natp x))
;;     :rule-classes :compound-recognizer)

;;   (define bfr-varname-fix ((x bfr-varname-p))
;;     :enabled t
;;     (mbe :logic (nfix x) :exec x))

;;   (fty::deffixtype bfr-varname :pred bfr-varname-p :fix bfr-varname-fix :equiv acl2::nat-equiv))
             


;; (define aig-var-fix ((x acl2::aig-var-p))
;;   :returns (new-x acl2::aig-var-p)
;;   (mbe :logic (if (acl2::aig-var-p x)
;;                   x
;;                 0)
;;        :exec x)
;;   ///
;;   (defthm aig-var-fix-when-aig-var-p
;;     (implies (acl2::aig-var-p x)
;;              (equal (aig-var-fix x) x)))

;;   (fty::deffixtype aig-var
;;     :pred acl2::aig-var-p
;;     :fix aig-var-fix
;;     :equiv aig-var-equiv
;;     :define t))


;; (define bfr-varname-p (x &optional (logicman 'logicman))
;;   (bfr-case :bdd (natp x)
;;     :aig (acl2::aig-var-p x)
;;     :aignet (natp x))
;;   ///
;;   (define bfr-varname-fix ((x bfr-varname-p) &optional (logicman 'logicman))
;;     :returns (new-x bfr-varname-p)
;;     (bfr-case :bdd (nfix x)
;;       :aig (aig-var-fix x)
;;       :aignet (nfix x))
;;     ///
;;     (defthm bfr-varname-fix-when-bfr-varname-p
;;       (implies (bfr-varname-p x)
;;                (equal (bfr-varname-fix x) x)))

;;     (defthm nfix-of-bfr-varname-fix
;;       (equal (nfix (bfr-varname-fix x))
;;              (nfix x))
;;       :hints(("Goal" :in-theory (enable bfr-varname-fix aig-var-fix))))

;;     (defthm bfr-varname-fix-of-nfix
;;       (equal (bfr-varname-fix (nfix x))
;;              (nfix x))
;;       :hints(("Goal" :in-theory (enable bfr-varname-fix))))

;;     (defthm bfr-varname-p-when-natp
;;       (implies (natp x)
;;                (bfr-varname-p x))
;;       :hints(("Goal" :in-theory (enable bfr-varname-p))))))


(define bfr-lookup ((n natp) env &optional (logicman 'logicman))
  ;; :prepwork ((local (in-theory (enable bfr-varname-p))))
  (lbfr-case
    :bdd (and (nth n (list-fix env)) t)
    :aig (acl2::aig-env-lookup (lnfix n) env)
    :aignet (bool-fix (cdr (hons-assoc-equal (lnfix n) env))))
  ///
  (def-updater-independence-thm bfr-lookup-logicman-updater-indep
    (implies (equal (lbfr-mode new) (lbfr-mode old))
             (equal (bfr-lookup n env new)
                    (bfr-lookup n env old)))))

(define bfr-set-var ((n natp) val env &optional (logicman 'logicman))
  :parents (bfr)
  :short "Set the @('n')th BFR variable to some value in an AIG/BDD environment."
  (lbfr-case :bdd (acl2::with-guard-checking
                   nil
                   (ec-call (update-nth n (and val t) env)))
    :aig (hons-acons (lnfix n) (and val t) env)
    :aignet (hons-acons (lnfix n) (and val t) env))
  ///
  (in-theory (disable (:e bfr-set-var)))

  (defthm bfr-lookup-bfr-set-var
    (equal (bfr-lookup n (bfr-set-var m val env))
           (if (equal (nfix n) (nfix m))
               (and val t)
             (bfr-lookup n env)))
    :hints(("Goal" :in-theory (e/d (bfr-lookup bfr-set-var)
                                   (update-nth nth)))))

  (defthm bfr-set-var-of-logicman-extension
    (implies (bind-logicman-extension new old)
             (equal (bfr-set-var n val env new)
                    (bfr-set-var n val env old)))))


;; (defsection bfr-semantic-depends-on

;;   (defun-sk bfr-semantic-depends-on (k x logicman)
;;     (exists (env v)
;;             (not (equal (bfr-eval x (bfr-set-var k v env))
;;                         (bfr-eval x env)))))

;;   (defthm bfr-semantic-depends-on-of-set-var
;;     (implies (not (bfr-semantic-depends-on k x logicman))
;;              (equal (bfr-eval x (bfr-set-var k v env))
;;                     (bfr-eval x env))))

;;   (in-theory (disable bfr-semantic-depends-on
;;                       bfr-semantic-depends-on-suff))

;;   (defthm bfr-semantic-depends-on-bdd-mode
;;     (implies (and (syntaxp (not (equal logicman ''nil)))
;;                   (not (bfr-mode logicman)))
;;              (equal (bfr-semantic-depends-on k x logicman)
;;                     (bfr-semantic-depends-on k x nil)))
;;     :hints (("goal" :cases (bfr-semantic-depends-on k x logicman))
;;             (and stable-under-simplificationp
;;                  (b* ((lit (assoc 'bfr-semantic-depends-on clause))
;;                       (other-lit `(bfr-semantic-depends-on k x ,(if (equal (fourth lit) 'logicman) nil 'logicman))))
;;                    `(:expand (,other-lit)
;;                      :use ((:instance bfr-semantic-depends-on-suff
;;                             (env (mv-nth 0 (bfr-semantic-depends-on-witness . ,(cdr other-lit))))
;;                             (v (mv-nth 1 (bfr-semantic-depends-on-witness . ,(cdr other-lit))))
;;                             (logicman ,(fourth lit))))
;;                      :in-theory (e/d (bfr-eval bfr-set-var logicman->mode bfr-fix))))))))

(local
 #!acl2
 (defthm eval-bdd-of-update-when-not-dependent-fix
   (implies (not (nth n (ubdd-deps (ubdd-fix x))))
            (equal (eval-bdd x (update-nth n v env))
                   (eval-bdd x env)))
   :hints (("goal" :use ((:instance eval-bdd-of-update-when-not-dependent
                          (x (ubdd-fix x))))))))



(local 
 #!acl2
 (encapsulate nil
   (local (defthm boolean-listp-of-or-list
            (implies (and (boolean-listp x) (boolean-listp y))
                     (boolean-listp (or-lists x y)))
            :hints(("Goal" :in-theory (enable or-lists)))))
   (defthm boolean-listp-of-ubdd-deps
     (boolean-listp (ubdd-deps x))
     :hints(("Goal" :in-theory (enable ubdd-deps))))))

(define bfr-depends-on ((v natp) (x lbfr-p) &optional (logicman 'logicman))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-varname-p))))
  :returns (val booleanp :rule-classes :type-prescription)
  :prepwork ((local (defthm booleanp-nth-of-boolean-listp
                      (implies (boolean-listp x)
                               (booleanp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth))))))
  (b* ((bfrstate (logicman->bfrstate)))
    (bfrstate-case
      :bdd (nth v (acl2::ubdd-deps (bfr-fix x)))
      :aig (set::in (lnfix v) (acl2::aig-vars (bfr-fix x)))
      :aignet
      (b* ((lit (bfr->aignet-lit x)))
        (stobj-let ((aignet (logicman->aignet logicman)))
                   (depends-on)
                   (and (< (lnfix v) (aignet::num-ins aignet))
                        (aignet::depends-on (satlink::lit->var lit)
                                            (aignet::innum->id v aignet)
                                            aignet))
                   depends-on))))
  ///
  ;; (local (defthm alist-to-bitarr-aux-of-update-less
  ;;          (implies (< (nfix m) (nfix n))
  ;;                   (acl2::bits-equiv (alist-to-bitarr-aux n alist (update-nth m val bitarr))
  ;;                                     (update-nth m val (alist-to-bitarr-aux n alist bitarr))))
  ;;          :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))

  ;; (local (defthm alist-to-bitarr-aux-of-cons
  ;;          (equal (alist-to-bitarr-aux n (cons (cons var val) alist) bitarr)
  ;;                 (if (and (natp var)
  ;;                          (<= (nfix n) var)
  ;;                          (< var (len bitarr)))
  ;;                     (update-nth var (bool->bit val) (alist-to-bitarr-aux n alist bitarr))
  ;;                    (alist-to-bitarr-aux n alist bitarr)))
  ;;          :hints(("Goal" :in-theory (enable alist-to-bitarr-aux)
  ;;                  :induct (alist-to-bitarr-aux n alist bitarr)))))



  (local (defthm alist-to-bitarr-of-cons
           (acl2::bits-equiv (alist-to-bitarr max (cons (cons var val) alist) bitarr)
                             (if (and (natp var)
                                      (< var (nfix max)))
                                 (update-nth var (bool->bit val) (alist-to-bitarr max alist bitarr))
                               (alist-to-bitarr max alist bitarr)))
           :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))
  
  (local (defthm aig-eval-of-cons-env-when-not-member-aig-vars
           (implies (not (set::in v (acl2::aig-vars x)))
                    (equal (acl2::aig-eval x (cons (cons v val) env))
                           (acl2::aig-eval x env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval acl2::aig-vars)))))

  (defthm bfr-depends-on-of-bfr-fix
    (b* ((bfrstate (logicman->bfrstate)))
      (equal (bfr-depends-on v (bfr-fix x))
             (bfr-depends-on v x)))
    :hints ((acl2::use-termhint
             (lbfr-case
               :bdd '(:in-theory (enable bfr-fix))))))

  (defthm bfr-eval-of-bfr-set-var-when-not-depends-on
    (implies (not (bfr-depends-on v x))
             (equal (bfr-eval x (bfr-set-var v val env))
                    (bfr-eval x env)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (bfr-eval bfr-set-var bfr-fix logicman->mode)
                                   ((logicman->mode)))))))

  (local (defthm not-depends-on-0
           (not (aignet::depends-on id 0 aignet))
           :hints(("Goal" :in-theory (enable aignet::depends-on)))))

  (local
   #!aignet
   (defthm fanin-count-of-lookup-in-extension-when-not-in-orig
     (implies (and (aignet-extension-p new old)
                   (< (nfix v) (stype-count stype new))
                   (<= (stype-count stype old) (nfix v))
                   (not (equal (ctype stype) (out-ctype))))
              (< (fanin-count old) (fanin-count (lookup-stype v stype new))))
     :hints(("Goal" :induct (aignet-extension-p new old)
             :in-theory (e/d ((:i aignet-extension-p)
                              fanin-node-p)
                             (AIGNET::AIGNET-EXTENSION-SIMPLIFY-LOOKUP-STYPE-WHEN-COUNTS-SAME))
             :expand ((aignet-extension-p new old)
                      (stype-count stype new)
                      (lookup-stype v stype new)
                      (fanin-count new))))))

  (local
   #!aignet
   (defthm depends-on-of-out-of-bounds-ci-id
     (implies (< (fanin-count aignet) (nfix ci-id))
              (not (aignet::depends-on id ci-id aignet)))
     :hints(("Goal" :in-theory (enable aignet::depends-on)))))

  (defthm bfr-depends-on-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-p x old))
             (equal (bfr-depends-on v x new)
                    (bfr-depends-on v x old)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable logicman-extension-p
                                      bfr-p bfr-varname-p
                                      aignet::consp-of-lookup-stype)))
            (and stable-under-simplificationp
                 '(:cases ((< (nfix v) (aignet::stype-count :pi (logicman->aignet old))))))
            (and stable-under-simplificationp
                 '(:cases ((< (nfix v) (aignet::stype-count :pi (logicman->aignet new)))))))))


(define bfr-list-depends-on ((v natp) (x lbfr-listp) &optional (logicman 'logicman))
  :returns (val booleanp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (or (bfr-depends-on v (car x))
        (bfr-list-depends-on v (cdr x))))

  ///

  (defthm bfr-list-depends-on-of-bfr-list-fix
    (equal (bfr-list-depends-on v (lbfr-list-fix x))
           (bfr-list-depends-on v x)))

  (fty::deffixcong acl2::list-equiv equal (bfr-list-depends-on v x) x)

  (defthm bfr-list-eval-of-bfr-set-var-when-not-depends-on
    (implies (not (bfr-list-depends-on v x))
             (equal (bfr-list-eval x (bfr-set-var v val env))
                    (bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-list-eval))))

  (defthm bfr-list-depends-on-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp x old))
             (equal (bfr-list-depends-on v x new)
                    (bfr-list-depends-on v x old))))

  (defthm bfr-list-depends-on-of-nil
    (not (bfr-list-depends-on v nil)))

  (defthm bfr-list-depends-on-of-append
    (equal (bfr-list-depends-on v (append a b))
           (or (bfr-list-depends-on v a)
               (bfr-list-depends-on v b))))

  (defthm bfr-list-depends-on-of-cons
    (equal (bfr-list-depends-on v (cons a b))
           (or (bfr-depends-on v a)
               (bfr-list-depends-on v b))))

  (defthmd bfr-list-depends-on-when-consp
    (implies (consp x)
             (equal (bfr-list-depends-on v x)
                    (or (bfr-depends-on v (car x))
                        (bfr-list-depends-on v (cdr x))))))

  (defthm bfr-depends-on-of-car-when-bfr-list-depends-on
    (implies (not (bfr-list-depends-on v x))
             (not (bfr-depends-on v (car x))))
    :hints (("goal" :expand ((bfr-depends-on v nil))
             :in-theory (enable bfr->aignet-lit)))))
                                


(define bfr-var ((n natp) &optional (logicman 'logicman))
  :guard (bfr-varname-p n)
  :returns (bfr lbfr-p :hints((acl2::use-termhint
                               (lbfr-case
                                 :aignet nil
                                 :otherwise
                                 '(:in-theory (enable bfr-p aig-p
                                                      bfr-nvars)))))
                :hyp (< (nfix n) (bfr-nvars logicman)))
  :guard-hints (("goal" :in-theory (enable bfr-varname-p bfr-nvars)))
  (b* ((bfrstate (logicman->bfrstate)))
    (bfrstate-case
      :bdd (acl2::qv n)
      :aig (lnfix n)
      :aignet (stobj-let
               ((aignet (logicman->aignet logicman)))
               (lit)
               (aignet::make-lit (aignet::innum->id n aignet) 0)
               (aignet-lit->bfr lit))))
  ///
  ;; (local (defthm bounded-lit-fix-is-aignet-lit-fix
  ;;          (equal (

  (defthm bfr-eval-of-bfr-var
    (implies (bfr-varname-p n)
             (equal (bfr-eval (bfr-var n) env)
                    (bfr-lookup n env)))
    :hints(;; ("Goal" :in-theory (enable bfr-varname-p
           ;;                            bfr-eval
           ;;                            bfr-fix
           ;;                            aig-fix
           ;;                            bfr-lookup
           ;;                            aignet::lit-eval-of-aignet-lit-fix)
           ;;  :expand ((:free (id invals regvals aignet)
           ;;            (aignet::lit-eval (aignet::make-lit id 0) invals regvals aignet))
           ;;           (:free (n invals regvals aignet)
           ;;            (aignet::id-eval (aignet::fanin-count (aignet::lookup-stype n :pi aignet))
           ;;                             invals regvals aignet))))
           (acl2::use-termhint
            (lbfr-case
              :aignet '(:in-theory (enable bfr-eval ;; logicman->bfrstate
                                           bfr-lookup bfr-varname-p bfr-nvars)
                        :expand ((:free (id invals regvals aignet)
                                  (aignet::lit-eval (aignet::make-lit id 0) invals regvals aignet))
                                 (:free (id invals regvals aignet)
                                  (aignet::id-eval id invals regvals aignet))))
              :otherwise '(:in-theory (enable bfr-varname-p
                                              bfr-eval
                                              bfr-fix
                                              aig-fix
                                              bfr-nvars
                                              bfr-lookup)))))
    :otf-flg t)

  (defthm bfr-var-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p n old))
             (equal (bfr-var n new)
                    (bfr-var n old)))
    :hints((acl2::use-termhint
            (lbfr-case old
              :aignet '(:in-theory (enable ;; logicman->bfrstate
                                           logicman-extension-p bfr-varname-p bfr-nvars
                                           aignet-lit->bfr bounded-lit-fix))
              :otherwise '(:in-theory (enable logicman-extension-p aignet-lit->bfr
                                              bfr-varname-p))))))

  (defthm bfr-depends-on-of-bfr-var
    (implies (and (bfr-varname-p v)
                  (bfr-varname-p n))
             (iff (bfr-depends-on v (bfr-var n))
                  (equal (nfix v) (nfix n))))
    :hints(("Goal" :in-theory (enable bfr-depends-on bfr-varname-p bfr-nvars bfr-fix aig-fix
                                      bounded-lit-fix ;; logicman->bfrstate
                                      )
            :expand ((:free (ci x) (aignet::depends-on
                                    (aignet::fanin-count x)
                                    ci
                                    (logicman->aignet logicman))))))))


(local (defthm aig-p-when-bfr-p
         (implies (and (bfr-p x)
                       (bfrstate-mode-is :aig)
                       (equal bound (bfrstate->bound bfrstate)))
                  (aig-p x bound))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm aig-p-of-bfr-fix
         (implies (and (bfrstate-mode-is :aig)
                       (equal bound (bfrstate->bound bfrstate)))
                  (aig-p (bfr-fix x) bound))
         :hints (("goal" :use ((:instance aig-p-when-bfr-p
                                (x (bfr-fix x))))
                  :in-theory (disable aig-p-when-bfr-p)))))

(local (defthm bfr-p-when-aig-p
         (implies (and (bfrstate-mode-is :aig)
                       (aig-p x (bfrstate->bound bfrstate)))
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(defthm logicman->mode-when-not-others
  (implies (and (not (equal (logicman->mode logicman) (bfrmode :bdd)))
                (not (equal (logicman->mode logicman) (bfrmode :aignet))))
           (equal (equal (logicman->mode logicman) (bfrmode :aig)) t)))

(local (defthm ubdd-p-when-bfr-p
         (implies (and (bfr-p x)
                       (bfrstate-mode-is :bdd)
                       (equal bound (bfrstate->bound bfrstate)))
                  (and (ubddp x bound)
                       (acl2::ubddp x)))
         :hints(("Goal" :in-theory (enable bfr-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable ubddp))))))

(local (defthm ubdd-p-of-bfr-fix
         (implies (and (bfrstate-mode-is :bdd)
                       (equal bound (bfrstate->bound bfrstate)))
                  (and (ubddp (bfr-fix x) bound)
                       (acl2::ubddp (bfr-fix x))))
         :hints (("goal" :use ((:instance ubdd-p-when-bfr-p
                                (x (bfr-fix x))))
                  :in-theory (disable ubdd-p-when-bfr-p))
                 (and stable-under-simplificationp
                      '(:in-theory (enable ubddp))))))

(local (defthm bfr-p-when-ubdd-p
         (implies (and (bfrstate-mode-is :bdd)
                       (ubddp x (bfrstate->bound bfrstate)))
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm aignet-litp-when-bfr-p
         (b* ((bfrstate (logicman->bfrstate)))
           (implies (and (bfr-p x)
                         (bfrstate-mode-is :aignet)
                         (not (booleanp x)))
                    (aignet::aignet-litp x (logicman->aignet logicman))))
         :hints(("Goal" :in-theory (enable bfr-p aignet::aignet-idp logicman->bfrstate)))))

(local (defthm bfr-p-when-aignet-litp
         (b* ((bfrstate (logicman->bfrstate)))
           (implies (and (bfrstate-mode-is :aignet)
                         (aignet::aignet-litp x (logicman->aignet logicman))
                         (satlink::litp x)
                         (not (equal x 1))
                         (not (equal x 0)))
                    (bfr-p x)))
         :hints(("Goal" :in-theory (enable bfr-p aignet::aignet-idp logicman->bfrstate)))))

(local (defthm bfr-mode-is-possibilities
         (or (bfr-mode-is :aig)
             (bfr-mode-is :aignet)
             (bfr-mode-is :bdd))
         :rule-classes ((:forward-chaining :trigger-terms ((bfr-mode-fix bfr-mode))))))


(define bfr-not ((x lbfr-p) &optional (logicman 'logicman))
  :returns (bfr lbfr-p :hints((and stable-under-simplificationp
                                   '(:in-theory (enable bfr-p
                                                        aignet-lit->bfr
                                                        bfr->aignet-lit)))))
  :prepwork ((local (defthm lit->var-not-0
                      (implies (and (satlink::litp x)
                                    (not (equal x 1))
                                    (not (equal x 0)))
                               (not (equal (satlink::lit->var x) 0)))
                      :hints (("goal" :use ((:instance satlink::equal-of-make-lit
                                             (a 1) (var (satlink::lit->var x)) (neg (satlink::lit->neg x)))
                                            (:instance satlink::equal-of-make-lit
                                             (a 0) (var (satlink::lit->var x)) (neg (satlink::lit->neg x)))))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-p bfr->aignet-lit aignet-lit->bfr
                                          satlink::lit-negate
                                          satlink::equal-of-make-lit))))
  (mbe :logic (b* ((x (lbfr-fix x)))
                (lbfr-case
                  :bdd (acl2::q-not x)
                  :aig (acl2::aig-not x)
                  :aignet (b* ((bfrstate (logicman->bfrstate)))
                            (aignet-lit->bfr
                             (aignet::lit-negate
                              (bfr->aignet-lit x))))))
       :exec (if (booleanp x)
                 (not x)
               (lbfr-case
                 :bdd (acl2::q-not x)
                 :aig (acl2::aig-not x)
                 :aignet (aignet::lit-negate x))))
  ///
  (defthm bfr-eval-of-bfr-not
    (equal (bfr-eval (bfr-not x) env)
           (not (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-not-of-bfr-fix
    (equal (bfr-not (bfr-fix x (logicman->bfrstate)))
           (bfr-not x))
    :hints(("Goal" :in-theory (enable bfr-fix
                                      aignet-lit->bfr))))

  (defthm bfr-depends-on-of-bfr-not
    (implies (not (bfr-depends-on v x))
             (not (bfr-depends-on v (bfr-not x))))
    :hints(("Goal" :in-theory (enable bfr-depends-on))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix)))))

  (defthm bfr-negate-of-logicman->bfrstate
    (equal (bfr-negate x (logicman->bfrstate))
           (bfr-not x))
    :hints(("Goal" :in-theory (enable bfr-negate)))))



(local (defthm aignet-hash-and-of-0
         (and (equal (aignet::aignet-hash-and 0 x gatesimp strash aignet)
                     (mv 0 strash (aignet::node-list-fix aignet)))
              (equal (aignet::aignet-hash-and x 0 gatesimp strash aignet)
                     (mv 0 strash (aignet::node-list-fix aignet))))
         :hints(("Goal" :in-theory (enable aignet::aignet-hash-and
                                           aignet::aignet-and-gate-simp/strash
                                           aignet::reduce-and-gate
                                           aignet::aignet-install-gate
                                           AIGNET::|SIMPLIFY-(AND X0 X1)-LEVEL-1|
                                           aignet::aignet-strash-gate)
                 :expand ((:free (x) (aignet::reduce-gate-rec 0 0 x gatesimp strash aignet))
                          (:free (x) (aignet::reduce-gate-rec 0 x 0 gatesimp strash aignet))
                          (:free (x) (aignet::reduce-gate-rec 4 0 x gatesimp strash aignet)))))))

(local (defthm lit-negate-cond-0
         (equal (satlink::lit-negate-cond x 0)
                (satlink::lit-fix x))
         :hints(("Goal" :in-theory (enable satlink::lit-negate-cond)))))

(local (defthm aignet-hash-and-of-1
         (and (equal (aignet::aignet-hash-and 1 x gatesimp strash aignet)
                     (mv (aignet::aignet-lit-fix x aignet) strash (aignet::node-list-fix aignet)))
              (equal (aignet::aignet-hash-and x 1 gatesimp strash aignet)
                     (mv (aignet::aignet-lit-fix x aignet) strash (aignet::node-list-fix aignet))))
         :hints(("Goal" :in-theory (enable aignet::aignet-hash-and
                                           aignet::aignet-and-gate-simp/strash
                                           aignet::reduce-and-gate
                                           aignet::aignet-install-gate
                                           AIGNET::|SIMPLIFY-(AND X0 X1)-LEVEL-1|
                                           aignet::aignet-strash-gate)
                 :expand ((:free (x) (aignet::reduce-gate-rec 0 1 x gatesimp strash aignet))
                          (:free (x) (aignet::reduce-gate-rec 0 x 1 gatesimp strash aignet))
                          (:free (x) (aignet::reduce-gate-rec 4 x 0 gatesimp strash aignet)))))))

(local (defthm make-lit-of-lit->var
         (implies (and (satlink::litp x)
                       (equal neg (satlink::lit->neg x)))
                  (equal (satlink::make-lit (satlink::lit->var x) neg) x))))

(local (defthm make-lit-of-lit->var-neg
         (implies (and (satlink::litp x)
                       (equal neg (b-not (satlink::lit->neg x))))
                  (equal (satlink::make-lit (satlink::lit->var x) neg) (satlink::lit-negate x)))))

(local (defthm lit-negate-equal-const
         (implies (and (syntaxp (quotep y))
                       (satlink::litp y))
                  (equal (equal (satlink::lit-negate x) y)
                         (equal (satlink::lit-fix x) (satlink::lit-negate y))))
         :hints(("Goal" :in-theory (e/d (satlink::lit-negate
                                           satlink::equal-of-make-lit))))))

(local (defthm aignet-hash-xor-of-consts
         (and (equal (aignet::aignet-hash-xor 0 x gatesimp strash aignet)
                     (mv (aignet::aignet-lit-fix x aignet) strash (aignet::node-list-fix aignet)))
              (equal (aignet::aignet-hash-xor 1 x gatesimp strash aignet)
                     (mv (satlink::lit-negate (aignet::aignet-lit-fix x aignet))
                         strash (aignet::node-list-fix aignet)))
              (equal (aignet::aignet-hash-xor x 0 gatesimp strash aignet)
                     (mv (aignet::aignet-lit-fix x aignet) strash (aignet::node-list-fix aignet)))
              (equal (aignet::aignet-hash-xor x 1 gatesimp strash aignet)
                     (mv (satlink::lit-negate (aignet::aignet-lit-fix x aignet))
                         strash (aignet::node-list-fix aignet))))
         :hints(("Goal" :in-theory (enable aignet::aignet-hash-xor
                                           aignet::aignet-xor-gate-simp/strash
                                           aignet::reduce-xor-gate
                                           aignet::reduce-xor-gate-normalized
                                           aignet::aignet-install-gate
                                           AIGNET::|SIMPLIFY-(XOR X0 X1)-LEVEL-1|
                                           aignet::aignet-strash-gate
                                           aignet::aignet-lit-fix
                                           satlink::equal-of-make-lit
                                           )
                 :expand ((:free (x y) (aignet::reduce-gate-rec 2 x y gatesimp strash aignet))
                          (:free (x y) (aignet::reduce-gate-rec 4 x y gatesimp strash aignet))
                          (:free (x y) (aignet::reduce-gate-rec 5 x y gatesimp strash aignet)))))))



(local (in-theory (disable set::in-tail))) ;; incompatible with trivial ancestors check

(local (defthm lit->var-lte-when-aignet-litp
         (implies (aignet::aignet-litp x aignet)
                  (<= (satlink::lit->var x) (aignet::fanin-count aignet)))
         :hints(("Goal" :in-theory (enable aignet::aignet-idp)))))


(local
 #!aignet
 (defthm node-listp-when-aignetp
   (implies (aignetp x)
            (node-listp x))
   :hints(("Goal" :in-theory (enable aignetp)))))

;; (defthm aignet-litp-of-bfr->aignet-lit-bfrstate
;;   (aignet::aignet-litp (bfr->aignet-lit x (bfrstate 0 (aignet::fanin-count aignet))) aignet)
;;   :hints(("Goal" :in-theory (enable bfr->aignet-lit aignet::aignet-idp bfr-fix aignet-lit->bfr))))

;; (local (in-theory (disable (force)
;;                            ;; acl2::q-and-of-t-slow
;;                            )))



(define bfr-and ((x lbfr-p)
                 (y lbfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (and-bfr (lbfr-p and-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t))
  :guard-debug t
  (mbe :logic
       (b* ((x (lbfr-fix x))
            (y (lbfr-fix y)))
         (lbfr-case
           :bdd (mv (acl2::q-binary-and x y) logicman)
           :aig (mv (acl2::aig-and x y) logicman)
           :aignet (b* ((bfrstate (logicman->bfrstate))
                        (x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-and x y (aignet::default-gatesimp) aignet::strash aignet)
                      (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman))))))
       :exec
       (cond ((not x) (mv nil logicman))
             ((not y) (mv nil logicman))
             ((eq x t) (mv y logicman))
             ((eq y t) (mv x logicman))
             (t (b* ((bfrstate (logicman->bfrstate)))
                  (bfrstate-case
                  :bdd (mv (acl2::q-binary-and x y) logicman)
                  :aig (mv (acl2::aig-and x y) logicman)
                  :aignet
                  (b* ((x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-and x y (aignet::default-gatesimp) aignet::strash aignet)
                     (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman)))))))))
  ///
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-eval-of-bfr-and
    (equal (bfr-eval and-bfr env new-logicman)
           (and (bfr-eval x env logicman)
                (bfr-eval y env logicman)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-and-of-bfr-fix-x
    (equal (bfr-and (lbfr-fix x) y)
           (bfr-and x y)))

  (defthm bfr-and-of-bfr-fix-y
    (equal (bfr-and x (lbfr-fix y))
           (bfr-and x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman) (bfr-nvars logicman)))

  (defret logicman-get-of-<fn>
    (implies (and (equal key1 (logicman-field-fix key))
                  (not (eq key1 :aignet))
                  (not (eq key1 :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret bfr-depends-on-of-<fn>
    (implies (and (not (bfr-depends-on v x))
                  (not (bfr-depends-on v y)))
             (not (bfr-depends-on v and-bfr new-logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-depends-on)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix))))))



(define bfr-or ((x lbfr-p)
                (y lbfr-p)
                &optional (logicman 'logicman))
  :returns (mv (or-bfr (lbfr-p or-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable aignet::aignet-hash-or)))

  (mbe :logic
       (b* ((x (lbfr-fix x))
            (y (lbfr-fix y)))
         (lbfr-case
           :bdd (mv (acl2::q-binary-or x y) logicman)
           :aig (mv (acl2::aig-or x y) logicman)
           :aignet (b* ((bfrstate (logicman->bfrstate))
                        (x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-or x y (aignet::default-gatesimp) aignet::strash aignet)
                      (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman))))))
       :exec
       (cond ((eq x t) (mv t logicman))
             ((eq y t) (mv t logicman))
             ((eq x nil) (mv y logicman))
             ((eq y nil) (mv x logicman))
             (t (lbfr-case
                  :bdd (mv (acl2::q-binary-or x y) logicman)
                  :aig (mv (acl2::aig-or x y) logicman)
                  :aignet
                  (b* ((bfrstate (logicman->bfrstate))
                       (x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-or x y (aignet::default-gatesimp) aignet::strash aignet)
                     (b* ((bfrstate (logicman->bfrstate)))
                       (mv (aignet-lit->bfr lit) logicman))))))))
  ///
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-eval-of-bfr-or
    (equal (bfr-eval or-bfr env new-logicman)
           (or (bfr-eval x env logicman)
               (bfr-eval y env logicman)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-or-of-bfr-fix-x
    (equal (bfr-or (lbfr-fix x) y)
           (bfr-or x y)))

  (defthm bfr-or-of-bfr-fix-y
    (equal (bfr-or x (lbfr-fix y))
           (bfr-or x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman) (bfr-nvars logicman)))

  (defret logicman-get-of-<fn>
    (implies (and (equal key1 (logicman-field-fix key))
                  (not (eq key1 :aignet))
                  (not (eq key1 :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret bfr-depends-on-of-<fn>
    (implies (and (not (bfr-depends-on v x))
                  (not (bfr-depends-on v y)))
             (not (bfr-depends-on v or-bfr new-logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-depends-on)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix acl2::aig-or))))))


(local (defthm ubddp-implies-ubddp
         (implies (ubddp x bound)
                  (acl2::ubddp x))
         :hints(("Goal" :in-theory (enable ubddp)))
         :rule-classes :forward-chaining))

(define bfr-xor ((x lbfr-p)
                 (y lbfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (xor-bfr (lbfr-p xor-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable bfr-not acl2::aig-xor acl2::q-xor))
                (and stable-under-simplificationp '(:in-theory (enable bfr-p))))
  :guard-debug t
  (mbe :logic
       (b* ((x (lbfr-fix x))
            (y (lbfr-fix y)))
         (lbfr-case
           :bdd (mv (acl2::q-binary-xor x y) logicman)
           :aig (mv (acl2::aig-xor x y) logicman)
           :aignet (b* ((bfrstate (logicman->bfrstate))
                        (x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-xor x y (aignet::default-gatesimp) aignet::strash aignet)
                      (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman))))))
       :exec
       (cond ((eq x t) (mv (bfr-not y) logicman))
             ((eq x nil) (mv y logicman))
             ((eq y t) (mv (bfr-not x) logicman))
             ((eq y nil) (mv x logicman))
             (t (lbfr-case
                  :bdd (mv (acl2::q-binary-xor x y) logicman)
                  :aig (mv (acl2::aig-xor x y) logicman)
                  :aignet
                  (b* ((bfrstate (logicman->bfrstate))
                       (x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-xor x y (aignet::default-gatesimp) aignet::strash aignet)
                     (b* ((bfrstate (logicman->bfrstate)))
                       (mv (aignet-lit->bfr lit) logicman))))))))
  ///
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-eval-of-bfr-xor
    (equal (bfr-eval xor-bfr env new-logicman)
           (xor (bfr-eval x env logicman)
                (bfr-eval y env logicman)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-xor-of-bfr-fix-x
    (equal (bfr-xor (lbfr-fix x) y)
           (bfr-xor x y)))

  (defthm bfr-xor-of-bfr-fix-y
    (equal (bfr-xor x (lbfr-fix y))
           (bfr-xor x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman) (bfr-nvars logicman)))

  (defret logicman-get-of-<fn>
    (implies (and (equal key1 (logicman-field-fix key))
                  (not (eq key1 :aignet))
                  (not (eq key1 :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret bfr-depends-on-of-<fn>
    (implies (and (not (bfr-depends-on v x))
                  (not (bfr-depends-on v y)))
             (not (bfr-depends-on v xor-bfr new-logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-depends-on)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix acl2::aig-xor acl2::aig-or))))))


(define bfr-iff ((x lbfr-p)
                 (y lbfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (iff-bfr (lbfr-p iff-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable bfr-not acl2::aig-iff acl2::q-iff
                                    aignet::aignet-hash-iff))
                (and stable-under-simplificationp '(:in-theory (enable bfr-p))))

  (mbe :logic
       (b* ((x (lbfr-fix x))
            (y (lbfr-fix y)))
         (lbfr-case
           :bdd (mv (acl2::q-binary-iff x y) logicman)
           :aig (mv (acl2::aig-iff x y) logicman)
           :aignet (b* ((bfrstate (logicman->bfrstate))
                        (x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-iff x y (aignet::default-gatesimp) aignet::strash aignet)
                      (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman))))))
       :exec
       (cond ((eq x nil) (mv (bfr-not y) logicman))
             ((eq x t) (mv y logicman))
             ((eq y nil) (mv (bfr-not x) logicman))
             ((eq y t) (mv x logicman))
             (t (lbfr-case
                  :bdd (mv (acl2::q-binary-iff x y) logicman)
                  :aig (mv (acl2::aig-iff x y) logicman)
                  :aignet
                  (b* ((bfrstate (logicman->bfrstate))
                       (x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-iff x y (aignet::default-gatesimp) aignet::strash aignet)
                     (b* ((bfrstate (logicman->bfrstate)))
                       (mv (aignet-lit->bfr lit) logicman))))))))
  ///
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-eval-of-bfr-iff
    (equal (bfr-eval iff-bfr env new-logicman)
           (iff (bfr-eval x env logicman)
                (bfr-eval y env logicman)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-iff-of-bfr-fix-x
    (equal (bfr-iff (lbfr-fix x) y)
           (bfr-iff x y)))

  (defthm bfr-iff-of-bfr-fix-y
    (equal (bfr-iff x (lbfr-fix y))
           (bfr-iff x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman) (bfr-nvars logicman)))
  
  (defret logicman-get-of-<fn>
    (implies (and (equal key1 (logicman-field-fix key))
                  (not (eq key1 :aignet))
                  (not (eq key1 :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret bfr-depends-on-of-<fn>
    (implies (and (not (bfr-depends-on v x))
                  (not (bfr-depends-on v y)))
             (not (bfr-depends-on v iff-bfr new-logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-depends-on)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix acl2::aig-iff  acl2::aig-or))))))




(local (defthm equal-of-bfr->aignet-lit
         (implies (and (bfr-p x) (bfr-p y)
                       (bfrstate-mode-is :aignet))
                  (iff (equal (bfr->aignet-lit x) (bfr->aignet-lit y))
                       (equal x y)))
         :hints (("goal" :use ((:instance aignet-lit->bfr-of-bfr->aignet-lit (x x))
                               (:instance aignet-lit->bfr-of-bfr->aignet-lit (x y)))
                  :in-theory (disable aignet-lit->bfr-of-bfr->aignet-lit)))))

(define bfr-ite ((x lbfr-p)
                 (y lbfr-p)
                 (z lbfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (ite-bfr (lbfr-p ite-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable acl2::aig-ite-fn aignet::aignet-hash-mux
                                    aignet::aignet-hash-or)))

  (mbe :logic
       (b* ((x (lbfr-fix x))
            (y (lbfr-fix y))
            (z (lbfr-fix z)))
         (lbfr-case
           :bdd (mv (acl2::q-ite x y z) logicman)
           :aig (mv (acl2::aig-ite x y z) logicman)
           :aignet (b* ((bfrstate (logicman->bfrstate))
                        (x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y))
                        (z (bfr->aignet-lit z)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-mux x y z (aignet::default-gatesimp) aignet::strash aignet)
                      (b* ((bfrstate (logicman->bfrstate)))
                        (mv (aignet-lit->bfr lit) logicman))))))
       :exec
       (cond ((eq x t) (mv y logicman))
             ((eq x nil) (mv z logicman))
             ((hons-equal y z) (mv y logicman))
             (t (lbfr-case
                  :bdd (mv (acl2::q-ite x y z) logicman)
                  :aig (mv (acl2::aig-ite x y z) logicman)
                  :aignet
                  (b* ((bfrstate (logicman->bfrstate))
                       (x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y))
                       (z (bfr->aignet-lit z)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-mux x y z (aignet::default-gatesimp) aignet::strash aignet)
                     (b* ((bfrstate (logicman->bfrstate)))
                       (mv (aignet-lit->bfr lit) logicman))))))))
  ///
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-eval-of-bfr-ite
    (equal (bfr-eval ite-bfr env new-logicman)
           (if (bfr-eval x env logicman)
               (bfr-eval y env logicman)
             (bfr-eval z env logicman)))
    :hints(("Goal" :in-theory (enable bfr-eval)
            :do-not-induct t))
    :otf-flg t)

  (defthm bfr-ite-of-bfr-fix-x
    (equal (bfr-ite (lbfr-fix x) y z)
           (bfr-ite x y z)))

  (defthm bfr-ite-of-bfr-fix-y
    (equal (bfr-ite x (lbfr-fix y) z)
           (bfr-ite x y z)))
  
  (defthm bfr-ite-of-bfr-fix-z
    (equal (bfr-ite x y (lbfr-fix z))
           (bfr-ite x y z)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman) (bfr-nvars logicman)))
  
  (defret logicman-get-of-<fn>
    (implies (and (equal key1 (logicman-field-fix key))
                  (not (eq key1 :aignet))
                  (not (eq key1 :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret bfr-depends-on-of-<fn>
    (implies (and (not (bfr-depends-on v x))
                  (not (bfr-depends-on v y))
                  (not (bfr-depends-on v z)))
             (not (bfr-depends-on v ite-bfr new-logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-depends-on)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix acl2::aig-ite acl2::aig-or))))))





;; (define alist-fix ((x alistp))
;;   :returns (new-x alistp)
;;   :inline t
;;   :verify-guards nil
;;   (mbe :logic
;;        (if (atom x)
;;            nil
;;          (if (consp (car x))
;;              (cons (car x)
;;                    (alist-fix (cdr x)))
;;            (alist-fix (cdr x))))
;;        :exec x)
;;   ///
;;   (defret alist-fix-when-alistp
;;     (implies (alistp x)
;;              (equal (alist-fix x) x)))

;;   (verify-guards alist-fix$inline)

;;   (fty::deffixtype alist :pred alistp :fix alist-fix :equiv alist-fix-equiv :define t))

(fty::defmap obj-alist :true-listp t)

(fty::defprod fgl-env
  :parents (fgl-object-eval)
  :short "Type of environment objects for FGL object evaluation."
  ((obj-alist obj-alist "Alist mapping free variable names to their values")
   (bfr-vals            "Boolean function evaluation environment for use by @(see bfr-eval)"))
  :layout :tree)

(define gobj-bfr-eval ((x lbfr-p)
                       (env fgl-env-p)
                       &optional (logicman 'logicman))
  :returns (bool t)
  (bfr-eval x (fgl-env->bfr-vals env))
  ///
  (defthm gobj-bfr-eval-consts
    (and (equal (gobj-bfr-eval t env) t)
         (equal (gobj-bfr-eval nil env) nil)))

  (defthm gobj-bfr-eval-of-bfr-fix
    (equal (gobj-bfr-eval (lbfr-fix x) env)
           (gobj-bfr-eval x env)))
  
  (defthm gobj-bfr-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-p x old))
             (equal (gobj-bfr-eval x env new)
                    (gobj-bfr-eval x env old))))

  (defthm gobj-bfr-eval-of-bfr-var
    (implies (bfr-varname-p n)
             (equal (gobj-bfr-eval (bfr-var n) env)
                    (bfr-lookup n (fgl-env->bfr-vals env)))))

  (defthm gobj-bfr-eval-of-bfr-not
    (equal (gobj-bfr-eval (bfr-not x) env)
           (not (gobj-bfr-eval x env))))

  (defret gobj-bfr-eval-of-bfr-and
    (equal (gobj-bfr-eval and-bfr env new-logicman)
           (and (gobj-bfr-eval x env logicman)
                (gobj-bfr-eval y env logicman)))
    :fn bfr-and)

  (defret gobj-bfr-eval-of-bfr-or
    (equal (gobj-bfr-eval or-bfr env new-logicman)
           (or (gobj-bfr-eval x env logicman)
               (gobj-bfr-eval y env logicman)))
    :fn bfr-or)

  (defret gobj-bfr-eval-of-bfr-xor
    (equal (gobj-bfr-eval xor-bfr env new-logicman)
           (xor (gobj-bfr-eval x env logicman)
                (gobj-bfr-eval y env logicman)))
    :fn bfr-xor)

  (defret gobj-bfr-eval-of-bfr-iff
    (equal (gobj-bfr-eval iff-bfr env new-logicman)
           (iff (gobj-bfr-eval x env logicman)
                (gobj-bfr-eval y env logicman)))
    :fn bfr-iff)

  (defret gobj-bfr-eval-of-bfr-ite
    (equal (gobj-bfr-eval ite-bfr env new-logicman)
           (if (gobj-bfr-eval x env logicman)
               (gobj-bfr-eval y env logicman)
             (gobj-bfr-eval z env logicman)))
    :fn bfr-ite)

  
  (defthm gobj-bfr-eval-reduce-by-bfr-eval
    (implies (and (equal ans (bfr-eval x (fgl-env->bfr-vals env)))
                  (syntaxp (pseudo-term-case ans :fncall (not (eq ans.fn 'bfr-eval-fn)) :otherwise t)))
             (equal (gobj-bfr-eval x env) ans))))


(define gobj-bfr-list-eval ((x lbfr-listp) (env fgl-env-p) &optional (logicman 'logicman))
  :returns (bools boolean-listp)
  (if (atom x)
      nil
    (cons (gobj-bfr-eval (car x) env)
          (gobj-bfr-list-eval (cdr x) env)))
  ///
  (defthm gobj-bfr-list-eval-of-gobj-bfr-list-fix
    (equal (gobj-bfr-list-eval (lbfr-list-fix x) env)
           (gobj-bfr-list-eval x env)))

  (defthm gobj-bfr-list-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp x old))
             (equal (gobj-bfr-list-eval x env new)
                    (gobj-bfr-list-eval x env old))))

  (defthm gobj-bfr-list-eval-of-cons
    (equal (gobj-bfr-list-eval (cons a b) env)
           (cons (gobj-bfr-eval a env)
                 (gobj-bfr-list-eval b env))))

  (defthm consp-of-gobj-bfr-list-eval
    (equal (consp (gobj-bfr-list-eval x env))
           (consp x)))
 
  (defthm len-of-gobj-bfr-list-eval
    (equal (len (gobj-bfr-list-eval x env))
           (len x)))

  (fty::deffixequiv gobj-bfr-list-eval :args ((x true-listp) (env fgl-env-p)))

  (defthmd gobj-bfr-list-eval-is-bfr-list-eval
    (equal (gobj-bfr-list-eval x env)
           (bfr-list-eval x (fgl-env->bfr-vals env)))
    :hints(("Goal" :in-theory (enable bfr-list-eval gobj-bfr-eval))))

  (defthm gobj-bfr-list-eval-reduce-by-bfr-list-eval
    (implies (and (equal ans (bfr-list-eval x (fgl-env->bfr-vals env)))
                  (syntaxp (pseudo-term-case ans :fncall (not (eq ans.fn 'bfr-list-eval-fn)) :otherwise t)))
             (equal (gobj-bfr-list-eval x env) ans))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval))))

  (defthmd gobj-bfr-list-eval-of-boolean-list
    (implies (boolean-listp (true-list-fix x))
             (equal (gobj-bfr-list-eval x env) (true-list-fix x)))))


(define gobj-var-lookup ((name pseudo-var-p) (env fgl-env-p))
  :prepwork ((local (defthm consp-of-assoc-when-obj-alist-p
                      (implies (obj-alist-p x)
                               (iff (consp (assoc key x))
                                    (assoc key x))))))
  (cdr (assoc-equal (pseudo-var-fix name) (fgl-env->obj-alist env))))






(define append-alist-vals ((x true-list-listp))
  (if (atom x)
      nil
    (append (cdar x)
            (append-alist-vals (cdr x)))))

(defconst *fgl-object-eval-template*
  '(progn
     (defapply <prefix>-apply <prefix>-ev  <fns>)
     
     (acl2::def-meta-extract <prefix>-ev <prefix>-ev-list)
     (acl2::def-ev-pseudo-term-fty-support <prefix>-ev <prefix>-ev-list)

     (defines <prefix>-object-eval
       :flag-local nil
       (define <prefix>-object-eval ((x lgl-bfr-object-p)
                                      (env fgl-env-p)
                                      &optional (logicman 'logicman))
         :measure (acl2::two-nats-measure (fgl-object-count x) 0)
         :verify-guards nil
         :returns (val)
         (fgl-object-case x
           :g-concrete x.val
           :g-boolean (gobj-bfr-eval x.bool env)
           :g-integer (bools->int (gobj-bfr-list-eval x.bits env))
           :g-ite (if (<prefix>-object-eval x.test env)
                      (<prefix>-object-eval x.then env)
                    (<prefix>-object-eval x.else env))
           :g-apply (<prefix>-apply x.fn (<prefix>-objectlist-eval x.args env))
           :g-var (gobj-var-lookup x.name env)
           :g-cons (cons (<prefix>-object-eval x.car env)
                         (<prefix>-object-eval x.cdr env))
           :g-map (<prefix>-object-alist-eval x.alist env)))
       (define <prefix>-objectlist-eval ((x lgl-bfr-objectlist-p)
                                          (env fgl-env-p)
                                          &optional (logicman 'logicman))
         :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
         :returns (vals true-listp :rule-classes :type-prescription)
         (if (atom x)
             nil
           (cons (<prefix>-object-eval (car x) env)
                 (<prefix>-objectlist-eval (cdr x) env))))
       (define <prefix>-object-alist-eval ((x lgl-bfr-object-alist-p)
                                  (env fgl-env-p)
                                  &optional (logicman 'logicman))
         :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
         :returns (vals)
         (if (atom x)
             x
           (if (mbt (consp (car x)))
               (cons (cons (caar x) (<prefix>-object-eval (cdar x) env))
                     (<prefix>-object-alist-eval (cdr x) env))
             (<prefix>-object-alist-eval (cdr x) env))))
       ///
       (verify-guards <prefix>-object-eval-fn
         :hints(("Goal" :in-theory (disable fgl-bfr-object-p-when-fgl-object-p
                                            fgl-bfr-objectlist-p-when-fgl-objectlist-p
                                            fgl-bfr-object-alist-p-when-fgl-object-alist-p)
                 :expand ((fgl-bfr-object-alist-p x (logicman->bfrstate))))))
       
       (defret-mutual <prefix>-object-eval-of-fgl-bfr-object-fix
        (defret <prefix>-object-eval-of-fgl-bfr-object-fix
          (equal (<prefix>-object-eval (lgl-bfr-object-fix x) env)
                 val)
          :hints ('(:expand ((lgl-bfr-object-fix x))))
          :fn <prefix>-object-eval)
        (defret <prefix>-objectlist-eval-of-fgl-bfr-objectlist-fix
          (equal (<prefix>-objectlist-eval (lgl-bfr-objectlist-fix x) env)
                 vals)
          :hints ('(:expand ((lgl-bfr-objectlist-fix x))))
          :fn <prefix>-objectlist-eval)
        (defret <prefix>-object-alist-eval-of-fgl-bfr-object-alist-fix
          (equal (<prefix>-object-alist-eval (lgl-bfr-object-alist-fix x) env)
                 vals)
          :hints ('(:expand ((lgl-bfr-object-alist-fix x)
                             (fgl-object-alist-fix x))))
          :fn <prefix>-object-alist-eval))

       (defret-mutual <prefix>-object-eval-of-fgl-object-fix
         (defret <prefix>-object-eval-of-fgl-object-fix
           (equal (<prefix>-object-eval (fgl-object-fix x) env)
                  val)
           :hints ('(:expand ((fgl-object-fix x))
                               :in-theory (e/d (<prefix>-object-eval))))
           :fn <prefix>-object-eval)
         (defret <prefix>-objectlist-eval-of-fgl-object-fix
           (equal (<prefix>-objectlist-eval (fgl-objectlist-fix x) env)
                  vals)
           :hints ('(:expand ((fgl-objectlist-fix x)
                                        (:free (a b) (<prefix>-objectlist-eval (cons a b) env))
                                        (<prefix>-objectlist-eval nil env)
                                        (<prefix>-objectlist-eval x env))))
           :fn <prefix>-objectlist-eval)
         (defret <prefix>-object-alist-eval-of-fgl-object-fix
           (equal (<prefix>-object-alist-eval (fgl-object-alist-fix x) env)
                  vals)
           :hints ('(:expand ((fgl-object-alist-fix x)
                                        (:free (a b) (<prefix>-object-alist-eval (cons a b) env))
                                        (<prefix>-object-alist-eval nil env)
                                        (<prefix>-object-alist-eval x env))))
           :fn <prefix>-object-alist-eval))

       (fty::deffixcong fgl-object-equiv equal (<prefix>-object-eval x env) x)
       (fty::deffixcong fgl-objectlist-equiv equal (<prefix>-objectlist-eval x env) x)
       (fty::deffixcong fgl-object-alist-equiv equal (<prefix>-object-alist-eval x env) x)

       (defthm-<prefix>-object-eval-flag
         (defthm <prefix>-object-eval-of-logicman-extension
           (implies (and (bind-logicman-extension new old)
                         (lbfr-listp (fgl-object-bfrlist x) old))
                    (equal (<prefix>-object-eval x env new)
                           (<prefix>-object-eval x env old)))
           :hints ('(:expand ((:free (logicman) (<prefix>-object-eval x env logicman))
                               (fgl-object-bfrlist x))))
           :flag <prefix>-object-eval)
         (defthm <prefix>-objectlist-eval-of-logicman-extension
           (implies (and (bind-logicman-extension new old)
                         (lbfr-listp (fgl-objectlist-bfrlist x) old))
                    (equal (<prefix>-objectlist-eval x env new)
                           (<prefix>-objectlist-eval x env old)))
           :hints ('(:expand ((:free (logicman) (<prefix>-objectlist-eval x env logicman))
                              (fgl-objectlist-bfrlist x))))
            :flag <prefix>-objectlist-eval)
         (defthm <prefix>-object-alist-eval-of-logicman-extension
           (implies (and (bind-logicman-extension new old)
                         (lbfr-listp (fgl-object-alist-bfrlist x) old))
                    (equal (<prefix>-object-alist-eval x env new)
                           (<prefix>-object-alist-eval x env old)))
           :hints ('(:expand ((:free (logicman) (<prefix>-object-alist-eval x env logicman))
                              (fgl-object-alist-bfrlist x))))
            :flag <prefix>-object-alist-eval)
         :hints (("goal" :induct (<prefix>-object-eval-flag flag x env old))))

       (defthm <prefix>-object-eval-when-g-concrete
         (implies (fgl-object-case x :g-concrete)
                  (equal (<prefix>-object-eval x env)
                         (g-concrete->val x)))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-concrete
         (equal (<prefix>-object-eval (g-concrete val) env)
                val))

       (defthm <prefix>-object-eval-when-g-boolean
         (implies (fgl-object-case x :g-boolean)
                  (equal (<prefix>-object-eval x env)
                         (gobj-bfr-eval (g-boolean->bool x) env)))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-boolean
         (equal (<prefix>-object-eval (g-boolean bool) env)
                (gobj-bfr-eval bool env)))

       (defthm <prefix>-object-eval-when-g-integer
         (implies (fgl-object-case x :g-integer)
                  (equal (<prefix>-object-eval x env)
                         (bools->int (gobj-bfr-list-eval (g-integer->bits x) env))))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-integer
         (equal (<prefix>-object-eval (g-integer bits) env)
                (bools->int (gobj-bfr-list-eval bits env))))

       (defthm <prefix>-object-eval-when-g-ite
         (implies (fgl-object-case x :g-ite)
                  (equal (<prefix>-object-eval x env)
                         (if (<prefix>-object-eval (g-ite->test x) env)
                             (<prefix>-object-eval (g-ite->then x) env)
                           (<prefix>-object-eval (g-ite->else x) env))))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-ite
         (equal (<prefix>-object-eval (g-ite test then else) env)
                (if (<prefix>-object-eval test env)
                    (<prefix>-object-eval then env)
                  (<prefix>-object-eval else env))))

       (defthm <prefix>-object-eval-when-g-apply
         (implies (fgl-object-case x :g-apply)
                  (equal (<prefix>-object-eval x env)
                         (<prefix>-apply (g-apply->fn x)
                                                 (<prefix>-objectlist-eval (g-apply->args x) env))))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-apply
         (equal (<prefix>-object-eval (g-apply fn args) env)
                (<prefix>-apply (pseudo-fnsym-fix fn)
                              (<prefix>-objectlist-eval args env))))

       (defthm <prefix>-object-eval-when-g-var
         (implies (fgl-object-case x :g-var)
                  (equal (<prefix>-object-eval x env)
                         (gobj-var-lookup (g-var->name x) env)))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-var
         (equal (<prefix>-object-eval (g-var name) env)
                (gobj-var-lookup name env)))

       (defthm <prefix>-object-eval-when-g-cons
         (implies (fgl-object-case x :g-cons)
                  (equal (<prefix>-object-eval x env)
                         (cons (<prefix>-object-eval (g-cons->car x) env)
                               (<prefix>-object-eval (g-cons->cdr x) env))))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-cons
         (equal (<prefix>-object-eval (g-cons car cdr) env)
                (cons (<prefix>-object-eval car env)
                      (<prefix>-object-eval cdr env))))

       (defthm <prefix>-object-eval-when-g-map
         (implies (fgl-object-case x :g-map)
                  (equal (<prefix>-object-eval x env)
                         (<prefix>-object-alist-eval (g-map->alist x) env)))
         :hints (("goal" :expand ((<prefix>-object-eval x env)))))

       (defthm <prefix>-object-eval-of-g-map
         (equal (<prefix>-object-eval (g-map tag alist) env)
                (<prefix>-object-alist-eval alist env)))

       (defthm <prefix>-object-eval-of-mk-g-boolean
         (equal (<prefix>-object-eval (mk-g-boolean x) env)
                (gobj-bfr-eval x env))
         :hints(("Goal" :in-theory (enable mk-g-boolean booleanp))))

       (defthm <prefix>-object-eval-of-mk-g-integer
         (equal (<prefix>-object-eval (mk-g-integer x) env)
                (bools->int (gobj-bfr-list-eval x env)))
         :hints(("Goal" :in-theory (enable mk-g-integer
                                           gobj-bfr-list-eval-of-boolean-list))))

       (defthm <prefix>-objectlist-eval-of-cons
         (equal (<prefix>-objectlist-eval (cons x y) env)
                (cons (<prefix>-object-eval x env)
                      (<prefix>-objectlist-eval y env))))

       (defthm <prefix>-objectlist-eval-of-nil
         (equal (<prefix>-objectlist-eval nil env) nil))

       (defthm <prefix>-object-alist-eval-of-cons
         (equal (<prefix>-object-alist-eval (cons (cons var val) y) env)
                (cons (cons var (<prefix>-object-eval val env))
                      (<prefix>-object-alist-eval y env))))

       (defthm <prefix>-object-alist-eval-of-nil
         (equal (<prefix>-object-alist-eval nil env) nil))

       (fty::deffixequiv-mutual <prefix>-object-eval))

     (define <prefix>-object-bindings-eval ((x lgl-bfr-object-bindings-p)
                                (env fgl-env-p)
                                &optional (logicman 'logicman))
       :guard-hints (("goal" :in-theory (enable fgl-bfr-object-bindings-p)))
       :returns (val alistp)
       (if (atom x)
           nil
         (if (mbt (and (consp (car x))
                       (pseudo-var-p (caar x))))
             (cons (cons (caar x)
                         (<prefix>-object-eval (cdar x) env))
                   (<prefix>-object-bindings-eval (cdr x) env))
           (<prefix>-object-bindings-eval (cdr x) env)))
       ///
       (deffixequiv <prefix>-object-bindings-eval :args ((x fgl-object-bindings-p))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-fix))))
       
       (defthm <prefix>-object-bindings-eval-of-logicman-extension
         (implies (and (bind-logicman-extension new old)
                       (lbfr-listp (fgl-object-bindings-bfrlist x) old))
                  (equal (<prefix>-object-bindings-eval x env new)
                         (<prefix>-object-bindings-eval x env old)))
         :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist)))))

     (table fgl-evaluators '<prefix> '<fns>)
     (table fgl-last-evaluator :last '<prefix>)))


(defconst *fgl-ev-base-fns*
  ;; note: these are the ones actually used in the proof of correctness of the clause processors.
  ;; The rest below are used in primitives.

  ;; (bool concrete
  ;;        cons endint equal fgl-sat-check if
  ;;        iff implies int intcons intcons* not return-last
  ;;        synp syntax-bind-fn typespec-check)
  '(acl2-numberp
    binary-* binary-+
    unary-- unary-/ < char-code characterp
    code-char complex complex-rationalp
    coerce consp denominator imagpart
    integerp intern-in-package-of-symbol
    numerator rationalp realpart
    stringp symbol-name symbol-package-name
    symbolp
    binder syntax-interp-fn abort-rewrite unequiv assume narrow-equiv fgl-interp-obj
    fgl-time-fn
    

    equal not if iff int bool
    concrete return-last synp cons car cdr
    intcons intcons* endint intcar intcdr int-endp
    typespec-check implies fgl-sat-check))

(defun def-fgl-object-eval-fn (prefix fns union-previous wrld)
  (declare (xargs :mode :program))
  (let ((fns (set::mergesort
              (append (and union-previous
                           (append-alist-vals (table-alist 'fgl-evaluators wrld)))
                      fns
                      *fgl-ev-base-fns*))))
    (acl2::template-subst *fgl-object-eval-template*
                          :atom-alist `((<prefix> . ,prefix)
                                        (<fns> . ,fns))
                          :str-alist `(("<PREFIX>" . ,(symbol-name prefix)))
                          :pkg-sym prefix)))

(defmacro def-fgl-object-eval (prefix fns &key union-previous)
  `(make-event
    (def-fgl-object-eval-fn ',prefix ',fns ',union-previous (w state))))

(defxdoc fgl-object-eval
  :parents (fgl-object)
  :short "Evaluator for FGL symbolic objects."
  :long "

<p>@('Fgl-object-eval') gives the semantics for FGL symbolic objects, in the
same way as a term evaluator gives the semantics for terms.  In fact,
@('fgl-object-eval') uses a term evaluator @('fgl-ev') to interpret function
calls.</p>

<p>The inputs to @('fgl-object-eval') are the object to be evaluated; an
@('env') containing two parts: a Boolean formula environment binding Boolean
variables to values, and a term-level environment binding term variables to
objects; and the logic manager or @('logicman'), a stobj containing (mainly)
the Boolean function mode and AIGNET relative to which Boolean formulas are
evaluated using @(see bfr-eval).</p>

<ul>
<li>@(csee g-concrete) objects return the quoted value.</li>

<li>@(csee g-boolean) objects return the evaluation using @(see bfr-eval) of
the Boolean formula under the Boolean environment.</li>

<li>@(csee g-integer) objects return the integer consisting of the bits
produced by evaluating the bits using @(see bfr-eval).</li>

<li>@(csee g-ite) objects return the if-then-else of the recursive
@('fgl-object-eval') of the three arguments.</li>

<li>@(csee g-apply) objects return the @('fgl-ev') evaluation of the function
applied to the recursive @('fgl-object-eval') evaluation of the arguments.</li>

<li>@(csee g-var) objects return the binding of the variable in the term-level
environment.</li>

<li>@(csee g-map) objects return the alist, with the bound values recursively
evaluated using @('fgl-object-eval').</li>

<li>@(csee g-cons) objects return the cons of the recursive
@('fgl-object-eval') evaluations of the car and cdr.</li>

</ul>

")


(def-fgl-object-eval fgl nil)









(local (include-book "aabf"))
(local
 (defthm aabf-trivial-thm
   (b* ((orig-man man)
        (notx (aabf-not x man))
        ((mv yxorz man) (aabf-xor y z man))
        ((mv res man) (aabf-and notx yxorz man)))
     (implies (and (aabf-p x orig-man)
                   (aabf-p y orig-man)
                   (aabf-p z orig-man))
              (equal (aabf-eval res env man)
                     (and (not (aabf-eval x env orig-man))
                          (xor (aabf-eval y env orig-man)
                               (aabf-eval z env orig-man))))))))


(local
 (defthm logicman-aabf-functional-instance-ok
   t
   :rule-classes nil
   :hints (("goal" :use ((:functional-instance aabf-trivial-thm
                          (aabf-eval bfr-eval-fn)
                          (aabf-p (lambda (x man) (bfr-p x (logicman->bfrstate man))))
                          (aabf-pred (lambda (x man) (bfr-p x (logicman->bfrstate man))))
                          (aabf-true (lambda () t))
                          (aabf-false (lambda () nil))
                          (aabf-not bfr-not-fn)
                          (aabf-and bfr-and-fn)
                          (aabf-or bfr-or-fn)
                          (aabf-xor bfr-xor-fn)
                          (aabf-iff bfr-iff-fn)
                          (aabf-ite bfr-ite-fn)
                          (aabf-syntactically-equal equal)
                          (aabf-extension-p logicman-extension-p)))))))

(local (defthm bfr-depends-on-of-nil
         (not (bfr-depends-on var nil logicman))
         :hints(("Goal" :in-theory (enable bfr-depends-on)))))

(local (defthm bfr-depends-on-of-t
         (not (bfr-depends-on var t logicman))
         :hints(("Goal" :in-theory (enable bfr-depends-on)))))

(local
 (defthm logicman-aabf-dependency-functional-instance-ok
   t
   :rule-classes nil
   :hints (("goal" :use ((:functional-instance aabf-trivial-thm
                          (aabf-eval bfr-eval-fn)
                          (aabf-p (lambda (x man) (bfr-p x (logicman->bfrstate man))))
                          (aabf-pred (lambda (x man) (not (bfr-depends-on var x man))))
                          (aabf-true (lambda () t))
                          (aabf-false (lambda () nil))
                          (aabf-not bfr-not-fn)
                          (aabf-and bfr-and-fn)
                          (aabf-or bfr-or-fn)
                          (aabf-xor bfr-xor-fn)
                          (aabf-iff bfr-iff-fn)
                          (aabf-ite bfr-ite-fn)
                          (aabf-syntactically-equal equal)
                          (aabf-extension-p logicman-extension-p)))))))



(define logicman-equiv (x y)
  :non-executable t
  :verify-guards nil
  (and (equal (logicman->aignet x) (logicman->aignet y))
       (equal (logicman->mode x) (logicman->mode y)))
  ///
  (defequiv logicman-equiv)
  (defcong logicman-equiv equal (logicman->bfrstate logicman) 1
    :hints(("Goal" :in-theory (enable logicman->bfrstate))))

  (defcong logicman-equiv equal (logicman->mode logicman) 1)
  (defcong logicman-equiv equal (logicman->aignet logicman) 1)


  (local (in-theory (disable logicman-equiv)))

  (defcong logicman-equiv equal (bfr-eval x env logicman) 3
    :hints(("Goal" :in-theory (enable bfr-eval))))

  (defcong logicman-equiv equal (bfr-list-eval x env logicman) 3
    :hints(("Goal" :in-theory (enable bfr-list-eval))))

  (defcong logicman-equiv equal (gobj-bfr-eval x env logicman) 3
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)
                                   (gobj-bfr-eval-reduce-by-bfr-eval))
            :do-not '(preprocess))))

  (defcong logicman-equiv equal (gobj-bfr-list-eval x env logicman) 3
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defret-mutual fgl-object-eval-logicman-equiv-congruence
    (defret fgl-object-eval-logicman-equiv-congruence
      (implies (logicman-equiv logicman logicman2)
               (equal (fgl-object-eval x env logicman)
                      (fgl-object-eval x env logicman2)))
      :hints ('(:expand ((:free (logicman) (fgl-object-eval x env logicman)))))
      :rule-classes :congruence
      :fn fgl-object-eval)

    (defret fgl-objectlist-eval-logicman-equiv-congruence
      (implies (logicman-equiv logicman logicman2)
               (equal (fgl-objectlist-eval x env logicman)
                      (fgl-objectlist-eval x env logicman2)))
      :hints ('(:expand ((:free (logicman) (fgl-objectlist-eval x env logicman)))))
      :rule-classes :congruence
      :fn fgl-objectlist-eval)

    (defret fgl-object-alist-eval-logicman-equiv-congruence
      (implies (logicman-equiv logicman logicman2)
               (equal (fgl-object-alist-eval x env logicman)
                      (fgl-object-alist-eval x env logicman2)))
      :hints ('(:expand ((:free (logicman) (fgl-object-alist-eval x env logicman)))))
      :rule-classes :congruence
      :fn fgl-object-alist-eval)

    :mutual-recursion fgl-object-eval)

  (defcong logicman-equiv equal (fgl-object-bindings-eval x env logicman) 3
    :hints(("Goal" :in-theory (enable fgl-object-bindings-eval))))

  (defcong logicman-equiv equal (bfr-nvars logicman) 1
    :hints(("Goal" :in-theory (enable bfr-nvars logicman-equiv)))))

(defsection logicman-ipasir-sat-lits-invar
  (defun-sk logicman-ipasir-sat-lits-invar (logicman)
    (forall n
            (implies (< (nfix n) (logicman->ipasir-length logicman))
                     (b* ((ipasir (logicman->ipasiri n logicman))
                          (sat-lits (logicman->sat-litsi n logicman))
                          (aignet (logicman->aignet logicman)))
                       (implies (not (equal (ipasir::ipasir$a->status ipasir) :undef))
                                (and (consp (ipasir::ipasir$a->history ipasir))
                                     (equal (ipasir::ipasir$a->new-clause ipasir) nil)
                                     (aignet::sat-lits-wfp sat-lits aignet)
                                     (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                                     (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                                     (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits))))))
    :rewrite :direct)

  (in-theory (disable logicman-ipasir-sat-lits-invar))

  (defthm logicman-ipasir-sat-lits-invar-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-ipasir-sat-lits-invar old)
                  (equal (logicman-get :ipasir new)
                         (logicman-get :ipasir old))
                  (equal (logicman-get :sat-lits new)
                         (logicman-get :sat-lits old)))
             (logicman-ipasir-sat-lits-invar new))
    :hints (("goal" :expand ((logicman-ipasir-sat-lits-invar new))
             :in-theory (enable logicman-extension-p))))

  (defthm logicman-ipasir-sat-lits-invar-of-create-logicman
    ;; BOZO figure out how to reason about create-logicman and other stobj creators
    (logicman-ipasir-sat-lits-invar '(NIL (NIL) NIL NIL 0 NIL 0))
    :hints(("Goal" :in-theory (enable logicman-ipasir-sat-lits-invar))))

  ;; (local (defthm logicman->ipasiri-of-greater-than-length
  ;;          (implies (<= (logicman->ipasir-length logicman) (nfix n))
  ;;                   (equal (logicman->ipasiri n logicman) nil))
  ;;          :hints(("Goal" :in-theory (enable logicman->ipasiri
  ;;                                            logicman->ipasir-length)))))

  (defthm logicman-ipasir-sat-lits-invar-implies-aignet
    (implies (and (logicman-ipasir-sat-lits-invar logicman)
                  (equal aignet (logicman->aignet logicman))
                  (< (nfix n) (logicman->ipasir-length logicman)))
             (b* ((ipasir (logicman->ipasiri n logicman))
                  (sat-lits (logicman->sat-litsi n logicman)))
               (implies (not (equal (ipasir::ipasir$a->status ipasir) :undef))
                        (and (aignet::sat-lits-wfp sat-lits aignet)
                             (implies (equal formula (ipasir::ipasir$a->formula ipasir))
                                      (aignet::cnf-for-aignet aignet formula sat-lits)))))))
             

  (defthm logicman-ipasir-sat-lits-invar-of-update-1
    (implies (and (logicman-ipasir-sat-lits-invar logicman)
                  (< (nfix n) (logicman->ipasir-length logicman))
                  (or (equal (ipasir::ipasir$a->status ipasir) :undef)
                      (b* ((aignet (logicman->aignet logicman)))
                        (and (consp (ipasir::ipasir$a->history ipasir))
                             (equal (ipasir::ipasir$a->new-clause ipasir) nil)
                             (aignet::sat-lits-wfp sat-lits aignet)
                             (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                             (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                             (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))
             (logicman-ipasir-sat-lits-invar
              (update-logicman->ipasiri
               n ipasir
               (update-logicman->sat-litsi
                n sat-lits logicman))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split
                                        logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                     :cases ((< (nfix (logicman-ipasir-sat-lits-invar-witness . ,(cdr lit)))
                                (logicman->ipasir-length logicman))))))))

  (defthm logicman-ipasir-sat-lits-invar-of-update-2
    (implies (and (logicman-ipasir-sat-lits-invar logicman)
                  (< (nfix n) (logicman->ipasir-length logicman))
                  (or (equal (ipasir::ipasir$a->status ipasir) :undef)
                      (b* ((aignet (logicman->aignet logicman)))
                        (and (consp (ipasir::ipasir$a->history ipasir))
                             (equal (ipasir::ipasir$a->new-clause ipasir) nil)
                             (aignet::sat-lits-wfp sat-lits aignet)
                             (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                             (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                             (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))
             (logicman-ipasir-sat-lits-invar
               (update-logicman->sat-litsi
                n sat-lits
                (update-logicman->ipasiri
                 n ipasir
                 logicman))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split
                                        logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                     :cases ((< (nfix (logicman-ipasir-sat-lits-invar-witness . ,(cdr lit)))
                                (logicman->ipasir-length logicman))))))))


  (local (in-theory (enable logicman->ipasiri-of-resize
                            logicman->sat-litsi-of-resize)))
  
  (defthm logicman-ipasir-sat-lits-invar-of-resize-1
    (implies (and (logicman-ipasir-sat-lits-invar logicman)
                  (equal (logicman->ipasir-length logicman)
                         (logicman->sat-lits-length logicman)))
             (logicman-ipasir-sat-lits-invar
              (resize-logicman->ipasir
               size
               (resize-logicman->sat-lits
                size logicman))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split
                                        logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                     :cases ((< (nfix (logicman-ipasir-sat-lits-invar-witness . ,(cdr lit)))
                                (logicman->ipasir-length logicman))))))))

  (defthm logicman-ipasir-sat-lits-invar-of-resize-2
    (implies (and (logicman-ipasir-sat-lits-invar logicman)
                  (equal (logicman->ipasir-length logicman)
                         (logicman->sat-lits-length logicman)))
             (logicman-ipasir-sat-lits-invar
              (resize-logicman->sat-lits
               size
               (resize-logicman->ipasir
                size
                logicman))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split
                                        logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                     :cases ((< (nfix (logicman-ipasir-sat-lits-invar-witness . ,(cdr lit)))
                                (logicman->ipasir-length logicman)))))))))
  



(define logicman-invar (logicman)
  (non-exec
   (b* (;; (mode (logicman->mode logicman))
        (refcounts-index (logicman->refcounts-index logicman)))
     (stobj-let ((aignet (logicman->aignet logicman))
                 (u32arr (logicman->aignet-refcounts logicman)))
                (ok)
                (and (<= (lnfix refcounts-index) (aignet::u32-length u32arr))
                     (eql (aignet::num-regs aignet) 0))
                (and ok
                     (equal (logicman->sat-lits-length logicman) (logicman->ipasir-length logicman))
                     (ec-call (logicman-ipasir-sat-lits-invar logicman))))))
  ///
  (defthm logicman-invar-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-invar old)
                  (equal (logicman-get :ipasir new)
                         (logicman-get :ipasir old))
                  (equal (logicman-get :sat-lits new)
                         (logicman-get :sat-lits old))
                  (equal (logicman->refcounts-index new)
                         (logicman->refcounts-index old))
                  (equal (logicman->aignet-refcounts new)
                         (logicman->aignet-refcounts old)))
             (logicman-invar new))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable logicman-extension-p)))))

  (defthm logicman-invar-implies
    (implies (logicman-invar logicman)
             (b* ((refcounts-index (logicman->refcounts-index logicman))
                  (aignet (logicman->aignet logicman))
                  (u32arr (logicman->aignet-refcounts logicman)))
               (and (<= refcounts-index (len u32arr))
                    (equal (aignet::stype-count :reg aignet) 0)
                    (equal (logicman->sat-lits-length logicman)
                           (logicman->ipasir-length logicman))
                    (logicman-ipasir-sat-lits-invar logicman)
                    (implies (< (nfix n) (logicman->ipasir-length logicman))
                             (b* ((ipasir (logicman->ipasiri n logicman))
                                  (sat-lits (logicman->sat-litsi n logicman)))
                               (implies (not (equal (ipasir::ipasir$a->status ipasir) :undef))
                                        (and (ipasir::ipasir-some-history ipasir)
                                             (ipasir::ipasir-empty-new-clause ipasir)
                                             (aignet::sat-lits-wfp sat-lits aignet)
                                             (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                                             (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                                             (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))))))

  (defthm logicman-invar-of-update-ipasir-1
    (implies (and (logicman-invar logicman)
                  (< (nfix n) (logicman->ipasir-length logicman))
                  (or (equal (ipasir::ipasir$a->status ipasir) :undef)
                      (b* ((aignet (logicman->aignet logicman)))
                        (and (consp (ipasir::ipasir$a->history ipasir))
                             (equal (ipasir::ipasir$a->new-clause ipasir) nil)
                             (aignet::sat-lits-wfp sat-lits aignet)
                             (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                             (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                             (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))
             (logicman-invar
              (update-logicman->ipasiri
               n ipasir
               (update-logicman->sat-litsi
                n sat-lits logicman))))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split
                                        logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                     :cases ((< (nfix (logicman-invar-witness . ,(cdr lit)))
                                (logicman->ipasir-length logicman))))))))

  (defthm logicman-invar-of-update-ipasir-2
    (implies (and (logicman-invar logicman)
                  (< (nfix n) (logicman->ipasir-length logicman))
                  (or (equal (ipasir::ipasir$a->status ipasir) :undef)
                      (b* ((aignet (logicman->aignet logicman)))
                        (and (consp (ipasir::ipasir$a->history ipasir))
                             (equal (ipasir::ipasir$a->new-clause ipasir) nil)
                             (aignet::sat-lits-wfp sat-lits aignet)
                             (aignet::sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                             (aignet::sat-lit-listp (ipasir::ipasir$a->assumption ipasir) sat-lits)
                             (aignet::cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))
             (logicman-invar
               (update-logicman->sat-litsi
                n sat-lits
                (update-logicman->ipasiri
                 n ipasir
                 logicman)))))

  

  (defthm logicman-invar-of-resize-ipasir-1
    (implies (logicman-invar logicman)
             (logicman-invar
              (resize-logicman->ipasir
               size
               (resize-logicman->sat-lits
                size logicman)))))

  (defthm logicman-invar-of-resize-ipasir-2
    (implies (logicman-invar logicman)
             (logicman-invar
              (resize-logicman->sat-lits
               size
               (resize-logicman->ipasir
                size
                logicman))))))



(define logicman-update-refcounts (logicman)
  :returns (new-logicman)
  (b* ((refcounts-index (lnfix (logicman->refcounts-index logicman))))
    (stobj-let ((aignet (logicman->aignet logicman))
                (u32arr (logicman->aignet-refcounts logicman)))
               (u32arr num-fanins)
               (b* ((u32arr (if (< (u32-length u32arr) (aignet::num-fanins aignet))
                                (resize-u32 (* 2 (aignet::num-fanins aignet)) u32arr)
                              u32arr))
                    (u32arr (aignet::aignet-count-gate-refs-tailrec
                             (min refcounts-index (aignet::num-fanins aignet)) u32arr aignet)))
                 (mv u32arr (aignet::num-fanins aignet)))
               (update-logicman->refcounts-index num-fanins logicman)))
  ///
  (local (defthm len-of-aignet-count-gate-refs-tailrec
           (<= (len u32arr)
               (len (aignet::aignet-count-gate-refs-tailrec n u32arr logicman)))
           :hints(("Goal" :in-theory (enable aignet::aignet-count-gate-refs-tailrec)))
           :rule-classes :linear))

  (defret <fn>-updater-independence
    (implies (and (not (equal (logicman-field-fix key) :aignet-refcounts))
                  (not (equal (logicman-field-fix key) :refcounts-index)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret refcounts-length-of-<fn>
    (< (aignet::fanin-count (logicman->aignet logicman))
       (len (logicman->aignet-refcounts new-logicman)))
    :rule-classes :linear)

  (defret logicman->refcounts-index-of-<fn>
    (equal (logicman->refcounts-index new-logicman)
           (aignet::num-fanins (logicman->aignet logicman))))

  (defret logicman-equiv-of-<fn>
    (logicman-equiv new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (defret logicman-invar-of-<fn>
    (implies (logicman-invar logicman)
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable logicman-invar)))))


(defsection bfr-boundedp
  ;; Recognizes a BFR that uses only variables less than N.
  (defun-sk bfr-boundedp (x n logicman)
    (forall (var env)
            (implies (and (natp var)
                          (<= (nfix n) var))
                     (equal (bfr-eval x (bfr-set-var var t env))
                            (bfr-eval x env))))
    :rewrite :direct)

  (local
   (encapsulate nil
     (local (defun ind (x n env)
              (if (zp n)
                  (list x env)
                (if (car env)
                    (ind (car x) (1- n) (cdr env))
                  (ind (cdr x) (1- n) (cdr env))))))
     (local
      (defthm eval-bdd-of-update-past-max-depth
        (implies (<= (max-depth x) (nfix n))
                 (equal (acl2::eval-bdd x (update-nth n val env))
                        (acl2::eval-bdd x env)))
        :hints (("goal" :induct (ind x n env)
                 :expand ((update-nth n val env)
                          (max-depth x)
                          (:free (env) (acl2::eval-bdd x env)))))))

     (defthm eval-bdd-of-ubdd-fix-update-past
       (implies (<= (nfix m) (nfix n))
                (equal (acl2::eval-bdd (ubdd-fix x m) (update-nth n val env))
                       (acl2::eval-bdd (ubdd-fix x m) env)))
       :hints(("Goal" :in-theory (enable ubdd-fix))))))

  (local
   (encapsulate nil
     (local
      (defthm aig-eval-of-update-past-max-vars
        (implies (and (aig-p x m)
                      (<= (nfix m) n))
                 (equal (acl2::aig-eval x (cons (cons n val) env))
                        (acl2::aig-eval x env)))
        :hints (("goal" :induct (acl2::aig-eval x env)
                 :expand ((aig-p x m)
                          (aig-p n m)
                          (:free (env) (acl2::aig-eval x env)))))))

     (defthm aig-eval-of-aig-fix-update-past
       (implies (<= (nfix m) n)
                (equal (acl2::aig-eval (aig-fix x m) (cons (cons n val) env))
                       (acl2::aig-eval (aig-fix x m) env)))
       :hints (("goal" :use ((:instance aig-eval-of-update-past-max-vars
                              (x (aig-fix x m))))
                :in-theory (disable aig-eval-of-update-past-max-vars))))))


  (local
   (defthm alist-to-bitarr-aux-of-update-past
     (implies (<= (len bitarr) n)
              (equal (alist-to-bitarr-aux k (cons (cons n val) env) bitarr)
                     (alist-to-bitarr-aux k env bitarr)))
     :hints(("Goal" :induct (alist-to-bitarr-aux k env bitarr)
             :in-theory (enable (:i alist-to-bitarr-aux))
             :expand ((:free (env) (alist-to-bitarr-aux k env bitarr)))))))
  (local
   (defthm alist-to-bitarr-of-update-past
     (implies (<= (nfix m) n)
              (equal (alist-to-bitarr m (cons (cons n val) env) bitarr)
                     (alist-to-bitarr m env bitarr)))
     :hints(("Goal" :in-theory (enable alist-to-bitarr)))))

  (defthm bfr-boundedp-of-current-num-vars
    (bfr-boundedp x (bfr-nvars logicman) logicman)
    :hints(("Goal" :in-theory (enable bfr-boundedp
                                      bfr-set-var
                                      bfr-eval
                                      bfr-nvars
                                      bfr-fix
                                      bfr->aignet-lit
                                      aignet-lit->bfr
                                      bounded-lit-fix))))


  (in-theory (disable bfr-boundedp bfr-boundedp-necc))

  (fty::deffixcong acl2::nat-equiv equal (bfr-boundedp x n logicman) n
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'bfr-boundedp clause))
                        (other (if (eq (third lit) 'n) '(nfix n) 'n)))
                   `(:expand (,lit)
                     :use ((:instance bfr-boundedp-necc
                            (var (mv-nth 0 (bfr-boundedp-witness . ,(cdr lit))))
                            (env (mv-nth 1 (bfr-boundedp-witness . ,(cdr lit))))
                            (n ,other))))))))

  (defthm bfr-boundedp-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-p x old)
                  (bfr-boundedp x n old))
             (bfr-boundedp x n new))
    :hints (("goal" :expand ((bfr-boundedp x n new))
             :use ((:instance bfr-boundedp-necc
                    (logicman old)
                    (var (mv-nth 0 (bfr-boundedp-witness x n new)))
                    (env (mv-nth 1 (bfr-boundedp-witness x n new)))))))))


(encapsulate nil
           
  (local
   (encapsulate nil
     (local (defun ind (x n env)
              (if (zp n)
                  (list x env)
                (if (car env)
                    (ind (car x) (1- n) (cdr env))
                  (ind (cdr x) (1- n) (cdr env))))))

     (defthm eval-bdd-of-update-same
       (implies (iff (nth n env) val)
                (equal (acl2::eval-bdd x (update-nth n val env))
                       (acl2::eval-bdd x env)))
       :hints (("goal" :induct (ind x n env)
                :expand ((:free (val) (update-nth n val env))
                         (:free (val) (update-nth 0 val env))
                         (nth n env)
                         (nth 0 env)
                         (:free (env) (acl2::eval-bdd x env))))))))

  (local (defthm alist-to-bitarr-aux-of-cons-same
           (implies (iff (cdr (hons-assoc-equal var env)) val)
                    (equal (alist-to-bitarr-aux n (cons (cons var val) env) bitarr)
                           (alist-to-bitarr-aux n env bitarr)))
           :hints(("Goal" :in-theory (enable (:i alist-to-bitarr-aux))
                   :induct (alist-to-bitarr-aux n env bitarr)
                   :expand ((:free (env) (alist-to-bitarr-aux n env bitarr)))))))

  (local (defthm alist-to-bitarr-of-cons-same
           (implies (iff (cdr (hons-assoc-equal var env)) val)
                    (equal (alist-to-bitarr max (cons (cons var val) env) bitarr)
                           (alist-to-bitarr max env bitarr)))
           :hints(("Goal" :in-theory (enable alist-to-bitarr)))))

  (local (defthm aig-eval-of-cons-same
           (implies (iff (acl2::aig-env-lookup var env) val)
                    (equal (acl2::aig-eval x (cons (cons var val) env))
                           (acl2::aig-eval x env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval)))))

  (local (defthm bfr-eval-of-bfr-set-var-same
           (implies (iff (bfr-lookup var env) val)
                    (equal (bfr-eval x (bfr-set-var var val env))
                           (bfr-eval x env)))
           :hints(("Goal" :in-theory (enable bfr-eval bfr-lookup bfr-set-var)))))

  (local (defthm update-nth-redundant
           (equal (update-nth n val (update-nth n val2 x))
                  (update-nth n val x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (local (defthm alist-to-bitarr-aux-of-cons-redundant
           (equal (alist-to-bitarr-aux n (list* (cons var val)
                                                (cons var val2)
                                                env)
                                       bitarr)
                  (alist-to-bitarr-aux n (cons (cons var val) env) bitarr))
           :hints(("Goal" :in-theory (enable (:i alist-to-bitarr-aux))
                   :induct (alist-to-bitarr-aux n (cons (cons var val) env) bitarr)
                   :expand ((:free (env) (alist-to-bitarr-aux n (cons (cons var val) env) bitarr)))))))

  (local (defthm alist-to-bitarr-of-cons-redundant
           (equal (alist-to-bitarr max (list* (cons var val)
                                              (cons var val2)
                                              env)
                                   bitarr)
                  (alist-to-bitarr max (cons (cons var val) env) bitarr))
           :hints(("Goal" :in-theory (enable alist-to-bitarr)))))

  (local (defthm aig-eval-of-cons-redundant
           (equal (acl2::aig-eval x (cons (cons var val) (cons (cons var val2) env)))
                  (acl2::aig-eval x (cons (cons var val) env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval acl2::aig-env-lookup)))))

  (local (defthm bfr-eval-of-bfr-set-var-redundant
           (equal (bfr-eval x (bfr-set-var var val (bfr-set-var var val2 env)))
                  (bfr-eval x (bfr-set-var var val env)))
           :hints(("Goal" :in-theory (enable bfr-eval bfr-lookup bfr-set-var)))))

  (defthm bfr-eval-of-bfr-set-var-when-bfr-boundedp
    (implies (and (bfr-boundedp x n logicman)
                  (<= (nfix n) (nfix var)))
             (equal (bfr-eval x (bfr-set-var var val env))
                    (bfr-eval x env)))
    :hints (("goal" :use ((:instance bfr-boundedp-necc (var (nfix var))
                           (env (bfr-set-var var val env)))
                          (:instance bfr-boundedp-necc (var (nfix var))
                           (env (bfr-set-var var nil env))))
             :cases ((bfr-lookup var env))))))
                 

(define bfrlist-boundedp (x (n natp) logicman)
  :verify-guards nil
  (if (atom x)
      t
    (and (bfr-boundedp (car x) n logicman)
         (bfrlist-boundedp (cdr x) n logicman)))
  ///
  (defthm bfrlist-boundedp-of-current-num-vars
    (bfrlist-boundedp x (bfr-nvars logicman) logicman))

  (defthm bfrlist-boundedp-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp x old)
                  (bfrlist-boundedp x n old))
             (bfrlist-boundedp x n new))
    :hints(("Goal" :in-theory (enable bfr-listp$)
            :induct (bfrlist-boundedp x n new))))

  (defthm bfrlist-boundedp-of-append
    (iff (bfrlist-boundedp (append x y) n logicman)
         (and (bfrlist-boundedp x n logicman)
              (bfrlist-boundedp y n logicman))))

  (defthm bfrlist-boundedp-of-cons
    (iff (bfrlist-boundedp (cons x y) n logicman)
         (and (bfr-boundedp x n logicman)
              (bfrlist-boundedp y n logicman))))

  (defthm bfrlist-boundedp-of-nil
    (bfrlist-boundedp nil n logicman)))
