; GL - A Symbolic Simulation Framework for ACL2
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
(include-book "bvar-db")
(include-book "gl-object")
(include-book "pathcond-stobj")
(include-book "centaur/ubdds/deps" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(local (include-book "theory"))
(local (include-book "tools/trivial-ancestors-check" :dir :system))

(fty::defalist nat-nat-alist :key-type natp :val-type natp :true-listp t)

(defstobj interp-profiler
  (prof-enabledp :type (satisfies booleanp))
  (prof-indextable)
  (prof-totalcount :type (integer 0 *) :initially 0)
  (prof-nextindex :type (integer 0 *) :initially 0)
  (prof-array :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (prof-stack :type (satisfies nat-nat-alist-p)))


(defconst *logicman-fields*
  '((aignet :type aignet::aignet)
    (aignet-refcounts :type aignet::aignet-refcounts)
    (strash :type aignet::strash)
    (ipasir :type ipasir::ipasir)
    (sat-lits :type aignet::sat-lits)
    (pathcond :type pathcond)
    (bvar-db :type bvar-db)
    (prof :type interp-profiler)
    (mode :type (satisfies bfr-mode-p))))


              

(local (defun logicman-fields-to-templates (fields)
         (declare (xargs :mode :program))
         (if (atom fields)
             nil
           (cons (acl2::make-tmplsubst :atoms `((<field> . ,(caar fields))
                                                (:<field> . ,(intern$ (symbol-name (caar fields)) "KEYWORD"))
                                                (<type> . ,(third (car fields))))
                                       :strs `(("<FIELD>" . ,(symbol-name (caar fields))))
                                       :pkg-sym 'fgl::foo)
                 (logicman-fields-to-templates (cdr fields))))))

(make-event
 `(defconst *logicman-field-templates*
    ',(logicman-fields-to-templates *logicman-fields*)))
  

(make-event
 (acl2::template-subst
  '(defstobj logicman
     (:@proj fields (logicman-><field> :type <type>)))
  :subsubsts `((fields . ,*logicman-field-templates*))))

(defthm logicmanp-implies-aignetp
  (implies (logicmanp logicman)
           (aignet::node-listp (logicman->aignet logicman))))

(defthm logicmanp-implies-bfr-mode-p
  (implies (logicmanp logicman)
           (bfr-mode-p (logicman->mode logicman))))

(defthm logicmanp-implies-pathcondp
  (implies (logicmanp logicman)
           (pathcondp (logicman->pathcond logicman))))

(in-theory (disable logicmanp))

(make-event
 (acl2::template-subst
  '(std::defenum logicman-field-p ((:@proj fields :<field>)))
  :subsubsts `((fields . ,*logicman-field-templates*))))

(make-event
 (acl2::template-subst
  '(define logicman-get ((key logicman-field-p) &optional (logicman 'logicman))
     ;; bozo define doesn't correctly support :non-executable t with macro args
     (declare (xargs :non-executable t))
     :no-function t
     :prepwork ((local (in-theory (enable logicman-field-fix))))
     (prog2$ (acl2::throw-nonexec-error 'logicman-get-fn (list key logicman))
             (case key
               (:@proj fields (:<field> (logicman-><field> logicman)))
               (t (logicman->mode logicman)))))
  :subsubsts `((fields . ,(butlast *logicman-field-templates* 1)))))

(make-event
 (acl2::template-subst
  '(defsection logicman-field-basics
     (local (in-theory (enable logicman-get
                               logicman-field-fix)))
     (:@append fields
      (def-updater-independence-thm logicman-><field>-updater-independence
        (implies (equal (logicman-get :<field> new)
                        (logicman-get :<field> old))
                 (equal (logicman-><field> new)
                        (logicman-><field> old))))

      (defthm update-logicman-><field>-preserves-others
        (implies (not (equal (logicman-field-fix i) :<field>))
                 (equal (logicman-get i (update-logicman-><field> x logicman))
                        (logicman-get i logicman))))

      (defthm update-logicman-><field>-self-preserves-logicman
        (implies (logicmanp logicman)
                 (equal (update-logicman-><field>
                         (logicman-><field> logicman)
                         logicman)
                        logicman))
        :hints(("Goal" :in-theory (enable logicmanp
                                          aignet::redundant-update-nth))))

      (defthm logicman-><field>-of-update-logicman-><field>
        (equal (logicman-><field> (update-logicman-><field> x logicman))
               x)))

     (:@proj fields
      (in-theory (disable logicman-><field>
                          update-logicman-><field>)))

     (local (in-theory (disable logicman-get
                                logicman-field-fix)))

     ;; test:
     (local 
      (defthm logicman-test-updater-independence
        (b* ((logicman1 (update-logicman->strash strash logicman))
             (logicman2 (update-logicman->ipasir ipasir logicman)))
          (and (equal (logicman->mode logicman2) (logicman->mode logicman))
               (equal (logicman->mode logicman1) (logicman->mode logicman)))))))
  
  :subsubsts `((fields . ,*logicman-field-templates*))))


(defmacro bfr-mode (&optional (logicman 'logicman))
  `(logicman->mode ,logicman))

(defsection bfr-case
  :short "Choose behavior based on the current @(see bfr) mode."
  :long "<p>Usage:</p>

@({
     (brf-case :aig aigcode
               :bdd bddcode)
})

<p>expands to @('aigcode') if we are currently in AIG mode, or @('bddcode') if
we are currently in BDD mode.  This is often used to implement basic wrappers
like @(see bfr-and).</p>

@(def bfr-case)"

  (defmacro bfr-case (&key aig bdd aignet)
    `(case (bfr-mode)
       ((nil) ,bdd)
       (:aignet ,aignet)
       (t ,aig))))

;; Include pathcond? parametrization hyp?

(define logicman-extension-p (new old)
  :non-executable t
  :verify-guards nil
  (and (aignet::aignet-extension-p (logicman->aignet new)
                                   (logicman->aignet old))
       (bvar-db-extension-p (logicman->bvar-db new)
                            (logicman->bvar-db old))
       (equal (logicman->mode new) (logicman->mode old)))
  ///
  (def-updater-independence-thm logicman-extension-p-updater-independence-1
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :bvar-db new)
                         (logicman-get :bvar-db old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old))
                  (logicman-extension-p old other))
             (logicman-extension-p new other)))

  (def-updater-independence-thm logicman-extension-p-updater-independence-2
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :bvar-db new)
                         (logicman-get :bvar-db old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old))
                  (logicman-extension-p other old))
             (logicman-extension-p other new)))

  (def-updater-independence-thm logicman-extension-p-updater-independence-2
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :bvar-db new)
                         (logicman-get :bvar-db old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old))
                  (logicman-extension-p other old))
             (logicman-extension-p other new)))

  (in-theory (disable logicman-extension-p-updater-independence-1
                      logicman-extension-p-updater-independence-2))

  (defmacro bind-logicman-extension (new old-var)
    `(and (bind-free (acl2::prev-stobj-binding ,new ',old-var mfc state))
          (logicman-extension-p ,new ,old-var)))

  (defthm logicman-extension-self
    (logicman-extension-p x x))

  (defthm aignet-extension-when-logicman-extension
    (implies (logicman-extension-p new old)
             (aignet::aignet-extension-p (logicman->aignet new)
                                         (logicman->aignet old))))

  (defthm logicman-extension-p-transitive
    (implies (and (bind-logicman-extension x y)
                  (logicman-extension-p y z))
             (logicman-extension-p x z)))

  (defthm logicman-extension-when-same
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :bvar-db new)
                         (logicman-get :bvar-db old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old)))
             (logicman-extension-p new old)))

  (defthm logicman->mode-of-extension
    (implies (bind-logicman-extension x y)
             (equal (logicman->mode x)
                    (logicman->mode y)))))








(define bfr-p (x &optional (logicman 'logicman))
  (bfr-case
    :aig (aig-p x)
    :bdd (acl2::ubddp x)
    :aignet
    (or (booleanp x)
        (and (satlink::litp x)
             (not (eql x 0))
             (not (eql x 1))
             (stobj-let
              ((aignet (logicman->aignet logicman)))
              (ans)
              (aignet::fanin-litp x aignet)
              ans))))
  ///
  (defthm bfr-p-of-constants
    (and (bfr-p t)
         (bfr-p nil)))

  (def-updater-independence-thm bfr-p-updater-independence
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old)))
             (equal (bfr-p x new) (bfr-p x old))))

  (defthm bfr-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x old))
             (bfr-p x new))
    :hints(("Goal" :in-theory (enable logicman-extension-p)))))

(std::deflist bfr-listp$ (x logicman)
  (bfr-p x)
  :true-listp t
  ///
  (defthm bfr-listp-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-listp$ x old))
             (bfr-listp$ x new))))

(defmacro bfr-listp (x &optional (logicman 'logicman))
  `(bfr-listp$ ,x ,logicman))

(add-macro-alias bfr-listp bfr-listp$)



(define aignet-lit->bfr ((x satlink::litp) &optional (logicman 'logicman))
  :guard (stobj-let ((aignet (logicman->aignet logicman)))
                    (ans)
                    (aignet::fanin-litp x aignet)
                    ans)
  :returns (bfr bfr-p :hyp (eq (bfr-mode) :aignet)
                :hints(("Goal" :in-theory (enable bfr-p))))
  (b* ((x (mbe :logic (non-exec (aignet::aignet-lit-fix x (logicman->aignet logicman)))
               :exec x)))
    (case x
      (0 nil)
      (1 t)
      (t x)))
  ///
  
  (defthm aignet-lit->bfr-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (aignet::aignet-litp x (logicman->aignet old)))
             (equal (aignet-lit->bfr x new)
                    (aignet-lit->bfr x old)))
    :hints(("Goal" :in-theory (enable logicman-extension-p)))))


(define bfr-fix ((x bfr-p) &optional (logicman 'logicman))
  :returns (new-x bfr-p)
  :prepwork ((local (in-theory (enable bfr-p aignet-lit->bfr))))
  (mbe :logic (bfr-case
                :aig (aig-fix x)
                :bdd (acl2::ubdd-fix x)
                :aignet
                (if (booleanp x)
                    x
                  (aignet-lit->bfr x)))
       :exec x)
  ///
  (std::defret bfr-fix-when-bfr-p
    (implies (bfr-p x)
             (equal new-x x))))

(define bfr-list-fix ((x bfr-listp) &optional (logicman 'logicman))
  :returns (new-x bfr-listp)
  (if (atom x)
      nil
    (cons (bfr-fix (car x))
          (bfr-list-fix (cdr x))))
  ///
  (defret bfr-list-fix-when-bfr-listp
    (implies (bfr-listp x)
             (equal (bfr-list-fix x) x)))

  (defret car-of-bfr-list-fix
    (implies (consp x)
             (equal (car (bfr-list-fix x))
                    (bfr-fix (car x)))))

  (defret cdr-of-bfr-list-fix
    (implies (consp x)
             (equal (cdr (bfr-list-fix x))
                    (bfr-list-fix (cdr x)))))

  (defret consp-of-bfr-list-fix
    (equal (consp (bfr-list-fix x))
           (consp x)))

  (defret len-of-bfr-list-fix
    (equal (len (bfr-list-fix x))
           (len x))))

(define bfr->aignet-lit ((x bfr-p) &optional (logicman 'logicman))
  :guard (eq (bfr-mode) :aignet)
  :returns (lit (implies (eq (bfr-mode) :aignet)
                         (aignet::aignet-litp lit (logicman->aignet logicman))))
  :prepwork ((local (in-theory (enable bfr-fix aignet-lit->bfr bfr-p))))
  (b* ((x (bfr-fix x)))
    (case x
      ((nil) 0)
      ((t) 1)
      (t (satlink::lit-fix x))))
  ///
  (defthm bfr->aignet-lit-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x old))
             (equal (bfr->aignet-lit x new)
                    (bfr->aignet-lit x old))))

  (defthm bfr->aignet-lit-of-aignet-lit->bfr
    (implies (equal (bfr-mode) :aignet)
             (equal (bfr->aignet-lit (aignet-lit->bfr x))
                    (aignet::aignet-lit-fix x (logicman->aignet logicman))))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr))))

  (defthm aignet-lit->bfr-of-bfr->aignet-lit
    (implies (equal (bfr-mode) :aignet)
             (equal (aignet-lit->bfr (bfr->aignet-lit x))
                    (bfr-fix x)))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr bfr-fix))))

  (defthm bfr->aignet-lit-of-bfr-fix
    (equal (bfr->aignet-lit (bfr-fix x))
           (bfr->aignet-lit x))
    :hints(("Goal" :in-theory (enable bfr-fix)))))



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
                                    acl2::take-redefinition))
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
                  (aignet-idp x old))
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
                  (aignet-litp x old))
             (equal (lit-eval x (fgl::alist-to-bitarr (stype-count :pi new) env bitarr) regvals old)
                    (lit-eval x (fgl::alist-to-bitarr (stype-count :pi old) env bitarr) regvals old)))
    :hints (("goal" 
             :expand ((:free (invals regvals)
                       (lit-eval x invals regvals old)))
             :in-theory (enable aignet-idp)))))



(define bfr-eval ((x bfr-p) env &optional (logicman 'logicman))
  :short "Evaluate a BFR under an appropriate BDD/AIG environment."
  :returns bool
  :prepwork (;; (local (include-book "std/lists/nth" :dir :system))
             (local (defthm alist-to-bits-of-nil-under-bits-equiv
                      (aignet::bits-equiv (alist-to-bitarr max nil bitarr)
                                          nil)
                      :hints(("Goal" :in-theory (enable aignet::bits-equiv)))))
             ;; (local (defthm bools-to-bits-of-take-under-bits-equiv
             ;;          (aignet::bits-equiv (bools-to-bits (take n x))
             ;;                              (take n (bools-to-bits x)))
             ;;          :hints(("Goal" :in-theory (enable aignet::bits-equiv)))))
             ;; (local (defthm bools-to-bits-of-repeat
             ;;          (aignet::bits-equiv (bools-to-bits (acl2::repeat n nil))
             ;;                              nil)
             ;;          :hints(("Goal" :in-theory (enable aignet::bits-equiv)))))
             ;; (local
             ;;  #!aignet
             ;;  (progn
             ;;    ;; bozo, copied from aignet/copying.lisp
             ;;    (defthm id-eval-of-take-num-ins
             ;;      (equal (id-eval id (take (stype-count :pi aignet) invals)
             ;;                      regvals aignet)
             ;;             (id-eval id invals regvals aignet))
             ;;      :hints (("goal" :induct (id-eval-ind id aignet)
             ;;               :expand ((:free (invals regvals)
             ;;                         (id-eval id invals regvals aignet)))
             ;;               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

             ;;    (defthm id-eval-of-take-num-regs
             ;;      (equal (id-eval id invals
             ;;                      (take (stype-count :reg aignet) regvals)
             ;;                      aignet)
             ;;             (id-eval id invals regvals aignet))
             ;;      :hints (("goal" :induct (id-eval-ind id aignet)
             ;;               :expand ((:free (invals regvals)
             ;;                         (id-eval id invals regvals aignet)))
             ;;               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

             ;;    (defthm lit-eval-of-take-num-ins
             ;;      (equal (lit-eval lit (take (stype-count :pi aignet) invals)
             ;;                       regvals aignet)
             ;;             (lit-eval lit invals regvals aignet))
             ;;      :hints(("Goal"
             ;;              :expand ((:free (invals regvals)
             ;;                        (lit-eval lit invals regvals aignet))))))))
             )

  (bfr-case
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
                    (mv ans aignet::invals aignet::regvals)))))
  ///
  (defthm bfr-eval-consts
    (and (equal (bfr-eval t env) t)
         (equal (bfr-eval nil env) nil))
    :hints(("Goal" :in-theory (enable bfr->aignet-lit))))

  (defthm bfr-eval-of-aignet-lit->bfr
    (implies (equal (bfr-mode) :aignet)
             (equal (bfr-eval (aignet-lit->bfr x) env)
                    (acl2::bit->bool (aignet::lit-eval
                                      x
                                      (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman)) env nil)
                                      nil
                                      (logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr bfr->aignet-lit
                                      logicman-extension-p
                                      bfr-fix)
            :use ((:instance aignet::lit-eval-of-aignet-lit-fix
                   (x x)
                   (invals (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman)) env nil))
                   (regvals nil)
                   (aignet (logicman->aignet logicman)))))))

  (defthm bfr-eval-of-bfr-fix
    (equal (bfr-eval (bfr-fix x) env)
           (bfr-eval x env))
    :hints(("Goal" :in-theory (enable bfr-fix
                                      bfr->aignet-lit
                                      aignet-lit->bfr
                                      aignet::lit-eval-of-aignet-lit-fix))))
  
  (defthm bfr-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x old))
             (equal (bfr-eval x env new)
                    (bfr-eval x env old)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable logicman-extension-p))))))


(define bfr-list-eval ((x bfr-listp) env &optional (logicman 'logicman))
  :returns bools
  (if (atom x)
      nil
    (cons (bfr-eval (car x) env)
          (bfr-list-eval (cdr x) env)))
  ///
  (defthm bfr-list-eval-of-bfr-list-fix
    (equal (bfr-list-eval (bfr-list-fix x) env)
           (bfr-list-eval x env)))

  (defthm bfr-list-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-listp x old))
             (equal (bfr-list-eval x env new)
                    (bfr-list-eval x env old)))))

(define bools->int (x)
  (mbe :logic (if (atom (cdr x))
                  (- (bool->bit (car x)))
                (logcons (bool->bit (car x))
                         (bools->int (cdr x))))
       :exec (cond ((atom x) 0)
                   ((atom (cdr x)) (- (bool->bit (car x))))
                   (t (logcons (bool->bit (car x))
                         (bools->int (cdr x)))))))




(define logicman-nvars-ok (&optional (logicman 'logicman))
  (bfr-case
    :bdd t
    :aig t
    :aignet
    (stobj-let
     ((aignet (logicman->aignet logicman))
      (bvar-db (logicman->bvar-db logicman)))
     (ok)
     (equal (next-bvar bvar-db)
            (aignet::num-ins aignet))
     ok))
  ///
  (def-updater-independence-thm logicman-nvars-ok-updater-independence
    (implies (and (equal (logicman->mode new)
                         (logicman->mode old))
                  (equal (next-bvar (logicman->bvar-db new))
                         (next-bvar (logicman->bvar-db old)))
                  (equal (aignet::num-ins (logicman->aignet new))
                         (aignet::num-ins (logicman->aignet old))))
             (equal (logicman-nvars-ok new)
                    (logicman-nvars-ok old)))))


(define bfr-nvars (&optional (logicman 'logicman))
  :guard (logicman-nvars-ok)
  :prepwork ((local (in-theory (enable logicman-nvars-ok))))
  (mbe :logic (non-exec (next-bvar$a (logicman->bvar-db logicman)))
       :exec (stobj-let
              ((bvar-db (logicman->bvar-db logicman)))
              (nvars)
              (next-bvar bvar-db)
              nvars))
  ///
  (def-updater-independence-thm bfr-nvars-updater-independenc
    (implies (equal (next-bvar (logicman->bvar-db new))
                    (next-bvar (logicman->bvar-db old)))
             (equal (bfr-nvars new) (bfr-nvars old))))

  (defthm bfr-nvars-of-logicman-extension
    (implies (bind-logicman-extension new old)
             (<= (bfr-nvars old) (bfr-nvars new)))
    :hints(("Goal" :in-theory (enable logicman-extension-p
                                      bvar-db-extension-p)))
    :rule-classes ((:linear :trigger-terms ((bfr-nvars new)))))

  (defthm logicman-nvars-ok-implies
    (implies (and (logicman-nvars-ok)
                  (equal (bfr-mode) :aignet))
             (equal (aignet::stype-count :pi (logicman->aignet logicman))
                    (bfr-nvars)))))
                    
(define logicman-init ((base-nvars natp)
                       (mode bfr-mode-p)
                       &optional (logicman 'logicman))
  :returns (new-logicman logicman-nvars-ok
                         :hints(("Goal" :in-theory (enable logicman-nvars-ok))))
  (b* ((logicman (update-logicman->mode (bfr-mode-fix mode) logicman))
       (logicman
        (stobj-let
         ((bvar-db (logicman->bvar-db logicman)))
         (bvar-db)
         (init-bvar-db base-nvars bvar-db)
         logicman))
       ((unless (eq (bfr-mode-fix mode) :aignet))
        logicman))
    (stobj-let
     ((aignet (logicman->aignet logicman)))
     (aignet)
     (b* ((aignet (aignet::aignet-init 0 0 (* 2 (lnfix base-nvars)) 100000 aignet)))
       (aignet::aignet-add-ins base-nvars aignet))
     logicman)))
   

(define logicman-add-var ((obj gl-object-p)
                          &optional (logicman 'logicman))
  :returns (new-logicman
            (implies (logicman-nvars-ok logicman)
                     (logicman-nvars-ok new-logicman))
            :hints(("Goal" :in-theory (enable logicman-nvars-ok))))
  (b* ((logicman
        (stobj-let
         ((bvar-db (logicman->bvar-db logicman)))
         (bvar-db)
         (add-term-bvar (gl-object-fix obj) bvar-db)
         logicman))
       ((unless (eq (logicman->mode logicman) :aignet))
        logicman))
    (stobj-let
     ((aignet (logicman->aignet logicman)))
     (aignet)
     (aignet::aignet-add-in aignet)
     logicman))
  ///
  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (+ 1 (bfr-nvars logicman)))
    :hints(("Goal" :in-theory (enable bfr-nvars)))))




(define bfr-varname-p (x &optional (logicman 'logicman))
  :guard (logicman-nvars-ok)
  ;; :guard-hints (("goal" :in-theory (enable logicman-nvars-ok)))
  (and (natp x)
       (< x (bfr-nvars))
       (mbt (or (not (equal (bfr-mode) :aignet))
                (non-exec (< x (aignet::num-ins (logicman->aignet logicman)))))))
  ///
  ;; (def-updater-independence-thm bfr-varname-p-updater-independence
  ;;   (implies (and (bfr-varname-p x old)
  ;;                 (equal (next-bvar (logicman->bvar-db new))
  ;;                        (next-bvar (logicman->bvar-db old)))
  ;;                 (equal (aignet::num-ins (logicman->aignet new))
  ;;                        (aignet::num-ins (logicman->aignet old))))
  ;;            (bfr-varname-p x new)))

  (defthm bfr-varname-p-implies-natp
    (implies (bfr-varname-p x)
             (natp x))
    :rule-classes :forward-chaining)

  (defthm bfr-varname-p-of-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p x old))
             (bfr-varname-p x new))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable logicman-extension-p))))))
             


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


(define bfr-lookup ((n (bfr-varname-p n logicman)) env &optional ((logicman logicman-nvars-ok) 'logicman))
  :prepwork ((local (in-theory (enable bfr-varname-p))))
  (bfr-case
    :bdd (and (nth n (list-fix env)) t)
    :aig (acl2::aig-env-lookup (lnfix n) env)
    :aignet (bool-fix (cdr (hons-assoc-equal (lnfix n) env))))
  ///
  (def-updater-independence-thm bfr-lookup-logicman-updater-indep
    (implies (equal (bfr-mode new) (bfr-mode old))
             (equal (bfr-lookup n env new)
                    (bfr-lookup n env old)))))

(define bfr-set-var ((n bfr-varname-p) val env &optional ((logicman logicman-nvars-ok) 'logicman))
  :short "Set the @('n')th BFR variable to some value in an AIG/BDD environment."
  (bfr-case :bdd (acl2::with-guard-checking
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
                                   (update-nth nth))))))


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

(define bfr-depends-on ((v bfr-varname-p) (x bfr-p) &optional ((logicman logicman-nvars-ok) 'logicman))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-varname-p))))
  :returns (val booleanp :rule-classes :type-prescription)
  :prepwork ((local (defthm booleanp-nth-of-boolean-listp
                      (implies (boolean-listp x)
                               (booleanp (nth n x)))
                      :hints(("Goal" :in-theory (enable nth))))))
  (bfr-case
    :bdd (ec-call (nth v (acl2::ubdd-deps (acl2::ubdd-fix x))))
    :aig (set::in (lnfix v) (acl2::aig-vars (bfr-fix x)))
    :aignet
    (b* ((lit (bfr->aignet-lit x)))
      (stobj-let ((aignet (logicman->aignet logicman)))
                 (depends-on)
                 (aignet::depends-on (satlink::lit->var lit)
                                     (aignet::innum->id v aignet)
                                     aignet)
                 depends-on)))
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
    (equal (bfr-depends-on v (bfr-fix x))
           (bfr-depends-on v x))
    :hints(("Goal" :in-theory (enable bfr-fix bfr->aignet-lit))))

  (defthm bfr-eval-of-bfr-set-var-when-not-depends-on
    (implies (not (bfr-depends-on v x))
             (equal (bfr-eval x (bfr-set-var v val env))
                    (bfr-eval x env)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (bfr-eval bfr-set-var bfr-fix logicman->mode)
                                   ((logicman->mode)))))))

  (defthm bfr-depends-on-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p v old)
                  (bfr-p x old))
             (equal (bfr-depends-on v x new)
                    (bfr-depends-on v x old)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable logicman-extension-p
                                      bfr-p bfr-varname-p))))))


(define bfr-list-depends-on ((v bfr-varname-p) (x bfr-listp) &optional ((logicman logicman-nvars-ok) 'logicman))
  :returns (val booleanp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (or (bfr-depends-on v (car x))
        (bfr-list-depends-on v (cdr x))))

  ///

  (defthm bfr-list-depends-on-of-bfr-list-fix
    (equal (bfr-list-depends-on v (bfr-list-fix x))
           (bfr-list-depends-on v x)))

  (fty::deffixcong acl2::list-equiv equal (bfr-list-depends-on v x) x)

  (defthm bfr-list-eval-of-bfr-set-var-when-not-depends-on
    (implies (not (bfr-list-depends-on v x))
             (equal (bfr-list-eval x (bfr-set-var v val env))
                    (bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-list-eval))))

  (defthm bfr-list-depends-on-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p v old)
                  (bfr-listp x old))
             (equal (bfr-list-depends-on v x new)
                    (bfr-list-depends-on v x old)))))
                                


(define bfr-var ((n bfr-varname-p) &optional ((logicman logicman-nvars-ok) 'logicman))
  :returns (bfr bfr-p :hints((and stable-under-simplificationp
                                  '(:in-theory (enable bfr-p aig-p)))))
  :guard-hints (("goal" :in-theory (enable bfr-varname-p)))
  (bfr-case
    :bdd (acl2::qv n)
    :aig (lnfix n)
    :aignet (stobj-let
             ((aignet (logicman->aignet logicman)))
             (lit)
             (aignet::make-lit (aignet::innum->id n aignet) 0)
             (aignet-lit->bfr lit)))
  ///
  (defthm bfr-eval-of-bfr-var
    (implies (bfr-varname-p n)
             (equal (bfr-eval (bfr-var n) env)
                    (bfr-lookup n env)))
    :hints(("Goal" :in-theory (enable bfr-varname-p
                                      bfr-eval
                                      bfr-fix
                                      aig-fix
                                      bfr-lookup
                                      aignet::lit-eval-of-aignet-lit-fix)
            :expand ((:free (id invals regvals aignet)
                      (aignet::lit-eval (aignet::make-lit id 0) invals regvals aignet))
                     (:free (n invals regvals aignet)
                      (aignet::id-eval (aignet::fanin-count (aignet::lookup-stype n :pi aignet))
                                       invals regvals aignet))))))

  (defthm bfr-var-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p n old))
             (equal (bfr-var n new)
                    (bfr-var n old)))
    :hints(("Goal" :in-theory (enable logicman-extension-p aignet-lit->bfr
                                      bfr-varname-p))))

  (defthm bfr-depends-on-of-bfr-var
    (implies (and (bfr-varname-p v)
                  (bfr-varname-p n))
             (iff (bfr-depends-on v (bfr-var n))
                  (equal (nfix v) (nfix n))))
    :hints(("Goal" :in-theory (enable bfr-depends-on bfr-varname-p bfr-fix aig-fix)
            :expand ((:free (ci x) (aignet::depends-on
                                    (aignet::fanin-count x)
                                    ci
                                    (logicman->aignet logicman))))))))

(local (defthm aig-p-when-bfr-p
         (implies (and (bfr-mode)
                       (not (equal (bfr-mode) :aignet))
                       (bfr-p x))
                  (aig-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm bfr-p-when-aig-p
         (implies (and (bfr-mode)
                       (not (equal (bfr-mode) :aignet))
                       (aig-p x))
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm ubdd-p-when-bfr-p
         (implies (and (not (bfr-mode))
                       (bfr-p x))
                  (acl2::ubddp x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm bfr-p-when-ubdd-p
         (implies (and (not (bfr-mode))
                       (acl2::ubddp x))
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm aignet-litp-when-bfr-p
         (implies (and (bfr-p x)
                       (equal (bfr-mode) :aignet)
                       (not (booleanp x)))
                  (aignet::aignet-litp x (logicman->aignet logicman)))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(local (defthm bfr-p-when-aignet-litp
         (implies (and (equal (bfr-mode) :aignet)
                       (aignet::aignet-litp x (logicman->aignet logicman))
                       (satlink::litp x)
                       (not (equal x 1))
                       (not (equal x 0)))
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p)))))


(define bfr-not ((x bfr-p) &optional (logicman 'logicman))
  :returns (bfr bfr-p :hints(("Goal" :in-theory (enable bfr-p))))
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
  (mbe :logic (b* ((x (bfr-fix x)))
                (bfr-case
                  :bdd (acl2::q-not x)
                  :aig (acl2::aig-not x)
                  :aignet (aignet-lit->bfr
                           (aignet::lit-negate
                            (bfr->aignet-lit x)))))
       :exec (if (booleanp x)
                 (not x)
               (bfr-case
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
    (equal (bfr-not (bfr-fix x))
           (bfr-not x)))

  (defthm bfr-depends-on-of-bfr-not
    (implies (not (bfr-depends-on v x))
             (not (bfr-depends-on v (bfr-not x))))
    :hints(("Goal" :in-theory (enable bfr-depends-on))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-fix))))))


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
                 :expand ((:free (x) (aignet::reduce-gate-rec 0 0 x gatesimp aignet))
                          (:free (x) (aignet::reduce-gate-rec 0 x 0 gatesimp aignet))
                          (:free (x) (aignet::reduce-gate-rec 4 0 x gatesimp aignet)))))))

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
                 :expand ((:free (x) (aignet::reduce-gate-rec 0 1 x gatesimp aignet))
                          (:free (x) (aignet::reduce-gate-rec 0 x 1 gatesimp aignet))
                          (:free (x) (aignet::reduce-gate-rec 4 x 0 gatesimp aignet)))))))

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
                 :expand ((:free (x y) (aignet::reduce-gate-rec 2 x y gatesimp aignet))
                          (:free (x y) (aignet::reduce-gate-rec 4 x y gatesimp aignet))
                          (:free (x y) (aignet::reduce-gate-rec 5 x y gatesimp aignet)))))))

(local (defthm bfr->aignet-lit-of-consts
         (and (Equal (bfr->aignet-lit nil) 0)
              (equal (Bfr->aignet-lit t) 1))
         :hints(("Goal" :in-theory (enable bfr->aignet-lit)))))
(local (defthm aignet-lit->bfr-of-consts
         (and (equal (aignet-lit->bfr 1) t)
              (equal (aignet-lit->bfr 0) nil))
         :hints(("Goal" :in-theory (enable aignet-lit->bfr)))))


(local (in-theory (disable set::in-tail))) ;; incompatible with trivial ancestors check

(define bfr-and ((x bfr-p)
                 (y bfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (and-bfr (bfr-p and-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t))

  (mbe :logic
       (b* ((x (bfr-fix x))
            (y (bfr-fix y)))
         (bfr-case
           :bdd (mv (acl2::q-binary-and x y) logicman)
           :aig (mv (acl2::aig-and x y) logicman)
           :aignet (b* ((x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-and x y (aignet::default-gatesimp) aignet::strash aignet)
                      (mv (aignet-lit->bfr lit) logicman)))))
       :exec
       (cond ((not x) (mv nil logicman))
             ((not y) (mv nil logicman))
             ((eq x t) (mv y logicman))
             ((eq y t) (mv x logicman))
             (t (bfr-case
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
                     (mv (aignet-lit->bfr lit) logicman)))))))
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
    (equal (bfr-and (bfr-fix x) y)
           (bfr-and x y)))

  (defthm bfr-and-of-bfr-fix-y
    (equal (bfr-and x (bfr-fix y))
           (bfr-and x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

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



(define bfr-or ((x bfr-p)
                (y bfr-p)
                &optional (logicman 'logicman))
  :returns (mv (or-bfr (bfr-p or-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable aignet::aignet-hash-or)))

  (mbe :logic
       (b* ((x (bfr-fix x))
            (y (bfr-fix y)))
         (bfr-case
           :bdd (mv (acl2::q-binary-or x y) logicman)
           :aig (mv (acl2::aig-or x y) logicman)
           :aignet (b* ((x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-or x y (aignet::default-gatesimp) aignet::strash aignet)
                      (mv (aignet-lit->bfr lit) logicman)))))
       :exec
       (cond ((eq x t) (mv t logicman))
             ((eq y t) (mv t logicman))
             ((eq x nil) (mv y logicman))
             ((eq y nil) (mv x logicman))
             (t (bfr-case
                  :bdd (mv (acl2::q-binary-or x y) logicman)
                  :aig (mv (acl2::aig-or x y) logicman)
                  :aignet
                  (b* ((x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-or x y (aignet::default-gatesimp) aignet::strash aignet)
                     (mv (aignet-lit->bfr lit) logicman)))))))
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
    (equal (bfr-or (bfr-fix x) y)
           (bfr-or x y)))

  (defthm bfr-or-of-bfr-fix-y
    (equal (bfr-or x (bfr-fix y))
           (bfr-or x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

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


(define bfr-xor ((x bfr-p)
                 (y bfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (xor-bfr (bfr-p xor-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable bfr-not acl2::aig-xor acl2::q-xor))
                (and stable-under-simplificationp '(:in-theory (enable bfr-p))))

  (mbe :logic
       (b* ((x (bfr-fix x))
            (y (bfr-fix y)))
         (bfr-case
           :bdd (mv (acl2::q-binary-xor x y) logicman)
           :aig (mv (acl2::aig-xor x y) logicman)
           :aignet (b* ((x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-xor x y (aignet::default-gatesimp) aignet::strash aignet)
                      (mv (aignet-lit->bfr lit) logicman)))))
       :exec
       (cond ((eq x t) (mv (bfr-not y) logicman))
             ((eq x nil) (mv y logicman))
             ((eq y t) (mv (bfr-not x) logicman))
             ((eq y nil) (mv x logicman))
             (t (bfr-case
                  :bdd (mv (acl2::q-binary-xor x y) logicman)
                  :aig (mv (acl2::aig-xor x y) logicman)
                  :aignet
                  (b* ((x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-xor x y (aignet::default-gatesimp) aignet::strash aignet)
                     (mv (aignet-lit->bfr lit) logicman)))))))
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
    (equal (bfr-xor (bfr-fix x) y)
           (bfr-xor x y)))

  (defthm bfr-xor-of-bfr-fix-y
    (equal (bfr-xor x (bfr-fix y))
           (bfr-xor x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

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


(define bfr-iff ((x bfr-p)
                 (y bfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (iff-bfr (bfr-p iff-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable bfr-not acl2::aig-iff acl2::q-iff
                                    aignet::aignet-hash-iff))
                (and stable-under-simplificationp '(:in-theory (enable bfr-p))))

  (mbe :logic
       (b* ((x (bfr-fix x))
            (y (bfr-fix y)))
         (bfr-case
           :bdd (mv (acl2::q-binary-iff x y) logicman)
           :aig (mv (acl2::aig-iff x y) logicman)
           :aignet (b* ((x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-iff x y (aignet::default-gatesimp) aignet::strash aignet)
                      (mv (aignet-lit->bfr lit) logicman)))))
       :exec
       (cond ((eq x nil) (mv (bfr-not y) logicman))
             ((eq x t) (mv y logicman))
             ((eq y nil) (mv (bfr-not x) logicman))
             ((eq y t) (mv x logicman))
             (t (bfr-case
                  :bdd (mv (acl2::q-binary-iff x y) logicman)
                  :aig (mv (acl2::aig-iff x y) logicman)
                  :aignet
                  (b* ((x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-iff x y (aignet::default-gatesimp) aignet::strash aignet)
                     (mv (aignet-lit->bfr lit) logicman)))))))
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
    (equal (bfr-iff (bfr-fix x) y)
           (bfr-iff x y)))

  (defthm bfr-iff-of-bfr-fix-y
    (equal (bfr-iff x (bfr-fix y))
           (bfr-iff x y)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

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
                       (equal (bfr-mode) :aignet))
                  (iff (equal (bfr->aignet-lit x) (bfr->aignet-lit y))
                       (equal x y)))
         :hints (("goal" :use ((:instance aignet-lit->bfr-of-bfr->aignet-lit (x x))
                               (:instance aignet-lit->bfr-of-bfr->aignet-lit (x y)))
                  :in-theory (disable aignet-lit->bfr-of-bfr->aignet-lit)))))

(define bfr-ite ((x bfr-p)
                 (y bfr-p)
                 (z bfr-p)
                 &optional (logicman 'logicman))
  :returns (mv (ite-bfr (bfr-p ite-bfr new-logicman))
               (new-logicman))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable acl2::aig-ite-fn aignet::aignet-hash-mux
                                    aignet::aignet-hash-or)))

  (mbe :logic
       (b* ((x (bfr-fix x))
            (y (bfr-fix y))
            (z (bfr-fix z)))
         (bfr-case
           :bdd (mv (acl2::q-ite x y z) logicman)
           :aig (mv (acl2::aig-ite x y z) logicman)
           :aignet (b* ((x (bfr->aignet-lit x))
                        (y (bfr->aignet-lit y))
                        (z (bfr->aignet-lit z)))
                     (stobj-let
                      ((aignet (logicman->aignet logicman))
                       (aignet::strash (logicman->strash logicman)))
                      (lit aignet::strash aignet)
                      (aignet::aignet-hash-mux x y z (aignet::default-gatesimp) aignet::strash aignet)
                      (mv (aignet-lit->bfr lit) logicman)))))
       :exec
       (cond ((eq x t) (mv y logicman))
             ((eq x nil) (mv z logicman))
             ((hons-equal y z) (mv y logicman))
             (t (bfr-case
                  :bdd (mv (acl2::q-ite x y z) logicman)
                  :aig (mv (acl2::aig-ite x y z) logicman)
                  :aignet
                  (b* ((x (bfr->aignet-lit x))
                       (y (bfr->aignet-lit y))
                       (z (bfr->aignet-lit z)))
                    (stobj-let
                     ((aignet (logicman->aignet logicman))
                      (aignet::strash (logicman->strash logicman)))
                     (lit aignet::strash aignet)
                     (aignet::aignet-hash-mux x y z (aignet::default-gatesimp) aignet::strash aignet)
                     (mv (aignet-lit->bfr lit) logicman)))))))
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
    (equal (bfr-ite (bfr-fix x) y z)
           (bfr-ite x y z)))

  (defthm bfr-ite-of-bfr-fix-y
    (equal (bfr-ite x (bfr-fix y) z)
           (bfr-ite x y z)))
  
  (defthm bfr-ite-of-bfr-fix-z
    (equal (bfr-ite x y (bfr-fix z))
           (bfr-ite x y z)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

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



(defines gl-bfr-object-p-aux
  (define gl-bfr-object-p-aux ((x gl-object-p)
                           &optional (logicman 'logicman))
    :measure (gl-object-count x)
    (gl-object-case x
      :g-concrete t
      :g-boolean (bfr-p x.bool)
      :g-integer (bfr-listp x.bits)
      :g-ite (and (gl-bfr-object-p-aux x.test)
                  (gl-bfr-object-p-aux x.then)
                  (gl-bfr-object-p-aux x.else))
      :g-apply (gl-bfr-objectlist-p-aux x.args)
      :g-var t
      :g-cons (and (gl-bfr-object-p-aux x.car)
                   (gl-bfr-object-p-aux x.cdr))))
  (define gl-bfr-objectlist-p-aux ((x gl-objectlist-p)
                               &optional (logicman 'logicman))
    :measure (gl-objectlist-count x)
    (if (atom x)
        t
      (and (gl-bfr-object-p-aux (car x))
           (gl-bfr-objectlist-p-aux (cdr x))))))


(defines gl-bfr-object-p
  (define gl-bfr-object-p (x &optional (logicman 'logicman))
    :measure (gl-object-count x)
    :verify-guards nil
    (mbe :logic (and (gl-object-p x)
                     (gl-object-case x
                       :g-concrete t
                       :g-boolean (bfr-p x.bool)
                       :g-integer (bfr-listp x.bits)
                       :g-ite (and (gl-bfr-object-p x.test)
                                   (gl-bfr-object-p x.then)
                                   (gl-bfr-object-p x.else))
                       :g-apply (gl-bfr-objectlist-p x.args)
                       :g-var t
                       :g-cons (and (gl-bfr-object-p x.car)
                                    (gl-bfr-object-p x.cdr))))
         :exec (and (gl-object-p x)
                    (gl-bfr-object-p-aux x))))
  (define gl-bfr-objectlist-p (x
                               &optional (logicman 'logicman))
    :measure (gl-objectlist-count x)
    (mbe :logic (and (gl-objectlist-p x)
                     (if (atom x)
                         t
                       (and (gl-bfr-object-p (car x))
                            (gl-bfr-objectlist-p (cdr x)))))
         :exec (and (gl-objectlist-p x)
                    (gl-bfr-objectlist-p-aux x))))
  ///
  (local
   (defthm-gl-bfr-object-p-flag
     (defthm gl-bfr-object-p-aux-elim
       (implies (gl-object-p x)
                (equal (gl-bfr-object-p-aux x)
                       (gl-bfr-object-p x)))
       :hints ('(:expand ((gl-bfr-object-p-aux x)
                          (gl-bfr-object-p x))))
       :flag gl-bfr-object-p)
     (defthm gl-bfr-objectlist-p-aux-elim
       (implies (gl-objectlist-p x)
                (equal (gl-bfr-objectlist-p-aux x)
                       (gl-bfr-objectlist-p x)))
       :hints ('(:expand ((gl-bfr-objectlist-p-aux x)
                          (gl-bfr-objectlist-p-aux nil)
                          (gl-bfr-objectlist-p x)
                          (gl-bfr-objectlist-p nil))))
       :flag gl-bfr-objectlist-p)))
  
  (verify-guards gl-bfr-object-p-fn)

  (defthm gl-object-p-when-gl-bfr-object-p
    (implies (gl-bfr-object-p x)
             (gl-object-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm gl-objectlist-p-when-gl-bfr-objectlist-p
    (implies (gl-bfr-objectlist-p x)
             (gl-objectlist-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm gl-bfr-object-p-when-g-boolean
    (implies (and (gl-object-case x :g-boolean)
                  (gl-bfr-object-p x))
             (bfr-p (g-boolean->bool x)))
    :hints (("goal" :expand ((gl-bfr-object-p x)))))

  (defthm gl-bfr-object-p-when-g-integer
    (implies (and (gl-object-case x :g-integer)
                  (gl-bfr-object-p x))
             (bfr-listp (g-integer->bits x)))
    :hints (("goal" :expand ((gl-bfr-object-p x)))))

  (defthm gl-bfr-object-p-when-g-ite
    (implies (and (gl-object-case x :g-ite)
                  (gl-bfr-object-p x))
             (and (gl-bfr-object-p (g-ite->test x))
                  (gl-bfr-object-p (g-ite->then x))
                  (gl-bfr-object-p (g-ite->else x))))
    :hints (("goal" :expand ((gl-bfr-object-p x)))))

  (defthm gl-bfr-object-p-when-g-apply
    (implies (and (gl-object-case x :g-apply)
                  (gl-bfr-object-p x))
             (gl-bfr-objectlist-p (g-apply->args x)))
    :hints (("goal" :expand ((gl-bfr-object-p x)))))

  (defthm gl-bfr-object-p-when-g-cons
    (implies (and (gl-object-case x :g-cons)
                  (gl-bfr-object-p x))
             (and (gl-bfr-object-p (g-cons->car x))
                  (gl-bfr-object-p (g-cons->cdr x))))
    :hints (("goal" :expand ((gl-bfr-object-p x)))))

  (defthm gl-bfr-objectlist-p-implies-car/cdr
    (implies (gl-bfr-objectlist-p x)
             (and (gl-bfr-object-p (car x))
                  (gl-bfr-objectlist-p (cdr x))))
    :hints (("goal" :expand ((gl-bfr-objectlist-p x)
                             (gl-bfr-object-p nil)
                             (gl-bfr-objectlist-p nil)))))

  (defthm gl-bfr-objectlist-p-of-cons
    (implies (and (gl-bfr-object-p x)
                  (gl-bfr-objectlist-p y))
             (gl-bfr-objectlist-p (cons x y)))
    :hints (("goal" :expand ((gl-bfr-objectlist-p (cons x y))))))

  (defthm gl-bfr-objectlist-p-of-nil
    (gl-bfr-objectlist-p nil)
    :hints (("goal" :expand ((gl-bfr-objectlist-p nil)))))

  (defthm gl-bfr-object-p-of-g-concrete
    (gl-bfr-object-p (g-concrete val))
    :hints (("goal" :expand ((gl-bfr-object-p (g-concrete val))))))

  (defthm gl-bfr-object-p-of-g-boolean
    (implies (bfr-p bool)
             (gl-bfr-object-p (g-boolean bool)))
    :hints (("goal" :expand ((gl-bfr-object-p (g-boolean bool))))))

  (defthm gl-bfr-object-p-of-g-integer
    (implies (bfr-listp bits)
             (gl-bfr-object-p (g-integer bits)))
    :hints (("goal" :expand ((gl-bfr-object-p (g-integer bits))))))

  (defthm gl-bfr-object-p-of-g-ite
    (implies (and (gl-bfr-object-p test)
                  (gl-bfr-object-p then)
                  (gl-bfr-object-p else))
             (gl-bfr-object-p (g-ite test then else)))
    :hints (("goal" :expand ((gl-bfr-object-p (g-ite test then else))))))

  (defthm gl-bfr-object-p-of-g-apply
    (implies (and (gl-bfr-objectlist-p args))
             (gl-bfr-object-p (g-apply fn args)))
    :hints (("goal" :expand ((gl-bfr-object-p (g-apply fn args))))))

  (defthm gl-bfr-object-p-of-g-var
    (gl-bfr-object-p (g-var name))
    :hints (("goal" :expand ((gl-bfr-object-p (g-var name))))))

  (defthm gl-bfr-object-p-of-g-cons
    (implies (and (gl-bfr-object-p car)
                  (gl-bfr-object-p cdr))
             (gl-bfr-object-p (g-cons car cdr)))
    :hints (("goal" :expand ((gl-bfr-object-p (g-cons car cdr))))))

  (defthm-gl-bfr-object-p-flag gl-bfr-object-p-of-logicman-extension
    (defthm gl-bfr-object-p-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-object-p x old))
               (gl-bfr-object-p x new))
      :hints ('(:expand ((:free (logicman) (gl-bfr-object-p x logicman)))))
      :flag gl-bfr-object-p)
    (defthm gl-bfr-objectlist-p-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-objectlist-p x old))
               (gl-bfr-objectlist-p x new))
      :hints ('(:expand ((:free (logicman) (gl-bfr-objectlist-p x logicman)))))
      :flag gl-bfr-objectlist-p)
    :hints (("goal" :induct (gl-bfr-object-p-flag flag x new)))))


(defines gl-bfr-object-fix
  (define gl-bfr-object-fix ((x gl-bfr-object-p)
                             &optional (logicman 'logicman))
    :measure (gl-object-count x)
    :returns (new-x gl-bfr-object-p
                    :hints ('(:in-theory (enable gl-bfr-object-p))))
    :verify-guards nil
    (mbe :logic
         (gl-object-case x
           :g-concrete (g-concrete x.val)
           :g-boolean (g-boolean (bfr-fix x.bool))
           :g-integer (g-integer (bfr-list-fix x.bits))
           :g-ite (g-ite (gl-bfr-object-fix x.test)
                         (gl-bfr-object-fix x.then)
                         (gl-bfr-object-fix x.else))
           :g-apply (g-apply x.fn (gl-bfr-objectlist-fix x.args))
           :g-var (g-var x.name)
           :g-cons (g-cons (gl-bfr-object-fix x.car)
                           (gl-bfr-object-fix x.cdr)))
         :exec x))
  (define gl-bfr-objectlist-fix ((x gl-bfr-objectlist-p)
                               &optional (logicman 'logicman))
    :measure (gl-objectlist-count x)
    :returns (new-x gl-bfr-objectlist-p
                    :hints ('(:in-theory (enable gl-bfr-objectlist-p))))
    (if (atom x)
        nil
      (cons (gl-bfr-object-fix (car x))
            (gl-bfr-objectlist-fix (cdr x)))))
  ///
  (defthm-gl-bfr-object-fix-flag gl-bfr-object-fix-when-gl-bfr-object-p
    (defthm gl-bfr-object-fix-when-gl-bfr-object-p
      (implies (gl-bfr-object-p x)
               (equal (gl-bfr-object-fix x) x))
      :hints ('(:expand ((gl-bfr-object-p x)
                         (gl-bfr-object-fix x))))
      :flag gl-bfr-object-fix)
    (defthm gl-bfr-objectlist-fix-when-gl-bfr-objectlist-p
      (implies (gl-bfr-objectlist-p x)
               (equal (gl-bfr-objectlist-fix x) x))
      :hints ('(:expand ((gl-bfr-objectlist-p x)
                         (gl-bfr-objectlist-fix x))))
      :flag gl-bfr-objectlist-fix))

  (defret-mutual gl-object-p-of-gl-bfr-object-fix
    (defret gl-object-p-of-gl-bfr-object-fix
      (gl-object-p new-x)
      :fn gl-bfr-object-fix)
    (defret gl-objectlist-p-of-gl-bfr-objectlist-fix
      (gl-objectlist-p new-x)
      :fn gl-bfr-objectlist-fix))

  (verify-guards gl-bfr-object-fix-fn
    :hints('(:expand ((gl-bfr-object-p x)
                      (gl-bfr-objectlist-p x))))))


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

(fty::defprod gl-env
  ((obj-alist obj-alist)
   (bfr-vals))
  :layout :tree)

(define gobj-bfr-eval ((x bfr-p)
                       (env gl-env-p)
                       &optional (logicman 'logicman))
  :returns bool
  (bfr-eval x (gl-env->bfr-vals env))
  ///
  (defthm gobj-bfr-eval-consts
    (and (equal (gobj-bfr-eval t env) t)
         (equal (gobj-bfr-eval nil env) nil)))

  (defthm gobj-bfr-eval-of-bfr-fix
    (equal (gobj-bfr-eval (bfr-fix x) env)
           (gobj-bfr-eval x env)))
  
  (defthm gobj-bfr-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-p x old))
             (equal (gobj-bfr-eval x env new)
                    (gobj-bfr-eval x env old))))

  (defthm gobj-bfr-eval-of-bfr-var
    (implies (bfr-varname-p n)
             (equal (gobj-bfr-eval (bfr-var n) env)
                    (bfr-lookup n (gl-env->bfr-vals env)))))

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
    :fn bfr-ite))


(define gobj-bfr-list-eval ((x bfr-listp) (env gl-env-p) &optional (logicman 'logicman))
  :returns bools
  (if (atom x)
      nil
    (cons (gobj-bfr-eval (car x) env)
          (gobj-bfr-list-eval (cdr x) env)))
  ///
  (defthm gobj-bfr-list-eval-of-gobj-bfr-list-fix
    (equal (gobj-bfr-list-eval (bfr-list-fix x) env)
           (gobj-bfr-list-eval x env)))

  (defthm gobj-bfr-list-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-listp x old))
             (equal (gobj-bfr-list-eval x env new)
                    (gobj-bfr-list-eval x env old))))

  (fty::deffixequiv gobj-bfr-list-eval :args ((x true-listp) (env gl-env-p))))



  
    
(encapsulate
  (((base-gl-object-apply * *) => *
    :formals (fn args)
    :guard (and (symbolp fn)
                (true-listp args))))

  (local (defun base-gl-object-apply (fn args)
           (Declare (Xargs :guard (and (Symbolp fn)
                                       (true-listp args)))
                    (ignore fn args))
           nil))

  (fty::deffixequiv base-gl-object-apply :args ((fn symbolp) (args true-listp))))

(define gobj-var-lookup (name (env gl-env-p))
  :prepwork ((local (defthm consp-of-assoc-when-obj-alist-p
                      (implies (obj-alist-p x)
                               (iff (consp (assoc key x))
                                    (assoc key x))))))
  (cdr (assoc-equal name (gl-env->obj-alist env))))

(defines base-gl-object-eval
  (define base-gl-object-eval ((x gl-bfr-object-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
    :measure (gl-object-count x)
    :verify-guards nil
    :returns (val)
    (gl-object-case x
      :g-concrete x.val
      :g-boolean (gobj-bfr-eval x.bool env)
      :g-integer (bools->int (gobj-bfr-list-eval x.bits env))
      :g-ite (if (base-gl-object-eval x.test env)
                 (base-gl-object-eval x.then env)
               (base-gl-object-eval x.else env))
      :g-apply (base-gl-object-apply x.fn (base-gl-objectlist-eval x.args env))
      :g-var (gobj-var-lookup x.name env)
      :g-cons (cons (base-gl-object-eval x.car env)
                    (base-gl-object-eval x.cdr env))))
  (define base-gl-objectlist-eval ((x gl-bfr-objectlist-p)
                                   (env gl-env-p)
                                   &optional (logicman 'logicman))
    :measure (gl-objectlist-count x)
    :returns (vals true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (cons (base-gl-object-eval (car x) env)
            (base-gl-objectlist-eval (cdr x) env))))
  ///
  (verify-guards base-gl-object-eval-fn)

  (defret-mutual base-gl-object-eval-of-gl-bfr-object-fix
    (defret base-gl-object-eval-of-gl-bfr-object-fix
      (equal (base-gl-object-eval (gl-bfr-object-fix x) env)
             val)
      :hints ('(:expand ((gl-bfr-object-fix x))))
      :fn base-gl-object-eval)
    (defret base-gl-objectlist-eval-of-gl-bfr-object-fix
      (equal (base-gl-objectlist-eval (gl-bfr-objectlist-fix x) env)
             vals)
      :hints ('(:expand ((gl-bfr-objectlist-fix x))))
      :fn base-gl-objectlist-eval))

  (defret-mutual base-gl-object-eval-of-gl-object-fix
    (defret base-gl-object-eval-of-gl-object-fix
      (equal (base-gl-object-eval (gl-object-fix x) env)
             val)
      :hints ('(:expand ((gl-object-fix x))
                :in-theory (e/d (base-gl-object-eval))))
      :fn base-gl-object-eval)
    (defret base-gl-objectlist-eval-of-gl-object-fix
      (equal (base-gl-objectlist-eval (gl-objectlist-fix x) env)
             vals)
      :hints ('(:expand ((gl-objectlist-fix x)
                         (:free (a b) (base-gl-objectlist-eval (cons a b) env))
                         (base-gl-objectlist-eval nil env)
                         (base-gl-objectlist-eval x env))))
      :fn base-gl-objectlist-eval))

  (defthm-base-gl-object-eval-flag
    (defthm base-gl-object-eval-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-object-p x old))
               (equal (base-gl-object-eval x env new)
                      (base-gl-object-eval x env old)))
      :hints ('(:expand ((:free (logicman) (base-gl-object-eval x env logicman))
                         (gl-bfr-object-p x old))))
      :flag base-gl-object-eval)
    (defthm base-gl-objectlist-eval-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-objectlist-p x old))
               (equal (base-gl-objectlist-eval x env new)
                      (base-gl-objectlist-eval x env old)))
      :hints ('(:expand ((:free (logicman) (base-gl-objectlist-eval x env logicman))
                         (gl-bfr-objectlist-p x old))))
      :flag base-gl-objectlist-eval)
    :hints (("goal" :induct (base-gl-object-eval-flag flag x env old))))

  (defthm base-gl-object-eval-when-g-concrete
    (implies (gl-object-case x :g-concrete)
             (equal (base-gl-object-eval x env)
                    (g-concrete->val x)))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-concrete
    (equal (base-gl-object-eval (g-concrete val) env)
           val))

  (defthm base-gl-object-eval-when-g-boolean
    (implies (gl-object-case x :g-boolean)
             (equal (base-gl-object-eval x env)
                    (gobj-bfr-eval (g-boolean->bool x) env)))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-boolean
    (equal (base-gl-object-eval (g-boolean bool) env)
           (gobj-bfr-eval bool env)))

  (defthm base-gl-object-eval-when-g-integer
    (implies (gl-object-case x :g-integer)
             (equal (base-gl-object-eval x env)
                    (bools->int (gobj-bfr-list-eval (g-integer->bits x) env))))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-integer
    (equal (base-gl-object-eval (g-integer bits) env)
           (bools->int (gobj-bfr-list-eval bits env))))

  (defthm base-gl-object-eval-when-g-ite
    (implies (gl-object-case x :g-ite)
             (equal (base-gl-object-eval x env)
                    (if (base-gl-object-eval (g-ite->test x) env)
                        (base-gl-object-eval (g-ite->then x) env)
                      (base-gl-object-eval (g-ite->else x) env))))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-ite
    (equal (base-gl-object-eval (g-ite test then else) env)
           (if (base-gl-object-eval test env)
               (base-gl-object-eval then env)
             (base-gl-object-eval else env))))

  (defthm base-gl-object-eval-when-g-apply
    (implies (gl-object-case x :g-apply)
             (equal (base-gl-object-eval x env)
                    (base-gl-object-apply (g-apply->fn x)
                                          (base-gl-objectlist-eval (g-apply->args x) env))))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-apply
    (equal (base-gl-object-eval (g-apply fn args) env)
           (base-gl-object-apply fn
                                 (base-gl-objectlist-eval args env))))

  (defthm base-gl-object-eval-when-g-var
    (implies (gl-object-case x :g-var)
             (equal (base-gl-object-eval x env)
                    (gobj-var-lookup (g-var->name x) env)))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-var
    (equal (base-gl-object-eval (g-var name) env)
           (gobj-var-lookup name env)))

  (defthm base-gl-object-eval-when-g-cons
    (implies (gl-object-case x :g-cons)
             (equal (base-gl-object-eval x env)
                    (cons (base-gl-object-eval (g-cons->car x) env)
                          (base-gl-object-eval (g-cons->cdr x) env))))
    :hints (("goal" :expand ((base-gl-object-eval x env)))))

  (defthm base-gl-object-eval-of-g-cons
    (equal (base-gl-object-eval (g-cons car cdr) env)
           (cons (base-gl-object-eval car env)
                 (base-gl-object-eval cdr env)))))


(defines gl-object-depends-on
  (define gl-object-depends-on ((v bfr-varname-p)
                                (x gl-bfr-object-p)
                               &optional ((logicman logicman-nvars-ok) 'logicman))
    :measure (gl-object-count x)
    :verify-guards nil
    :returns (val booleanp :rule-classes :type-prescription)
    (gl-object-case x
      :g-concrete nil
      :g-boolean (bfr-depends-on v x.bool)
      :g-integer (bfr-list-depends-on v x.bits)
      :g-ite (or (gl-object-depends-on v x.test)
                 (gl-object-depends-on v x.then)
                 (gl-object-depends-on v x.else))
      :g-apply (gl-objectlist-depends-on v x.args)
      :g-var nil
      :g-cons (or (gl-object-depends-on v x.car)
                  (gl-object-depends-on v x.cdr))))
  (define gl-objectlist-depends-on ((v bfr-varname-p)
                                   (x gl-bfr-objectlist-p)
                                   &optional ((logicman logicman-nvars-ok) 'logicman))
    :measure (gl-objectlist-count x)
    :returns (vals booleanp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (or (gl-object-depends-on v (car x))
          (gl-objectlist-depends-on v (cdr x)))))
  ///
  (verify-guards gl-object-depends-on-fn)

  (defret-mutual gl-object-depends-on-of-gl-bfr-object-fix
    (defret gl-object-depends-on-of-gl-bfr-object-fix
      (equal (gl-object-depends-on v (gl-bfr-object-fix x))
             val)
      :hints ('(:expand ((gl-bfr-object-fix x))))
      :fn gl-object-depends-on)
    (defret gl-objectlist-depends-on-of-gl-bfr-object-fix
      (equal (gl-objectlist-depends-on v (gl-bfr-objectlist-fix x))
             vals)
      :hints ('(:expand ((gl-bfr-objectlist-fix x))))
      :fn gl-objectlist-depends-on))

  (defret-mutual gl-object-depends-on-of-gl-object-fix
    (defret gl-object-depends-on-of-gl-object-fix
      (equal (gl-object-depends-on v (gl-object-fix x))
             val)
      :hints ('(:expand ((gl-object-fix x))
                :in-theory (e/d (gl-object-depends-on))))
      :fn gl-object-depends-on)
    (defret gl-objectlist-depends-on-of-gl-object-fix
      (equal (gl-objectlist-depends-on v (gl-objectlist-fix x))
             vals)
      :hints ('(:expand ((gl-objectlist-fix x)
                         (:free (a b) (gl-objectlist-depends-on v (cons a b)))
                         (gl-objectlist-depends-on v nil)
                         (gl-objectlist-depends-on v x))))
      :fn gl-objectlist-depends-on))

  (defthm-gl-object-depends-on-flag
    (defthm gl-object-depends-on-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-object-p x old)
                    (bfr-varname-p v old))
               (equal (gl-object-depends-on v x new)
                      (gl-object-depends-on v x old)))
      :hints ('(:expand ((:free (logicman) (gl-object-depends-on v x logicman))
                         (gl-bfr-object-p x old))))
      :flag gl-object-depends-on)
    (defthm gl-objectlist-depends-on-of-logicman-extension
      (implies (and (bind-logicman-extension new old)
                    (gl-bfr-objectlist-p x old)
                    (bfr-varname-p v old))
               (equal (gl-objectlist-depends-on v x new)
                      (gl-objectlist-depends-on v x old)))
      :hints ('(:expand ((:free (logicman) (gl-objectlist-depends-on v x logicman))
                         (gl-bfr-objectlist-p x old))))
      :flag gl-objectlist-depends-on)
    :hints (("goal" :induct (gl-object-depends-on-flag flag v x old))))

  (defthm gl-object-depends-on-when-g-concrete
    (implies (gl-object-case x :g-concrete)
             (not (gl-object-depends-on v x)))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-concrete
    (not (gl-object-depends-on v (g-concrete val))))

  (defthm gl-object-depends-on-when-g-boolean
    (implies (gl-object-case x :g-boolean)
             (equal (gl-object-depends-on v x)
                    (bfr-depends-on v (g-boolean->bool x))))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-boolean
    (equal (gl-object-depends-on v (g-boolean bool))
           (bfr-depends-on v bool)))

  (defthm gl-object-depends-on-when-g-integer
    (implies (gl-object-case x :g-integer)
             (equal (gl-object-depends-on v x)
                    (bfr-list-depends-on v (g-integer->bits x))))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-integer
    (equal (gl-object-depends-on v (g-integer bits))
           (bfr-list-depends-on v bits)))

  (defthm gl-object-depends-on-when-g-ite
    (implies (gl-object-case x :g-ite)
             (equal (gl-object-depends-on v x)
                    (or (gl-object-depends-on v (g-ite->test x))
                        (gl-object-depends-on v (g-ite->then x))
                        (gl-object-depends-on v (g-ite->else x)))))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-ite
    (equal (gl-object-depends-on v (g-ite test then else))
           (or (gl-object-depends-on v test)
               (gl-object-depends-on v then)
               (gl-object-depends-on v else))))

  (defthm gl-object-depends-on-when-g-apply
    (implies (gl-object-case x :g-apply)
             (equal (gl-object-depends-on v x)
                    (gl-objectlist-depends-on v (g-apply->args x))))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-apply
    (equal (gl-object-depends-on v (g-apply fn args))
           (gl-objectlist-depends-on v args)))

  (defthm gl-object-depends-on-when-g-var
    (implies (gl-object-case x :g-var)
             (not (gl-object-depends-on v x)))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-var
    (not (gl-object-depends-on v (g-var name))))

  (defthm gl-object-depends-on-when-g-cons
    (implies (gl-object-case x :g-cons)
             (equal (gl-object-depends-on v x)
                    (or (gl-object-depends-on v (g-cons->car x))
                        (gl-object-depends-on v (g-cons->cdr x)))))
    :hints (("goal" :expand ((gl-object-depends-on v x)))))

  (defthm gl-object-depends-on-of-g-cons
    (equal (gl-object-depends-on v (g-cons car cdr))
           (or (gl-object-depends-on v car)
               (gl-object-depends-on v cdr)))))




                                   
      


