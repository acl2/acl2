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

(include-book "centaur/aignet/construction" :dir :system)
(include-book "centaur/aignet/ipasir" :dir :system)
(include-book "bvar-db")
(include-book "gl-object")
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/aig/aig-vars" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(local (include-book "theory"))

(std::defenum gl-bfr-mode-p
  (t nil :aignet))

(defconst *logicman-fields*
  '((aignet :type aignet::aignet)
    (aignet-refcounts :type aignet::aignet-refcounts)
    (strash :type aignet::strash)
    (ipasir :type ipasir::ipasir)
    (sat-lits :type aignet::sat-lits)
    (bvar-db :type bvar-db)
    (mode :type (satisfies gl-bfr-mode-p))))

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
             (logicman-extension-p new old))))

(std::deflist nat-listp (x) (natp x) :already-definedp t :true-listp t)

(define aig-p (x)
  (cond ((atom x) (or (booleanp x) ;; const
                      (natp x))) ;; var
        ((eq (cdr x) 'nil) (aig-p (car x)))
        ((eq (car x) 'nil) nil)
        (t (and (aig-p (car x))
                (aig-p (cdr x)))))
  ///
  (defthm nat-listp-aig-vars-when-aig-p
    (iff (nat-listp (acl2::aig-vars x))
         (aig-p x))
    :hints(("Goal" :in-theory (enable acl2::aig-atom-p))))

  (local (defthm aig-p-is-nat-listp-aig-vars
           (iff (aig-p x)
                (nat-listp (acl2::aig-vars x)))))
  (local (in-theory (disable nat-listp-aig-vars-when-aig-p)))

  (local (defun nat-listp-badguy (x)
           (if (atom x)
               nil
             (if (natp (car x))
                 (nat-listp-badguy (cdr x))
               (car x)))))

  (local (defthm nat-listp-when-nat-listp-badguy-not-member
           (implies (and (not (member (nat-listp-badguy x) x))
                         (true-listp x))
                    (nat-listp x))))

  (local (defthm not-natp-of-nat-listp-badguy
           (not (natp (nat-listp-badguy x)))
           :rule-classes :type-prescription))

  (local (defthm nat-listp-implies-not-member-of-non-nat
           (implies (and (nat-listp x)
                         (not (natp k)))
                    (not (member k x)))))

  (local (defthm member-aig-vars-aig-and
           (implies (and (not (member v (acl2::aig-vars x)))
                         (not (member v (acl2::aig-vars y))))
                    (not (member v (acl2::aig-vars (acl2::aig-and x y)))))
           :hints (("goal" :use ((:instance acl2::member-aig-vars-aig-and
                                  (v v) (x x)))
                    :in-theory (e/d (set::in-to-member)
                                    (acl2::member-aig-vars-aig-and))))))

  (defthm aig-p-of-aig-not
    (implies (aig-p x)
             (aig-p (acl2::aig-not x))))

  (defthm aig-p-of-aig-and
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-and x y))))

  (local (in-theory (disable aig-p-is-nat-listp-aig-vars)))

  (defthm aig-p-of-aig-or
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-or x y)))
    :hints(("Goal" :in-theory (enable acl2::aig-or))))

  (defthm aig-p-of-aig-xor
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-xor x y)))
    :hints(("Goal" :in-theory (enable acl2::aig-xor))))

  (defthm aig-p-of-aig-ite
    (implies (and (aig-p x) (aig-p y) (aig-p z))
             (aig-p (acl2::aig-ite x y z)))
    :hints(("Goal" :in-theory (enable acl2::aig-ite)))))

(define aig-fix ((x aig-p))
  :returns (new-x aig-p :hints(("Goal" :in-theory (enable aig-p))))
  :verify-guards nil
  (mbe :logic (cond ((atom x) (and (or (booleanp x)
                                       (natp x))
                                   x))
                    ((eq (cdr x) nil)
                     (cons (aig-fix (car x)) nil))
                    ((eq (car x) nil) nil)
                    (t (b* ((car (aig-fix (car x)))
                            (cdr (aig-fix (cdr x))))
                         (and car cdr (cons car cdr)))))
       :exec x)
  ///
  (defthm aig-fix-when-aig-p
    (implies (aig-p x)
             (equal (aig-fix x) x))
    :hints(("Goal" :in-theory (enable aig-p))))

  (verify-guards aig-fix :hints(("Goal" :in-theory (enable aig-p)))))


(define logicman-bfr-p (x &optional (logicman 'logicman))
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
  (defthm logicman-bfr-p-of-constants
    (and (logicman-bfr-p t)
         (logicman-bfr-p nil)))

  (def-updater-independence-thm logicman-bfr-p-updater-independence
    (implies (and (equal (logicman-get :aignet new)
                         (logicman-get :aignet old))
                  (equal (logicman-get :mode new)
                         (logicman-get :mode old)))
             (equal (logicman-bfr-p x new) (logicman-bfr-p x old))))

  (defthm logicman-bfr-p-when-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-bfr-p x old))
             (logicman-bfr-p x new))
    :hints(("Goal" :in-theory (enable logicman-extension-p)))))

(define aignet-lit->bfr ((x satlink::litp) &optional (logicman 'logicman))
  :guard (stobj-let ((aignet (logicman->aignet logicman)))
                    (ans)
                    (aignet::fanin-litp x aignet)
                    ans)
  :returns (bfr logicman-bfr-p :hyp (eq (bfr-mode) :aignet)
                :hints(("Goal" :in-theory (enable logicman-bfr-p))))
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


(define bfr-fix ((x logicman-bfr-p) &optional (logicman 'logicman))
  :returns (new-x logicman-bfr-p)
  :prepwork ((local (in-theory (enable logicman-bfr-p aignet-lit->bfr))))
  (mbe :logic (bfr-case
                :aig (aig-fix x)
                :bdd (acl2::ubdd-fix x)
                :aignet
                (if (booleanp x)
                    x
                  (aignet-lit->bfr x)))
       :exec x)
  ///
  (std::defret bfr-fix-when-logicman-bfr-p
    (implies (logicman-bfr-p x)
             (equal new-x x))))

(define bfr->aignet-lit ((x logicman-bfr-p) &optional (logicman 'logicman))
  :guard (eq (bfr-mode) :aignet)
  :returns (lit (implies (eq (bfr-mode) :aignet)
                         (aignet::aignet-litp lit (logicman->aignet logicman))))
  :prepwork ((local (in-theory (enable bfr-fix aignet-lit->bfr logicman-bfr-p))))
  (b* ((x (bfr-fix x)))
    (case x
      ((nil) 0)
      ((t) 1)
      (t (satlink::lit-fix x))))
  ///
  (defthm bfr->aignet-lit-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-bfr-p x old))
             (equal (bfr->aignet-lit x new)
                    (bfr->aignet-lit x old))))

  (defthm bfr->aignet-lit-of-aignet-lit->bfr
    (implies (equal (bfr-mode) :aignet)
             (equal (bfr->aignet-lit (aignet-lit->bfr x))
                    (aignet::aignet-lit-fix x (logicman->aignet logicman))))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr)))))



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
             :in-theory (enable aignet-litp aignet-idp)))))



(define bfr-eval ((x logicman-bfr-p) env &optional (logicman 'logicman))
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
    :bdd (acl2::eval-bdd x env)
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
                  (logicman-bfr-p x old))
             (equal (bfr-eval x env new)
                    (bfr-eval x env old)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable logicman-extension-p))))))





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
  (defthm logicman-nvars-ok-implies
    (implies (and (logicman-nvars-ok)
                  (equal (bfr-mode) :aignet))
             (equal (aignet::stype-count :pi (logicman->aignet logicman))
                    (next-bvar$a (logicman->bvar-db logicman)))))
  (def-updater-independence-thm logicman-nvars-ok-updater-independence
    (implies (and (logicman-nvars-ok old)
                  (equal (logicman->mode new)
                         (logicman->mode old))
                  (equal (next-bvar (logicman->bvar-db new))
                         (next-bvar (logicman->bvar-db old)))
                  (equal (aignet::num-ins (logicman->aignet new))
                         (aignet::num-ins (logicman->aignet old))))
             (logicman-nvars-ok new))))
                    
   
(define bfr-nvars (&optional (logicman 'logicman))
  :guard (logicman-nvars-ok)
  :enabled t
  (mbe :logic (non-exec (next-bvar$a (logicman->bvar-db logicman)))
       :exec (stobj-let
              ((bvar-db (logicman->bvar-db logicman)))
              (nvars)
              (next-bvar bvar-db)
              nvars)))



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
    :rule-classes :forward-chaining))
             


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
    :aignet (bool-fix (cdr (hons-assoc-equal (lnfix n) env)))))

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


(define bfr-var ((n bfr-varname-p) &optional ((logicman logicman-nvars-ok) 'logicman))
  :returns (bfr logicman-bfr-p :hints((and stable-under-simplificationp
                                  '(:in-theory (enable logicman-bfr-p aig-p)))))
  :guard-hints (("goal" :in-theory (enable bfr-varname-p aignet::aignet-litp)))
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
                      (aignet::id-eval (aignet::node-count (aignet::lookup-stype n :pi aignet))
                                       invals regvals aignet))))))

  (defthm bfr-var-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-varname-p n old))
             (equal (bfr-var n new)
                    (bfr-var n old)))
    :hints(("Goal" :in-theory (enable logicman-extension-p aignet-lit->bfr
                                      bfr-varname-p
                                      aignet::aignet-litp)))))




  
  
