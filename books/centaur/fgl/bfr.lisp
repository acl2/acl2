; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "std/util/defenum" :dir :system)
(include-book "nat-var-aig")
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/satlink/litp" :dir :system)
(include-book "gl-object")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defsection bfr
  :parents (reference)
  :short "An abstraction of the <b>B</b>oolean <b>F</b>unction
<b>R</b>epresentation used by GL."

  :long "<p>GL was originally designed to operate on @(see ubdds), with support
for hons-@(see aig)s and @(see aignet) added later.  To avoid redoing a lot of
proof work, a small level of indirection was added.</p>

<p>The particular Boolean function representation that we are using at any
particular time is governed by @(see bfr-mode), and operations like @(see
bfr-and) allow us to construct new function nodes using whatever the current
representation is.</p>

<p>To support aignets, it is important for BFRs to be well-formed,
i.e. literals whose node index is in bounds for the current aignet.  So we
also use a @(see bfrstate) object which simultaneously tracks the bfr-mode and
current bound.</p>")

(local (xdoc::set-default-parents bfr))

(std::defenum bfr-mode-p (0 1 2))

(defxdoc bfr-mode
  :short "Determines whether GL is using @(see ubdds), hons-@(see aig)s, or @(see
          aignet) literals as its Boolean function representation."
  :long "<p>This is encoded using the numbers 0, 1, 2 so that it can be packed
into a @(see bfrstate) object efficiently.  0 means aignet, 1 means UBDDs, and
2 means hons-AIGs.  But please use @(see bfr-mode-case) instead of explicitly
checking for these values.</p>")

;; Translates bfr mode keyword :aig, :bdd, :aignet to the correct index.
(defmacro bfrmode (x)
  (case x
    (:aignet 0)
    (:bdd 1)
    (:aig 2)
    (otherwise (er hard? 'bfrmode "Bad bfrmode keyword: ~x0~%" x))))

(defsection bfr-mode-case
  :parents (bfr-mode)
  :short "Choose behavior based on a bfr-mode object"
  :long "<p>Usage:</p>

@({

     ;; Different cases for all modes, explicit bfr-mode supplied
     (bfr-mode-case my-bfr-mode
                    :aig aig-code
                    :bdd bdd-code
                    :aignet aignet-code)

     ;; Different case only for one mode with default for others,
     ;; implicitly uses the bfr-mode variable
     (bfr-mode-case :aig aig-code
                    :otherwise default-code)

})

<h4>Notes</h4>

<p>The bfr-mode argument may be left out, in which case the first argument must
be a keyword and the bfr-mode used is the variable @('bfr-mode').</p>

<p>The keyword arguments accepted are @(':aig'), @(':bdd'), @(':aignet'), and
@(':otherwise'), but you can't use all four in one form.</p>"

  (defmacro bfr-mode-case1 (mode &key (aig 'nil aig-p)
                                 (bdd 'nil bdd-p)
                                 (aignet 'nil aignet-p)
                                 (otherwise 'nil otherwise-p))
    (if (and aig-p bdd-p aignet-p otherwise-p)
        (er hard? 'bfr-mode-case "Provided :otherwise along with all three cases :aig, :bdd, :aignet.")
      `(case (bfr-mode-fix ,mode)
         ,@(and bdd-p `((1 ,bdd)))
         ,@(and aignet-p `((0 ,aignet)))
         ,@(and aig-p
                (if (and bdd-p aignet-p)
                    `((t ,aig))
                  `((2 ,aig))))
         ,@(and otherwise-p
                `((t ,otherwise))))))

  (defun bfr-mode-case-fn (args)
    (if (keywordp (car args))
        `(bfr-mode-case1 bfr-mode . ,args)
      `(bfr-mode-case1 ,(car args) . ,(cdr args))))

  (defmacro bfr-mode-case (&rest args)
    (bfr-mode-case-fn args)))

(defsection bfr-mode-is
  :short "Check the current bfr-mode."
  :long "<p>Just returns T if the given bfr-mode matches the keyword.
Like @(see bfr-mode-case), the bfr-mode argument is optional.  Usage:</p>

@({
 ;; Use the bfr-mode variable. T if aig mode, NIL if aignet or bdd.
 (bfr-mode-case :aig) 

 ;; Use the given bfr-mode object. T if bdd mode, NIL if aignet or aig.
 (bfr-mode-case :bdd my-bfr-mode)
})
"

  (defun bfr-mode-is-fn (key mode)
    (cond ((eq key :aignet) `(eql (bfr-mode-fix ,mode) 0))
          ((eq key :bdd) `(eql (bfr-mode-fix ,mode) 1))
          ((eq key :aig) `(eql (bfr-mode-fix ,mode) 2))
          (t (er hard? 'bfr-mode-is "Bad key: ~x0" key))))

  (defmacro bfr-mode-is (key &optional (mode 'bfr-mode))
    (bfr-mode-is-fn key mode)))


(define bfrstate-p (x)
  :parents (bfrstate)
  :short "Recognizer for a @(see bfrstate) object."
  (and (natp x)
       (bfr-mode-p (logand 3 x)))
  ///
  (defthm bfrstate-p-compound-recognizer
    (implies (bfrstate-p x)
             (natp x))
    :rule-classes :compound-recognizer))

  
(local (defthm unsigned-byte-p-when-bfr-mode-p
         (implies (bfr-mode-p x)
                  (unsigned-byte-p 2 x))
         :hints(("Goal" :in-theory (enable bfr-mode-p)))))

(define bfrstate ((mode bfr-mode-p)
                  (bound natp))
  :parents (bfr)
  :short "Object encoding the @(see bfr-mode) and current node index bound, if
          using AIGNET mode."
  :long "<p>For a @(see bfr) object to be well-formed, we need to know, first,
whether we're operating in BDD, AIG, or AIGNET mode, and second, if in AIGNET
mode, the bound on node indices.  This type encodes the @(see bfr-mode) in the
lower 2 bits and the node index bound in the upper bits of an integer.</p>"
  :prepwork ((local (in-theory (enable bfrstate-p))))
  :returns (bfrstate bfrstate-p :rule-classes (:rewrite :type-prescription))
  (logior (ash (lnfix bound) 2) (bfr-mode-fix mode)))

(define bfrstate-fix ((x bfrstate-p))
  :parents (bfrstate)
  :short "Fixing function for @(see bfrstate) objects."
  :prepwork ((local (in-theory (enable bfrstate-p))))
  :returns (new-x bfrstate-p)
  :verify-guards nil
  :inline t
  (mbe :logic (logior (logand -4 (nfix x)) (bfr-mode-fix (logand 3 (nfix x))))
       :exec x)
  ///
  (local (defthm logior-loghead-logsquash
           (equal (logior (loghead n x) (bitops::logsquash n x))
                  (ifix x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-redefs)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable bitops::equal-logcons-strong))))))

  (defthm bfrstate-fix-when-bfrstate-p
    (implies (bfrstate-p x)
             (equal (bfrstate-fix x) x))
    :hints(("Goal" :in-theory (enable bfrstate-p))))

  (verify-guards bfrstate-fix$inline
    :hints (("goal" :use bfrstate-fix-when-bfrstate-p
             :in-theory (disable bfrstate-fix-when-bfrstate-p))))

  (fty::deffixtype bfrstate :pred bfrstate-p :fix bfrstate-fix :equiv bfrstate-equiv
    :define t :forward t))

(define bfrstate->mode ((x bfrstate-p))
  :parents (bfrstate)
  :short "Access the @(see bfr-mode) field of a @(see bfrstate) object."
  :returns (mode bfr-mode-p :hints(("Goal" :in-theory (enable bfrstate-fix))))
  :inline t
  (logand 3 (bfrstate-fix x))
  ///
  (defthm bfrstate->mode-of-bfrstate
    (equal (bfrstate->mode (bfrstate mode bound))
           (bfr-mode-fix mode))
    :hints(("Goal" :in-theory (enable bfrstate bfrstate-fix)))))


(define bfrstate->bound ((x bfrstate-p))
  :parents (bfrstate)
  :short "Access the node index bound field of a @(see bfrstate) object."
  :returns (bound natp :rule-classes :type-prescription :hints(("Goal" :in-theory (enable bfrstate-fix))))
  :inline t
  (ash (bfrstate-fix x) -2)
  ///
  (defthm bfrstate->bound-of-bfrstate
    (equal (bfrstate->bound (bfrstate mode bound))
           (nfix bound))
    :hints(("Goal" :in-theory (enable bfrstate bfrstate-fix)))))

(defsection bfrstate-fix-redef
  (local (defthm ash-logtail-is-logsquash
           (implies (natp n)
                    (equal (ash (logtail n x) n)
                           (bitops::logsquash n x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-redefs)))))
  (defthmd bfrstate-fix-redef
    (equal (bfrstate-fix x)
           (bfrstate (bfrstate->mode x) (bfrstate->bound x)))
    :hints(("Goal" :in-theory (enable bfrstate-fix bfrstate bfrstate->mode bfrstate->bound)))))


(defsection bfrstate-case
  :short "Choose behavior based on the current @(see bfr) mode of the bfrstate"
  :long "<p>Same as @(see bfr-mode-case), but gets the bfr mode from a bfrstate
object.  If no bfrstate object is supplied (i.e., if the first argument is a
keyword), the variable named @('bfrstate') is implicitly used.</p>"

  (defun bfrstate-case-fn (args)
    (if (keywordp (car args))
        `(bfr-mode-case (bfrstate->mode bfrstate). ,args)
      `(bfr-mode-case (bfrstate->mode ,(car args)) . ,(cdr args))))

  (defmacro bfrstate-case (&rest args)
    (bfrstate-case-fn args)))


(defsection bfrstate-mode-is
  :short "Check the current bfr-mode of a bfrstate object."
  :long "<p>Same as @(see bfr-mode-is), but gets the bfr mode object from a
bfrstate object.  If no bfrstate object is supplied, the variable named
@('bfrstate') is implicitly used.</p>"
  (defun bfrstate-mode-is-fn (key bfrstate)
    `(bfr-mode-is ,key (bfrstate->mode ,bfrstate)))

  (defmacro bfrstate-mode-is (key &optional (bfrstate 'bfrstate))
    (bfrstate-mode-is-fn key bfrstate)))

;; (defsection bfrstate>=-bind
;;   :parents (bfrstate)
;;   :short "Binding scheme for rewriting based on the bfrstate>= relation."
;;   :long "<p>We want to have a rewriting scheme for bfrstates similar to the one
;; for aignet extensions, whereby if a bfrstate is modified in a way that
;; preserves the mode and may only increase the bound, then we can in some cases
;; rewrite that modification away.</p>

;; <p>What we'd like to be able to do is have simple rewrite rules like this:</p>

;; @({
;;  (implies (and (bfrstate>=-bind new old)
;;                (bfr-p x old))
;;           (bfr-p x new))
;;  })

;; <p>Where bfrstate>=-bind allows us to bind old based on the syntax of new.</p>

;; <p>This is going to be a little more complicated for bfrstates than for
;; aignets, because we're generally going to be pulling a bfrstate out of a
;; logicman.  We'd like to be able to just prove something like this:</p>

;; @({
;;  (implies (logicman-extension-p lnew lold)
;;           (bfrstate>= (logicman-bfrstate lnew) (logicman-bfrstate lold)))
;;  })

;; <p>and use our rules about finding a logicman extension binding to find lold
;; based on lnew, whenever the syntax of new is @('(logicman-bfrstate lnew)').</p>

;; <p>To complicate things, we'd like to define bfrstate>=-bind before the
;; relevant logicman stuff is in place, so we need some way to plug that stuff in
;; after the fact.  So what we'll do for now is leave it as an attachable
;; function; then later we can add the right mechanisms.</p>"

;;   (defmacro bfrstate>=-bind (new old)
;;     `(and (bind-free (bfrstate>=-bind-fn ,new ',old mfc state))
;;           (bfrstate>= ,new ,old)))

;;   (encapsulate
;;     (((bfrstate>=-bind-fn * * * state) => *
;;       :formals (new old mfc state)
;;       :guard (symbolp old)))
;;     (local (defun bfrstate>=-bind-fn (new old mfc state)
;;              (declare (xargs :guard (symbolp old))
;;                       (ignorable new old mfc state))
;;              `((,old . ,new)))))

;;   (define bfrstate>=-bind-fn-base (new
;;                                    (old symbolp)
;;                                    mfc state)
;;     (declare (ignore old mfc state))
;;     '((some-unused-variable . 'nil))))

             
     


(define bfrstate>= ((x bfrstate-p) (y bfrstate-p))
  (and (eql (bfrstate->mode x) (bfrstate->mode y))
       (b* ((bfr-mode (bfrstate->mode x)))
         (or (not (bfr-mode-is :aignet))
             (>= (bfrstate->bound x) (bfrstate->bound y)))))
  ///
  (defthm bfrstate>=-self
    (bfrstate>= x x))

  (defthmd bfrstate>=-implies-mode
    (implies (bfrstate>= x y)
             (equal (bfrstate->mode x)
                    (bfrstate->mode y))))

  (defthmd bfrstate>=-implies-bound
    (implies (and (bfrstate>= x y)
                  (b* ((bfr-mode (bfrstate->mode x)))
                    (bfr-mode-is :aignet)))
             (>= (bfrstate->bound x) (bfrstate->bound y)))
    :rule-classes (:rewrite :linear)))


(define bfr-p (x &optional ((bfrstate bfrstate-p) 'bfrstate))
  :short "Recognizer for valid Boolean Function Representation (@(see bfr)) objects."
  (bfrstate-case
    :aig (aig-p x)
    :bdd (acl2::ubddp x)
    :aignet
    (or (booleanp x)
        (and (satlink::litp x)
             (not (eql x 0))
             (not (eql x 1))
             (<= (satlink::lit->var x) (bfrstate->bound bfrstate)))))
  ///
  (defthm bfr-p-of-constants
    (and (bfr-p t)
         (bfr-p nil)))

  (defthm bfr-p-when-bfrstate>=
    (implies (and (bfrstate>= new old)
                  (bfr-p x old))
             (bfr-p x new))
    :hints(("Goal" :in-theory (enable bfrstate>=-implies-mode
                                      bfrstate>=-implies-bound))))

  (defthm bfr-p-in-terms-of-aig-p
    (equal (bfr-p x (bfrstate (bfrmode :aig) bound))
           (aig-p x)))

  (defthm bfr-p-in-terms-of-ubddp
    (equal (bfr-p x (bfrstate (bfrmode :bdd) bound))
           (acl2::ubddp x))))





(std::deflist bfr-listp$ (x bfrstate)
  :guard (bfrstate-p bfrstate)
  (bfr-p x)
  ///
  (defmacro bfr-listp (x &optional (bfrstate 'bfrstate))
    `(bfr-listp$ ,x ,bfrstate))

  (add-macro-alias bfr-listp bfr-listp$)

  (fty::deffixequiv bfr-listp$ :args ((bfrstate bfrstate-p)))

  (defthm bfr-listp-of-nil
    (bfr-listp nil))

  (defthm bfr-listp-when-bfrstate>=
    (implies (and (bfrstate>= new old)
                  (bfr-listp x old))
             (bfr-listp x new))))


(define bounded-lit-fix ((x satlink::litp)
                         (bound natp))
  :guard (<= (satlink::lit->var x) bound)
  :returns (new-x satlink::litp :rule-classes :type-prescription)
  :inline t
  (mbe :logic (if (<= (satlink::lit->var x) (nfix bound))
                  (satlink::lit-fix x)
                (satlink::make-lit 0 (satlink::lit->neg x)))
       :exec x)
  ///
  (defret bound-of-bounded-lit-fix
    (<= (satlink::lit->var new-x) (nfix bound))
    :rule-classes :linear)
  (defret bounded-lit-fix-when-bounded
    (implies (<= (satlink::lit->var x) (nfix bound))
             (equal new-x (satlink::lit-fix x)))))

(define aignet-lit->bfr ((x satlink::litp) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (and (bfrstate-mode-is :aignet)
              (<= (satlink::lit->var x) (bfrstate->bound bfrstate)))
  :returns (bfr (implies (bfrstate-mode-is :aignet)
                         (bfr-p bfr))
                :hints(("Goal" :in-theory (enable bfr-p))))
  (b* ((x (bounded-lit-fix x (bfrstate->bound bfrstate))))
    (case x
      (0 nil)
      (1 t)
      (t x))))


(define bfr-fix ((x bfr-p) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (new-x bfr-p)
  :prepwork ((local (in-theory (enable bfr-p aignet-lit->bfr))))
  (mbe :logic (bfrstate-case
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



(define bfr-list-fix ((x bfr-listp) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (new-x bfr-listp)
  (if (atom x)
      x
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


(define bfr->aignet-lit ((x bfr-p) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (bfrstate-mode-is :aignet)
  :returns (lit satlink::litp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable bfr-fix aignet-lit->bfr bfr-p))))
  (b* ((x (bfr-fix x)))
    (case x
      ((nil) 0)
      ((t) 1)
      (t (satlink::lit-fix x))))
  ///
  (defret bfr->aignet-lit-in-bounds
    (implies (bfrstate-mode-is :aignet)
             (<= (satlink::lit->var lit) (bfrstate->bound bfrstate)))
    :rule-classes :linear)

  (defthm bfr->aignet-lit-of-aignet-lit->bfr
    (implies (bfrstate-mode-is :aignet)
             (equal (bfr->aignet-lit (aignet-lit->bfr x))
                    (bounded-lit-fix x (bfrstate->bound bfrstate))))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr bounded-lit-fix))))

  (defthm aignet-lit->bfr-of-bfr->aignet-lit
    (implies (bfrstate-mode-is :aignet)
             (equal (aignet-lit->bfr (bfr->aignet-lit x))
                    (bfr-fix x)))
    :hints(("Goal" :in-theory (enable aignet-lit->bfr bfr-fix))))

  (defthm bfr->aignet-lit-of-bfr-fix
    (equal (bfr->aignet-lit (bfr-fix x))
           (bfr->aignet-lit x))
    :hints(("Goal" :in-theory (enable bfr-fix)))))




(defines gl-bfr-object-p-aux
  (define gl-bfr-object-p-aux ((x gl-object-p)
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
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
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (gl-objectlist-count x)
    (if (atom x)
        t
      (and (gl-bfr-object-p-aux (car x))
           (gl-bfr-objectlist-p-aux (cdr x)))))
  ///
  (local (in-theory (disable (:d gl-bfr-object-p-aux)
                             (:d gl-bfr-objectlist-p-aux))))

  (fty::deffixequiv-mutual gl-bfr-object-p-aux
    :hints ((acl2::use-termhint
             `(:expand ((gl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (gl-bfr-object-p-aux ,(acl2::hq (gl-object-fix x)) ,(acl2::hq bfrstate))
                        (gl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq (gl-objectlist-fix x)) ,(acl2::hq bfrstate))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))))))))


(defines gl-bfr-object-p
  (define gl-bfr-object-p (x &optional ((bfrstate bfrstate-p) 'bfrstate))
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
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
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

  (fty::deffixequiv-mutual gl-bfr-object-p-aux
    :hints ((acl2::use-termhint
             `(:expand ((gl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (gl-bfr-object-p-aux ,(acl2::hq (gl-object-fix x)) ,(acl2::hq bfrstate))
                        (gl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq (gl-objectlist-fix x)) ,(acl2::hq bfrstate))
                        (gl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate))))))))

  (defthm-gl-bfr-object-p-flag
    (defthm gl-bfr-object-p-when-bfrstate>=
      (implies (and (bfrstate>= new old)
                    (gl-bfr-object-p x old))
               (gl-bfr-object-p x new))
      :hints ('(:expand ((:free (bfrstate) (gl-bfr-object-p x)))))
      :flag gl-bfr-object-p)
    (defthm gl-bfr-objectlist-p-when-bfrstate>=
      (implies (and (bfrstate>= new old)
                    (gl-bfr-objectlist-p x old))
               (gl-bfr-objectlist-p x new))
      :hints ('(:expand ((:free (bfrstate) (gl-bfr-objectlist-p x)))))
      :flag gl-bfr-objectlist-p)
    :hints (("goal" :induct (gl-bfr-object-p-flag flag x old)))))





(defines gl-bfr-object-fix
  (define gl-bfr-object-fix ((x gl-bfr-object-p)
                             &optional ((bfrstate bfrstate-p) 'bfrstate))
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
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
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

  (defthm-gl-bfr-object-fix-flag gl-bfr-object-fix-of-gl-object-fix
    (defthm gl-bfr-object-fix-of-gl-object-fix
      (equal (gl-bfr-object-fix (gl-object-fix x))
             (gl-bfr-object-fix x))
      :hints ('(:expand ((gl-object-fix x)
                         (gl-bfr-object-fix x))
                :in-theory (enable gl-bfr-object-fix)))
      :flag gl-bfr-object-fix)
    (defthm gl-bfr-objectlist-fix-of-gl-objectlist-fix
      (equal (gl-bfr-objectlist-fix (gl-objectlist-fix x))
             (gl-bfr-objectlist-fix x))
      :hints ('(:expand ((gl-objectlist-fix x)
                         (gl-bfr-objectlist-fix x)
                         (:free (a b) (gl-bfr-objectlist-fix (cons a b))))))
      :flag gl-bfr-objectlist-fix))

  (verify-guards gl-bfr-object-fix-fn
    :hints('(:expand ((gl-bfr-object-p x)
                      (gl-bfr-objectlist-p x))))))





(defines gl-object-bfrlist
  (define gl-object-bfrlist ((x gl-object-p))
    :measure (gl-object-count x)
    :verify-guards nil
    :returns (bfrlist true-listp :rule-classes :type-prescription)
    (gl-object-case x
      :g-concrete nil
      :g-boolean (list x.bool)
      :g-integer x.bits
      :g-ite (append (gl-object-bfrlist x.test)
                     (append (gl-object-bfrlist x.then)
                             (gl-object-bfrlist x.else)))
      :g-apply (gl-objectlist-bfrlist x.args)
      :g-var nil
      :g-cons (append (gl-object-bfrlist x.car)
                      (gl-object-bfrlist x.cdr))))
  (define gl-objectlist-bfrlist ((x gl-objectlist-p))
    :measure (gl-objectlist-count x)
    :returns (bfrlist true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (append (gl-object-bfrlist (car x))
              (gl-objectlist-bfrlist (cdr x)))))
  ///
  
  (verify-guards gl-object-bfrlist)

  (fty::deffixequiv-mutual gl-object-bfrlist)

  (defthm gl-object-bfrlist-when-g-concrete
    (implies (gl-object-case x :g-concrete)
             (equal (gl-object-bfrlist x) nil))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-boolean
    (implies (gl-object-case x :g-boolean)
             (equal (gl-object-bfrlist x)
                    (list (g-boolean->bool x))))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-integer
    (implies (gl-object-case x :g-integer)
             (equal (gl-object-bfrlist x)
                    (g-integer->bits x)))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-ite
    (implies (gl-object-case x :g-ite)
             (equal (gl-object-bfrlist x)
                    (append (gl-object-bfrlist (g-ite->test x))
                            (append (gl-object-bfrlist (g-ite->then x))
                                    (gl-object-bfrlist (g-ite->else x))))))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-apply
    (implies (gl-object-case x :g-apply)
             (equal (gl-object-bfrlist x)
                    (gl-objectlist-bfrlist (g-apply->args x))))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-var
    (implies (gl-object-case x :g-var)
             (equal (gl-object-bfrlist x) nil))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-object-bfrlist-when-g-cons
    (implies (gl-object-case x :g-cons)
             (equal (gl-object-bfrlist x)
                    (append (gl-object-bfrlist (g-cons->car x))
                            (gl-object-bfrlist (g-cons->cdr x)))))
    :hints (("goal" :expand ((gl-object-bfrlist x)))))

  (defthm gl-objectlist-bfrlist-when-consp
    (implies (consp x)
             (equal (gl-objectlist-bfrlist x)
                    (append (gl-object-bfrlist (car x))
                            (gl-objectlist-bfrlist (cdr x)))))
    :hints (("goal" :expand ((gl-objectlist-bfrlist x)))))

  (defthm gl-objectlist-bfrlist-when-atom
    (implies (not (consp x))
             (equal (gl-objectlist-bfrlist x) nil))
    :hints (("goal" :expand ((gl-objectlist-bfrlist x)))))

  (def-ruleset! gl-object-bfrlist-when-thms
    '(gl-object-bfrlist-when-g-concrete
      gl-object-bfrlist-when-g-boolean
      gl-object-bfrlist-when-g-integer
      gl-object-bfrlist-when-g-ite
      gl-object-bfrlist-when-g-apply
      gl-object-bfrlist-when-g-cons
      gl-objectlist-bfrlist-when-consp
      gl-objectlist-bfrlist-when-atom))

  (defthm gl-objectlist-bfrlist-of-cons
    (equal (gl-objectlist-bfrlist (cons x y))
           (append (gl-object-bfrlist x)
                   (gl-objectlist-bfrlist y)))
    :hints (("goal" :expand ((gl-objectlist-bfrlist (cons x y))))))

  (defthm gl-objectlist-bfrlist-of-nil
    (equal (gl-objectlist-bfrlist nil) nil)
    :hints (("goal" :expand ((gl-objectlist-bfrlist nil)))))

  (defthm gl-object-bfrlist-of-g-concrete
    (equal (gl-object-bfrlist (g-concrete val)) nil))

  (defthm gl-object-bfrlist-of-g-boolean
    (equal (gl-object-bfrlist (g-boolean bool)) (list bool))
    :hints (("goal" :expand ((gl-object-bfrlist (g-boolean bool))))))

  (defthm gl-object-bfrlist-of-g-integer
    (equal (gl-object-bfrlist (g-integer bits))
           (acl2::true-list-fix bits)))

  (defthm gl-object-bfrlist-of-g-ite
    (equal (gl-object-bfrlist (g-ite test then else))
           (append (gl-object-bfrlist test)
                   (append (gl-object-bfrlist then)
                           (gl-object-bfrlist else)))))

  (defthm gl-object-bfrlist-of-g-apply
    (equal (gl-object-bfrlist (g-apply fn args))
           (gl-objectlist-bfrlist args)))

  (defthm gl-object-bfrlist-of-g-var
    (equal (gl-object-bfrlist (g-var name))nil))

  (defthm gl-object-bfrlist-of-g-cons
    (equal (gl-object-bfrlist (g-cons car cdr))
           (append (gl-object-bfrlist car)
                   (gl-object-bfrlist cdr))))

  (in-theory (disable* gl-object-bfrlist-when-thms))

  (def-ruleset! gl-object-bfrlist-of-thms
    '(gl-object-bfrlist-of-g-concrete
      gl-object-bfrlist-of-g-boolean
      gl-object-bfrlist-of-g-integer
      gl-object-bfrlist-of-g-ite
      gl-object-bfrlist-of-g-apply
      gl-object-bfrlist-of-g-var
      gl-object-bfrlist-of-g-cons
      gl-objectlist-bfrlist-of-cons
      gl-objectlist-bfrlist-of-nil))

  (defthm-gl-object-bfrlist-flag
    (defthm bfr-listp-of-gl-object-bfrlist
      (implies (gl-object-p x)
               (equal (bfr-listp (gl-object-bfrlist x))
                      (gl-bfr-object-p x)))
      :hints ('(:expand ((:free (bfrstate) (gl-bfr-object-p x))
                         (gl-object-p x)
                         (gl-object-bfrlist x))))
      :flag gl-object-bfrlist)
    (defthm bfrlist-okp-of-gl-objectlist-bfrlist
      (implies (gl-objectlist-p x)
               (equal (bfr-listp (gl-objectlist-bfrlist x))
                      (gl-bfr-objectlist-p x)))
      :hints ('(:expand ((:free (bfrstate) (gl-bfr-objectlist-p x))
                         (gl-objectlist-p x)
                         (gl-objectlist-bfrlist x))))
      :flag gl-objectlist-bfrlist))

  (defthm-gl-object-bfrlist-flag
    (defthmd gl-object-bfrlist-when-symbolic-boolean-free
      (implies (gl-object-symbolic-boolean-free x)
               (equal (gl-object-bfrlist x) nil))
      :hints ('(:expand ((gl-object-bfrlist x)
                         (gl-object-symbolic-boolean-free x))))
      :flag gl-object-bfrlist)
    (defthmd gl-objectlist-bfrlist-when-symbolic-boolean-free
      (implies (gl-objectlist-symbolic-boolean-free x)
               (equal (gl-objectlist-bfrlist x) nil))
      :hints ('(:expand ((gl-objectlist-bfrlist x)
                         (gl-objectlist-symbolic-boolean-free x))))
      :flag gl-objectlist-bfrlist)))

(define gl-object-alist-bfrlist ((x gl-object-alist-p))
  :returns (bfrlist)
  (if (atom x)
      nil
    (append (and (mbt (and (consp (car x))
                           (pseudo-var-p (caar x))))
                 (gl-object-bfrlist (cdar x)))
            (gl-object-alist-bfrlist (cdr x))))
  ///
  (defthm gl-object-alist-bfrlist-of-cons
    (implies (pseudo-var-p var)
             (equal (gl-object-alist-bfrlist (cons (cons var val) rest))
                    (append (gl-object-bfrlist val)
                            (gl-object-alist-bfrlist rest)))))

  (local (in-theory (enable gl-object-alist-fix))))


