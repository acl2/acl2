; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "ubdd")
(include-book "centaur/satlink/litp" :dir :system)
(include-book "fgl-object")
(include-book "std/basic/two-nats-measure" :dir :system)
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
particular time is governed by @(see bfr-mode), and operations like
@('bfr-and') allow us to construct new function nodes using whatever the
current representation is.</p>

<p>To support aignets, it is important for BFRs to be well-formed,
i.e. literals whose node index is in bounds for the current aignet.  So we
also use a @(see bfrstate) object which simultaneously tracks the bfr-mode and
current bound.</p>")

(local (xdoc::set-default-parents bfr))

(std::defenum bfr-mode-p (0 1 2))

(defxdoc bfr-mode
  :short "Determines whether FGL is using @(see ubdds), hons-@(see aig)s, or @(see
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
       (>= (bfrstate->bound x) (bfrstate->bound y)))
  ///
  (defthm bfrstate>=-self
    (bfrstate>= x x))

  (defthmd bfrstate>=-implies-mode
    (implies (bfrstate>= x y)
             (equal (bfrstate->mode x)
                    (bfrstate->mode y))))

  (defthmd bfrstate>=-implies-bound
    (implies (bfrstate>= x y)
             (>= (bfrstate->bound x) (bfrstate->bound y)))
    :rule-classes (:rewrite :linear)))


(define bfr-p (x &optional ((bfrstate bfrstate-p) 'bfrstate))
  :short "Recognizer for valid Boolean Function Representation (@(see bfr)) objects."
  (bfrstate-case
    :aig (aig-p x (bfrstate->bound bfrstate))
    :bdd (ubddp x (bfrstate->bound bfrstate))
    :aignet
    (or (booleanp x)
        (and (satlink::litp x)
             (not (eql x 0))
             (not (eql x 1))
             (<= (satlink::lit->var x) (bfrstate->bound bfrstate)))))
  ///
  (defthm bfr-p-of-constants
    (and (bfr-p t)
         (bfr-p nil))
    :hints(("Goal" :in-theory (enable aig-p ubddp))))

  (defthm bfr-p-when-bfrstate>=
    (implies (and (bfrstate>= new old)
                  (bfr-p x old))
             (bfr-p x new))
    :hints(("Goal" :in-theory (enable bfrstate>=-implies-mode
                                      bfrstate>=-implies-bound))))

  (defthm bfr-p-in-terms-of-aig-p
    (equal (bfr-p x (bfrstate (bfrmode :aig) bound))
           (aig-p x bound)))

  (defthm bfr-p-in-terms-of-ubddp
    (equal (bfr-p x (bfrstate (bfrmode :bdd) bound))
           (ubddp x bound))))





(std::deflist bfr-listp$ (x bfrstate)
  :guard (bfrstate-p bfrstate)
  :elementp-of-nil t
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
      (t x)))
  ///
  (defthm aignet-lit->bfr-of-consts
    (and (equal (aignet-lit->bfr 0) nil)
         (equal (aignet-lit->bfr 1) t))))


(define bfr-fix ((x bfr-p) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (new-x bfr-p)
  :prepwork ((local (in-theory (enable bfr-p aignet-lit->bfr))))
  (mbe :logic (bfrstate-case
                :aig (aig-fix x (bfrstate->bound bfrstate))
                :bdd (ubdd-fix x (bfrstate->bound bfrstate))
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
  (mbe :logic (if (atom x)
                  x
                (cons (bfr-fix (car x))
                      (bfr-list-fix (cdr x))))
       :exec x)
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
    :hints(("Goal" :in-theory (enable bfr-fix))))

  (defthm bfr->aignet-lit-of-consts
    (and (equal (bfr->aignet-lit t) 1)
         (equal (bfr->aignet-lit nil) 0))))

(define bfr-negate ((x bfr-p) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :returns (new-x bfr-p :hints(("Goal" :in-theory (enable bfr-p))
                               (and stable-under-simplificationp
                                    '(:in-theory (enable bfr->aignet-lit aignet-lit->bfr
                                                         bfr-fix)))))
  :guard-hints (("goal" :in-theory (enable bfr-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable bfr->aignet-lit aignet-lit->bfr
                                          bfr-fix))))
  :prepwork ((local (defthm lit->var-not-equal-0
                      (implies (and (satlink::litp x)
                                    (not (equal x 0))
                                    (not (equal x 1)))
                               (not (equal (satlink::lit->var x) 0)))
                      :hints(("Goal" :in-theory (enable satlink::lit->var satlink::litp
                                                        bitops::logtail**))))))
  (mbe :logic (b* ((x (bfr-fix x)))
                (bfrstate-case
                  :aig (acl2::aig-not x)
                  :bdd (acl2::q-not x)
                  :aignet
                  (aignet-lit->bfr (satlink::lit-negate (bfr->aignet-lit x)))))
       :exec (if (booleanp x)
                 (not x)
               (bfrstate-case
                 :aig (acl2::aig-not x)
                 :bdd (acl2::q-not x)
                 :aignet (satlink::lit-negate x))))
  ///
  (defthm bfr-negate-of-bfr-fix
    (equal (bfr-negate (bfr-fix x))
           (bfr-negate x))))




(defines fgl-bfr-object-p-aux
  (define fgl-bfr-object-p-aux ((x fgl-object-p)
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    (fgl-object-case x
      :g-concrete t
      :g-boolean (bfr-p x.bool)
      :g-integer (bfr-listp x.bits)
      :g-ite (and (fgl-bfr-object-p-aux x.test)
                  (fgl-bfr-object-p-aux x.then)
                  (fgl-bfr-object-p-aux x.else))
      :g-apply (fgl-bfr-objectlist-p-aux x.args)
      :g-var t
      :g-cons (and (fgl-bfr-object-p-aux x.car)
                   (fgl-bfr-object-p-aux x.cdr))
      :g-map (fgl-bfr-object-alist-p-aux x.alist)))
  (define fgl-bfr-objectlist-p-aux ((x fgl-objectlist-p)
                                   &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (if (atom x)
        t
      (and (fgl-bfr-object-p-aux (car x))
           (fgl-bfr-objectlist-p-aux (cdr x)))))

  (define fgl-bfr-object-alist-p-aux ((x fgl-object-alist-p)
                                     &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
      (if (atom x)
          t
        (if (mbt (consp (car x)))
            (and (fgl-bfr-object-p-aux (cdar x))
                 (fgl-bfr-object-alist-p-aux (cdr x)))
          (fgl-bfr-object-alist-p-aux (cdr x)))))
  ///
  (local (in-theory (disable (:d fgl-bfr-object-p-aux)
                             (:d fgl-bfr-objectlist-p-aux)
                             (:d fgl-bfr-object-alist-p-aux))))

  (fty::deffixequiv-mutual fgl-bfr-object-p-aux
    :hints (("goal" :expand ((fgl-object-alist-fix x)))
            (acl2::use-termhint
             `(:expand ((fgl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-p-aux ,(acl2::hq (fgl-object-fix x)) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq (fgl-objectlist-fix x)) ,(acl2::hq bfrstate))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
                        (fgl-bfr-object-alist-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-alist-p-aux ,(acl2::hq (fgl-object-alist-fix x)) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-alist-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))))))))


(defines fgl-bfr-object-p
  (define fgl-bfr-object-p (x &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (fgl-object-count x)
    :verify-guards nil
    (mbe :logic (and (fgl-object-p x)
                     (fgl-object-case x
                       :g-concrete t
                       :g-boolean (bfr-p x.bool)
                       :g-integer (bfr-listp x.bits)
                       :g-ite (and (fgl-bfr-object-p x.test)
                                   (fgl-bfr-object-p x.then)
                                   (fgl-bfr-object-p x.else))
                       :g-apply (fgl-bfr-objectlist-p x.args)
                       :g-var t
                       :g-cons (and (fgl-bfr-object-p x.car)
                                    (fgl-bfr-object-p x.cdr))
                       :g-map (fgl-bfr-object-alist-p x.alist)))
         :exec (and (fgl-object-p x)
                    (fgl-bfr-object-p-aux x))))
  (define fgl-bfr-objectlist-p (x
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (fgl-objectlist-count x)
    (mbe :logic (and (fgl-objectlist-p x)
                     (if (atom x)
                         t
                       (and (fgl-bfr-object-p (car x))
                            (fgl-bfr-objectlist-p (cdr x)))))
         :exec (and (fgl-objectlist-p x)
                    (fgl-bfr-objectlist-p-aux x))))
  (define fgl-bfr-object-alist-p (x
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (fgl-object-alist-count x)
    (mbe :logic (and (fgl-object-alist-p x)
                     (if (atom x)
                         t
                       (and (fgl-bfr-object-p (cdar x))
                            (fgl-bfr-object-alist-p (cdr x)))))
         :exec (and (fgl-object-alist-p x)
                    (fgl-bfr-object-alist-p-aux x))))
  ///
  (local
   (defthm-fgl-bfr-object-p-flag
     (defthm fgl-bfr-object-p-aux-elim
       (implies (fgl-object-p x)
                (equal (fgl-bfr-object-p-aux x)
                       (fgl-bfr-object-p x)))
       :hints ('(:expand ((fgl-bfr-object-p-aux x)
                          (fgl-bfr-object-p x))))
       :flag fgl-bfr-object-p)
     (defthm fgl-bfr-objectlist-p-aux-elim
       (implies (fgl-objectlist-p x)
                (equal (fgl-bfr-objectlist-p-aux x)
                       (fgl-bfr-objectlist-p x)))
       :hints ('(:expand ((fgl-bfr-objectlist-p-aux x)
                          (fgl-bfr-objectlist-p-aux nil)
                          (fgl-bfr-objectlist-p x)
                          (fgl-bfr-objectlist-p nil))))
       :flag fgl-bfr-objectlist-p)
     
     (defthm fgl-bfr-object-alist-p-aux-elim
       (implies (fgl-object-alist-p x)
                (equal (fgl-bfr-object-alist-p-aux x)
                       (fgl-bfr-object-alist-p x)))
       :hints ('(:expand ((fgl-bfr-object-alist-p-aux x)
                          (fgl-bfr-object-alist-p-aux nil)
                          (fgl-bfr-object-alist-p x)
                          (fgl-bfr-object-alist-p nil))))
       :flag fgl-bfr-object-alist-p)))
  
  (verify-guards fgl-bfr-object-p-fn)

  (defthm fgl-object-p-when-fgl-bfr-object-p
    (implies (fgl-bfr-object-p x)
             (fgl-object-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm fgl-objectlist-p-when-fgl-bfr-objectlist-p
    (implies (fgl-bfr-objectlist-p x)
             (fgl-objectlist-p x))
    :rule-classes (:rewrite :forward-chaining))

  (defthm fgl-bfr-object-p-when-g-boolean
    (implies (and (fgl-object-case x :g-boolean)
                  (fgl-bfr-object-p x))
             (bfr-p (g-boolean->bool x)))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-object-p-when-g-integer
    (implies (and (fgl-object-case x :g-integer)
                  (fgl-bfr-object-p x))
             (bfr-listp (g-integer->bits x)))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-object-p-when-g-ite
    (implies (and (fgl-object-case x :g-ite)
                  (fgl-bfr-object-p x))
             (and (fgl-bfr-object-p (g-ite->test x))
                  (fgl-bfr-object-p (g-ite->then x))
                  (fgl-bfr-object-p (g-ite->else x))))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-object-p-when-g-apply
    (implies (and (fgl-object-case x :g-apply)
                  (fgl-bfr-object-p x))
             (fgl-bfr-objectlist-p (g-apply->args x)))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-object-p-when-g-cons
    (implies (and (fgl-object-case x :g-cons)
                  (fgl-bfr-object-p x))
             (and (fgl-bfr-object-p (g-cons->car x))
                  (fgl-bfr-object-p (g-cons->cdr x))))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-object-p-when-g-map
    (implies (and (fgl-object-case x :g-map)
                  (fgl-bfr-object-p x))
             (fgl-bfr-object-alist-p (g-map->alist x)))
    :hints (("goal" :expand ((fgl-bfr-object-p x)))))

  (defthm fgl-bfr-objectlist-p-implies-car/cdr
    (implies (fgl-bfr-objectlist-p x)
             (and (fgl-bfr-object-p (car x))
                  (fgl-bfr-objectlist-p (cdr x))))
    :hints (("goal" :expand ((fgl-bfr-objectlist-p x)
                             (fgl-bfr-object-p nil)
                             (fgl-bfr-objectlist-p nil)))))

  (defthm fgl-bfr-object-alist-p-implies-cdar/cdr
    (implies (fgl-bfr-object-alist-p x)
             (and (fgl-bfr-object-p (cdar x))
                  (fgl-bfr-object-alist-p (cdr x))))
    :hints (("goal" :expand ((fgl-bfr-object-alist-p x)
                             (fgl-bfr-object-p nil)
                             (fgl-bfr-object-alist-p nil)))))

  (defthm fgl-bfr-objectlist-p-of-cons
    (implies (and (fgl-bfr-object-p x)
                  (fgl-bfr-objectlist-p y))
             (fgl-bfr-objectlist-p (cons x y)))
    :hints (("goal" :expand ((fgl-bfr-objectlist-p (cons x y))))))

  (defthm fgl-bfr-objectlist-p-of-nil
    (fgl-bfr-objectlist-p nil)
    :hints (("goal" :expand ((fgl-bfr-objectlist-p nil)))))

  (defthm fgl-bfr-object-p-of-g-concrete
    (fgl-bfr-object-p (g-concrete val))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-concrete val))))))

  (defthm fgl-bfr-object-p-of-g-boolean
    (implies (bfr-p bool)
             (fgl-bfr-object-p (g-boolean bool)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-boolean bool))))))

  (defthm fgl-bfr-object-p-of-g-integer
    (implies (bfr-listp bits)
             (fgl-bfr-object-p (g-integer bits)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-integer bits))))))

  (defthm fgl-bfr-object-p-of-g-ite
    (implies (and (fgl-bfr-object-p test)
                  (fgl-bfr-object-p then)
                  (fgl-bfr-object-p else))
             (fgl-bfr-object-p (g-ite test then else)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-ite test then else))))))

  (defthm fgl-bfr-object-p-of-g-apply
    (implies (and (fgl-bfr-objectlist-p args))
             (fgl-bfr-object-p (g-apply fn args)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-apply fn args))))))

  (defthm fgl-bfr-object-p-of-g-var
    (fgl-bfr-object-p (g-var name))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-var name))))))

  (defthm fgl-bfr-object-p-of-g-cons
    (implies (and (fgl-bfr-object-p car)
                  (fgl-bfr-object-p cdr))
             (fgl-bfr-object-p (g-cons car cdr)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-cons car cdr))))))

  (defthm fgl-bfr-object-p-of-g-map
    (implies (fgl-bfr-object-alist-p alist)
             (fgl-bfr-object-p (g-map tag alist)))
    :hints (("goal" :expand ((fgl-bfr-object-p (g-map tag alist))
                             (fgl-bfr-object-alist-p alist)
                             (fgl-bfr-object-alist-p (fgl-object-alist-fix alist))))))

  (fty::deffixequiv-mutual fgl-bfr-object-p
    :hints ((acl2::use-termhint
             `(:expand ((fgl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-p-aux ,(acl2::hq (fgl-object-fix x)) ,(acl2::hq bfrstate))
                        (fgl-bfr-object-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate)))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq bfrstate))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq (fgl-objectlist-fix x)) ,(acl2::hq bfrstate))
                        (fgl-bfr-objectlist-p-aux ,(acl2::hq x) ,(acl2::hq (bfrstate-fix bfrstate))))))))

  (defthm-fgl-bfr-object-p-flag
    (defthm fgl-bfr-object-p-when-bfrstate>=
      (implies (and (bfrstate>= new old)
                    (fgl-bfr-object-p x old))
               (fgl-bfr-object-p x new))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-object-p x)))))
      :flag fgl-bfr-object-p)
    (defthm fgl-bfr-objectlist-p-when-bfrstate>=
      (implies (and (bfrstate>= new old)
                    (fgl-bfr-objectlist-p x old))
               (fgl-bfr-objectlist-p x new))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-objectlist-p x)))))
      :flag fgl-bfr-objectlist-p)
    (defthm fgl-bfr-object-alist-p-when-bfrstate>=
      (implies (and (bfrstate>= new old)
                    (fgl-bfr-object-alist-p x old))
               (fgl-bfr-object-alist-p x new))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-object-alist-p x)))))
      :flag fgl-bfr-object-alist-p)
    :hints (("goal" :induct (fgl-bfr-object-p-flag flag x old)))))

(define fgl-bfr-object-bindings-p (x &optional ((bfrstate bfrstate-p) 'bfrstate))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-var-p (caar x))
         (fgl-bfr-object-p (cdar x))
         (fgl-bfr-object-bindings-p (cdr x))))
  ///
  (defthmd fgl-bfr-object-bindings-p-implies-fgl-object-bindings-p
    (implies (fgl-bfr-object-bindings-p x)
             (fgl-object-bindings-p x))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-p)))))



(defines fgl-bfr-object-fix
  :flag-local nil
  (define fgl-bfr-object-fix ((x fgl-bfr-object-p)
                             &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :returns (new-x fgl-bfr-object-p
                    :hints ('(:in-theory (enable fgl-bfr-object-p))))
    :verify-guards nil
    (mbe :logic
         (fgl-object-case x
           :g-concrete (g-concrete x.val)
           :g-boolean (g-boolean (bfr-fix x.bool))
           :g-integer (g-integer (bfr-list-fix x.bits))
           :g-ite (g-ite (fgl-bfr-object-fix x.test)
                         (fgl-bfr-object-fix x.then)
                         (fgl-bfr-object-fix x.else))
           :g-apply (g-apply x.fn (fgl-bfr-objectlist-fix x.args))
           :g-var (g-var x.name)
           :g-cons (g-cons (fgl-bfr-object-fix x.car)
                           (fgl-bfr-object-fix x.cdr))
           :g-map (g-map x.tag (fgl-bfr-object-alist-fix x.alist)))
         :exec x))
  (define fgl-bfr-objectlist-fix ((x fgl-bfr-objectlist-p)
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (new-x fgl-bfr-objectlist-p
                    :hints ('(:in-theory (enable fgl-bfr-objectlist-p))))
    (mbe :logic (if (atom x)
                    nil
                  (cons (fgl-bfr-object-fix (car x))
                        (fgl-bfr-objectlist-fix (cdr x))))
         :exec x))
  
  (define fgl-bfr-object-alist-fix ((x fgl-bfr-object-alist-p)
                               &optional ((bfrstate bfrstate-p) 'bfrstate))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (new-x fgl-bfr-object-alist-p
                    :hints ('(:in-theory (enable fgl-bfr-object-alist-p))))
    (mbe :logic
         (if (atom x)
             x
           (if (consp (car x))
               (cons (cons (caar x) (fgl-bfr-object-fix (cdar x)))
                     (fgl-bfr-object-alist-fix (cdr x)))
             (fgl-bfr-object-alist-fix (cdr x))))
         :exec x))
  ///
  (defthm-fgl-bfr-object-fix-flag fgl-bfr-object-fix-when-fgl-bfr-object-p
    (defthm fgl-bfr-object-fix-when-fgl-bfr-object-p
      (implies (fgl-bfr-object-p x)
               (equal (fgl-bfr-object-fix x) x))
      :hints ('(:expand ((fgl-bfr-object-p x)
                         (fgl-bfr-object-fix x))))
      :flag fgl-bfr-object-fix)
    (defthm fgl-bfr-objectlist-fix-when-fgl-bfr-objectlist-p
      (implies (fgl-bfr-objectlist-p x)
               (equal (fgl-bfr-objectlist-fix x) x))
      :hints ('(:expand ((fgl-bfr-objectlist-p x)
                         (fgl-bfr-objectlist-fix x))))
      :flag fgl-bfr-objectlist-fix)
    (defthm fgl-bfr-object-alist-fix-when-fgl-bfr-object-alist-p
      (implies (fgl-bfr-object-alist-p x)
               (equal (fgl-bfr-object-alist-fix x) x))
      :hints ('(:expand ((fgl-bfr-object-alist-p x)
                         (fgl-bfr-object-alist-fix x))))
      :flag fgl-bfr-object-alist-fix))

  (defret-mutual fgl-object-p-of-fgl-bfr-object-fix
    (defret fgl-object-p-of-fgl-bfr-object-fix
      (fgl-object-p new-x)
      :fn fgl-bfr-object-fix)
    (defret fgl-objectlist-p-of-fgl-bfr-objectlist-fix
      (fgl-objectlist-p new-x)
      :fn fgl-bfr-objectlist-fix)
    (defret fgl-object-alist-p-of-fgl-bfr-object-alist-fix
      (fgl-object-alist-p new-x)
      :fn fgl-bfr-object-alist-fix))

  (defthm-fgl-bfr-object-fix-flag fgl-bfr-object-fix-of-fgl-object-fix
    (defthm fgl-bfr-object-fix-of-fgl-object-fix
      (equal (fgl-bfr-object-fix (fgl-object-fix x))
             (fgl-bfr-object-fix x))
      :hints ('(:expand ((fgl-object-fix x)
                         (fgl-bfr-object-fix x))
                :in-theory (enable fgl-bfr-object-fix)))
      :flag fgl-bfr-object-fix)
    (defthm fgl-bfr-objectlist-fix-of-fgl-objectlist-fix
      (equal (fgl-bfr-objectlist-fix (fgl-objectlist-fix x))
             (fgl-bfr-objectlist-fix x))
      :hints ('(:expand ((fgl-objectlist-fix x)
                         (fgl-bfr-objectlist-fix x)
                         (:free (a b) (fgl-bfr-objectlist-fix (cons a b))))))
      :flag fgl-bfr-objectlist-fix)
    (defthm fgl-bfr-object-alist-fix-of-fgl-object-alist-fix
      (equal (fgl-bfr-object-alist-fix (fgl-object-alist-fix x))
             (fgl-bfr-object-alist-fix x))
      :hints ('(:expand ((fgl-object-alist-fix x)
                         (fgl-bfr-object-alist-fix x)
                         (:free (a b) (fgl-bfr-object-alist-fix (cons a b))))))
      :flag fgl-bfr-object-alist-fix))

  (verify-guards fgl-bfr-object-fix-fn
    :hints('(:expand ((fgl-bfr-object-p x)
                      (fgl-bfr-objectlist-p x)
                      (fgl-bfr-object-alist-p x))))))





(defines fgl-object-bfrlist
  (define fgl-object-bfrlist ((x fgl-object-p))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :verify-guards nil
    :returns (bfrlist true-listp :rule-classes :type-prescription)
    (fgl-object-case x
      :g-concrete nil
      :g-boolean (list x.bool)
      :g-integer x.bits
      :g-ite (append (fgl-object-bfrlist x.test)
                     (append (fgl-object-bfrlist x.then)
                             (fgl-object-bfrlist x.else)))
      :g-apply (fgl-objectlist-bfrlist x.args)
      :g-var nil
      :g-cons (append (fgl-object-bfrlist x.car)
                      (fgl-object-bfrlist x.cdr))
      :g-map (fgl-object-alist-bfrlist x.alist)))
  (define fgl-objectlist-bfrlist ((x fgl-objectlist-p))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (bfrlist true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (append (fgl-object-bfrlist (car x))
              (fgl-objectlist-bfrlist (cdr x)))))
  (define fgl-object-alist-bfrlist ((x fgl-object-alist-p))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (bfrlist true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (if (mbt (consp (car x)))
          (append (fgl-object-bfrlist (cdar x))
                  (fgl-object-alist-bfrlist (cdr x)))
        (fgl-object-alist-bfrlist (cdr x)))))
  ///
  
  (verify-guards fgl-object-bfrlist)

  (fty::deffixequiv-mutual fgl-object-bfrlist
    :hints ((and stable-under-simplificationp
                 '(:expand ((fgl-object-alist-fix x))))))

  (defthm fgl-object-bfrlist-when-g-concrete
    (implies (fgl-object-case x :g-concrete)
             (equal (fgl-object-bfrlist x) nil))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-boolean
    (implies (fgl-object-case x :g-boolean)
             (equal (fgl-object-bfrlist x)
                    (list (g-boolean->bool x))))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-integer
    (implies (fgl-object-case x :g-integer)
             (equal (fgl-object-bfrlist x)
                    (g-integer->bits x)))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-ite
    (implies (fgl-object-case x :g-ite)
             (equal (fgl-object-bfrlist x)
                    (append (fgl-object-bfrlist (g-ite->test x))
                            (append (fgl-object-bfrlist (g-ite->then x))
                                    (fgl-object-bfrlist (g-ite->else x))))))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-apply
    (implies (fgl-object-case x :g-apply)
             (equal (fgl-object-bfrlist x)
                    (fgl-objectlist-bfrlist (g-apply->args x))))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-var
    (implies (fgl-object-case x :g-var)
             (equal (fgl-object-bfrlist x) nil))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-cons
    (implies (fgl-object-case x :g-cons)
             (equal (fgl-object-bfrlist x)
                    (append (fgl-object-bfrlist (g-cons->car x))
                            (fgl-object-bfrlist (g-cons->cdr x)))))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-object-bfrlist-when-g-map
    (implies (fgl-object-case x :g-map)
             (equal (fgl-object-bfrlist x)
                    (fgl-object-alist-bfrlist (g-map->alist x))))
    :hints (("goal" :expand ((fgl-object-bfrlist x)))))

  (defthm fgl-objectlist-bfrlist-when-consp
    (implies (consp x)
             (equal (fgl-objectlist-bfrlist x)
                    (append (fgl-object-bfrlist (car x))
                            (fgl-objectlist-bfrlist (cdr x)))))
    :hints (("goal" :expand ((fgl-objectlist-bfrlist x)))))

  (defthm fgl-objectlist-bfrlist-when-atom
    (implies (not (consp x))
             (equal (fgl-objectlist-bfrlist x) nil))
    :hints (("goal" :expand ((fgl-objectlist-bfrlist x)))))

  (defthm fgl-object-alist-bfrlist-when-consp
    (implies (consp (car x))
             (equal (fgl-object-alist-bfrlist x)
                    (append (fgl-object-bfrlist (cdar x))
                            (fgl-object-alist-bfrlist (cdr x))))))

  (defthm fgl-object-alist-bfrlist-when-atom
    (implies (not (consp x))
             (equal (fgl-object-alist-bfrlist x) nil)))

  (def-ruleset! fgl-object-bfrlist-when-thms
    '(fgl-object-bfrlist-when-g-concrete
      fgl-object-bfrlist-when-g-boolean
      fgl-object-bfrlist-when-g-integer
      fgl-object-bfrlist-when-g-ite
      fgl-object-bfrlist-when-g-apply
      fgl-object-bfrlist-when-g-cons
      fgl-object-bfrlist-when-g-map
      fgl-objectlist-bfrlist-when-consp
      fgl-objectlist-bfrlist-when-atom
      fgl-object-alist-bfrlist-when-consp
      fgl-object-alist-bfrlist-when-atom))

  (defthm fgl-objectlist-bfrlist-of-cons
    (equal (fgl-objectlist-bfrlist (cons x y))
           (append (fgl-object-bfrlist x)
                   (fgl-objectlist-bfrlist y)))
    :hints (("goal" :expand ((fgl-objectlist-bfrlist (cons x y))))))

  ;; (defthm fgl-objectlist-bfrlist-of-nil
  ;;   (equal (fgl-objectlist-bfrlist nil) nil)
  ;;   :hints (("goal" :expand ((fgl-objectlist-bfrlist nil)))))

  (defthm fgl-object-alist-bfrlist-of-cons
    (equal (fgl-object-alist-bfrlist (cons (cons key val) x))
           (append (fgl-object-bfrlist val)
                   (fgl-object-alist-bfrlist x)))
    :hints (("Goal" :expand ((fgl-object-alist-bfrlist (cons (cons key val) x))))))

  (defthm fgl-object-bfrlist-of-g-concrete
    (equal (fgl-object-bfrlist (g-concrete val)) nil))

  (defthm fgl-object-bfrlist-of-g-boolean
    (equal (fgl-object-bfrlist (g-boolean bool)) (list bool))
    :hints (("goal" :expand ((fgl-object-bfrlist (g-boolean bool))))))

  (defthm fgl-object-bfrlist-of-g-integer
    (equal (fgl-object-bfrlist (g-integer bits))
           (acl2::true-list-fix bits)))

  (defthm fgl-object-bfrlist-of-g-ite
    (equal (fgl-object-bfrlist (g-ite test then else))
           (append (fgl-object-bfrlist test)
                   (append (fgl-object-bfrlist then)
                           (fgl-object-bfrlist else)))))

  (defthm fgl-object-bfrlist-of-g-apply
    (equal (fgl-object-bfrlist (g-apply fn args))
           (fgl-objectlist-bfrlist args)))

  (defthm fgl-object-bfrlist-of-g-var
    (equal (fgl-object-bfrlist (g-var name))nil))

  (defthm fgl-object-bfrlist-of-g-cons
    (equal (fgl-object-bfrlist (g-cons car cdr))
           (append (fgl-object-bfrlist car)
                   (fgl-object-bfrlist cdr))))

  (defthm fgl-object-bfrlist-of-g-map
    (equal (fgl-object-bfrlist (g-map tag alist))
           (fgl-object-alist-bfrlist alist)))

  (in-theory (disable* fgl-object-bfrlist-when-thms))

  (def-ruleset! fgl-object-bfrlist-of-thms
    '(fgl-object-bfrlist-of-g-concrete
      fgl-object-bfrlist-of-g-boolean
      fgl-object-bfrlist-of-g-integer
      fgl-object-bfrlist-of-g-ite
      fgl-object-bfrlist-of-g-apply
      fgl-object-bfrlist-of-g-var
      fgl-object-bfrlist-of-g-cons
      fgl-object-bfrlist-of-g-map
      fgl-objectlist-bfrlist-of-cons
      fgl-object-alist-bfrlist-of-cons
      ;; fgl-objectlist-bfrlist-of-nil
      ))

  (defthm-fgl-object-bfrlist-flag
    (defthm fgl-bfr-object-p-when-fgl-object-p
      (implies (fgl-object-p x)
               (equal (fgl-bfr-object-p x)
                      (bfr-listp (fgl-object-bfrlist x))))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-object-p x))
                         (fgl-object-p x)
                         (fgl-object-bfrlist x))))
      :flag fgl-object-bfrlist)
    (defthm fgl-bfr-objectlist-p-when-fgl-objectlist-p
      (implies (fgl-objectlist-p x)
               (equal (fgl-bfr-objectlist-p x)
                      (bfr-listp (fgl-objectlist-bfrlist x))))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-objectlist-p x))
                         (fgl-objectlist-p x)
                         (fgl-objectlist-bfrlist x))))
      :flag fgl-objectlist-bfrlist)
    (defthm fgl-bfr-object-alist-p-when-fgl-object-alist-p
      (implies (fgl-object-alist-p x)
               (equal (fgl-bfr-object-alist-p x)
                      (bfr-listp (fgl-object-alist-bfrlist x))))
      :hints ('(:expand ((:free (bfrstate) (fgl-bfr-object-alist-p x))
                         (fgl-object-alist-p x)
                         (fgl-object-alist-bfrlist x))))
      :flag fgl-object-alist-bfrlist))

  ;; (defthm-fgl-object-bfrlist-flag
  ;;   (defthm fgl-object-bfrlist-when-symbolic-boolean-free
  ;;     (equal (fgl-object-symbolic-boolean-free x)
  ;;            (equal (fgl-object-bfrlist x) nil))
  ;;     :hints ('(:expand ((fgl-object-bfrlist x)
  ;;                        (fgl-object-symbolic-boolean-free x))))
  ;;     :flag fgl-object-bfrlist)
  ;;   (defthm fgl-objectlist-bfrlist-when-symbolic-boolean-free
  ;;     (equal (fgl-objectlist-symbolic-boolean-free x)
  ;;            (equal (fgl-objectlist-bfrlist x) nil))
  ;;     :hints ('(:expand ((fgl-objectlist-bfrlist x)
  ;;                        (fgl-objectlist-symbolic-boolean-free x))))
  ;;     :flag fgl-objectlist-bfrlist)
  ;;   (defthm fgl-object-alist-bfrlist-when-symbolic-boolean-free
  ;;     (equal (fgl-object-alist-symbolic-boolean-free x)
  ;;            (equal (fgl-object-alist-bfrlist x) nil))
  ;;     :hints ('(:expand ((fgl-object-alist-bfrlist x)
  ;;                        (fgl-object-alist-symbolic-boolean-free x))))
  ;;     :flag fgl-object-alist-bfrlist))
  (local (defthm bfr-list-fix-of-append
           (equal (bfr-list-fix (append a b))
                  (append (bfr-list-fix a) (bfr-list-fix b)))
           :hints(("Goal" :in-theory (enable bfr-list-fix)))))
  (local (defthm bfr-list-fix-of-cons
           (equal (bfr-list-fix (cons a b))
                  (cons (bfr-fix a) (bfr-list-fix b)))
           :hints(("Goal" :in-theory (enable bfr-list-fix)))))

  (local (defthm true-listp-of-bfr-list-fix
           (implies (true-listp x)
                    (true-listp (bfr-list-fix x)))
           :hints(("Goal" :in-theory (enable bfr-list-fix)))))
  
  (defthm-fgl-object-bfrlist-flag
    (defthm fgl-object-bfrlist-of-fgl-bfr-object-fix
      (equal (fgl-object-bfrlist (fgl-bfr-object-fix x))
             (bfr-list-fix (fgl-object-bfrlist x)))
      :hints ('(:expand ((fgl-bfr-object-fix x)
                         (fgl-object-bfrlist x))))
      :flag fgl-object-bfrlist)
    (defthm fgl-objectlist-bfrlist-of-fgl-bfr-objectlist-fix
      (equal (fgl-objectlist-bfrlist (fgl-bfr-objectlist-fix x))
             (bfr-list-fix (fgl-objectlist-bfrlist x)))
      :hints ('(:expand ((fgl-bfr-objectlist-fix x)
                         (fgl-objectlist-bfrlist x))))
      :flag fgl-objectlist-bfrlist)
    (defthm fgl-object-alist-bfrlist-of-fgl-bfr-object-alist-fix
      (equal (fgl-object-alist-bfrlist (fgl-bfr-object-alist-fix x))
             (bfr-list-fix (fgl-object-alist-bfrlist x)))
      :hints ('(:expand ((fgl-bfr-object-alist-fix x)
                         (fgl-object-alist-bfrlist x))))
      :flag fgl-object-alist-bfrlist))

  (defthm fgl-object-bfrlist-of-mk-g-integer
    (implies (not (member v bits))
             (not (member v (fgl-object-bfrlist (mk-g-integer bits)))))
    :hints(("Goal" :in-theory (e/d (mk-g-integer)
                                   (bools->int)))))

  (defthm fgl-object-bfrlist-of-mk-g-cons
    (implies (and (not (member v (fgl-object-bfrlist a)))
                  (not (member v (fgl-object-bfrlist b))))
             (not (member v (fgl-object-bfrlist (mk-g-cons a b)))))
    :hints(("Goal" :in-theory (e/d (mk-g-cons)))))

  (defthm bfr-listp-of-mk-g-boolean
         (implies (bfr-p x)
                  (bfr-listp (fgl-object-bfrlist (mk-g-boolean x))))
         :hints(("Goal" :in-theory (enable mk-g-boolean))))

  (defthm fgl-object-bfrlist-of-gobj-syntactic-boolean-fix
    (implies (not (member v (fgl-object-bfrlist x)))
             (not (member v (fgl-object-bfrlist (mv-nth 1 (gobj-syntactic-boolean-fix x))))))
    :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix)))))

(define fgl-object-bindings-bfrlist ((x fgl-object-bindings-p))
  :returns (bfrlist)
  (if (atom x)
      nil
    (append (and (mbt (and (consp (car x))
                           (pseudo-var-p (caar x))))
                 (fgl-object-bfrlist (cdar x)))
            (fgl-object-bindings-bfrlist (cdr x))))
  ///
  (defthm fgl-object-bindings-bfrlist-of-cons
    (implies (pseudo-var-p var)
             (equal (fgl-object-bindings-bfrlist (cons (cons var val) rest))
                    (append (fgl-object-bfrlist val)
                            (fgl-object-bindings-bfrlist rest)))))

  (defthm bfr-listp-of-fgl-object-bindings-bfrlist
    (implies (fgl-object-bindings-p x)
             (equal (fgl-bfr-object-bindings-p x)
                    (bfr-listp (fgl-object-bindings-bfrlist x))))
    :hints(("Goal" :in-theory (enable fgl-bfr-object-bindings-p
                                      fgl-object-bindings-p))))
    

  (local (in-theory (enable fgl-object-bindings-fix))))




(define bfr-listp-witness (x (bfrstate bfrstate-p))
  (if (atom x)
      'not-a-bfr
    (if (bfr-p (car x))
        (bfr-listp-witness (cdr x) bfrstate)
      (car x)))
  ///
  (defthm bfr-listp-witness-nonnil
    (bfr-listp-witness x bfrstate))

  (local (defthm not-a-bfr-is-not-a-bfr
           (not (bfr-p 'not-a-bfr))
           :hints(("Goal" :in-theory (enable bfr-p aig-p ubddp)))))

  (defthm bfr-listp-witness-not-bfr-p
    (not (bfr-p (bfr-listp-witness x bfrstate) bfrstate)))

  (defthmd bfr-listp-when-not-member-witness
    (implies (not (member (bfr-listp-witness x bfrstate) x))
             (bfr-listp x bfrstate))
    :hints(("Goal" :in-theory (enable bfr-listp))))
  
  (local (defthm member-bfr-list-when-not-bfr-p
           (implies (and (bfr-listp x bfrstate)
                         (not (bfr-p v bfrstate)))
                    (not (member v x)))))

  (defthm not-member-bfr-listp-witness-when-bfr-listp
    (implies (bfr-listp x bfrstate)
             (not (member (bfr-listp-witness y bfrstate) x)))))


(defsection bfrlist-of-fgl-object-accessors
  (local (in-theory (enable* fgl-object-bfrlist-when-thms)))

  (defthm bfrlist-of-g-ite-accessors
    (implies (and (fgl-object-case x :g-ite)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-ite x)))
               (and (not (member v (fgl-object-bfrlist x.test)))
                    (not (member v (fgl-object-bfrlist x.then)))
                    (not (member v (fgl-object-bfrlist x.else)))))))

  (defthm bfrlist-of-g-boolean-accessor
    (implies (and (fgl-object-case x :g-boolean)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-boolean x)))
               (not (equal v x.bool)))))

  (defthm bfrlist-of-g-integer-accessor
    (implies (and (fgl-object-case x :g-integer)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-integer x)))
               (not (member v x.bits)))))

  (defthm bfrlist-of-g-apply-accessor
    (implies (and (fgl-object-case x :g-apply)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-apply x)))
               (not (member v (fgl-objectlist-bfrlist x.args))))))

  (defthm bfrlist-of-g-cons-accessor
    (implies (and (fgl-object-case x :g-cons)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-cons x)))
               (and (not (member v (fgl-object-bfrlist x.car)))
                    (not (member v (fgl-object-bfrlist x.cdr)))))))

  (defthm bfrlist-of-g-map-accessor
    (implies (and (fgl-object-case x :g-map)
                  (not (member v (fgl-object-bfrlist x))))
             (b* (((g-map x)))
               (not (member v (fgl-object-alist-bfrlist x.alist))))))

  (defthm member-fgl-objectlist-bfrlist-of-cdr
    (implies (not (member v (fgl-objectlist-bfrlist x)))
             (not (member v (fgl-objectlist-bfrlist (cdr x)))))
    :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist))))

  (defthm member-fgl-object-bfrlist-of-car
    (implies (not (member v (fgl-objectlist-bfrlist x)))
             (not (member v (fgl-object-bfrlist (car x)))))
    :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist))))

  (defthm member-fgl-object-alist-bfrlist-of-cdr
    (implies (not (member v (fgl-object-alist-bfrlist x)))
             (not (member v (fgl-object-alist-bfrlist (cdr x)))))
    :hints(("Goal" :expand ((fgl-object-alist-bfrlist x)
                            (fgl-object-alist-bfrlist (cdr x))
                            (fgl-object-alist-fix x)))))

  (defthm member-fgl-object-bfrlist-of-cdar
    (implies (not (member v (fgl-object-alist-bfrlist x)))
             (not (member v (fgl-object-bfrlist (cdar x)))))
    :hints(("Goal" :in-theory (enable fgl-object-alist-bfrlist)))))





