; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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

; esim-sexpr-support -- Functions that support esim-faig
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "patterns")
(include-book "centaur/esim/plist" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-vars" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "std/lists/remove-duplicates" :dir :system)
(local (include-book "std/strings/explode-atom" :dir :system))
(set-well-founded-relation nat-list-<)

(defund stringify-atom (x)
  (declare (xargs :guard (atom x)))
  (cond ((symbolp x) (symbol-name x))
        ((stringp x) x)
        ((characterp x) (coerce (list x) 'string))
        ((acl2-numberp x) (coerce (explode-atom x 10) 'string))
        (t "BAD-ATOM")))

(defund stringify (x)
  (declare (xargs :guard t))
  (if (atom x)
      (stringify-atom x)
    (concatenate 'string "(" (stringify (car x)) " . " (stringify (cdr x)) ")")))

(defund stringify-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (stringify (car x))
          (stringify-list (cdr x)))))


(defund prefix-atom (prefix sep x)
  (declare (Xargs :guard (and (stringp prefix) (stringp sep) (atom x))))
  (or (intern-in-package-of-symbol
       (concatenate 'string prefix sep (stringify-atom x))
       'foo)
      'this-prefixing-resulted-in-nil))

(defund prefix-pattern (prefix sep pat)
  (declare (xargs :guard (and (stringp prefix) (stringp sep))))
  (if pat
      (if (atom pat)
          (prefix-atom prefix sep pat)
        (cons (prefix-pattern prefix sep (car pat))
              (prefix-pattern prefix sep (cdr pat))))
    nil))


(defund onset-name (x)
  (declare (xargs :guard (atom x)))
  (intern-in-package-of-symbol
   (concatenate 'string (stringify-atom x) ".1")
   'foo))

(defund offset-name (x)
  (declare (xargs :guard (atom x)))
  (intern-in-package-of-symbol
   (concatenate 'string (stringify-atom x) ".0")
   'foo))


;; Produces a pattern containing fully expanded names for each state bit in a
;; module.  Similar to :full-s.  Should be duplicate-free in well-formed
;; modules.
(mutual-recursion
 (defun mod-state (mod)
   (declare (xargs :guard t
                   :measure (list (acl2-count mod) 3)))
   (if (gpl :x mod)
       (alist-keys (gpl :nst (gpl :x mod)))
     (occs-state (gpl :occs mod))))
 (defun occ-state (occ)
   (declare (xargs :guard t
                   :measure (list (acl2-count occ) 4)))
   (b* ((sop (mod-state (gpl :op occ))))
     (prefix-pattern (stringify (gpl :u occ)) "!" sop)))
 (defun occs-state (occs)
   (declare (Xargs :guard t
                   :measure (list (acl2-count occs) 2)))
   (if (atom occs)
       nil
     (b* ((occ (car occs))
          (s (occ-state occ))
          (rest (occs-state (cdr occs))))
       (if s (cons s rest) rest)))))


(memoize 'mod-state)
(memoize 'occ-state)


;; Collects the flattened list of all signals in a certain keyword of a list of
;; occurrences.  For example, (collect-signal-list :i occs) collects all
;; signals that are input to any occurrence in occs.
(defun collect-signal-list (key occs)
  (declare (xargs :guard (symbolp key)))
  (if (atom occs)
      nil
    (pat-flatten (gpl key (car occs))
                 (collect-signal-list key (cdr occs)))))

(memoize 'collect-signal-list :recursive nil)

(defabbrev driven-signals (mod)
  (collect-signal-list :o (gpl :occs mod)))



;; Produces a pattern containing fully expanded names of all internal signals
;; of a module.
(mutual-recursion
 (defun mod-internals (mod)
   (declare (xargs :guard t
                   :measure (list (acl2-count mod) 0)))
   (if (gpl :occs mod)
       (cons (occs-internals (gpl :occs mod))
             (hons-set-diff (driven-signals mod)
                            (pat-flatten1 (gpl :o mod))))
     (alist-keys (gpl :int (gpl :x mod)))))
 (defun occ-internals (occ)
   (declare (xargs :guard t
                   :measure (list (acl2-count occ) 1)))
   (b* ((sop (mod-internals (gpl :op occ))))
     (prefix-pattern (stringify (gpl :u occ)) "/" sop)))
 (defun occs-internals (occs)
   (declare (Xargs :guard t
                   :measure (list (acl2-count occs) 0)))
   (if (atom occs)
       nil
     (b* ((occ (car occs))
          (occi (occ-internals occ))
          (rest (occs-internals (cdr occs))))
       (if occi (cons occi rest) rest)))))

(memoize 'mod-internals)
(memoize 'occ-internals)

(defun str-prefix-atom (prefix sep x)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp sep)
                              (atom x))))
  (hons-copy (concatenate 'string prefix sep (stringify-atom x))))

(defun str-prefix-pattern (prefix sep pat)
  (declare (XArgs :guard (and (stringp prefix) (stringp sep))))
  (if pat
      (if (atom pat)
          (str-prefix-atom prefix sep pat)
        (cons (str-prefix-pattern prefix sep (car pat))
              (str-prefix-pattern prefix sep (cdr pat))))
    nil))



(mutual-recursion
 (defun module-ind (mod)
   (declare (xargs :measure (list (acl2-count mod) 5)))
   (if (gpl :x mod)
       mod
     (occs-ind (gpl :occs mod))))
 (defun occs-ind (occs)
   (declare (xargs :measure (list (acl2-count occs) 4)))
   (if (atom occs)
       nil
     (cons (occ-ind (car occs))
           (occs-ind (cdr occs)))))
 (defun occ-ind (occ)
   (declare (xargs :measure (list (acl2-count occ) 6)))
   (module-ind (gpl :op occ))))

(flag::make-flag mod-flag module-ind
                 :flag-mapping ((module-ind mod)
                                (occ-ind occ)
                                (occs-ind occs)))

(mutual-recursion
 (defun module1-ind (mod)
   (declare (xargs :measure (list (acl2-count mod) 2)))
   (if (gpl :occs mod)
       (occs1-ind (gpl :occs mod))
     mod))
 (defun occs1-ind (occs)
   (declare (xargs :measure (list (acl2-count occs) 3)))
   (if (atom occs)
       nil
     (cons (occ1-ind (car occs))
           (occs1-ind (cdr occs)))))
 (defun occ1-ind (occ)
   (declare (xargs :measure (list (acl2-count occ) 3)))
   (module1-ind (gpl :op occ))))

(flag::make-flag mod1-flag module1-ind
                 :flag-mapping ((module1-ind mod)
                                (occ1-ind occ)
                                (occs1-ind occs)))


(defsection occmap
  ;; Produces a fast alist mapping occurrence names to occurrences.
  (defun occmap1 (occs)
    (declare (xargs :guard t))
    (if (atom occs)
        nil
      (hons-acons (gpl :u (car occs)) (car occs)
                  (occmap1 (cdr occs)))))

  (defun occmap (mod)
    (declare (xargs :guard t))
    (occmap1 (gpl :occs mod)))

  (memoize 'occmap)

  (defthmd consp-alist-keys-implies-occs
    (implies (consp (alist-keys (occmap mod)))
             (consp (gpl :occs mod)))
    :hints(("Goal" :in-theory (enable occmap))))


  (defabbrev occs-for-names (names mod)
    (alist-vals (fal-extract names (occmap mod))))

  (defabbrev mod-occs (mod)
    (occs-for-names (alist-keys (occmap mod)) mod)))





;; Pattern-to-int-varmap:  Produces an alist mapping each atom in pat to a pair
;; of indices that are unique (as long as idx is greater than the max index in
;; varmap, the accumulator.)  Atoms that are repeated are only bound once.
(defun pattern-to-int-varmap (pat varmap idx)
  (declare (Xargs :guard (acl2-numberp idx)))
  (b* (((when (not pat)) (mv varmap idx))
       ((when (atom pat))
        (if (hons-get pat varmap)
            (mv varmap idx)
          (mv (hons-acons pat (cons idx (1+ idx)) varmap)
              (+ 2 idx))))
       ((mv varmap idx) (pattern-to-int-varmap (cdr pat) varmap idx)))
    (pattern-to-int-varmap (car pat) varmap idx)))

(local
 (defthm numberp-pattern-to-int-varmap-idx
  (implies (acl2-numberp idx)
           (acl2-numberp
            (mv-nth 1 (pattern-to-int-varmap pat varmap idx))))))


;; Esim-faig-int-varmap-occs repeats pattern-to-int-varmap over all the inputs
;; and outputs of occurrences named by occnames within mod.
(defun esim-faig-int-varmap-occs (mod occnames varmap idx)
  (declare (xargs :guard (acl2-numberp idx)))
  (if (atom occnames)
      (mv varmap idx)
    (b* ((occ (cdr (hons-get (car occnames) (occmap mod))))
         ((mv varmap idx) (pattern-to-int-varmap (gpl :i occ) varmap idx))
         ((mv varmap idx) (pattern-to-int-varmap (gpl :o occ) varmap idx)))
      (esim-faig-int-varmap-occs mod (cdr occnames) varmap idx))))







(local
 (defthm true-listp-collect-signal-list
   (true-listp (collect-signal-list k occs))))



(defconst *known-esim-x-ops*
  '(x-identity
    x-true x-false x-float x-unknown x-buf x-not x-and x-or x-xor x-mux
    x-t-wire x-pullup x-ft-buf x-ff x-latch+ x-latch- x-latch-+
    x-reg x-res x-ram))

(defun alist-keys-are-p (x y)
  ;; Stupid fused operation to avoid building the alist-keys
  (declare (xargs :guard t))
  (mbe :logic (equal (alist-keys x) y)
       :exec
       (if (atom x)
           (not y)
         (if (atom (car x))
             (alist-keys-are-p (cdr x) y)
           (and (consp y)
                (equal (caar x) (car y))
                (alist-keys-are-p (cdr x) (cdr y)))))))

(defund good-esim-primitivep (mod)
  (declare (Xargs :guard t))
  (b* ((x (gpl :x mod))
       (out (gpl :out x))
       (nst (gpl :nst x))
       (flat-mod-state (pat-flatten1 (mod-state mod))))
    (and (mbe :logic (equal (alist-keys nst) flat-mod-state)
              :exec  (alist-keys-are-p nst flat-mod-state))
         (mbe :logic (equal (alist-keys out) (pat-flatten1 (gpl :o mod)))
              :exec  (alist-keys-are-p out (pat-flatten1 (gpl :o mod))))
         (alistp nst)
         (alistp out)
         (hons-subset (4v-sexpr-vars-list (append (alist-vals nst)
                                               (alist-vals out)))
                      (mbe :logic
                           (append (pat-flatten1 (gpl :i mod))
                                   flat-mod-state)
                           :exec
                           (pat-flatten (gpl :i mod) flat-mod-state))))))

;; good-esim-modulep is a general well-formedness check for module x.
(mutual-recursion
 (defun good-esim-modulep (x)
   (declare (xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count x) 3)))
   ;; BOZO can we optimize this flattening?
   (b* ((sts (pat-flatten1 (mod-state x)))
        (ins (pat-flatten1 (gpl :i x)))
        (outs (pat-flatten1 (gpl :o x)))
        (occmap (occmap x))
        ((with-fast occmap)))
     (and (not (hons-dups-p (append ins outs sts)))
          ;; (not (hons-intersect-p sts ins))
          ;; (not (hons-intersect-p sts outs))
          ;; (not (hons-intersect-p ins outs))
            (let* ((occs (alist-vals
                          (fal-extract
                           (alist-keys occmap)
                           occmap)))
                   (driven (collect-signal-list :o occs)))
              (and (not (hons-dups-p (alist-keys occmap)))
                   (good-esim-occsp (gpl :occs x))
                   (not (hons-dups-p (append ins sts driven)))
                   (if (gpl :x x)
                       (good-esim-primitivep x)
                     (and (hons-subset
                           (collect-signal-list :i occs)
                           (append ins driven))
                          (hons-subset outs driven))))))))

 (defun good-esim-occp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 4)))
   (and (similar-patternsp (gpl :i (gpl :op x)) (gpl :i x))
        (similar-patternsp (gpl :o (gpl :op x)) (gpl :o x))
        (gpl :u x)
        (good-esim-modulep (gpl :op x))))

 (defun good-esim-occsp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 2)))
   (or (atom x)
       (and (good-esim-occp (car x))
            (good-esim-occsp (cdr x))))))

(memoize 'good-esim-modulep :condition '(gpl :occs x))

(in-theory (disable good-esim-modulep))




;; JCD BOZO can we get rid of esim-probe and switch everything to new-probe?

(mutual-recursion
 (defun good-esim-probe-modulep (x)
   (declare (xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count x) 3)
                   :hints (("goal" :in-theory
                            (disable mod-internals occ-internals
                                     good-esim-modulep
                                     hons-dups-p)))))
   (mbe :logic
        (let ((internals (pat-flatten1 (mod-internals x)))
              (ins (pat-flatten1 (gpl :i x)))
              (outs (pat-flatten1 (gpl :o x))))
          (and (not (hons-dups-p (append ins outs internals)))
               (good-esim-probe-occsp (gpl :occs x))))
        :exec
        ;; This just avoids the append above by using accumulators to do the
        ;; flattening.
        (and (not (hons-dups-p
                   (pat-flatten (gpl :i x)
                                (pat-flatten (gpl :o x)
                                             (pat-flatten1 (mod-internals x))))))
             (good-esim-probe-occsp (gpl :occs x)))))

 (defun good-esim-probe-occp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 4)))
   (and (let ((internals (pat-flatten1 (occ-internals x)))
              (ins (pat-flatten1 (gpl :i x)))
              (outs (pat-flatten1 (gpl :o x))))
          (and (not (hons-dups-p internals))
               (not (hons-intersect-p ins internals))
               (not (hons-intersect-p outs internals))))
        (good-esim-probe-modulep (gpl :op x))))

 (defun good-esim-probe-occsp (x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 2)))
   (or (atom x)
       (and (good-esim-probe-occp (car x))
            (good-esim-probe-occsp (cdr x))))))

(memoize 'good-esim-probe-modulep :condition '(gpl :occs x))




(defun bad-esim (x)
  (declare (Xargs :guard t))
  x)

(defmacro bad-esim-msg (&rest args)
  `(bad-esim (msg . ,args)))

;; good-esim-modulep is a general well-formedness check for module x.
(mutual-recursion
 (defun bad-esim-modulep (x)
   (declare (xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count x) 3)))
   (let ((sts (pat-flatten1 (mod-state x)))
         (ins (pat-flatten1 (gpl :i x)))
         (outs (pat-flatten1 (gpl :o x))))
     (or (and (hons-intersect-p sts ins)
              (bad-esim-msg
               "Inputs/states intersect in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-intersection sts ins)))
         (and (hons-intersect-p sts outs)
              (bad-esim-msg
               "Outputs/states intersect in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-intersection sts outs)))
         (and (hons-intersect-p ins outs)
              (bad-esim-msg
               "Inputs/outputs intersect in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-intersection ins outs)))
         (and (hons-dups-p ins)
              (bad-esim-msg
               "Inputs contain duplicates in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-duplicates ins)))
         (and (hons-dups-p outs)
              (bad-esim-msg
               "Outputs contain duplicates in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-duplicates outs)))
         (and (hons-dups-p sts)
              (bad-esim-msg
               "States contain duplicates in ~x0.  Names: ~x1~%"
               (gpl :n x) (hons-duplicates sts)))
         (let* ((occs (alist-vals
                       (fal-extract
                        (alist-keys (occmap x))
                        ;; Jared: sometimes this wasn't fast.
                        (make-fast-alist (occmap x)))))
                (driven (collect-signal-list :o occs)))
           (or  (and (hons-dups-p (alist-keys (occmap x)))
                     (bad-esim-msg
                      "Duplicates in occurrence names of ~x0. Names: ~x1~%"
                      (gpl :n x) (hons-dups-p (alist-keys (occmap x)))))
                (bad-esim-occsp (gpl :n x) (gpl :occs x))
                (and (hons-intersect-p ins driven)
                     (bad-esim-msg
                      "Inputs/driven signals intersect in ~x0.  Names: ~x1~%"
                      (gpl :n x) (hons-intersection ins driven)))
                (and (hons-intersect-p sts driven)
                     (bad-esim-msg
                      "States/driven signals intersect in ~x0.  Names: ~x1~%"
                      (gpl :n x) (hons-intersection sts driven)))
                (and (hons-dups-p driven)
                     (bad-esim-msg
                      "Duplicates in driven signals of ~x0. Names: ~x1~%"
                      (gpl :n x) (hons-dups-p driven)))
                (if (gpl :x x)
                    (and (not (good-esim-primitivep x))
                         (bad-esim-msg
                          "Unrecognized primitive operator ~x0 in ~x1~%"
                          (gpl :x x) (gpl :n x)))
                  (or (and (not (hons-subset
                                 (collect-signal-list :i occs)
                                 (append ins driven)))
                           (bad-esim-msg
                            "Undriven occurrence inputs in ~x0. Names: ~x1~%"
                            (gpl :n x) (hons-set-diff
                                        (collect-signal-list :i occs)
                                        (append ins driven))))
                      (and (not (hons-subset outs driven))
                           (bad-esim-msg
                            "Undriven output in ~x0. Names: ~x1~%"
                            (gpl :n x) (hons-set-diff outs driven))))))))))

 ;; Jared: added name so we can see where the error is.
 (defun bad-esim-occp (name x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 4)))
   (or (and (not (similar-patternsp (gpl :i (gpl :op x)) (gpl :i x)))
            (bad-esim-msg "In module ~x0.  input patterns mismatch in occ ~x1.~%"
                          name (gpl :u x)))
       (and (not (similar-patternsp (gpl :o (gpl :op x)) (gpl :o x)))
            (bad-esim-msg "In module ~x0, output patterns mismatch in occ ~x1.~%"
                          name (gpl :u x)))
       (and (not (gpl :u x))
            (bad-esim-msg "In module ~x0, unnamed occurrence: ~x1~%" name x))
       (bad-esim-modulep (gpl :op x))))

 (defun bad-esim-occsp (name x)
   (declare (xargs :guard t
                   :measure (list (acl2-count x) 2)))
   (and (not (atom x))
        (or (bad-esim-occp name (car x))
            (bad-esim-occsp name (cdr x))))))

(memoize 'bad-esim-modulep)

(make-flag flag-bad-esim-modulep
           bad-esim-modulep
           :flag-mapping ((bad-esim-modulep mod)
                          (bad-esim-occp occ)
                          (bad-esim-occsp occs)))

(defthm-flag-bad-esim-modulep
  (defthm bad-esim-modulep-to-good-esim-modulep
    (iff (bad-esim-modulep x)
         (not (good-esim-modulep x)))
    :flag mod)
  (defthm bad-esim-occp-to-good-esim-occp
    (iff (bad-esim-occp name x)
         (not (good-esim-occp x)))
    :flag occ)
  (defthm bad-esim-occsp-to-good-esim-occsp
    (iff (bad-esim-occsp name x)
         (not (good-esim-occsp x)))
    :flag occs)
  :hints(("Goal"
          :in-theory (e/d (good-esim-modulep)
                          (hons-intersect-p hons-dups-p
                                            hons-member-equal)))))







(defthm true-listp-append-iff
  (iff (true-listp (append a b))
       (true-listp b)))

(defun esim-mod-occs-guard (mod occs)
  (declare (xargs :guard t))
  (and (or (atom occs) (consp (gpl :occs mod)))
       (good-esim-modulep mod)
       (true-listp occs)
       (subsetp-equal
        occs (alist-keys (occmap mod)))))






;; These functions are useful for EMOD compatibility.


;; Removes duplicate occurrences in the module and reduces the fields to the
;; subset that have semantic meaning in ESIM-FAIG (mostly.  Actually, :n and
;; :full-s are unused and :s is unused in non-primitives.)
(mutual-recursion
 (defun mod-reduce (mod)
   (declare (xargs :guard t))
   (if (gpl :occs mod)
       (let ((occs (occs-reduce (hons-remove-duplicates
                                 (gpl :occs mod)))))
         (chgpl :occs occs mod))
     mod))
 (defun occs-reduce (occs)
   (declare (xargs :guard t))
   (if (atom occs)
       nil
     (let* ((occ (car occs))
            (mod (mod-reduce (gpl :op occ)))
            (occ1 (chgpl :op mod occ)))
       (cons occ1 (occs-reduce (cdr occs)))))))

(memoize 'mod-reduce :condition '(gpl :occs mod))



;; Mod-fix-t-f adds occurrences driving T and F signals, as necessary, in
;; modules that use T and F to represent constant-true and constant-false
;; signals.  These occurrences are only added if no occurrence drives the
;; respective signals.

(defconst *true-occ*
  '(:u true-supply :op (:n *true* :i nil :o o :x x-true)
       :i nil :o t))

(defconst *false-occ*
  '(:u false-supply :op (:n *false* :i nil :o o :x x-false)
       :i nil :o f))

(defun find-in-occs-field (key name occs)
  (declare (xargs :guard (and (symbolp key) (symbolp name))))
  (if (atom occs)
      nil
    (or (member-of-pat-flatten name (gpl key (car occs)))
        (find-in-occs-field key name (cdr occs)))))

(mutual-recursion
 (defun mod-fix-t-f (mod)
   (declare (xargs :guard t))
   (b* ((occs (gpl :occs mod))
        ((when (not occs)) mod)
        (t-used   (find-in-occs-field :i t occs))
        (t-driven (find-in-occs-field :o t occs))
        (f-used   (find-in-occs-field :i 'f occs))
        (f-driven (find-in-occs-field :o 'f occs))
        (occs (occs-fix-t-f occs))
        (occs (append (and t-used (not t-driven) (list *true-occ*))
                      (and f-used (not f-driven) (list *false-occ*))
                      occs)))
     (chgpl :occs occs mod)))
 (defun occs-fix-t-f (occs)
   (declare (xargs :guard t))
   (if (atom occs)
       nil
     (let* ((occ (car occs))
            (mod (mod-fix-t-f (gpl :op occ)))
            (occ1 (chgpl :op mod occ)))
       (cons occ1 (occs-fix-t-f (cdr occs)))))))

(memoize 'mod-fix-t-f)



(defun sexpr-res-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((atom x) *4vz-sexpr*)
        ((atom (cdr x)) (car x))
        (t (xxxjoin 'res x))))


;; BOZO redundant definitions also in ram-primitives, which includes this book
(defun ram-st-from-i-o (i o)
  (declare (xargs :guard t))
  (list i o))

(defun ram-o-from-st (s)
  (declare (xargs :guard t))
  (mbe :logic (cadr s)
       :exec (if (and (consp s)
                      (consp (cdr s)))
                 (cadr s)
               (er hard? 'ram-o-from-st "malformed primitive ram state"))))

(defun ram-i-from-st (s)
  (declare (xargs :guard t))
  (mbe :logic (car s)
       :exec (if (consp s)
                 (car s)
               (er hard? 'ram-o-from-st "malformed primitive ram state"))))



(defun esim-colon-x-replacement (i s o x)
  (declare (Xargs :guard t))
  (hons-copy
   (if (consp x)
       x
     (case x
       (x-identity  '(:out ((o . a))))
       (x-true      `(:out ((o . ,*4vt-sexpr*))))
       (x-false     `(:out ((o . ,*4vf-sexpr*))))
       (x-float     `(:out ((o . ,*4vz-sexpr*))))
       (x-unknown   `(:out ((o . ,*4vx-sexpr*))))
       (x-buf       '(:out ((o . (buf a)))))
       (x-not       '(:out ((o . (not a)))))
       (x-and       '(:out ((o . (and a b)))))
       (x-or        '(:out ((o . (or a b)))))
       (x-xor       '(:out ((o . (xor a b)))))
       (x-mux       '(:out ((o . (ite a b c)))))
       (x-t-wire    '(:out ((o . (res a b)))))
       (x-pullup    '(:out ((o . (pullup a)))))
       (x-ft-buf    '(:out ((b . (tristate cntl in)))))
       (x-ff        '(:nst ((s . a)) :out ((o . s))))
;; should these below be ITE*, perhaps?
       (x-latch+    '(:nst ((s . (ite clk d s)))
                           :out ((q . (ite clk d s))
                                 (qn . (not (ite clk d s))))))
       (x-latch-    '(:nst ((s . (ite clk s d)))
                           :out ((q . (ite clk d s))
                                 (qn . (not (ite clk d s))))))
       (x-latch-+   '(:nst ((s- . (ite clk s- d))
                            (s+ . (ite clk s- s+)))
                           :out ((q . (ite clk s- s+))
                                 (qn . (not (ite clk s- s+))))))
       (x-reg       '(:nst ((s- . (ite clk s- d))
                            (s+ . (ite clk s- s+)))
                           :out ((q . (ite clk s- s+)))))
       (x-res       `(:out ((o . ,(sexpr-res-list (pat-flatten1 i))))))
       (x-ram       `(:nst ,(append (pairlis$ (pat-flatten1 (ram-i-from-st s))
                                              (pat-flatten1 i))
                                    (pairlis$ (pat-flatten1 (ram-o-from-st s))
                                              nil))
                      :out ,(pairlis$ (pat-flatten1 o)
                                      (pat-flatten1 (ram-o-from-st s)))))
       (otherwise   (or x '(:out nil)))))))



(mutual-recursion
 (defun primitives-to-esim (mod)
   (declare (Xargs :guard t
                   :well-founded-relation nat-list-<
                   :measure (list (acl2-count mod) 2)))
   (if (gpl :x mod)
       (chgpl :x (esim-colon-x-replacement
                  (gpl :i mod) (gpl :s mod) (gpl :o mod) (gpl :x mod))
              mod)
     (chgpl :occs (primitives-to-esim-occs (gpl :occs mod)) mod)))

 (defun primitives-to-esim-occs (occs)
   (declare (xargs :guard t
                   :measure (list (acl2-count occs) 1)))
   (if (atom occs)
       nil
     (cons (primitives-to-esim-occ (car occs))
           (primitives-to-esim-occs (cdr occs)))))

 (defun primitives-to-esim-occ (occ)
   (declare (xargs :guard t
                   :measure (list (acl2-count occ) 3)))
   (chgpl :op (primitives-to-esim (gpl :op occ)) occ)))

(memoize 'primitives-to-esim)


(defun fix-emod-for-esim (mod)
  (declare (xargs :guard t))
  (if (good-esim-modulep mod)
      mod
    (prog2$
     (cw "Warning: Fixing ~x0 for esim.~%" (gpl :n mod))
     (primitives-to-esim
      (mod-fix-t-f
       (mod-reduce mod))))))




(defabbrev esim-driven-signals (mod)
  (collect-signal-list :o (alist-vals (fal-extract
                                       (alist-keys (occmap mod))
                                       (occmap mod)))))

(defabbrev esim-get-occ (occ mod)
  (cdr (mbe :logic (hons-assoc-equal occ (occmap mod))
            :exec (hons-get occ (occmap mod)))))



(defun bool-to-4v (x)
  (declare (xargs :guard t))
  (if x *4vt* *4vf*))

(defun bool-to-4v-lst (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (bool-to-4v (car x))
          (bool-to-4v-lst (cdr x)))))

(defun bool-to-4v-sexpr (x)
  (declare (xargs :guard t))
  (if x *4vt-sexpr* *4vf-sexpr*))

(defun bool-to-4v-sexpr-lst (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (bool-to-4v-sexpr (car x))
          (bool-to-4v-sexpr-lst (cdr x)))))


