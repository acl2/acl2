; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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

(in-package "SV")

(include-book "structure")
(include-book "../moddb")
(include-book "centaur/esim/stv/stv-util" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/strrpos" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(local (in-theory (disable nth update-nth)))
(local (include-book "centaur/misc/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))

(defxdoc expand.lisp :parents (svex-stvs))
(local (xdoc::set-default-parents expand.lisp))

(define svtv-mod-alias-guard ((modidx natp) (moddb moddb-ok) aliases)
  :enabled t
  (flet ((fn (modidx moddb aliases)
             (and (< (lnfix modidx) (lnfix (moddb->nmods moddb)))
                  (<= (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                 (nwires)
                                 (elab-mod->totalwires elab-mod)
                                 nwires)
                      (aliass-length aliases)))))
    (mbe :logic (non-exec (let ((moddb (moddb-fix moddb)))
                            (fn modidx moddb aliases)))
         :exec (fn modidx moddb aliases))))

(define svtv-hiername-rtokens->path ((x acl2::string-listp)
                                     (acc path-p))
  :returns (path path-p)
  :guard-hints (("goal" :in-theory (enable name-p)))
  (if (atom x)
      (path-fix acc)
    (svtv-hiername-rtokens->path
     (cdr x) (make-path-scope :namespace (acl2::str-fix (car x))
                              :subpath acc))))


(define svtv-hiername-parse ((x stringp) (last natp))
  :prepwork ((local (defthm true-listp-cdr
                      (implies (true-listp x)
                               (true-listp (cdr x)))))
             (local (defthm string-listp-of-cdr
                      (implies (string-listp x)
                               (string-listp (cdr x)))))
             (local (defthm stringp-car-of-string-listp
                      (implies (and (string-listp x) (consp x))
                               (stringp (car x)))))
             (local (in-theory (enable name-p))))
  :guard (<= last (length x))
  :returns (path path-p)
  (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
       (last (lnfix last))
       (rtokens (str::strtok-aux x 0 last '(#\.) nil nil)))
    (if (consp rtokens)
        (svtv-hiername-rtokens->path (cdr rtokens)
                                     (make-path-wire :name (car rtokens)))
      (prog2$ (raise "Bad hierarchical name: ~s0" x)
              "bad-path"))))


(define svtv-wire-parse ((x stringp))
  :prepwork ((local (defthm acl2::string-listp-of-cdr
                      (implies (acl2::string-listp x)
                               (acl2::string-listp (cdr x)))))
             (local (defthm stringp-car-of-string-listp
                      (implies (and (string-listp x) (consp x))
                               (stringp (car x)))))
             (local (in-theory (enable maybe-natp))))
  :Returns (mv errmsg
               (path path-p "string or path of hierarchical strings")
               (lsb  maybe-natp :rule-classes :type-prescription
                     "lsb of range or nil")
               (width maybe-natp :rule-classes :type-prescription
                      "width of range or nil")
               (revp "is the range backward"))
  :guard-debug t
  (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
       (len (length x))
       ((when (eql len 0)) (mv "Empty wirename?" "bad-path" nil nil nil))
       ((unless (eql (char x (1- len)) #\]))
        (mv nil (svtv-hiername-parse x len) nil nil nil))
       (openbrace (str::strrpos "[" x))
       ((unless (and openbrace
                     (< openbrace (1- len))))
        (mv "] without [" "bad-path" nil nil nil))
       (path (svtv-hiername-parse x openbrace))
       (nums (str::strtok-aux x (+ 1 openbrace) (1- len) '(#\:) nil nil))
       ((when (or (atom nums) (> (len nums) 2)))
        (mv "failed to tokenize 1 or 2 indices" "bad-path" nil nil nil))
       (lsb (str::strval (car nums)))
       ((unless lsb)
        (mv "non-number as lsb index" "bad-path" nil nil nil))
       (msb (if (consp (cdr nums))
                (str::strval (cadr nums))
              lsb))
       ((unless msb)
        (mv "non-number as msb index" "bad-path" nil nil nil))
       ;; ;; BOZO for reversed indices we're not really doing the right thing
       ;; (- (and (< msb lsb)
       ;;         (raise "Reversed indices not yet implemented")))
       (width (+ 1 (abs (- msb lsb))))
       (revp (< msb lsb)))
    ;; ==Backward Range Convention==
    (mv nil path lsb width revp))
  ///
  (defthm width-when-lsb-of-svtv-wire-parse
    (b* (((mv & & lsb width &) (svtv-wire-parse x)))
      (and (iff width lsb)
           (iff (rationalp width) lsb)
           (iff (acl2-numberp width) lsb)
           (iff (integerp width) lsb)
           (iff (natp width) lsb)))))

(define svtv-1wire->lhs ((x stringp) (modidx natp) (moddb moddb-ok) aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv err
               (lhs lhs-p))
  (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
       ((mv err path lsb width revp) (svtv-wire-parse x))
       ((when err) (mv err nil))
       (wireidx (moddb-path->wireidx path modidx moddb))
       ((unless wireidx)
        (mv (msg "Wire not found: ~s0" x) nil))
       (wire    (moddb-path->wiredecl path modidx moddb))
       ((wire wire) wire)
       ((when (and lsb (< 1 width) (< 1 wire.width)
                   (xor revp wire.revp)))
        (mv (msg "Wire ~s0: Declared and STV ranges are opposite oriented~%" x)
            nil))
       (wire-lsb (if wire.revp
                     (+ -1 wire.width wire.low-idx)
                   wire.low-idx))
       (lsb (or lsb wire-lsb))
       (width (or width wire.width))
       (shift (if wire.revp (- wire-lsb lsb) (- lsb wire-lsb)))
       ((when (< shift 0))
        (mv (msg "Wire ~s0: LSB out of bounds" x) nil))
       ((when (> (+ shift width) wire.width))
        (mv (msg "Wire ~s0: MSB out of bounds" x) nil))
       (alias (get-alias wireidx aliases)))
    (mv nil (lhs-concat width (lhs-rsh shift alias) nil))))


(define svtv-concat->lhs ((x string-listp) (modidx natp) (moddb moddb-ok) aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs
               (lhs lhs-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv err1 first) (svtv-1wire->lhs (car x) modidx moddb aliases))
       ((mv errs rest) (svtv-concat->lhs (cdr x) modidx moddb aliases)))
    (if err1
        (mv (cons err1 errs) nil)
      (mv nil (append first rest)))))

(define svtv-wire->lhs (x (modidx natp) (moddb moddb-ok) aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs
               (lhs lhs-p))
  (b* (((unless (stringp x))
        (mv (list (msg "SVTV wirenames must be strings; ~x0 is not" x)) nil))
       (toks (str::strtok x '(#\, #\Newline #\Tab #\Space #\{ #\})))
       ((mv errs lhs) (svtv-concat->lhs toks modidx moddb aliases)))
    (mv errs (lhs-norm lhs))))


(define msg-list ((x "list of msg objects"))
  :returns (msg "single msg object containing the list")
  (if (atom x)
      ""
    (if (car x)
        (msg "~@0~%~@1" (car x) (msg-list (cdr x)))
      (msg-list (cdr x)))))

(define svtv-wires->lhses ((entries true-list-listp)
                           (modidx natp)
                           (moddb moddb-ok)
                           aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs (in-entries svtv-lines-p))
  (b* (((when (atom entries)) (mv nil nil))
       (name (caar entries))
       ((mv errs lhs) (svtv-wire->lhs name modidx moddb aliases))
       (entrylist (mbe :logic (list-fix (cdar entries))
                       :exec (cdar entries)))
       ((mv rest-errs rest) (svtv-wires->lhses (cdr entries) modidx moddb aliases))
       ((unless (svtv-entrylist-p entrylist))
        (mv (cons (msg "Bad inentrylist: ~x0" entrylist)
                  (append-without-guard errs rest-errs))
            rest))
       (entry (make-svtv-line :lhs lhs :entries entrylist)))
    (mv (append-without-guard errs rest-errs)
        (cons entry rest)))

  :verbosep t
  :hooks ((:fix :hints (("goal" :in-theory (e/d (true-list-list-fix)
                                                (double-containment)))))))


(define svtv-max-length ((x svtv-lines-p))
  :returns (max natp :rule-classes :type-prescription)
  :hooks ((:fix :hints (("goal" :in-theory (enable svtv-lines-fix)))))
  (if (atom x)
      0
    (max (len (svtv-line->entries (car x)))
         (svtv-max-length (cdr x)))))

;; This does the following several things:
;; -- Extends the line to the simulation length
;; -- Normalizes ~ entries to their values
;; -- Shortens all constant values to their LHS width.
;; Lastval is the last normalized value.  Lastent is the last actual entry,
;; which might be ~ where the lastval is 1 or 0, e.g.
(define svtv-extend-entrylist ((x svtv-entrylist-p)
                               (len natp)
                               (lastval svtv-entry-p)
                               (lastent svtv-entry-p)
                               (width natp))
  :prepwork ((local (defthm svtv-entry-p-when-4vec-p
                      (implies (4vec-p x)
                               (svtv-entry-p x))
                      :hints(("Goal" :in-theory (enable svtv-entry-p))))))
  :hooks ((:fix :hints (("goal" :in-theory (enable svtv-entrylist-fix)))))
  :returns (xx svtv-entrylist-p)
  (b* (((when (zp len)) nil)
       (lastval (svtv-entry-fix lastval))
       (lastent (svtv-entry-fix lastent))
       (ent (if (consp x) (svtv-entry-fix (car x)) lastent))
       (val (if (and (symbolp ent) (equal (symbol-name ent) "~"))
                (if (4vec-p lastval)
                    (4vec-bitnot lastval)
                  (prog2$ (raise "Toggle entries (~) must be preceded by a constant value")
                          'acl2::_))
              ent))
       (val (if (4vec-p val)
                (4vec-zero-ext (2vec (lnfix width)) val)
              val)))
    (cons val (svtv-extend-entrylist (cdr x) (1- len) val ent width)))
  ///
  (defthm len-of-svtv-extend-entrylist
    (equal (len (svtv-extend-entrylist x len lastval lastent width))
           (nfix len))))


(define svtv-expand-lines ((x svtv-lines-p) (len natp))
  :returns (xx svtv-lines-p)
  :hooks ((:fix :hints (("goal" :in-theory (enable svtv-lines-fix)))))
  (if (atom x)
      nil
    (cons (change-svtv-line
           (car x)
           :entries (svtv-extend-entrylist
                     (svtv-line->entries (car x)) len 'acl2::_ 'acl2::_
                     (lhs-width (svtv-line->lhs (car x)))))
          (svtv-expand-lines (cdr x) len))))

(define svtv-lines->overrides ((x svtv-lines-p) (index natp))
  :returns (mv (svtv-ovs svtv-overridelines-p)
               (lhs-ovs lhs-overridelist-p))
  :hooks ((:fix :hints (("goal" :in-theory (enable svtv-lines-fix)))))
  (b* (((when (atom x)) (mv nil nil))
       ((svtv-line xf) (car x))
       (testvar (make-svar :name `(:svtv-override-test . ,(lnfix index))))
       (valvar  (make-svar :name `(:svtv-override-val . ,(lnfix index))))
       (ov (make-lhs-override :lhs xf.lhs
                              :test (svex-var testvar)
                              :val (svex-var valvar)))
       ((mv svtv-ovs lhs-ovs)
        (svtv-lines->overrides (cdr x) (1+ (lnfix index)))))
    (mv (cons (make-svtv-overrideline
               :lhs xf.lhs
               :test testvar
               :val valvar
               :entries xf.entries)
              svtv-ovs)
        (cons ov lhs-ovs))))



