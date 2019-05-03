; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "structure")
(include-book "../mods/moddb")
;; (include-book "centaur/esim/stv/stv-util" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/strrpos" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(local (in-theory (disable nth update-nth)))
(local (include-book "std/basic/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))

(defxdoc expand.lisp :parents (svex-stvs))
(local (xdoc::set-default-parents expand.lisp))

(define svtv-parse-path-indices ((bracketed-parts string-listp
                                                  "strings of the form \"[123\"")
                                 (lastp booleanp)
                                 (orig-x stringp))
  :prepwork ((local (defthm len-of-nthcdr
                      (equal (len (nthcdr n x))
                             (max 0 (- (len x) (nfix n))))
                      :hints(("Goal" :in-theory (enable nthcdr)
                              :induct (nthcdr n x)))))
             (local (defthm len-equal-0
                      (equal (equal (len x) 0)
                             (not (consp x)))))
             (local (in-theory (disable (tau-system)))))
  :guard (consp bracketed-parts)
  :returns (mv errmsg
               (path (implies path (path-p path)))
               (range-msb (or (not range-msb) (natp range-msb))
                          :rule-classes :type-prescription)
               (range-lsb (implies range-msb (natp range-lsb))
                          :rule-classes :type-prescription))
  :measure (len bracketed-parts)
  :ruler-extenders :lambdas
  :verify-guards nil
  (b* ((orig-x (mbe :logic (acl2::str-fix orig-x) :exec orig-x))
       ((mv err rest range-msb range-lsb)
        (if (atom (cdr bracketed-parts))
            (mv nil nil nil nil)
          (svtv-parse-path-indices (cdr bracketed-parts) lastp orig-x)))
       ((when err) (mv err nil nil nil))
       (first (mbe :logic (acl2::str-fix (car bracketed-parts))
                   :exec (car bracketed-parts)))
       ((unless (and (not (equal first ""))
                     (eql (char first 0) #\[)))
        (mv (msg "Missing [ at \"~s0]\" (inside \"~s1\"" first orig-x)
            nil nil nil))
       ((mv first-index first-digits)
        (str::parse-nat-from-string first 0 0 1 (length first)))
       ((when (eql 0 first-digits))
        (mv (msg "Missing index in \"~s0]\" (inside \"~s1\"" first orig-x)
            nil nil nil))
       ((when (equal (+ 1 first-digits) (length first)))
        ;; The whole first string was something like "[324".
        (mv nil
            (if rest
                (make-path-scope :namespace first-index :subpath rest)
              (make-path-wire :name first-index))
            range-msb range-lsb))
       ;; There was more to it than the index.  The only time this is allowed is if
       ;; this is the absolute last index and we have a partselect.
       ((unless (and lastp (atom (cdr bracketed-parts))))
        (mv (msg "Bad format for index: \"~s0]\" inside \"~s1\".  If this is ~
                  a partselect, they are only allowed last."
                 first orig-x)
            nil nil nil))
       ((unless (eql (char first (+ 1 first-digits)) #\:))
        (mv (msg "Bad format for last index \"~s0]\" of \"~s1\"."
                 first orig-x)
            nil nil nil))
       ((mv second-index second-digits)
        (str::parse-nat-from-string first 0 0 (+ 2 first-digits) (length first)))
       ((when (eql 0 second-digits))
        (mv (msg "Missing index in \"~s0]\" (inside \"~s1\"" first orig-x)
            nil nil nil))
       ((unless (eql (+ 2 first-digits second-digits) (length first)))
        (mv (msg "Bad format for last index \"~s0]\" of \"~s1\" -- extra ~
                  stuff after second index."
                 first orig-x)
            nil nil nil)))
    (mv nil nil first-index second-index))
  ///
  (local (in-theory (enable name-p)))
  (local (defthm len-of-nthcdr-1
           (implies (consp x)
                    (= (len (nthcdr 1 x))
                       (+ -1 (len x))))
           :rule-classes :linear))
  (verify-guards svtv-parse-path-indices
    :otf-flg t)

  (local (in-theory (disable len nthcdr (:d svtv-parse-path-indices) cons-equal
                             string-listp member-equal default-car default-cdr
                             str::take-leading-digits-when-digit-listp
                             str::explode-when-not-stringp
                             ;; acl2::member-when-atom
                             )))

  (deffixequiv svtv-parse-path-indices))




(define svtv-parse-path/select-aux ((dotted-parts string-listp)
                                    (orig-x stringp))
  :prepwork ((local (in-theory (disable (tau-system)
                                        ;; acl2::take
                                        ;; acl2::take-of-len-free
                                        acl2::take-of-too-many
                                        subseq-list)))
             (local (defthm len-equal-0
                      (equal (equal (len x) 0)
                             (not (consp x))))))
  :returns (mv errmsg
               (path (implies (not errmsg) (path-p path)))
               (range-msb (or (not range-msb) (natp range-msb))
                          :rule-classes :type-prescription)
               (range-lsb (implies range-msb (natp range-lsb))
                          :rule-classes :type-prescription))
  :measure (len dotted-parts)
  :verify-guards nil
  (b* ((orig-x (mbe :logic (acl2::str-fix orig-x) :exec orig-x))
       ((when (atom dotted-parts))
        (mv (msg "Error -- empty wire path? \"~s0\"" orig-x)
            nil nil nil))
       (lastp (atom (cdr dotted-parts)))
       (part1 (mbe :logic (acl2::str-fix (car dotted-parts))
                   :exec (car dotted-parts)))
       ((unless (and (not (equal part1 ""))
                     (eql (char part1 (1- (length part1))) #\])))
        (b* (((when lastp)
              (mv nil (make-path-wire :name part1) nil nil))
             ((mv errmsg rest range-msb range-lsb)
              (svtv-parse-path/select-aux (cdr dotted-parts) orig-x))
             ((when errmsg) (mv errmsg nil nil nil)))
          (mv nil
              (make-path-scope :subpath rest :namespace part1)
              range-msb range-lsb)))

       (lbrack-pos (str::strpos "[" part1))
       ((unless lbrack-pos)
        (mv (msg "Found ] without previous [: \"~s0\" inside \"~s1\""
                 part1 orig-x) nil nil nil))

       (name-part (subseq part1 0 lbrack-pos))
       (bracketed-part (subseq part1 lbrack-pos nil))
       (bracketed-parts (str::strtok bracketed-part '(#\])))
       ((unless bracketed-parts)
        (mv "This shouldn't happen." nil nil nil))
       ((mv err index-path range-msb range-lsb)
        (svtv-parse-path-indices bracketed-parts lastp orig-x))
       ((when err) (mv err nil nil nil))
       ((when lastp)
        (mv nil
            (if index-path
                (make-path-scope :namespace name-part :subpath index-path)
              (make-path-wire :name name-part))
            range-msb range-lsb))
       ((mv err rest-path range-msb range-lsb)
        (svtv-parse-path/select-aux (cdr dotted-parts) orig-x))
       ((when err) (mv err nil nil nil)))
    (mv nil
        (make-path-scope :namespace name-part
                         :subpath (if index-path
                                      (path-append index-path rest-path)
                                    rest-path))
        range-msb range-lsb))
  ///
  (local (in-theory (enable name-p)))
  (verify-guards svtv-parse-path/select-aux
    :otf-flg t)
  (local (in-theory (disable len nthcdr (:d svtv-parse-path/select-aux) cons-equal
                             string-listp member-equal default-car default-cdr
                             str::take-leading-digits-when-digit-listp
                             str::explode-when-not-stringp
                             acl2::lower-bound-of-len-when-sublistp
                             ;; acl2::member-when-atom
                             not)))

  (deffixequiv svtv-parse-path/select-aux))


(define svtv-parse-path/select ((x stringp))
  :returns (mv errmsg
               (path (implies (not errmsg) (path-p path)))
               (range-msb (or (not range-msb) (natp range-msb))
                          :rule-classes :type-prescription)
               (range-lsb (implies range-msb (natp range-lsb))
                          :rule-classes :type-prescription))
  (b* ((dotted-parts (str::strtok x '(#\.))))
    (svtv-parse-path/select-aux dotted-parts x)))

#|
(svtv-parse-path/select "a[0].b")
(svtv-parse-path/select "a[0][1].b[2][3:5]")
(svtv-parse-path/select "a[0].b[2:]")
(svtv-parse-path/select "a[0].b[:4]")
(svtv-parse-path/select "a[0].b[2]3][3:5]")
|#




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



(define svtv-1wire->lhs ((x stringp) (modidx natp) (moddb moddb-ok) aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv err
               (lhs lhs-p))
  :guard-hints (("goal" :do-not-induct t))
  (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
       ((mv err path range-msb range-lsb) (svtv-parse-path/select x))
       ((when err) (mv err nil))
       ((mv err wire wireidx bitsel) (moddb-path->wireidx/decl path modidx moddb))
       ((when err)
        (mv (msg "Wire not found: ~s0 -- ~@1" x err) nil))
       ((when (and bitsel range-msb))
        (mv (msg "Shouldn't have a part-select of a bit-select: ~s0" x) nil))
       ((wire wire) wire)
       (wire-lsb (if wire.revp
                     (+ -1 wire.width wire.low-idx)
                   wire.low-idx))
       (wire-msb (if wire.revp
                     wire.low-idx
                   (+ -1 wire.width wire.low-idx)))
       (range-lsb (if range-msb
                      range-lsb
                    (or bitsel wire-lsb)))
       (range-msb (or range-msb bitsel wire-msb))
       (range-ok (cond (range-msb
                        (if wire.revp
                            (and (<= wire.low-idx range-msb)
                                 (<= range-msb range-lsb)
                                 (< range-lsb (+ wire.low-idx wire.width)))
                          (and (<= wire.low-idx range-lsb)
                               (<= range-lsb range-msb)
                               (< range-msb (+ wire.low-idx wire.width)))))
                       (bitsel (and (<= wire.low-idx bitsel)
                                    (< bitsel (+ wire.low-idx wire.width))))))
       ((unless range-ok)
        (mv (msg "~s0: bit/partselect out of bounds or reversed" x) nil))

       (shift (if wire.revp (- wire-lsb range-lsb) (- range-lsb wire-lsb)))
       (range-width (+ 1 (abs (- range-msb range-lsb))))
       ;; ((when (< shift 0))
       ;;  (mv (msg "Wire ~s0: LSB out of bounds" x) nil))
       ;; ((when (> (+ shift width) wire.width))
       ;;  (mv (msg "Wire ~s0: MSB out of bounds" x) nil))
       (alias (get-alias wireidx aliases)))
    (mv nil (lhs-concat range-width (lhs-rsh shift alias) nil))))


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
       (entrylist (llist-fix (cdar entries)))
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
                      :hints(("Goal" :in-theory (enable svtv-entry-p svtv-baseentry-p))))))
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
