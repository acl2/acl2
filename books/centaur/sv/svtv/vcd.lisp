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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")
(include-book "../mods/moddb")
(include-book "std/stobjs/clone" :dir :system)
(include-book "../mods/path-string")
(include-book "std/strings/decimal" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (in-theory (disable acl2-count nth update-nth
                           acl2::nfix-when-not-natp)))

(local (std::add-default-post-define-hook :fix))

(defxdoc vcd.lisp :parents (svtv-debug))
(local (xdoc::set-default-parents vcd.lisp))

(defprod vcd-wire
  ((name stringp :rule-classes :type-prescription)
   (msb integerp :rule-classes :type-prescription)
   (lsb integerp :rule-classes :type-prescription)
   (code stringp :rule-classes :type-prescription)))

(define vcd-wire->width ((x vcd-wire-p))
  :returns (width natp :rule-classes :type-prescription)
  (b* (((vcd-wire x) x))
    (+ 1 (abs (- x.msb x.lsb)))))

(deflist vcd-wirelist :elt-type vcd-wire :true-listp t)

(deftypes vcd-scope
  (defprod vcd-scope
    ((name stringp)
     (wires vcd-wirelist)
     (subscopes vcd-scopelist))
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist vcd-scopelist :elt-type vcd-scope
    :measure (two-nats-measure (acl2-count x) 0)))

;; VCD wire codes use the printable ASCII characters: from ! (33) to ~ (126).
;; So we're essentially encoding the wire in base 94.
(define vcd-index->codechars ((x natp))
  :prepwork ((local (in-theory (disable floor mod)))
             (local (include-book "ihs/quotient-remainder-lemmas" :dir :system)))
  :returns (chars character-listp)
  :measure (nfix x)
  (b* ((first (code-char (+ 33 (mod (lnfix x) 94))))
       (rest (floor (lnfix x) 94))
       ((when (zp rest)) (list first)))
    (cons first (vcd-index->codechars rest))))

(define vcd-index->codestr ((x natp))
  :returns (code stringp :rule-classes :type-prescription)
  (reverse (coerce (vcd-index->codechars x) 'string)))

(make-event
 `(acl2::def-1d-arr vcd-wiremap
    :slotname vcdwire
    :pred vcd-wire-p
    :fix vcd-wire-fix$inline
    :default-val ,(vcd-wire "" 0 0 "")))





(define elab-mod->vcd-wires ((n natp)
                             (codeidx natp)
                             (elab-mod))
  :guard (<= n (elab-mod-nwires elab-mod))
  :measure (nfix (- (elab-mod-nwires elab-mod)
                    (nfix n)))
  :returns (wires vcd-wirelist-p)
  :verbosep t
  ;; ==Backward Range Convention ==
  (b* (((when (mbe :logic (zp (- (elab-mod-nwires elab-mod)
                                 (nfix n)))
                   :exec (eql (elab-mod-nwires elab-mod) n)))
        nil)
       (x (elab-mod-wiretablei n elab-mod))
       ((wire x) x)
       (vcdwire (make-vcd-wire :name (name->string x.name)
                               :msb (if x.revp
                                        x.low-idx
                                      (+ -1 x.width x.low-idx))
                               :lsb (if x.revp
                                        (+ -1 x.width x.low-idx)
                                      x.low-idx)
                               :code (vcd-index->codestr codeidx)))
       (- (and (equal (vcd-wire->code vcdwire) "")
               (cw "Created empty-named wire for wire ~s0~%" x.name))))
    (cons vcdwire
          (elab-mod->vcd-wires (1+ (lnfix n)) (1+ (lnfix codeidx)) elab-mod)))
  ///
  (defthm len-of-elab-mod->vcd-wires
    (equal (len (elab-mod->vcd-wires n codeidx elab-mod))
           (nfix (- (elab-mod-nwires elab-mod) (nfix n))))))

(define vcd-wirelist-add-to-wiremap ((x vcd-wirelist-p)
                                     (idx natp)
                                     (vcd-wiremap))
  :guard (<= (+ (len x) idx) (vcdwires-length vcd-wiremap))
  :returns vcd-wiremap1
  (b* (((when (atom x)) vcd-wiremap)
       (vcd-wiremap (set-vcdwire idx (car x) vcd-wiremap)))
    (vcd-wirelist-add-to-wiremap (cdr x) (1+ (lnfix idx)) vcd-wiremap))
  ///
  (defthm len-of-vcd-wirelist-add-to-wiremap-linear
    (<= (len vcd-wiremap) (len (vcd-wirelist-add-to-wiremap x idx vcd-wiremap)))
    :rule-classes :linear))

(defines vcd-moddb->scopes
  :verify-guards nil
  (define vcd-moddb->scopes ((instname name-p)
                             (modidx natp)
                             (codeidx natp)
                             (wireoffset natp)
                             (moddb moddb-ok)
                             (vcd-wiremap))
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (+ wireoffset (moddb-mod-totalwires modidx moddb))
                    (vcdwires-length vcd-wiremap)))
    :returns (mv (scope vcd-scope-p)
                 (codeidx1 natp)
                 (vcd-wiremap1
                  (<= (len vcd-wiremap) (len vcd-wiremap1))
                  :rule-classes :linear))
    :measure (nat-list-measure (list modidx 1 0))
    (b* (((stobj-get vcdwires nwires)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->vcd-wires 0 codeidx elab-mod)
              (elab-mod-nwires elab-mod)))
         (codeidx (+ (lnfix codeidx) nwires))
         (vcd-wiremap (vcd-wirelist-add-to-wiremap vcdwires wireoffset vcd-wiremap))
         ((mv scopes codeidx vcd-wiremap)
          (vcd-moddb->modinst-scopes 0 modidx codeidx wireoffset moddb vcd-wiremap)))
      (mv (make-vcd-scope :name (name->string instname)
                          :wires vcdwires
                          :subscopes scopes)
          codeidx vcd-wiremap)))

  (define vcd-moddb->modinst-scopes ((n natp)
                                     (modidx natp)
                                     (codeidx natp)
                                     (wireoffset natp)
                                     (moddb moddb-ok)
                                     (vcd-wiremap))
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (+ wireoffset (moddb-mod-totalwires modidx moddb))
                    (vcdwires-length vcd-wiremap))
                (<= n (moddb-mod-ninsts modidx moddb)))
    :returns (mv (scopes vcd-scopelist-p)
                 (codeidx1 natp)
                 (vcd-wiremap1
                  (<= (len vcd-wiremap) (len vcd-wiremap1))
                  :rule-classes :linear))
    :measure (nat-list-measure
              (list modidx 0
                    (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                               (ninsts)
                               (elab-mod-ninsts elab-mod)
                               (- ninsts (nfix n)))))
    (b* (((stobj-get donep submod-idx suboffset subname)
          ((elab-mod (moddb->modsi modidx moddb)))
          (if (mbe :logic (zp (- (elab-mod-ninsts elab-mod)
                                 (nfix n)))
                   :exec (eql (elab-mod-ninsts elab-mod) n))
              (mv t nil nil nil)
            (mv nil
                (elab-mod->inst-modidx n elab-mod)
                (elab-mod->inst-wireoffset n elab-mod)
                (elab-mod->instname n elab-mod))))
         ((when donep) (mv nil (lnfix codeidx) vcd-wiremap))
         ((unless ;; (and (stringp subname)
                       (mbt (< submod-idx (lnfix modidx))))
          (vcd-moddb->modinst-scopes (1+ (lnfix n)) modidx codeidx
                                     wireoffset moddb vcd-wiremap))
         ((mv scope1 codeidx vcd-wiremap)
          (vcd-moddb->scopes subname submod-idx codeidx
                             (+ (lnfix wireoffset) suboffset)
                             moddb vcd-wiremap))
         ((mv rest codeidx vcd-wiremap)
          (vcd-moddb->modinst-scopes (1+ (lnfix n)) modidx codeidx
                                     wireoffset moddb vcd-wiremap)))
      (mv (cons scope1 rest) codeidx vcd-wiremap)))
  ///
  (local (in-theory (disable vcd-moddb->modinst-scopes
                             vcd-moddb->scopes)))
  (deffixequiv-mutual vcd-moddb->scopes
    :hints ('(:expand ((:free (modidx codeidx wireoffset moddb vcd-wiremap)
                        (vcd-moddb->modinst-scopes n modidx codeidx wireoffset moddb vcd-wiremap))
                       (vcd-moddb->modinst-scopes (nfix n) modidx codeidx wireoffset moddb vcd-wiremap)
                       (:free (modidx codeidx wireoffset moddb vcd-wiremap)
                        (vcd-moddb->scopes instname modidx codeidx wireoffset moddb vcd-wiremap))
                       (vcd-moddb->scopes (name-fix instname) modidx codeidx wireoffset moddb vcd-wiremap))
              :in-theory (disable nth-of-elab-modlist-fix))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (verify-guards vcd-moddb->scopes
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance moddb-mod-inst-wireoffset-monotonic
                          (m (elab-mod-ninsts (moddb->modsi modidx moddb)))
                          (n (+ n 1))))
                   :expand ((moddb-mod-inst-wireoffset (+ 1 n) modidx moddb)
                            (:with moddb-mod-totalwires-in-terms-of-wireoffset
                             (moddb-mod-totalwires modidx moddb))
                            (moddb-mod-ninsts modidx moddb)))))))


(define vcd-print-wiredecls ((x vcd-wirelist-p)
                              (p vl-printedlist-p))
  :returns (p1 vl-printedlist-p)
  :hooks ((:fix :hints (("goal" :induct (vcd-print-wiredecls x p)
                         :expand ((:free (p) (vcd-print-wiredecls x p))
                                  (vcd-print-wiredecls (vcd-wirelist-fix x) p))
                         :in-theory (disable (:d vcd-print-wiredecls))))))
  (b* (((when (atom x))
        (vl::vl-printedlist-fix p))
       ((vcd-wire xf) (car x))
       (p (rlist* p "$var wire "
                  (natstr (vcd-wire->width (car x)))
                  " "
                  xf.code " " xf.name))
       (p (cond ((and (eql xf.msb 0) (eql xf.lsb 0)) p)
                ((eql xf.msb xf.lsb)
                 (rlist* p "[" (if (< xf.msb 0) "-" "") (natstr (abs xf.msb)) "]"))
                (t (rlist* p "[" (if (< xf.msb 0) "-" "") (natstr (abs xf.msb)) ":"
                           (if (< xf.lsb 0) "-" "")
                           (natstr (abs xf.lsb))
                           "]"))))
       (p (rlist* p " $end" #\Newline)))
    (vcd-print-wiredecls (cdr x) p)))



(defines vcd-print-scope
  :verify-guards nil
  (define vcd-print-scope ((x vcd-scope-p) (p vl-printedlist-p))
    :measure (vcd-scope-count x)
    :returns (p1 vl-printedlist-p)
    (b* (((vcd-scope x) x)
         (p (rlist* p "$scope module " x.name " $end" #\Newline))
         (p (vcd-print-wiredecls x.wires p))
         (p (vcd-print-scopes x.subscopes p)))
      (rlist* p "$upscope $end" #\Newline #\Newline)))
  (define vcd-print-scopes ((x vcd-scopelist-p) (p vl-printedlist-p))
    :measure (vcd-scopelist-count x)
    :returns (p1 vl-printedlist-p)
    (if (atom x)
        (vl::vl-printedlist-fix p)
      (vcd-print-scopes (cdr x) (vcd-print-scope (car x) p))))
  ///
  (deffixequiv-mutual vcd-print-scope
    :hints ('(:expand ((:Free (p) (vcd-print-scope x p))
                       (vcd-print-scope (vcd-scope-fix x) p)
                       (:Free (p) (vcd-print-scopes x p))
                       (vcd-print-scopes (vcd-scopelist-fix x) p))
              :in-theory (disable (:d vcd-print-scope)
                                  (:d vcd-print-scopes)))))
  (verify-guards vcd-print-scope))


(define vcd-print-header ((date stringp)
                          (scope vcd-scope-p)
                          (p vl-printedlist-p))
  :returns (p1 vl-printedlist-p)
  (b* ((p (rlist* p "$date " (str::str-fix date) "$end" #\Newline
                  "$version SVTV-DEBUG simulation $end" #\Newline
                  "$timescale 1 s $end" #\Newline #\Newline))
       (p (vcd-print-scope scope p)))
    (rlist* p "$enddefinitions $end" #\Newline #\Newline)))



(make-event
 `(acl2::def-1d-arr 4vecarr
    :slotname 4vec
    :pred 4vec-p
    :fix 4vec-fix$inline
    :default-val ,(4vec-x)))

(acl2::defstobj-clone vcd-vals 4vecarr :suffix "VCD")

(define vcd-print-4vec-aux ((upper integerp) (lower integerp)
                            (firstbit natp)
                            (p vl-printedlist-p))
  :returns (p1 vl-printedlist-p)
  :hooks ((:fix :hints (("goal" :induct (vcd-print-4vec-aux upper lower firstbit p)
                         :in-theory (disable (:d vcd-print-4vec-aux))
                         :expand ((:free (upper lower p)
                                   (vcd-print-4vec-aux upper lower firstbit p))
                                  (:free (upper lower p)
                                   (vcd-print-4vec-aux upper lower 0 p))
                                  (vcd-print-4vec-aux upper lower (nfix firstbit) p))))))
  (b* (((when (zp firstbit))
        (vl::vl-printedlist-fix p))
       (firstbit (1- firstbit))
       (ubit (logbitp firstbit upper))
       (lbit (logbitp firstbit lower))
       (char (if ubit (if lbit #\1 #\x) (if lbit #\z #\0))))
    (vcd-print-4vec-aux upper lower firstbit (cons char p))))

(define vcd-4vec-bitstr ((x 4vec-p) (width natp))
  :returns (bits stringp :rule-classes :type-prescription)
  (b* (((4vec x) x))
    (vl-printedlist->string
     (vcd-print-4vec-aux x.upper x.lower
                         (min (lnfix width)
                              (+ 1 (max (integer-length x.upper)
                                        (integer-length x.lower))))
                         nil))))

(define vcd-dump-first-snapshot-aux ((n natp) vcd-vals vcd-wiremap
                                     (p vl-printedlist-p))
  :guard (and (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (<= n (vcdwires-length vcd-wiremap)))
  :returns (p1 vl-printedlist-p)
  :measure (nfix (- (vcdwires-length vcd-wiremap) (nfix n)))
  (b* (((when (mbe :logic (zp (- (vcdwires-length vcd-wiremap) (nfix n)))
                   :exec (eql (vcdwires-length vcd-wiremap) n)))
        (vl::vl-printedlist-fix p))
       (wire (get-vcdwire n vcd-wiremap))
       ((vcd-wire wire) wire)
       ((when (equal wire.code ""))
        ;; BOZO Why does this happen?
        (cw "~x0, ~s1: skipping wire with empty code~%" n wire.name)
        (vcd-dump-first-snapshot-aux (1+ (lnfix n)) vcd-vals vcd-wiremap p))
       (wire.width (vcd-wire->width wire))
       ;; (val (4vec-zero-ext (2vec wire.width) (get-4vec n vcd-vals)))
       (valstr (vcd-4vec-bitstr (get-4vec n vcd-vals) wire.width))
       (p (if (eql wire.width 1)
              (rlist* p valstr)
            (rlist* p #\b valstr #\Space)))
       (p (rlist* p wire.code #\Newline))

       ;; (- (and (member-equal wire.code '("\"?" "\"@" ""))
       ;;         (cw "Code ~s0, last entries: ~x1~%" wire.code (take 10 p))))
       )
    (vcd-dump-first-snapshot-aux (1+ (lnfix n)) vcd-vals vcd-wiremap p)))


(define vcd-dump-first-snapshot (vcd-vals vcd-wiremap (p vl-printedlist-p))
  :guard (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
  :returns (p1 vl-printedlist-p)
  (b* ((p (rlist* p "$dumpvars" #\Newline))
       (p (vcd-dump-first-snapshot-aux 0 vcd-vals vcd-wiremap p)))
    (rlist* p "$end" #\Newline)))

(define vcd-dump-delta-aux ((changes nat-listp) vcd-vals vcd-wiremap
                            (p vl-printedlist-p))
  :guard (and (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (or (atom changes)
                  (< (nat-list-max changes) (vcdwires-length vcd-wiremap))))
  :guard-hints (("goal" :in-theory (enable nat-list-max)))
  :returns (p1 vl-printedlist-p)
  (b* (((when (atom changes)) (vl::vl-printedlist-fix p))
       (n (car changes))
       (wire (get-vcdwire n vcd-wiremap))
       ((vcd-wire wire) wire)
       ((when (equal wire.code ""))
        ;; BOZO Why does this happen?
        (cw "~x0, ~s1: skipping wire with empty code~%" n wire.name)
        (vcd-dump-delta-aux (cdr changes) vcd-vals vcd-wiremap p))
       (wire.width (vcd-wire->width wire))
       ;; (val (4vec-zero-ext (2vec wire.width) (get-4vec n vcd-vals)))
       (valstr (vcd-4vec-bitstr (get-4vec n vcd-vals) wire.width))
       (p (if (eql wire.width 1)
              (rlist* p valstr)
            (rlist* p #\b valstr #\Space)))
       (p (rlist* p wire.code #\Newline)))
    (vcd-dump-delta-aux (cdr changes) vcd-vals vcd-wiremap p)))

(fty::deffixcong nat-equiv equal (natstr n) n)

(define vcd-dump-delta ((time natp) (changes nat-listp) vcd-vals vcd-wiremap (p vl-printedlist-p))
  :guard (and (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (or (atom changes)
                  (< (nat-list-max changes) (vcdwires-length vcd-wiremap))))
  :returns (p1 vl-printedlist-p)
  (b* ((p (rlist* p #\# (natstr time) #\Newline))
       (p (vcd-dump-delta-aux changes vcd-vals vcd-wiremap p)))
    (rlist* p #\Newline)))
