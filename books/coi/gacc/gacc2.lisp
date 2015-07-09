; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:
;;
(include-book "../defstructure/defstructure")
(include-book "ram")

;These two rules get sucked in by defstructure.  We disable these for
;efficiency, since we don't expect to reason about all-conses or no-conses.
;(The free variables in these rules make them not too bad, but still they are
;hung on cons, so every time we're reasoning about a call to cons, these rules
;go looking for calls to all-conses and no-conses.) -ews

(in-theory (disable cpath::consp-when-member-of-all-conses))
(in-theory (disable cpath::not-consp-when-member-of-no-conses))



;(in-theory (disable WFIXN-REWRITE-TO-LOGHEAD))

;from gacc.lisp - bzo

(defun syntax-consp-or-quote (skel)
  (declare (type t skel))
  (or (quotep skel)
      (and (consp skel)
           (equal (car skel) 'cons))))

(defun syntax-consp-or-symbol (skel)
  (declare (type t skel))
  (or (symbolp skel)
      (and (consp skel)
           (or (equal (car skel) 'cons)
               (and (equal (car skel) 'quote)
                    (consp (cdr skel))
                    (not (null (cadr skel))))))))

;move?
(defthmd open-flat
  (implies (and (syntaxp (syntax-consp-or-symbol list))
                (consp list))
           (equal (flat list)
                  (append (car list)
                          (flat (cdr list)))))
  :hints (("goal" :in-theory (enable flat))))

(defun syntax-atom (m)
  (declare (type t m))
  (or (symbolp m)
      (quotep m)))



;end stuff from gacc.lisp



(acl2::defstructure+ skel
  base
  spec
  (:options :guards))

;apparently, these happen to be the same...
;consider enabling this?
(defthmd skel-p-reduction
  (equal (skel-p x)
         (weak-skel-p x))
  :hints (("goal" :in-theory (enable skel-p))))

(acl2::defstructure+ line
  key
  (skel (:assert (skel-p skel) :rewrite :forward-chaining))
  (:options :guards))

;this is a weird lemma?:
(defthm not-line-p-not-equal
  (implies (not (line-p x))
           (equal (equal (line k (skel b s)) x)
                  nil))
  :hints (("goal" :in-theory (enable ;weak-skel-p skel-p
                                     ;line-p line-skel weak-line-p line skel
                                     ))))

(acl2::defstructure+ slot
  name
  off
  size
  val
  type
  (skel (:assert (skel-p skel) :rewrite :forward-chaining))
  (:options :guards
            (:keyword-constructor mk-slot)))

(in-theory (disable slot-p))

(defun which-p (which)
  (declare (type t which))
  (memberp which '(:all :ptr :val :nil)))

(defun how-p (how)
  (declare (type t how))
  (memberp how '(:g :x :z)))

(acl2::defstructure+ op
  (which (:assert (which-p which) :rewrite :forward-chaining))
  (how   (:assert (how-p   how)   :rewrite :forward-chaining))
  (:options :guards))

(defun ptr? (type)
  (declare (type t type))
  (equal type :ptr))

(defun x? (op)
  (declare (type (satisfies op-p) op))
  (let ((how (op-how op)))
    (equal how :x)))

(defun whichnum (n)
  (declare (type integer n))
  (case n
        (3 :all)
        (2 :ptr)
        (1 :val)
        (0 :nil)))

;; Disabling this (and other functions like it) in some proofs helped speed
;; them up a lot!
;;
(defun numwhich (which)
  (declare (type t which))
  (case which
        (:all 3)
        (:ptr 2)
        (:nil 0)
        (t    1)))

(defthm logbit-1-1-of-numwhich
  (equal (equal 1 (acl2::logbit 1 (numwhich which)))
         (or (equal :all which)
             (equal :ptr which)))
  :hints (("Goal" :in-theory (enable acl2::logbit))))


(defun numtype (type)
  (declare (type t type))
  (case type
        (:ptr 2)
        (t    1)))

(defun whichtype (which type)
  (declare (type t which type))
  (let ((which (numwhich which))
        (type  (numtype  type)))
    (equal type (logand which type))))

(defmacro optype (op type)
  `(let ((which (op-which ,op)))
     (whichtype which ,type)))

(defthm skel-measure
  (implies (consp list)
           (e0-ord-< (acl2-count (skel-spec (slot-skel (car list))))
                     (acl2-count list)))
  :hints (("goal" :in-theory (enable skel-spec slot-skel))))

(defun fix-skel (skel)
  (declare (type t skel))
  (if (skel-p skel) skel (skel 0 nil)))

(defthm fix-skel-skel-p
  (implies (skel-p skel)
           (equal (fix-skel skel)
                  skel))
  :hints (("goal" :in-theory (enable fix-skel))))

(defun wfixn-skel (size skel)
  (let ((skel (fix-skel skel)))
    (skel (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                 (skel-base skel))
          (skel-spec skel))))

(defthm skel-p-fix-skel
  (and (skel-p (fix-skel skel))
       (skel-p (wfixn-skel size skel))))

(in-theory (disable fix-skel))

(defmacro +<> (a b)
  `(+ (ifix ,a) (ifix ,b)))

(defun spectype (type)
  (declare (type t type))
  (if (equal type :ptr) :ptr :val))

(defun op-base (h type base valu)
  (declare (type t h type base valu))
  (if (equal type :ptr)
      (if (equal h :x) base
        (if (equal h :z) 0 valu))
    base))

(defun wf-spec (spec)
  (declare (type t spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((skel (slot-skel slot))
                  (type (slot-type slot)))
              (and (skel-p skel)
                   (implies (ptr? type) (wf-spec (skel-spec skel)))
                   (wf-spec (cdr spec))))
          (wf-spec (cdr spec))))
    t))

(defun wf-skels (skels)
  (declare (type t skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (and (skel-p skel)
                   (wf-spec (skel-spec skel))
                   (wf-skels (cdr skels))))
          (wf-skels (cdr skels))))
    t))

(defun g*-spec (op ptr spec ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec)
           (xargs :verify-guards nil))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read))
                                       )))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                          (ifix (if (whichtype w type) read value))
                                          )))
                        (let ((skel (if (ptr? type) (skel base (g*-spec op base (skel-spec skel) ram)) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (g*-spec op ptr (cdr spec) ram)))))))))
          (cons slot
                (g*-spec op ptr (cdr spec) ram))))
    spec))


(defun G*-SPEC-car (op ptr slot ram)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((OFF (SLOT-OFF SLOT))
      (SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ (RX SIZE (|+<>| OFF PTR) RAM)))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((VALUE
           (ACL2::LOGHEAD
            (FIX-SIZE SIZE)
            (IFIX (IF (WHICHTYPE W TYPE) READ VALUE)))))
         (LET
          ((SKEL
            (IF (PTR? TYPE)
                (SKEL BASE
                      (G*-SPEC OP BASE (SKEL-SPEC SKEL) RAM))
                SKEL)))
          (UPDATE-SLOT SLOT :VAL VALUE :SKEL SKEL))))))))
   SLOT))

(DEFTHM G*-SPEC-of-non-cons
  (implies (not (consp spec))
           (EQUAL (G*-SPEC OP ptr spec RAM)
                  spec))
  :hints (("Goal" :in-theory (enable g*-spec))))

(defthm g*-spec-of-cons
  (equal (g*-spec op ptr (cons slot spec) ram)
         (cons (g*-spec-car op ptr slot ram)
               (g*-spec op ptr spec ram)))
  :hints (("Goal" :in-theory (e/d (g*-spec) (numwhich numtype op-base ptr? whichtype)))))


(defthm car-of-g*-spec
  (equal (car (G*-SPEC OP ptr spec RAM))
         (if (consp spec)
             (g*-spec-car op ptr (car spec) ram)
           (car spec)))
  :hints (("Goal" :in-theory (enable g*-spec))))

(defthm cdr-of-g*-spec
  (equal (cdr (G*-SPEC OP ptr spec RAM))
         (g*-spec op ptr (cdr spec) ram))
  :hints (("Goal" :in-theory (e/d (g*-spec) (numwhich numtype op-base ptr? whichtype)))))



(defthm wf-spec-g*-spec
  (wf-spec (g*-spec op ptr spec ram))
  :hints (("Goal" :in-theory (disable numwhich numtype op-base whichtype ptr? ifix))))

(defthm consp-g*-spec
  (equal (consp (g*-spec op ptr spec ram))
         (consp spec)))

(verify-guards g*-spec)

;bzo
(defthm loghead-of-ifix
  (equal (acl2::loghead n (ifix base))
         (acl2::loghead n base)))

(defthm open-g*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (g*-spec op ptr spec ram)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                          (if (whichtype w type) read value))))
                        (let ((skel (if (ptr? type) (skel base (g*-spec op base (skel-spec skel) ram)) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (g*-spec op ptr (cdr spec) ram)))))))))
          (cons slot
                (g*-spec op ptr (cdr spec) ram))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (g*-spec op ptr spec ram)
           spec)))
  :hints (("goal" :in-theory '(g*-spec loghead-of-ifix))))

(in-theory (disable (:definition g*-spec) (g*-spec)))

(defund g*-list (op skels ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((line (line key (skel base (g*-spec op base (skel-spec skel) ram)))))
                  (cons line
                        (g*-list op (cdr skels) ram)))))
          (cons line
                (g*-list op (cdr skels) ram))))
    skels))

(in-theory (disable (:executable-counterpart g*-list)))

;bzo Eric added this to support G*-LIST-of-cons.  Could change g*-list to call this function?
(defun g*-list-car (op line ram)
  (IF (LINE-P LINE)
      (LET
       ((KEY (LINE-KEY LINE))
        (SKEL (LINE-SKEL LINE)))
       (LET
        ((BASE (OP-BASE (OP-HOW OP)
                              :PTR (SKEL-BASE SKEL)
                              KEY)))
        (LINE KEY
              (SKEL BASE
                    (G*-SPEC OP BASE (SKEL-SPEC SKEL)
                             RAM)))))
      LINE))

(defthm car-of-g*-list
  (equal (car (g*-list op skels ram))
         (if (consp skels)
             (g*-list-car op (car skels) ram)
           (car skels)))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthm cdr-of-g*-list
  (equal (cdr (g*-list op skels ram))
         (g*-list op (cdr skels) ram))
  :hints (("Goal" :in-theory (enable g*-list))))

;big speed up in a later book from this instead of using open-g*-list!
(defthm g*-list-of-cons
  (equal (g*-list op (cons line skels) ram)
         (cons (g*-list-car op line ram) (g*-list op skels ram)))
  :hints (("Goal" :in-theory (enable g*-list))))

(DEFTHM G*-LIST-of-non-cons
  (implies (not (consp skels))
           (EQUAL (G*-LIST OP SKELS RAM)
                  SKELS))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthmd open-g*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (g*-list op skels ram)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((line (line key (skel base (g*-spec op base (skel-spec skel) ram)))))
                  (cons line
                        (g*-list op (cdr skels) ram)))))
          (cons line
                (g*-list op (cdr skels) ram))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (g*-list op skels ram)
           skels)))
  :hints (("goal" :in-theory '(g*-list))))

(defthm consp-g*-list
  (equal (consp (g*-list op list ram))
         (consp list))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthm g*-list-append
  (equal (g*-list op (append x y) ram)
         (append (g*-list op x ram)
                 (g*-list op y ram)))
  :hints (("goal" :in-theory (enable binary-append g*-list)
           :induct (append x y))))

(defthm wf-skels-g*-list
  (wf-skels (g*-list op skels ram))
  :hints (("Goal" :in-theory (enable g*-list))))



(defun s*-spec (op ptr spec ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((size  (slot-size slot))
                    (off   (slot-off  slot))
                    (value (slot-val  slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read)))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                          (ifix (if (whichtype w type) value (rx size (+<> off ptr) ram))))))
                        (let ((ram (wx size (+<> off ptr) value ram)))
                          (let ((ram (if (ptr? type)
                                         (s*-spec op base (skel-spec skel) ram)
                                       ram)))
                            (s*-spec op ptr (cdr spec) ram)))))))))
          (s*-spec op ptr (cdr spec) ram)))
    ram))


(defthm open-s*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (s*-spec op ptr spec ram)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((size  (slot-size slot))
                    (off   (slot-off  slot))
                    (value (slot-val  slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                          (if (whichtype w type) value (rx size (+<> off ptr) ram)))))
                        (let ((ram (wx size (+<> off ptr) value ram)))
                          (let ((ram (if (ptr? type)
                                         (s*-spec op base (skel-spec skel) ram)
                                       ram)))
                            (s*-spec op ptr (cdr spec) ram)))))))))
          (s*-spec op ptr (cdr spec) ram)))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (s*-spec op ptr spec ram)
           ram)))
  :hints (("goal" :in-theory '(s*-spec loghead-of-ifix))))

(in-theory (disable (:definition s*-spec) (s*-spec)))

(defun s*-list (op skels ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line))
                  (key  (line-key line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((ram (s*-list op (cdr skels) ram)))
                  (s*-spec op base (skel-spec skel) ram))))
          (s*-list op (cdr skels) ram)))
    ram))

(defthm open-s*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (s*-list op skels ram)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line))
                  (key  (line-key line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((ram (s*-list op (cdr skels) ram)))
                  (s*-spec op base (skel-spec skel) ram))))
          (s*-list op (cdr skels) ram)))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (s*-list op skels ram)
           ram)))
  :hints (("goal" :in-theory '(s*-list))))

(in-theory (disable (:definition s*-list) (s*-list)))

;;
;; f* (flatten) returns the addresses of selected locations, useful
;; for determining disjointness.
;;


(defun f*-spec (op ptr spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read)))))
                      (let ((blk (if (whichtype w type) (list (sblk size (+<> off ptr))) nil)))
                        (let ((rec (if (ptr? type) (f*-spec op base (skel-spec skel)) nil)))
                          (append blk
                                  rec
                                  (f*-spec op ptr (cdr spec))))))))))
          (f*-spec op ptr (cdr spec))))
    nil))

(defthm f*-spec-when-ptr-is-not-an-integerp
  (implies (not (integerp ptr))
           (equal (f*-spec op ptr spec)
                  (f*-spec op 0 spec))))

(defthm open-f*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (f*-spec op ptr spec)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((blk (if (whichtype w type) (list (sblk size (+<> off ptr))) nil)))
                        (let ((rec (if (ptr? type) (f*-spec op base (skel-spec skel)) nil)))
                          (append blk
                                  rec
                                  (f*-spec op ptr (cdr spec))))))))))
          (f*-spec op ptr (cdr spec))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (f*-spec op ptr spec)
           nil)))
  :hints (("goal" :in-theory '(f*-spec loghead-of-ifix))))

(defthm true-listp-f*-spec
  (true-listp (f*-spec op ptr spec)))

(defthm f*-spec-nil
  (implies (equal (op-which fop) :nil)
           (equal (f*-spec fop fptr spec)
                  nil)))

(in-theory (disable (:definition f*-spec) (f*-spec)))

;; We will need to prove that (f*-x :all ..) is a permutation of
;; (append (f*-x :ptr ..) (f*-x :val ..))  and rewrite it as such
;; under uniqueness/disjointness, etc.

(defun f*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (f*-spec op base (skel-spec skel))
                        (f*-list op (cdr skels)))))
          (f*-list op (cdr skels))))
    nil))

(defthm open-f*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (f*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (f*-spec op base (skel-spec skel))
                        (f*-list op (cdr skels)))))
          (f*-list op (cdr skels))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (f*-list op skels)
           nil)))
  :hints (("goal" :in-theory '(f*-list))))

(defthm true-listp-f*-list
  (true-listp (f*-list op spec)))

(defthm f*-list-append
  (equal (f*-list op (append x y))
         (append (f*-list op x)
                 (f*-list op y)))
  :hints (("goal" :in-theory (enable binary-append))))


(defthm f*-list-nil
  (implies (equal (op-which fop) :nil)
           (equal (f*-list fop list) nil))
  :hints (("Goal" :in-theory (enable  op-which)
           :expand ( (f*-list fop list))))
  )

(in-theory (disable (:definition f*-list) (f*-list)))

;;
;; h* (heirarchy) returns a pared-down structure, useful for determining
;; structural equivalence.
;;

(defun h*-spec (op spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                               (ifix (op-base h type base read)))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                                  (ifix (if (whichtype w type) read 0)))))
                        (let ((skel (if (ptr? type) (skel base (h*-spec op (skel-spec skel))) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (h*-spec op (cdr spec))))))))))
          (cons slot (h*-spec op (cdr spec)))))
    spec))


(defthm H*-SPEC-of-non-cons
  (implies (not (consp spec))
           (equal (H*-SPEC OP SPEC)
                  spec)))

(defun car-h*-spec (op slot)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ VALUE))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((VALUE (ACL2::LOGHEAD
                  (FIX-SIZE SIZE)
                  (IFIX (IF (WHICHTYPE W TYPE) READ 0)))))
         (LET
          ((SKEL (IF (PTR? TYPE)
                     (SKEL BASE (H*-SPEC OP (SKEL-SPEC SKEL)))
                     SKEL)))
          (UPDATE-SLOT SLOT :VAL VALUE :SKEL SKEL))))))))
   SLOT))

(defthm H*-SPEC-of-cons
  (equal (H*-SPEC OP (cons slot SPEC))
         (cons (car-h*-spec op slot)  (H*-SPEC OP SPEC)))
  :hints (("Goal" :in-theory (disable numtype numwhich op-base ptr? whichtype))))

(defthm car-of-h*-spec
  (equal (car (h*-spec op spec))
         (if (consp spec)
             (car-h*-spec op (car spec))
           nil))
  :hints (("Goal" :in-theory (disable numtype numwhich op-base ptr?))))

(defthm cdr-h*-spec
  (implies
   (consp spec)
   (equal (cdr (h*-spec op spec))
          (h*-spec op (cdr spec))))
  :hints (("goal" :in-theory (enable default-cdr)
           :expand (h*-spec op spec))))

#|
(defthm consp-h*-spec
  (implies
   (consp (h*-spec hop hspec))
   (consp hspec))
  :rule-classes (:forward-chaining))

(defthm not-consp-h*-spec
  (implies (not (consp (h*-spec hop hspec)))
           (not (consp hspec)))
  :rule-classes (:forward-chaining))
|#

(defthm consp-h*-spec-whamo
  (equal (consp (h*-spec op spec))
         (consp spec)))


(defthm open-h*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (h*-spec op spec)
           (let ((slot (car spec)))
             (if (slot-p slot)
                 (let ((w (op-which op))
                       (h (op-how   op)))
                   (let ((size  (slot-size slot))
                         (type  (slot-type slot))
                         (skel  (slot-skel slot))
                         (value (slot-val  slot))
                         )
                     (let ((read value))
                       (let ((base (skel-base skel)))
                         (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                                    (op-base h type base read))))
                           (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                                       (if (whichtype w type) read 0))))
                             (let ((skel (if (ptr? type) (skel base (h*-spec op (skel-spec skel))) skel)))
                               (cons (update-slot slot
                                                  :val  value
                                                  :skel skel
                                                  )
                                     (h*-spec op (cdr spec))))))))))
               (cons slot (h*-spec op (cdr spec)))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (h*-spec op spec)
           spec)))
  :hints (("goal" :in-theory '(h*-spec loghead-of-ifix))))


(defthm wf-spec-h*-spec
  (wf-spec (h*-spec op spec)))

(in-theory (disable (:definition h*-spec) (h*-spec) ))

(defun h*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((key key))
                  (cons (line key (skel base (h*-spec op (skel-spec skel))))
                        (h*-list op (cdr skels))))))
          (cons line (h*-list op (cdr skels)))))
    skels))

(defthm h*-list-append
  (equal (h*-list op (append x y))
         (append (h*-list op x) (h*-list op y)))
  :hints (("goal" :in-theory (enable binary-append))))

(defthm len-h*-list
  (equal (len (h*-list op list))
         (len list)))

(defthm true-listp-h*-list
  (equal (true-listp (h*-list op list))
         (true-listp list)))

(defthm consp-h*-list
  (equal (consp (h*-list op list))
         (consp list)))

;add type-prescriptions?

(defthm open-h*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (h*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((key key))
                  (cons (line key (skel base (h*-spec op (skel-spec skel))))
                        (h*-list op (cdr skels))))))
          (cons line (h*-list op (cdr skels)))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (h*-list op skels)
           skels)))
  :hints (("goal" :in-theory '(h*-list))))

(defthm wf-skels-h*-list
  (wf-skels (h*-list op skels)))

(in-theory (disable (:definition h*-list) (h*-list)))

;;
;; v* (value) returns a list of selected values from the skel
;;

(defun v*-spec (op spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  )
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((value (if (whichtype w type) (list (acl2::loghead (fix-size size) ;wfixn 8 size
                                                                           (ifix read)
                                                                           )) nil)))
                    (let ((rec (if (ptr? type) (v*-spec op (skel-spec skel)) nil)))
                      (append value
                              rec
                              (v*-spec op (cdr spec))))))))
          (v*-spec op (cdr spec))))
    nil))

(defthm open-v*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (v*-spec op spec)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  )
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((value (if (whichtype w type) (list (acl2::loghead (fix-size size) ;wfixn 8 size
                                                                           read)) nil)))
                    (let ((rec (if (ptr? type) (v*-spec op (skel-spec skel)) nil)))
                      (append value
                              rec
                              (v*-spec op (cdr spec))))))))
          (v*-spec op (cdr spec))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (v*-spec op spec)
           nil)))
  :hints (("goal" :in-theory '(v*-spec loghead-of-ifix))))


(defthm true-listp-v*-spec
  (true-listp (v*-spec op spec)))

(in-theory
 (disable
  (:definition v*-spec)
  (v*-spec)
  ))

(defun v*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (append (v*-spec op (skel-spec skel))
                      (v*-list op (cdr skels))))
          (v*-list op (cdr skels))))
    nil))

(defthm open-v*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (v*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (append (v*-spec op (skel-spec skel))
                      (v*-list op (cdr skels))))
          (v*-list op (cdr skels))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (v*-list op skels)
           nil)))
  :hints (("goal" :in-theory '(v*-list))))

(defthm true-listp-v*-list
  (true-listp (v*-list op spec)))

(in-theory (disable (:definition v*-list) (v*-list)))



(defun fixed-spec-p (spec)
  (declare (type t spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (type  (slot-type slot))
                  (skel  (slot-skel slot))
                  (value (slot-val  slot))
                  )
              (let ((base  (skel-base skel))
                    (sspec (skel-spec skel)))
                (and (acl2::unsigned-byte-p (fix-size size) value) ;(wintn 8 size value)
                     (implies* (ptr? type)
                               (and (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size
                                           base)
                                    (fixed-spec-p sspec)))
                     (fixed-spec-p (cdr spec)))))
          (fixed-spec-p (cdr spec))))
    t))

(defthm open-fixed-spec-p
  (implies
   (consp spec)
   (equal (fixed-spec-p spec)
          (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (type  (slot-type slot))
                  (skel  (slot-skel slot))
                  (value (slot-val  slot))
                  )
              (let ((base  (skel-base skel))
                    (sspec (skel-spec skel)))
                (and (acl2::unsigned-byte-p (fix-size size) value); (wintn 8 size value)
                     (implies* (ptr? type)
                               (and (acl2::unsigned-byte-p (fix-size size) base) ;(wintn 8 size base)
                                    (fixed-spec-p sspec)))
                     (fixed-spec-p (cdr spec)))))
          (fixed-spec-p (cdr spec)))))))

(defun fixed-skel-list (list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (and (fixed-spec-p (skel-spec skel))
                   (fixed-skel-list (cdr list))))
          (fixed-skel-list (cdr list))))
    t))

(defthm h*-spec-fixed-spec-p
  (implies
   (fixed-spec-p spec)
   (equal (h*-spec (op :all :x) spec) spec)))

(defthm h*-list-fixed-skel-list
  (implies
   (fixed-skel-list list)
   (equal (h*-list (op :all :x) list) list)))

(defthm fixed-spec-p-h*-spec
  (fixed-spec-p (h*-spec op spec)))

(defthm fixed-skel-list-h*-list
  (fixed-skel-list (h*-list op list)))

(defthm fixed-spec-p-g*-spec
  (fixed-spec-p (g*-spec op ptr spec ram)))

(defthm fixed-skel-list-g*-list
  (fixed-skel-list (g*-list op list ram))
  :hints (("Goal" :in-theory (enable g*-list))))


(defmacro xop (op)
  `(op (op-which ,op) (op-how ,op)))

(defthm atomic-f*-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (f*-spec fop base spec)
          (f*-spec (xop fop) base spec))))

(defthm atomic-h*-op-replacement
  (implies
   (syntaxp (symbolp hop))
   (equal (h*-spec hop spec)
          (h*-spec (xop hop) spec))))

(defthm atomic-g*-op-replacement
  (implies
   (syntaxp (symbolp gop))
   (equal (g*-spec gop ptr spec ram)
          (g*-spec (xop gop) ptr spec ram))))

(defthm atomic-s*-op-replacement
  (implies
   (syntaxp (symbolp sop))
   (equal (s*-spec sop ptr spec ram)
          (s*-spec (xop sop) ptr spec ram)))
  :hints (("Goal" :in-theory (disable
                              ;for efficiency:
                              whichtype OP-BASE ptr? ifix
                                      ))))

(defthm atomic-f*-list-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (f*-list fop list)
          (f*-list (xop fop) list))))

(defthm atomic-h*-list-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (h*-list fop list)
          (h*-list (xop fop) list))))
