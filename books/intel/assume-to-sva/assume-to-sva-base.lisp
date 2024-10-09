; Copyright (C) Intel Corporation
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

; Basic constants, functions, and types needed for generate SVAs from ACL2 SVTV
; proof assumptions.

(in-package "SV")

(include-book "std/strings/pretty" :dir :system)
(include-book "std/strings/suffixp" :dir :system)
(include-book "centaur/sv/svex/4vec-base" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

(define conspn1 (x (n natp))
  (if (zp n)
      `((null ,x))
    (cons `(consp ,x)
          (conspn1 `(cdr ,x) (1- n)))))

(defmacro conspn (x n)
  (if (zp n)
      x
    (cons 'and (conspn1 x n))))

(defconst *acl2-equal-fns-to-vl*
  '((equal ("(" s0 " == " s1 ")"))))

(defconst *acl2-bitops-fns-to-vl*
  '((lognot         ("(" "~" s0 ")"))
    ;; is this the right operator?
    (binary-logxor  ("(" s0 " ^ " s1 ")"))
    (binary-logand  ("(" s0 " & " s1 ")"))
    (binary-logior  ("(" s0 " | " s1 ")"))
    (acl2::loghead$inline
                    (s1 "[ 0 +:" s0 "]")
                    ;; ("(" s1 " & " "((1 << " s0 ") - 1))")
                    )
    ))

(defconst *acl2-logops-fns-to-vl*
;    acl2      vl    arity
  '((not       ("(" "!" s0 ")"))
    (implies   ("(" s0 " -> " s1 ")"))
    (<         ("(" s0 " < " s1 ")"))
    (xor       ("(" s0 " ^ " s1 ")")))
  ;; ACL2-AND/OR and VL-AND/OR have different semantics.
  ;; In ACL2, (and a b) := (if a b nil)
  ;; In VL, a && b := a != 0 ? b != 0 : 0
  )

(defconst *acl2-arithops-fns-to-vl*
  '((acl2::binary-*     ("(" s0 " * " s1 ")"))
    (acl2::imod$inline  ("(" s0 " % " s1 ")"))
    ))

(defconst *acl2-misc-fns-to-vl*
;    acl2         vl        arity
  '(;; !!! [VR]: member-equal has different semantics than VL member. ACL2
    ;; member-equal returns the remainder of the list.
    (member-equal ("`member(" s0 "," s1 "," s2 ")"))
    (if           ("(" s0 " ? " s1 " : " s2 ")"))
    ;; SystemVerilog Manual: "Both msb_expr and lsb_expr shall be constant
    ;; integer expressions."
    (sv::4vec-part-select
                  (s2 "[" s0 "+:" s1 "]"))
    ))

(defconst *acl2-fn-to-vl*
  (make-fast-alist
   (append *acl2-equal-fns-to-vl*
           *acl2-bitops-fns-to-vl*
           *acl2-logops-fns-to-vl*
           *acl2-arithops-fns-to-vl*
           *acl2-misc-fns-to-vl*)
   ))

(define subst-targetp (x)
  (if (atom x)
      (null x)
    (b* ((el (car x)))
      (and (or (stringp el)
               (member-eq el '(s0 s1 s2)))
           (subst-targetp (cdr x))))))

(define make-subst1 ((target subst-targetp)
                     (arg0 acl2::maybe-stringp)
                     (arg1 acl2::maybe-stringp)
                     (arg2 acl2::maybe-stringp))
  :returns r
  :guard-hints (("Goal" :in-theory (enable subst-targetp)))
  (if (atom target)
      nil
    (b* ((el (car target))
         (new-el
          (cond ((equal el 's0)
                 (or arg0
                     (prog2$ (raise "arg0 should be non-nil!")
                             "")))
                ((equal el 's1)
                 (or arg1
                     (prog2$ (raise "arg1 should be non-nil!")
                             "")))
                ((equal el 's2)
                 (or arg2
                     (prog2$ (raise "arg2 should be non-nil!")
                             "")))
                (t el))))
      (cons new-el (make-subst1
                    (cdr target) arg0 arg1 arg2))))
  ///
  (defret string-listp-<fn>
    :hyp :guard
    (string-listp r)
    :hints (("Goal" :in-theory (enable subst-targetp)))))

(define make-subst ((fn symbolp)
                    (args string-listp))
  :returns (r :hyp :guard string-listp)
  (b* ((entry (hons-get fn *acl2-fn-to-vl*))
       ((unless entry)
        (raise "Unsupported function ~x0" fn))
       (target (second entry))
       (arg0 (first args))
       (arg1 (second args))
       (arg2 (third args)))
    (make-subst1 target arg0 arg1 arg2)))

(define add-literals ((x string-listp)
                      (literal stringp))
  "Inserts a string literal in between each string in a list"
  :returns (r string-listp)
  (if (endp x) ()
    (cons (if (endp (rest x))
              (acl2::str-fix (first x))
            (str::cat (first x) literal))
          (add-literals (rest x) literal))))

(define part-select-p (x)
  "Recognizer for a term that performs a part-select on a vl variable"
  (case-match x
    (('sv::4vec-part-select lsb width var)
     ;; SystemVerilog Manual: "The size of the part-select or slice shall be
     ;; constant, but the position can be variable".  [VR]: For simplicity,
     ;; assume that all part-select calls use integer lsb and width in ACL2
     ;; assumptions.

     ;; can we support 4vec indices? What do we do about width of indices when
        ;; converting?
     (and (and (quotep lsb)
               (conspn lsb 2)
               (integerp (unquote lsb)))
          (and (quotep width)
               (conspn width 2)
               (integerp (unquote width)))
          (symbolp var)))
    (& nil)))

(define integer-list->vl-array1 ((l integer-listp))
  (if (atom l)
      ""
    (b* ((int-as-str (str::int-to-dec-string (car l))))
      (if (atom (cdr l))
          int-as-str
        (str::cat int-as-str
                  ", "
                  (integer-list->vl-array1 (cdr l)))))))

(define integer-list->vl-array ((l integer-listp))
  "Convert an integer-list into a verilog array"
  (str::cat "{"
            (integer-list->vl-array1 l)
            "}"))

; Recognizing "zero" in SystemVerilog
(define sva-valid-basep ((x characterp))
  (member x '(#\b #\o #\d #\h #\d
              #\B #\O #\D #\H #\D)))

(define all-zero-until-base ((x character-listp))
  (if (atom x)
      t
    (b* ((char (car x)))
      (cond ((eql char #\0)
             (all-zero-until-base (cdr x)))
            ((sva-valid-basep char) (and (consp (cdr x))
                                         (eql (second x) #\')))
            (t nil)))))

(local
 (defthm character-listp-reverse
   (implies (character-listp x)
            (character-listp (reverse x)))))

(local
; Matt K. addition: It is surprising that this lemma is needed for ACL2(r), but
; without it, a proof fails in ACL2(r) for the define form below.
 (defthm realp-len
   (real/rationalp (len x))))

(define sva-str-zerop ((x stringp))
  "Check that a verilog string is all zero until the base character"
  (b* ((l (reverse (coerce x 'list))))
    (or (equal x "'0") ; special case: unbased, unsized literal
        (and (< 0 (len l))
             (all-zero-until-base l)))))

; Some help with formatting a generated SystemVerilog property RHS string

(local
 (defthm character-listp-rev
   (implies (character-listp l)
            (character-listp (rev l)))))

(define del-spaces ((l character-listp))
  :returns (r :hyp :guard character-listp)
  (if (atom l)
      nil
    (if (eql (car l) #\Space)
        (del-spaces (cdr l))
      l))
  ///
  (defret acl2-count-<fn>
    (<= (acl2-count (del-spaces l))
        (acl2-count l))
    :rule-classes :linear))

(define split-on-space ((l character-listp)
                        (acc character-listp))
  :returns (mv (l1 :hyp :guard character-listp) (l2 :hyp :guard character-listp))
  (if (atom l)
      (mv nil nil)
    (b* ((char (car l)))
      (if (eql char #\Space)
          (mv (rev acc) (cdr l))
        (split-on-space (cdr l) (cons char acc))))))

(define format-rhs1 ((l character-listp)
                     (line-acc character-listp)
                     (pos natp)
                     (soft-margin natp))
  :returns (r :hyp :guard string-listp)
  :verify-guards nil
  (if (atom l)
      nil
    (b* ((char (car l))
         (cur-line (cons char line-acc)))
      (cond
       ((or (eql char #\?)
            (atom (cdr l)))
        (cons
         (coerce (del-spaces (rev cur-line)) 'string)
         ;;(indent-1
         (format-rhs1 (del-spaces (cdr l)) nil 0 soft-margin)
         ;; )
         ))
       ((<= soft-margin pos)
        ;; search cur-line, which is reversed, for a space and split
        (b* (((mv 2nd-part 1st-part) (split-on-space cur-line nil))
             (rest (format-rhs1
                    (del-spaces (cdr l)) 2nd-part (len 2nd-part) soft-margin)))
          (if (consp 1st-part)
              (cons (coerce (rev 1st-part) 'string) rest)
            rest)))
       (t (format-rhs1 (cdr l) cur-line (1+ pos) soft-margin)))))
  ///
  (verify-guards+ format-rhs1))

(define format-rhs ((s stringp))
  :returns (r string-listp)
  (b* ((l (coerce s 'list)))
    (format-rhs1 l nil 0 acl2::*fmt-hard-right-margin-default*)))
