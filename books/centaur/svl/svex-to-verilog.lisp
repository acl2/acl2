
; Export an SVEXL instance to Verilog.

; Copyright (C) 2023 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>, <temelmertcan@gmail.com>

(in-package "SVL")

(include-book "svexl/svexl")
(include-book "svex-reduce/width-of-svex")
(include-book "svex-reduce/svex-reduce-with-env")
(include-book "std/strings/pad" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "centaur/sv/svex/vars" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)

;; Start with an svex/svex-alist

;; 1. first detect repeated nodes.
;;     -- can use svex-to-svexl-get-stats from svexl.lisp
;; 2. at every repeated node, try to break into a wire.
;; 3. almost every part-select should trigger a wire-break, unless it can be
;; avoided.
;; 4. every foreign function should trigger  a module break.  If their width is
;; not known through the width-config, then throw an error. User is expected to
;; add module definitions for foreign functions.

(define symbol-name-for-verilog ((x symbolp))
  :mode :program
  (b* ((x (symbol-name x))
       (x (str::strsubst "-" "_" x))
       (X (str::strsubst "+" "_" X))
       ;; 1. maybe improve implementation
       ;; 2. possibly add others...
       )
    x)
  ///
  (defbadge symbol-name-for-verilog))

(defmacro nicer-fmt-to-string (m &rest args)
  `(b* ((m (msg ,m ,@args))
        ((mv & str) (fmt-to-string (car m) (cdr m)
                                   :fmt-control-alist
                                   `((fmt-soft-right-margin . 20000)
                                     (fmt-hard-right-margin . 20000)))))
     (str::trim str)))

(defmacro svex-to-verilog-ret (current-expr width signed &rest rest)
  `(mv ,current-expr
       ,width
       ,signed
       verilog-lines
       svex-to-wires
       wire-cnt
       ,@rest))

(acl2::def-b*-binder svex-to-verilog-ret
  :body
  (b* ((args acl2::args)
       (forms acl2::forms))
    `(b* (((mv ,(first args) ,(second args) ,(third args) verilog-lines svex-to-wires
               wire-cnt ,@(nthcdr 3 args))
           ,@forms))
       ,acl2::rest-expr)))

;; (b* (((svex-to-verilog-ret cr wd) (mv 1 2 3 4 5)))
;;   (list verilog-lines cr wd ))

;; remove surronding parenthesis of a string.
(define str-remove-sur-parant (str paran-start paran-end
                                   &key (append '""))
  :mode :program
  (b* ((str-exploded (explode str))
       ((when (and (equal (take 1 str-exploded) (explode paran-start))
                   (equal (last str-exploded) (explode paran-end))))
        (str::cat (acl2::implode (cdr (take (1- (len str-exploded)) str-exploded)))
                  append)))
    str))

(defwarrant str::fast-string-append)

(define svex-to-verilog--quoted-aux (val
                                     &key
                                     ((verilog-lines string-listp) 'verilog-lines)
                                     ((svex-to-wires alistp) 'svex-to-wires)
                                     ((wire-cnt natp) 'wire-cnt))
  :mode :program
  (cond ((equal val 0)
         (svex-to-verilog-ret "" 0 nil))
        ((equal val (sv::4vec-x))
         (svex-to-verilog-ret "x" 1 t))
        ((equal val (sv::4vec-z))
         (svex-to-verilog-ret "z" 1 t))
        ((equal val -1)
         (svex-to-verilog-ret "1" 1 t))
        (t (b* (((sv::4vec c) (sv::4vec-part-select 0 1 val))
                ((svex-to-verilog-ret rest-expr rest-size rest-signed)
                 (svex-to-verilog--quoted-aux (sv::4vec-rsh 1 val))))
             (svex-to-verilog-ret
              (str::cat rest-expr (cond ((equal c 1) "1")
                                        ((equal c 0) "0")
                                        ((equal c.lower 1) "z")
                                        ((equal c.upper 1) "x")))
              (1+ rest-size)
              rest-signed))))
  ///
  (define svex-to-verilog--quoted (val
                                   &key
                                   ((verilog-lines string-listp) 'verilog-lines)
                                   ((svex-to-wires alistp) 'svex-to-wires)
                                   ((wire-cnt natp) 'wire-cnt))
    :mode :program
    (b* (((when (equal val 0))
          (svex-to-verilog-ret "0" 0 nil))
         ((svex-to-verilog-ret expr size signed)
          (svex-to-verilog--quoted-aux val)))
      (svex-to-verilog-ret (str::cat (str::intstr size) "'b" expr) size signed)))
  )

;; (define svex-to-verilog-aux--size-val ((val-expr stringp)
;;                                        (size integerp))
;;   :mode :program
;;   (b* ((sd (search "'d" val-expr))
;;        (sb (search "'b" val-expr))
;;        ((Unless (or sd sb))
;;         (str::cat (str::intstr size) "'d" val-expr))


(defines svex-to-verilog-aux
  (define svex-to-verilog-break-to-wire ((x sv::svex-p)
                                         &key

                                         ;; precalculated vals:
                                         (current-expr 'nil)
                                         (width 'nil)
                                         (signed 'nil)

                                         (do-not-save 'nil)

                                         (maybe-width 'nil) ;; if width cannot be retrieved, maybe get it from here.
                                         (force-break  'nil) ;;  normally  an
                                         ;; already   broken
                                         ;; wire will not be
                                         ;; broken again unless force-break is set.
                                         (force-width 'nil) ;; force the width
                                         (enabled 't)
                                         ;;(register-svex 'nil) ;; use this svex to streo svex-to-wires
                                         ((reuse-stats reuse-statsp) 'reuse-stats)
                                         ((verilog-lines string-listp) 'verilog-lines)
                                         ((svex-to-wires alistp) 'svex-to-wires)
                                         ((wire-cnt natp) 'wire-cnt)
                                         ((config svex-reduce-config-p)
                                          'config))
    :mode :program
    :returns (mv new-current-expr width signed verilog-lines new-svex-to-wires new-wire-cnt)
    (b* (((svex-to-verilog-ret current-expr width signed)
          (if (or current-expr width)
              (svex-to-verilog-ret current-expr width signed)
            (svex-to-verilog-aux x)))

         (width (or force-width width))
         (do-not-save (or do-not-save ;; do not save when the original width cannot be used.
                          force-width
                          (and (not width) maybe-width)))
         (force-break (or force-break
                          force-width
                          (and (not width) maybe-width)))
         (width (or width maybe-width))

         ((when (equal width 0))
          (svex-to-verilog-ret "0" width signed))
         ((unless (or force-break
                      (str::substrp " " current-expr)
                      (str::substrp "[" current-expr)
                      (str::substrp "(" current-expr)))
          (svex-to-verilog-ret current-expr width signed))
         ((unless enabled)
          (svex-to-verilog-ret current-expr width signed))

         ;; When width cannot be found, assuming that it is 1-bit wide. this is
         ;; probably dangerous.
         (width (or width
                    (rp::cwe "Warning: couldn't calculate width for: ~p0. Going to assume this is 1-bit wide. ~%" x)
                    1
                    ))

         (new-wire-name (str::cat (if signed "_sw" "_w") (str::intstr wire-cnt)))
         (wire-cnt (1+ wire-cnt))
         (svex-to-wires (if do-not-save svex-to-wires
                          (hons-acons x (list new-wire-name width signed) svex-to-wires)))

         (signed-txt (if signed "signed " ""))

         (verilog-lines ;; list wil be reversed later.
          (cons
           (str::cat
            "    "
            (cond  ((not width) ;; should be unreachable.
                    (str::cat "wire " signed-txt new-wire-name ";") ;; not reachable.
                    )
                   (t
                    (str::cat "wire " signed-txt "[" (str::intstr (1- width)) ":0] " new-wire-name ";")))
            "
    "
            (str::cat "assign " new-wire-name " = "
                      (str-remove-sur-parant current-expr "(" ")")
                      ";"))
           verilog-lines)))
      (svex-to-verilog-ret new-wire-name width signed)))

  (define svexlist-to-verilog-aux ((lst sv::svexlist-p)
                                   &key
                                   ((reuse-stats reuse-statsp) 'reuse-stats)
                                   ((verilog-lines string-listp) 'verilog-lines)
                                   ((svex-to-wires alistp) 'svex-to-wires)
                                   ((wire-cnt natp) 'wire-cnt)
                                   ((config svex-reduce-config-p)
                                    'config))
    (declare (ignorable config))
    :mode :program
    :returns (mv current-exprs widths signeds
                 verilog-lines
                 new-svex-to-wires
                 new-wire-cnt)
    (if (atom lst)
        (svex-to-verilog-ret nil nil nil)
      (b* (((svex-to-verilog-ret expr1 width1 signed1) (svex-to-verilog-aux (car lst)))
           ((svex-to-verilog-ret exprs widths signeds) (svexlist-to-verilog-aux (cdr lst))))
        (svex-to-verilog-ret (cons expr1 exprs)
                             (cons width1 widths)
                             (cons signed1 signeds)))))

  ;; (defines svex-to-verilog-aux
  (define svex-to-verilog-aux ((x sv::svex-p)
                               &key
                               ((reuse-stats reuse-statsp) 'reuse-stats)
                               ((verilog-lines string-listp) 'verilog-lines)
                               ((svex-to-wires alistp) 'svex-to-wires)
                               ((wire-cnt natp) 'wire-cnt)
                               ((config svex-reduce-config-p)
                                'config)
                               )
    (declare (ignorable config))
    :mode :program
    :returns (mv current-expr width signed
                 verilog-lines
                 new-svex-to-wires
                 new-wire-cnt)
    (b* ((already-parsed? (hons-get x svex-to-wires))
         ((when already-parsed?)
          ;; first value is string expressions, second value is calculated width for the svex.
          (svex-to-verilog-ret (first (cdr already-parsed?))
                               (second (cdr already-parsed?))
                               (third (cdr already-parsed?))))
         (repeated-node? (should-be-an-svexl-node reuse-stats x)))
      (sv::svex-case
       x
       :var (svex-to-verilog-ret
             (if (symbolp x)
                 (symbol-name-for-verilog x)
               (raise "Unexpected var name: ~p0 ~%" x))
             nil
             nil)
       :quote (b* ((val x.val)
                   ((svex-to-verilog-ret expr width signed)
                    (if (integerp val)
                        (svex-to-verilog-ret
                         ;;(str::intstr (abs val))
                         (if (equal val 0)
                             "0" ;; freaks out about 0'd0.
                           (str::cat (str::intstr (integer-length val)) "'d" (str::intstr (abs val))))
                         (integer-length val)
                         (< val 0))
                      (svex-to-verilog--quoted val)))
                   ((when signed)
                    (svex-to-verilog-break-to-wire x
                                                   :width width
                                                   :current-expr expr
                                                   :signed t
                                                   :force-break t)))
                (svex-to-verilog-ret expr width signed))
       :call
       (b* (((svex-to-verilog-ret current-expr width signed break-to-wire2?)
             (cond
              ((and* (equal x.fn 'sv::concat)
                     (equal-len x.args 3))
               (b* ((width0 (first x.args))
                    (- (or (natp width0)
                           (raise "Expected natp for the 1st argument of concat: ~p0" x)))
                    (term1 (second x.args))
                    (term2 (third x.args))
                    ((svex-to-verilog-ret arg1 ?width1 ?signed1)
                     (svex-to-verilog-break-to-wire term1
                                                    :maybe-width width0
                                                    :enabled (or (not (equal (sv::svex-kind term1) :call))
                                                                 (not (equal (sv::svex-call->fn term1) 'sv::concat)))))
                    ((svex-to-verilog-ret arg2 ?width2 ?signed2)
                     (svex-to-verilog-break-to-wire term2
                                                    :enabled (or (not (equal (sv::svex-kind term2) :call))
                                                                 (not (equal (sv::svex-call->fn term2) 'sv::concat)))))

                    ((svex-to-verilog-ret arg1 ?width1 ?signed1)
                     (if (or (not width1)
                             (and #|signed1|# (> width0 width1)))
                         ;; break into  a wire when  the concat size  is larger
                         ;; but do  not save because  breaking the wire  with a
                         ;; custom width
                         (svex-to-verilog-break-to-wire term1
                                                        :current-expr arg1 :width width0 :signed nil
                                                        :do-not-save t
                                                        :force-break t)
                       (svex-to-verilog-ret (str-remove-sur-parant arg1 "{" "}") width1 signed1)))

                    (arg2 (str-remove-sur-parant arg2 "{" "}"))

                    (lsb arg1
                         #|(if (and (integerp (second x.args))
                         (not (str::strprefixp "_" arg1)))
                         (str::cat (str::intstr width0) "'d" arg1)
                         arg1)|#
                         #|(if (and (or (natp width1)
                         (rp::cwe "Warning! Size of this svex inside concat couldn't be calculated: ~p0~%" arg1))
                         (< width1 width0))
                         ;; fill with zeros when the lsb's size is smaller.
                         (str::cat "{" (str::intstr (+ (- width1) width0))
                         "'d0" ;; padding with zero  will only
                         ;; happen when  unsigned because
                         ;; arg1  is broken  into a  wire
                         ;; above.
                         ", " arg1 "/* extra */}")
                         arg1)|#)

                    (msb arg2 #|(if (and (integerp (third x.args))
                         (not (str::strprefixp "_" arg2))
                         )
                         (str::cat (str::intstr width2) "'d" arg2)
                         arg2)|#)

                    (current-expr (if (equal (third x.args) 0) ;; freaks out when it sees "0'd0" in verilog code.
                                      lsb
                                    (str::cat "{"  msb ", " lsb "}")))
                    (width (and (natp width2) (+ width0 width2))))
                 (svex-to-verilog-ret current-expr width signed2 nil)))
              ((and* (eq x.fn 'sv::zerox)
                     (equal-len x.args 2))
               (b* ((w (first x.args))
                    (term (second x.args))
                    (- (or (natp w)
                           (raise "Expected natp for the 1st argument of zerox: ~p0" x)))

                    ;; this is basically partsel, so I will let that code handle this.
                    ((svex-to-verilog-ret current-expr width signed)
                     (svex-to-verilog-aux (hons-list 'sv::partsel 0 w term)))
                    )
                 (svex-to-verilog-ret current-expr width signed nil)))

              ((and* (or (eq x.fn 'sv::bitxor)
                         (eq x.fn 'sv::bitor)
                         (eq x.fn 'sv::+)
                         (eq x.fn 'sv::b-)
                         (eq x.fn 'sv::*)
                         (eq x.fn 'sv::==)
                         (eq x.fn 'sv::==??)
                         (eq x.fn 'sv::bitand))
                     (equal-len x.args 2))
               (b* (((svex-to-verilog-ret arg1 width1 signed1) (svex-to-verilog-aux (first x.args)))
                    ((svex-to-verilog-ret arg2 width2 signed2) (svex-to-verilog-aux (second x.args)))

                    (current-expr (str::cat "("
                                            arg1
                                            " "
                                            (cond ((eq x.fn 'sv::+) "+")
                                                  ((eq x.fn 'sv::b-) "-")
                                                  ((eq x.fn 'sv::*) "*")
                                                  ((eq x.fn 'sv::bitxor) "^")
                                                  ((eq x.fn 'sv::bitand) "&")
                                                  ((eq x.fn 'sv::bitor) "|")
                                                  ((eq x.fn 'sv::==) "==")
                                                  ((eq x.fn 'sv::==??) "=="))
                                            " "
                                            arg2
                                            ")"))

                    (signed (cond ((eq x.fn 'sv::+) (or signed1 signed2))
                                  ((eq x.fn 'sv::b-) t)
                                  ((eq x.fn 'sv::*) (or signed1 signed2))
                                  ((eq x.fn 'sv::bitxor) (or signed1 signed2))
                                  ((eq x.fn 'sv::bitor) (or signed1 signed2))
                                  ((eq x.fn 'sv::bitand) (and signed1 signed2))
                                  ((eq x.fn 'sv::==) t)
                                  ((eq x.fn 'sv::==??) t)))

                    (width (and (natp width1) (natp width2)
                                (cond ((eq x.fn 'sv::+) (integer-length (+ (1- (expt 2 width1)) (1- (expt 2 width2)))))
                                      ((eq x.fn 'sv::b-) (1+ (max width1 width2))) ;; this is prob not right...
                                      ((eq x.fn 'sv::*) (+ width1 width2))
                                      ((eq x.fn 'sv::bitxor) (max width1 width2))
                                      ((eq x.fn 'sv::bitor) (max width1 width2))
                                      ((eq x.fn 'sv::bitand) (min width1 width2))
                                      ((eq x.fn 'sv::==) 1)
                                      ((eq x.fn 'sv::==??) 1)))))
                 (svex-to-verilog-ret current-expr width signed nil)))
              ((and* (eq x.fn 'sv::bitnot)
                     (equal-len x.args 1))
               (b* (((svex-to-verilog-ret arg1 width1 ?signed1) (svex-to-verilog-aux (first x.args)))
                    (current-expr (str::cat "(~" arg1 ")"))
                    (signed t) ;; to match 4vec-* notation. This is probably ok.
                    (width width1))
                 (svex-to-verilog-ret current-expr width signed t)))
              ((and* (eq x.fn 'sv::u-)
                     (equal-len x.args 1))
               (b* (((svex-to-verilog-ret arg1 width1 ?signed1)
                     (svex-to-verilog-break-to-wire (first x.args)
                                                    :force-break t))
                    (current-expr (str::cat "(-" arg1 ")"))
                    (signed t) ;; todo: is this right????
                    (width width1))
                 (svex-to-verilog-ret current-expr width signed t)))
              ((and* (eq x.fn 'sv::xdet)
                     (equal-len x.args 1))
               (b* (((svex-to-verilog-ret arg1 width1 ?signed1)
                     (svex-to-verilog-break-to-wire (first x.args)
                                                    :force-break t))
                    (current-expr (str::cat "(" arg1 " + 0)")))
                 (svex-to-verilog-ret current-expr width1 signed1 nil)))
              ((and* (or (eq x.fn 'sv::unfloat)
                         (eq x.fn 'sv::id))
                     (equal-len x.args 1))
               (b* (((svex-to-verilog-ret arg1 width signed) (svex-to-verilog-aux (first x.args))))
                 (svex-to-verilog-ret arg1 width signed nil)))

              ((and* (eq x.fn 'sv::partsel)
                     (equal-len x.args 3))
               (b* ((s (first x.args))
                    (w (second x.args))
                    (- (or (natp s)
                           (raise "Expected natp for the 1st argument of partsel: ~p0" x)))
                    (- (or (natp w)
                           (raise "Expected natp for the 2nd argument of partsel: ~p0" x)))
                    (term (third x.args))

                    ((svex-to-verilog-ret arg1 width1 signed1)
                     (svex-to-verilog-break-to-wire term
                                                    ;;:maybe-width (+ s w)
                                                    ))

                    ;; when it is signed break again in case its size is smaller so it is safely sign extended.
                    ((svex-to-verilog-ret arg1 width1 signed1)
                     (if (or (and signed1 (or (not (and (natp w) (natp width1) (natp s)))
                                              (< width1 (+ s w)))
                                  )
                             (sv::4vec-p term))
                         (svex-to-verilog-break-to-wire
                          term
                          :current-expr arg1
                          :width (+ s w)
                          :signed nil ;; make it no longer signed..
                          :do-not-save t
                          :force-break t)
                       (svex-to-verilog-ret arg1 width1 signed1)))

                    ((when (and (equal s 0)
                                (equal w width1)
                                (not signed1)))
                     (svex-to-verilog-ret arg1 w nil nil))

                    (w (if (and (natp w) (natp width1) (natp s))
                           (if (< width1 (+ w s)) (- width1 s) w)
                         w))

                    (current-expr (cond ((<= w 0)
                                         "0")
                                        ((equal w 1)
                                         (str::cat arg1 "[" (str::intstr s) "]"))
                                        (t
                                         (str::cat arg1 "[" (str::intstr (+ -1 s w)) ":" (str::intstr s) "]")))))
                 (svex-to-verilog-ret current-expr (nfix w) nil nil)))

              ((and* (or (eq x.fn 'sv::rsh)
                         (eq x.fn 'sv::lsh))
                     (equal-len x.args 2))
               (b* ((w (first x.args))
                    (- (or (natp w)
                           (raise "Expected natp for the 1st argument of rsh/lsh: ~p0" x)))
                    ((svex-to-verilog-ret arg1 width1 signed1) (svex-to-verilog-aux (second x.args)))
                    (current-expr (str::cat "(" arg1 ")"
                                            (cond ((eq x.fn 'sv::lsh) " >> ")
                                                  ((eq x.fn 'sv::rsh) " << "))
                                            (str::intstr w)))
                    (width (if (integerp width1)
                               (cond ((eq x.fn 'sv::lsh) (+ (ifix w) width1))
                                     ((eq x.fn 'sv::rsh) (+ (- (ifix w)) width1)))
                             nil)))
                 (svex-to-verilog-ret current-expr width signed1 nil)))

              ((and* (or (eq x.fn 'sv::signx))
                     (equal-len x.args 2))
               (b* ((w (first x.args))
                    (- (or (natp w)
                           (raise "Expected natp for the 1st argument of signx ~p0" x)))

                    ((svex-to-verilog-ret arg1 ?width1 ?signed)
                     ;; this is kind of like part select so I will let that handle it.
                     (svex-to-verilog-break-to-wire (hons-list 'sv::partsel 0 w (second x.args))
                                                    ;;:force-break t
                                                    ))
                    (current-expr (str::cat "signed'("arg1")"))
                    )
                 (svex-to-verilog-ret current-expr w t nil)))

              ((and* (or (eq x.fn 'sv::uor)
                         (eq x.fn 'sv::uand)
                         (eq x.fn 'sv::uxor))
                     (equal-len x.args 1))
               (b* (((svex-to-verilog-ret arg1 ?width1 ?signed1)
                     (svex-to-verilog-break-to-wire (first x.args)))
                    (current-expr (str::cat "("
                                            (cond ((eq x.fn 'sv::uor) "|")
                                                  ((eq x.fn 'sv::uand) "&")
                                                  ((eq x.fn 'sv::uxor) "^"))
                                            arg1
                                            ")"
                                            )))
                 (svex-to-verilog-ret current-expr 1 t t)))

              ((and* (or* (equal x.fn 'sv::?!)
                          (equal x.fn 'sv::?)
                          (equal x.fn 'sv::?*)
                          (equal x.fn 'sv::bit?!)
                          (equal x.fn 'sv::bit?))
                     (equal-len x.args 3))
               (b* (((svex-to-verilog-ret arg1 w1 ?s1) (svex-to-verilog-aux (first x.args)))
                    ((svex-to-verilog-ret arg2 w2 ?s2) (svex-to-verilog-aux (second x.args)))
                    ((svex-to-verilog-ret arg3 w3 ?s3) (svex-to-verilog-aux (third x.args)))
                    (current-expr
                     (str::cat "(" arg1 " ? " arg2 " : " arg3 ")"))
                    (w (max (nfix w1) (max (nfix w2) (nfix w3)))))
                 (svex-to-verilog-ret current-expr (if (equal w 0) nil w) (or s2 s3) nil)))

              (t
               (b* (((svex-reduce-config config) config)
                    (obj (assoc-equal x.fn config.width-extns))
                    ((unless obj) (svex-to-verilog-ret (raise "unexpected svex: ~p0 ~%" x) nil nil nil))
                    ((width-of-svex-extn obj) obj)
                    ((unless (equal (len x.args) obj.arg-len))
                     (svex-to-verilog-ret (raise "unexpected svex: ~p0 ~%" x) nil nil nil))
                    ((svex-to-verilog-ret exprs widths ?signeds) (svexlist-to-verilog-aux x.args))
                    (width (width-of-svex-extn-formula-eval obj.formula x.args widths))
                    (width (if (natp width) width (raise "Problem calculating width for svex: ~p0. Arg widths: ~p1 ~%" x widths)))
                    (wire-name (str::cat "_mw" (str::intstr wire-cnt)))
                    (line1 (str::cat "    wire [" (str::intstr (1- width)) ":0] " wire-name ";
"))
                    (module-name (acl2::string-downcase (symbol-name-for-verilog x.fn)))
                    (line2 (str::cat "    " module-name " _m" (str::intstr wire-cnt) "("
                                     (str::fast-string-append-lst
                                      (loop$ for x in exprs collect (str::cat x ", ")))
                                     wire-name ");"))
                    (verilog-lines (list* (str::cat line1 line2) verilog-lines))
                    (wire-cnt (1+ wire-cnt))
                    (svex-to-wires (hons-acons x (list wire-name width) svex-to-wires))
                    )

                 ;; BOZO: forcing the signed to be nil which should be ok 99% of the time.
                 (svex-to-verilog-ret wire-name width nil nil)))))

            (break-to-wire? (or repeated-node?
                                break-to-wire2?
                                ;; if the expressions grow too large, break it into a wire.
                                (> (length current-expr)
                                   300)))

            ((svex-to-verilog-ret current-expr width signed)
             (svex-to-verilog-break-to-wire x
                                            :current-expr current-expr
                                            :width width
                                            :signed signed
                                            :enabled break-to-wire?)))

         (svex-to-verilog-ret current-expr width signed)))))

  ///
  ;;(profile 'svex-to-verilog-aux)
  )

(acl2::defines get-svex-var-sizes-aux
  (define get-svex-var-sizes-aux ((x sv::Svex-p)
                                  &key
                                  (already-parsed 'already-parsed)
                                  (collected 'collected))
    :mode :program
    :measure (sv::svex-count x)
    :returns (mv collected already-parsed)
    (if (hons-get x already-parsed)
        (mv collected already-parsed)
      (sv::svex-case
       x
       :var (mv collected already-parsed)
       :quote (mv collected already-parsed)
       :call
       (cond ((and (equal x.fn 'sv::partsel)
                   (equal-len x.args 3)
                   (equal (sv::svex-kind (third x.args)) :var)
                   (natp (second x.args))
                   (natp (first x.args)))
              (b* ((c (hons-assoc-equal (third x.args) collected))
                   (width (+ (second x.args) (first x.args)))
                   (add? (or (not c)
                             (and (natp (cdr c))
                                  (> width (cdr c)))))
                   (collected (if add? (acons (third x.args)
                                              width
                                              collected)
                                collected))
                   (already-parsed (hons-acons x nil already-parsed)))
                (mv collected already-parsed)))
             (t (b* (((mv collected already-parsed)
                      (get-svexlist-var-sizes-aux x.args)))
                  (mv collected (hons-acons x nil already-parsed))))))))
  (define get-svexlist-var-sizes-aux ((lst sv::svexlist-p)
                                      &key
                                      (already-parsed 'already-parsed)
                                      (collected 'collected))
    :measure (sv::svexlist-count lst)
    :returns (mv collected already-parsed)
    (if (atom lst)
        (mv collected already-parsed)
      (b* (((mv collected already-parsed)
            (get-svex-var-sizes-aux (car lst))))
        (get-svexlist-var-sizes-aux (cdr lst)))))
  ///

  (define get-svex-var-sizes ((x sv::Svex-p))
    :mode :program
    (b* (((mv collected already-parsed)
          (get-svex-var-sizes-aux x :collected nil :already-parsed nil))
         (collected (fast-alist-clean collected))
         (- (fast-alist-free already-parsed)))
      collected))

  (define get-svex-alist-var-sizes ((x sv::Svex-alist-p))
    :mode :program
    (b* (((mv collected already-parsed)
          (get-svexlist-var-sizes-aux (strip-cdrs x) :collected nil :already-parsed nil))
         (collected (fast-alist-clean collected))
         (- (fast-alist-free already-parsed)))
      collected)))

(acl2::defconsts *svex-to-verilog-header*
  "
//
// This file is automatically generated by the svl::svex-to-verilog utility in ACL2
// For any problems, questions, and feedback, please contact:
// Mertcan Temel (temelmertcan@gmail.com)
//

"
  )

(progn
  (defwarrant str::fast-string-append-lst)
  (defwarrant str::int-to-dec-string$inline)
  (define deep-flatten (x)
    (if (atom x)
        (if (equal x nil) x (list x))
      (append (deep-flatten (car x))
              (deep-flatten (cdr x)))))
  (defttag :write-to-file-okp)
  (define svex-alist-to-verilog-fn ((x sv::svex-alist-p)
                                    (modulename stringp)
                                    &key
                                    (extra-lines)
                                    (state 'state)
                                    ((config svex-reduce-config-p)
                                     'nil))
    :mode :program
    (b* ((keys (strip-cars x))
         (svexlist (strip-cdrs x))
         (reuse-stats (svex-to-svexl-get-stats-lst nil svexlist))
         ((svex-to-verilog-ret current-exprs ?widths ?signeds)
          (svexlist-to-verilog-aux svexlist
                                   :verilog-lines nil
                                   :wire-cnt 0
                                   :svex-to-wires nil))
         (- (cw "Wire count: ~p0 ~%" wire-cnt))
         (- (fast-alist-free svex-to-wires))
         (- (fast-alist-free reuse-stats))

         (modulename (symbol-name-for-verilog (intern$ modulename "SVL")))
         (filename (nicer-fmt-to-string "~s0.v" modulename))

         (out-declr (str::fast-string-append-lst
                     (loop$ for x in (pairlis$ keys widths) collect
                            (str::cat "output ["
                                      (str::intstr (nfix (1- (cdr x))))
                                      ":0] "
                                      (symbol-name-for-verilog (car x))
                                      ", "))))
          
         (out-assigns (loop$ for x in (pairlis$ keys current-exprs) collect
                             (str::cat "    "
                                       "assign "
                                       (symbol-name-for-verilog (car x))
                                       " = "
                                       (cdr x)
                                       ";")))

         (in-widths (get-svex-alist-var-sizes x))
         (in-declr (acl2::explode
                    (str::fast-string-append-lst
                     (loop$ for x in in-widths collect
                            (str::cat "input ["
                                      (str::intstr (1- (cdr x)))
                                      ":0] "
                                      (symbol-name-for-verilog (car x))
                                      ", ")))))
         (in-declr (acl2::implode (take (- (len in-declr) 2)
                                        in-declr)))

         (out-declr (if in-widths ;; If no inputs are detected, then drop the last comma.
                        out-declr
                      (b* ((out-declr (acl2::explode out-declr)))
                        (acl2::implode (take (- (len out-declr) 2)
                                        out-declr)))))

         (parse-events-for-sanity-check
          (acl2::template-subst
           `((local
              (acl2::defconsts
                (*<module-name>-vl-design* state)
                (b* (((mv loadresult state)
                      (vl::vl-load (vl::make-vl-loadconfig
                                    :start-files '(,filename)))))
                  (mv (vl::vl-loadresult->design loadresult) state))))

             ;; Load SV design.
             (local
              (acl2::defconsts
                (*<module-name>-sv-design*)
                (b* (((mv errmsg sv-design & &)
                      (vl::vl-design->sv-design ,modulename
                                                *<module-name>-vl-design*
                                                (vl::make-vl-simpconfig))))
                  (and errmsg (acl2::raise "~@0~%" errmsg)) sv-design)))

             (local
              (sv::defsvtv exported-design-svtv
                :mod *<module-name>-sv-design*
                :inputs ',(loop$ for x in in-widths collect
                                 `(,(symbol-name-for-verilog (car x)) ,(car x)))
                :outputs ',(loop$ for x in keys collect
                                  `(,(symbol-name-for-verilog x) ,x)))))
           :str-alist `(("<MODULE-NAME>" . ,modulename))))

         (objs (append (list *svex-to-verilog-header*)
                       extra-lines
                       (list
                        (nicer-fmt-to-string
                         "module ~s0 (~s1 ~s2);"
                         modulename
                         out-declr in-declr))
                       (reverse (deep-flatten verilog-lines))
                       out-assigns
                       (list "endmodule")))

         ((mv chan state)
          (open-output-channel! filename
                                :object state)))
      (if chan
          (pprogn
           (acl2::write-objects objs chan state)
           (value parse-events-for-sanity-check))
        (er soft 'write-string-to-file
            "Could not open for writing: ~x0"
            filename)))
    ///
    (profile 'svex-alist-to-verilog-fn))
  (defttag nil))

(define svex-to-verilog-fn ((x sv::svex-p)
                            (modulename stringp)
                            &key
                            (extra-lines)
                            (state 'state)
                            ((config svex-reduce-config-p)
                             'nil))
  :mode :program
  (b* ((alist (acons '_out x nil)))
    (svex-alist-to-verilog-fn alist
                              modulename
                              :extra-lines extra-lines
                              :config config)))


(define rp-rw-context-main-for-svex-simplify ((term rp::rp-termp)
                                              &key
                                              (rp::rp-state 'rp::rp-state)
                                              (state 'state))
  :prepwork
  ((local
    (include-book "projects/rp-rewriter/proofs/rp-correct" :dir :system))
   (local
    (include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system))
   (local
    (include-book "projects/rp-rewriter/proofs/extract-formula-lemmas" :dir :system))
   )
  (b* ((rp::rp-state (rp::rp-state-new-run rp::rp-state))
       (rp::rp-state (rp::rp-state-init-rules nil nil nil
                                              rp::rp-state
                                              state
                                              :ruleset 'svex-simplify-rules))
       ((mv context rp::rp-state)
        (rp::rp-rw-context-main term nil t t (expt 2 20) rp::rp-state state)))
    (mv context rp::rp-state)))

(defmacro svex-alist-to-verilog (svex-alist
                                 &key
                                 (output-file-name '"test")

                                 (output-vars 'nil)
                                 (out-wrappers 'nil) ;; must be an alist. e.g.,: ((res . '(sv::partsel 0 3 res)))

                                 (input-vars  'nil) ;;  the  input   vars  to
                                 ;; keep. If nil, all will be
                                 ;; selected.  The rest  will
                                 ;; be don't care unless they
                                 ;; are bound in the env.
                                 (env 'nil)

                                 (assume ''t)

                                 (export-to-svexl 'nil)
                                 
                                 (sanity-check 't)
                                 ;; maybe skip svex-simplify as it can potentially have soundness bugs.
                                 ;; best to try this out when we get a problem with sanity check.
                                 (skip-svex-simplify 'nil)

                                 (skip-dumping-to-verilog 'nil)
                                 
                                 )
  `(make-event
    (b* ((acl2::__function__ 'svex-alist-to-verilog)
         (svex-alist ,svex-alist)
         (env ,env)
         (out-wrappers ,out-wrappers)
         (output-file-name ,output-file-name)
         (input-vars ',input-vars)
         (output-vars ',output-vars)
         (assume ',assume)
         (export-to-svexl ',export-to-svexl)
         (skip-dumping-to-verilog ,skip-dumping-to-verilog)
         (sanity-check (and (not skip-dumping-to-verilog)
                            ,sanity-check))
         (config nil) ;,svl-config)
         (skip-svex-simplify ,skip-svex-simplify)

         ;; --------------------------------------------------
         ;; 1. prep the svex-alist based on the selected output variables.
         (- (or (subsetp-equal output-vars
                               (strip-cars svex-alist))
                (raise "Given output-vars ~p0 should be a subset of the available output variables ~p1.~%"
                       output-vars (strip-cars svex-alist))))
         (output-vars (or output-vars (strip-cars svex-alist)))
         (svex-alist (loop$ for var in output-vars collect
                            (b* ((svex-entry (hons-assoc-equal var svex-alist))
                                 ;; svex-entry is guaranteed to exist here.
                                 (wrapper (hons-assoc-equal var out-wrappers))
                                 ((unless wrapper) svex-entry)
                                 (new-svex (subst (cdr svex-entry) var (cdr wrapper))))
                              (cons var new-svex))))
         
         ;; --------------------------------------------------
         ;; 2. prep the svex-eval environment
         (all-vars (sv::svex-alist-vars svex-alist))
         (- (or (subsetp-equal input-vars all-vars)
                (raise "Given input-vars ~p0 should be a subset of the available variables ~p1.~%"
                       input-vars all-vars)))
         (input-vars (or input-vars (set-difference-equal all-vars
                                                          (strip-cars env))))
         (falist-env (append (loop$ for x in input-vars collect
                                    `(,x . (rp::rp 'integerp ,x)))
                             env))
         (falist-env (make-fast-alist
                      ;; to make it suitable for svex-reduce-w/-env
                      (add-quotes-to-4vec-values-in-alist falist-env)))

         ;; --------------------------------------------------
         ;; 3. Create context based on given user assumptions
         (assume-orig assume)
         ((mv & assume state)
          (acl2::translate assume t t nil 'svex-alist-to-verilog (w state) state))
         ((mv context rp::rp-state)
          (rp-rw-context-main-for-svex-simplify assume))

         ;; --------------------------------------------------
         ;; 4. Call svex-reduce-w/-env
         (config (change-svex-reduce-config config
                                            :skip-bitor/and/xor-repeated t
                                            :keep-missing-env-vars nil))
         (svex-alist (svl::svex-alist-reduce-w/-env svex-alist
                                                    :env falist-env
                                                    :context context
                                                    :config config))

         ;; so  far all  the tools  are verified,  and the  flow given  here is
         ;; trusted to be sound. Also user given env is applied.
         (- (acl2::sneaky-save 'reference-svex-alist svex-alist))

         ;; --------------------------------------------------
         ;; 5. Call svex-alist-simplify
         ((mv svex-alist rp::rp-state) (if skip-svex-simplify
                                           (mv svex-alist rp::rp-state)
                                         (svex-alist-simplify svex-alist
                                                              :context context)))

         ;; --------------------------------------------------
         ;; 6.  Call svex-alis-reduce again  just in case svex-simplify created
         ;; some constant  but couldn't clean  it up because of  only localized
         ;; simplifications.
         (svex-alist (svl::svex-alist-reduce-w/-env svex-alist
                                                    :env falist-env
                                                    :context context
                                                    :config config))

         (- (acl2::sneaky-save 'final-svexl-alist
                               (svex-alist-to-svexl-alist svex-alist)))

         ((mv & parse-events-for-sanity-check state)
          (if skip-dumping-to-verilog
              (mv nil nil state)
            (svl::svex-alist-to-verilog-fn svex-alist
                                           output-file-name
                                           :extra-lines nil
                                           :config config)))

         (- (fast-alist-free falist-env))

         (export-to-svexl-event (and export-to-svexl
                                     `((with-output
                                         :off :all :on (error)
                                         :gag-mode nil
                                         (acl2::defconsts (,export-to-svexl state)
                                           (acl2::sneaky-load 'final-svexl-alist state))))))
         )
      (if sanity-check
          (mv nil
              `(encapsulate
                 nil
                 ,@export-to-svexl-event
                 
                 (with-output :off :all :on (error) :gag-mode nil
                   (progn ,@parse-events-for-sanity-check
                          (local
                           (acl2::defconsts (*reference-svex-alist* state)
                             (acl2::sneaky-load 'reference-svex-alist state)))))
                 (value-triple (acl2::tshell-ensure))
                 (local
                  (make-event
                   `(:or
                     (fgl::fgl-thm
                      (implies (and (svl::exported-design-svtv-autohyps)
                                    ,',assume-orig)
                               (b* ((orig-out (sv::svex-alist-eval *reference-svex-alist*
                                                                   (svl::exported-design-svtv-autoins)))
                                    (exported-out (sv::svtv-run (svl::exported-design-svtv)
                                                                (svl::exported-design-svtv-autoins)))
                                    (- (cw "~%Output values of the original design: ~p0~%" orig-out))
                                    (- (cw "~%Output values of the exported design: ~p0~%" exported-out)))
                                 (equal orig-out exported-out))))
                     (value-triple (hard-error 'export-to-verilog-after-adder-detection
                                               "Sanity check failed. Please see the counterexample above~%"
                                               nil)))))
                 (value-triple :sanity-check-passed))
              state rp::rp-state)
        (mv nil `(progn ,@export-to-svexl-event
                        (value-triple :done))
            state rp::rp-state)))))



(defmacro svex-to-verilog (svex
                           &key
                           (output-file-name '"test")
                           (out-wrapper 'nil) ;; must be an alist. e.g.,: ((res . '(sv::partsel 0 3 res)))

                           (input-vars  'nil) ;;  the  input   vars  to
                           ;; keep. If nil, all will be
                           ;; selected.  The rest  will
                           ;; be don't care unless they
                           ;; are bound in the env.
                           (env 'nil)

                           (assume ''t)

                           (export-to-svexl 'nil)
                           
                           (sanity-check 't)
                           ;;(svl-config 'nil)

                           ;; maybe skip svex-simplify as it can potentially have soundness bugs.
                           ;; best to try this out when we get a problem with sanity check.
                           (skip-svex-simplify 'nil)

                           (skip-dumping-to-verilog 'nil)
                           )
  `(make-event
    (b* ((svex ,svex)
         (svex-alist `((_out . ,svex)))
         (out-wrappers (and ,out-wrapper `((out . ,,out-wrapper)))))
      `(svex-alist-to-verilog ',svex-alist
                              :out-wrappers ',out-wrappers
                              
                              :output-file-name ,',output-file-name
                              :input-vars ,',input-vars
                              :env ,',env
                              :assume ,',assume
                              :export-to-svexl ,',export-to-svexl
                              ;;:svl-config ,',svl-config
                              :skip-svex-simplify ,',skip-svex-simplify

                              :sanity-check ,',sanity-check
                              :skip-dumping-to-verilog ,',skip-dumping-to-verilog
                              ))))

(defmacro svtv-to-verilog (svtv
                           &rest args)
  `(svex-alist-to-verilog (sv::svtv->outexprs ,svtv)
                          ,@args
                          ))


(xdoc::defxdoc svex-to-verilog
  :short "Export an SVEX to a Verilog file"
  :parents (svl)
  :long "<p> Dumps a Verilog file based on a given @(see sv::SVEX) </p>
<p> Use:
@(call svex-to-verilog)
</p>
<p> This calls @(see svex-alist-to-verilog) by creating a faux output variable svl::_out. </p>

<p> Example call: </p>

<code>
@('
(svl::svex-to-verilog *my-svex*
                      :output-file-name \"test\"
                      :out-wrapper '(sv::partsel 0 1 svl::_out)
                      :input-vars (srca)
                      :env `((srcb . 0) (srcc . 0) (srcd . 0))
                      :assume (and (equal (svl::bits srca 24 1) 0))
                      :skip-svex-simplify nil)
')
</code>

<p> See @(see svex-alist-to-verilog) for more details. </p>
")

(xdoc::defxdoc svtv-to-verilog
  :short "Export an SVTV instance to a Verilog file"
  :parents (svex-to-verilog)
  :long "<p> Dumps a Verilog file based on a given @(see sv::defsvtv$) </p>
<p> This calls @(see svex-alist-to-verilog) by extracting svex-alist from SVTV. Please see  @(see svex-alist-to-verilog) for more details. Example use: </p>

<code>
@('
(svl::svtv-to-verilog (my-svtv)
                      :output-file-name \"test\"
                      :output-vars (my-out)
                      :out-wrappers '((my-out . (sv::partsel 4 4 my-out)))
                      :input-vars (srca)
                      :env `((srcb . 0) (srcc . 0) (srcd . 0))
                      :assume (and (equal (svl::bits srca 24 1) 0))
                      :skip-svex-simplify nil)
')
</code>

")

(xdoc::defxdoc svex-alist-to-verilog
  :short "Export an SVEX-ALIST to a Verilog file"
  :parents (svex-to-verilog)
  :long "<p> Dumps a Verilog file based on a given @(see sv::svex-alist) </p>
<p> Use:
@(call svex-alist-to-verilog)
</p>

<p> This program dumps a Verilog file from a given svex-alist by simplifying
the given expressions based on user configurations. These can include binding
some input variables to contants, masking certain portions of the output,
simplifying expressions based on user-defined rewrite rules, and so on. </p>

<p> Example use: </p>
<code>
@('
(svl::svex-alist-to-verilog (sv::svtv->outexprs (evfalu-run))
                            :output-file-name \"test\"
                            :output-vars (my-out)
                            :out-wrappers '((my-out . (sv::partsel 4 4 my-out)))
                            :input-vars (srca)
                            :env `((srcb . 0) (srcc . 0) (srcd . 0))
                            :assume (and (equal (svl::bits srca 24 1) 0))
                            :skip-svex-simplify nil
                            :export-to-svexl *test-svexl*)
')
</code>

<p> The arguments: </p>
<ul>
<li>
:output-file-name will be used to determine the name of the resulting Verilog
file and module name.
</li>

<li>
:output-vars should be the list of output-variables that will be included in
the output file.
</li>

<li>
:out-wrappers is an optional argument and can be used to wrap output
expressions inside other expressions. This can be useful for when selecting a
certain portion of the output. In the example above, only my-out[7:4] will
appear in the output file.
</li>

<li>
:input-vars is a list of input variables that needs to be left as a free
variable. When nothing is provided, the program will use all available
variables. 
</li>

<li>
:env can be used to bind variables to constants. If a variable is bound to a
constant, and :input-vars includes it in its list, then :input-vars will
override it unless :input-vars is nil.
</li>

<li>
:assume should be an untranslated term that the user wants to assume during
simplification. The assumptions given are not guaranteed to be applied. Adding
rewrite rules for @(see svex-simplify) might help in those cases.
</li>

<li>
:sanity-check is highly recommended. There are 2 components in this program
whose soundness are in question. First one is @(see svl::svex-simplify), which
uses @(see rp::rp-rewriter) to conduct its simplifications with some wrappers
around it. Even though rp::rp-rewriter is verified, that surrounding program
might be buggy. The second part that might have soundness bugs is the part of
the program that creates the resulting Verilog file content. The sanity check
mechanism makes sure that the resulting file is functionally equivalent to the
input expressions under the given user configurations. Sanity check is
performed by parsing the output file with VL/SV/SVTV and using FGL. Setting up
AIG transforms is recommended especially for slow cases.
</li>


<li>
:skip-svex-simplify should be nil or t, and it is nil default. It tells the
program to skip @(see svl::Svex-simplify) stage. This is worthwhile to try in
case sanity-check fails.
</li>

<li>
:export-to-svexl should be nil or a name for a constant. It exports an ACL2
constant containing an svexl object after all the svex simplifications.
</li>
</ul>
")




;; (svex-to-verilog-fn
;;  '(sv::partsel 0 15 (sv::concat 4 (sv::signx 1 srca)
;;                                 (sv::concat 4
;;                                             (sv::concat 1 c 0)
;;                                             (sv::concat 3
;;                                                         (sv::uand (sv::signx 2 c))
;;                                                         0))))
;;  "testmult")

;; :i-am-here

;; (time$
;;  (svex-alist-to-verilog-fn (acons 'my-out2 (@ svex) nil)
;;                            "testmult"
;;                            :config (rp::svex-reduce-w/-env-config-1)

;;                            :extra-lines
;;                            (list "
;; module ha_c_chain(input a, input b, output o);
;;    assign o = a & b;
;; endmodule

;; module ha_s_chain(input a, input b, output o);
;;     assign o = a ^ b;
;; endmodule

;; module ha_1_c_chain(input a, input b, output o);
;;     assign o = a | b;
;; endmodule

;; module ha_1_s_chain(input m, input a, input b, output o);
;;     assign o = a ^ b ^ 1'b1;
;; endmodule

;; module fa_c_chain(input m, input a, input b, input c, output o);
;;     assign o = a & b | a & c | b & c;
;; endmodule

;; module fa_s_chain(input a, input b, input c, output o);
;;     assign o = a ^ b ^ c;
;; endmodule")
;;                            ))

;; (time$
;;  (svex-to-verilog-fn `(sv::bitor (sv::partsel 0 16 (sv::uor (partsel 0 4 srca))) ,(@ svex))
;;                      "testmult"
;;                      :config (rp::svex-reduce-w/-env-config-1)
;;                      :extra-lines
;;                      (list "
;; module ha_c_chain(input a, input b, output o);
;;    assign o = a & b;
;; endmodule

;; module ha_s_chain(input a, input b, output o);
;;     assign o = a ^ b;
;; endmodule

;; module ha_1_c_chain(input a, input b, output o);
;;     assign o = a | b;
;; endmodule

;; module ha_1_s_chain(input m, input a, input b, output o);
;;     assign o = a ^ b ^ 1'b1;
;; endmodule

;; module fa_c_chain(input m, input a, input b, input c, output o);
;;     assign o = a & b | a & c | b & c;
;; endmodule

;; module fa_s_chain(input a, input b, input c, output o);
;;     assign o = a ^ b ^ c;
;; endmodule")
;;                      ))

;; :i-am-here

;; (acl2::defconsts
;;   (*mult2-vl-design* state)
;;   (b* (((mv loadresult state)
;;         (vl::vl-load (vl::make-vl-loadconfig
;;                       :start-files '("testmult.v")))))
;;     (mv (vl::vl-loadresult->design loadresult) state)))

;; ;; Load SV design.
;; (acl2::defconsts
;;   (*mult2-sv-design*)
;;   (b* (((mv errmsg sv-design & &)
;;         (vl::vl-design->sv-design "testmult"
;;                                   *mult2-vl-design*
;;                                   (vl::make-vl-simpconfig))))
;;     (and errmsg
;;          (acl2::raise "~@0~%" errmsg))
;;     sv-design))

;; (sv::defsvtv test-svtv
;;   :mod *mult2-sv-design*
;;   :inputs '(("SRCA" srca)
;;             ("SRCB" srcb))
;;   :outputs
;;   '(("_OUT" result)
;;     ("_w10" _w10)
;;     ("_w11" _w11)))

;; (acl2::defconsts *svex* (@ svex))

;; (rp::add-rp-rule test-svtv-autohyps)
;; (rp::add-rp-rule test-svtv-autoins)

;; (sv::Svtv-run (test-svtv)
;;               (test-svtv-autoins :srca 1
;;                                  :srcb 0))

;; (rp::defthmrp-then-fgl test
;;   (implies (test-svtv-autohyps)
;;            (b* (((sv::svassocs result)
;;                  (hide (sv::svtv-run (hide (test-svtv))
;;                                      (test-svtv-autoins)))))
;;              (equal result
;;                     (sv::svex-eval$ *svex*
;;                                     (test-svtv-autoins)))))
;;   :disable-meta-rules (rp::s-c-spec-meta))
