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

(in-package "SV")

(include-book "svtv-to-sva-runs")
(include-book "centaur/misc/tshell" :dir :system)
(include-book "centaur/fgl/interp-st" :dir :system)
(include-book "strtok-ie")
(include-book "centaur/sv/svtv/structure" :dir :System)
(include-book "std/typed-lists/string-listp" :dir :system)
(include-book "std/strings/strtok" :dir :system)
;;;;

(define skip-leading-wspace-pos ((x stringp) (i natp) (l natp))
  :guard (and (<= i l) (eql l (length x)))
  :measure (nfix (- l i))
  :returns (r natp)
  (if (or (mbe :logic (zp (- l i))
               :exec (eql i l))
          (not (member (char x i) (list #\Newline #\Space #\Tab))))
      (if (mbe :logic (<= i (length x))
               :exec t)
          (lnfix i)
        0)
    (skip-leading-wspace-pos x (1+ i) l))
  ///
  (defthm skip-leading-wspace-pos-<=-len-x
    (implies (and (natp i) (natp l) (<= i l)
                  (eql l (len (acl2::explode x))))
             (<= (skip-leading-wspace-pos x i l)
                 (len (acl2::explode x))))
    :rule-classes (:linear :rewrite)))

(define trim-leading-wspace ((x stringp))
  :returns (r stringp)
  (b* ((i (skip-leading-wspace-pos x 0 (length x))))
    (cond ((mbe :logic (not (stringp x)) :exec nil) "")
          ((eql i 0) x)
          (t (subseq x i nil)))))

(define parse-concats* ((x string-listp) &key ((acc true-listp) 'nil))
  :returns (mv (r true-listp :hyp (true-listp acc))
               (y string-listp :hyp (string-listp x)))
  :measure (len x)
  :verify-guards nil
  (cond ((endp x) (mv acc ()))
        ((equal (first x) "{") ;; start of new concat
         (b* (((mv r y) (parse-concats* (rest x))))
           (if (mbe :logic (< (len y) (len x))
                    :exec t)
               (parse-concats* y :acc (cons r acc))
             (mv () ()))))
        ((equal (first x) "}")
         (mv (reverse acc) (rest x)))
        ((equal (first x) ",")
         (parse-concats* (rest x) :acc acc))
        (t
         (b* ((e (trim-leading-wspace (first x))))
           (parse-concats* (rest x)
                           :acc (if (equal e "") acc (cons e acc))))))
  ///
  (defthm parse-concats*-len-decr
    (implies (consp x)
             (< (len (mv-nth 1 (parse-concats* x :acc acc)))
                (len x)))
    :rule-classes nil))

(verify-guards parse-concats*-fn
  :hints (("Goal" :use ((:instance parse-concats*-len-decr
                                   (x (cdr x)) (acc nil))))))

(define parse-concats ((x stringp))
  :returns (r true-listp)
  (b* (((mv r y)
        (parse-concats* (strtok-ie x (coerce "{}," 'list) ()))))
    (if (atom y) r
      (raise "Imbalanced brackets? should not get here:~x0" x))))

(defines print-concat-mod
 (define print-concat-mod (x (mod stringp))
   :measure (two-nats-measure (acl2-count x) 2)
   :returns (r stringp)
   :verify-guards nil
   (cond ((stringp x)
          (str::cat mod "." x))
         ((atom x)
          (prog2$ (raise "Unexpected atom.. would only come from empty concat?")
                  ""))
         ((and (consp x)
               (atom (rest x)))
          (print-concat-mod (first x) mod))
         (t (str::cat "{" (print-concats-mod x mod) "}"))))

  (define print-concats-mod (x (mod stringp))
    :measure (two-nats-measure (acl2-count x) 1)
    :returns (r stringp)
    (if (atom x) ""
      (str::cat (print-concat-mod (first x) mod)
                (if (atom (rest x)) "" ", ")
                (print-concats-mod (rest x) mod))))
)

(verify-guards print-concat-mod)

;;;;

(define legal-verilog-char-p ((x characterp))
  (or (and (<= (char-code x) (char-code #\9))
           (<= (char-code #\0) (char-code x)))
      (and (<= (char-code x) (char-code #\Z))
           (<= (char-code #\A) (char-code x)))
      (and (<= (char-code x) (char-code #\z))
           (<= (char-code #\a) (char-code x)))
      (eql x #\_)))

(define legal-verilog-chars-p ((x character-listp))
  (or (endp x)
      (and (legal-verilog-char-p (first x))
           (legal-verilog-chars-p (rest x)))))

(define legal-verilog-name-p ((x stringp))
  (legal-verilog-chars-p (coerce x 'list)))

(define lhs-total-width ((x sv::lhs-p))
  :returns (r natp)
  (if (endp x) 0
    (+ (sv::lhrange->w (first x))
       (lhs-total-width (rest x)))))

(local (defthm svex-env-alist
         (implies (sv::svex-env-p x)
                  (alistp x))
         :hints (("Goal" :in-theory (enable alistp)))))

(local (defthm svex-env-is-4vec
         (implies (sv::svex-env-p x)
                  (sv::maybe-4vec-p (cdr (assoc-eq e x))))
         :hints (("Goal" :in-theory (enable sv::maybe-4vec-p sv::svex-env-p)))))

(define get-to-4vec (x (env sv::svex-env-p))
  :returns (r sv::maybe-4vec-p)
  (cond ((eq x :ones)
         -1)
        ((symbolp x)
         (sv::maybe-4vec-fix (cdr (assoc-eq x env))))
        ((sv::4vec-p x)
         x)
        (t (raise "unexpected entry encountered:~x0" x))))

(define svar-name-to-ver-str (x)
  :returns (r stringp)
  (cond ((null x)     "")
        ((symbolp x)  (symb-to-verilog x))
        ((stringp x)  x)
        ((natp x)     (str::natstr x))
        ((atom x)     (prog2$ (raise "unsupported atom:~x0" x)
                              ""))
        (t (str::cat (if (natp (first x))
                         (str::cat "[" (str::natstr (first x)) "]")
                       (str::cat (svar-name-to-ver-str (first x))
                                 "."))
                     (svar-name-to-ver-str (rest x))))))

(define lhrange-ver-str ((x sv::lhrange-p)
                         (cfg svtv-sva-cfg-p))
  :returns (r stringp)
  (b* (((sv::lhrange x) x)
       ((svtv-sva-cfg c) cfg))
    (case (sv::lhatom-kind x.atom)
      (:z (str::cat "{{" (str::natstr x.w) "}1'bz}"))
      (:var (b* (((sv::lhatom-var a) x.atom)
                 (name (svar-name-to-ver-str (sv::svar->name a.name))))
              (str::cat name
                        (if (and (eql a.rsh 0) (eql x.w 1)
                                 (eql (cdr (assoc-equal name c.sizes)) 1))
                            ""
                          (str::cat "[" (str::natstr a.rsh) "+:"
                                    (str::natstr x.w) "]")))))
      (t (prog2$ (raise "illegal lhrange:~x0" x)
                 "")))))

(define lhs-conc-str ((x sv::lhs-p)
                      (cfg svtv-sva-cfg-p))
  :returns (r stringp)
  (cond ((endp x) "")
        ((endp (rest x)) (lhrange-ver-str (first x) cfg))
        (t (str::cat (lhrange-ver-str (first x) cfg)
                     ","
                     (lhs-conc-str (rest x) cfg)))))

(define lhs-verilog-str ((x sv::lhs-p)
                         (cfg svtv-sva-cfg-p))
  :returns (r stringp)
  (cond ((endp x) "")
        ((endp (rest x)) (lhrange-ver-str (first x) cfg))
        (t (str::cat "{" (lhs-conc-str x cfg) "}"))))

;;;;

(define sig-is-high1 ((x sv::svtv-line-p) (i natp)
                      (sig stringp) (cfg svtv-sva-cfg-p))
  (b* (((sv::svtv-line x) x)
       (e (nth i x.entries))
       (var (lhs-verilog-str x.lhs cfg)))
    (and (str::substrp sig var) (eql e 1))))

(define sig-is-high ((x sv::svtv-lines-p) (i natp)
                     (sig stringp) (cfg svtv-sva-cfg-p))
  (and (consp x)
       (or (sig-is-high1 (first x) i sig cfg)
           (sig-is-high (rest x) i sig cfg))))

(define clk-is-high ((x sv::svtv-lines-p) (i natp)
                     (cfg svtv-sva-cfg-p))
  (sig-is-high x i (svtv-sva-cfg->clk cfg) cfg))

(define rst-is-high ((x sv::svtv-lines-p) (i natp)
                     (cfg svtv-sva-cfg-p))
  (sig-is-high x i (svtv-sva-cfg->rst cfg) cfg))

;;;;

(define mk-sva-assume-base ((x sv::svtv-line-p) (i natp)
                            (env sv::svex-env-p)
                            (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (b* (((sv::svtv-line x) x)
       ((svtv-sva-cfg c) cfg)
       (e (nth i x.entries))
       (w (lhs-total-width x.lhs))
       (var (lhs-verilog-str x.lhs cfg)))
    (and e
         (not (sv::svtv-dontcare-p e))
         (not (and (symbolp e) (member-eq e c.out-vars)))
         (not (and (consp e) (symbolp (car e)) (member-eq (car e) c.out-vars)))
         (b* ((o (and (consp e) (consp (cdr e)) (cadr e)))
              (o (get-to-4vec o env))
              (v (if (consp e) (car e) e))
              (v (get-to-4vec v env)))
           (cond ((and o v)
                  (b* ((o (4vec-to-verilog o w))
                       (v (4vec-to-verilog v w)))
                    (list (str::cat "((" var "&" o ") == (" v "&" o "))"))))
                 (v
                  (b* ((v (4vec-to-verilog v w)))
                    (list (str::cat "(" var " == " v ")")))))))))

(define mk-sva-assume-step-base ((x sv::svtv-lines-p) (i natp)
                                 (env sv::svex-env-p)
                                 (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (if (endp x) ()
    (append (mk-sva-assume-base (first x) i env cfg)
            (mk-sva-assume-step-base (rest x) i env cfg))))

(define mk-sva-assumes-base ((x sv::svtv-lines-p)
                             (n natp)
                             (env sv::svex-env-p)
                             (cfg svtv-sva-cfg-p)
                             &key ((i natp) '0))
  :returns (r string-list-list-p)
  (if (zp n) ()
    (append (and
             ;; jasper should run the reset stages as well
             ;;(not (rst-is-high x i cfg))
             (or (not (svtv-sva-cfg->double-clock cfg))
                 (clk-is-high x i cfg))
             (b* ((e (mk-sva-assume-step-base x i env cfg)))
               ;; (and e (list e))
               (list e)))
            (mk-sva-assumes-base x (1- n) env cfg :i (1+ i)))))

;;;;

(define mk-sva-assume-xmrs ((x true-listp) (i natp)
                            (env sv::svex-env-p)
                            (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (b* (((svtv-sva-cfg c) cfg)
       (e (nth i (rest x)))
       (var (first x))
       ((unless (sv::svtv-entry-p e))
        (raise "should be entry:~x0" e))
       ((unless (stringp var))
        (raise "should be string:~x0" var))
       (look (assoc-equal var c.sizes))
       ((unless look)
        (raise "should have found var in sizes:~x0" var))
       (w (cdr look))
       ((unless (posp w))
        (raise "internal error: should be positive:~x0" (list var w)))
       (var (if (member-equal var c.needs-xmr)
                (print-concat-mod (parse-concats var) c.target-mod)
              var)))
    (and e
         (not (sv::svtv-dontcare-p e))
         (not (and (symbolp e) (member-eq e c.out-vars)))
         (not (and (consp e) (symbolp (car e)) (member-eq (car e) c.out-vars)))
         (b* ((o (and (consp e) (consp (cdr e)) (cadr e)))
              (o (get-to-4vec o env))
              (v (if (consp e) (car e) e))
              (v (get-to-4vec v env)))
           (cond ((and o v)
                  (b* ((o (4vec-to-verilog o w))
                       (v (4vec-to-verilog v w)))
                    (list (str::cat "((" var "&" o ") == (" v "&" o "))"))))
                 (v
                  (b* ((v (4vec-to-verilog v w)))
                    (list (str::cat "(" var " == " v ")")))))))))

(define mk-sva-assume-step-xmrs ((x true-list-listp) (i natp)
                                 (env sv::svex-env-p)
                                 (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (if (endp x) ()
    (append (mk-sva-assume-xmrs (first x) i env cfg)
            (mk-sva-assume-step-xmrs (rest x) i env cfg))))

(define sig-is-high1-xmr ((x true-listp) (i natp)
                          (sig stringp) (cfg svtv-sva-cfg-p))
  (declare (ignore cfg))
  (b* ((e (nth i (cdr x)))
       (var (car x)))
    (and (stringp var) (str::substrp sig var) (eql e 1))))

(define sig-is-high-xmr ((x true-list-listp) (i natp)
                         (sig stringp) (cfg svtv-sva-cfg-p))
  (and (consp x)
       (or (sig-is-high1-xmr (first x) i sig cfg)
           (sig-is-high-xmr (rest x) i sig cfg))))

(define clk-is-high-xmr ((x true-list-listp) (i natp)
                         (cfg svtv-sva-cfg-p))
  (sig-is-high-xmr x i (svtv-sva-cfg->clk cfg) cfg))

(define rst-is-high-xmr ((x true-list-listp) (i natp)
                         (cfg svtv-sva-cfg-p))
  (sig-is-high-xmr x i (svtv-sva-cfg->rst cfg) cfg))

(define mk-sva-assumes-xmrs ((x true-list-listp)
                             (n natp)
                             (env sv::svex-env-p)
                             (cfg svtv-sva-cfg-p)
                             &key ((i natp) '0))
  :returns (r string-list-list-p)
  (if (zp n) ()
    (append (and
             ;; [VR]: jasper should run the reset stages as well
             ;; (not (rst-is-high-xmr x i cfg))
             (or (not (svtv-sva-cfg->double-clock cfg))
                 (clk-is-high-xmr x i cfg))
             (b* ((e (mk-sva-assume-step-xmrs x i env cfg)))
               (list e)
               ;; (and e (list e))
               ))
            (mk-sva-assumes-xmrs x (1- n) env cfg :i (1+ i)))))

;;;;

(define mk-sva-assumes ((org true-list-listp)
                        (exp sv::svtv-lines-p)
                        (n natp)
                        (env sv::svex-env-p)
                        (cfg svtv-sva-cfg-p))
  :returns (r string-list-list-p)
  (if (svtv-sva-cfg->abuse-xmrs cfg)
      (mk-sva-assumes-xmrs org n env cfg)
    (mk-sva-assumes-base exp n env cfg)))

;;;;

(fty::defalist sva-past-bind
  :key-type symbolp
  :val-type stringp
  :true-listp t)

(define mk-sva-past-bind-1 ((x true-listp) (i natp) (n natp)
                            (cfg svtv-sva-cfg-p))
  :returns (r sva-past-bind-p)
  (b* ((sig (first x))
       ((unless (stringp sig))
        (raise "Should have been string:~x0" x))
       ((svtv-sva-cfg c) cfg)
       (sig (if (and c.abuse-xmrs
                     (member-equal sig c.needs-xmr))
                (str::cat c.target-mod "." sig)
              sig))
       (var (nth i (rest x)))
       (var (if (consp var) (cdr var) var))
       ((unless (and (symbolp var)
                     (not (booleanp var))
                     (not (keywordp var))
                     (not (sv::svtv-dontcare-p var))))
        ()))
    (list (cons var
                (if (zp n) sig
                  (str::cat "\$past(" sig ","
                            (str::natstr n)
                            ")")))
          )))

(define mk-sva-past-bind-time ((x true-list-listp) (i natp) (n natp)
                               (cfg svtv-sva-cfg-p))
  :returns (r sva-past-bind-p)
  (if (endp x) ()
    (append (mk-sva-past-bind-1 (first x) i n cfg)
            (mk-sva-past-bind-time (rest x) i n cfg))))

(define mk-sva-past-bind ((x true-list-listp)
                          (n natp)
                          (cfg svtv-sva-cfg-p)
                          &key ((i natp) '0))
  :returns (r sva-past-bind-p)
  (if (zp n) ()
    (append (mk-sva-past-bind-time x i (1- n) cfg)
            (mk-sva-past-bind x (1- n) cfg :i (1+ i)))))

(local (defthm integer-is-4vec
         (implies (integerp x)
                  (sv::4vec-p x))
         :hints (("Goal" :in-theory (enable sv::4vec-p)))))

(define mk-sva-conc-and-1 ((var symbolp)
                           (past stringp)
                           (env sv::svex-env-p)
                           (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (b* (((svtv-sva-cfg c) cfg)
       (val (cdr (assoc-eq var env)))
       ((unless val) ()) ;; nothing to ensure..
       (size (cdr (assoc-eq var c.out-sizes)))
       ((unless size)
        (raise "Could not find size:~x0" (list var c.out-sizes)))
       (up (sv::4vec->upper val))
       (lo (sv::4vec->lower val)))
    (if (equal up lo)
        (list (str::cat "(" past " == " (4vec-to-verilog val size) ")"))
      (b* ((msk (logeqv up lo))
           (val (logand up lo)))
        (list (str::cat "((" past " & " (4vec-to-verilog msk size) ") == " (4vec-to-verilog val size) ")"))))))

(define mk-sva-conc-and ((x sva-past-bind-p)
                         (env sv::svex-env-p)
                         (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  :verify-guards :after-returns
  (if (endp x) ()
    (b* ((rst (mk-sva-conc-and (cdr x) env cfg))
         (fst (mk-sva-conc-and-1 (caar x) (cdar x) env cfg)))
      (append fst rst))))

(define mk-sva-concludes ((x true-list-listp)
                          (n natp)
                          (env sv::svex-env-p)
                          (cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (mk-sva-conc-and (mk-sva-past-bind x n cfg) env cfg))

;;;;


(define sva-mask-sizes ((x sv::svar-boolmasks-p))
  :returns (r svtv-out-sizes-p)
  (if (atom x) ()
    (b* ((var (caar x))
         ((unless (symbolp var))
          (raise "outexprs alist should bind symbols:~x0" var))
         (size (integer-length (cdar x)))
         ;; BOZO -- should this ever be 0? should we throw an error!
         (size (if (eql size 0) 1 size)))
      (cons (cons var size)
            (sva-mask-sizes (cdr x))))))

(define sva-remove-size (name (x svtv-sva-sizes-p))
  :returns (r svtv-sva-sizes-p :hyp :guard)
  (cond ((endp x) ())
        ((equal name (caar x)) (cdr x))
        (t (cons (car x) (sva-remove-size name (cdr x))))))

(define sva-merge-sizes ((x svtv-sva-sizes-p)
                         (y svtv-sva-sizes-p))
  :returns (r svtv-sva-sizes-p :hyp :guard)
  (if (endp x) (svtv-sva-sizes-fix y)
    (sva-merge-sizes (rest x)
                     (b* ((name (caar x))
                          (size (cdar x))
                          (look (assoc-equal name y)))
                       (cond
                        ((not look)
                         (cons (car x) y))
                        ((> size (cdr look))
                         (cons (car x) (sva-remove-size name y)))
                        (t y))))))

(define lhrange-in-sizes ((x sv::lhrange-p))
  :returns (r svtv-sva-sizes-p)
  (b* (((sv::lhrange x) x))
    (case (sv::lhatom-kind x.atom)
      (:z ())
      (:var (b* (((sv::lhatom-var a) x.atom)
                 (name (svar-name-to-ver-str (sv::svar->name a.name))))
              (list (cons name (+ a.rsh x.w))))))))

(define lhs-in-sizes ((x sv::lhs-p))
  :returns (r svtv-sva-sizes-p)
  :verify-guards :after-returns
  (if (endp x) ()
    (sva-merge-sizes (lhrange-in-sizes (first x))
                     (lhs-in-sizes (rest x)))))

(define sva-in-sizes ((x sv::svtv-lines-p))
  :returns (r svtv-sva-sizes-p)
  :verify-guards :after-returns
  (if (endp x) ()
    (sva-merge-sizes (lhs-in-sizes (sv::svtv-line->lhs (first x)))
                     (sva-in-sizes (rest x)))))

(define lhs-total-size ((x sv::lhs-p))
  :returns (r natp)
  :verify-guards :after-returns
  (if (endp x) 0
    (+ (lnfix (sv::lhrange->w (first x)))
       (lhs-total-size (rest x)))))

(define sva-corr-sizes ((x true-list-listp)
                        (y sv::svtv-lines-p))
  :returns (r svtv-sva-sizes-p)
  :verify-guards :after-returns
  (cond ((and (endp x) (endp y)) ())
        ((or (endp x) (endp y))
         (raise "Should have been same length:~x0"
                (list x y)))
        (t
         (b* ((name (caar x))
              ((unless (stringp name))
               (raise "Should have been a string:~x0" x))
              (size (lhs-total-size (sv::svtv-line->lhs (first y))))
              ((unless (posp size))
               (raise "Should have been a positive size:~x0" y)))
           (cons (cons name size)
                 (sva-corr-sizes (rest x) (rest y)))))))

(define sva-find-out-str ((x true-list-listp)
                          (var symbolp))
  :returns (r stringp)
  (cond
   ((endp x)
    (prog2$ (raise "Could not find out var:~x0" var) ""))
   ((member-eq var (cdar x))
    (b* ((s (caar x)))
      (if (stringp s) s
        (prog2$ (raise "Variable is not a string:~x0" x) ""))))
   (t (sva-find-out-str (cdr x) var))))

(define sva-out-sizes ((x true-list-listp)
                       (os svtv-out-sizes-p))
  :returns (r svtv-sva-sizes-p :hyp :guard)
  :verify-guards :after-returns
  (if (endp os) ()
    (b* ((name (sva-find-out-str x (caar os))))
      (if (or (str::substrp "[" name)
              (str::substrp "." name)) ;; BOZO -- structured names are skipped but need to handle them
          (sva-out-sizes x (cdr os))
        (sva-merge-sizes (list (cons name (cdar os)))
                         (sva-out-sizes x (cdr os)))))))

(define lhrange-needs-xmr ((x sv::lhrange-p))
  (b* (((sv::lhrange x) x))
    (case (sv::lhatom-kind x.atom)
       (:z nil)
       (:var (b* (((sv::lhatom-var a) x.atom))
               (atom (sv::svar->name a.name)))))))

(define lhs-needs-xmr ((x sv::lhs-p))
  (and (consp x)
       (or (lhrange-needs-xmr (first x))
           (lhs-needs-xmr (rest x)))))

(define sva-in-need-xmrs ((org true-list-listp)
                          (exp sv::svtv-lines-p))
  :returns (r string-listp)
  :measure (len org)
  (cond ((endp org) ())
        ((endp exp) (raise "both lists should be same length;~x0" (list org exp)))
        ((lhs-needs-xmr (sv::svtv-line->lhs (first exp)))
         (b* ((name (caar org))
              ((unless (stringp name))
               (raise "list should have started with string:~x0" org)))
           (cons name (sva-in-need-xmrs (rest org) (rest exp)))))
        (t (sva-in-need-xmrs (rest org) (rest exp)))))

(define sva-out-need-xmrs ((org true-list-listp))
  :returns (r string-listp)
  ;; we just go ahead and mark all of the outputs as needing xmr:
  (if (endp org) ()
    (b* ((name (caar org))
         ((unless (stringp name))
          (raise "list should have started with string:~x0" org)))
      (cons name (sva-out-need-xmrs (rest org))))))

(local (defthm true-list-listp-of-append
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (append x y)))))

(define svtv-fill-in-cfg ((run symbolp)
                          (svtv sv::svtv-p)
                          (repo stringp)
                          (cfg svtv-sva-cfg-p))
  :returns (r svtv-sva-cfg-p :hyp :guard)
  (b* (((sv::svtv s) svtv)
       ((svtv-sva-cfg c) cfg)
       (out-sizes (sva-mask-sizes s.outmasks))
       (sizes (sva-merge-sizes (if c.abuse-xmrs
                                   (sva-corr-sizes (append s.orig-ins s.orig-overrides)
                                                   (append s.expanded-ins s.expanded-overrides))
                                 (sva-in-sizes  (append s.expanded-ins s.expanded-overrides)))
                               (sva-out-sizes (append s.orig-outs s.orig-internals) out-sizes)))
       (needs-xmr (append (sva-in-need-xmrs s.orig-ins s.expanded-ins)
                          (sva-in-need-xmrs s.orig-overrides s.expanded-overrides)
                          (sva-out-need-xmrs s.orig-outs)
                          (sva-out-need-xmrs s.orig-internals)))
       ;; (- (cw "needs-xmr:~x0~%" needs-xmr))
       (cfg (change-svtv-sva-cfg cfg
                                 :abuse-xmrs t
                                 :repo-path repo)))
    (change-svtv-sva-cfg cfg
                         :run-name run
                         :clk (sva-run-clk run)
                         :rst (sva-run-rst run)
                         :out-file (sva-run-sv-file run cfg)
                         :tmp-dir (sva-tmp-sv-dir cfg)
                         :target-mod (sva-run-top-module-name run)
                         :cp-cmd (sva-run-cp-cmd run cfg)
                         :make-cmd (sva-run-make-cmd run)
                         :needs-xmr needs-xmr
                         :sizes sizes
                         :out-sizes out-sizes)))

;;;;

(define sva-refs-env ((x true-list-listp)
                      (out-vars symbol-listp)
                      (i natp)
                      (env sv::svex-env-p))
  (and (consp x)
       (or (b* ((var-pair (assoc-equal (nth i (cdar x)) env)))
             (and var-pair
                  ;; if output variables specified, only generate nphases
                  ;; needed for output.
                  (or (null out-vars)
                      (member-eq (car var-pair) out-vars))))
           (sva-refs-env (cdr x) out-vars i env))))

(define sva-prune-nphases ((x true-list-listp)
                           ;; the output variables
                           (out-vars symbol-listp)
                           (n natp)
                           (env sv::svex-env-p)
                           &key
                           ((i natp) '0)
                           ((r natp) '0))
  :returns (r natp)
  (if (zp n) (lnfix (1+ r))
    (sva-prune-nphases x out-vars
                       (1- n) env :i (1+ i)
                       :r (if (sva-refs-env x out-vars i env) i r))))

;;;;

(include-book "kestrel/file-io-light/write-strings-to-file-bang" :dir :system)

(define add-newlines ((x string-listp))
  :returns (r string-listp)
  (if (endp x) ()
    (cons (str::cat (first x) (coerce (list #\Newline) 'string))
          (add-newlines (rest x)))))

(define write-out-strs ((file stringp) (x string-listp) state)
  (b* ((x (add-newlines x))
       ((mv errp state)
        (acl2::write-strings-to-file! x file 'write-out-strs state))
       ((when errp)
        (raise "Encountered error in writing output file:~x0" file)
        state))
    state))

(define sva-finish-assumes ((x string-list-list-p))
  :returns (r string-listp)
  (if (endp x) ()
    (append (list "(")
            (indent (if (endp (first x)) (list "1'b1") (add-conjuncts (first x))))
            (list ")")
            (and (consp (rest x))
                 (list "##1"))
            (sva-finish-assumes (rest x)))))

(define sva-finish-concludes ((x string-listp))
  :returns (r string-listp)
  (append (list "(")
          (add-conjuncts x)
          (list ")")))

(define svtv-to-sva-prop ((name stringp         "name of the property to generate")
                          (env  sv::svex-env-p  "alist of vars to 4vecs either as assumes (ins) or concludes (outs)")
                          (svtv sv::svtv-p      "svtv on which we are doing the check/proof")
                          (cfg  svtv-sva-cfg-p   "config object holding additional generation fields"))
  :parents (|Generating SVAs from SVTVs|)
  :short "Generate a string defining an SVA for reproducing an env. relative to a given svtv"
  :returns (r string-listp)
  (b* (((sv::svtv s) svtv)
       ((svtv-sva-cfg c) cfg)
       (- "1. Determine number of phases to include from SVTV (prune to outputs being checked):")
       (nphases   (if (svtv-sva-cfg->disable-prune cfg) s.nphases
                    (sva-prune-nphases (append s.orig-outs s.orig-internals)
                                       c.out-vars
                                       s.nphases env)))
       (- "2. Compute the assumptions in the generated property from ins and overrides:")
       (assumes   (mk-sva-assumes   (append s.orig-ins s.orig-overrides)
                                    (append s.expanded-ins s.expanded-overrides)
                                    nphases env cfg))
       (- "3. Compute the conclusions in the generated property from the outputs:")
       (concludes (mk-sva-concludes (append s.orig-outs s.orig-internals)
                                    nphases env cfg))
       (- "4. Allow some svtv or run specific modifications of the assumptions and conclusions:")
       (assumes   (sva-run-modify-assumes   assumes   c.run-name))
       (concludes (sva-run-modify-concludes concludes c.run-name))
       (- "5. Final conversion of assumptions and conclusions into conjunctions for SVA definition:")
       (assumes   (sva-finish-assumes assumes))
       (concludes (sva-finish-concludes concludes))
       (- "6. Now glue together the assumptions and conclusions to make the property:"))
    (append (list (str::cat name ":"
                            " assert property ( @(posedge " c.clk
                            ")" ;; "disable iff (" c.rst ")"
                            ))
            (indent (append (list "(")
                            (indent assumes)
                            (list (str::cat ") |-> "
                                            (if c.negate-conclude "!" "")
                                            " ("))
                            (indent concludes)
                            (list ")")))
            (list ");"))))

(define svtv-to-sva-params ((sizes svtv-sva-sizes-p "variable and size specifications"))
  :returns (r string-listp)
  (cond
   ((endp sizes) ())
   ((str::substrp "." (caar sizes))
    ;; skip anything that is a field of a struct or XMRef:
    (svtv-to-sva-params (cdr sizes)))
   (t
    (cons (str::cat "input logic "
                    (if (> (cdar sizes) 1)
                        (str::cat "[" (str::natstr (1- (cdar sizes))) ":0]")
                      "")
                    " "
                    (caar sizes)
                    (if (endp (cdr sizes)) "" ","))
          (svtv-to-sva-params (cdr sizes))))))

(define svtv-to-sva-mod ((cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (b* (((svtv-sva-cfg c) cfg))
    (append (list (str::cat "module " c.prop-mod " ("))
            (indent (cons (str::cat "input logic " c.clk ",")
                          (if c.abuse-xmrs
                              (list (str::cat "input logic " c.rst))
                            (svtv-to-sva-params c.sizes))))
            (list ");"))))

(define svtv-to-sva-bind ((cfg svtv-sva-cfg-p))
  :returns (r string-listp)
  (b* (((svtv-sva-cfg c) cfg)
       (inst-name (str::cat c.prop-mod "_inst")))
    (list (str::cat "bind " c.target-mod " " c.prop-mod " " inst-name "(.*);"))))

(define sva-start-after-endmod ((x string-listp))
  :returns (r string-listp :hyp :guard)
  (cond ((endp x) ())
        ((str::substrp "endmodule" (first x))
         (rest x))
        (t (sva-start-after-endmod (rest x))))
  ///
  (defthm len-of-sva-start-after-endmod
    (<= (len (sva-start-after-endmod x))
        (len x))
    :rule-classes (:rewrite :linear)))

(define sva-std-verilog-toks ((x stringp))
  :returns (r string-listp)
  (str::strtok x (list #\Space #\( #\Tab #\; #\. #\*)))

(define sva-remove-mod-lines ((x string-listp) (mod stringp))
  :returns (r string-listp :hyp :guard)
  :measure (len x)
  (cond ((endp x) ())
        ((and (str::substrp "module" (first x))
              (b* ((toks (sva-std-verilog-toks (first x))))
                (and (member-equal "module" toks)
                     (member-equal mod toks))))
         (sva-remove-mod-lines (sva-start-after-endmod (rest x)) mod))
        ((and (str::substrp "bind" (first x))
              (b* ((toks (sva-std-verilog-toks (first x))))
                (and (member-equal "bind" toks)
                     (member-equal mod toks))))
         (sva-remove-mod-lines (rest x) mod))
        (t (cons (first x)
                 (sva-remove-mod-lines (rest x) mod)))))

(include-book "std/strings/strtok-bang" :dir :system)

(define svtv-to-sva-fn ((run  symbolp        "fn name of a supported svtv")
                        (repo stringp        "path to the top of the FV repo")
                        (prop stringp        "base name of property module containing property")
                        (env  sv::svex-env-p "environment we want to generate the check for against the svtv")
                        (out-vars symbol-listp "variables which should be treated as outputs if they are overrides")
                        (filename-suffix stringp "suffix for the sva_generated file")
                        (svtv sv::svtv-p     "svtv used to generate the property along with env")
                        &key
                        (state 'state))
  :parents (|Generating SVAs from SVTVs|)
  :short "Generate a verilog file with a module and SVAs for showing svtv/envs in Jasper"
  (b* (((unless (legal-verilog-name-p prop))
        (prog2$ (raise "Property name should be legal verilog name:~x0" prop)
                state))
       (cfg (make-svtv-sva-cfg))
       (prop-mod (str::cat prop "_mod"))
       (cfg (change-svtv-sva-cfg cfg
                                 :prop-mod prop-mod
                                 :out-vars out-vars
                                 :filename-suffix filename-suffix))
       ((svtv-sva-cfg c) (svtv-fill-in-cfg run svtv repo cfg))
       (new-lines  (append (list "")
                           (svtv-to-sva-mod c)
                           (list "")
                           (svtv-to-sva-prop prop env svtv c)
                           (list "")
                           (list "endmodule")
                           (list "")
                           (svtv-to-sva-bind c)
                           (list "")))
       (read-text  (acl2::read-file-into-string c.out-file))
       (read-text  (if (stringp read-text) read-text ""))
       (read-lines (str::strtok! read-text (list #\Newline)))
       (read-lines (sva-remove-mod-lines read-lines prop-mod))
       (out-lines  (append new-lines read-lines))
       (- (cw "[[[ ]]]~%"))
       (- (cw "~S0~%" (str::cat "[[[ BEGIN Jasper SVA notes for " prop " ]]]")))
       (- (cw "[[[ ]]]~%"))
       (- (cw "~S0~%" " Please see XDOC topic Generating SVAs from SVTVs for
                        full details about setup and use."))
       (- (cw "~S0~%" " Following are specific commands to run after setup to bring up Jasper with target SVA:"))
       (- (cw "  1. ~S0~%" c.cp-cmd))
       (- (cw "  2. ~S0~%" c.make-cmd))
       (- (cw "[[[ ]]]~%"))
       (- (cw "~S0~%" "To save this counterexample to your debug directory
                        automatically, run the following command:"))
       (- (cw "~S0~%" "save-sva"))
       (- (cw "[[[ ]]]~%"))
       (- (cw "~S0~%" (str::cat "[[[ END Jasper SVA notes for " prop " ]]]")))
       (- (cw "[[[ ]]]~%"))
       (state (write-out-strs c.out-file out-lines state))

       (tmp-sv-file (str::cat c.tmp-dir "sva_generated.sv"))
       (state (write-out-strs tmp-sv-file new-lines state))

       (tmp-conf-file (str::cat c.tmp-dir "config"))
       (conf (list c.out-file))
       (state (write-out-strs tmp-conf-file conf state)))
    state))

;;;;;;;;;;

(define sva-get-fgl-ctrex (&key (fgl::interp-st 'fgl::interp-st))
  ;;:returns (r sv::svex-env-p)
  (b* ((debug-info (fgl::interp-st->debug-info fgl::interp-st)))
    (and (consp debug-info)
         (equal (car debug-info) "Counterexample.")
         ;;(sv::svex-env-p (cdr  debug-info)) ;; if  there is a  free variable,
         ;;which may  be assigned  to nil  in the env,  then this  check causes
         ;;everything to  be dropped. A better  way is to rebuild  the env only
         ;;for integer values:
         (loop$ for x in (true-list-fix (cdr debug-info))
                when (and (consp x) (integerp (cdr x)))
                collect x)
         ;;(cdr debug-info)
         )))

(define svtv-sva-trans-eval-env1 (env
                                  ctrex-env
                                  &key
                                  (state 'state))
  :mode :program
  (b* (((when (sv::svex-env-p env))
        env)
       ((mv erp trm)
        (acl2::translate-cmp env ;; env: term to translate
                             t   ;; stobjs-out: is t for logical translation
                             t   ;; logic-modep: fail if program-mode fn.
                             nil ;; known-stobjs: do not use any stobjs
                             'svtv-sva-trans-eval-env ;; ctx
                             (w state) ;; w: world
                             (acl2::default-state-vars t))) ;; state-vars: get from state
       ((when erp)
        (raise "Error occured during translation:~x0 for term:~x1 with result:~x2"
               erp env trm))
       ((unless (acl2::pseudo-termp trm))
        (raise "Translation did not produce a pseudo-term:~x0 from ~x1"
               trm env))
       ;; now evaluate using magic-ev:
       ((mv erp val)
        (acl2::magic-ev trm        ;; trm to evaluate
                        ctrex-env  ;; alist binding variables to values
                        state      ;; acl2 state
                        nil        ;; hard-error-returns-nilp
                        nil))      ;; aokp
       ((when erp)
        (raise "Error occured during evaluation:~x0 for term:~x1 for env:~p2 with error message:~%~@3"
               erp trm ctrex-env val))
       ((unless (sv::svex-env-p val))
        (raise "Evaluation did not produce and svex-env-p as expected for term:~x0 with result:~x1 and alist:~x2"
               trm val ctrex-env)))
    val))

(define svtv-sva-trans-eval-env (output-var-bindings
                                 input-var-bindings
                                 ctrex-var-bindings
                                 ignore-fgl
                                 &key
                                 (fgl::interp-st 'fgl::interp-st)
                                 (state 'state))
  :mode :program
  (b* ((alst (acl2::project-dir-alist (w state)))
       ((unless (alistp alst))
        (mv (raise "project-dir-alist should be alist:~x0" alst) () ()))
       (repo-path (cdr (assoc-eq :FV alst)))
       ((unless (stringp repo-path))
        (mv (raise "project-dir-alist FV entry should be string:~x0" alst) () ()))
       (ctrex-env (and (not ignore-fgl)
                       (sva-get-fgl-ctrex)))
       (ctrex-eval (svtv-sva-trans-eval-env1 ctrex-var-bindings ctrex-env))
       (full-ctrex-env (append ctrex-eval ctrex-env))
       (input-eval (svtv-sva-trans-eval-env1 input-var-bindings full-ctrex-env))
       (full-input-env (append input-eval full-ctrex-env))
       (output-eval (svtv-sva-trans-eval-env1 output-var-bindings full-input-env)))
    (mv repo-path (append output-eval full-input-env) (strip-cars output-eval))))

(include-book "std/util/defmacro-plus" :dir :system)

(acl2::defmacro+ svtv-to-sva (prop svtv output-var-bindings
                                   &key
                                   input-var-bindings
                                   ctrex-var-bindings
                                   ignore-fgl
                                   (filename-suffix '""))
  :short "macro which takes an svtv and environment and generates an sva assertion to check"
  :parents (|Generating SVAs from SVTVs|)
  :long " <p>Dump an SVA intended to replicate some particular run of an SVTV,
asserting that if (some or all) signals corresponding to SVTV inputs have some
specified values, then (some or all) signals corresponding to SVTV outputs will
have specified values.</p>

<p>Unless the @(':ignore-fgl') keyword is true, the latest FGL counterexample
is fetched from the FGL interpreter state and used to provide input assumptions
for the SVTV.  Alternatively or in addition, the @('input-var-bindings')
keyword argument may be used to provide such bindings if the @(':ignore-fgl')
option is used, or additional bindings besides the ones from the FGL
counterexample otherwise.  Bindings from FGL may also be used in the
computation of these bindings, if not ignored.</p>

<p>The third argument, @('output-var-bindings'), should be provided in order to
give expected values for output variables.  This may be a quoted svex-env
object or a term that evaluates to one under the FGL counterexample's variable
bindings.  For example, if you expect input variables @('a'), @('b'), @('c') to
be bound in the FGL counterexample, this argument could look like:
@({
  (list (cons 'my-output (my-spec-fn a b c)))
 })
or equivalently
@({
 `((my-output . ,(my-spec-fn a b c)))
 })
</p>

<p>A keyword argument @(':input-var-bindings') may be provided to either
provide inputs when the FGL counterexample is ignored or to provide additional
inputs not included in the FGL counterexample.  E.g., if an SVTV variable
@('opcode') is bound to a concrete value in the environment of the conjecture
rather than a variable, then the variable @('opcode') won't appear in the FGL
counterexample; it should then be bound in the input-var-bindings.
Additionally, if the value provided for an SVTV variable is computed from some
theorem variables but does not correspond to one exactly, they should also be
bound here.  This may also be a term or a quoted svex-env object.</p>

<p>Another keyword argument @(':filename-suffix'), if provided, should be a
string that will determine where the SVA is written, i.e., in a file named
@('sva_generated<suffix>.sv').</p>

<h3>Common Use Cases</h3>

<h4>Counterexample directly from FGL.</h4>
<p>If we want to record a counterexample from FGL where the free variables of
the theorem correspond exactly to the SVTV input variables needed, then only
the output-var-bindings need to be provided, computing the desired result from
the specification:</p>
@({
 (svtv-to-sva \"my_counterexample\" (my-svtv)
             (b* (((mv res flags)
                   ;; note: the following srca, srcb, mxcsr variables will be extracted
                   ;; from the FGL counterxample
                   (my_op-spec 'packed_sp srca srcb mxcsr)))
               ;; construct an alist mapping the SVTV output signals to be
               ;; checked to their desired values
               `((fp_unit_res . ,res) (fp_unit_flags . ,flags))))
 })

<h4>Counterexample from FGL with SVTV inputs computed from theorem
variables.</h4>
<p>If we want to record a counterexample from FGL, but the free variables of
the theorem are used to compute the inputs to the SVTV rather than
corresponding directly to those inputs, then we need to use the
@(':input-var-bindings') argument as well.  The output-var-bindings argument is
the same as above.</p>
@({
 (svtv-to-sva \"my_counterexample\" (my-svtv)
             (b* (((mv res flags)
                   ;; note: the following srca, srcb, mxcsr variables will be extracted
                   ;; from the FGL counterxample
                   (my_op-spec 'packed_sp srca srcb mxcsr)))
               ;; construct an alist mapping the SVTV output signals to be
               ;; checked to their desired values
               `((fp_unit_res . ,res) (fp_unit_flags . ,flags)))
             :input-var-bindings
             ;; Compute the missing SVTV input variables from the variables of
             ;; the FGL counterexample.
             `((rc . ,(mxcsr->rc mxcsr)) (um . ,(mxcsr->um mxcsr))))
})

<h4>Manually specified counterexample not from FGL.</h4>

<p>If we want to record a counterexample not from FGL, we can use the
@(':ctrex-var-bindings') input to bind the common variables used by the inputs
and outputs.  Keep in mind that even though the output-var-bindings are
specified first, they use variables computed in the ctrex-var-bindings and
input-var-bindings.</p>
@({
 (svtv-to-sva \"my_counterexample\" (my-svtv)
             (b* (((mv res flags)
                   ;; note: the following srca, srcb, mxcsr variables will be extracted
                   ;; from the :input-var-bindings
                   (my_op-spec 'packed_sp srca srcb mxcsr)))
               ;; construct an alist mapping the SVTV output signals to be
               ;; checked to their desired values
               `((fp_unit_res . ,res) (fp_unit_flags . ,flags)))
             ;; ignore any counterexample stored by FGL in case there happens to be one
             :ignore-fgl t
             :ctrex-var-bindings '((mxcsr . #x1f80)
                                   (srca . #x3f800000)
                                   (srcb . #xc0800000))
             :input-var-bindings
             ;; Compute the missing SVTV input variables from the variables of
             ;; the FGL counterexample.
             `((rc . ,(mxcsr->rc mxcsr))
               (um . ,(mxcsr->um mxcsr))))
})



"
  (declare (xargs :guard (and (consp svtv)
                              (symbolp (car svtv))
                              (null (cdr svtv))
                              (stringp prop))))
  `(make-event (b* (((mv repo env out-vars)
                     (svtv-sva-trans-eval-env (quote ,output-var-bindings)
                                              (quote ,input-var-bindings)
                                              (quote ,ctrex-var-bindings)
                                              (quote ,ignore-fgl)))
                    (state (svtv-to-sva-fn (quote ,(car svtv))
                                           repo
                                           (quote ,prop)
                                           env
                                           out-vars
                                           ,filename-suffix
                                           ,svtv)))
                 (value '(value-triple t)))))

;;;;;;;;;;

(defsection |Generating SVAs from SVTVs|
  :short "Converting SVTV and an environment to a generated SVA property and Running in Jasper"
  :long "
<h3> SVTV-to-SVA and Running in Jasper </h3>

<p> We cover the utility svtv-to-sva. This utility provides a process for
generating SVA assertions which capture the conditions needed to replicate SVTV
fails in JasperGold for the sake of RTL bug demonstration and checking
fixes. We cover several aspects of the use of this utility along with the
general setup for getting an RTL build checked out (required to run Jasper on
RTL files), and several potential issues that can be encountered in trying to
establish the correlation between SVTVs and SVAs in Jasper.</p>

<p> A few quick notes. SVAs are created from SVTVs coupled with an environment
binding (some or all) of the remaining unbound variables referenced in the
SVTV. The SVTV defines a connection to RTL signals and constants or
variables. The generated SVA consists of assumptions for any RTL bound to
constants in the SVTV and any input or override signals with variables bound in
the environment. As a conclusion of the generated SVA, any SVTV output or
internal signals connected to variables bound in the environment will be
checked as a conclusion of the input and override assumptions. </p>

<p> Note: In order to run svtv-to-sva, include the top file. Then, initialize
the project-specific functions in the file \"svtv-to-sva-runs.lisp\" that are
introduced with the \"define-stub\" macro. These can functions can be
initialized using defattach. </p>

")
