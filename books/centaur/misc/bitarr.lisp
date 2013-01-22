
(in-package "ACL2")

(include-book "arith-equivs")
(include-book "universal-equiv")
(local (include-book "data-structures/list-defthms" :dir :system))

;; Abstract stobj containing an array of bits.  Represented by a list of bits,
;; accessed/updated by nth/update-nth.

(defstobj bitarr$c
  (bits$c :type (array bit (0))
          :initially 0
          :resizable t)
  :inline t)

(def-universal-equiv bits-equiv
  :qvars (i)
  :equiv-terms ((bit-equiv (nth i x))))

(defcong bits-equiv bit-equiv (nth i x) 2
  :hints(("Goal" :in-theory (e/d (bits-equiv-necc)
                                 (bit-equiv)))))

(defcong bits-equiv bits-equiv (update-nth i v x) 3
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defcong bit-equiv bits-equiv (update-nth i v x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))


(defun bitsp (x)
  (declare (xargs :guard t :verify-guards t))
  (if (atom x)
      (equal x nil)
    (and (bitp (car x))
         (bitsp (cdr x)))))

(defthm bits$cp-is-bitsp
  (equal (bits$cp x) (bitsp x)))

(defthm bitp-nth-of-bitsp
  (implies (and (bitsp x)
                (< (nfix n) (len x)))
           (bitp (nth n x))))

(defthm bitsp-of-update-nth
  (implies (and (bitsp x)
                (bitp v)
                (<= (nfix n) (len x)))
           (bitsp (update-nth n v x))))

(defthm bitsp-of-resize-list
  (implies (and (bitsp x)
                (bitp default))
           (bitsp (resize-list x n default))))

(defun bitarr$ap (bitarr$a)
  (declare (xargs :guard t))
  (bitsp bitarr$a))
(defun create-bitarr$a ()
  (declare (xargs :guard t))
  nil)
(defun bits$a-length (bitarr$a)
  (declare (xargs :guard (bitarr$ap bitarr$a)
                  :verify-guards t))
  (len bitarr$a))
(defun resize-bits$a (i bitarr$a)
  (declare (xargs :guard (bitarr$ap bitarr$a)))
  (resize-list bitarr$a i 0))

(defun bits$ai (i bitarr$a)
  (declare (xargs :guard (and (bitarr$ap bitarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (bits$a-length bitarr$a)))
                  :verify-guards t))
  (bfix (nth i bitarr$a)))

(defun update-bits$ai (i v bitarr$a)
  (declare (xargs :guard (and (bitarr$ap bitarr$a)
                              (integerp i)
                              (<= 0 i)
                              (< i (bits$a-length bitarr$a))
                              (bitp v))
                  :verify-guards t))
  (update-nth i (bfix v) bitarr$a))

(defun-nx bitarr$corr (bitarr$c bitarr$a)
  (and (bitarr$cp bitarr$c)
       (equal (len bitarr$a) (len (nth 0 bitarr$c)))
       (bits-equiv bitarr$a (nth 0 bitarr$c))))

(local (in-theory (disable nth (bitarr$corr))))

(DEFTHM CREATE-BITARR{CORRESPONDENCE}
        (BITARR$CORR (CREATE-BITARR$C)
                     (CREATE-BITARR$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-BITARR{PRESERVED}
        (BITARR$AP (CREATE-BITARR$A))
        :RULE-CLASSES NIL)

(DEFTHM GET-BIT{CORRESPONDENCE}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR)
                      (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$A-LENGTH BITARR)))
                 (EQUAL (BITS$CI I BITARR$C)
                        (BITS$AI I BITARR)))
        :hints (("goal" :use ((:instance bits-equiv-necc (x bitarr)
                                     (y (nth 0 bitarr$c))))
                    :in-theory (disable bits-equiv-implies-bit-equiv-nth-2)))
        :RULE-CLASSES NIL)

(DEFTHM GET-BIT{GUARD-THM}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR)
                      (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$A-LENGTH BITARR)))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$C-LENGTH BITARR$C))))
        :RULE-CLASSES NIL)


(DEFTHM SET-BIT{CORRESPONDENCE}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR)
                      (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$A-LENGTH BITARR))
                      (BITP V))
                 (BITARR$CORR (UPDATE-BITS$CI I V BITARR$C)
                              (UPDATE-BITS$AI I V BITARR)))
        :RULE-CLASSES NIL)

(DEFTHM SET-BIT{GUARD-THM}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR)
                      (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$A-LENGTH BITARR))
                      (BITP V))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$C-LENGTH BITARR$C))
                      (OR (EQUAL V 1) (EQUAL V 0))))
        :RULE-CLASSES NIL)

(DEFTHM SET-BIT{PRESERVED}
        (IMPLIES (AND (BITARR$AP BITARR)
                      (INTEGERP I)
                      (<= 0 I)
                      (< I (BITS$A-LENGTH BITARR))
                      (BITP V))
                 (BITARR$AP (UPDATE-BITS$AI I V BITARR)))
        :RULE-CLASSES NIL)

(DEFTHM RESIZE-BITS{CORRESPONDENCE}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR))
                 (BITARR$CORR (RESIZE-BITS$C I BITARR$C)
                              (RESIZE-BITS$A I BITARR)))
        :hints ((and stable-under-simplificationp
                     (let ((concl (car (last clause))))
                       (and (eq (car concl) 'bits-equiv)
                            `(:expand (,concl)
                              :in-theory (enable nth-of-resize-list-split))))))
        :RULE-CLASSES NIL)

(DEFTHM RESIZE-BITS{PRESERVED}
        (IMPLIES (BITARR$AP BITARR)
                 (BITARR$AP (RESIZE-BITS$A I BITARR)))
        :RULE-CLASSES NIL)

(DEFTHM BITS-LENGTH{CORRESPONDENCE}
        (IMPLIES (AND (BITARR$CORR BITARR$C BITARR)
                      (BITARR$AP BITARR))
                 (EQUAL (BITS$C-LENGTH BITARR$C)
                        (BITS$A-LENGTH BITARR)))
        :RULE-CLASSES NIL)



(defabsstobj bitarr
  :exports ((bits-length :exec bits$c-length :logic bits$a-length)
            (get-bit :exec bits$ci :logic bits$ai)
            (set-bit :exec update-bits$ci :logic update-bits$ai)
            resize-bits))


;; Disable this because get-bit's logical definition BFIXes anyway; this tends
;; to get rid of the bfix which makes it harder to know (e.g. by type prescrip)
;; that the NTH is e.g. an integer.
(in-theory (disable bitp-nth-of-bitsp))
