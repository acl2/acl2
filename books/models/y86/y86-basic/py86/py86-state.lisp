(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

;;; From x86-state.lisp

; Increase memory for X86 memory.
(include-book "centaur/misc/memory-mgmt-logic" :dir :system)
(value-triple (set-max-mem (* 6 (expt 2 30))))

; Here we include the GL book to help verify various arithmetic facts.
(local (include-book "centaur/gl/gl" :dir :system))

(defun gl-int (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (gl-int (+ by start) by (1- count)))))

;;; From y86.lisp

(include-book "../common/misc-events")
(include-book "../common/operations")
(include-book "../common/constants")

;;;

(defun lookup (i lst default)
  (declare (xargs :guard (and (eqlablep i)
                              (eqlable-alistp lst))))
  (let ((pair (hons-get i lst)))
    (if pair
        (cdr pair)

; Use value of :initially if we don't find the pair.

      default)))

(defun rgfp (x)
  (declare (xargs :guard t :verify-guards t))
  (if (atom x)
      (equal x nil)
    (and (unsigned-byte-p 32 (car x))
         (rgfp (cdr x)))))

(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defthm nat-listp-forward-to-integer-listp
  (implies (nat-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)

(defthm rgfp-forward-to-nat-listp
  (implies (rgfp x)
           (nat-listp x))
  :rule-classes :forward-chaining)

(defun eipp (x)
       (declare (xargs :guard t :verify-guards t))
       (unsigned-byte-p 32 x))

(defun flgp (x)
       (declare (xargs :guard t :verify-guards t))
       (unsigned-byte-p 32 x))

(defun memp (x)
  (declare (xargs :guard t :verify-guards t))
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (natp (caar x))
         (unsigned-byte-p 32 (cdar x))
         (memp (cdr x)))))

(defthm memp-forward-to-eqlable-alistp
  (implies (memp x)
           (eqlable-alistp x))
  :rule-classes :forward-chaining)

(defun msp (x)
  (declare (xargs :guard t))
  (declare (ignore x))
  t)

(defun x86-32p (x86-32)
  (declare (xargs :guard t :verify-guards t))
  (and (true-listp x86-32)
       (= (length x86-32) 5)
       (rgfp (nth 0 x86-32))
       (equal (len (nth 0 x86-32)) 8)
       (eipp (nth 1 x86-32))
       (flgp (nth 2 x86-32))
       (memp (nth 3 x86-32))
       (msp  (nth 4 x86-32))
       t))

(defun create-x86-32 nil
  (declare (xargs :guard t :verify-guards t))
  (list (make-list 8 :initial-element '0)
        '0
        '0
        nil
        nil))

(defun rgf-length (x86-32)
       (declare (xargs :guard (x86-32p x86-32)
                       :verify-guards t)
                (ignore x86-32))
       8)

(defun resize-rgf (i x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t)
           (ignore i))
  (prog2$
   (hard-error
    'resize-rgf
    "the array field corresponding to accessor ~x0 of ~
              stobj ~x1 was not declared :resizable t.  ~
              therefore, it is illegal to resize this array."
    (list (cons #\0 'rgfi)
          (cons #\1 'x86-32)))
   x86-32))

(defun rgfi (i x86-32)
       (declare (xargs :guard (and (x86-32p x86-32)
                                   (integerp i)
                                   (<= 0 i)
                                   (< i (rgf-length x86-32)))
                       :verify-guards t))
       (nth i (nth 0 x86-32)))

(defun !rgfi (i v x86-32)
  (declare (xargs :guard (and (x86-32p x86-32)
                              (integerp i)
                              (<= 0 i)
                              (< i (rgf-length x86-32))
                              (unsigned-byte-p 32 v))
                  :verify-guards t))
  (update-nth-array 0 i v x86-32))

(defun eip (x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t))
  (nth 1 x86-32))

(defun !eip (v x86-32)
  (declare (xargs :guard (and (unsigned-byte-p 32 v)
                              (x86-32p x86-32))
                  :verify-guards t))
  (update-nth 1 v x86-32))

(defun flg (x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t))
  (nth 2 x86-32))

(defun !flg (v x86-32)
  (declare (xargs :guard (and (unsigned-byte-p 32 v)
                              (x86-32p x86-32))
                  :verify-guards t))
  (update-nth 2 v x86-32))

#||
(defun mem-length (x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t)
           (ignore x86-32))
  #x40000000)
||#

(defun resize-mem (i x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t)
           (ignore i))
  (prog2$
   (hard-error
    'resize-mem
    "the array field corresponding to accessor ~x0 of ~
              stobj ~x1 was not declared :resizable t.  ~
              therefore, it is illegal to resize this array."
    (list (cons #\0 'memi)
          (cons #\1 'x86-32)))
   x86-32))

(defun memi (i x86-32)
  (declare (xargs :guard (and (x86-32p x86-32)
                              (integerp i)
                              (<= 0 i))
                  :verify-guards t))
  (lookup i
          (nth 3 x86-32)
; Use value of :initially if we don't find the pair:
          0))

(defun !memi (i v x86-32)
  (declare (xargs :guard (and (x86-32p x86-32)
                              (integerp i)
                              (<= 0 i)
                              (unsigned-byte-p 32 v))
                  :verify-guards t))
  (update-nth 3
              (hons-acons i v (nth 3 x86-32))
              x86-32))

(defun ms (x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t))
  (nth 4 x86-32))

(defun !ms (v x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :verify-guards t))
  (update-nth 4 v x86-32))

(defconst *rgfi* 0)
(defconst *eip* 1)
(defconst *flg* 2)
(defconst *memi* 3)
(defconst *ms* 4)

; Theorems from ../common/x86-state.lisp

; We first deal with the STOBJ read lemmas

; RGF read lemmas

(defthm natp-nth-of-rgf
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-rgf-<=4294967296
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4294967296))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-rgfi
  (implies (and (force (x86-32p x86-32))
                (force (n03p i)))
           (and (integerp (rgfi i x86-32))
                (<= 0 (rgfi i x86-32))))
  :rule-classes :type-prescription)

(defthm rgfi-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n03p i))
           (< (rgfi i x86-32) 4294967296))
  :rule-classes :linear)


; EIP read lemmas

(defthm natp-eip
  (implies (force (x86-32p x86-32))
           (and (integerp (eip x86-32))
                (<= 0 (eip x86-32))))
  :rule-classes :type-prescription)

(defthm eip-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (eip x86-32) 4294967296))
  :rule-classes :linear)


; FLG read lemmas

(defthm natp-flg
  (implies (force (x86-32p x86-32))
           (and (integerp (flg x86-32))
                (<= 0 (flg x86-32))))
  :rule-classes :type-prescription)

(defthm flg-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (flg x86-32) 4294967296))
  :rule-classes :linear)

; MEM read lemmas

(defthm natp-lookup
  (implies (and (memp x)
                (natp default))
           (and (integerp (lookup i x default))
                (<= 0 (lookup i x default))))
  :rule-classes :type-prescription)

(defthm lookup-is-unsigned-byte-p-32
  (implies (and (memp x)
                (unsigned-byte-p 32 default))
           (< (lookup i x default) #x100000000))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(in-theory (disable lookup))

(defthm natp-memi-when-n30p-addr
  (implies (and (force (x86-32p x86-32))
                (force (n30p addr)))
           (and (integerp (memi addr x86-32))
                (<= 0 (memi addr x86-32))))
  :rule-classes (:rewrite :type-prescription))

(defthm memi-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (force (n30p addr)))
           (< (memi addr x86-32) #x100000000))
  :rule-classes :linear)

(encapsulate
 ()

 (local
  (def-gl-thm n32p-ash--2-is-n30p-lemma
    :hyp (n32p x)
    :concl (n30p (ash x -2))
    :g-bindings
    `((x (:g-number ,(gl-int  0  1  33))))))

 (defthm n32p-ash--2-is-n30p
   (implies (n32p x)
            (n30p (ash x -2)))
   :hints (("Goal" :by n32p-ash--2-is-n30p-lemma))
   :rule-classes ((:type-prescription
                   :corollary (implies (n32p x)
                                       (natp (ash x -2))))
                  (:linear
                   :corollary (implies (n32p x)
                                       (< (ash x -2) 1073741824))))))

; We wonder if the two lemmas about !xxx would be better as
; :FORWARD-CHAINING rules (or, as both :REWRITE and :FORWARD-CHAINING
; rules), using *MEM-SIZE-IN-BYTES* and *REG-SIZE-IN-DWRDS* in the
; hypotheses instead of LEN.

(defthm length-is-len-when-not-stringp
  (implies (not (stringp x))
           (equal (length x)
                  (len x)))
  :hints (("Goal" :in-theory (e/d (length) ()))))

; RGF update lemmas

(defthm rgfp-update-nth
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (rgfp (update-nth i v x))))

(defthm x86-32p-!rgfi-n03p
  (implies (and (x86-32p x86-32)
                (n03p i)
                (n32p v))
           (x86-32p (!rgfi i v x86-32))))


; EIP update lemma

(defthm x86-32p-!eip
  (implies (and (x86-32p x86-32)
                (n32p v))
           (x86-32p (!eip v x86-32))))

; EFLAGS update lemma

(defthm x86-32p-!flg
  (implies (and (x86-32p x86-32)
                (n32p v))
           (x86-32p (!flg v x86-32))))

; Memory update lemmas

(defthm memp-update-nth
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (n32p v))
           (memp (hons-acons i v x))))

(defthm x86-32p-!memi-n30p
  (implies (and (force (x86-32p x86-32))
                (force (n30p i))
                (force (n32p v)))
           (x86-32p (!memi i v x86-32))))

; MS update lemma

(defthm x86-32p-!ms
  (implies (x86-32p x86-32)
           (x86-32p (!ms v x86-32))))

; Should we have this next group of lemmas?  Probably not, but the
; first, for instance, one allows later lemma X86-32P-WMB-NO-WRAP (see
; below) to be proven.

(defthm len-x86-32-rgf
  (implies (x86-32p x86-32)
           (equal (len (nth *rgfi* x86-32))
                  *m86-32-reg-names-len*)))

#||
(defthm len-x86-32-mem
  (implies (x86-32p x86-32)
           (equal (len (nth *memi* x86-32))
                  *mem-size-in-dwords*)))
||#

(defthm x86-32p-properties
  (implies (x86-32p x86-32)
           (and (true-listp x86-32)
                (equal (len x86-32) 5)

                (rgfp (nth 0 x86-32))
                (equal (len (nth 0 x86-32))
                       *m86-32-reg-names-len*)

                (eipp (nth 1 x86-32))
                (flgp (nth 2 x86-32))

                (memp (nth 3 x86-32))
                ;; (equal (len (nth 3 x86-32)) *mem-size-in-dwords*)

                (msp (nth 4 x86-32))
                ))
  :rule-classes :forward-chaining)

; Additional lemmas to help with later guard proofs.

; Hopefully, we have proven all the facts we need about the X86
; machine state.

(in-theory (disable x86-32p
                    rgfp        rgfi        !rgfi
                    eipp        eip         !eip
                    flgp        flg         !flg
                    memp        memi        !memi
                    msp         ms          !ms
                    ))

; Read memory byte and memory double-word functions

(encapsulate
 ()

 (local
  (def-gl-thm ash-logand-addr-3-is-integerp-less-or-equal-24
    :hyp (n32p addr)
    :concl (<= (ash (logand addr 3) 3) 24)
    :g-bindings
     `((addr (:g-number ,(gl-int  0 1 33))))))

 (local
  (def-gl-thm ash-memi-ash-logand-addr
    :hyp (and (n32p mem-value)
              (n32p addr))
    :concl (< (ash mem-value (- (ash (logand addr 3) 3)))
              4294967296)
    :rule-classes :linear
    :g-bindings
    `((addr      (:g-number ,(gl-int  0 1 33)))
      (mem-value (:g-number ,(gl-int 33 1 33))))))

 (defun rm08 (addr x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (x86-32p x86-32))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num     (n02 addr))
          (dword-addr   (ash addr -2))
          (dword        (memi dword-addr x86-32))
          (shift-amount (ash byte-num 3))
          ;; Next form causes (callq (@ .SPBUILTIN-ASH)).
          (shifted-word (ash dword (- shift-amount))))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword shifted-word)
              (type (integer 0     24) shift-amount))
     (n08 shifted-word)))

 (defun rm16 (addr x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (x86-32p x86-32))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num   (n02 addr))
          (dword-addr (ash addr -2))
          (dword      (memi dword-addr x86-32)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword))
     (if (= byte-num 3)
       ;; Memory "wrap"
         (let* ((byte0 (rm08       addr    x86-32))
                (byte1 (rm08 (n32+ addr 1) x86-32)))
           (declare (type (unsigned-byte 8) byte0 byte1))
           (logior (ash byte1 8) byte0))
       (logand (ash dword (- (ash byte-num 3)))
               #xffff))))

 (local (defthm integerp-+
          (implies (and (integerp x)
                        (integerp y))
                   (integerp (+ x y)))))

 (local (defthm integerp-expt
          (implies (natp x)
                   (integerp (expt 2 x)))))

 (defun rm32 (addr x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (x86-32p x86-32))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num   (n02 addr))
          (dword-addr (ash addr -2))
          (dword      (memi dword-addr x86-32)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword))
     (if (= byte-num 0)
         dword

; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;     dword-addr+1  dword-addr  ...... 0
;           |        |
; [next-dword] [dword]
;    xxxxxxxx xxxxxxxx  [from old mem]
;                   <>  shift0 [ 8 in this example]
;               <-  ->  shift1 [24 in this example]
;             xx        lo
;      xxxxxx           hi

       (let* ((shift0 (ash (- 4 byte-num) 3))
              (shift1 (ash byte-num 3))
              (lo (ash dword (- shift1)))
              (dword-addr+1 (n30+ dword-addr 1))
              (next-dword (memi dword-addr+1 x86-32))
              (hi (logand next-dword (- (ash 1 shift1)
                                        1))))
         (declare (type (unsigned-byte 32) lo hi))
         (logior lo (ash hi shift0)))))))

(defthm natp-rm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm08 addr x86-32))
                (<= 0 (rm08 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm08-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (< (rm08 addr x86-32) 256))
  :rule-classes :linear)

(in-theory (disable rm08))

(encapsulate
 ()
 (local
  (def-gl-thm logior-ash-bytes-<=-0
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl
    (<= 0 (logior (ash byte1 8) byte0))
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9))))))

 (local
  (def-gl-thm logior-ash-bytes-<-4294967296
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl
    (< (logior (ash byte1 8) byte0)
       65536)
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9))))))

 (defthm integerp-rm16
   (implies (and (force (x86-32p x86-32))
                 (force (n32p addr)))
            (and (integerp (rm16 addr x86-32))
                 (<= 0 (rm16 addr x86-32))))
   :rule-classes :type-prescription)

 (defthm rm16-less-than-expt-2-16
   (implies (and (x86-32p x86-32)
                 (n32p addr))
            (< (rm16 addr x86-32) 65536))
   :rule-classes :linear))

(in-theory (disable rm16))

(defthm integerp-rm32
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm32 addr x86-32))
                (<= 0 (rm32 addr x86-32))))
  :rule-classes :type-prescription)

(encapsulate
 ()

 (local
  (def-gl-thm hack
    :hyp (and (n32p dword1)
              (n32p dword2)
              (integerp addr)
              (<= 0 addr)
              (< addr 4294967296)
              (not (equal (logand addr 3) 0)))
    :concl (< (logior (ash dword1
                           (- (ash (logand addr 3) 3)))
                      (ash (logand dword2
                                   (+ -1 (ash 1 (ash (logand addr 3) 3))))
                           (ash (+ 4 (- (logand addr 3))) 3)))
              4294967296)
    :g-bindings
    `((addr (:g-number ,(gl-int 0 1 33)))
      (dword1 (:g-number ,(gl-int 33 1 33)))
      (dword2 (:g-number ,(gl-int 66 1 33))))))

 (defthm rm32-less-than-expt-2-32
   (implies (and (x86-32p x86-32)
                 (n32p addr))
            (< (rm32 addr x86-32) 4294967296))
   :rule-classes :linear))

(in-theory (disable rm32))

; Write memory byte, memory double-word functions

(encapsulate
 ()

 (local
  (def-gl-thm ash-logand-addr-3-is-integerp-less-than-or-equal-24
    :hyp (n32p addr)
    :concl (<= (ash (logand addr 3) 3) 24)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33))))))

 (local
  (def-gl-thm ash-n08p-ash-logand-addr-3-3
    :hyp (and (n32p addr)
              (n08p byte))
    :concl (< (ash byte (ash (logand addr 3) 3))
               4294967296)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9))))))

 (local
  (def-gl-thm word-to-write-equality
    :hyp (and (n08p byte)
              (n32p val)
              (n32p addr))
    :concl
    (equal (logand (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
                           (ash byte (ash (logand addr 3) 3)))
                   4294967295)
           (logior (logand (lognot (ash 255 (ash (logand addr 3) 3)))
                           val)
                   (ash byte (ash (logand addr 3) 3))))
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (val  (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm natp-word-to-write
    :hyp (and (n08p byte)
              (n32p value)
              (n32p addr))
    :concl
    (<= 0 (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) value)
                  (ash byte (ash (logand addr 3) 3))))
    :rule-classes :linear
    :g-bindings
    `((addr  (:g-number ,(gl-int  0 1 33)))
      (byte  (:g-number ,(gl-int 33 1 9)))
      (value (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm word-to-write-equality-less-than-2^32
    :hyp (and (n08p byte)
              (n32p val)
              (n32p addr))
    :concl
    (< (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
               (ash byte (ash (logand addr 3) 3)))
       4294967296)
    :rule-classes :linear
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (val  (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm another-logand-fact
    :hyp (and (n32p word)
              (n08p byte)
              (n32p addr))
    :concl
    (<= 0 (logior (logand (+ -1 (- (ash 255 (ash (logand addr 3) 3)))) word)
                  (ash byte (ash (logand addr 3) 3))))
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (word (:g-number ,(gl-int 42 1 33))))))

 (defun wm08 (addr byte x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (n08p byte)
                               (x86-32p x86-32))
                   :guard-hints
                   (("Goal" :in-theory (e/d () (lognot))))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num       (n02 addr))
          (dword-addr     (ash addr -2))
          (dword          (memi dword-addr x86-32))
          (mask           #xFF)
          (shift-amount   (ash byte-num 3))
          (byte-mask      (ash mask shift-amount))
          (dword-masked   (logand (lognot byte-mask) dword))
          (byte-to-write  (ash byte shift-amount))
          (dword-to-write (logior dword-masked byte-to-write)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (integer 0     24) shift-amount)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32)
                    byte-mask dword dword-masked byte-to-write dword-to-write))
     (!memi dword-addr dword-to-write x86-32)))

 (defthm x86-32p-wm08
   (implies (and (x86-32p x86-32)
                 (n32p addr)
                 (n08p byte))
            (x86-32p (wm08 addr byte x86-32)))))

(in-theory (disable wm08))

(encapsulate
 ()

 (local
  (def-gl-thm hack1
    :hyp (and (n32p addr)
              (not (equal (logand addr 3) 3)))
    :concl (<= (ash (logand addr 3) 3) 16)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33))))
    :rule-classes :linear))

 (local
  (def-gl-thm hack2
    :hyp (and (n16p word)
              (natp shift)
              (<= shift 16))
    :concl (< (ash word shift) 4294967296)
    :g-bindings
    `((word  (:g-number ,(gl-int 0 1 17)))
      (shift (:g-number ,(gl-int 17 1 6))))
    :rule-classes :linear))

 (local
  (def-gl-thm logior-ash-bytes-<-4294967296
    :hyp (and (n08p byte0)
              (n08p byte1)
              (n08p byte2)
              (n08p byte3))
    :concl
    (< (logior (ash byte3 24) (ash byte2 16) (ash byte1 8) byte0)
       4294967296)
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9)))
      (byte2 (:g-number ,(gl-int 18 1 9)))
      (byte3 (:g-number ,(gl-int 27 1 9))))))

 (defun wm16 (addr word x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (n16p word)
                               (x86-32p x86-32))
                   :guard-hints
                   (("Goal" :in-theory (e/d () (lognot))))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num      (n02 addr))
          (dword-addr    (ash addr -2)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr))
     (if (= byte-num 3) ; memory wrap
         (b* ((x86-32 (wm08       addr    (n08      word     ) x86-32))
              (x86-32 (wm08 (n32+ addr 1) (n08 (ash word  -8)) x86-32)))
             x86-32)
       (let* ((dword          (memi dword-addr x86-32))
              (mask           #xFFFF)
              (shift-amount   (ash byte-num 3))
              (byte-mask      (ash mask shift-amount))
              (dword-masked   (logand (lognot byte-mask) dword))
              (word-to-write  (ash word shift-amount))
              (dword-to-write (logior dword-masked word-to-write)))
         (declare (type (integer 0 16) shift-amount)
                  (type (unsigned-byte 32)
                        byte-mask dword dword-masked word-to-write
                        dword-to-write))
         (!memi dword-addr dword-to-write x86-32)))))

 (defthm x86-32p-wm16
   (implies (and (x86-32p x86-32)
                 (n32p addr)
                 (n16p word))
            (x86-32p (wm16 addr word x86-32)))))

(in-theory (disable wm16))

; The next two hack lemmas are needed not only to admit wm32 (below), but also
; to prove x86-32p-wm32 (below).

(local
 (def-gl-thm hack1
   :hyp (and (n32p dword)
             (n32p addr))
   :concl
   (< (ash (logand dword
                   (+ -1
                      (ash 1 (ash (+ 4 (- (logand addr 3))) 3))))
           (ash (logand addr 3) 3))
      4294967296)
   :g-bindings
   `((dword (:g-number ,(gl-int  0 1 33)))
     (addr  (:g-number ,(gl-int 34 1 33))))))

(local
 (def-gl-thm hack2
   :hyp (and (n32p dword)
             (n32p addr))
   :concl
   (< (ash dword
           (- (ash (+ 4 (- (logand addr 3))) 3)))
      4294967296)
   :g-bindings
   `((dword (:g-number ,(gl-int  0 1 33)))
     (addr  (:g-number ,(gl-int 34 1 33))))))

(defun wm32 (addr dword x86-32)
  (declare (xargs :guard (and (n32p addr)
                              (n32p dword)
                              (x86-32p x86-32))))
  (declare (type (unsigned-byte 32) addr))
  (let* ((byte-num   (n02 addr))
         (dword-addr (ash addr -2)))
    (declare (type (integer 0 3) byte-num)
             (type (unsigned-byte 30) dword-addr))
    (if (= byte-num 0)
        (!memi dword-addr dword x86-32)

; We write two dwords to memory: a lower dword obtained by replacing the upper
; bits of the original lower dword, and similarly, an upper dword obtained by
; replacing the lower bits of the original upper dword.

; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;  dword-addr+1  dword-addr  ...... 0
;        |        |
; xxxxxxxx xxxxxxxx  [from old mem]
;   xxxxxx xx        dword
;                <>  shift0 [ 8 in this example]
;                ff  mask0
;            <-  ->  shift1 [24 in this example]
;            ffffff  mask1

      (let* ((dword0-old   (memi dword-addr x86-32))
             (shift0       (ash (- 4 byte-num) 3))
             (mask0        (- (ash 1 shift0) 1))
             (shift1       (ash byte-num 3))
             (mask1        (- (ash 1 shift1) 1))
             (dword0-lo    (logand dword0-old mask1))
             (dword0-hi    (ash (logand dword mask0) shift1))
             (dword0-new   (logior dword0-lo dword0-hi))
             (x86-32       (!memi dword-addr dword0-new x86-32))
             (dword-addr+1 (n30+ dword-addr 1))
             (dword1-old   (memi dword-addr+1 x86-32))
             (dword1-lo    (ash dword (- shift0)))
             (dword1-hi    (logand dword1-old (ash mask0 shift1)))
             (dword1-new   (logior dword1-lo dword1-hi))
             (x86-32       (!memi dword-addr+1 dword1-new x86-32)))
        x86-32))))

(defthm x86-32p-wm32
  (implies (and (x86-32p x86-32)
                (n32p addr)
                (n32p dword))
           (x86-32p (wm32 addr dword x86-32))))

(in-theory (disable wm32))

;;; The following lemmas probably won't be needed once we can traffic in stobjs
;;; when doing alist-based reasoning.

(defthm logior-<=-expt-2-to-n
   (implies (and (natp x) (natp y)
                 (< x (expt 2 n))
                 (< y (expt 2 n)))
            (< (logior x y) (expt 2 n)))
   :rule-classes :linear)

(defthm logior-bound-2^32
  (implies (and (natp x)
                (natp y)
                (< x *2^32*)
                (< y *2^32*))
           (< (logior x y) *2^32*))
  :hints (("Goal" :use ((:instance logior-<=-expt-2-to-n
                                   (n 32))))))

(local
 (def-gl-thm hack3
   :hyp (and (natp addr)
             (< addr 4294967296)
             (natp byte)
             (< byte 256))
   :concl
   (< (ash byte (ash (logand addr 3) 3))
      4294967296)
   :g-bindings
   `((addr (:g-number ,(gl-int  0 1 33)))
     (byte  (:g-number ,(gl-int 34 1 9))))))

;(in-theory (disable (expt)))

(defthm wm08-preserves-x86-32p
  (implies (and (force (n32p addr))
                (force (n08p byte))
                (force (x86-32p x86-32)))
           (x86-32p (wm08 addr byte x86-32)))
  :hints (("Goal" :in-theory (enable wm08))))

(defthm wm16-preserves-x86-32p
  (implies (and (force (n32p addr))
                (force (n16p word))
                (force (x86-32p x86-32)))
           (x86-32p (wm32 addr word x86-32)))
  :hints (("Goal" :in-theory (enable wm16))))

(defthm wm32-preserves-x86-32p
  (implies (and (force (n32p addr))
                (force (n32p dword))
                (force (x86-32p x86-32)))
           (x86-32p (wm32 addr dword x86-32)))
  :hints (("Goal" :in-theory (enable wm32))))
