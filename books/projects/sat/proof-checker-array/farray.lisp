;; Custom package
(in-package "PROOF-CHECKER-ARRAY")

;; ===================================================================
;; ============================= FARRAY ==============================
;; ===================================================================

;; In this book, a data structure for a field-addressable array, or "farray",
;; is defined and analyzed.

;; =================== BACKGROUND AND DESCRIPTION ====================

;; Stobjs provide constant time lookup for stobj fields/arrays in ACL2, as
;; opposed to lists which require linear time lookup for nth/update-nth
;; operations.  If one wants to store multiple fields within a stobj, they need
;; to prove theorems about how writes to each field interact with each other
;; field.  This leads to poor "proof convenience" and "proof efficiency" (I
;; believe these terms were used by J Moore at some point in our discussions
;; and I've latched onto it) because each fields leads to a quadratic number of
;; theorems.

;; Instead, a stobj "st" can be defined with just one field: an array for
;; memory, or "mem".  This field can be subdivided further into other arrays
;; and scalars.  In this way, a single array in a stobj can simulate a stobj
;; with multiple fields.  To accomplish this, an offset table is defined that
;; redirects reads and writes to the proper field/subarray.  With the proper
;; invariants, one can show that writes to any field do not interfere with
;; other fields.  Furthermore, the addition of a field to an farray structure
;; does not create any extra proof effort.  This solves the problem of
;; quadratic blowup of theorems for stobj data structures.  (This approach is a
;; generalization of an abstraction J Moore used in the M1 model.)  The only
;; catch is that all arrays and scalars will share the same type (60-bit
;; signed-integers in this definition).

;; Other thoughts:

;; This approach is somewhat analogous to memory usage in a traditional C or
;; C-like language.  More thoughts on this later...

;; In theory, farrays can be embedded; that is, a field of an farray may
;; contain another farray.  I haven't experimented with this yet...

;; This could very well be similar in execution efficiency and proof efficiency
;; to record-like stobjs (Jared Davis) or abstract stobjs (Shilpi Goel and Matt
;; Kaufmann)...

;; ============================= LAYOUT ==============================

;; The layout of this book is as follows:
;; -- Define the stobj in which the farray will reside.
;; -- Define and analyze recursive predicate for checking farray field table.
;; -- Define farray predicate.
;; -- Define types, accessors, and updaters including:
;;    ++ num-fields
;;    ++ fieldp
;;    ++ flength
;;    ++ field-offsetp
;;    ++ fread
;;    ++ fwrite
;; -- Prove theorems about fread and fwrite such as read of write, write of
;;    write, etc.
;; -- Define functions for easily reading lists from and writing lists to stobj
;; -- Define and analyze a membership operator for ranges within a field

;; ============================ INCLUDES =============================

;; This book contains the macro for (signed-byte-p 60 x).
(include-book "supplemental/sb60")
;; (defmacro sb60p (x) `(signed-byte-p 60 ,x))


;; We want rewrite rules in this book to be tight.  Best to keep this handy.
;; Commented out hypotheses in the theorems below were determined to be
;; unnecessary by remove-hyps.
(include-book "tools/remove-hyps" :dir :system)

;; ======================== STOBJ DEFINITION =========================

;; Multiple farrays can reside in the same stobj array, but (for now) the
;; farray needs to be in the "st" stobj defined here.

;; Initially, the field "mem" will be length 0.
(defconst *init-mem-size* 0)

;; Stobj definition for "st", short for "state".
(defstobj st
  ;; One field called "mem", short for "memory", is an array of 60-bit signed
  ;; integers.
  (mem :type (array (signed-byte 60) (*init-mem-size*))
       ;; All values are initially 0,
       :initially 0
       ;; And the field is resizable.
       :resizable t)

  ;; Accessors/updaters are inlined
  :inline t
  ;; Renaming for the shorter functions names !memi and mem-len
  :renaming ((update-memi !memi)
             (mem-length mem-len)))


;; ===================================================================

;; nth on the mem returns a sb60p
(defthm sb60p-nth-mem
  (implies (and (memp mem)
                ;; (integerp i)
                (<= 0 i)
                (< i (len mem)))
           (sb60p (nth i mem))))

;; update-nth returns a memp object
(defthm memp-update-nth
  (implies (and (memp mem)
                ;; (integerp i)
                ;; (<= 0 i)
                (< i (len mem))
                (sb60p v))
           (memp (update-nth i v mem))))

;; Two update-nths to the same location resolve to the outermost update-nth.
(defthm update-nth-update-nth-same
  (equal (update-nth i v2 (update-nth i v1 x))
         (update-nth i v2 x)))

;; Using update-nth to write the same value that is already present at a
;; location results in the same list.
(defthm update-nth-redundant
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len x))
                (equal (nth i x) v))
           (equal (update-nth i v x)
                  x)))

;; update-nths to distict locations can be rearranged to a canonical form.
(defthm update-nth-update-nth-different
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                (not (equal i j)))
           (equal (update-nth j v2 (update-nth i v1 x))
                  (update-nth i v1 (update-nth j v2 x)))))
  ;; An explicit :loop-stopper instruction.  This is inferred by ACL2.
  ;; :rule-classes ((:rewrite :loop-stopper ((j i update-nth)))))

;; Resizing a list results in a valid memp object.
(defthm memp-resize-list
  (implies (and (stp st)
                (sb60p default))
           (memp (resize-list (car st)
                              new-size
                              default))))

;; The length of resized a list is equal to the new size.
(defthm len-resize-list
  (implies (natp new-size)
           (equal (len (resize-list list new-size default))
                  new-size)))

;; Remove *memi* constant from theorems.
(defthm nth-*memi*
  (equal (nth *memi* st)
         (car st)))

;; Remove *memi* constant from theorems.
(defthm update-nth-*memi*
  (equal (update-nth *memi* v st)
         (cons v (cdr st))))

;; Disable nth, update-nth, and resize-list.  Everything from here out will be
;; about memi, !memi, mem-len, and resize-mem.
(in-theory (disable nth update-nth resize-list))


;; ===================================================================

;; All values in the memory are 60-bit signed integers.
(defthm sb60p-memi
  (implies (and (stp st)
                ;; (integerp i)
                (<= 0 i)
                (< i (mem-len st)))
           (sb60p (memi i st))))

;; Writing to mem results in a valid st.
(defthm stp-!memi
  (implies (and (stp st)
                ;; (integerp i)
                ;; (<= 0 i)
                (< i (mem-len st))
                (sb60p v))
           (stp (!memi i v st))))

;; Reading a value from a write results in the written value if the indices are
;; equal.
(defthm memi-!memi
  (implies (and (integerp i)
                (<= 0 i)
                ;; (< i (mem-len st))
                (integerp j)
                (<= 0 j)
                ;; (< j (mem-len st))
                )
           (equal (memi i (!memi j v st))
                  (if (equal i j)
                      v
                    (memi i st)))))

;; Resizing mem results in a valid st.
(defthm stp-resize-mem
  (implies (and (stp st)
                (natp new-size))
           (stp (resize-mem new-size st))))

;; The length of mem will be the new size.
(defthm mem-len-resize-mem
  (implies (natp new-size)
           (equal (mem-len (resize-mem new-size st))
                  new-size)))

;; Writing to mem has no effect on the length of mem.
(defthm mem-len-!memi
  (implies (and ;; (integerp i)
                (<= 0 i)
                (< i (mem-len st)))
           (equal (mem-len (!memi i v st))
                  (mem-len st))))

;; Writing to the same location twice results in the outermost write.
(defthm !memi-!memi-same
  (equal (!memi i v2 (!memi i v1 st))
         (!memi i v2 st)))

;; Writing the the value already present at a location results in the same st.
(defthm !memi-redundant
  (implies (and (stp st)
                (integerp i)
                (<= 0 i)
                (< i (mem-len st))
                (equal (memi i st) v))
           (equal (!memi i v st)
                  st)))

;; Writes to distinct locations can be canonicalized.
(defthm !memi-!memi-different
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                (not (equal i j)))
           (equal (!memi j v2 (!memi i v1 x))
                  (!memi i v1 (!memi j v2 x)))))
  ;; An explicit :loop-stopper instruction.  This is inferred by ACL2.
  ;; :rule-classes ((:rewrite :loop-stopper ((j i !memi)))))

;; Disable all stobj primitives.
(in-theory (disable stp
                    memp
                    memi
                    !memi
                    mem-len
                    resize-mem))


;; ===================== TYPE INFO / ARITHMETIC ======================

;; sb60p implies other things.  Wish this could be removed...  Potentially make
;; this forward-chaining.
(defthm sb60p-types
  (implies (sb60p x)
           (and (integerp x)
                (real/rationalp x)
                (acl2-numberp x))))

;; integerp implies other things.  Wish this could be removed...  Potentially
;; make this forward-chaining.
(defthm integerp-types
  (implies (integerp x)
           (and (real/rationalp x)
                (acl2-numberp x))))

;; addition preserves integerp
(local
 (defthm integerp-+
   (implies (and (integerp i)
                 (integerp j))
            (integerp (+ i j)))))

;; addition preserves <= 0
(local
 (defthm <=-0-+
   (implies (and (<= 0 i)
                 (<= 0 j))
            (<= 0 (+ i j)))))


;; ========================== FIELD-TABLEP ===========================

;; The field-tablep predicate is a recursive function that validates the table
;; of indices used by the farray.

;; "i" is the current index in the field table.  "end" is the last address in
;; the field table.  "end" is always one beyond the last addressable field
;; position.
(defun field-tablep (i end st)
  (declare (xargs :guard (and (stp st)
                              (integerp i)
                              (<= 0 i)
                              (< i (mem-len st))
                              (integerp end)
                              (<= 0 end)
                              (< end (mem-len st))
                              (<= i end))
                  :stobjs (st)
                  :measure (nfix (- end i))))
  (if (not (mbt (and (integerp i)
                     (<= 0 i)
                     (< i (mem-len st))
                     (integerp end)
                     (<= 0 end)
                     (< end (mem-len st))
                     (<= i end))))
      nil
    (if (equal i end)
        t
      (and (integerp (memi i st))
           (<= 0 (memi i st))
           (< (memi i st) (mem-len st))
           ;; The entry at i is past the end of the field table.
           (< end (memi i st))
           ;; The entry at i is before next offset at i+1.
           (< (memi i st) (memi (1+ i) st))
           (field-tablep (1+ i) end st)))))


;; Field table entries are integers.
(local
 (defthm field-tablep-implies-integerp-memi
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 ;; (< i end)
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (< j end))
            (integerp (memi j st)))))

;; Field table entries are greater than 0.
(local
 (defthm field-tablep-implies-<=-0-memi
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 ;; (< i end)
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (< j end))
            (<= 0 (memi j st)))
   :rule-classes (:linear :rewrite)))

;; Field table entries are less than the length of mem.
(local
 (defthm field-tablep-implies-<-memi-mem-len
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 ;; (< i end)
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (< j end))
            (< (memi j st) (mem-len st)))
   :rule-classes (:linear :rewrite)))

;; Field table entries are greater than the position of the last entry
(local
 (defthm field-tablep-implies-<-end-memi
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 ;; (< i end)
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (< j end))
            (< end (memi j st)))
   :rule-classes (:linear :rewrite)))

;; Field table entries are less than the next (i+1) entry.
(local
 (defthm field-tablep-implies-<-memi-memi-1+
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 ;; (< i end) ;
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (< j end))
            (< (memi j st) (memi (1+ j) st)))
   :rule-classes (:linear :rewrite)))

;; The field table is preserved when writes are above the table.
(local
 (defthm field-tablep-!memi
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 (integerp j)
                 ;; (<= 0 j)
                 (< j (mem-len st))
                 ;; (<= i end)
                 (< end j))
            (field-tablep i end (!memi j v st)))))

;; All inductive theorems are established.  Disable recursive field-tablep.
(in-theory (disable field-tablep))


;; ============================= FARRAYP =============================

;; An farray needs an "st" stobj and a start index.
(defun farrayp (start st)
  (declare (xargs :guard t
                  :stobjs (st)))
  (and (stp st) ; Valid stobj

       ;; The start index is valid.
       (integerp start)
       (<= 0 start)
       (< start (mem-len st))

       ;; The number of fields is valid.
       (integerp (memi start st))
       (<= 0 (memi start st))

       ;; The last field table entry is less than the length of mem.
       (< (+ start (memi start st) 1) (mem-len st))

       ;; The last field index is less than the length of mem.
       (< (memi (+ start (memi start st) 1) st)
          (mem-len st))

       ;; The length is limited to a 60-bit signed integer.
       (sb60p (mem-len st))

       ;; The field table is valid.  It starts at one past the start location
       ;; and ends at the start location plus the number of fields plus one.
       (field-tablep (+ start 1) (+ start (memi start st) 1) st)
       ))



;; =========================== NUM-FIELDS ============================

;; The num-fields accessor returns the number of fields in an farray.  It is
;; defined for convenience.

(defun num-fields (start st)
  (declare (xargs :guard (farrayp start st)
                  :stobjs (st)))
  (memi start st))

;; The number of fields is a sb60p.
(defthm sb60p-num-fields
  (implies (farrayp start st)
           (sb60p (num-fields start st)))
  :rule-classes :type-prescription)


;; ============================= FIELDP ==============================

;; The fieldp predicate checks if a field value is valid for an farray.  The
;; predicate serves as a shorthand form during proofs.

;; A value f is a field for an farray at start in st.
(defun fieldp (f start st)
  (declare (xargs :guard (farrayp start st)
                  :stobjs (st)))
  (and (integerp f)
       (<= 1 f)
       (<= f (num-fields start st))))

;; This forward-chaining rule provides the definition of fieldp even when
;; fieldp is disabled.
(defthm fieldp-forward-chaining
  (implies (fieldp f start st)
           (and (integerp f)
                (<= 1 f)
                (<= f (num-fields start st))))
  :rule-classes :forward-chaining)


;; ============================= FLENGTH =============================

;; The flength accessor will return the length of a field subarray.  The length
;; is defined to be the difference between two consecutive fields.

;; The length of field f for farray at start in st.
(defun flength (f start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st))
                  :stobjs (st)))
  (- (memi (+ start f 1) st)
     (memi (+ start f) st)))


;; A field's length is always positive.
(encapsulate
 ()
 (local (include-book "arithmetic/top-with-meta" :dir :system))
 (defthm <-0-flength
   (implies (and (farrayp start st)
                 (fieldp f start st))
            (< 0 (flength f start st)))
   :hints (("Goal"
            :use ((:instance field-tablep-implies-<-memi-memi-1+
                             (i (+ 1 start))
                             (end (+ start 1 (memi start st)))
                             (j (+ f start))))))))

;; A field's length is always in integer.
(defthm integerp-flength
  (implies (and (farrayp start st)
                (fieldp f start st))
           (integerp (flength f start st)))
  :hints (("Goal"
           :in-theory (disable field-tablep-implies-integerp-memi sb60p-memi)
           :use ((:instance field-tablep-implies-integerp-memi
                            (i (+ 1 start))
                            (end (+ start 1 (memi start st)))
                            (j (+ f start)))
                 (:instance sb60p-memi
                            (i (+ start 1 f)))))))

;; Each field fits inside mem.
(defthm flength-<-mem-len
  (implies (and (farrayp start st)
                (fieldp f start st))
           (< (flength f start st)
              (mem-len st)))
  :hints (("Goal"
           :use ((:instance field-tablep-implies-<-memi-mem-len
                            (i (+ 1 start))
                            (end (+ start 1 (memi start st)))
                            (j (+ start 1 f)))))))

;; A field's length is a sb60p.
(defthm sb60p-flength
  (implies (and (farrayp start st)
                (fieldp f start st))
           (sb60p (flength f start st)))
  :hints (("Goal"
           :use ((:instance flength-<-mem-len)
                 (:instance <-0-flength)
                 (:instance integerp-flength)))))


;; ========================== FIELD-OFFSETP ==========================

;; The field-offsetp predicate checks if an offset into a field subarray is
;; valid.  That is, each field has a starting location and ending location as
;; defined by the field table.  The locations that belong to a field are
;; addressable from 0 to (1- flength).

;; A value "offset" is a field offset for field f for an farray at start in st.
(defun field-offsetp (offset f start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st))
                  :stobjs (st)))
  (and (integerp offset)
       (<= 0 offset)
       ;; The following test was originally enforced by the predicate, but it
       ;; can be inferred with some proof effort later.
       ;; (< (+ offset (memi (+ start f) st)) (mem-len st))
       (< offset (flength f start st))))

;; The last field offset is within mem.
(local
 (encapsulate
  ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm flength-+-index-<-mem-len
    (implies (and (farrayp start st)
                  (fieldp f start st))
             (< (+ (flength f start st)
                   (memi (+ start f) st))
                (mem-len st)))
    :hints (("Goal"
             :use ((:instance field-tablep-implies-<-memi-mem-len
                              (i (+ 1 start))
                              (j (+ 1 start f))
                              (end (+ 1 start (memi start st))))))))))

;; Any field offset is within mem.
(local
 (defthm field-offsetp-implies-offset-+-index-<-mem-len
   (implies (and (field-offsetp offset f start st)
                 (farrayp start st)
                 (fieldp f start st))
            (< (+ offset (memi (+ start f) st)) (mem-len st)))
   :hints (("Goal"
            :use ((:instance flength-+-index-<-mem-len))))
   :rule-classes (:forward-chaining :rewrite)))

;; This forward-chaining rule provides the definition of field-offsetp even
;; when field-offsetp is disabled.
(defthm field-offsetp-forward-chaining
  (implies (field-offsetp offset f start st)
           (and (integerp offset)
                (<= 0 offset)
                (< offset (flength f start st))))
  :rule-classes :forward-chaining)

;; Zero is always a valid field-offset.
(defthm field-offsetp-0
  (implies (and (farrayp start st)
                (fieldp f start st))
           (field-offsetp 0 f start st))
  :hints (("Goal"
           :in-theory (disable flength))))

;; If the field offset is not zero, then one minus the offset is valid.
(defthm field-offsetp-1--not-0
  (implies (and (field-offsetp x f start st)
                (not (equal x 0)))
           (field-offsetp (1- x) f start st)))

;; Squeeze lemma for integers.
(local
 (defthm <-1+
   (implies (and (integerp x)
                 (integerp y)
                 (< x y)
                 (not (equal (1+ x) y)))
            (< (1+ x) y))))

;; If the field offset is not the last field offset for that particular field,
;; then one plus the offset is valid.
(defthm field-offsetp-1+-not-flength
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp x f start st)
                (not (equal (1+ x) (flength f start st))))
           (field-offsetp (1+ x) f start st))
  :hints (("Goal"
           :in-theory (disable flength))))

;; Given two offsets that are at least one apart, one minus the higher offset
;; is valid.
(defthm field-offsetp-1--squeeze
  (implies (and (field-offsetp x f start st)
                (field-offsetp y f start st)
                (<= (1- y) x)
                (not (equal x (1- y)))
                (not (equal (1- x) (1- y)))
                )
           (field-offsetp (1- x) f start st)))

;; A field offset is a sb60p.
(defthm sb60p-field-offsetp
  (implies (and (field-offsetp i f start st)
                (farrayp start st)
                (fieldp f start st))
           (sb60p i))
  :hints (("Goal"
           :use ((:instance sb60p-flength))))
  :rule-classes :forward-chaining)

;; One plus a field offset is a sb60p.
(defthm sb60p-1+-field-offsetp
  (implies (and (field-offsetp i f start st)
                (farrayp start st)
                (fieldp f start st))
           (sb60p (1+ i)))
  :hints (("Goal"
           :use ((:instance sb60p-flength)))))

;; One minus a field offset is a sb60p.
(defthm sb60p-1--field-offsetp
  (implies (and (field-offsetp i f start st)
                (farrayp start st)
                (fieldp f start st))
           (sb60p (1- i)))
  :hints (("Goal"
           :use ((:instance sb60p-flength)))))


;; ============================== FREAD ==============================

;; The fread accessor reads values in a field of an farray.  The correct index
;; in st is calculated based on the farray start location and the field table
;; entry.

;; Read the value at offset in field f for an farray at start in st.
(defun fread (f offset start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st)
                              (field-offsetp offset f start st))
                  ;; Need to find a way to remove this guard hint.
                  :guard-hints (("Goal"
                                 :use ((:instance field-offsetp-implies-offset-+-index-<-mem-len))))
                  :stobjs (st)))
  (memi (+ (memi (+ start f) st) offset) st))



;; ============================= FWRITE ==============================

;; The fwrite updater writes a value to a field of an farray.  The correct
;; index in st is calculated based on the farray start location and the field
;; table entry.

;; Write the value v to offset in field f for an farray at start in st.
(defun fwrite (f offset v start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st)
                              (field-offsetp offset f start st)
                              (sb60p v))
                  ;; Need to find a way to remove this guard hint.
                  :guard-hints (("Goal"
                                 :use ((:instance field-offsetp-implies-offset-+-index-<-mem-len))))
                  :stobjs (st)))
  (!memi (+ (memi (+ start f) st) offset) v st))



;; ==================== FREAD AND FWRITE THEOREMS ====================

;; An fread returns a sb60p.
(defthm sb60p-fread
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset f start st))
           (sb60p (fread f offset start st)))
  :hints (("Goal"
           :use ((:instance field-offsetp-implies-offset-+-index-<-mem-len)))))


;; An fwrite returns an farray
(defthm farrayp-fwrite
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset f start st)
                (sb60p v))
           (farrayp start (fwrite f offset v start st)))
  :hints (("Goal"
           :use ((:instance field-offsetp-implies-offset-+-index-<-mem-len)))))


;; An fwrite does not affect a field's length.
(defthm flength-fwrite
  (implies (and (farrayp start st)
                (fieldp f1 start st)
                (fieldp f2 start st)
                (field-offsetp offset2 f2 start st)
                ;; (sb60p v)
                )
           (equal (flength f1 start (fwrite f2 offset2 v start st))
                  (flength f1 start st))) )


;; ===================================================================

;; FREAD-FWRITE

;; The following theorems are used to build up to the theorem that describes an
;; fread of an fwrite.  The strategy is a two-part induction on the field table
;; to establish that two field entries are distinct.  This is then used to show
;; that valid offsets into fields are also distinct.

;; Induct once to show that all fields less than k have entries less than k's
;; entry.
(local
 (defthm field-tablep-ordering-arbitrary-k
   (implies (and ;; (integerp i)
             ;; (<= 0 i)
             ;; (< i (mem-len st))
             ;; (integerp end)
             ;; (<= 0 end)
             ;; (< end (mem-len st))
             (integerp k)
             ;; (<= 0 k)
             ;; (< k (mem-len st))
             (< i k)
             (< k end)
             (field-tablep i end st) ; moved to end
             )
            (< (memi i st)
               (memi k st)))
   :hints (("Goal"
            :in-theory (enable field-tablep)))))

;; Induct a second time to show that two arbitrary fields j and k with (< j k)
;; have field entries where the entry for j is less than the entry for k.
(local
 (defthm field-tablep-ordering-arbitrary-j-k
   (implies (and (field-tablep i end st)
                 ;; (integerp i)
                 ;; (<= 0 i)
                 ;; (< i (mem-len st))
                 ;; (integerp end)
                 ;; (<= 0 end)
                 ;; (< end (mem-len st))
                 (integerp j)
                 ;; (<= 0 j)
                 ;; (< j (mem-len st))
                 (<= i j)
                 (integerp k)
                 ;; (<= 0 k)
                 ;; (< k (mem-len st))
                 (< j k)
                 ;; (<= i k)
                 ;; (< j end)
                 (< k end))
            (< (memi j st)
               (memi k st)))
   :hints (("Goal"
            :in-theory (enable field-tablep)
            :induct (field-tablep i end st)))))

;; Disable the previous lemma for one induction.
(local (in-theory (disable field-tablep-ordering-arbitrary-k)))

;; Abstract the lemmas above to be based on fields instead of field table
;; entries.
(local
 (defthm field-tablep-ordering-arbitrary-field-based
   (implies (and (farrayp start st)
                 (fieldp f1 start st)
                 (fieldp f2 start st)
                 (< f1 f2))
            (< (memi (+ start f1) st)
               (memi (+ start f2) st)))))

;; Disable the other inductive lemma.
(local (in-theory (disable field-tablep-ordering-arbitrary-j-k)))

;; A field offset is less than the beginning of another field.
(local
 (encapsulate
  ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm field-tablep-ordering-arbitrary-field-based-offset-one
    (implies (and (farrayp start st)
                  (fieldp f1 start st)
                  (fieldp f2 start st)
                  (< f1 f2)
                  (field-offsetp offset1 f1 start st))
             (< (+ offset1 (memi (+ start f1) st))
                (memi (+ start f2) st)))
    :hints (("Goal"
             :use ((:instance field-tablep-ordering-arbitrary-field-based
                              (f1 (+ f1 1)))))))))

;; Two field offsets are less than each other if the fields are less than each
;; other.
(local
 (defthm field-tablep-ordering-arbitrary-field-based-offset-both
   (implies (and (farrayp start st)
                 (fieldp f1 start st)
                 (fieldp f2 start st)
                 (< f1 f2)
                 (field-offsetp offset1 f1 start st)
                 (field-offsetp offset2 f2 start st))
            (< (+ offset1 (memi (+ start f1) st))
               (+ offset2 (memi (+ start f2) st))))
   :hints (("Goal"
            :use ((:instance field-tablep-ordering-arbitrary-field-based-offset-one))))))

;; If two fields are distict, so are all offsets into those fields.
(local
 (defthm field-tablep-ordering-arbitrary-field-based-offset-both-ne
   (implies (and (farrayp start st)
                 (fieldp f1 start st)
                 (fieldp f2 start st)
                 (not (equal f1 f2))
                 (field-offsetp offset1 f1 start st)
                 (field-offsetp offset2 f2 start st))
            (not (equal (+ offset1 (memi (+ start f1) st))
                        (+ offset2 (memi (+ start f2) st)))))
   :hints (("Goal"
            :use ((:instance
                   field-tablep-ordering-arbitrary-field-based-offset-both
                   (f1 f2)
                   (offset1 offset2)
                   (f2 f1)
                   (offset2 offset1))
                  (:instance field-tablep-ordering-arbitrary-field-based-offset-both))))))


;; An fwrite followed by an fread results in the value written only if the
;; fields and offsets are equal.
(defthm fread-fwrite
  (implies (and (farrayp start st)
                (fieldp f1 start st)
                (field-offsetp offset1 f1 start st)
                ;; (sb60p v)
                (fieldp f2 start st)
                (field-offsetp offset2 f2 start st))
           (equal (fread f2 offset2 start (fwrite f1 offset1 v start st))
                  (if (and (equal f1 f2)
                           (equal offset1 offset2))
                      v
                    (fread f2 offset2 start st))))
  :hints (("Goal"
           :use ((:instance field-tablep-ordering-arbitrary-field-based-offset-both-ne)))))

;; ===================================================================

;; More theorems about fwrites.

;; Two fwrites to the same field and offset are the same as just one fwrite.
(defthm fwrite-fwrite-same
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset f start st)
                ;; (sb60p v1)
                ;; (sb60p v2)
                )
           (equal (fwrite f offset v2 start (fwrite f offset v1 start st))
                  (fwrite f offset v2 start st))))

;; An fwrite of the value already at the location is the same as no fwrite.
(defthm fwrite-redundant
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset f start st)
                ;; (sb60p v)
                (equal (fread f offset start st) v))
           (equal (fwrite f offset v start st)
                  st))
  :hints (("Goal"
           :use ((:instance field-offsetp-implies-offset-+-index-<-mem-len)))))

;; Two fwrites to distinct fields can be canonicalized.
(defthm fwrite-fwrite-different-field
  (implies (and (farrayp start st)
                (fieldp f1 start st)
                (field-offsetp offset1 f1 start st)
                ;; (sb60p v1)
                ;; (sb60p v2)
                (fieldp f2 start st)
                (field-offsetp offset2 f2 start st)
                (not (equal f1 f2)))
           (equal (fwrite f2 offset2 v2 start (fwrite f1 offset1 v1 start st))
                  (fwrite f1 offset1 v1 start (fwrite f2 offset2 v2 start st))))
  :hints (("Goal"
           :use ((:instance !memi-!memi-different
                            (i (+ offset1 (memi (+ f1 start) st)))
                            (j (+ offset2 (memi (+ f2 start) st)))
                            (x st))
                 (:instance field-tablep-ordering-arbitrary-field-based-offset-both-ne)))))
  ;; :rule-classes ((:rewrite :loop-stopper ((f2 f1 fwrite)))))

;; Two fwrites to the same field but distinct offsets can be canonicalized.
(defthm fwrite-fwrite-different-offset
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset1 f start st)
                (field-offsetp offset2 f start st)
                ;; (sb60p v1)
                ;; (sb60p v2)
                (not (equal offset1 offset2)))
           (equal (fwrite f offset2 v2 start (fwrite f offset1 v1 start st))
                  (fwrite f offset1 v1 start (fwrite f offset2 v2 start st))))
  :hints (("Goal"
           :use ((:instance !memi-!memi-different
                            (i (+ offset1 (memi (+ f start) st)))
                            (j (+ offset2 (memi (+ f start) st)))
                            (x st))))))
  ;; :rule-classes ((:rewrite :loop-stopper ((offset2 offset1 fwrite)))))


;; ===================================================================

;; A few more theorems about accessors and predicates of an fwrite.


;; An fwrite does not affect the number of fields.
(defthm num-fields-fwrite
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp offset f start st)
                ;; (sb60p v)
                )
           (equal (num-fields start (fwrite f offset v start st))
                  (num-fields start st))))

;; An fwrite does not change if a field if valid.
(defthm fieldp-fwrite
  (implies (and (farrayp start st)
                ;; (fieldp f1 start st)
                (fieldp f2 start st)
                (field-offsetp o2 f2 start st)
                ;; (sb60p v)
                )
           (equal (fieldp f1 start (fwrite f2 o2 v start st))
                  (fieldp f1 start st))))

;; An fwrite does not change if a field offset is valid.
(defthm field-offsetp-fwrite
  (implies (and (farrayp start st)
                (fieldp f1 start st)
                ;; (field-offsetp o1 f1 start st)
                (fieldp f2 start st)
                (field-offsetp o2 f2 start st)
                ;; (sb60p v)
                )
           (equal (field-offsetp o1 f1 start (fwrite f2 o2 v start st))
                  (field-offsetp o1 f1 start st))))




;; ============================ PRINTING =============================

;; This function can print the contents of an array in a stobj.  Specifically,
;; the array mem in stobj st.

(include-book "std/util/bstar" :dir :system)

(defun print-st1 (i max st)
  (declare (xargs :guard (and (integerp i)
                              (<= 0 i)
                              (< i (mem-len st))
                              (integerp max)
                              (<= 0 max)
                              (< max (mem-len st))
                              (<= i max))
                  :stobjs (st)
                  :measure (nfix (- max i))))
  (b* (((if (not (mbt (and (integerp i)
                           (<= 0 i)
                           (< i (mem-len st))
                           (integerp max)
                           (<= 0 max)
                           (< max (mem-len st))
                           (<= i max)))))
        nil)
       (- (cw "st[~p0] = ~p1~%" i (memi i st)))
       ((if (equal i max))
        t))
      (print-st1 (1+ i) max st)))

(defun print-st (st)
  (declare (xargs :stobjs (st)))
  (if (equal (mem-len st) 0)
      nil
    (print-st1 0 (- (mem-len st) 1) st)))

;; ============================== INIT ===============================

;; This function can write a list of 60-bit signed integers to a stobj.  This
;; is useful for easily initializing an farray.

(defun sb60-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (sb60p (car x))
         (sb60-listp (cdr x)))))

(defun write-list1 (i x st)
  (declare (xargs :guard (and (integerp i)
                              (<= 0 i)
                              (<= i (mem-len st))
                              (sb60-listp x))
                  :stobjs (st)
                  :measure (nfix (- (mem-len st) i))))
  (b* (((if (not (and (integerp i)
                      (<= 0 i)
                      (<= i (mem-len st))
                      (sb60-listp x))))
        st)
       ((if (equal i (mem-len st)))
        st)
       ((if (atom x))
        st)
       (st (!memi i (car x) st)))
      (write-list1 (1+ i) (cdr x) st)))

(defun write-list (x st)
  (declare (xargs :guard (sb60-listp x)
                  :stobjs (st)))
  (b* ((st (resize-mem (len x) st))
       ((if (equal (len x) 0))
        st)
       (st (write-list1 0 x st)))
      st))


;; ============================ DISABLES =============================

;; All theorems about farrays have been established.  All functions can now be
;; disabled.
(in-theory (disable farrayp num-fields fieldp flength field-offsetp fread fwrite))




;; ========================== FIELD-MEMBERP ==========================

;; The following function can be used to check or membership of an element
;; within a range of a field.  This is useful when a certain range of a field
;; corresponds to a list.

;; A value e is a member of the range from top to bottom in field f for an
;; farray at start in st.
(defun field-memberp (e top bottom f start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st)
                              (field-offsetp bottom f start st)
                              (or (field-offsetp top f start st)
                                  (equal top (1- bottom)))
                              (<= (1- bottom) top)
                              ;; (sb60p e)
                              )
                  :stobjs (st)
                  ;; Top decreases until is is below bottom.
                  :measure (nfix (- top (1- bottom)))))
  (if (not (mbt (and (farrayp start st)
                     (fieldp f start st)
                     (field-offsetp bottom f start st)
                     (or (field-offsetp top f start st)
                         (equal top (1- bottom)))
                     (<= (1- bottom) top)
                     ;; (sb60p e)
                     )))
      nil
    (if (equal top (1- bottom))
        nil
      (if (equal (fread f top start st) e)
          t
        (field-memberp e (1- top) bottom f start st)))))

;; ===================================================================

;; The field-memberp predicate has a rather complicated interaction with
;; fwrites to the farray.  Below, we break the interaction down by case analysis:
;; Case 1: fwrite to field different than field-memberp field
;; Case 2: fwrite to same field as field-memberp, but fwrite is out of bounds,
;;         below the range tested
;; Case 3: fwrite to same field as field-memberp, but fwrite is out of bounds,
;;         above the range tested
;; Case 4: fwrite is within the range tested by field-memberp, the value
;;         already present is written again
;; Case 5: fwrite is within the range tested by field-memberp, a different
;;         value is written, that value is the one tested for by field-memberp
;; Case 6: fwrite is within the range tested by field-memberp, a different
;;         value is written, that value is not the value tested for by
;;         field-memberp, the value overwritten is not the value tested by
;;         field-memberp
;; Case 7: fwrite is within the range tested by field-memberp, a different
;;         value is written, that value is not the value tested for by
;;         field-memberp, the value overwritten is the value tested by
;;         field-memberp



;; Case 1.  field-memberp of fwrite to different field
(defthm field-memberp-fwrite-diff-field
  (implies (and (not (equal f1 f2))
                (farrayp start st)
                ;; (fieldp f1 start st)
                ;; (field-offsetp o1-high f1 start st)
                ;; (field-offsetp o1-low f1 start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (fieldp f2 start st)
                (field-offsetp o2 f2 start st)
                (sb60p v2))
           (equal (field-memberp v1 o1-high o1-low f1 start (fwrite f2 o2 v2 start st))
                  (field-memberp v1 o1-high o1-low f1 start st))))

;; ;; < implies !=
;; ;; Would like to remove without adding arithmetic.
;; (local
;;  (defthm <-implies-not-equal
;;    (implies (< x y)
;;             (not (equal x y)))
;;    :rule-classes :forward-chaining))

;; ;; < transitive
;; ;; Would like to remove without adding arithmetic.
;; (local
;;  (defthm <-transitive-fc
;;    (implies (and (< x y)
;;                  (< y z))
;;             (< x z))
;;    :rule-classes :forward-chaining))

(defthm field-memberp-fread-fwrite-weird
  (implies (and (farrayp start st)
                (fieldp f start st)
                (field-offsetp o1-high f start st)
                (field-offsetp o1-low f start st)
                (field-offsetp o2 f start st)
                (sb60p v2)
                (<= o1-low o1-high)
                (not (equal o2 o1-high)))
           (field-memberp (fread f o1-high start st)
                          o1-high o1-low f start
                          (fwrite f o2 v2 start st))))

;; Case 2.  field-memberp of fwrite out of bounds below
(defthm field-memberp-fwrite-out-of-bounds-low
  (implies (and (< o2 o1-low)
                (farrayp start st)
                (fieldp f start st)
                ;; (field-offsetp o1-high f start st)
                ;; (field-offsetp o1-low f start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (field-offsetp o2 f start st)
                (sb60p v2))
           (equal (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))
                  (field-memberp v1 o1-high o1-low f start st))))

;; Case 3.  field-memberp of fwrite out of bounds above
(defthm field-memberp-fwrite-out-of-bounds-high
  (implies (and (< o1-high o2)
                (farrayp start st)
                (fieldp f start st)
                ;; (field-offsetp o1-high f start st)
                ;; (field-offsetp o1-low f start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (field-offsetp o2 f start st)
                (sb60p v2))
           (equal (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))
                  (field-memberp v1 o1-high o1-low f start st))))

;; Case 4.  field-memberp of fwrite to same value already present.
(defthm field-memberp-fwrite-same-value
  (implies (and (equal (fread f o2 start st) v2)
                (farrayp start st)
                (fieldp f start st)
                ;; (field-offsetp o1-high f start st)
                ;; (field-offsetp o1-low f start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (field-offsetp o2 f start st)
                (sb60p v2))
           (equal (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))
                  (field-memberp v1 o1-high o1-low f start st))))

;; Case 5.  field-memberp of fwrite where value written is value tested
(defthm field-memberp-fwrite-diff-value-is-elem
  (implies (and (not (equal (fread f o2 start st) v2))
                (equal v1 v2)
                (<= o1-low o2)
                (<= o2 o1-high)
                (farrayp start st)
                (fieldp f start st)
                (field-offsetp o1-high f start st)
                (field-offsetp o1-low f start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (field-offsetp o2 f start st)
                (sb60p v2))
           (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))))


;; Case 6.  field-memberp of fwrite where value written is different and not
;; value tested.
(defthm field-memberp-fwrite-diff-value-not-elem
  (implies (and ;; (not (equal (fread f o2 start st) v2))
                (not (equal v1 v2))
                (not (equal (fread f o2 start st) v1))
                ;; (<= o1-low o2)
                ;; (<= o2 o1-high)
                (farrayp start st)
                (fieldp f start st)
                ;; (field-offsetp o1-high f start st)
                ;; (field-offsetp o1-low f start st)
                ;; (<= o1-low o1-high)
                ;; (sb60p v1)
                (field-offsetp o2 f start st)
                (sb60p v2))
           (equal (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))
                  (field-memberp v1 o1-high o1-low f start st)))
  :hints (;; ("Subgoal *1/4'''"
          ;;  :use ((:instance field-memberp-fwrite-out-of-bounds-high
          ;;                   (o1-high (1- o1-high))
          ;;                   (o2 o1-high))))
          ("Subgoal *1/3''"
           :expand (field-memberp (fread f o1-high start st) o1-high o1-low f
                                  start (fwrite f o2 v2 start st)))))

;; (local
;;  (in-theory (disable <-implies-not-equal <-transitive-fc)))


;; Case 7.  field-memberp of fwrite where value written overwrites value tested
;; IN PROGRESS...

;; (defthm field-memberp-fwrite-diff-value-not-elem-overwrite-1
;;   (implies (and (field-memberp v1 o1-high (1+ o2) f start st)
;;                 (not (equal (fread f o2 start st) v2))
;;                 (not (equal v1 v2))
;;                 (equal (fread f o2 start st) v1)
;;                 (<= o1-low o2)
;;                 (<= o2 o1-high)
;;                 (farrayp start st)
;;                 (fieldp f start st)
;;                 (field-offsetp o1-high f start st)
;;                 (field-offsetp o1-low f start st)
;;                 (< o1-low o1-high)
;;                 (sb60p v1)
;;                 (field-offsetp o2 f start st)
;;                 (sb60p v2))
;;            (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))) )


;; (defthm field-memberp-fwrite-diff-value-not-elem-overwrite-2
;;   (implies (and (field-memberp v1 (1- o2) o1-low f start st)
;;                 (not (equal (fread f o2 start st) v2))
;;                 (not (equal v1 v2))
;;                 (equal (fread f o2 start st) v1)
;;                 (<= o1-low o2)
;;                 (<= o2 o1-high)
;;                 (farrayp start st)
;;                 (fieldp f start st)
;;                 (field-offsetp o1-high f start st)
;;                 (field-offsetp o1-low f start st)
;;                 (< o1-low o1-high)
;;                 (sb60p v1)
;;                 (field-offsetp o2 f start st)
;;                 (sb60p v2))
;;            (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st)))
;;   :hints (("Subgoal *1/6.2"
;;            :cases ((equal o2 o1-high)))))


;; (defthm field-memberp-fwrite-diff-value-not-elem-overwrite-3
;;   (implies (and (not (field-memberp v1 o1-high (1+ o2) f start st))
;;                 (not (field-memberp v1 (1- o2) o1-low f start st))
;;                 (not (equal (fread f o2 start st) v2))
;;                 (not (equal v1 v2))
;;                 (equal (fread f o2 start st) v1)
;;                 (<= o1-low o2)
;;                 (<= o2 o1-high)
;;                 (farrayp start st)
;;                 (fieldp f start st)
;;                 (field-offsetp o1-high f start st)
;;                 (field-offsetp o1-low f start st)
;;                 (< o1-low o1-high)
;;                 (sb60p v1)
;;                 (field-offsetp o2 f start st)
;;                 (sb60p v2))
;;            (not (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))) ))
;;   :hints (("Subgoal *1/6.2"
;;            :cases ((equal o2 o1-high)))))



;; (defthm field-memberp-fwrite-diff-value-not-elem-overwrite
;;   (implies (and (not (equal (fread f o2 start st) v2))
;;                 (not (equal v1 v2))
;;                 (equal (fread f o2 start st) v1)
;;                 (<= o1-low o2)
;;                 (<= o2 o1-high)
;;                 (farrayp start st)
;;                 (fieldp f start st)
;;                 (field-offsetp o1-high f start st)
;;                 (field-offsetp o1-low f start st)
;;                 (< o1-low o1-high)
;;                 (sb60p v1)
;;                 (field-offsetp o2 f start st)
;;                 (sb60p v2))
;;            (equal (field-memberp v1 o1-high o1-low f start (fwrite f o2 v2 start st))
;;                   (or (field-memberp v1 o1-high o2 f start st)
;;                       (field-memberp v1 o2 o1-low f start st))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :do-not-induct t)
;;           ("Subgoal 4'"
;;            :use ((:instance
;;                   field-memberp-fwrite-diff-value-not-elem-overwrite-1
;;                   (v1 (fread f o2 start st)))))))








;; ========================= EXAMPLE FARRAYS =========================

;; (defconst *a*
;;   '(0
;;     0
;;     0
;;     2
;;     7
;;     8
;;     11
;;     5
;;     1
;;     2
;;     3
;;     0
;;     0
;;     0
;;     0))

;; (farrayp 3 *a*)
;; (flength 1 3 *a*)
;; (flength 2 3 *a*)
;; (fread 1 0 3 *a*)
;; (fread 2 0 3 *a*)
;; (fread 2 1 3 *a*)
;; (fread 2 2 3 *a*)
;; (fwrite 2 2 10 3 *a*)


;; ===================================================================


;; (defconst *st-4*
;;   '(4  ;  0 - num-fields
;;     6  ;  1 - num-vars offset
;;     7  ;  2 - stack-end offset
;;     8  ;  3 - stack offset
;;     13 ;  4 - lookup offset
;;     23 ;  5 - end offset
;;     4  ;  6 - 0 - num-vars
;;     3  ;  7 - 0 - stack-end
;;     2  ;  8 - 0 - stack bottom
;;     4  ;  9 - 1
;;     7  ; 10 - 2
;;     0  ; 11 - 3
;;     0  ; 12 - 4 - padding
;;     0  ; 13 - 0 - lookup
;;     0  ; 14 - 1
;;     1  ; 15 - 2
;;     0  ; 16 - 3
;;     1  ; 17 - 4
;;     0  ; 18 - 5
;;     0  ; 19 - 6
;;     1  ; 20 - 7
;;     0  ; 21 - 8
;;     0  ; 22 - 9
;;     0  ; 23 - end
;;     ))


;; ===================================================================

;; (defconst *st-4-empty*
;;   '(4  ;  0 - num-fields
;;     6  ;  1 - num-vars offset
;;     7  ;  2 - stack-end offset
;;     8  ;  3 - stack offset
;;     13 ;  4 - lookup offset
;;     23 ;  5 - end offset
;;     4  ;  6 - 0 - num-vars
;;     0  ;  7 - 0 - stack-end
;;     0  ;  8 - 0 - stack bottom
;;     0  ;  9 - 1
;;     0  ; 10 - 2
;;     0  ; 11 - 3
;;     0  ; 12 - 4 - padding
;;     0  ; 13 - 0 - lookup
;;     0  ; 14 - 1
;;     0  ; 15 - 2
;;     0  ; 16 - 3
;;     0  ; 17 - 4
;;     0  ; 18 - 5
;;     0  ; 19 - 6
;;     0  ; 20 - 7
;;     0  ; 21 - 8
;;     0  ; 22 - 9
;;     0  ; 23 - end
;;     ))
