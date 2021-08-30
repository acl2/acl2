

(in-package "AIGNET")

(include-book "centaur/aignet/semantics" :dir :system)
(include-book "centaur/truth/sizes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "centaur/fty/bitstruct" :dir :system)

;; (include-book "std/stobjs/rewrites" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/util/termhints" :dir :system))

(local (acl2::use-trivial-ancestors-check))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable nth update-nth unsigned-byte-p
                           stobjs::range-nat-equiv-by-badguy-literal
                           stobjs::range-equal-by-badguy-literal)))

(local (in-theory (enable stobjs::nth-when-range-nat-equiv)))
(std::make-returnspec-config :hints-sub-returnnames t)

(defmacro defalias (x y)
  `(progn (defmacro ,x (&rest args) (cons ',y args))
          (table acl2::macro-aliases-table
                 ',x (or (cdr (assoc ',y (table-alist 'acl2::macro-aliases-table world)))
                         ',y))))

(defalias hq acl2::hq)
(defalias iff* acl2::iff*)
(defalias truth4-p truth::truth4-p)
(defalias truth4-fix truth::truth4-fix)
(defalias truth-norm truth::truth-norm)
(defalias truth-eval truth::truth-eval)
;; (defalias loghead acl2::loghead)
;; (defalias logtail acl2::logtail)
;; (defalias logcar acl2::logcar)
;; (defalias logcdr acl2::logcdr)
;; (defalias logcons acl2::logcons)
;; (defalias logbit acl2::logbit)
;; (defalias install-bit acl2::install-bit)
(defalias nth-set-bit-pos truth::nth-set-bit-pos)
(defalias range-nat-equiv stobjs::range-nat-equiv)


;; BOZO redundant
(defstobj-clone refcounts u32arr :prefix "REFCOUNTS-")




(local (defthmd nth-past-len
         (implies (<= (len x) (nfix n))
                  (equal (nth n x) nil))
         :hints(("Goal" :in-theory (enable nth)))))


(fty::defprod cuts4-config
  ((max-cuts posp :rule-classes :type-prescription
             :default 10
             "Maximum number of cuts to keep for each node"))
  :short "Configuration object for the 4-cut sweeping algorithm used in the aignet @(see rewrite) transform."
  :parents (rewrite rewrite-config)
  :layout :tree)



(define cutsize-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x 4))
  ///
  (defthm cutsize-p-compound-recognizer
    (implies (cutsize-p x)
             (natp x))
    :rule-classes :compound-recognizer)

  (defthm cutsize-p-implies-unsigned-byte-p
    (implies (cutsize-p x)
             (unsigned-byte-p 3 x)))

  (defthm cutsize-p-by-bound
    (implies (and (<= n 4)
                  (natp n))
             (cutsize-p n))))

(define cutsize-fix ((x cutsize-p))
  :prepwork ((local (in-theory (enable cutsize-p))))
  :returns (new-x cutsize-p :rule-classes (:rewrite (:type-prescription :typed-term new-x)))
  (mbe :logic (if (cutsize-p x) x 0)
       :exec x)
  ///
  (defret cutsize-fix-when-cutsize-p
    (implies (cutsize-p x)
             (equal new-x x)))

  (fty::deffixtype cutsize :pred cutsize-p :fix cutsize-fix :equiv cutsize-equiv
    :define t :forward t)

  (fty::fixtype-to-bitstruct cutsize :width 3))

(fty::fixtype-to-bitstruct truth::truth4 :width 16 :fullp t)

(fty::defbitstruct cutscore 12)

; Matt K. mod: Avoid ACL2(p) error from generated computed hint
; (FTY::BITSTRUCT-LOGBITP-REASONING), which returns an error triple.
(set-waterfall-parallelism nil)

(fty::defbitstruct cutinfo
  ((truth truth::truth4-p)
   (size cutsize-p)
   (valid booleanp)
   (score cutscore-p)))

(defthm cutinfo->size-bound
  (<= (cutinfo->size x) 4)
  :hints(("Goal" :use ((:instance cutsize-p
                        (x (cutinfo->size x))))))
  :rule-classes :linear)


(fty::deflist cutinfolist :elt-type cutinfo :true-listp t)

(defstobj cutsdb
  ;; Each cut-info entry corresponds to 4 entries in cut-leaves.
  ;; Nodecut-indices maps node IDs to cut-info ranges.
  ;; nodecut-indices[n] is the starting index of the cut data, so there needs
  ;; to be at least cut-nnodes+1 entries in nodecut-indices in order to track
  ;; the ending index of the last node.

  ;; If we decide we need to add nodes' cuts out of order, then we'll need an
  ;; additional mapping from AIG node indices to nodecut-indices entries.  But
  ;; for now we think we don't need that -- we'll be close enough to strict
  ;; order that we might as well just stay with that.
  (cut-info :type (array (and (unsigned-byte 32)
                              (satisfies cutinfo-p))
                         (0))
            :initially 0 :resizable t)
  (cut-leaves :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (nodecut-indices :type (array (unsigned-byte 32) (1)) :initially 0 :resizable t)
  ;; (node-table :type (array (unsigned-byte 32) (1)) :initially 0 :resizable t)
  (cut-nnodes :type (integer 0 *) :initially 0)
  :renaming ((cut-infoi cut-infoi1)
             (cut-leavesi cut-leavesi1)
             (nodecut-indicesi nodecut-indicesi1)
             ;; (node-tablei node-tablei1)
             (cut-nnodes cut-nnodes1))
  :inline t)

(defthm cut-infop-is-cutinfolist-p
  (equal (cut-infop x)
         (cutinfolist-p x)))

(defthm cut-leavesp-is-u32-listp
  (equal (cut-leavesp x)
         (acl2::u32-listp x)))

(defthm nodecut-indicesp-is-u32-listp
  (equal (nodecut-indicesp x)
         (acl2::u32-listp x)))

(local (in-theory (disable cut-infop cut-leavesp nodecut-indicesp)))



(defsection update-cut-infoi
  (defthm nth-of-update-cut-infoi
    (implies (not (equal (nfix n) *cut-infoi1*))
             (equal (nth n (update-cut-infoi i v cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-info-of-update-cut-infoi
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth n (nth *cut-infoi1* (update-cut-infoi i v cutsdb)))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  ;; (defthmd cut-info-of-update-cut-infoi
  ;;   (equal (nth *cut-infoi1* (update-cut-infoi n v cutsdb))
  ;;          (update-nth n v (nth *cut-infoi1* cutsdb))))

  (defthm nth-updated-index-of-update-cut-infoi
    (equal (nth n (nth *cut-infoi1* (update-cut-infoi n v cutsdb)))
           v))

  (defthm cut-infoi1-of-update-cut-infoi
    (equal (cut-infoi1 n (update-cut-infoi n v cutsdb))
           v))

  (defthm cut-info-length-of-update-cut-infoi
    (implies (< (nfix n) (cut-info-length cutsdb))
             (equal (cut-info-length (update-cut-infoi n v cutsdb))
                    (cut-info-length cutsdb))))

  (defthm cut-info-length-of-update-cut-infoi-greater
    (>= (cut-info-length (update-cut-infoi n v cutsdb))
        (cut-info-length cutsdb))
    :hints(("Goal" :in-theory (enable cut-info-length)))
    :rule-classes :linear)

  (defthm cut-info-length-of-update-cut-infoi-greater-than-index
    (> (cut-info-length (update-cut-infoi n v cutsdb))
       (nfix n))
    :hints(("Goal" :in-theory (enable cut-info-length)))
    :rule-classes :linear)

  (fty::deffixequiv update-cut-infoi :args ((acl2::i natp)))

  ;; (set-stobj-updater update-cut-infoi 2)
  (in-theory (disable update-cut-infoi)))

(defsection resize-cut-info
  (defthm nth-of-resize-cut-info
    (implies (not (equal (nfix n) *cut-infoi1*))
             (equal (nth n (resize-cut-info size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-info-of-resize-cut-info
    (implies (and (< (nfix n) (nfix size))
                  (< (nfix n) (cut-info-length cutsdb)))
             (equal (nth n (nth *cut-infoi1* (resize-cut-info size cutsdb)))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defthm nth-cut-info-of-resize-cut-info-grow
    (implies (<= (cut-info-length cutsdb) (nfix size))
             (cutinfo-equiv (nth n (nth *cut-infoi1* (resize-cut-info size cutsdb)))
                            (nth n (nth *cut-infoi1* cutsdb))))
    :hints(("Goal" :in-theory (enable nth-past-len))))

  ;; (defthmd cut-info-of-resize-cut-info
  ;;   (equal (nth *cut-infoi1* (resize-cut-info size cutsdb))
  ;;          (resize-list (nth *cut-infoi1* cutsdb) size 0)))

  (defthm cut-info-length-of-resize-cut-info
    (equal (cut-info-length (resize-cut-info size cutsdb))
           (nfix size)))

  (fty::deffixequiv resize-cut-info :args ((acl2::i natp)))

  ;; (set-stobj-updater resize-cut-info 1)
  (in-theory (disable resize-cut-info)))



(defsection cut-infoi1

  (def-updater-independence-thm cut-infoi1-updater-independence
    (implies (equal (nth n (nth *cut-infoi1* new))
                    (nth n (nth *cut-infoi1* old)))
             (equal (cut-infoi1 n new)
                    (cut-infoi1 n old))))

  (local (defthm cutinfo-p-of-nth
           (implies (and (cutinfolist-p x)
                         (< (nfix n) (len x)))
                    (cutinfo-p (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm natp-of-cut-infoi1
    (implies (and (cutinfolist-p (nth *cut-infoi1* cutsdb))
                  (< (nfix n) (cut-info-length cutsdb)))
             (cutinfo-p (cut-infoi1 n cutsdb)))
    :hints(("Goal" :in-theory (enable cut-info-length))))

  (fty::deffixequiv cut-infoi1 :args ((acl2::i natp)))

  (in-theory (disable cut-infoi1)))

(defsection cut-info-length
  (def-updater-independence-thm cut-info-length-updater-independence
    (implies (equal (len (nth *cut-infoi1* new))
                    (len (nth *cut-infoi1* old)))
             (equal (cut-info-length new)
                    (cut-info-length old))))

  (in-theory (disable cut-info-length)))

(define cut-infoi ((n natp) cutsdb)
  :returns (entry cutinfo-p :rule-classes (:rewrite (:type-prescription :typed-term entry)))
  :guard (< n (cut-info-length cutsdb))
  :inline t
  :prepwork ((local (in-theory (enable acl2::nth-in-u32-listp-natp))))
  (cutinfo-fix (cut-infoi1 n cutsdb))
  ///
  (def-updater-independence-thm cut-infoi-updater-independence
    (implies (cutinfo-equiv (nth n (nth *cut-infoi1* new))
                            (nth n (nth *cut-infoi1* old)))
             (equal (cut-infoi n new)
                    (cut-infoi n old)))
    :hints(("Goal" :in-theory (enable cut-infoi1))))

  (defthm cut-infoi-of-update-cut-info
    (equal (cut-infoi n (update-cut-infoi n v cutsdb))
           (cutinfo-fix v))))




(defsection update-cut-leavesi
  (defthm nth-of-update-cut-leavesi
    (implies (not (equal (nfix n) *cut-leavesi1*))
             (equal (nth n (update-cut-leavesi i v cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-leaves-of-update-cut-leavesi
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth n (nth *cut-leavesi1* (update-cut-leavesi i v cutsdb)))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  ;; (defthmd cut-leaves-of-update-cut-leavesi
  ;;   (equal (nth *cut-leavesi1* (update-cut-leavesi n v cutsdb))
  ;;          (update-nth n v (nth *cut-leavesi1* cutsdb))))

  (defthm nth-updated-index-of-update-cut-leavesi
    (equal (nth n (nth *cut-leavesi1* (update-cut-leavesi n v cutsdb)))
           v))

  (defthm cut-leavesi1-of-update-cut-leavesi
    (equal (cut-leavesi1 n (update-cut-leavesi n v cutsdb))
           v))

  (defthm cut-leaves-length-of-update-cut-leavesi
    (implies (< (nfix n) (cut-leaves-length cutsdb))
             (equal (cut-leaves-length (update-cut-leavesi n v cutsdb))
                    (cut-leaves-length cutsdb))))

  (defthm cut-leaves-length-of-update-cut-leavesi-greater
    (>= (cut-leaves-length (update-cut-leavesi n v cutsdb))
        (cut-leaves-length cutsdb))
    :hints(("Goal" :in-theory (enable cut-leaves-length)))
    :rule-classes :linear)

  (defthm cut-leaves-length-of-update-cut-leavesi-greater-than-index
    (> (cut-leaves-length (update-cut-leavesi n v cutsdb))
       (nfix n))
    :hints(("Goal" :in-theory (enable cut-leaves-length)))
    :rule-classes :linear)

  (fty::deffixequiv update-cut-leavesi :args ((acl2::i natp)))

  ;; (set-stobj-updater update-cut-leavesi 2)
  (in-theory (disable update-cut-leavesi)))

(defsection resize-cut-leaves
  (defthm nth-of-resize-cut-leaves
    (implies (not (equal (nfix n) *cut-leavesi1*))
             (equal (nth n (resize-cut-leaves size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-leaves-of-resize-cut-leaves
    (implies (and (< (nfix n) (nfix size))
                  (< (nfix n) (cut-leaves-length cutsdb)))
             (equal (nth n (nth *cut-leavesi1* (resize-cut-leaves size cutsdb)))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defthm nth-cut-leaves-of-resize-cut-leaves-grow
    (implies (<= (cut-leaves-length cutsdb) (nfix size))
             (nat-equiv (nth n (nth *cut-leavesi1* (resize-cut-leaves size cutsdb)))
                        (nth n (nth *cut-leavesi1* cutsdb))))
    :hints(("Goal" :in-theory (enable nth-past-len))))

  ;; (defthmd cut-leaves-of-resize-cut-leaves
  ;;   (equal (nth *cut-leavesi1* (resize-cut-leaves size cutsdb))
  ;;          (resize-list (nth *cut-leavesi1* cutsdb) size 0)))

  (defthm cut-leaves-length-of-resize-cut-leaves
    (equal (cut-leaves-length (resize-cut-leaves size cutsdb))
           (nfix size)))

  (fty::deffixequiv resize-cut-leaves :args ((acl2::i natp)))

  ;; (set-stobj-updater resize-cut-leaves 1)
  (in-theory (disable resize-cut-leaves)))



(defsection cut-leavesi1

  (def-updater-independence-thm cut-leavesi1-updater-independence
    (implies (equal (nth n (nth *cut-leavesi1* new))
                    (nth n (nth *cut-leavesi1* old)))
             (equal (cut-leavesi1 n new)
                    (cut-leavesi1 n old))))

  (defthm natp-of-cut-leavesi1
    (implies (and (acl2::u32-listp (nth *cut-leavesi1* cutsdb))
                  (< (nfix n) (cut-leaves-length cutsdb)))
             (natp (cut-leavesi1 n cutsdb)))
    :hints(("Goal" :in-theory (enable cut-leaves-length))))

  (fty::deffixequiv cut-leavesi1 :args ((acl2::i natp)))

  (in-theory (disable cut-leavesi1)))

(defsection cut-leaves-length
  (def-updater-independence-thm cut-leaves-length-updater-independence
    (implies (equal (len (nth *cut-leavesi1* new))
                    (len (nth *cut-leavesi1* old)))
             (equal (cut-leaves-length new)
                    (cut-leaves-length old))))

  (in-theory (disable cut-leaves-length)))

(define cut-leavesi ((n natp) cutsdb)
  :returns (entry natp :rule-classes :type-prescription)
  :guard (< n (cut-leaves-length cutsdb))
  :inline t
  :prepwork ((local (in-theory (enable acl2::nth-in-u32-listp-natp))))
  (lnfix (cut-leavesi1 n cutsdb))
  ///
  (def-updater-independence-thm cut-leavesi-updater-independence
    (implies (nat-equiv (nth n (nth *cut-leavesi1* new))
                        (nth n (nth *cut-leavesi1* old)))
             (equal (cut-leavesi n new)
                    (cut-leavesi n old)))
    :hints(("Goal" :in-theory (enable cut-leavesi1))))

  (defthm cut-leavesi-of-update-cut-leaves
    (equal (cut-leavesi n (update-cut-leavesi n v cutsdb))
           (nfix v))))





(defsection update-nodecut-indicesi
  (defthm nth-of-update-nodecut-indicesi
    (implies (not (equal (nfix n) *nodecut-indicesi1*))
             (equal (nth n (update-nodecut-indicesi i v cutsdb))
                    (nth n cutsdb))))

  (defthm nth-nodecut-indices-of-update-nodecut-indicesi
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth n (nth *nodecut-indicesi1* (update-nodecut-indicesi i v cutsdb)))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (defthmd nodecut-indices-of-update-nodecut-indicesi
  ;;   (equal (nth *nodecut-indicesi1* (update-nodecut-indicesi n v cutsdb))
  ;;          (update-nth n v (nth *nodecut-indicesi1* cutsdb))))

  (defthm nth-updated-index-of-update-nodecut-indicesi
    (equal (nth n (nth *nodecut-indicesi1* (update-nodecut-indicesi n v cutsdb)))
           v))

  (defthm nodecut-indicesi1-of-update-nodecut-indicesi
    (equal (nodecut-indicesi1 n (update-nodecut-indicesi n v cutsdb))
           v))

  (defthm nodecut-indices-length-of-update-nodecut-indicesi
    (implies (< (nfix n) (nodecut-indices-length cutsdb))
             (equal (nodecut-indices-length (update-nodecut-indicesi n v cutsdb))
                    (nodecut-indices-length cutsdb))))

  (defthm nodecut-indices-length-of-update-nodecut-indicesi-greater
    (>= (nodecut-indices-length (update-nodecut-indicesi n v cutsdb))
        (nodecut-indices-length cutsdb))
    :rule-classes :linear)

  (defthm nodecut-indices-length-of-update-nodecut-indicesi-greater-than-index
    (> (nodecut-indices-length (update-nodecut-indicesi n v cutsdb))
       (nfix n))
    :hints(("Goal" :in-theory (enable nodecut-indices-length)))
    :rule-classes :linear)

  (fty::deffixequiv update-nodecut-indicesi :args ((acl2::i natp)))

  ;; (set-stobj-updater update-nodecut-indicesi 2)
  (in-theory (disable update-nodecut-indicesi)))

(defsection resize-nodecut-indices
  (defthm nth-of-resize-nodecut-indices
    (implies (not (equal (nfix n) *nodecut-indicesi1*))
             (equal (nth n (resize-nodecut-indices size cutsdb))
                    (nth n cutsdb))))

  ;; (defthmd nodecut-indices-of-resize-nodecut-indicesi
  ;;   (equal (nth *nodecut-indicesi1* (resize-nodecut-indices size cutsdb))
  ;;          (resize-list (nth *nodecut-indicesi1* cutsdb) size 0)))

  (defthm nth-nodecut-indices-of-resize-nodecut-indices
    (implies (and (< (nfix n) (nfix size))
                  (< (nfix n) (nodecut-indices-length cutsdb)))
             (equal (nth n (nth *nodecut-indicesi1* (resize-nodecut-indices size cutsdb)))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defthm nth-nodecut-indices-of-resize-nodecut-indices-grow
    (implies (<= (nodecut-indices-length cutsdb) (nfix size))
             (nat-equiv (nth n (nth *nodecut-indicesi1* (resize-nodecut-indices size cutsdb)))
                        (nth n (nth *nodecut-indicesi1* cutsdb))))
    :hints(("Goal" :in-theory (enable nth-past-len))))

  (defthm nodecut-indices-length-of-resize-nodecut-indices
    (equal (nodecut-indices-length (resize-nodecut-indices size cutsdb))
           (nfix size)))

  (fty::deffixequiv resize-nodecut-indices :args ((acl2::i natp)))

  ;; (set-stobj-updater resize-nodecut-indices 1)
  (in-theory (disable resize-nodecut-indices)))

(defsection nodecut-indicesi1

  (def-updater-independence-thm nodecut-indicesi1-updater-independence
    (implies (equal (nth n (nth *nodecut-indicesi1* new))
                    (nth n (nth *nodecut-indicesi1* old)))
             (equal (nodecut-indicesi1 n new)
                    (nodecut-indicesi1 n old))))

  (defthm natp-of-nodecut-indicesi1
    (implies (and (acl2::u32-listp (nth *nodecut-indicesi1* cutsdb))
                  (< (nfix n) (nodecut-indices-length cutsdb)))
             (natp (nodecut-indicesi1 n cutsdb)))
    :hints(("Goal" :in-theory (enable nodecut-indices-length))))

  (fty::deffixequiv nodecut-indicesi1 :args ((acl2::i natp)))

  (in-theory (disable nodecut-indicesi1)))

(defsection nodecut-indices-length
  (def-updater-independence-thm nodecut-indices-length-updater-independence
    (implies (equal (len (nth *nodecut-indicesi1* new))
                    (len (nth *nodecut-indicesi1* old)))
             (equal (nodecut-indices-length new)
                    (nodecut-indices-length old))))

  (in-theory (disable nodecut-indices-length)))

(define nodecut-indicesi ((n natp) cutsdb)
  :returns (entry natp :rule-classes :type-prescription)
  :guard (< n (nodecut-indices-length cutsdb))
  :inline t
  :prepwork ((local (in-theory (enable acl2::nth-in-u32-listp-natp))))
  (lnfix (nodecut-indicesi1 n cutsdb))
  ///

  (def-updater-independence-thm nodecut-indicesi-updater-independence
    (implies (nat-equiv (nth n (nth *nodecut-indicesi1* new))
                        (nth n (nth *nodecut-indicesi1* old)))
             (equal (nodecut-indicesi n new)
                    (nodecut-indicesi n old)))
    :hints(("Goal" :in-theory (enable nodecut-indicesi1))))

  (local (include-book "std/lists/nth" :dir :system))

  (defthm nodecut-indicesi-of-update-nodecut-indices
    (equal (nodecut-indicesi n (update-nodecut-indicesi n v cutsdb))
           (nfix v)))

  (defret size-of-nodecut-indicesi
    (implies (cutsdbp cutsdb)
             (unsigned-byte-p 32 entry))
    :hints(("Goal" :in-theory (enable cutsdbp nodecut-indicesi1
                                      nodecut-indices-length
                                      acl2::nth-in-u32-listp-natp
                                      acl2::nth-in-u32-listp-u32p
                                      ;; acl2::nth-when-too-large
                                      )
            :cases ((< (nfix n) (nodecut-indices-length cutsdb)))
            :do-not-induct t))))


(defsection update-cut-nnodes
  (defthm nth-of-update-cut-nnodes
    (implies (not (equal (nfix n) *cut-nnodes1*))
             (equal (nth n (update-cut-nnodes v cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-nnodes1-of-update-cut-nnodes
    (equal (nth *cut-nnodes1* (update-cut-nnodes v cutsdb))
           v))

  (defthm cut-nnodes1-of-update-cut-nnodes
    (equal (cut-nnodes1 (update-cut-nnodes v cutsdb))
           v))

  ;; (set-stobj-updater update-cut-nnodes 1)
  (in-theory (disable update-cut-nnodes)))

(defsection cut-nnodes1
  (def-updater-independence-thm cut-nnodes1-updater-independence
    (implies (equal (nth *cut-nnodes1* new)
                    (nth *cut-nnodes1* old))
             (equal (cut-nnodes1 new)
                    (cut-nnodes1 old))))

  (defthm natp-of-cut-nnodes1
    (implies (natp (nth *cut-nnodes1* cutsdb))
             (natp (cut-nnodes1 cutsdb))))

  (in-theory (disable cut-nnodes1)))

(define cut-nnodes (cutsdb)
  :returns (entry natp :rule-classes :type-prescription)
  :inline t
  (lnfix (cut-nnodes1 cutsdb))
  ///
  (def-updater-independence-thm cut-nnodes-updater-independence
    (implies (nat-equiv (nth *cut-nnodes1* new)
                        (nth *cut-nnodes1* old))
             (equal (cut-nnodes new)
                    (cut-nnodes old)))
    :hints(("Goal" :in-theory (enable cut-nnodes1))))

  (defthm cut-nnodes-of-update-cut-nnodes
    (equal (cut-nnodes (update-cut-nnodes n cutsdb))
           (nfix n))))

;; (stobjs::def-stobj-meta-rules cutsdb
;;   :simple-accs (cut-nnodes nth)
;;   :array-accs (nodecut-indicesi cut-leavesi nth))

(local (in-theory (disable cutsdbp)))

(encapsulate nil
  ;; make sure our updater independence theory works
  (local (defthmd cut-nnodes-of-update-cut-leavesi
           (equal (cut-nnodes (update-cut-leavesi i val cut-leaves))
                  (cut-nnodes cut-leaves)))))




;; Same as range-equal/range-equal-badguy but compares corresponding elements
;; with cutinfo-equiv.
(define range-cutinfo-equiv ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  (if (zp num)
      t
    (and (ec-call (cutinfo-equiv (nth start x) (nth start y)))
         (range-cutinfo-equiv (1+ (lnfix start)) (1- num) x y)))
  ///
  (defthmd range-cutinfo-equiv-open
    (implies (not (zp num))
             (equal (range-cutinfo-equiv start num x y)
                    (and (cutinfo-equiv (nth start x) (nth start y))
                         (range-cutinfo-equiv (1+ (lnfix start)) (1- num) x y)))))

  (local (defthm nth-of-list-fix
           (equal (nth n (acl2::list-fix x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nth acl2::list-fix)))))

  (fty::deffixequiv range-cutinfo-equiv)

  (local (defthm range-cutinfo-equiv-when-greater-num-lemma
           (implies (range-cutinfo-equiv start (+ (nfix num2) (nfix n)) x y)
                    (range-cutinfo-equiv start num2 x y))
           :rule-classes nil))

  (defthm range-cutinfo-equiv-when-greater-num
    (implies (and (range-cutinfo-equiv start num x y)
                  (syntaxp (not (equal num num2)))
                  (<= (nfix num2) (nfix num)))
             (range-cutinfo-equiv start num2 x y))
    :hints (("goal" :use ((:instance range-cutinfo-equiv-when-greater-num-lemma
                           (num2 num2) (n (- (nfix num) (nfix num2))))))))

  (defthm range-cutinfo-equiv-when-superrange
    (implies (and (range-cutinfo-equiv start num x y)
                  (syntaxp (not (and (equal start start2)
                                     (equal num num2))))
                  (<= (nfix start) (nfix start2))
                  (<= (+ (nfix num2) (nfix start2)) (+ (nfix num) (nfix start))))
             (range-cutinfo-equiv start2 num2 x y))
    :hints (("goal" :induct (range-cutinfo-equiv start num x y)
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (and stable-under-simplificationp
                 '(:expand ((range-cutinfo-equiv start num2 x y))))))

  (defthmd nth-when-range-cutinfo-equiv
    (implies (and (range-cutinfo-equiv start num x y)
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix num))))
             (cutinfo-equiv (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm range-cutinfo-equiv-self
    (range-cutinfo-equiv start num x x))


  (defthm range-cutinfo-equiv-of-update-out-of-range-1
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-cutinfo-equiv start num (update-nth n v x) y)
                    (range-cutinfo-equiv start num x y))))

  (defthm range-cutinfo-equiv-of-update-out-of-range-2
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-cutinfo-equiv start num x (update-nth n v y))
                    (range-cutinfo-equiv start num x y))))

  (defthm range-cutinfo-equiv-of-empty
    (range-cutinfo-equiv start 0 x y)))


(define range-cutinfo-equiv-badguy ((start natp) (num natp) (x true-listp) (y true-listp))
  :measure (nfix num)
  :returns (badguy natp :rule-classes :type-prescription)
  (if (or (zp num) (eql num 1))
      (nfix start)
    (if (ec-call (cutinfo-equiv (nth start x) (nth start y)))
        (range-cutinfo-equiv-badguy (1+ (lnfix start)) (1- num) x y)
      (nfix start)))
  ///
  (local (in-theory (enable range-cutinfo-equiv)))
  (defret range-cutinfo-equiv-badguy-lower-bound
    (<= (nfix start) badguy)
    :rule-classes :linear)

  (defret range-cutinfo-equiv-badguy-lower-bound-rewrite
    (implies (<= start1 (nfix start))
             (<= start1 badguy)))

  (defret range-cutinfo-equiv-badguy-lower-bound-not-equal
    (implies (< start1 (nfix start))
             (not (equal start1 badguy))))

  (defret range-cutinfo-equiv-badguy-upper-bound
    (implies (posp num)
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes :linear)

  (defret range-cutinfo-equiv-badguy-upper-bound-when-not-equal
    (implies (not (range-cutinfo-equiv start num x y))
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-cutinfo-equiv-badguy-upper-bound-when-not-equal-rewrite
    (implies (and (not (range-cutinfo-equiv start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (< badguy foo))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-cutinfo-equiv-badguy-not-equal-past-upper-bound
    (implies (and (not (range-cutinfo-equiv start num x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (not (equal badguy foo)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-cutinfo-equiv-by-badguy
    (implies (cutinfo-equiv (nth badguy x) (nth badguy y))
             (range-cutinfo-equiv start num x y)))

  (defretd range-cutinfo-equiv-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-cutinfo-equiv ,start ,num ,x ,y))
             (iff (range-cutinfo-equiv start num x y)
                  (or (not (< badguy (+ (nfix start) (nfix num))))
                      (cutinfo-equiv (nth badguy x) (nth badguy y)))))))



(defthm range-cutinfo-equiv-when-range-cutinfo-equiv
  (implies (range-cutinfo-equiv start num x y)
           (range-cutinfo-equiv start num x y)))




(local
 (defsection cutinfo-equiv-under-mask-thms
   (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

   (defthm cutinfo-equiv-under-mask-self
     (cutinfo-equiv-under-mask x x mask)
     :hints(("Goal" :in-theory (enable cutinfo-equiv-under-mask
                                       fty::int-equiv-under-mask))))

   (defthm cutinfo-equiv-under-mask-by-larger-mask
     (implies (and (cutinfo-equiv-under-mask x y mask)
                   (equal (logand (lognot mask) mask1) 0))
              (cutinfo-equiv-under-mask x y mask1))
     :hints(("Goal" :in-theory (enable cutinfo-equiv-under-mask
                                       fty::int-equiv-under-mask))
            (bitops::logbitp-reasoning)))

   (defthmd cutinfo-equiv-under-mask-commutative
     (implies (cutinfo-equiv-under-mask x y mask)
              (cutinfo-equiv-under-mask y x mask))
     :hints(("Goal" :in-theory (enable cutinfo-equiv-under-mask
                                       fty::int-equiv-under-mask))))

   (defthmd cutinfo-equiv-under-mask-transitive
     (implies (and (cutinfo-equiv-under-mask x y mask)
                   (cutinfo-equiv-under-mask y z mask))
              (cutinfo-equiv-under-mask x z mask))
     :hints(("Goal" :in-theory (enable cutinfo-equiv-under-mask
                                       fty::int-equiv-under-mask))
            (bitops::logbitp-reasoning)))

   (defthmd cutinfo-equiv-under-mask-transitive2
     (implies (and (cutinfo-equiv-under-mask y z mask)
                   (cutinfo-equiv-under-mask x y mask))
              (cutinfo-equiv-under-mask x z mask))
     :hints(("Goal" :in-theory (enable cutinfo-equiv-under-mask-transitive))))

   (defthm cutinfo-equiv-under-mask-reduce-1
     (implies (and (fty::bitstruct-read-over-write-hyps x cutinfo-equiv-under-mask
                                                        :mask-var mask :y-var y)
                   (cutinfo-equiv-under-mask x y mask)
                   (equal (logand (lognot mask) mask1) 0))
              (equal (cutinfo-equiv-under-mask x z mask1)
                     (cutinfo-equiv-under-mask y z mask1)))
     :hints (("goal" :use cutinfo-equiv-under-mask-by-larger-mask
              :cases ((cutinfo-equiv-under-mask x z mask1))
              :in-theory (e/d (cutinfo-equiv-under-mask-transitive
                               cutinfo-equiv-under-mask-transitive2
                               cutinfo-equiv-under-mask-commutative)
                              (cutinfo-equiv-under-mask-by-larger-mask)))))

   (defthm cutinfo-equiv-under-mask-reduce-2
     (implies (and (fty::bitstruct-read-over-write-hyps x cutinfo-equiv-under-mask
                                                        :mask-var mask :y-var y)
                   (cutinfo-equiv-under-mask x y mask)
                   (equal (logand (lognot mask) mask1) 0))
              (equal (cutinfo-equiv-under-mask z x mask1)
                     (cutinfo-equiv-under-mask z y mask1)))
     :hints (("goal" :use cutinfo-equiv-under-mask-by-larger-mask
              :cases ((cutinfo-equiv-under-mask z x mask1))
              :in-theory (e/d (cutinfo-equiv-under-mask-transitive
                               cutinfo-equiv-under-mask-transitive2
                               cutinfo-equiv-under-mask-commutative)
                              (cutinfo-equiv-under-mask-by-larger-mask)))))

   (def-updater-independence-thm cutinfo->size-updater-independence
     (implies (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                        (nth n (nth *cut-infoi1* old))
                                        #x70000)
              (equal (cutinfo->size (cut-infoi n new))
                     (cutinfo->size (cut-infoi n old))))
     :hints(("Goal" :in-theory (enable cut-infoi cut-infoi1)
             :use ((:instance cutinfo->size-of-write-with-mask
                    (x (cut-infoi n new))
                    (y (cut-infoi n old))
                    (mask #x70000))))))

   (def-updater-independence-thm cutinfo->truth-updater-independence
     (implies (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                        (nth n (nth *cut-infoi1* old))
                                        #xffff)
              (equal (cutinfo->truth (cut-infoi n new))
                     (cutinfo->truth (cut-infoi n old))))
     :hints(("Goal" :in-theory (enable cut-infoi cut-infoi1)
             :use ((:instance cutinfo->truth-of-write-with-mask
                    (x (cut-infoi n new))
                    (y (cut-infoi n old))
                    (mask #xffff))))))

   (def-updater-independence-thm cutinfo->valid-updater-independence
     (implies (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                        (nth n (nth *cut-infoi1* old))
                                        #x80000)
              (equal (cutinfo->valid (cut-infoi n new))
                     (cutinfo->valid (cut-infoi n old))))
     :hints(("Goal" :in-theory (enable cut-infoi cut-infoi1)
             :use ((:instance cutinfo->valid-of-write-with-mask
                    (x (cut-infoi n new))
                    (y (cut-infoi n old))
                    (mask #x80000))))))

   (def-updater-independence-thm cutinfo->score-updater-independence
     (implies (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                        (nth n (nth *cut-infoi1* old))
                                        #xfff00000)
              (equal (cutinfo->score (cut-infoi n new))
                     (cutinfo->score (cut-infoi n old))))
     :hints(("Goal" :in-theory (enable cut-infoi cut-infoi1)
             :use ((:instance cutinfo->score-of-write-with-mask
                    (x (cut-infoi n new))
                    (y (cut-infoi n old))
                    (mask #xfff00000))))))))


;; Same as range-equal/range-equal-badguy but compares corresponding elements
;; with cutinfo-equiv under a bitmask.
(define range-cutinfo-equiv-under-mask ((start natp) (num natp) (mask integerp)
                             (x true-listp) (y true-listp))
  :measure (nfix num)
  (if (zp num)
      t
    (and (ec-call (cutinfo-equiv-under-mask (nth start x) (nth start y) mask))
         (range-cutinfo-equiv-under-mask (1+ (lnfix start)) (1- num) mask x y)))
  ///
  (defthmd range-cutinfo-equiv-under-mask-open
    (implies (not (zp num))
             (equal (range-cutinfo-equiv-under-mask start num mask x y)
                    (and (cutinfo-equiv-under-mask (nth start x) (nth start y) mask)
                         (range-cutinfo-equiv-under-mask (1+ (lnfix start)) (1- num) mask x y)))))

  (local (defthm nth-of-list-fix
           (equal (nth n (acl2::list-fix x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nth acl2::list-fix)))))

  (fty::deffixequiv range-cutinfo-equiv-under-mask)

  (local (defthm range-cutinfo-equiv-under-mask-when-greater-num-lemma
           (implies (And (range-cutinfo-equiv-under-mask start (+ (nfix num2) (nfix n)) mask x y)
                         (equal (logand mask2 (lognot mask)) 0))
                    (range-cutinfo-equiv-under-mask start num2 mask2 x y))
           :hints (("goal" :induct (range-cutinfo-equiv-under-mask start num2 mask2 x y)
                    :expand ((:free (end)
                              (range-cutinfo-equiv-under-mask start end mask x y)))))
           :rule-classes nil))

  (local (defthm range-cutinfo-equiv-under-mask-when-greater-num/mask
           (implies (and (range-cutinfo-equiv-under-mask start num mask x y)
                         (syntaxp (not (equal num num2)))
                         (<= (nfix num2) (nfix num))
                         (equal (logand mask2 (lognot mask)) 0))
                    (range-cutinfo-equiv-under-mask start num2 mask2 x y))
           :hints (("goal" :use ((:instance range-cutinfo-equiv-under-mask-when-greater-num-lemma
                                  (num2 num2) (n (- (nfix num) (nfix num2)))))))))

  (defthm range-cutinfo-equiv-under-mask-when-superrange
    (implies (and (range-cutinfo-equiv-under-mask start num mask x y)
                  (syntaxp (not (and (equal start start2)
                                     (equal num num2)
                                     (equal mask mask2))))
                  (<= (nfix start) (nfix start2))
                  (<= (+ (nfix num2) (nfix start2)) (+ (nfix num) (nfix start)))
                  (equal (logand mask2 (lognot mask)) 0))
             (range-cutinfo-equiv-under-mask start2 num2 mask2 x y))
    :hints (("goal" :induct (range-cutinfo-equiv-under-mask start num mask x y)
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (and stable-under-simplificationp
                 '(:expand ((range-cutinfo-equiv-under-mask start num2 mask2 x y))))))

  (defthmd nth-when-range-cutinfo-equiv-under-mask
    (implies (and (range-cutinfo-equiv-under-mask start num mask x y)
                  (<= (nfix start) (nfix n))
                  (< (nfix n) (+ (nfix start) (nfix num)))
                  (equal (logand mask1 (lognot mask)) 0))
             (cutinfo-equiv-under-mask (nth n x) (nth n y) mask1))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm range-cutinfo-equiv-under-mask-self
    (range-cutinfo-equiv-under-mask start num mask x x))


  (defthm range-cutinfo-equiv-under-mask-of-update-out-of-range-1
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-cutinfo-equiv-under-mask start num mask (update-nth n v x) y)
                    (range-cutinfo-equiv-under-mask start num mask x y))))

  (defthm range-cutinfo-equiv-under-mask-of-update-out-of-range-2
    (implies (not (and (<= (nfix start) (nfix n))
                       (< (nfix n) (+ (nfix start) (nfix num)))))
             (equal (range-cutinfo-equiv-under-mask start num mask x (update-nth n v y))
                    (range-cutinfo-equiv-under-mask start num mask x y))))

  (defthm range-cutinfo-equiv-under-mask-of-update-bitfield-1
    (implies (cutinfo-equiv-under-mask v (nth n x) mask)
             (equal (range-cutinfo-equiv-under-mask start num mask (update-nth n v x) y)
                    (range-cutinfo-equiv-under-mask start num mask x y)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
                                       cutinfo-equiv-under-mask-transitive2
                                       cutinfo-equiv-under-mask-commutative))))

  (defthm range-cutinfo-equiv-under-mask-of-update-bitfield-2
    (implies (cutinfo-equiv-under-mask v (nth n y) mask)
             (equal (range-cutinfo-equiv-under-mask start num mask x (update-nth n v y))
                    (range-cutinfo-equiv-under-mask start num mask x y)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
                                       cutinfo-equiv-under-mask-transitive
                                       cutinfo-equiv-under-mask-commutative))))


  (defthm range-cutinfo-equiv-under-mask-of-empty
    (range-cutinfo-equiv-under-mask start 0 mask x y)))


(define range-cutinfo-equiv-under-mask-badguy ((start natp) (num natp) (mask integerp) (x true-listp) (y true-listp))
  :measure (nfix num)
  :returns (badguy natp :rule-classes :type-prescription)
  (if (or (zp num) (eql num 1))
      (nfix start)
    (if (ec-call (cutinfo-equiv-under-mask (nth start x) (nth start y) mask))
        (range-cutinfo-equiv-under-mask-badguy (1+ (lnfix start)) (1- num) mask x y)
      (nfix start)))
  ///
  (local (in-theory (enable range-cutinfo-equiv-under-mask)))
  (defret range-cutinfo-equiv-under-mask-badguy-lower-bound
    (<= (nfix start) badguy)
    :rule-classes :linear)

  (defret range-cutinfo-equiv-under-mask-badguy-lower-bound-rewrite
    (implies (<= start1 (nfix start))
             (<= start1 badguy)))

  (defret range-cutinfo-equiv-under-mask-badguy-lower-bound-not-equal
    (implies (< start1 (nfix start))
             (not (equal start1 badguy))))

  (defret range-cutinfo-equiv-under-mask-badguy-upper-bound
    (implies (posp num)
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes :linear)

  (defret range-cutinfo-equiv-under-mask-badguy-upper-bound-when-not-equal
    (implies (not (range-cutinfo-equiv-under-mask start num mask x y))
             (< badguy (+ (nfix start) (nfix num))))
    :rule-classes ((:linear :backchain-limit-lst 0)))

  (defret range-cutinfo-equiv-under-mask-badguy-upper-bound-when-not-equal-rewrite
    (implies (and (not (range-cutinfo-equiv-under-mask start num mask x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (< badguy foo))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-cutinfo-equiv-under-mask-badguy-not-equal-past-upper-bound
    (implies (and (not (range-cutinfo-equiv-under-mask start num mask x y))
                  (<= (+ (nfix start) (nfix num)) foo))
             (not (equal badguy foo)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defret range-cutinfo-equiv-under-mask-by-badguy
    (implies (cutinfo-equiv-under-mask (nth badguy x) (nth badguy y) mask)
             (range-cutinfo-equiv-under-mask start num mask x y)))

  (defretd range-cutinfo-equiv-under-mask-by-badguy-literal
    (implies (acl2::rewriting-positive-literal `(range-cutinfo-equiv-under-mask ,start ,num ,mask ,x ,y))
             (iff (range-cutinfo-equiv-under-mask start num mask x y)
                  (or (not (< badguy (+ (nfix start) (nfix num))))
                      (cutinfo-equiv-under-mask (nth badguy x) (nth badguy y) mask))))))



(defthm range-cutinfo-equiv-under-mask-when-range-cutinfo-equiv-under-mask
  (implies (range-cutinfo-equiv-under-mask start num mask x y)
           (range-cutinfo-equiv-under-mask start num mask x y)))






(define leaves-sorted ((idx natp)
                           (num natp)
                           cutsdb)
  :guard (<= (+ idx num) (cut-leaves-length cutsdb))
  :measure (nfix num)
  (b* (((when (<= (lnfix num) 1)) t))
    (and (< (cut-leavesi idx cutsdb)
            (cut-leavesi (+ 1 (lnfix idx)) cutsdb))
         (leaves-sorted (+ 1 (lnfix idx)) (1- (lnfix num)) cutsdb)))
  ///

  (def-updater-independence-thm leaves-sorted-updater-independence
    (implies (range-nat-equiv idx num (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
             (equal (leaves-sorted idx num new)
                    (leaves-sorted idx num old)))
    :hints (("goal" :induct (leaves-sorted idx num new)
             :expand ((:free (new) (leaves-sorted idx num new))
                      ;; (:free (x) (range-of-nths idx num x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  (defthmd leaves-sorted-implies-compare
    (implies (and (leaves-sorted idx num cutsdb)
                  (< (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (< (cut-leavesi idx cutsdb)
                (cut-leavesi n cutsdb)))
    :rule-classes (:rewrite :linear)))


(define leaves-bounded ((idx natp)
                        (num natp)
                        (bound natp)
                        cutsdb)
  :guard (<= (+ idx num) (cut-leaves-length cutsdb))
  :measure (nfix num)
  (b* (((when (zp num)) t))
    (and (< (cut-leavesi idx cutsdb) (lnfix bound))
         (leaves-bounded (+ 1 (lnfix idx)) (1- (lnfix num)) bound cutsdb)))
  ///
  (def-updater-independence-thm leaves-bounded-updater-independence
    (implies (range-nat-equiv idx num (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
             (equal (leaves-bounded idx num bound new)
                    (leaves-bounded idx num bound old)))
    :hints (("goal" :induct (leaves-bounded idx num bound new)
             :expand ((:free (new) (leaves-bounded idx num bound new))
                      ;; (:free (x) (range-of-nths idx num bound x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  (defthmd leaves-bounded-implies-compare
    (implies (and (leaves-bounded idx num bound cutsdb)
                  (<= (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (< (cut-leavesi n cutsdb) (nfix bound)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defthmd leaves-bounded-when-bounded-lesser
    (implies (and (leaves-bounded idx num bound1 cutsdb)
                  (<= (nfix bound1) (nfix bound)))
             (leaves-bounded idx num bound cutsdb))))




(define truth4-deps-bounded ((n natp) (truth truth4-p))
  :guard (<= n 4)
  :measure (nfix (- 4 (nfix n)))
  (if (mbe :logic (zp (- 4 (nfix n)))
           :exec (eql n 4))
      t
    (and (not (truth::depends-on4 n truth))
         (truth4-deps-bounded (1+ (lnfix n)) truth)))
  ///
  ;; (local (defthm loghead-of-zp
  ;;          (implies (zp n)
  ;;                   (equal (loghead n x) 0))
  ;;          :hints(("Goal" :in-theory (enable bitops::loghead**)))))

  (local (defthm depends-on-of-truth-norm
           (equal (truth::depends-on n (truth::truth-norm truth 4) 4)
                  (truth::depends-on n truth 4))
           :hints(("Goal" :in-theory (enable truth::depends-on
                                             truth::truth-norm)))))

  (local (defun loghead-of-install-bit-ind (n i env)
           (if (zp n)
               (list n i env)
             (loghead-of-install-bit-ind (1- n) (1- (nfix i)) (logcdr env)))))

  (local (Defthm loghead-of-install-bit-greater
           (implies (<= (nfix n) (nfix i))
                    (equal (loghead n (install-bit i val env))
                           (loghead n env)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              acl2::install-bit**)
                   :induct (loghead-of-install-bit-ind n i env)))))

  (local (defthm truth-eval-of-env-update-greater
           (implies (<= 4 (nfix i))
                    (equal (truth::truth-eval truth (truth::env-update i val env) 4)
                           (truth::truth-eval truth env 4)))
           :hints(("Goal" :in-theory (enable truth::truth-eval
                                             truth::env-update)))))

  (defthm eval-of-env-update-when-truth4-deps-bounded
    (implies (and (truth4-deps-bounded n truth)
                  (<= (nfix n) (nfix i)))
             (equal (truth::truth-eval truth (truth::env-update i val env) 4)
                    (truth::truth-eval truth env 4)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct t)))

  (defthm truth4-deps-bounded-of-logand
    (implies (and (truth4-deps-bounded n x)
                  (truth4-deps-bounded n y)
                  (<= (nfix n) 4))
             (truth4-deps-bounded n (logand x y))))

  (defthm truth4-deps-bounded-of-logxor
    (implies (and (truth4-deps-bounded n x)
                  (truth4-deps-bounded n y)
                  (<= (nfix n) 4))
             (truth4-deps-bounded n (logxor x y))))

  (defthm truth4-deps-bounded-of-truth-norm
    (implies (<= (nfix n) 4)
             (iff (truth4-deps-bounded n (truth::truth-norm x 4))
                  (truth4-deps-bounded n x))))

  (defthm truth4-deps-bounded-implies-not-depends
    (implies (and (truth4-deps-bounded n truth)
                  (<= (nfix n) (nfix k))
                  (< (nfix k) 4))
             (not (truth::depends-on k truth 4)))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))




(local (defthm logcount-of-loghead
         (implies (natp x)
                  (<= (logcount (loghead n x)) (logcount x)))
         :hints(("Goal" :in-theory (enable* acl2::logcount**
                                            bitops::loghead**
                                            bitops::ihsext-inductions)))
         :rule-classes :linear))

(local (defthmd logcount-loghead-+1
         (equal (logcount (loghead (+ 1 (nfix n)) mask))
                (+ (logbit n mask) (logcount (loghead n mask))))
         :hints(("Goal" :in-theory (enable* acl2::logcount**
                                            bitops::loghead**
                                            bitops::logbitp**
                                            bitops::ihsext-inductions)))))

(local (defthmd logcount-loghead-monotonic-lemma
           (<= (logcount (loghead n x))
               (logcount (loghead (+ (nfix n) (nfix m)) x)))
           :hints (("goal" :induct (bitops::count-down m))
                   (and stable-under-simplificationp
                        '(:use ((:instance logcount-loghead-+1
                                 (n (+ -1 (nfix n) (nfix m)))
                                 (mask x))))))))

(local (defthmd logcount-loghead-monotonic
         (implies (<= (nfix n) (nfix m))
                  (<= (logcount (loghead n x))
                      (logcount (loghead m x))))
         :hints (("goal" :use ((:instance logcount-loghead-monotonic-lemma
                                (m (- (nfix m) (nfix n)))))))
         :rule-classes (:rewrite :linear)))



(local (defthm logcount-of-loghead-lte-n
         (<= (logcount (loghead n x)) (nfix n))
         :hints(("Goal" :in-theory (enable* acl2::logcount**
                                            bitops::loghead**
                                            bitops::ihsext-inductions)))
         :rule-classes :linear))

(define truth4-deps-unbounded-witness ((n natp)
                                       (truth truth4-p))
  :guard (<= n 4)
  :measure (nfix (- 4 (nfix n)))
  :returns (witness natp :rule-classes :type-prescription)
  (if (mbe :logic (zp (- 4 (nfix n)))
           :exec (eql n 4))
      4
    (if (truth::depends-on4 n truth)
        (nfix n)
      (truth4-deps-unbounded-witness (1+ (lnfix n)) truth)))
  ///
  (local (in-theory (enable truth4-deps-bounded)))

  (defret truth4-deps-unbounded-witness-lower-bound
    (implies (not (truth4-deps-bounded n truth))
             (<= (nfix n) witness)))

  (defret truth4-deps-unbounded-witness-upper-bound
    (implies (not (truth4-deps-bounded n truth))
             (< witness 4)))

  (defretd truth4-deps-unbounded-witness-correct
    (implies (not (truth4-deps-bounded n truth))
             (truth::depends-on witness truth 4)))

  (local (in-theory (disable truth4-deps-bounded)))


  (local (in-theory (enable logcount-loghead-+1)))

  (local (defthmd index-permute-shrink-upper-bound
           (implies (and (<= (nfix k) (logcount (loghead n mask))) ;; (<= (nth-set-bit-pos k mask) (nfix n))
                         ;; (<= (nfix k) (logcount (loghead 4 mask)))
                         (natp mask)
                         (< (nfix n) 4))
                    (<= (nfix k) (truth::index-permute-shrink 0 nil mask n 4)))
           :hints(("Goal" :in-theory (enable truth::index-permute-shrink-redef)
                   :use ((:instance logcount-loghead-monotonic (n n) (m 4) (x mask)))))))

  ;; (local (in-theory (disable TRUTH::NTH-SET-BIT-POS-GREATER-IFF-LOGCOUNT-LESS)))


   ;; suppose x only depends on vars 0,1 -- so deps are bounded by 2
  ;; permute mask is b1101 so new x will depend on 0, 2
  ;; n=3, k=2
  ;; this works because 2 is the logcount of the loghead 3 of the mask

  (defthm truth4-deps-bounded-of-permute-stretch
    (implies (and (truth4-deps-bounded k x)
                  (natp permute-mask)
                  ;; (<= (nfix k) (logcount (loghead 4 permute-mask)))

                  (<= (nfix k) (logcount (loghead n permute-mask))))
             (truth4-deps-bounded n (truth::permute-stretch 0 nil permute-mask x 4)))
    :hints ((acl2::use-termhint
             (b* ((perm (truth::permute-stretch 0 nil permute-mask x 4))
                  (witness (truth4-deps-unbounded-witness n perm))
                  (shrink (truth::index-permute-shrink 0 nil permute-mask witness 4)))
               `'(:use ((:instance truth4-deps-unbounded-witness-correct
                         (truth ,(hq perm) ))
                        (:instance truth4-deps-unbounded-witness-lower-bound
                         (truth ,(hq perm)))
                        (:instance truth4-deps-unbounded-witness-upper-bound
                         (truth ,(hq perm)))
                        (:instance truth::depends-on-of-permute-stretch
                         (numvars 4)
                         (n ,(hq witness))
                         (mask permute-mask)
                         (truth x))
                        (:instance index-permute-shrink-upper-bound
                         (mask permute-mask)
                         (k k)
                         (n ,(hq witness)))
                        (:instance logcount-loghead-monotonic
                         (x permute-mask)
                         (n n) (m ,(hq witness)))
                        (:instance truth4-deps-bounded-implies-not-depends
                         (n k) (truth x)
                         (k ,(hq shrink))))
                  :in-theory (e/d (;; truth::index-permute-shrink-redef
                                   )
                                  (truth4-deps-unbounded-witness-upper-bound
                                   truth4-deps-unbounded-witness-lower-bound
                                   truth::depends-on-of-permute-stretch
                                   truth4-deps-bounded-implies-not-depends
                                   ))
                  :do-not-induct t))))
    :otf-flg t)

  (defthm truth4-deps-bounded-of-permute-stretch-rw
    (implies (and (truth4-deps-bounded (logcount (loghead n permute-mask)) x)
                  (natp permute-mask))
             (truth4-deps-bounded n (truth::permute-stretch 0 nil permute-mask x 4)))
    :hints (("goal" :use ((:instance truth4-deps-bounded-of-permute-stretch
                           (k (logcount (loghead n permute-mask)))))
             :in-theory (disable truth4-deps-bounded-of-permute-stretch)))
    :otf-flg t))








(define cut-truth-bounded ((n natp) cutsdb)
  :guard (< n (cut-info-length cutsdb))
  (b* (((cutinfo info) (cut-infoi n cutsdb)))
    (truth4-deps-bounded info.size info.truth))
  ///
  (def-updater-independence-thm cut-truth-bounded-updater-independence
    (implies (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                       (nth n (nth *cut-infoi1* old))
                                       #x7ffff)
             (equal (cut-truth-bounded n new)
                    (cut-truth-bounded n old))))

  (defthm cut-truth-bounded-implies-truth4-deps-bounded
    (implies (cut-truth-bounded n cutsdb)
             (b* (((cutinfo info) (cut-infoi n cutsdb)))
               (truth4-deps-bounded info.size info.truth)))))

(define cutsdb-truths-bounded ((n natp) cutsdb)
  :guard (<= n (cut-info-length cutsdb))
  (or (zp n)
      (and (cut-truth-bounded (1- n) cutsdb)
           (cutsdb-truths-bounded (1- n) cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-truths-bounded-updater-independence
    (implies (range-cutinfo-equiv-under-mask 0 n #x7ffff
                                             (nth *cut-infoi1* new)
                                             (nth *cut-infoi1* old))
             (equal (cutsdb-truths-bounded n new)
                    (cutsdb-truths-bounded n old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defthm cutsdb-truths-bounded-implies-cut-truths-bounded
    (implies (and (cutsdb-truths-bounded n cutsdb)
                  (< (nfix m) (nfix n)))
             (cut-truth-bounded m cutsdb))))


(define cut-leaves-sorted ((n natp) cutsdb)
  :guard (and (< n (cut-info-length cutsdb))
              (<= (+ 4 (* 4 n)) (cut-leaves-length cutsdb)))
  (b* (((cutinfo info) (cut-infoi n cutsdb)))
    (leaves-sorted (* 4 (lnfix n)) info.size cutsdb))
  ///
  (def-updater-independence-thm cut-leaves-sorted-updater-independence
    (implies (and (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                            (nth n (nth *cut-infoi1* old))
                                            #x70000)
                  (range-nat-equiv (* 4 (nfix n)) 4
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cut-leaves-sorted n new)
                    (cut-leaves-sorted n old))))

  (defthm cut-leaves-sorted-implies-leaves-sorted
    (implies (and (cut-leaves-sorted n cutsdb)
                  (natp n)
                  (nat-equiv size (cutinfo->size (cut-infoi n cutsdb))))
             (leaves-sorted (* 4 n) size cutsdb))))

(define cutsdb-leaves-sorted ((n natp) cutsdb)
  :guard (and (<= n (cut-info-length cutsdb))
              (<= (* 4 n) (cut-leaves-length cutsdb)))
  (or (zp n)
      (and (cut-leaves-sorted (1- n) cutsdb)
           (cutsdb-leaves-sorted (1- n) cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-leaves-sorted-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask 0 n #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv 0 (* 4 (nfix n)) (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cutsdb-leaves-sorted n new)
                    (cutsdb-leaves-sorted n old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defthm cutsdb-leaves-sorted-implies-cut-leaves-sorted
    (implies (and (cutsdb-leaves-sorted n cutsdb)
                  (< (nfix m) (nfix n)))
             (cut-leaves-sorted m cutsdb))))


(define cut-leaves-bounded ((n natp) (bound natp) cutsdb)
  :guard (and (< n (cut-info-length cutsdb))
              (<= (+ 4 (* 4 n)) (cut-leaves-length cutsdb)))
  (b* (((cutinfo info) (cut-infoi n cutsdb)))
    (leaves-bounded (* 4 (lnfix n)) info.size bound cutsdb))
  ///
  (def-updater-independence-thm cut-leaves-bounded-updater-independence
    (implies (and (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                            (nth n (nth *cut-infoi1* old))
                                            #x70000)
                  (range-nat-equiv (* 4 (nfix n)) 4
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cut-leaves-bounded n bound new)
                    (cut-leaves-bounded n bound old))))

  (defthmd cut-leaves-bounded-when-bounded-lesser
    (implies (and (cut-leaves-bounded n bound1 cutsdb)
                  (<= (nfix bound1) (nfix bound)))
             (cut-leaves-bounded n bound cutsdb))
    :hints(("Goal" :in-theory (enable leaves-bounded-when-bounded-lesser)))))


(define cut-range-leaves-bounded ((n natp) (max natp) (bound natp) cutsdb)
  :guard (and (<= n max)
              (<= max (cut-info-length cutsdb))
              (<= (* 4 max) (cut-leaves-length cutsdb)))
  :measure (nfix (- (nfix max) (nfix n)))
  (or (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (eql max n))
      (and (cut-leaves-bounded (1- max) bound cutsdb)
           (cut-range-leaves-bounded n (1- max) bound cutsdb)))
  ///
  (def-updater-independence-thm cut-range-leaves-bounded-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask n (- (nfix max) (nfix n))
                                                  #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv (* 4 (nfix n)) (* 4 (- (nfix max) (nfix n)))
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cut-range-leaves-bounded n max bound new)
                    (cut-range-leaves-bounded n max bound old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defthmd cut-range-leaves-bounded-when-bounded-lesser
    (implies (and (cut-range-leaves-bounded n max bound1 cutsdb)
                  (<= (nfix bound1) (nfix bound)))
             (cut-range-leaves-bounded n max bound cutsdb))
    :hints(("Goal" :in-theory (enable cut-leaves-bounded-when-bounded-lesser))))

  (defthmd cut-range-leaves-bounded-implies-cut-bounded
    (implies (and (cut-range-leaves-bounded n max bound cutsdb)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix max)))
             (cut-leaves-bounded m bound cutsdb))))


(define nodecut-indices-increasing ((n natp) cutsdb)
  :guard (< n (nodecut-indices-length cutsdb))
  (or (zp n)
      (and (<= (nodecut-indicesi (1- n) cutsdb) (nodecut-indicesi n cutsdb))
           (nodecut-indices-increasing (1- n) cutsdb)))
  ///
  (def-updater-independence-thm nodecut-indices-increasing-updater-independence
    (implies (range-nat-equiv 0 (+ 1 (nfix n)) (nth *nodecut-indicesi1* new)
                              (nth *nodecut-indicesi1* old))
             (equal (nodecut-indices-increasing n new)
                    (nodecut-indices-increasing n old))))

  (local (defthm nodecut-indices-increasing-implies-lte-nth
           (implies (and (nodecut-indices-increasing n cutsdb)
                         (<= (nfix m) (nfix n)))
                    (<= (nodecut-indicesi m cutsdb) (nodecut-indicesi n cutsdb)))))

  (defthmd nodecut-indices-increasing-implies-monotonic
    (implies (and (nodecut-indices-increasing n cutsdb)
                  (<= (nfix i) (nfix j))
                  (<= (nfix j) (nfix n)))
             (<= (nodecut-indicesi i cutsdb) (nodecut-indicesi j cutsdb)))))



(define nodecuts-leaves-bounded ((n natp) cutsdb)
  :guard (and (< n (nodecut-indices-length cutsdb))
              (nodecut-indices-increasing n cutsdb)
              (b* ((max (nodecut-indicesi n cutsdb)))
                (and (<= max (cut-info-length cutsdb))
                     (<= (* 4 max) (cut-leaves-length cutsdb)))))
  :guard-hints (("goal" :expand ((nodecut-indices-increasing n cutsdb))))
  (or (zp n)
      (and (cut-range-leaves-bounded (nodecut-indicesi (1- n) cutsdb) (nodecut-indicesi n cutsdb)
                                     n cutsdb)
           (nodecuts-leaves-bounded (1- n) cutsdb)))
  ///
  (def-updater-independence-thm nodecuts-leaves-bounded-updater-independence
    (implies (and (range-nat-equiv 0 (+ 1 (nfix n)) (nth *nodecut-indicesi1* new)
                                   (nth *nodecut-indicesi1* old))
                  (nodecut-indices-increasing n old)
                  (range-cutinfo-equiv-under-mask 0 (nodecut-indicesi n old)
                                                  #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv 0 (* 4 (nodecut-indicesi n old))
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (nodecuts-leaves-bounded n new)
                    (nodecuts-leaves-bounded n old)))
    :hints(("Goal" :in-theory (enable nodecut-indices-increasing)))))


(define cutsdb-ok (cutsdb)
  :returns (ok)
  (and (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
       (equal (nodecut-indicesi 0 cutsdb) 0)
       (nodecut-indices-increasing (cut-nnodes cutsdb) cutsdb)
       (b* ((next-cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
         (and (<= next-cut (cut-info-length cutsdb))
              (<= (* 4 next-cut) (cut-leaves-length cutsdb))
              (nodecuts-leaves-bounded (cut-nnodes cutsdb) cutsdb)
              (cutsdb-leaves-sorted next-cut cutsdb)
              (cutsdb-truths-bounded next-cut cutsdb))))
  ///

  (defthm cutsdb-ok-implies-initial-nodecut-index
    (implies (cutsdb-ok cutsdb)
             (equal (nodecut-indicesi 0 cutsdb) 0)))


  (defret cutsdb-ok-implies-nodecut-indices-monotonic
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb))
                  (<= (nfix n) (nfix m)))
             (<= (nodecut-indicesi n cutsdb) (nodecut-indicesi m cutsdb)))
    :hints(("Goal" :in-theory (enable nodecut-indices-increasing-implies-monotonic))))

  (defret cutsdb-ok-implies-nodecut-indices-bounded-by-last
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi m cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
    :rule-classes :linear)

  (defret cutsdb-ok-implies-start-<=-next
    (implies (and ok
                  (< (nfix m) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi m cutsdb) (nodecut-indicesi (+ 1 (nfix m)) cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defret cutsdb-ok-implies-leaves-length-sufficient
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (<= (* 4 (nodecut-indicesi m cutsdb)) (cut-leaves-length cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes (:rewrite :linear))

  (defret cutsdb-ok-implies-info-length-sufficient
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi m cutsdb) (cut-info-length cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes (:rewrite :linear))

  (defret cutsdb-ok-implies-nnodes-<-indices-length
    (implies ok
             (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb)))
    :rule-classes (:rewrite :linear))

  (defret cutsdb-ok-implies-cut-leaves-sorted
    (implies (and ok
                  (< (nfix m) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cut-leaves-sorted m cutsdb)))

  (defret cutsdb-ok-implies-cut-truth-bounded
    (implies (and ok
                  (< (nfix m) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cut-truth-bounded m cutsdb)))

  ;; (local (defthm range-nat-equiv-badguy-not-equal-n-at-upper-bound
  ;;          (implies (and (<= (nfix upper-bound) (nfix n))
  ;;                        (posp upper-bound))
  ;;                   (not (equal (range-nat-equiv-badguy 0 upper-bound x y) (nfix n))))
  ;;          :hints (("goal" :use ((:instance range-nat-equiv-badguy-upper-bound
  ;;                                 (start 0) (num upper-bound)))
  ;;                   :in-theory (disable range-nat-equiv-badguy-upper-bound)))))

  (def-updater-independence-thm cutsdb-ok-updater-independence
    (implies (and (cutsdb-ok old)
                  (equal (nth *cut-nnodes1* new) (nth *cut-nnodes1* old))
                  (equal (nth *nodecut-indicesi1* new) (nth *nodecut-indicesi1* old))
                  (<= (cut-leaves-length old) (cut-leaves-length new))
                  (<= (cut-info-length old) (cut-info-length new))
                  (range-nat-equiv 0 (* 4 (nodecut-indicesi (cut-nnodes old) old))
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old))
                  (range-cutinfo-equiv-under-mask 0 (nodecut-indicesi (cut-nnodes old) old)
                                                  #x7ffff
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old)))
             (cutsdb-ok new)))

  (defthm cutsdb-ok-of-update-cut-leaves-past-last
    (implies (and (cutsdb-ok cutsdb)
                  (<= (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (nfix n))
                  ;; (< (nfix n) (cut-leaves-length cutsdb))
                  )
             (cutsdb-ok (update-cut-leavesi n v cutsdb)))
    :hints (("goal" :cases ((equal 0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))))

  (defthm cutsdb-ok-of-update-cut-info-past-last
    (implies (and (cutsdb-ok cutsdb)
                  (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix n))
                  ;; (< (nfix n) (cut-leaves-length cutsdb))
                  )
             (cutsdb-ok (update-cut-infoi n v cutsdb)))
    :hints (("goal" :cases ((equal 0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))))

  (set-ignore-ok t)

  (defthm cutsdb-ok-of-update-last-node
    (implies (cutsdb-ok cutsdb)
             (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)))
               (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                             (not (equal 0 (cut-nnodes cutsdb)))
                             (equal next (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                             (cut-truth-bounded (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb)
                             (cut-leaves-sorted (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb)
                             (cut-leaves-bounded (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                                 (cut-nnodes cutsdb) cutsdb)
                             (<= (* 4 next) (cut-leaves-length cutsdb))
                             (<= next (cut-info-length cutsdb))
                             ;; (<= size 4)
                             ;; (< (+ 2 m size) (cut-leaves-length cutsdb))
                             ;; (truth4-p truth)
                             ;; (truth4-deps-bounded size truth)
                             ;; (cut-leaves-sorted data size cutsdb)
                             ;; (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                             ;;        (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb))
                             )
                        (cutsdb-ok (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                            next cutsdb)))))
    :hints (("goal" :in-theory (e/d* (acl2::arith-equiv-forwarding))
             :expand ((:free (cutsdb1) (nodecut-indices-increasing (cut-nnodes cutsdb) cutsdb1))
                      (:free (cutsdb1) (nodecuts-leaves-bounded (cut-nnodes cutsdb) cutsdb1))
                      (cutsdb-truths-bounded (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                             cutsdb)
                      (cutsdb-leaves-sorted (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                             cutsdb)
                      (:free (n m bound) (cut-range-leaves-bounded n (+ 1 m) bound cutsdb))))))


  (local (defthm nodecuts-leaves-bounded-implies-cuts-bounded
           (implies (and (nodecuts-leaves-bounded n cutsdb)
                         (equal (nodecut-indicesi 0 cutsdb) 0)
                         (< (nfix cut) (nodecut-indicesi n cutsdb)))
                    (cut-leaves-bounded cut n cutsdb))
           :hints(("Goal" :in-theory (enable nodecuts-leaves-bounded
                                             cut-leaves-bounded-when-bounded-lesser
                                             cut-range-leaves-bounded-implies-cut-bounded)))))

  (defthm cutsdb-ok-implies-cuts-bounded-by-nnodes
    (implies (and (cutsdb-ok cutsdb)
                  (equal bound (cut-nnodes cutsdb))
                  (< (nfix cut) (nodecut-indicesi bound cutsdb)))
             (cut-leaves-bounded cut bound cutsdb))))

(define leaves-lit-idsp ((idx natp)
                         (num natp)
                         (aignet)
                         cutsdb)
  :guard (<= (+ idx num) (cut-leaves-length cutsdb))
  :measure (nfix num)
  (b* (((when (zp num)) t)
       (data (cut-leavesi idx cutsdb)))
    (and (id-existsp data aignet)
         (not (eql (id->type data aignet) (out-type)))
         (leaves-lit-idsp (+ 1 (lnfix idx)) (1- (lnfix num)) aignet cutsdb)))
  ///
  (def-updater-independence-thm leaves-lit-idsp-updater-independence
    (implies (range-nat-equiv idx num (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
             (equal (leaves-lit-idsp idx num aignet new)
                    (leaves-lit-idsp idx num aignet old)))
    :hints (("goal" :induct (leaves-lit-idsp idx num aignet new)
             :expand ((:free (new) (leaves-lit-idsp idx num aignet new))
                      ;; (:free (x) (range-of-nths idx num aignet x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  ;; (defthm leaves-lit-idsp-preserved-by-write
  ;;   (implies (<= (+ (nfix idx) (nfix num)) (nfix dest-idx))
  ;;            (equal (leaves-lit-idsp idx num aignet (update-cut-leavesi dest-idx val cutsdb))
  ;;                   (leaves-lit-idsp idx num aignet cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-array-acc-meta-split))))

  (defthmd leaves-lit-idsp-implies
    (implies (and (leaves-lit-idsp idx num aignet cutsdb)
                  (<= (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (and (aignet-idp (cut-leavesi n cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-leavesi n cutsdb) aignet)))) :output))
                  (not (equal (stype (car (lookup-id (cut-leavesi n cutsdb) aignet))) :po))
                  (not (equal (stype (car (lookup-id (cut-leavesi n cutsdb) aignet))) :nxst))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthmd leaves-lit-idsp-implies-aignet-litp
    (implies (and (leaves-lit-idsp idx num aignet cutsdb)
                  (<= (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (aignet-litp (make-lit (cut-leavesi n cutsdb) bit) aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding aignet-idp))))

  (defthm leaves-lit-idsp-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (leaves-lit-idsp idx num orig cutsdb))
             (leaves-lit-idsp idx num new cutsdb))))

(define cut-leaves-lit-idsp ((n natp) aignet cutsdb)
  :guard (and (< n (cut-info-length cutsdb))
              (<= (+ 4 (* 4 n)) (cut-leaves-length cutsdb)))
  (b* (((cutinfo info) (cut-infoi n cutsdb)))
    (leaves-lit-idsp (* 4 (lnfix n)) info.size aignet cutsdb))
  ///
  (def-updater-independence-thm cut-leaves-lit-idsp-updater-independence
    (implies (and (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new))
                                            (nth n (nth *cut-infoi1* old))
                                            #x70000)
                  (range-nat-equiv (* 4 (nfix n)) 4
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cut-leaves-lit-idsp n aignet new)
                    (cut-leaves-lit-idsp n aignet old))))

  (defthm cut-leaves-lit-idsp-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (cut-leaves-lit-idsp n orig cutsdb))
             (cut-leaves-lit-idsp n new cutsdb))))

(define cutsdb-leaves-lit-idsp ((n natp) aignet cutsdb)
  :guard (and (<= n (cut-info-length cutsdb))
              (<= (* 4 n) (cut-leaves-length cutsdb)))
  (or (zp n)
      (and (cut-leaves-lit-idsp (1- n) aignet cutsdb)
           (cutsdb-leaves-lit-idsp (1- n) aignet cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-leaves-lit-idsp-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask 0 n #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv 0 (* 4 (nfix n)) (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cutsdb-leaves-lit-idsp n aignet new)
                    (cutsdb-leaves-lit-idsp n aignet old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defthm cutsdb-leaves-lit-idsp-implies-cut-leaves-lit-idsp
    (implies (and (cutsdb-leaves-lit-idsp n aignet cutsdb)
                  (< (nfix m) (nfix n)))
             (cut-leaves-lit-idsp m aignet cutsdb)))

  (defthm cutsdb-leaves-lit-idsp-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (cutsdb-leaves-lit-idsp n orig cutsdb))
             (cutsdb-leaves-lit-idsp n new cutsdb))))

(define cutsdb-leaves-lit-idsp-badguy ((n natp) aignet cutsdb)
  :guard (and (<= n (cut-info-length cutsdb))
              (<= (* 4 n) (cut-leaves-length cutsdb)))
  :returns (badguy natp :rule-classes :type-prescription)
  (if (zp n)
      0
    (if (cut-leaves-lit-idsp (1- n) aignet cutsdb)
        (cutsdb-leaves-lit-idsp-badguy (1- n) aignet cutsdb)
      (1- n)))
  ///
  (def-updater-independence-thm cutsdb-leaves-lit-idsp-badguy-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask 0 n #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv 0 (* 4 (nfix n)) (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cutsdb-leaves-lit-idsp-badguy n aignet new)
                    (cutsdb-leaves-lit-idsp-badguy n aignet old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defret cutsdb-leaves-lit-idsp-by-badguy
    (implies (cut-leaves-lit-idsp badguy
              aignet cutsdb)
             (cutsdb-leaves-lit-idsp n aignet cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp))))

  (defretd cutsdb-leaves-lit-idsp-by-badguy-literal
    (implies (acl2::rewriting-positive-literal
              `(cutsdb-leaves-lit-idsp ,n ,aignet ,cutsdb))
             (iff (cutsdb-leaves-lit-idsp n aignet cutsdb)
                  (or (<= (nfix n) badguy)
                      (cut-leaves-lit-idsp badguy
                                           aignet cutsdb))))
    :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp))))

  (defret cutsdb-leaves-lit-idsp-badguy-range
    (implies (not (cutsdb-leaves-lit-idsp n aignet cutsdb))
             (< badguy (nfix n)))
    :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp)))
    :rule-classes :linear))

(defthm cutsdb-leaves-lit-idsp-ancestor-hack
  (implies (cutsdb-leaves-lit-idsp n aignet cutsdb)
           (cutsdb-leaves-lit-idsp n aignet cutsdb)))


(define cutsdb-lit-idsp (aignet (cutsdb cutsdb-ok))
  (cutsdb-leaves-lit-idsp
   (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
   aignet cutsdb)
  ///
  (def-updater-independence-thm cutsdb-lit-idsp-updater-independence
    (implies (and (equal max (nodecut-indicesi (cut-nnodes new) new))
                  (equal max (nodecut-indicesi (cut-nnodes old) old))
                  (range-cutinfo-equiv-under-mask 0 max #x70000
                                                  (nth *cut-infoi1* new)
                                                  (nth *cut-infoi1* old))
                  (range-nat-equiv 0 (* 4 max)
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cutsdb-lit-idsp aignet new)
                    (cutsdb-lit-idsp aignet old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defthmd cutsdb-lit-idsp-implies-cut-leaves-lit-idsp
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cut-leaves-lit-idsp cut aignet cutsdb)))

  (defthm cutsdb-lit-idsp-of-aignet-extension
   (implies (and (aignet-extension-binding)
                 (cutsdb-lit-idsp orig cutsdb))
            (cutsdb-lit-idsp new cutsdb))))








(define cutsdb-maybe-grow-nodecut-indices ((size natp) cutsdb)
  :returns (new-cutsdb)
  (if (<= (nodecut-indices-length cutsdb) (lnfix size))
      (resize-nodecut-indices (max 16 (* 2 (lnfix size))) cutsdb)
    cutsdb)
  ///

  (defthm nth-of-cutsdb-maybe-grow-nodecut-indices
    (implies (not (equal (nfix n) *nodecut-indicesi1*))
             (equal (nth n (cutsdb-maybe-grow-nodecut-indices size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-nodecut-indices-of-cutsdb-maybe-grow-nodecut-indices
    (nat-equiv (nth n (nth *nodecut-indicesi1* (cutsdb-maybe-grow-nodecut-indices size cutsdb)))
               (nth n (nth *nodecut-indicesi1* cutsdb))))

  (defthm nth-nodecut-indices-of-cutsdb-maybe-grow-nodecut-indices-below-size
    (implies (< (nfix n) (nodecut-indices-length cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* (cutsdb-maybe-grow-nodecut-indices size cutsdb)))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret cutsdb-ok-of-cutsdb-maybe-grow-nodecut-indices
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok))))

  (defret nodecut-indices-length-of-cutsdb-maybe-grow-nodecut-indices
    (< (nfix size) (nodecut-indices-length new-cutsdb))
    :rule-classes :linear))


(define cutsdb-maybe-grow-cut-leaves ((size natp) cutsdb)
  :returns (new-cutsdb)
  (if (<= (cut-leaves-length cutsdb) (lnfix size))
      (resize-cut-leaves (max 16 (* 2 (lnfix size))) cutsdb)
    cutsdb)
  ///

  (defthm nth-of-cutsdb-maybe-grow-cut-leaves
    (implies (not (equal (nfix n) *cut-leavesi1*))
             (equal (nth n (cutsdb-maybe-grow-cut-leaves size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-leaves-of-cutsdb-maybe-grow-cut-leaves
    (nat-equiv (nth n (nth *cut-leavesi1* (cutsdb-maybe-grow-cut-leaves size cutsdb)))
               (nth n (nth *cut-leavesi1* cutsdb))))

  (defthm nth-cut-leaves-of-cutsdb-maybe-grow-cut-leaves-below-size
    (implies (< (nfix n) (cut-leaves-length cutsdb))
             (equal (nth n (nth *cut-leavesi1* (cutsdb-maybe-grow-cut-leaves size cutsdb)))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret cutsdb-ok-of-cutsdb-maybe-grow-cut-leaves
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok))))

  (defret cut-leaves-length-of-cutsdb-maybe-grow-cut-leaves
    (< (nfix size) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-leaves-length-nondecreasing-of-cutsdb-maybe-grow-cut-leaves
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-leaves-length-of-cutsdb-maybe-grow-cut-leaves-rw
    (implies (natp size)
             (and (< size (cut-leaves-length new-cutsdb))
                  (<= size (cut-leaves-length new-cutsdb))))))

(define cutsdb-maybe-grow-cut-info ((size natp) cutsdb)
  :returns (new-cutsdb)
  (if (<= (cut-info-length cutsdb) (lnfix size))
      (resize-cut-info (max 16 (* 2 (lnfix size))) cutsdb)
    cutsdb)
  ///

  (defthm nth-of-cutsdb-maybe-grow-cut-info
    (implies (not (equal (nfix n) *cut-infoi1*))
             (equal (nth n (cutsdb-maybe-grow-cut-info size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-info-of-cutsdb-maybe-grow-cut-info
    (cutinfo-equiv (nth n (nth *cut-infoi1* (cutsdb-maybe-grow-cut-info size cutsdb)))
                   (nth n (nth *cut-infoi1* cutsdb))))

  (defthm nth-cut-info-of-cutsdb-maybe-grow-cut-info-below-size
    (implies (< (nfix n) (cut-info-length cutsdb))
             (equal (nth n (nth *cut-infoi1* (cutsdb-maybe-grow-cut-info size cutsdb)))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret cutsdb-ok-of-cutsdb-maybe-grow-cut-info
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok))))

  (defret cut-info-length-of-cutsdb-maybe-grow-cut-info
    (< (nfix size) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-cutsdb-maybe-grow-cut-info
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-of-cutsdb-maybe-grow-cut-info-rw
    (implies (natp size)
             (and (< size (cut-info-length new-cutsdb))
                  (<= size (cut-info-length new-cutsdb))))))





(define cuts-add-node ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  (b* ((old-nnodes (cut-nnodes cutsdb))
       (new-nnodes (+ 1 old-nnodes))
       (cutsdb (update-cut-nnodes new-nnodes cutsdb))
       (cutsdb (cutsdb-maybe-grow-nodecut-indices new-nnodes cutsdb)))
    (update-nodecut-indicesi new-nnodes (nodecut-indicesi old-nnodes cutsdb) cutsdb))

  ///

  (defret cutsdb-ok-of-cuts-add-node
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints (("goal" :in-theory (enable cutsdb-ok cut-range-leaves-bounded)
             :Expand ((:free (cutsdb1) (nodecut-indices-increasing (+ 1 (cut-nnodes cutsdb)) cutsdb1))
                      (:free (cutsdb1) (nodecuts-leaves-bounded (+ 1 (cut-nnodes cutsdb)) cutsdb1))))))

  (defret cut-nnodes-of-cuts-add-node
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-of-cuts-add-node
    (implies (and (not (equal (nfix n) *cut-nnodes1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nodecut-indices-length-of-cuts-add-node
    (< (+ 1 (cut-nnodes cutsdb)) (nodecut-indices-length new-cutsdb))
    :rule-classes :linear)

  (defret nth-nodecut-indices-of-cuts-add-node
    (implies (and (not (equal (nfix n) (+ 1 (cut-nnodes cutsdb))))
                  ;; (< (nfix n) (nodecut-indices-length cutsdb))
                  )
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret last-node-index-of-cuts-add-node
    (implies (and (equal (nfix new-node) (+ 1 (cut-nnodes cutsdb)))
                  ;; (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
                  )
             (equal (nodecut-indicesi new-node new-cutsdb)
                    (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))))





(define leaves-merge-count ((idx0 natp) (size0 natp)
                               (idx1 natp) (size1 natp)
                               cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-leaves-length cutsdb))
              (<= (+ idx1 size1) (cut-leaves-length cutsdb)))
  :measure (+ (lnfix size1) (lnfix size0))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((when (zp size0)) (lnfix size1))
       ((when (zp size1)) (lnfix size0))
       (node0 (cut-leavesi idx0 cutsdb))
       (node1 (cut-leavesi idx1 cutsdb))
       ((when (eql node0 node1))
        (+ 1 (leaves-merge-count (1+ (lnfix idx0)) (1- size0)
                                    (1+ (lnfix idx1)) (1- size1)
                                    cutsdb)))
       ((when (< node0 node1))
        (+ 1 (leaves-merge-count (1+ (lnfix idx0)) (1- size0)
                                    idx1 size1
                                    cutsdb))))
    (+ 1 (leaves-merge-count idx0 size0
                                (1+ (lnfix idx1)) (1- size1)
                                cutsdb)))
  ///
  (def-updater-independence-thm leaves-merge-count-updater-independence
    (implies (and (range-nat-equiv idx0 size0 (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
                  (range-nat-equiv idx1 size1 (nth *cut-leavesi1* new) (nth *cut-leavesi1* old)))
             (equal (leaves-merge-count idx0 size0 idx1 size1 new)
                    (leaves-merge-count idx0 size0 idx1 size1 old)))))

(defthm nth-in-u32-listp-nfix-u32p
  (implies (and (acl2::u32-listp gates)
                (< (nfix idx) (len gates)))
           (unsigned-byte-p 32 (nfix (nth idx gates))))
  :hints(("Goal" :in-theory (enable nth))))


(defthm unsigned-byte-p-of-cut-leavesi
  (implies (and (cutsdbp cutsdb)
                (< (nfix n) (cut-leaves-length cutsdb)))
           (unsigned-byte-p 32 (cut-leavesi n cutsdb)))
  :hints(("Goal" :in-theory (enable cut-leavesi cut-leavesi1 cutsdbp cut-leaves-length))))

(defthm unsigned-byte-p-of-nodecut-indicesi
  (implies (and (cutsdbp cutsdb)
                (< (nfix n) (nodecut-indices-length cutsdb)))
           (unsigned-byte-p 32 (nodecut-indicesi n cutsdb)))
  :hints(("Goal" :in-theory (enable nodecut-indicesi nodecut-indicesi1 cutsdbp nodecut-indices-length))))



(define leaves-copy ((src-idx natp) (size natp)
                                (dest-idx natp)
                                cutsdb)
  :guard (and (<= (+ src-idx size) (cut-leaves-length cutsdb))
              (<= (+ dest-idx size) (cut-leaves-length cutsdb)))
  :returns (new-cutsdb)
  (b* (((when (zp size)) cutsdb)
       (cutsdb (update-cut-leavesi dest-idx (cut-leavesi src-idx cutsdb) cutsdb)))
    (leaves-copy (1+ (lnfix src-idx)) (1- size) (1+ (lnfix dest-idx)) cutsdb))
  ///
  (defret nth-of-leaves-copy
    (implies (not (equal (nfix n) *cut-leavesi1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-leaves-copy
    (implies (not (and (<= (nfix dest-idx) (nfix n))
                       (< (nfix n) (+ (nfix dest-idx) (nfix size)))))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  ;; (set-stobj-updater leaves-copy 3)

  (local (defthm x-x+y
           (equal (+ x (- x) y)
                  (fix y))))

  (defret cut-leavesi-of-leaves-copy
    (implies (or (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx))
                 (<= (nfix dest-idx) (nfix src-idx)))
             (equal (cut-leavesi n new-cutsdb)
                    (if (or (< (nfix n) (nfix dest-idx))
                            (<= (+ (nfix dest-idx) (nfix size)) (nfix n)))
                        (cut-leavesi n cutsdb)
                      (cut-leavesi (+ (nfix src-idx) (- (nfix n) (nfix dest-idx))) cutsdb))))
    :hints (("goal" :induct t
             :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (Defthm pos-fix-when-zp
           (implies (zp x) (equal (acl2::pos-fix x) 1))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (defret leaves-sorted-of-leaves-copy
    (implies (and (leaves-sorted src-idx size cutsdb)
                  (or (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx))
                      (<= (nfix dest-idx) (nfix src-idx))))
             (leaves-sorted dest-idx size new-cutsdb))
    :hints(("Goal" :in-theory (enable leaves-sorted
                                      leaves-merge-count)
            :induct <call>
            :expand ((:free (cutsdb) (leaves-sorted dest-idx size cutsdb))))))

  (defret cut-leaves-length-of-leaves-copy
    (implies (<= (+ (nfix dest-idx) (nfix size)) (cut-leaves-length cutsdb))
             (equal (cut-leaves-length new-cutsdb) (cut-leaves-length cutsdb))))

  (defret cutsdb-ok-of-leaves-copy
    (implies (and (<= (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (nfix dest-idx))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))

  (defret cut-leaves-length-nondecreasing-of-leaves-copy
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defretd cut-leaves-length-lower-bound-of-leaves-copy
    (implies (posp size)
             (<= (+ (nfix dest-idx) size) (cut-leaves-length new-cutsdb)))
    :rule-classes :linear)

  (defret leaves-bounded-of-leaves-copy
    (implies (and (leaves-bounded src-idx size bound cutsdb)
                  (or (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx))
                      (<= (nfix dest-idx) (nfix src-idx))))
             (leaves-bounded dest-idx size bound new-cutsdb))
    :hints(("Goal" :in-theory (enable leaves-bounded)
            :induct <call>)))

  (defret leaves-lit-idsp-of-leaves-copy
    (implies (and (leaves-lit-idsp src-idx size aignet cutsdb)
                  (or (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx))
                      (<= (nfix dest-idx) (nfix src-idx))))
             (leaves-lit-idsp dest-idx size aignet new-cutsdb))
    :hints(("Goal" :in-theory (enable leaves-lit-idsp)
            :induct <call>))))

(define leaves-truthenv ((idx natp) (size natp) (bit-idx natp) cutsdb bitarr)
  :verify-guards nil
  :returns (env natp :rule-classes :type-prescription)
  (b* (((when (zp size)) 0)
       (rest (leaves-truthenv (+ 1 (lnfix idx)) (1- size) (1+ (lnfix bit-idx)) cutsdb bitarr))
       (node (cut-leavesi idx cutsdb)))
    (install-bit bit-idx (get-bit node bitarr) rest))
  ///
  (def-updater-independence-thm leaves-truthenv-updater-independence
    (implies (range-nat-equiv idx size (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
             (equal (leaves-truthenv idx size bit-idx new bitarr)
                    (leaves-truthenv idx size bit-idx old bitarr))))

  (defthm lookup-in-leaves-truthenv
    (equal (truth::env-lookup k (leaves-truthenv idx size bit-idx cutsdb bitarr))
           (and (<= (nfix bit-idx) (nfix k))
                (< (nfix k) (+ (nfix bit-idx) (nfix size)))
                (acl2::bit->bool (get-bit (cut-leavesi (+ (nfix idx) (- (nfix k) (nfix bit-idx))) cutsdb) bitarr))))
    :hints(("Goal" :in-theory (enable truth::env-lookup
                                      bitops::logbitp-of-install-bit-split)))))


(define cut-value ((cut natp)
                   (cutsdb)
                   (bitarr))
  :verify-guards nil
  (b* (((cutinfo info) (cut-infoi cut cutsdb))
       (truthenv (leaves-truthenv (* 4 (lnfix cut)) info.size 0 cutsdb bitarr)))
    (truth::truth-eval4 info.truth truthenv))
  ///
  (def-updater-independence-thm cut-value-updater-independence
    (implies (and (cutinfo-equiv-under-mask
                   (nth cut (nth *cut-infoi1* new))
                   (nth cut (nth *cut-infoi1* old))
                   #x7ffff)
                  (range-nat-equiv (* 4 (nfix cut)) 4
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cut-value cut new bitarr)
                    (cut-value cut old bitarr)))))



(define copy-cut ((src natp)
                  (dst natp)
                  (cutsdb))
  :guard (and (< src (cut-info-length cutsdb))
              (<= (+ 4 (* 4 src)) (cut-leaves-length cutsdb))
              (< dst (cut-info-length cutsdb))
              (<= (+ 4 (* 4 dst)) (cut-leaves-length cutsdb)))
  :returns (new-cutsdb)
  (b* (((cutinfo srci) (cut-infoi src cutsdb))
       (cutsdb (update-cut-infoi dst srci cutsdb)))
    (leaves-copy (* 4 (lnfix src)) srci.size (* 4 (lnfix dst)) cutsdb))
  ///

  (defret nth-of-copy-cut
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-copy-cut
    (implies (or (< (nfix n) (* 4 (nfix dst)))
                 (<= (+ 4 (* 4 (nfix dst))) (nfix n)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-copy-cut
    (implies (not (equal (nfix n) (nfix dst)))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret cut-infoi-of-copy-cut
    (equal (cut-infoi dst new-cutsdb)
           (cut-infoi src cutsdb)))

  (defret cut-leavesi-of-copy-cut
    (implies (and (<= (* 4 (nfix dst)) (nfix n))
                  (< (nfix n) (+ (* 4 (nfix dst)) (cutinfo->size (cut-infoi src cutsdb)))))
             (equal (cut-leavesi n new-cutsdb)
                    (cut-leavesi (+ (* 4 (nfix src))
                                    (- (nfix n) (* 4 (nfix dst))))
                                 cutsdb)))
    :hints (("goal" :cases ((< (nfix src) (nfix dst))))))

  (defret cut-leaves-bounded-of-copy-cut
    (implies (and (cut-leaves-bounded n bound cutsdb)
                  (cut-leaves-bounded src bound cutsdb))
             (cut-leaves-bounded n bound new-cutsdb))
    :hints(("Goal" :in-theory (enable* cut-leaves-bounded
                                       acl2::arith-equiv-forwarding)
            :cases ((< (nfix n) (nfix dst))
                    (< (nfix dst) (nfix n))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix src) (nfix dst)))))))

  (local (defret cutsdb-leaves-sorted-of-copy-cut
           (implies (and (cutsdb-leaves-sorted n cutsdb)
                         (cut-leaves-sorted src cutsdb))
                    (cutsdb-leaves-sorted n new-cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-leaves-sorted)
                   :induct (cutsdb-leaves-sorted n cutsdb)
                   :do-not-induct t)
                  (and stable-under-simplificationp
                       '(:cases ((equal (nfix (1- n)) (nfix dst))
                                 (< (nfix (1- n)) (nfix dst)))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable cut-leaves-sorted)
                         :cases ((< (nfix src) (nfix dst))))))
           :otf-flg t))

  (local (defret cutsdb-truths-bounded-of-copy-cut
           (implies (and (cutsdb-truths-bounded n cutsdb)
                         (cut-truth-bounded src cutsdb))
                    (cutsdb-truths-bounded n new-cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-truths-bounded)
                   :induct (cutsdb-truths-bounded n cutsdb)
                   :do-not-induct t)
                  (and stable-under-simplificationp
                       '(:cases ((equal (nfix (1- n)) (nfix dst))
                                 (< (nfix (1- n)) (nfix dst)))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable cut-truth-bounded)
                         :cases ((< (nfix src) (nfix dst))))))))

  (local (defret cut-range-leaves-bounded-of-copy-cut
           (implies (and (cut-leaves-bounded src bound cutsdb)
                         (cut-range-leaves-bounded min max bound cutsdb))
                    (cut-range-leaves-bounded min max bound new-cutsdb))
           :hints(("Goal" :in-theory (enable cut-range-leaves-bounded)
                   :induct (cut-range-leaves-bounded min max bound cutsdb))
                  (and stable-under-simplificationp
                       '(:cases ((equal (1- max) (nfix dst))
                                 (< (1- max) (nfix dst)))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable cut-leaves-bounded)
                         :cases ((< (nfix src) (nfix dst))))))))

  (local (defret nodecuts-leaves-bounded-of-copy-cut
           (implies (and (cut-leaves-bounded src bound cutsdb)
                         (posp bound)
                         (<= (nodecut-indicesi (1- bound) cutsdb) (nfix dst))
                         (nodecut-indices-increasing m cutsdb)
                         (<= (nfix n) (nfix m))
                         (<= (nfix bound) (nfix m))
                         (nodecuts-leaves-bounded n cutsdb))
                    (nodecuts-leaves-bounded n new-cutsdb))
           :hints(("Goal" :in-theory (e/d (nodecuts-leaves-bounded)
                                          (copy-cut))
                   :induct (nodecuts-leaves-bounded n cutsdb))
                  (and stable-under-simplificationp
                       '(:cases ((< (nfix dst) (nodecut-indicesi (+ -1 n) cutsdb))
                                 (<= (nodecut-indicesi n cutsdb) (nfix dst)))))
                  (and stable-under-simplificationp
                       '(:use ((:instance cut-range-leaves-bounded-of-copy-cut
                                (min (nodecut-indicesi (+ -1 n) cutsdb))
                                (max (nodecut-indicesi n cutsdb))
                                (bound n))
                               (:instance nodecut-indices-increasing-implies-monotonic
                                (n m) (i n) (j (1- bound)))
                               (:instance nodecut-indices-increasing-implies-monotonic
                                (n m) (i (1- n)) (j n)))
                         :cases ((< (nfix n) (nfix bound)))
                         :in-theory (e/d (cut-leaves-bounded-when-bounded-lesser)
                                         (cut-range-leaves-bounded-of-copy-cut
                                          copy-cut)))))))


  (defret cut-leaves-length-nondecr-of-copy-cut
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecr-of-copy-cut
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (defret cutsdb-ok-of-copy-cut
    (implies (and (cutsdb-ok cutsdb)
                  (cut-leaves-sorted src cutsdb)
                  (cut-leaves-bounded src bound cutsdb)
                  (posp bound)
                  (<= bound (cut-nnodes cutsdb))
                  (<= (nodecut-indicesi (+ -1 bound) cutsdb) (nfix dst))
                  (cut-truth-bounded src cutsdb))
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (e/d (cutsdb-ok) (copy-cut)))))


  (local (defun-sk leaves-truthenv-of-leaves-copy-invar (src dst size cutsdb bitarr)
           (forall bit-idx
                   (equal (leaves-truthenv dst size bit-idx (leaves-copy src size dst cutsdb) bitarr)
                           (leaves-truthenv src size bit-idx cutsdb bitarr)))
           :rewrite :direct))

  (local (in-theory (disable leaves-truthenv-of-leaves-copy-invar)))

  (local (defret leaves-truthenv-of-leaves-copy
           (implies (or (<= (+ (nfix src) (nfix size)) (nfix dst))
                        (<= (nfix dst) (nfix src)))
                    (leaves-truthenv-of-leaves-copy-invar src dst size cutsdb bitarr))
           :hints(("Goal" :in-theory (enable leaves-truthenv leaves-copy)
                   :induct (leaves-copy src size dst cutsdb))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))
                                  (:free (bit-idx cutsdb) (leaves-truthenv src size bit-idx cutsdb bitarr))
                                  (:free (bit-idx cutsdb) (leaves-truthenv dst size bit-idx cutsdb bitarr))))))))

  (defret cut-value-of-copy-cut
    (equal (cut-value dst new-cutsdb bitarr)
           (cut-value src cutsdb bitarr))
    :hints(("Goal" :in-theory (enable cut-value)
            :cases ((< (nfix src) (nfix dst))))))


  (defret cut-leaves-sorted-of-copy-cut
    (implies (cut-leaves-sorted src cutsdb)
             (cut-leaves-sorted dst new-cutsdb))
    :hints(("Goal" :in-theory (enable cut-leaves-sorted)
            :cases ((< (nfix src) (nfix dst))))))

  (defret cut-truth-bounded-of-copy-cut
    (implies (cut-truth-bounded src cutsdb)
             (cut-truth-bounded dst new-cutsdb))
    :hints(("Goal" :in-theory (enable cut-truth-bounded))))

  (defret cut-leaves-lit-idsp-of-copy-cut
    (implies (cut-leaves-lit-idsp src aignet cutsdb)
             (cut-leaves-lit-idsp dst aignet new-cutsdb))
    :hints(("Goal" :in-theory (enable cut-leaves-lit-idsp)
            :cases ((< (nfix src) (nfix dst))))))

  )




(define leaves-merge ((idx0 natp) (size0 natp)
                               (idx1 natp) (size1 natp)
                               (dest-idx natp)
                               cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-leaves-length cutsdb))
              (<= (+ idx1 size1) (cut-leaves-length cutsdb))
              (<= (+ idx0 size0) dest-idx)
              (<= (+ idx1 size1) dest-idx)
              (<= (+ dest-idx (leaves-merge-count idx0 size0 idx1 size1 cutsdb))
                  (cut-leaves-length cutsdb)))
  :guard-hints (("goal" ;; :in-theory (enable cut-leaves-of-update-cut-leavesi)
                 :expand ((leaves-merge-count idx0 size0 idx1 size1 cutsdb))))
  :returns (new-cutsdb)
  :measure (+ (lnfix size1) (lnfix size0))
  (b* (((when (zp size0)) (leaves-copy idx1 size1 dest-idx cutsdb))
       ((when (zp size1)) (leaves-copy idx0 size0 dest-idx cutsdb))
       (node0 (cut-leavesi idx0 cutsdb))
       (node1 (cut-leavesi idx1 cutsdb))
       ((when (eql node0 node1))
        (b* ((cutsdb (update-cut-leavesi dest-idx node0 cutsdb)))
          (leaves-merge (1+ (lnfix idx0)) (1- size0)
                                 (1+ (lnfix idx1)) (1- size1)
                                 (1+ (lnfix dest-idx))
                                 cutsdb)))
       ((when (< node0 node1))
        (b* ((cutsdb (update-cut-leavesi dest-idx node0 cutsdb)))
          (leaves-merge (1+ (lnfix idx0)) (1- size0)
                                 idx1 size1
                                 (1+ (lnfix dest-idx))
                                 cutsdb)))
       (cutsdb (update-cut-leavesi dest-idx node1 cutsdb)))
    (leaves-merge idx0 size0
                           (1+ (lnfix idx1)) (1- size1)
                           (1+ (lnfix dest-idx))
                           cutsdb))
  ///
  ;; (local (in-theory (enable cut-leaves-of-update-cut-leavesi)))

  (defret nth-of-leaves-merge
    (implies (not (equal (nfix n) *cut-leavesi1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defretd nth-cut-leaves-of-leaves-merge
    (implies (and (not (and (<= (nfix dest-idx) (nfix n))
                            (< (nfix n) (+ (nfix dest-idx)
                                           (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))))
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb))))
    :hints(("Goal" :in-theory (enable leaves-merge-count))))

  (defret nth-cut-leaves-of-leaves-merge-weaker
    (implies (< (nfix n) (nfix dest-idx))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb))))
    :hints(("Goal" :in-theory (enable leaves-merge-count))))

  ;; (set-stobj-updater leaves-merge 5)

  (local (Defthm pos-fix-when-zp
           (implies (zp x) (equal (acl2::pos-fix x) 1))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (local (defthm cut-leavesi-of-update-cut-leavesi-split
           (equal (cut-leavesi n (update-cut-leavesi m v cutsdb))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-leavesi n cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (defretd first-element-of-leaves-merge
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (cut-leavesi dest-idx new-cutsdb)
                    (if (zp size1)
                        (if (zp size0)
                            (cut-leavesi dest-idx cutsdb)
                          (cut-leavesi idx0 cutsdb))
                      (if (zp size0)
                          (cut-leavesi idx1 cutsdb)
                        (min (cut-leavesi idx0 cutsdb)
                             (cut-leavesi idx1 cutsdb))))))
    :hints (("Goal" ;; :induct <call>
             :do-not-induct t
             :expand ((:free (size0 size1) <call>)
                      (:free (size0) (leaves-copy idx0 size0 dest-idx cutsdb))
                      (:free (size1) (leaves-copy idx1 size1 dest-idx cutsdb))))))

  (local (in-theory (enable first-element-of-leaves-merge)))

  (local (in-theory (disable ;; range-nat-equiv-open
                             ;; range-nat-equiv-of-update-out-of-range-2
                             acl2::nfix-when-not-natp)))

  ;; (defret first-element-of-leaves-merge
  ;;   (implies (posp size1)
  ;;            (<= (cut-leavesi dest-idx new-cutsdb)
  ;;                (cut-leavesi idx1 cutsdb)))
  ;;   :hints (("Goal" :induct <call>
  ;;            :expand ((:free (size0 size1) <call>)
  ;;                     (leaves-copy idx1 size1 dest-idx cutsdb))))
  ;;   :rule-classes :linear)

  (defret leaves-sorted-of-leaves-merge
    (implies (and (leaves-sorted idx0 size0 cutsdb)
                  (leaves-sorted idx1 size1 cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (leaves-sorted dest-idx (leaves-merge-count idx0 size0 idx1 size1 cutsdb)
                                       new-cutsdb))
    :hints(("Goal" :in-theory (enable leaves-merge-count)
            :induct <call>
            :expand ((:free (size cutsdb) (leaves-sorted dest-idx size cutsdb))
                     (:free (size1 size0) <call>)))
           (acl2::use-termhint
            (b* ((node0 (cut-leavesi idx0 cutsdb))
                 (node1 (cut-leavesi idx1 cutsdb))
                 ((when (eql node0 node1))
                  ''(:expand ((:free (size cutsdb) (leaves-sorted idx0 size cutsdb))
                              (:free (size cutsdb) (leaves-sorted idx1 size cutsdb)))))
                 ((when (< node0 node1))
                  ''(:expand ((:free (size cutsdb) (leaves-sorted idx0 size cutsdb))))))
              ''(:expand ((:free (size cutsdb) (leaves-sorted idx1 size cutsdb))))))))



  (defret cut-leaves-length-of-leaves-merge
    (implies (and (<= (+ (nfix dest-idx)
                         (leaves-merge-count idx0 size0 idx1 size1 cutsdb))
                      (cut-leaves-length cutsdb))
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (cut-leaves-length new-cutsdb) (cut-leaves-length cutsdb)))
    :hints(("Goal" :in-theory (enable leaves-merge-count)
            :induct <call>
            :expand (<call>))))

  (defret cutsdb-ok-of-leaves-merge
    (implies (and (<= (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (nfix dest-idx))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))

  (defret cut-leaves-length-nondecreasing-of-leaves-merge
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (local (defthm leaves-merge-count-is-zero
           (equal (equal 0 (leaves-merge-count idx0 size0 idx1 size1 cutsdb))
                  (and (zp size0) (zp size1)))
           :hints(("Goal" :in-theory (enable leaves-merge-count)))))

  (defretd cut-leaves-length-lower-bound-of-leaves-merge
    (b* ((size (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))
      (implies (and (posp size)
                    (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                    (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
               (<= (+ (nfix dest-idx) size) (cut-leaves-length new-cutsdb))))
    :hints(("Goal" :in-theory (enable cut-leaves-length-lower-bound-of-leaves-copy
                                      leaves-merge-count)
            :induct <call>
            :expand (<call>)))
    :rule-classes :linear)

  (defret leaves-bounded-of-leaves-merge
    (implies (and (leaves-bounded idx0 size0 bound cutsdb)
                  (leaves-bounded idx1 size1 bound cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (leaves-bounded dest-idx
                                        (leaves-merge-count idx0 size0 idx1 size1 cutsdb)
                                        bound
                                        new-cutsdb))
    :hints(("Goal" :in-theory (enable leaves-bounded)
            :induct <call>
            :expand (<call>
                     (:free (size0 size1) (leaves-merge-count idx0 size0 idx1 size1 cutsdb))))))

  (defret leaves-lit-idsp-of-leaves-merge
    (implies (and (leaves-lit-idsp idx0 size0 aignet cutsdb)
                  (leaves-lit-idsp idx1 size1 aignet cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (leaves-lit-idsp dest-idx
                                        (leaves-merge-count idx0 size0 idx1 size1 cutsdb)
                                        aignet
                                        new-cutsdb))
    :hints(("Goal" :in-theory (e/d (leaves-lit-idsp)
                                   (lookup-id-implies-aignet-idp
                                    lookup-id-in-bounds-when-positive))
            :induct <call>
            :expand (<call>
                     (:free (size0 size1) (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))))))


(define leaves-subsetp ((subidx natp) (subsize natp)
                            (idx natp) (size natp)
                            cutsdb)
  :guard (and (<= (+ subidx subsize) (cut-leaves-length cutsdb))
              (<= (+ idx size) (cut-leaves-length cutsdb)))
  ;; Checks whether the cut at subidx (of size subsize) is contained in the one at index idx (of size size)
  :measure (nfix size)
  (b* (((when (zp subsize)) t)
       ((when (zp size)) nil)
       (subdata (cut-leavesi subidx cutsdb))
       (data (cut-leavesi idx cutsdb))
       ((when (< subdata data)) nil)
       ((when (eql subdata data))
        (leaves-subsetp (1+ (lnfix subidx)) (1- subsize)
                            (1+ (lnfix idx)) (1- size)
                            cutsdb)))
    (leaves-subsetp subidx subsize
                        (1+ (lnfix idx)) (1- size)
                        cutsdb))
  ///
  (def-updater-independence-thm leaves-subsetp-updater-independence
    (implies (and (range-nat-equiv subidx subsize (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
                  (range-nat-equiv idx size (nth *cut-leavesi1* new) (nth *cut-leavesi1* old)))
             (equal (leaves-subsetp subidx subsize idx size new)
                    (leaves-subsetp subidx subsize idx size old))))

  (defthm leaves-subsetp-of-leaves-copy
    (implies (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
             (b* ((cutsdb (leaves-copy idx1 size1 dest-idx cutsdb)))
               (leaves-subsetp idx1 size1 dest-idx size1 cutsdb)))
    :hints(("Goal" :in-theory (enable leaves-copy)
            :induct (leaves-copy idx1 size1 dest-idx cutsdb))))

  (fty::deffixequiv leaves-subsetp)

  (local (in-theory (enable first-element-of-leaves-merge)))

  (local (defthm cut-leavesi-of-update-cut-leavesi-split
           (equal (cut-leavesi n (update-cut-leavesi m v cutsdb))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-leavesi n cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local
   (defthm leaves-subsetp-of-leaves-merge-first-lemma
     (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                   (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
              (b* ((size (leaves-merge-count idx0 size0 idx1 size1 cutsdb))
                   (cutsdb (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)))
                (leaves-subsetp idx0 size0 dest-idx size cutsdb)))
     :hints(("Goal" :in-theory (enable leaves-merge
                                       leaves-merge-count
                                       ;; cut-leaves-of-update-cut-leavesi
                                       )
             :induct (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)
             :expand ((leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)
                      (:free (cutsdb) (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))))))

  (defthm leaves-subsetp-of-leaves-merge-first
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
                  (equal (nfix size) (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))
             (b* ((cutsdb (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)))
               (leaves-subsetp idx0 size0 dest-idx size cutsdb)))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                    (leaves-subsetp
                                     leaves-subsetp-of-leaves-merge-first-lemma))
            :use leaves-subsetp-of-leaves-merge-first-lemma)))

  (local
   (defthm leaves-subsetp-of-leaves-merge-second-lemma
     (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                   (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
              (b* ((size (leaves-merge-count idx0 size0 idx1 size1 cutsdb))
                   (cutsdb (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)))
                (leaves-subsetp idx1 size1 dest-idx size cutsdb)))
     :hints(("Goal" :in-theory (enable leaves-merge
                                       leaves-merge-count
                                       ;; cut-leaves-of-update-cut-leavesi
                                       )
             :induct (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)
             :expand ((leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)
                      (:free (cutsdb) (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))))))

  (defthm leaves-subsetp-of-leaves-merge-second
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
                  (equal (nfix size) (leaves-merge-count idx0 size0 idx1 size1 cutsdb)))
             (b* ((cutsdb (leaves-merge idx0 size0 idx1 size1 dest-idx cutsdb)))
               (leaves-subsetp idx1 size1 dest-idx size cutsdb)))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                    (leaves-subsetp
                                     leaves-subsetp-of-leaves-merge-second-lemma))
            :use leaves-subsetp-of-leaves-merge-second-lemma))))



(define merged-leaves-expandmask ((idx0 natp) (size0 natp)
                             (dest-idx natp) (dest-size natp)
                             (bit-idx natp)
                             cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-leaves-length cutsdb))
              (<= (+ dest-idx dest-size) (cut-leaves-length cutsdb))
              (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb))
  :verify-guards nil
  :measure (nfix dest-size)
  :returns (bitmask natp :rule-classes :type-prescription)
  (b* (((when (zp size0)) 0)
       ((unless (mbt (not (zp dest-size)))) 0)
       (data0 (cut-leavesi idx0 cutsdb))
       (destdata (cut-leavesi dest-idx cutsdb))
       ((when (eql data0 destdata))
        (install-bit bit-idx 1
                           (merged-leaves-expandmask (+ 1 (lnfix idx0)) (1- size0)
                                                (+ 1 (lnfix dest-idx)) (1- dest-size)
                                                (+ 1 (lnfix bit-idx))
                                                cutsdb))))
    (merged-leaves-expandmask idx0 size0
                         (+ 1 (lnfix dest-idx)) (1- dest-size)
                         (+ 1 (lnfix bit-idx))
                         cutsdb))
  ///
  (def-updater-independence-thm merged-leaves-expandmask-updater-independence
    (implies (and (range-nat-equiv idx0 size0 (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
                  (range-nat-equiv dest-idx dest-size (nth *cut-leavesi1* new) (nth *cut-leavesi1* old)))
             (equal (merged-leaves-expandmask idx0 size0 dest-idx dest-size bit-idx new)
                    (merged-leaves-expandmask idx0 size0 dest-idx dest-size bit-idx old))))

  (Verify-guards merged-leaves-expandmask
                 :hints (("goal" :in-theory (enable leaves-subsetp))))

  (defret size-of-merged-leaves-expandmask
    (implies (and (natp n)
                  (<= (+ (nfix bit-idx) (nfix dest-size)) n))
             (unsigned-byte-p n bitmask)))





  (local (defret logbitp-early-of-merged-leaves-expandmask
           (implies (< (nfix n) (nfix bit-idx))
                    (not (logbitp n bitmask)))))

  (local (defthm logcdr-when-not-negp
           (implies (not (acl2::negp x))
                    (natp (logcdr x)))
           :rule-classes :type-prescription))

  (local (defthm logcount-of-install-bit
           (implies (and (not (logbitp n x))
                         (not (acl2::negp x)))
                    (equal (logcount (install-bit n 1 x))
                           (+ 1 (logcount x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions
                                              acl2::install-bit**)
                   :induct (logbitp n x)))))


  ;; (local (defthm nth-set-bit-pos-of-logtail
  ;;          (implies (and (equal (loghead n x) 0)
  ;;                        (< (logcount x) (nfix k)))
  ;;                   (equal (nth-set-bit-pos k (logtail n x))
  ;;                          (- (nth-set-bit-pos k x) (- (nfix n)))))
  ;;          :hints(("Goal" :in-theory (enable* truth::nth-set-bit-pos
  ;;                                             bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs)
  ;;                  :induct (logtail n x)
  ;;                  :expand ((nth-set-bit-pos k x))))))


  (defret logcount-of-merged-leaves-expandmask
    (implies (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
             (equal (logcount bitmask)
                    (nfix size0)))
    :hints(("Goal" :in-theory (enable leaves-subsetp)
            :induct <call>)))


  (local (defun induct-n-m-x (n m x)
           (if (zp m)
               (list n x)
             (induct-n-m-x (1- n) (1- m) (logcdr x)))))

  (local (defthm loghead-of-install-bit-same
           (implies (<= (nfix m) (nfix n))
                    (equal (loghead m (install-bit n v x))
                           (loghead m x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::install-bit**)
                   :induct (induct-n-m-x n m x)))))

  (defret loghead-of-merged-leaves-expandmask
    (implies (<= (nfix m) (nfix bit-idx))
             (equal (loghead m bitmask) 0))
    :hints (("goal" :induct <call>)))

  ;; (local
  ;;  (defret lookup-index-permute-stretch-of-merged-leaves-expandmask-lemma
  ;;    (implies (and (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
  ;;                  (<= (nfix size0) (- 4 (nfix bit-idx)))
  ;;                  (<= (nfix idx0) (nfix idx))
  ;;                  (< (nfix idx) (+ (nfix idx0) (nfix size0))))
  ;;             (equal (cut-leavesi (+ (nfix dest-idx)
  ;;                                  (truth::index-permute-stretch bit-idx nil bitmask
  ;;                                                                (- (nfix idx) (nfix idx0))
  ;;                                                                4)) cutsdb)
  ;;                    (cut-leavesi idx cutsdb)))
  ;;    :hints(("Goal" :in-theory (enable* leaves-subsetp
  ;;                                       acl2::arith-equiv-forwarding
  ;;                                       truth::index-permute-stretch
  ;;                                       truth::index-move-up-redef)
  ;;            :induct <call>
  ;;            :expand ((:free (x y) (truth::index-permute-stretch bit-idx nil x y 4)))
  ;;            ;; :expand ((:free (x) (logtail bit-idx x)))
  ;;            )
  ;;           (and stable-under-simplificationp
  ;;                '(:cases ((equal (nfix idx) (nfix idx0)))))
  ;;           )
  ;;    :rule-classes nil))


  (local (defthm 0th-set-bit-pos-of-install-bit
           (implies (equal (loghead n x) 0)
                    (equal (nth-set-bit-pos 0 (install-bit n 1 x))
                           (nfix n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::install-bit**
                                              truth::nth-set-bit-pos)))))

  (local (defthm nth-set-bit-pos-of-install-bit
           (implies (and (equal (loghead (+ 1 (nfix n)) x) 0)
                         (not (zp k)))
                    (equal (nth-set-bit-pos k (install-bit n 1 x))
                           (nth-set-bit-pos (+ -1 (nfix k)) x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::install-bit**
                                              truth::nth-set-bit-pos)
                   :induct (loghead n x)))))

  (local (defthm a-minus-a-plus-b
           (equal (+ a (- a) b)
                  (fix b))))


  (local (defthm nth-set-bit-pos-of-logcdr
           (implies (nth-set-bit-pos n (logcdr x))
                    (equal (nth-set-bit-pos n (logcdr x))
                           (- (nth-set-bit-pos (+ (logcar x) (nfix n)) x)
                              1)))
           :hints (("goal" :expand
                    ((nth-set-bit-pos (+ (logcar x) (nfix n)) x)
                     (nth-set-bit-pos n 0)
                     ;; (nth-set-bit-pos n (logcdr x))
                     ;; (nth-set-bit-pos 0 (logcdr x))
                     (logcount x))))))


  (local (defthm logcount-of-logtail
           (implies (not (acl2::negp x))
                    (equal (logcount (logtail n x))
                           (- (logcount x)
                              (logcount (loghead n x)))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))))


  (local
   (defthm nth-set-bit-pos-of-logtail-under-iff
     (iff (nth-set-bit-pos n (logtail k x))
          (nth-set-bit-pos (+ (logcount (loghead k x)) (nfix n)) x))
     :hints(("Goal" :in-theory (enable* nth-set-bit-pos
                                        bitops::logtail**
                                        bitops::loghead**
                                        bitops::logcount**
                                        bitops::ihsext-inductions)
             :induct (logtail k x)))))

  (local
   (defthm nth-set-bit-pos-of-logtail
     (implies (nth-set-bit-pos n (logtail k x))
              (equal (nth-set-bit-pos n (logtail k x))
                     (- (nth-set-bit-pos (+ (logcount (loghead k x)) (nfix n))
                                         x)
                        (nfix k))))
     :hints (("goal" :induct (logtail k x)
              ;; :expand ((:with logtail&& (logtail k x)))
              :in-theory (enable* bitops::ihsext-inductions
                                  bitops::ihsext-recursive-redefs
                                  bitops::logcount**)
              )
             (and stable-under-simplificationp
                  '(:expand ((nth-set-bit-pos n x))))
             )))


  (local
   (defret lookup-nth-set-bit-pos-of-expandmask-lemma
     (implies (and (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
                   (<= (nfix idx0) (nfix idx))
                   (< (nfix idx) (+ (nfix idx0) (nfix size0))))
              (equal (cut-leavesi (+ (nfix dest-idx)
                                   (nth-set-bit-pos (- (nfix idx) (nfix idx0))
                                                           (logtail bit-idx bitmask))) cutsdb)
                     (cut-leavesi idx cutsdb)))
     :hints(("Goal" :in-theory (enable* leaves-subsetp
                                        acl2::arith-equiv-forwarding)
             :induct <call>
             ;; :expand ((:free (x) (logtail bit-idx x)))
             )
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix idx) (nfix idx0))))))
     :rule-classes nil))

  (defret lookup-nth-set-bit-pos-of-merged-leaves-expandmask
    (implies (and (equal bit-idx 0)
                  (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
                  (< (nfix n) (nfix size0)))
              (equal (cut-leavesi (+ (nfix dest-idx)
                                   (nth-set-bit-pos n bitmask)) cutsdb)
                     (cut-leavesi (+ (nfix idx0) (nfix n)) cutsdb)))
    :hints (("goal" :use ((:instance lookup-nth-set-bit-pos-of-expandmask-lemma
                           (idx (+ (nfix idx0) (nfix n))))))))


  (local (defun nth-set-bit-pos-bound-when-unsigned-byte-p-ind (n k x)
           (if (zp n)
               (list k x)
             (nth-set-bit-pos-bound-when-unsigned-byte-p-ind
              (1- n) (- (nfix k) (logbit 0 x)) (logcdr x)))))

  (local (defthm unsigned-byte-p-logcdr-implies-natp
           (implies (and (unsigned-byte-p n (logcdr x))
                         (integerp x))
                    (natp x))
           :rule-classes :forward-chaining))

  (local (defthm nth-set-bit-pos-bound-when-unsigned-byte-p
           (implies (and (unsigned-byte-p n x)
                         (< (nfix k) (logcount x)))
                    (< (nth-set-bit-pos k x) n))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              logcount)
                   :expand ((nth-set-bit-pos k x))
                   :induct (nth-set-bit-pos-bound-when-unsigned-byte-p-ind n k x)))
           :rule-classes :linear))


  (defret nth-set-bit-pos-bound-of-merged-leaves-expandmask
    (implies (and (< (nfix n) (nfix size0))
                  (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb))
             (< (nth-set-bit-pos n bitmask) (+ (nfix bit-idx) (nfix dest-size))))
    :hints (("goal" :use ((:instance nth-set-bit-pos-bound-when-unsigned-byte-p
                           (k n) (x bitmask) (n (+ (nfix bit-idx) (nfix dest-size)))))
             :in-theory (disable nth-set-bit-pos-bound-when-unsigned-byte-p)
             :do-not-induct t))
    :rule-classes :linear)


  (local (defret logcount-of-loghead-expandmask-lemma
           (implies (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
                    (equal (logcount (loghead (+ (nfix bit-idx) (nfix dest-size) (nfix n)) bitmask))
                           (nfix size0)))
           :hints(("Goal" :in-theory (enable leaves-subsetp
                                             bitops::loghead**)
                   :induct <call>))
           :rule-classes nil))

  (defret logcount-of-loghead-expandmask
    (implies (and (leaves-subsetp idx0 size0 dest-idx dest-size cutsdb)
                  (equal bit-idx 0)
                  (<= (nfix dest-size) (nfix n)))
             (equal (logcount (loghead n bitmask))
                    (nfix size0)))
    :hints (("goal" :use ((:instance logcount-of-loghead-expandmask-lemma
                           (n (- (nfix n) (nfix dest-size)))))
             :in-theory (disable logcount-of-merged-leaves-expandmask
                                 acl2::loghead-identity)
             :do-not-induct t)))
  )









;; (define cuts-add-cut ((cutsdb cutsdb-ok))
;;   :returns (new-cutsdb)
;;   :guard (b* ((
;;   ;; Adds a cut that has already been written in the empty space beyond the last nodecut index.
;;   (b* ((last-index (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;        (new-cut-size (cut-leavesi last-index cutsdb))
;;        (new-last-index (+ 2 (nfix size) last-index)))
;;     (update-nodecut-indicesi (cut-nnodes cutsdb) new-last-index))
;;   ///
;;   (defret cutsdb-ok-of-cuts-add-cut



(define update-nodecut-indicesi$ ((n natp) (v natp) (cutsdb))
  :guard (< n (nodecut-indices-length cutsdb))
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic (update-nodecut-indicesi n v cutsdb)
       :exec (if (unsigned-byte-p 32 v)
                 (update-nodecut-indicesi n v cutsdb)
               (ec-call (update-nodecut-indicesi n v cutsdb)))))

(define update-cut-leavesi$ ((n natp) (v natp) (cutsdb))
  :guard (< n (cut-leaves-length cutsdb))
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic (update-cut-leavesi n v cutsdb)
       :exec (if (unsigned-byte-p 32 v)
                 (update-cut-leavesi n v cutsdb)
               (ec-call (update-cut-leavesi n v cutsdb)))))

;; (define collect-leaves ((data natp)
;;                         (size natp)
;;                         (cutsdb))
;;   :guard (<= (+ data size) (cut-leaves-length cutsdb))
;;   (if (zp size)
;;       nil
;;     (cons (cut-leavesi data cutsdb)
;;           (collect-leaves (1+ (lnfix data)) (1- size) cutsdb))))

;; (include-book "std/strings/hexify" :dir :system)


;; (define print-cut ((cut natp)
;;                    (cutsdb))
;;   :guard (and (< cut (cut-info-length cutsdb))
;;               (<= (+ 4 (* 4 cut)) (cut-leaves-length cutsdb)))
;;   (b* (((cutinfo cutinf) (cut-infoi cut cutsdb)))
;;     (acl2::msg "Cut ~x0: truth ~s1, valid ~x2, score ~x3, leaves ~x4"
;;                (lnfix cut) (str::hexify cutinf.truth)
;;                cutinf.valid cutinf.score (collect-leaves (* 4 (lnfix cut)) cutinf.size cutsdb))))


(define cuts-check-any-contained ((start natp)
                                  (end natp)
                                  (data natp)
                                  (size natp)
                                  (cutsdb cutsdb-ok))
  :guard (and (<= (+ data size) (cut-leaves-length cutsdb))
              (<= start end)
              (<= end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  :returns (cut-is-redundant)
  :measure (nfix (- (nfix end) (nfix start)))
  (b* ((start (lnfix start))
       (end (lnfix end))
       ((when (mbe :logic (zp (- end start))
                   :exec (eql start end)))
        nil)
       (cut-size (cutinfo->size (cut-infoi start cutsdb)))
       (cut-leaves (* 4 start))
       (contained (and (<= cut-size (lnfix size))
                       (leaves-subsetp cut-leaves cut-size data size cutsdb)))
       ;; (- (and contained
       ;;         (cw "Contained: ~x0~%in: ~@1~%"
       ;;             (collect-leaves data size cutsdb)
       ;;             (print-cut start cutsdb))))
       )
    (or contained
        (cuts-check-any-contained (1+ start) end data size cutsdb))))




(define cuts-invalidate-any-contained ((start natp)
                                       (end natp)
                                       (data natp)
                                       (size natp)
                                       (found-acc)
                                       (cutsdb))
  :guard (and (<= (+ data size) (cut-leaves-length cutsdb))
              (<= start end)
              (<= end (cut-info-length cutsdb))
              (<= (* 4 end) (cut-leaves-length cutsdb)))
  :returns (mv found new-cutsdb)
  :measure (nfix (- (nfix end) (nfix start)))
  (b* ((start (lnfix start))
       (end (lnfix end))
       ((when (mbe :logic (zp (- end start))
                   :exec (eql start end)))
        (mv found-acc cutsdb))
       (info  (cut-infoi start cutsdb))
       (cut-size (cutinfo->size info))
       (cut-leaves (* 4 start))
       (contained (and (<= (lnfix size) cut-size)
                       (leaves-subsetp data size cut-leaves cut-size cutsdb)))
       ((unless contained)
        (cuts-invalidate-any-contained (1+ (lnfix start)) end data size found-acc cutsdb))
       ;; (- (cw "Invalidating:~%~@0~%based on: ~x1~%"
       ;;        (print-cut start cutsdb) (collect-leaves data size cutsdb)))
       (cutsdb (update-cut-infoi start (!cutinfo->valid nil info) cutsdb)))
    (cuts-invalidate-any-contained (1+ (lnfix start)) end data size t cutsdb))
  ///
  (defret nth-of-cuts-invalidate-any-contained
    (implies (not (equal (nfix n) *cut-infoi1*))
             (equal (nth n new-cutsdb) (nth n cutsdb))))

  (defret nth-cutinfo-out-of-bounds-of-cuts-invalidate-any-contained
    (implies (or (< (nfix n) (nfix start))
                 (<= (nfix end) (nfix n)))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret cut-info-length-nondecr-of-cuts-invalidate-any-contained
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-of-cuts-invalidate-any-contained
    (implies (<= (nfix end) (cut-info-length cutsdb))
             (equal (cut-info-length new-cutsdb)
                    (cut-info-length cutsdb))))

  (defret nth-cutinfo-mask-equiv-of-cuts-invalidate-any-contained
    (cutinfo-equiv-under-mask (nth n (nth *cut-infoi1* new-cutsdb))
                              (nth n (nth *cut-infoi1* cutsdb))
                              #xfff7ffff)
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix n) (nfix start)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))
            ;; gross, better way?
            (and stable-under-simplificationp
                 '(:in-theory (enable cut-infoi cut-infoi1))))))




(define cut-and ((val0 booleanp)
                 (neg0 bitp)
                 (val1 booleanp)
                 (neg1 bitp))
  :returns (result booleanp :rule-classes :type-prescription)
  (and (xor val0
            (acl2::bit->bool neg0))
       (xor val1
            (acl2::bit->bool neg1))
       t))

(define cut-xor ((val0 booleanp)
                 (neg0 bitp)
                 (val1 booleanp)
                 (neg1 bitp))
  :returns (result booleanp :rule-classes :type-prescription)
  (xor (xor val0
            (acl2::bit->bool neg0))
       (xor val1
            (acl2::bit->bool neg1))))

(define cut-spec ((val0 booleanp)
                  (neg0 bitp)
                  (val1 booleanp)
                  (neg1 bitp)
                  (xor bitp))
  (if (bit->bool xor)
      (cut-xor val0 neg0 val1 neg1)
    (cut-and val0 neg0 val1 neg1)))


(define cuts-merge-aux ((cut0 natp)
                        (neg0 bitp)
                        (cut1 natp)
                        (neg1 bitp)
                        (xor  bitp)
                        ;; (node-cuts-start natp)
                        (cutsdb cutsdb-ok))
  :guard (b* ((next-cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
           (and (not (eql 0 (cut-nnodes cutsdb)))
                (< cut0 next-cut)
                (< cut1 next-cut)
                ;; (<= node-cuts-start next-cut)
                (<= (+ 4 (* 4 next-cut))
                    (cut-leaves-length cutsdb))
                (<= (+ 1 next-cut)
                    (cut-info-length cutsdb))))
  :verify-guards nil
  :returns (mv (updatedp)
               (new-cutsdb))
  (b* ((cut0 (lnfix cut0))
       (data0 (* 4 cut0))
       ((cutinfo info0) (cut-infoi cut0 cutsdb))
       (cut1 (lnfix cut1))
       (data1 (* 4 cut1))
       ((cutinfo info1) (cut-infoi cut1 cutsdb))
       (dest-cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       (dest-data (* 4 dest-cut))
       (dest-size (leaves-merge-count data0 info0.size data1 info1.size cutsdb))
       ((when (< 4 dest-size))
        (mv nil cutsdb))
       (cutsdb (leaves-merge data0 info0.size data1 info1.size dest-data cutsdb))
       (node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
       ((when (cuts-check-any-contained node-cuts-start dest-cut dest-data dest-size cutsdb))
        (mv nil cutsdb))
       (expmask0 (merged-leaves-expandmask data0 info0.size dest-data dest-size 0 cutsdb))
       (expmask1 (merged-leaves-expandmask data1 info1.size dest-data dest-size 0 cutsdb))
       (truth0 (truth::truth-norm4 (logxor (- (bfix neg0)) info0.truth)))
       (truth1 (truth::truth-norm4 (logxor (- (bfix neg1)) info1.truth)))
       (exptruth0 (truth::permute-stretch4 0 0 expmask0 truth0))
       (exptruth1 (truth::permute-stretch4 0 0 expmask1 truth1))
       (dest-truth (if (eql 1 (lbfix xor))
                       (logxor exptruth0 exptruth1)
                     (logand exptruth0 exptruth1)))
       (dest-info (make-cutinfo :truth dest-truth
                                :size dest-size
                                :score 0 ;; BOZO
                                :valid t))
       (cutsdb (update-cut-infoi dest-cut dest-info cutsdb)))
    (mv t cutsdb))
  ///

  (verify-guards cuts-merge-aux
    :hints (("goal" :do-not-induct t)))

  (defret nth-of-cuts-merge-aux
    (implies (and (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *cut-infoi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-cuts-merge-aux
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-cuts-merge-aux
    (implies (and (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret cutsdb-ok-of-cuts-merge-aux
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))

  (defret cut-leaves-length-of-cuts-merge-aux
    (implies (and ;; (cutsdb-ok cutsdb)
                  (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (+ 4 (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (cut-leaves-length cutsdb)))
             (equal (cut-leaves-length new-cutsdb)
                    (cut-leaves-length cutsdb)))
    ;; :hints(("Goal" :in-theory (enable cut-leaves-of-update-cut-leavesi)))
    )

  (defret cut-info-length-of-cuts-merge-aux
    (implies (and ;; (cutsdb-ok cutsdb)
                  ;; (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              ;; (<= (nfix node-cuts-start) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (cut-info-length cutsdb)))
             (equal (cut-info-length new-cutsdb)
                    (cut-info-length cutsdb)))
    ;; :hints(("Goal" :in-theory (enable cut-leaves-of-update-cut-leavesi)))
    )

  (defret cut-leaves-length-nondecreasing-of-cuts-merge-aux
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-cuts-merge-aux
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :hints(("Goal" :in-theory (disable cut-info-length-of-update-cut-infoi)))
    :rule-classes :linear)

  (local (defthm truth-eval-of-consts
           (and (equal (truth::truth-eval 0 env nvars) nil)
                (equal (truth::truth-eval -1 env nvars) t))
           :hints(("Goal" :in-theory (enable truth::truth-eval)))))

  (local (in-theory (disable truth::env-mismatch-when-eval-mismatch)))

  (local (defthm depends-on-implies-bound-when-truth4-deps-bounded
           (implies (and (truth4-deps-bounded n truth)
                         (truth::depends-on v truth 4)
                         (< (nfix v) 4))
                    (< (nfix v) (nfix n)))
           :hints(("Goal" :in-theory (enable* truth4-deps-bounded
                                              acl2::arith-equiv-forwarding)))
           :rule-classes nil))

  (local (defthm truth-evals-similar
           (b* ((mask (merged-leaves-expandmask cut-leaves cut-size dst-data dst-size 0 cutsdb))
                (dst-env (leaves-truthenv dst-data dst-size 0 cutsdb bitarr))
                (cut-env (leaves-truthenv cut-leaves cut-size 0 cutsdb bitarr))
                (shrink-env (truth::env-permute-shrink 0 nil mask dst-env 4)))
             (implies (and (truth4-deps-bounded cut-size cut-truth)
                           (leaves-subsetp cut-leaves cut-size dst-data dst-size cutsdb)
                           (<= (nfix dst-size) 4))
                      (equal (truth::truth-eval cut-truth shrink-env 4)
                             (truth::truth-eval cut-truth cut-env 4))))
           :hints (("goal" :in-theory (enable truth::index-permute-stretch-redef))
                   (acl2::use-termhint
                    (b* ((mask (merged-leaves-expandmask cut-leaves cut-size dst-data dst-size 0 cutsdb))
                         (dst-env (leaves-truthenv dst-data dst-size 0 cutsdb bitarr))
                         (cut-env (leaves-truthenv cut-leaves cut-size 0 cutsdb bitarr))
                         (shrink-env (truth::env-permute-shrink 0 nil mask dst-env 4))
                         (mismatch (truth::env-mismatch cut-truth shrink-env cut-env 4))
                         ((acl2::termhint-seq
                           `'(:use ((:instance truth::env-mismatch-when-eval-mismatch
                                     (truth ,(hq cut-truth))
                                     (env1 ,(hq shrink-env))
                                     (env2 ,(hq cut-env))
                                     (numvars 4))))))
                         ((unless (< mismatch
                                     (nfix cut-size)))
                          `'(:use ((:instance depends-on-implies-bound-when-truth4-deps-bounded
                                    (n ,(hq cut-size)) (truth ,(hq cut-truth))
                                    (v ,(hq mismatch)))))))
                      nil)))
           :otf-flg t))


  (defret truth-value-of-cuts-merge-aux2
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (data (* 4 m))
         ((cutinfo info) (cut-infoi m new-cutsdb))
         (cut0 (nfix cut0))
         ((cutinfo info0) (cut-infoi cut0 cutsdb))
         (data0 (* 4 cut0))
         (cut1 (nfix cut1))
         ((cutinfo info1) (cut-infoi cut1 cutsdb))
         (data1 (* 4 cut1)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval info.truth env 4)
                      (b* ((eval0 (truth::truth-eval info0.truth
                                                     (truth::env-permute-shrink
                                                      0 nil (merged-leaves-expandmask data0 info0.size data info.size 0 new-cutsdb)
                                                      env 4)
                                                     4))
                           (eval1 (truth::truth-eval info1.truth
                                                     (truth::env-permute-shrink
                                                      0 nil (merged-leaves-expandmask data1 info1.size data info.size 0 new-cutsdb)
                                                      env 4)
                                                     4)))
                        (cut-spec eval0 neg0 eval1 neg1 xor)))))
    :hints(("Goal" :in-theory (enable cut-and cut-xor cut-spec))))

  (defret truth-value-of-cuts-merge-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (data (* 4 m))
         ((cutinfo info) (cut-infoi m new-cutsdb))
         (cut0 (nfix cut0))
         ((cutinfo info0) (cut-infoi cut0 cutsdb))
         (data0 (* 4 cut0))
         (cut1 (nfix cut1))
         ((cutinfo info1) (cut-infoi cut1 cutsdb))
         (data1 (* 4 cut1)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval info.truth (leaves-truthenv data info.size 0 new-cutsdb bitarr) 4)
                      (b* ((eval0 (truth::truth-eval info0.truth
                                                     (leaves-truthenv data0 info0.size 0 cutsdb bitarr)
                                                     4))
                           (eval1 (truth::truth-eval info1.truth
                                                     (leaves-truthenv data1 info1.size 0 cutsdb bitarr)
                                                     4)))
                        (cut-spec eval0 neg0 eval1 neg1 xor)))))
    :hints(("Goal" :in-theory (enable cut-and cut-xor cut-spec))))

  (local (defthm truth-eval-of-norm-minus1
           (implies (and (syntaxp (and (quotep x)
                                       (quotep numvars)
                                       (equal (cadr x) (truth::truth-norm -1 (cadr numvars)))))
                         (equal x (truth::truth-norm -1 numvars)))
                    (equal (truth::truth-eval x env numvars) t))))

  (local (defthm depends-on-of-consts
           (implies (< (nfix n) 4)
                    (and (not (truth::depends-on n -1 4))
                         (not (truth::depends-on n 0 4))
                         (not (truth::depends-on n 65535 4))))
           :hints (("goal" :use ((:instance truth::depends-on-witness-correct
                                  (truth -1) (n n) (numvars 4))
                                 (:instance truth::depends-on-witness-correct
                                  (truth 0) (n n) (numvars 4))
                                 (:instance truth::depends-on-witness-correct
                                  (truth 65535) (n n) (numvars 4)))
                    :in-theory (disable truth::depends-on-witness-correct)))))

  (local (defthm truth4-deps-bounded-of-const
           (implies (bitp x)
                    (truth4-deps-bounded n (- x)))
           :hints(("Goal" :in-theory (enable bitp truth4-deps-bounded)
                   :induct (truth4-deps-bounded n (- x))))))


  (defret cut-truth-bounded-of-cuts-merge-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-truth-bounded (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) new-cutsdb)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret cut-leaves-sorted-of-cuts-merge-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-sorted (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) new-cutsdb)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret cut-leaves-bounded-of-cuts-merge-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                    (cutsdb-ok cutsdb)
                    (cut-leaves-bounded cut0 bound cutsdb)
                    (cut-leaves-bounded cut1 bound cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-bounded (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) bound new-cutsdb)))
    :hints(("Goal" :in-theory (enable cut-leaves-bounded))))

  ;; (defret new-data-bounded-of-cuts-merge-aux
  ;;   (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  ;;     (implies (and updatedp
  ;;                   (cutsdb-ok cutsdb)
  ;;                   ;; (cutsdb-cut-bounded cut0 bound cutsdb)
  ;;                   ;; (cutsdb-cut-bounded cut1 bound cutsdb)
  ;;                   (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  ;;              (cut-leaves-bounded m (cut-nnodes cutsdb) new-cutsdb)))
  ;;   :hints(("goal" :in-theory (e/d (cut-leaves-bounded) ()))))

  (defret cut-leaves-lit-ids-of-cuts-merge-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-leaves-lit-idsp cut0 aignet cutsdb)
                    (cut-leaves-lit-idsp cut1 aignet cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-lit-idsp m aignet new-cutsdb)))
    :hints(("goal" :in-theory (e/d (cut-leaves-lit-idsp)
                                   ())))))

;; (trace$ #!acl2 (relieve-hyp :entry (list 'relieve-hyp
;;                                          rune bkptr hyp0 unify-subst
;;                                          ancestors)
;;                             :exit (b* (((list ?step-limit ?wonp ?failure-reason) values))
;;                                     (list 'relieve-hyp wonp failure-reason))))


(define truth-reducemask ((size natp) (bit-idx natp) (truth truth4-p))
  :guard (<= (+ size bit-idx) 4)
  :returns (bitmask natp :rule-classes :type-prescription)
  (b* (((when (zp size)) 0)
       (mask (truth-reducemask (1- size) (1+ (lnfix bit-idx)) truth))
       ((unless (truth::depends-on4 bit-idx truth))
        mask))
    (install-bit bit-idx 1 mask))
  ///
  (local (defthm logcount-of-install-bit-bound
           (implies (natp mask)
                    (<= (logcount (install-bit idx val mask))
                        (+ (bfix val) (logcount mask))))
           :hints(("Goal" :in-theory (enable* bitops::logcount**
                                              bitops::install-bit**
                                              bitops::ihsext-inductions)
                   :induct (loghead idx mask)))
           :rule-classes :linear))

  (defret logcount-of-truth-reducemask
    (<= (logcount bitmask) (nfix size))
    :rule-classes :linear)

  (defret unsigned-byte-4-of-truth-reducemask
    (implies (<= (+ (nfix size) (nfix bit-idx)) 4)
             (unsigned-byte-p 4 bitmask)))

  (defret logbitp-of-truth-reducemask
    (equal (logbitp n bitmask)
           (and (<= (nfix bit-idx) (nfix n))
                (< (nfix n) (+ (nfix bit-idx) (nfix size)))
                (truth::depends-on n truth 4)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
                                       bitops::logbitp-of-install-bit-split))))

  (local (defthm loghead-of-install-bit-lemma
           (implies (posp n)
                    (equal (loghead (+ (nfix bit-idx) n) (install-bit bit-idx val x))
                           (install-bit bit-idx val (loghead (+ (nfix bit-idx) n) x))))
           :hints (("goal" :induct (logbitp bit-idx x)
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        bitops::install-bit**)
                    :expand ((:free (x) (loghead n x)))))))


  (local (defthm loghead-of-install-bit
           (implies (< (nfix bit-idx) (nfix size))
                    (equal (loghead size (install-bit bit-idx val x))
                           (install-bit bit-idx val (loghead size x))))
           :hints (("goal" :use ((:instance loghead-of-install-bit-lemma
                                  (n (- (nfix size) (nfix bit-idx)))))
                    :in-theory (disable loghead-of-install-bit-lemma)))))



  (local (defret loghead-of-truth-reducemask-lemma
           (equal (loghead (+ (nfix size) (nfix bit-idx)) bitmask) bitmask)))

  (defret loghead-of-truth-reducemask
    (implies (<= (+ (nfix size) (nfix bit-idx)) (nfix k))
             (equal (loghead k bitmask) bitmask))
    :hints (("goal" :use ((:instance loghead-of-truth-reducemask-lemma))
             :in-theory (disable loghead-of-truth-reducemask-lemma))))




  (local (defthm logcount-logtail-of-n+1
           (implies (and (natp n) (natp mask))
                    (equal (logcount (acl2::logtail (+ 1 n) mask))
                           (- (logcount (acl2::logtail n mask)) (logbit n mask))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                              bitops::ihsext-inductions
                                              bitops::logcount**)))))

  (local (defthm index-permute-stretch-of-greater-not-in-mask
           (implies (and (<= (logcount (loghead numvars (nfix mask))) (nfix x))
                         (< (nfix x) (nfix numvars)))
                    (not (logbitp (truth::index-permute-stretch
                                   0 count mask x numvars)
                                  (nfix mask))))
           :hints(("Goal" :in-theory (enable truth::index-permute-stretch-redef)))))


  (defthm truth4-deps-bounded-of-permute-shrink
    (b* ((permute-mask (truth-reducemask k 0 x)))
      (implies (and (truth4-deps-bounded k x)
                    ;; (<= (nfix k) (logcount (loghead 4 permute-mask)))
                    (<= (nfix k) 4)
                    (<= (logcount permute-mask) (nfix n)))
               (truth4-deps-bounded n (truth::permute-shrink 0 nil permute-mask x 4))))
    :hints ((acl2::use-termhint
             (b* ((permute-mask (truth-reducemask k 0 x))
                  (perm (truth::permute-shrink 0 nil permute-mask x 4))
                  (witness (truth4-deps-unbounded-witness n perm))
                  ;; (shrink (truth::index-permute-stretch 0 nil permute-mask witness 4))
                  )
               `'(:use ((:instance truth4-deps-unbounded-witness-correct
                         (truth ,(hq perm) ))
                        (:instance truth4-deps-unbounded-witness-lower-bound
                         (truth ,(hq perm)))
                        (:instance truth4-deps-unbounded-witness-upper-bound
                         (truth ,(hq perm)))
                        (:instance truth::depends-on-of-permute-shrink
                         (numvars 4)
                         (n ,(hq witness))
                         (mask ,(hq permute-mask))
                         (truth x))
                        (:instance index-permute-stretch-of-greater-not-in-mask
                         (mask ,(hq permute-mask))
                         (x ,(hq witness))
                         (numvars 4))

                        ;; (:instance index-permute-shrink-upper-bound
                        ;;  (mask permute-mask)
                        ;;  (k k)
                        ;;  (n ,(hq witness)))
                        ;; (:instance logcount-loghead-monotonic
                        ;;  (x permute-mask)
                        ;;  (n n) (m ,(hq witness)))
                        ;; (:instance truth4-deps-bounded-implies-not-depends
                        ;;  (n k) (truth x)
                        ;;  (k ,(hq shrink)))
                        )
                  :in-theory (e/d (;; truth::index-permute-shrink-redef
                                   ;; truth::index-permute-stretch-redef
                                   )
                                  (truth4-deps-unbounded-witness-upper-bound
                                   truth4-deps-unbounded-witness-lower-bound
                                   truth::depends-on-of-permute-shrink
                                   index-permute-stretch-of-greater-not-in-mask
                                   ;; truth4-deps-bounded-implies-not-depends
                                   ))
                  :do-not-induct t))))
    :otf-flg t))


(define leaves-reduce ((read-loc natp) (read-size natp) (write-loc natp)
                         (bit-idx natp) (mask natp) cutsdb)
  :guard (and (<= (+ read-loc read-size) (cut-leaves-length cutsdb))
              (<= write-loc read-loc))
  :measure (nfix read-size)
  :returns (new-cutsdb)
  (b* (((when (zp read-size)) cutsdb)
       ((when (or (not (logbitp bit-idx (lnfix mask)))
                  (<= (lnfix read-loc) (lnfix write-loc))))
        (leaves-reduce (+ 1 (lnfix read-loc))
                         (1- read-size)
                         (+ (logbit bit-idx (lnfix mask)) (lnfix write-loc))
                         (1+ (lnfix bit-idx)) mask cutsdb))
       (cutsdb (update-cut-leavesi write-loc (cut-leavesi read-loc cutsdb) cutsdb)))
    (leaves-reduce (+ 1 (lnfix read-loc))
                     (1- read-size)
                     (+ 1 (lnfix write-loc))
                     (1+ (lnfix bit-idx)) mask cutsdb))
  ///
  (defret nth-of-leaves-reduce
    (implies (not (Equal (nfix n) *cut-leavesi1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  ;; (local (defthm logcount-when-current-bit
  ;;          (implies (and (not (zp read-size))
  ;;                        (logbitp bit-idx mask)
  ;;                        (natp mask))
  ;;                   (equal (logcount (loghead read-size (logtail bit-idx mask)))
  ;;                          (+ 1 (logcount (loghead (+ -1 read-size)
  ;;                                                        (logtail (+ 1 (nfix bit-idx)) mask))))))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs
  ;;                                             bitops::logcount**)))))

  ;; (local (defthm logcount-when-not-current-bit
  ;;          (implies (and (not (zp read-size))
  ;;                        (not (logbitp bit-idx mask))
  ;;                        (natp mask))
  ;;                   (equal (logcount (loghead read-size (logtail bit-idx mask)))
  ;;                          (logcount (loghead (+ -1 read-size)
  ;;                                                   (logtail (+ 1 (nfix bit-idx)) mask)))))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs
  ;;                                             bitops::logcount**)))))

  (local (defthm loghead-of-logtail
           (equal (loghead n (logtail m x))
                  (logtail m (loghead (+ (nfix n) (nfix m)) x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (in-theory (disable bitops::logtail-of-loghead)))

  ;; (local (defthmd nth-cut-leavesi-of-update-cut-leavesi-split
  ;;          (equal (nth n (nth *cut-leavesi1* (update-cut-leavesi m v x)))
  ;;                 (if (equal (nfix n) (nfix m))
  ;;                     v
  ;;                   (nth n (nth *cut-leavesi1* x))))
  ;;          :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
  ;;                                             update-cut-leavesi)))))



  (local (Defthm logtail-not-0-when-logbitp
           (implies (logbitp n x)
                    (not (equal 0 (logtail n x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  ;; (local (in-theory (disable truth::nth-set-bit-pos-of-logtail)))

  (local (defthm 0th-set-bit-pos-of-logtail-when-logbitp
           (implies (logbitp bit-idx mask)
                    (equal (nth-set-bit-pos 0 (logtail bit-idx mask))
                           0))
           :hints (("goal" :expand ((:with truth::nth-set-bit-pos
                                     (nth-set-bit-pos 0 (logtail bit-idx mask))))))))

  (local (defthmd logtail-expand
           (equal (logtail n x)
                  (logcons (logbit n x) (logtail (+ 1 (nfix n)) x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm 0th-set-bit-pos-of-logtail-when-not-logbitp
           (implies (and (not (logbitp bit-idx mask))
                         (natp mask)
                         (< 0 (logcount (logtail bit-idx mask))))
                    (equal (nth-set-bit-pos 0 (logtail bit-idx mask))
                           (+ 1 (nth-set-bit-pos 0 (logtail (+ 1 (nfix bit-idx)) mask)))))
           :hints (("goal" :expand ((:with truth::nth-set-bit-pos
                                     (nth-set-bit-pos 0 (logtail bit-idx mask))))
                    :use ((:instance logtail-expand (n bit-idx) (x mask)))
                    :in-theory (e/d (acl2::logcount**) ())))))

  ;; (local (defthm logcount-of-logtail
  ;;          (implies (not (acl2::negp x))
  ;;                   (equal (logcount (logtail n x))
  ;;                          (- (logcount x)
  ;;                             (logcount (loghead n x)))))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs
  ;;                                             bitops::logcount**)))))


  (local (defthm logcount-when-current-bit-tail
           (implies (and (logbitp bit-idx mask)
                         (natp mask))
                    (equal (logcount (logtail bit-idx mask))
                           (+ 1 (logcount (logtail (+ 1 (nfix bit-idx)) mask)))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))))

  (local (defthm logcount-when-not-current-bit-tail
           (implies (and (not (logbitp bit-idx mask))
                         (natp mask))
                    (equal (logcount (logtail bit-idx mask))
                           (logcount (logtail (+ 1 (nfix bit-idx)) mask))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))))

  (local (defthm logcount-when-current-bit-head
           (implies (and (logbitp bit-idx mask)
                         (natp mask))
                    (equal (logcount (loghead bit-idx mask))
                           (+ -1 (logcount (loghead (+ 1 (nfix bit-idx)) mask)))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))))

  (local (defthm logcount-when-not-current-bit-head
           (implies (and (not (logbitp bit-idx mask))
                         (natp mask))
                    (equal (logcount (loghead (+ 1 (nfix bit-idx)) mask))
                           (logcount (loghead bit-idx mask))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))))

  (local (defthm nth-set-bit-pos-of-logtail-when-logbitp
           (implies (and (logbitp bit-idx mask)
                         (not (zp n))
                         (natp mask)
                         (< (nfix n) (logcount (logtail bit-idx mask))))
                    (equal (nth-set-bit-pos n (logtail bit-idx mask))
                           (+ 1 (nth-set-bit-pos (1- n) (logtail (+ 1 (nfix bit-idx)) mask)))))
           :hints(("Goal"
                   :expand ((nth-set-bit-pos n (logtail bit-idx mask))
                            )))))

  (local (defthmd logtail-plus1-when-zero
           (implies (equal (logtail n x) 0)
                    (equal (logtail (+ 1 (nfix n)) x) 0))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm nth-set-bit-pos-of-logtail-when-not-logbitp
           (implies (and (not (logbitp bit-idx mask))
                         (not (zp n))
                         (natp mask)
                         (< (nfix n) (logcount (logtail bit-idx mask))))
                    (equal (nth-set-bit-pos n (logtail bit-idx mask))
                           (+ 1 (nth-set-bit-pos n (logtail (+ 1 (nfix bit-idx)) mask)))))
           :hints(("Goal"
                   :in-theory (enable logtail-plus1-when-zero)
                   :expand ((nth-set-bit-pos n (logtail bit-idx mask)))))))

  ;; (local (in-theory (disable truth::logcount-of-logtail)))

  (local (defthm logcount-of-loghead
           (implies (natp x)
                    (<= (logcount (loghead n x)) (logcount x)))
           :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs
                                               bitops::logcount**)))
           :rule-classes :linear))



  (local (defthm cut-leavesi-of-update-cut-leavesi-split
           (equal (cut-leavesi n (update-cut-leavesi m v x))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-leavesi n x)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local (defthm plus-minus
           (equal (+ a (- a) x)
                  (fix x))))


  (defthm nth-set-bit-pos-of-count
    (implies (and (logbitp bit-idx mask)
                  (natp mask))
             (equal (nth-set-bit-pos (logcount (loghead bit-idx mask))
                                     mask)
                    (nfix bit-idx)))
    :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                     bitops::ihsext-recursive-redefs
                                     nth-set-bit-pos
                                     ;; truth::nth-set-bit-pos-when-logcount
                                     )
                                    (logcount-when-current-bit-head))
            :induct (logbitp bit-idx mask))))

  (local (defthm nth-set-bit-pos-of-count-1-of-plus-1
           (implies (and (logbitp bit-idx mask)
                         (natp mask))
                    (equal (nth-set-bit-pos (+ -1 (logcount (loghead (+ 1 (nfix bit-idx)) mask)))
                                                   mask)
                           (nfix bit-idx)))
           :hints (("goal" :use nth-set-bit-pos-of-count
                    :in-theory (disable nth-set-bit-pos-of-count)))))

  (local (defthm truth-when-gte-logcount
           (implies (and (<= (logcount x) (nfix n))
                         (natp x))
                    (not (nth-set-bit-pos n x)))
           :hints(("Goal" :in-theory (e/d (nth-set-bit-pos
                                           acl2::logcount**))
                   :induct (nth-set-bit-pos n x)
                   :expand ((:with truth::nth-set-bit-pos
                             (nth-set-bit-pos n x)))))))

  ;; (local (defthm nth-set-bit-pos-of-logtail
  ;;          (implies (and (natp x))
  ;;                   (equal (nth-set-bit-pos n (logtail k x))
  ;;                          (and (< (nfix n) (logcount (logtail k x)))
  ;;                               (- (nth-set-bit-pos (+ (logcount (loghead k x)) (nfix n))
  ;;                                                   x)
  ;;                                  (nfix k)))))))

  (local (defthm dumb
           (implies (and (acl2::maybe-natp x)
                         (<= j k))
                    (not (equal j (+ 1 k x))))
           :hints(("Goal" :in-theory (enable acl2::maybe-natp)))))

  (defret nth-cut-leaves-of-leaves-reduce
    (implies (not (and (<= (nfix write-loc) (nfix n))
                       (< (nfix n) (+ (nfix write-loc) (logcount (loghead read-size (logtail bit-idx (nfix mask))))))))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb))))
    :hints (("goal" :induct t :in-theory (enable* acl2::bool->bit
                                                  ;; nth-cut-leavesi-of-update-cut-leavesi-split
                                                  ;; cut-leaves-of-update-cut-leavesi
                                                  acl2::arith-equiv-forwarding))
            (and stable-under-simplificationp
                 '(:in-theory (enable ;; nth-cut-leavesi-of-update-cut-leavesi-split
                                      logcount-loghead-monotonic)))
            ;; (and stable-under-simplificationp
            ;;      '(:expand ((logtail bit-idx (nfix mask))
            ;;                 (logtail 1 (nfix mask))
            ;;                 (:free (x) (loghead read-size x))
            ;;                 (:free (a b) (logcount (logcons a b))))))
            ))

  ;; for fixequiv hint
  ;; (set-stobj-updater leaves-reduce 5)


  (defret cut-leaves-entry-of-leaves-reduce
    (implies (and (<= (nfix write-loc) (nfix read-loc))
                  (<= (nfix write-loc) (nfix n))
                  (< (nfix n) (+ (nfix write-loc) (logcount (loghead read-size (logtail bit-idx (nfix mask)))))))
             (equal (cut-leavesi n new-cutsdb)
                    (cut-leavesi (+ (nfix read-loc)
                                  (nth-set-bit-pos (- (nfix n) (nfix write-loc))
                                                          (loghead read-size (logtail bit-idx (nfix mask)))))
                               cutsdb)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit))
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix n) (nfix write-loc)))))))



  (defret cut-leaves-length-of-leaves-reduce
    (implies (<= (+ (nfix write-loc) (nfix read-size)) (cut-leaves-length cutsdb))
             (equal (cut-leaves-length new-cutsdb)
                    (cut-leaves-length cutsdb))))


  (defret cutsdb-ok-of-leaves-reduce
    (implies (and (<= (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (nfix write-loc))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))


  (local (in-theory (disable (:d leaves-reduce))))

  (local (defthmd leaves-sorted-implies-order
           (implies (and (leaves-sorted idx size cutsdb)
                         (< (nfix idx) (nfix idx2))
                         (< (nfix idx2) (+ (nfix idx) (nfix size))))
                    (< (cut-leavesi idx cutsdb) (cut-leavesi idx2 cutsdb)))
           :hints(("Goal" :in-theory (enable leaves-sorted)))))

  (local (defthm leaves-sorted-implies-order-rw
           (implies (and (leaves-sorted idx size cutsdb)
                         (<= (nfix idx) (nfix idx2))
                         (case-split (< (nfix idx2) (+ (nfix idx) (nfix size))))
                         (< (cut-leavesi idx1 cutsdb) (cut-leavesi idx cutsdb)))
                    (< (cut-leavesi idx1 cutsdb) (cut-leavesi idx2 cutsdb)))
           :hints (("goal" :use leaves-sorted-implies-order
                    :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))


  (local (defun nth-set-bit-pos-upper-bound-ind (k n x)
           (if (zp n)
               (list k x)
             (if (logbitp 0 x)
                 (nth-set-bit-pos-upper-bound-ind (1- (nfix k)) (1- n) (logcdr x))
               (nth-set-bit-pos-upper-bound-ind k (1- n) (logcdr x))))))

  (local (defthmd nth-set-bit-pos-upper-bound
           (implies (and (unsigned-byte-p n x)
                         (< (nfix k) (logcount x)))
                    (< (nth-set-bit-pos k x) (nfix n)))
           :hints (("goal" :induct (nth-set-bit-pos-upper-bound-ind k n x)
                    :in-theory (enable* bitops::ihsext-recursive-redefs
                                        ;; truth::nth-set-bit-pos-when-logcount
                                        )
                    :expand ((nth-set-bit-pos k x))))))

  (local (defthm nth-set-bit-pos-upper-bound-of-logtail-loghead
           (implies (< (nfix k) (logcount (logtail n (loghead m x))))
                    (< (nth-set-bit-pos k (logtail n (loghead m x)))
                       (- (nfix m) (nfix n))))
           :hints (("goal" :use ((:instance nth-set-bit-pos-upper-bound
                                  (n (- (nfix m) (nfix n)))
                                  (x (logtail n (loghead m x)))))
                    :cases ((<= (nfix n) (nfix m)))
                    :in-theory (e/d (bitops::logtail-of-loghead)
                                    (loghead-of-logtail))))
           :rule-classes :linear))


  (local (defret leaves-sorted-of-leaves-reduce-lemma
           (implies (and (leaves-sorted read-loc read-size cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (leaves-sorted
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 leaves-sorted)))))


  (defret leaves-sorted-of-leaves-reduce
    (implies (and (leaves-sorted read-loc read-size cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (leaves-sorted write-loc size new-cutsdb))
    :hints (("goal" :use leaves-sorted-of-leaves-reduce-lemma
             :in-theory (disable leaves-sorted-of-leaves-reduce-lemma))))

  (local (defret leaves-bounded-of-leaves-reduce-lemma
           (implies (and (leaves-bounded read-loc read-size bound cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (leaves-bounded
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     bound
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 leaves-bounded)))))

  (defret leaves-bounded-of-leaves-reduce
    (implies (and (leaves-bounded read-loc read-size bound cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (leaves-bounded write-loc size bound new-cutsdb))
    :hints (("goal" :use leaves-bounded-of-leaves-reduce-lemma
             :in-theory (disable leaves-bounded-of-leaves-reduce-lemma))))

  (local (defret leaves-lit-idsp-of-leaves-reduce-lemma
           (implies (and (leaves-lit-idsp read-loc read-size aignet cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (leaves-lit-idsp
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     aignet
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 leaves-lit-idsp)))))

  (defret leaves-lit-idsp-of-leaves-reduce
    (implies (and (leaves-lit-idsp read-loc read-size aignet cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (leaves-lit-idsp write-loc size aignet new-cutsdb))
    :hints (("goal" :use leaves-lit-idsp-of-leaves-reduce-lemma
             :in-theory (disable leaves-lit-idsp-of-leaves-reduce-lemma))))

  (defret cut-leaves-length-nondecreasing-of-leaves-reduce
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :hints (("goal" :induct <call>
             :expand ((:free (read-size) <call>))))
    :rule-classes :linear))


;; Ranking of cuts: Keep a smaller cut if it's available.  Otherwise, heavily
;; penalize leaves that have few references.
(define cut-score-aux ((start natp) (size natp) (refcounts) (cutsdb))
  :guard (and (<= (+ start size) (cut-leaves-length cutsdb))
              (leaves-bounded start size (u32-length refcounts) cutsdb))
  :measure (nfix size)
  :returns (score natp :rule-classes :type-prescription)
  :verify-guards nil
  (b* (((when (zp size)) 0)
       (leaf (cut-leavesi start cutsdb))
       (nrefs ;;(if (< leaf (u32-length refcounts))
                  (get-u32 leaf refcounts))
                ;;0))
       (leaf-score (case nrefs
                     (0 0)
                     (1 8)
                     (2 12)
                     (3 14)
                     (t 15))))
    (+ leaf-score (cut-score-aux (1+ (lnfix start)) (1- size) refcounts cutsdb)))
  ///
  (verify-guards cut-score-aux
    :hints (("goal" :in-theory (enable leaves-bounded))))

  (defret cut-score-aux-bound
    (<= score (* 15 (nfix size)))
    :rule-classes :linear))

(define cut-refcount ((start natp) (size natp) (refcounts) (cutsdb))
  :guard (and (<= (+ start size) (cut-leaves-length cutsdb))
              (leaves-bounded start size (u32-length refcounts) cutsdb))
  :measure (nfix size)
  :returns (score natp :rule-classes :type-prescription)
  :verify-guards nil
  (b* (((when (zp size)) 0)
       (leaf (cut-leavesi start cutsdb))
       (nrefs ;;(if (< leaf (u32-length refcounts))
                  (get-u32 leaf refcounts))
                ;;0))
       )
    (+ nrefs (cut-refcount (1+ (lnfix start)) (1- size) refcounts cutsdb)))
  ///
  (verify-guards cut-refcount
    :hints (("goal" :in-theory (enable leaves-bounded)))))

(define cut-onerefcount ((start natp) (size natp) (refcounts) (cutsdb))
  :guard (and (<= (+ start size) (cut-leaves-length cutsdb))
              (leaves-bounded start size (u32-length refcounts) cutsdb))
  :measure (nfix size)
  :returns (score natp :rule-classes :type-prescription)
  :verify-guards nil
  (b* (((when (zp size)) 0)
       (leaf (cut-leavesi start cutsdb))
       (nrefs ;;(if (< leaf (u32-length refcounts))
                  (get-u32 leaf refcounts))
                ;;0))
       )
    (+ (if (eql nrefs 1) 1 0) (cut-onerefcount (1+ (lnfix start)) (1- size) refcounts cutsdb)))
  ///
  (verify-guards cut-onerefcount
    :hints (("goal" :in-theory (enable leaves-bounded))))

  (defret cut-onerefcount-bound
    (<= score (nfix size))
    :rule-classes :linear))


(define cut-has-unreferenced ((start natp) (size natp) (refcounts) (cutsdb))
  :guard (and (<= (+ start size) (cut-leaves-length cutsdb))
              (leaves-bounded start size (u32-length refcounts) cutsdb))
  :guard-hints (("goal" :in-theory (enable leaves-bounded)))
  :measure (nfix size)
  (b* (((when (zp size)) nil)
       (leaf (cut-leavesi start cutsdb))
       (nrefs ;;(if (< leaf (u32-length refcounts))
                  (get-u32 leaf refcounts))
                ;;0))
       )
    (or (eql nrefs 0)
        (cut-has-unreferenced (1+ (lnfix start)) (1- size) refcounts cutsdb))))

(define cut-score((cut natp)
                   (refcounts)
                   (cutsdb cutsdb-ok))
  :guard (and (< cut (cut-info-length cutsdb))
              (<= (+ 4 (* 4 cut)) (cut-leaves-length cutsdb))
              (cut-leaves-bounded cut (cut-nnodes cutsdb) cutsdb)
              (<= (cut-nnodes cutsdb) (u32-length refcounts)))
  ;; BOZO bounds checking on refcounts because we don't have the invariant that
  ;; leaves are bounded
  :returns (score natp :rule-classes :type-prescription)
  :verify-guards nil
  ;; (b* (((cutinfo info) (cut-infoi cut cutsdb))
  ;;      ((when (< info.size 2)) 1001)
  ;;      (refcount (min 1000 (cut-refcount (* 4 (lnfix cut)) info.size refcounts cutsdb)))
  ;;      (onescount (cut-onerefcount (* 4 (lnfix cut)) info.size refcounts cutsdb))
  ;;      ((when (< 3 onescount))
  ;;       (- 5 onescount)))
  ;;   refcount)
  (b* (((cutinfo info) (cut-infoi cut cutsdb)))
    (+ (cut-score-aux (* 4 (lnfix cut)) info.size refcounts cutsdb)
       (case info.size
         (0 1000)
         (1 900)
         (2 700)
         (3 400)
         (t 0))))
  ///
  (verify-guards cut-score
    :hints (("goal" :in-theory (enable cut-leaves-bounded
                                       leaves-bounded-when-bounded-lesser))))

  (defret cut-score-bound
    (<= score 1001)
    :rule-classes :linear)

  (defret size-of-cut-score
    (unsigned-byte-p 12 score)
    :hints(("Goal" :in-theory (e/d (unsigned-byte-p)
                                   (cut-score))))))


(define cut-reduce ((refcounts)
                    (cutsdb cutsdb-ok))
  :guard (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              ((unless (and (< m (cut-info-length cutsdb))
                            (<= (+ 4 (* 4 m)) (cut-leaves-length cutsdb))))
               nil))
           (and (cut-leaves-sorted m cutsdb)
                (cut-leaves-bounded m (cut-nnodes cutsdb) cutsdb)
                (<= (cut-nnodes cutsdb) (u32-length refcounts))))
           ;;    (size (cut-leavesi m cutsdb))
           ;;    ((unless (<= (cut-next m cutsdb) (cut-leaves-length cutsdb))) nil)
           ;;    (truth (cut-leavesi (+ 1 m) cutsdb))
           ;;    (data (+ 2 m)))
           ;; (and (<= size 4)
           ;;      (truth4-p truth)
           ;;      (truth4-deps-bounded size truth)
  ;;      (cut-leaves-sorted data size cutsdb)))
  :prepwork ((local (defthm unsigned-byte-p-when-natp
                      (implies (and (natp x)
                                    (< x (expt 2 32)))
                               (unsigned-byte-p 32 x))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p))))))
  :guard-hints (("goal" :in-theory (enable cut-leaves-bounded)))
  :returns (new-cutsdb)
  (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       ((cutinfo info) (cut-infoi m cutsdb))
       (mask (truth-reducemask info.size 0 info.truth))
       ((when (eql mask (loghead info.size -1)))
        ;; No reduction -- just score
        (b* ((score (cut-score m refcounts cutsdb))
             ;; (- (acl2::sneaky-incf score))
             (info2 (!cutinfo->score score info)))
          (update-cut-infoi m info2 cutsdb)))
       (new-size (logcount mask))
       (new-truth (truth::permute-shrink4 0 0 mask info.truth))
       (cutsdb (leaves-reduce (* 4 m) info.size (* 4 m) 0 mask cutsdb))
       (info1 (make-cutinfo :size new-size
                            :truth new-truth
                            :score 0
                            :valid t))
       (cutsdb (update-cut-infoi m info1 cutsdb))
       (score (cut-score m refcounts cutsdb))
       ;; (- (acl2::sneaky-incf score))
       (info2 (!cutinfo->score score info1)))
    (update-cut-infoi m info2 cutsdb))
  ///
  (defret cutsdb-ok-of-cut-reduce
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))

  (local (defthm logcount-loghead-less-when-logbitp
           (implies (and (logbitp n x)
                         (natp x))
                    (< (logcount (loghead n x)) (logcount x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::logcount**)))
           :rule-classes (:rewrite :linear)))

  (local (defthm logcount-logheads-less-when-logbitp
           (implies (and (logbitp n x)
                         (< (nfix n) (nfix m))
                         (natp x))
                    (< (logcount (loghead n x)) (logcount (loghead m x))))
           :hints (("goal" :use ((:instance logcount-loghead-less-when-logbitp
                                  (x (loghead m x))))
                    :in-theory (disable logcount-loghead-less-when-logbitp)))
           :rule-classes (:rewrite :linear)))


  (local (defthm nth-set-bit-pos-of-logcount-loghead-when-logbitp
           (implies (and (logbitp n x)
                         (< (nfix n) (nfix m))
                         (natp x))
                    (equal (nth-set-bit-pos (logcount (loghead n x)) (loghead m x))
                           (nfix n)))
           :hints (("goal" :use ((:instance nth-set-bit-pos-of-count
                                  (mask (loghead m x))
                                  (bit-idx n)))
                    :in-theory (disable nth-set-bit-pos-of-count)))))

  ;; (local (defthm a-minus-a-plus-b
  ;;          (equal (+ a (- a) b)
  ;;                 (fix b))))

  ;; (local (defthm logcount-of-loghead-plus-1
  ;;          (implies (natp n)
  ;;                   (equal (logcount (loghead (+ 1 n) x))
  ;;                          (+ (logbit n x) (logcount (loghead n x)))))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs
  ;;                                             bitops::logcount**)))))



  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (local (in-theory (enable (:rewrite logcount-loghead-monotonic))))

  (local (defthm truth-evals-similar
           (b* ((mask (truth-reducemask cut-size 0 truth))
                (orig-env (leaves-truthenv data cut-size 0 cutsdb bitarr))
                (new-cutsdb (leaves-reduce data cut-size data 0 mask cutsdb))
                (cut-env (leaves-truthenv data (logcount mask) 0 new-cutsdb bitarr))
                (stretch-env (truth::env-permute-stretch 0 nil mask cut-env 4)))
             (implies (and (truth4-deps-bounded cut-size truth)
                           (<= (nfix cut-size) 4))
                      (equal (truth::truth-eval truth stretch-env 4)
                             (truth::truth-eval truth orig-env 4))))
           :hints (("goal" :in-theory (enable truth::index-permute-shrink-redef))
                   (acl2::use-termhint
                    (b* ((mask (truth-reducemask cut-size 0 truth))
                         (orig-env (leaves-truthenv data cut-size 0 cutsdb bitarr))
                         (new-cutsdb (leaves-reduce data cut-size data 0 mask cutsdb))
                         (cut-env (leaves-truthenv data (logcount mask) 0 new-cutsdb bitarr))
                         (stretch-env (truth::env-permute-stretch 0 nil mask cut-env 4))
                         (mismatch (truth::env-mismatch truth stretch-env orig-env 4))
                         ((acl2::termhint-seq
                           `'(:use ((:instance truth::env-mismatch-when-eval-mismatch
                                     (truth ,(hq truth))
                                     (env1 ,(hq stretch-env))
                                     (env2 ,(hq orig-env))
                                     (numvars 4))))))
                         ((unless (< mismatch
                                     (nfix cut-size)))
                          `'(:use ((:instance depends-on-implies-bound-when-truth4-deps-bounded
                                    (n ,(hq cut-size)) (truth ,(hq truth))
                                    (v ,(hq mismatch))))))
                         )
                      nil)))
           :otf-flg t))


  (defret truth-value-of-cut-reduce
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ((cutinfo new) (cut-infoi m new-cutsdb))
         ((cutinfo old) (cut-infoi m cutsdb))
         (data (* 4 m)))
      (implies (and ;; (cutsdb-ok cutsdb)
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-truth-bounded m cutsdb)
                    (cut-leaves-sorted m cutsdb)
                    ;; (<= old-size 4)
                    ;; (truth4-deps-bounded old-size old-truth)
                    )
               (equal (truth::truth-eval new.truth (leaves-truthenv data new.size 0 new-cutsdb bitarr) 4)
                      (truth::truth-eval old.truth (leaves-truthenv data old.size 0 cutsdb bitarr) 4)))))

  (defret cut-leaves-sorted-of-cut-reduce
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-leaves-sorted m cutsdb))
               (cut-leaves-sorted m new-cutsdb)))
    :hints(("Goal" :in-theory (enable cut-leaves-sorted))))

  (defret cut-truth-bounded-of-cut-reduce
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-truth-bounded m cutsdb))
               (cut-truth-bounded m new-cutsdb)))
    :hints(("Goal" :in-theory (enable cut-truth-bounded))))

  (defret cut-leaves-bounded-of-cut-reduce
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-leaves-bounded m bound cutsdb))
               (cut-leaves-bounded m bound new-cutsdb)))
    :hints(("Goal" :in-theory (enable cut-leaves-bounded))))

  ;; (defret new-data-bounded-of-cut-reduce
  ;;   (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
  ;;        ;; (size (cut-leavesi m new-cutsdb))
  ;;        ;; (data (+ 2 m))
  ;;        ;; (truth (cut-leavesi (+ 1 m) new-cutsdb))
  ;;        ;; (old-size (cut-leavesi m cutsdb))
  ;;        ;; (old-truth (cut-leavesi (+ 1 m) cutsdb))
  ;;        )
  ;;     (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (cutsdb-cut-bounded m bound cutsdb)
  ;;                   (cutsdb-ok cutsdb)
  ;;                   ;; (<= old-size 4)
  ;;                   ;; (truth4-p old-truth)
  ;;                   ;; (truth4-deps-bounded old-size old-truth)
  ;;                   ;; (cut-leaves-sorted data old-size cutsdb)
  ;;                   ;; (cutsdb-ok cutsdb)
  ;;                   )
  ;;              (cutsdb-cut-bounded m bound new-cutsdb)
  ;;              ;; (and (<= size 4)
  ;;              ;;      (truth4-p truth)
  ;;              ;;      (truth4-deps-bounded size truth)
  ;;              ;;      (cut-leaves-sorted data size new-cutsdb))
  ;;              ))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-cut-bounded))))

  (defret cut-leaves-lit-idsp-of-cut-reduce
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cut-leaves-lit-idsp m aignet cutsdb))
               (cut-leaves-lit-idsp m aignet new-cutsdb)))
    :hints(("Goal" :in-theory (enable cut-leaves-lit-idsp))))

  (defret nth-of-cut-reduce
    (implies (and (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *cut-infoi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-cut-reduce
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-cut-reduce
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret cut-leaves-length-of-cut-reduce
    (implies (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (<= (+ 4 (* 4 m)) (cut-leaves-length cutsdb)))
             (equal (cut-leaves-length new-cutsdb)
                    (cut-leaves-length cutsdb))))

  (defret cut-info-length-of-cut-reduce
    (implies (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (< m (cut-info-length cutsdb)))
             (equal (cut-info-length new-cutsdb)
                    (cut-info-length cutsdb))))

  (defret cut-leaves-length-nondecreasing-of-cut-reduce
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-cut-reduce
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :hints(("Goal" :in-theory (disable CUT-INFO-LENGTH-OF-UPDATE-CUT-INFOI)))
    :rule-classes :linear)

  )


(define cuts-merge ((cut0 natp)
                    (neg0 bitp)
                    (cut1 natp)
                    (neg1 bitp)
                    (xor bitp)
                    ;; (node-cuts-start natp)
                    (refcounts)
                    (cutsdb cutsdb-ok))
  :guard (and (not (eql 0 (cut-nnodes cutsdb)))
              (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              ;; (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= (+ 4 (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                  (cut-leaves-length cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (cut-info-length cutsdb))
              (<= (cut-nnodes cutsdb) (u32-length refcounts))
              )
  :returns (mv (updatedp)
               (new-cutsdb))
  (b* (((mv updatedp cutsdb) (cuts-merge-aux cut0 neg0 cut1 neg1 xor cutsdb))
       ((unless updatedp) (mv nil cutsdb))
       (cutsdb (cut-reduce refcounts cutsdb)))
    (mv t cutsdb))
  ///


  (defret nth-of-cuts-merge
    (implies (and (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *cut-infoi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-cuts-merge
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-cuts-merge
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  ;; (set-stobj-updater cuts-merge 4 1)

  (defret cutsdb-ok-of-cuts-merge
    (implies (and (cutsdb-ok cutsdb)
                  (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-ok new-cutsdb)))

  ;; (local (defthm cut-leaves-length-of-update-cut-leavesi
  ;;          (implies (< (nfix n) (cut-leaves-length cutsdb))
  ;;                   (equal (cut-leaves-length (update-cut-leavesi n val cutsdb))
  ;;                          (cut-leaves-length cutsdb)))))

  (defret cut-leaves-length-of-cuts-merge
    (implies (and (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (+ 4 (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (cut-leaves-length cutsdb)))
             (equal (cut-leaves-length new-cutsdb)
                    (cut-leaves-length cutsdb))))

  ;; (defret cuts-merge-when-not-updated
  ;;   (implies (not updatedp)
  ;;            (equal new-cutsdb cutsdb)))


  ;; (local (defret new-data-ok-of-cut-reduce-free
  ;;          (b* ((m (nodecut-indicesi (cut-nnodes cdb) cdb))
  ;;               ;; (size (cut-leavesi m new-cutsdb))
  ;;               ;; (data (+ 2 m))
  ;;               ;; (truth (cut-leavesi (+ 1 m) new-cutsdb))
  ;;               ;; (old-size (cut-leavesi m cutsdb))
  ;;               ;; (old-truth (cut-leavesi (+ 1 m) cutsdb))
  ;;               )
  ;;            (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                          (cutsdb-cut-ok m cutsdb)
  ;;                          (cutsdb-ok cutsdb)
  ;;                          ;; (cutsdb-ok cutsdb)
  ;;                          ;; (<= old-size 4)
  ;;                          ;; (truth4-p old-truth)
  ;;                          ;; (truth4-deps-bounded old-size old-truth)
  ;;                          ;; (cut-leaves-sorted data old-size cutsdb)
  ;;                          ;; (cutsdb-ok cutsdb)
  ;;                          )
  ;;                     (cutsdb-cut-ok m new-cutsdb)
  ;;                     ;; (and (<= size 4)
  ;;                     ;;      (truth4-p truth)
  ;;                     ;;      (truth4-deps-bounded size truth)
  ;;                     ;;      (cut-leaves-sorted data size new-cutsdb))
  ;;                     ))
  ;;          ;; :hints (("goal" :use new-data-ok-of-cut-reduce
  ;;          ;;          :in-theory (disable new-data-ok-of-cut-reduce)))
  ;;          :fn cut-reduce))

  (defret truth-value-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ((cutinfo new) (cut-infoi m new-cutsdb))
         (data (* 4 m))
         ((cutinfo in0) (cut-infoi cut0 cutsdb))
         (data0 (* 4 (nfix cut0)))
         ((cutinfo in1) (cut-infoi cut1 cutsdb))
         (data1 (* 4 (nfix cut1))))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval new.truth (leaves-truthenv data new.size 0 new-cutsdb bitarr) 4)
                      (cut-spec (truth::truth-eval in0.truth (leaves-truthenv data0 in0.size 0 cutsdb bitarr) 4)
                                neg0
                                (truth::truth-eval in1.truth (leaves-truthenv data1 in1.size 0 cutsdb bitarr) 4)
                                neg1
                                xor))))
    ;; :hints ((acl2::use-termhint
    ;;          (b* (((mv ?updatedp cutsdb) (cuts-merge-aux cut0 neg0 cut1 neg1 cutsdb)))
    ;;            `'(:use ((:instance truth-value-of-cut-reduce
    ;;                      (cutsdb ,(hq cutsdb))))
    ;;               :in-theory (disable truth-value-of-cut-reduce)))))
    )

  (defret cut-leaves-sorted-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-sorted m new-cutsdb))))

  (defret cut-leaves-bounded-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (cut-leaves-bounded cut0 bound cutsdb)
                    (cut-leaves-bounded cut1 bound cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-bounded m bound new-cutsdb))))

  (defret cut-truth-bounded-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-truth-bounded m new-cutsdb))))

  ;; (defret new-data-bounded-of-cuts-merge
  ;;   (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
  ;;        ;; (size (cut-leavesi m new-cutsdb))
  ;;        ;; (truth (cut-leavesi (+ 1 m) new-cutsdb))
  ;;        ;; (data (+ 2 m))
  ;;        )
  ;;     (implies (and updatedp
  ;;                   (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
  ;;                   (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (cutsdb-ok cutsdb)
  ;;                   (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (< (+ 6 m) (cut-leaves-length cutsdb)))
  ;;              (cutsdb-cut-bounded m (cut-nnodes cutsdb1) new-cutsdb)
  ;;              ;; (and (<= size 4)
  ;;              ;;      (truth4-p truth)
  ;;              ;;      (truth4-deps-bounded size truth)
  ;;              ;;      (cut-leaves-sorted data size new-cutsdb))
  ;;              )))

  (defret cut-leaves-lit-idsp-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-leavesi m new-cutsdb))
         ;; (truth (cut-leavesi (+ 1 m) new-cutsdb))
         ;; (data (+ 2 m))
         )
      (implies (and updatedp
                    (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (cut-leaves-lit-idsp cut0 aignet cutsdb)
                    (cut-leaves-lit-idsp cut1 aignet cutsdb)
                    (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cut-leaves-lit-idsp m aignet new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-lit-idsp size truth)
               ;;      (cut-leaves-sorted data size new-cutsdb))
               )))

  (defret cut-leaves-length-nondecreasing-of-cuts-merge
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-cuts-merge
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (defret cuts-merge-updatedp
    (iff updatedp
         (mv-nth 0 (cuts-merge-aux cut0 neg0 cut1 neg1 xor cutsdb))))


  (defret cut-value-of-cuts-merge
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (< (nfix cut0) m)
                    (< (nfix cut1) m))
               (equal (cut-value m new-cutsdb bitarr)
                      (cut-spec (cut-value cut0 cutsdb bitarr)
                                neg0
                                (cut-value cut1 cutsdb bitarr)
                                neg1
                                xor))))
    :hints(("Goal" :in-theory (e/d (cut-value) (cuts-merge))))))


(define cuts-find-worst-aux ((start natp)
                             (end natp)
                             (worst-cut natp)
                             (worst-score natp)
                             (cutsdb))
  :measure (nfix (- (nfix end) (nfix start)))
  :guard (and (<= start end)
              (<= end (cut-info-length cutsdb)))
  :returns (mv (cut natp :rule-classes :type-prescription)
               (score natp :rule-classes :type-prescription)
               (validp))
  (b* (((when (mbe :logic (zp (- (nfix end) (nfix start)))
                   :exec (eql start end)))
        (mv (lnfix worst-cut) (lnfix worst-score) t))
       ((cutinfo info) (cut-infoi start cutsdb))
       ((unless info.valid)
        (mv (lnfix start) info.score nil))
       ((mv worst-cut worst-score)
        (if (< info.score (lnfix worst-score))
            (mv (lnfix start) info.score)
          (mv worst-cut worst-score))))
    (cuts-find-worst-aux (+ 1 (lnfix start)) end worst-cut worst-score cutsdb))
  ///
  (def-updater-independence-thm cuts-find-worst-aux-updater-independence
    (implies (range-cutinfo-equiv-under-mask
              start (- (nfix end) (nfix start))
              #xfff80000
              (nth *cut-infoi1* new)
              (nth *cut-infoi1* old))
             (equal (cuts-find-worst-aux start end worst-cut worst-score new)
                    (cuts-find-worst-aux start end worst-cut worst-score old)))
    :hints (("goal" :induct (cuts-find-worst-aux start end worst-cut worst-score new)
             :expand ((:free (cutsdb)
                       (cuts-find-worst-aux
                        start end worst-cut worst-score cutsdb)))
             :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defret cuts-find-worst-aux-cut-lower-bound
    (implies (not (equal cut (nfix worst-cut)))
             (<= (nfix start) cut))
    :rule-classes :linear)

  (defret cuts-find-worst-aux-cut-upper-bound
    (implies (not (equal cut (nfix worst-cut)))
             (< cut (nfix end)))
    :rule-classes :linear))



(define cuts-find-worst ((start natp)
                         (end natp)
                         (cutsdb))
  :guard (and (< start end)
              (<= end (cut-info-length cutsdb)))
  :returns (mv (cut natp :rule-classes :type-prescription)
               (score natp :rule-classes :type-prescription)
               (validp))
  :inline t
  (b* (((cutinfo info) (cut-infoi start cutsdb))
       ((unless info.valid) (mv (lnfix start) info.score nil)))
    (cuts-find-worst-aux
     (+ 1 (lnfix start)) end
     (lnfix start)
     info.score
     cutsdb))
  ///
  (def-updater-independence-thm cuts-find-worst-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask
                   start (- (nfix end) (nfix start))
                   #xfff80000
                   (nth *cut-infoi1* new)
                   (nth *cut-infoi1* old))
                  (< (nfix start) (nfix end)))
             (equal (cuts-find-worst start end new)
                    (cuts-find-worst start end old)))
    :hints(("Goal" :in-theory (enable nth-when-range-cutinfo-equiv-under-mask))))

  (defret cuts-find-worst-lower-bound
    (<= (nfix start) cut)
    :rule-classes :linear)

  (defret cuts-find-worst-upper-bound
    (implies (< (nfix start) (nfix end))
             (< cut (nfix end)))
    :rule-classes :linear))

(define cuts-consistent ((cut natp)
                         (max natp)
                         (value booleanp)
                         (cutsdb)
                         (bitarr))
  :verify-guards nil
  :measure (nfix (- (nfix max) (nfix cut)))
  (b* (((when (mbe :logic (zp (- (nfix max) (nfix cut)))
                   :exec (eql max cut)))
        t))
    (and (iff* (cut-value cut cutsdb bitarr) value)
         (cuts-consistent (+ 1 (lnfix cut)) max value cutsdb bitarr)))
  ///


  (def-updater-independence-thm cuts-consistent-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask
                   cut (- (nfix max) (nfix cut))
                   #x7ffff
                   (nth *cut-infoi1* new)
                   (nth *cut-infoi1* old))
                  (range-nat-equiv (* 4 (nfix cut))
                                   (* 4 (- (nfix max) (nfix cut)))
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cuts-consistent cut max value new bitarr)
                    (cuts-consistent cut max value old bitarr)))
    :hints (("goal" :induct (cuts-consistent cut max value new bitarr)
             :in-theory (e/d (nth-when-range-cutinfo-equiv-under-mask)
                             ((:d cuts-consistent)))
             :expand ((:free (value new) (cuts-consistent cut max value new bitarr))))))

  (defthm cuts-consistent-compose
    (implies (and (cuts-consistent b c val cutsdb bitarr)
                  (cuts-consistent a b val cutsdb bitarr)
                  (<= (nfix a) (nfix b))
                  (<= (nfix b) (nfix c)))
             (cuts-consistent a c val cutsdb bitarr))
    :hints (("goal" :induct (cuts-consistent a b val cutsdb bitarr)
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :expand ((:free (b) (cuts-consistent a b val cutsdb bitarr))))))

  (defthm cuts-consistent-compose2
    (implies (and ;; binding hyp
              (cuts-consistent a b val cutsdb1 bitarr)
              (cuts-consistent a b val cutsdb bitarr)
              (cuts-consistent b c val cutsdb bitarr)
              (<= (nfix a) (nfix b))
              (<= (nfix b) (nfix c)))
             (cuts-consistent a c val cutsdb bitarr))
    :hints (("Goal" :by cuts-consistent-compose)))

  (defthm cuts-consistent-trivial
    (cuts-consistent a a val cutsdb bitarr)
    :hints (("goal" :expand ((cuts-consistent a a val cutsdb bitarr)))))

  (defthmd cuts-consistent-implies-cut-value
    (implies (and (cuts-consistent n max value cutsdb bitarr)
                  (<= (lnfix n) (lnfix cut))
                  (< (lnfix cut) (lnfix max)))
             (iff (cut-value cut cutsdb bitarr) value))
    :hints (("goal" :induct t
             :in-theory (enable* acl2::arith-equiv-forwarding)))))

(define cuts-consistent-badguy ((cut natp)
                                (max natp)
                                (value booleanp)
                                (cutsdb)
                                (bitarr))
  :verify-guards nil
  :measure (nfix (- (nfix max) (nfix cut)))
  :returns (badguy natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix max) (nfix cut)))
                   :exec (eql max cut)))
        (lnfix cut)))
    (if (iff* (cut-value cut cutsdb bitarr) value)
        (cuts-consistent-badguy (+ 1 (lnfix cut)) max value cutsdb bitarr)
      (lnfix cut)))
  ///

  (def-updater-independence-thm cuts-consistent-badguy-updater-independence
    (implies (and (range-cutinfo-equiv-under-mask
                   cut (- (nfix max) (nfix cut))
                   #x7ffff
                   (nth *cut-infoi1* new)
                   (nth *cut-infoi1* old))
                  (range-nat-equiv (* 4 (nfix cut))
                                   (* 4 (- (nfix max) (nfix cut)))
                                   (nth *cut-leavesi1* new)
                                   (nth *cut-leavesi1* old)))
             (equal (cuts-consistent-badguy cut max value new bitarr)
                    (cuts-consistent-badguy cut max value old bitarr)))
    :hints (("goal" :induct (cuts-consistent-badguy cut max value new bitarr)
             :in-theory (e/d (nth-when-range-cutinfo-equiv-under-mask)
                             ((:d cuts-consistent)))
             :expand ((:free (value new) (cuts-consistent-badguy cut max value new bitarr))))))

  (defret cuts-consistent-by-badguy
    (implies (iff* (cut-value badguy cutsdb bitarr) value)
             (cuts-consistent cut max value cutsdb bitarr))
    :hints(("Goal" :in-theory (enable cuts-consistent))))

  (defretd cuts-consistent-by-badguy-literal
    (implies (acl2::rewriting-positive-literal
              `(cuts-consistent ,cut ,max ,value ,cutsdb ,bitarr))
             (iff (cuts-consistent cut max value cutsdb bitarr)
                  (or (<= (nfix max) badguy)
                      (iff* (cut-value badguy cutsdb bitarr) value))))
    :hints(("Goal" :in-theory (enable cuts-consistent))))

  (defret cuts-consistent-badguy-lower-bound
    (<= (nfix cut) badguy)
    :rule-classes :linear)

  (defret cuts-consistent-badguy-upper-bound
    (implies (not (cuts-consistent cut max value cutsdb bitarr))
             (< badguy (nfix max)))
    :hints(("Goal" :in-theory (enable cuts-consistent-by-badguy-literal)))
    :rule-classes :linear))

(defthm cuts-consistent-ancestor-hack
  (implies (cuts-consistent cut max value cutsdb bitarr)
           (cuts-consistent cut max value cutsdb bitarr)))


(define node-locate-cut (;; (node-cuts-start natp)
                         (config cuts4-config-p)
                         (cutsdb cutsdb-ok))
  :guard (and ;; (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
          (not (eql 0 (cut-nnodes cutsdb)))
              (<= (+ 4 (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                  (cut-leaves-length cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (cut-info-length cutsdb)))
  :prepwork ((local (defthm cuts-invalidate-any-contained-none-invalidated-when-end
                      (not (mv-nth 0 (cuts-invalidate-any-contained
                                      x x data size nil cutsdb)))
                      :hints(("Goal" :in-theory (enable cuts-invalidate-any-contained)))))
             (local (defthm cuts-invalidate-any-contained-invalidated-implies-start-<-end
                      (implies (and (mv-nth 0 (cuts-invalidate-any-contained
                                               start end data size nil cutsdb))
                                    (natp start) (natp end))
                               (< start end))
                      :hints(("Goal" :in-theory (enable cuts-invalidate-any-contained)))
                      :rule-classes :forward-chaining))

             (local (defthmd cutsdb-truths-bounded-decr
                      (implies (and (cutsdb-truths-bounded n cutsdb)
                                    (<= (nfix m) (nfix n)))
                               (cutsdb-truths-bounded m cutsdb))
                      :hints(("Goal" :in-theory (enable cutsdb-truths-bounded)))))

             (local (defthmd cutsdb-leaves-sorted-decr
                      (implies (and (cutsdb-leaves-sorted n cutsdb)
                                    (<= (nfix m) (nfix n)))
                               (cutsdb-leaves-sorted m cutsdb))
                      :hints(("Goal" :in-theory (enable cutsdb-leaves-sorted)))))

             (local (defthmd cut-range-leaves-bounded-decr
                      (implies (and (cut-range-leaves-bounded min n bound cutsdb)
                                    (<= (nfix m) (nfix n)))
                               (cut-range-leaves-bounded min m bound cutsdb))
                      :hints(("Goal" :in-theory (enable cut-range-leaves-bounded)))))

             (local (defthm cutsdb-ok-of-reduce-nodecut-indices
                      (implies (and (cutsdb-ok cutsdb)
                                    (equal nnodes (cut-nnodes cutsdb))
                                    (not (equal 0 (cut-nnodes cutsdb)))
                                    (<= (nfix val) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                    (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb) (nfix val)))
                               (cutsdb-ok (update-nodecut-indicesi nnodes val cutsdb)))
                      :hints(("Goal" :in-theory (enable cutsdb-ok
                                                        cutsdb-truths-bounded-decr
                                                        cutsdb-leaves-sorted-decr
                                                        cut-range-leaves-bounded-decr)
                              :expand ((:free (cutsdb1) (nodecut-indices-increasing (cut-nnodes cutsdb) cutsdb1))
                                       (:free (cutsdb1) (nodecuts-leaves-bounded (cut-nnodes cutsdb) cutsdb1)))))))

             (local (in-theory (disable cuts-find-worst-updater-independence
                                        cuts-consistent-badguy-updater-independence
                                        cutsdb-leaves-lit-idsp-by-badguy))))
  :guard-debug t
  :returns (mv constp new-cutsdb)
  :guard-hints ((and stable-under-simplificationp
                     '(:cases ((< (NODECUT-INDICESI (+ -1 (CUT-NNODES CUTSDB))
                                                    CUTSDB)
                                  (NODECUT-INDICESI (CUT-NNODES CUTSDB)
                                                    CUTSDB))))))
  (b* ((new-cut-idx (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       ((cutinfo info) (cut-infoi new-cut-idx cutsdb))
       (node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
       ((when (eql info.size 0))
        ;; Constant cut -- replace the first cut and reduce the number of cuts to 1.
        (b* ((cutsdb (copy-cut new-cut-idx node-cuts-start cutsdb))
             (cutsdb (update-nodecut-indicesi$ (cut-nnodes cutsdb) (+ 1 (lnfix node-cuts-start)) cutsdb)))
          (mv t cutsdb)))
       ((when (eql new-cut-idx (lnfix node-cuts-start)))
        (b* ((cutsdb (update-nodecut-indicesi$
                      (cut-nnodes cutsdb)
                      (+ 1 new-cut-idx)
                      cutsdb)))
          (mv nil cutsdb)))
       ((mv ?some-invalidated cutsdb)
        (cuts-invalidate-any-contained node-cuts-start new-cut-idx
                                       (* 4 new-cut-idx) info.size nil cutsdb))
       ((mv worst-cut worst-score worst-validp)
        (cuts-find-worst node-cuts-start new-cut-idx cutsdb))
       ((when (and worst-validp
                   (< (- new-cut-idx (lnfix node-cuts-start))
                      (cuts4-config->max-cuts config))))
        ;; (acl2::sneaky-incf 'added-new)
       ;; ((unless (or some-invalidated
       ;;              (<= (cuts4-config->max-cuts config)
       ;;                  (- new-cut-idx (lnfix node-cuts-start)))))
        (b* ((cutsdb (update-nodecut-indicesi$
                      (cut-nnodes cutsdb)
                      (+ 1 new-cut-idx)
                      cutsdb)))
          (mv nil cutsdb)))
       (new-score (cutinfo->score (cut-infoi new-cut-idx cutsdb)))
       ((when (and worst-validp (< new-score worst-score)))
        ;; (acl2::sneaky-incf 'worst-was-better)
        (mv nil cutsdb))
       ;; (- (acl2::sneaky-incf 'worst-replaced))
       (cutsdb (copy-cut new-cut-idx worst-cut cutsdb)))
    (mv nil cutsdb))
  ///


  (defret nth-of-node-locate-cut
    (implies (and (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-node-locate-cut
    (implies (< (nfix n) (* 4 (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
             (equal (nth n (nth *cut-leavesi1* new-cutsdb))
                    (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-locate-cut
    (implies (< (nfix n) (nfix (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
             (equal (nth n (nth *cut-infoi1* new-cutsdb))
                    (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-locate-cut
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret next-cut-of-node-locate-cut-not-const
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not constp))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :rule-classes :linear)

  (defretd next-cut-of-node-locate-cut
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                      (nodecut-indicesi nnodes cutsdb))
                  (not (equal 0 nnodes)))
             (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :rule-classes :linear)

  (defret cut-leaves-length-nondecreasing-of-node-locate-cut
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-node-locate-cut
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (local (defret cutsdb-ok-of-copy-cut-rw
           (implies (and (cutsdb-ok cutsdb)
                         (cut-leaves-sorted src cutsdb)
                         (bind-free `((bound1 . (cut-nnodes$inline ,cutsdb))) (bound1))
                         (equal bound (double-rewrite bound1))
                         (cut-leaves-bounded src bound cutsdb)
                         (posp bound)
                         (<= bound (cut-nnodes cutsdb))
                         (<= (nodecut-indicesi (+ -1 bound) cutsdb) (nfix dst))
                         (cut-truth-bounded src cutsdb))
                    (cutsdb-ok new-cutsdb))
           :fn copy-cut))
  (local (in-theory (disable cutsdb-ok-of-copy-cut)))

  (defret cutsdb-ok-of-node-locate-cut
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (<= (+ 4 (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (cut-leaves-length cutsdb))
                  (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                     (cut-info-length cutsdb))
                  (cut-leaves-sorted (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                     cutsdb)
                  (cut-leaves-bounded (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                      (cut-nnodes cutsdb)
                                      cutsdb)
                  (cut-truth-bounded (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                     cutsdb))
             (cutsdb-ok new-cutsdb))
    :hints ((and stable-under-simplificationp
                 '(:cases ((equal (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                  (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb)))))))

  (local (defret cut-leaves-lit-idsp-of-copy-cut-gen
           (implies (and (cutsdb-leaves-lit-idsp k aignet cutsdb)
                         (cut-leaves-lit-idsp src aignet cutsdb)
                         (< (nfix n) (nfix k)))
                    (cut-leaves-lit-idsp n aignet new-cutsdb))
           :hints (("goal" :cases ((equal (nfix n) (nfix dst))
                                   (< (nfix n) (nfix dst)))
                    :in-theory (e/d* (acl2::arith-equiv-forwarding
                                      stobjs::nth-when-range-nat-equiv))))
           :fn copy-cut))

  (local (defthmd cutsdb-leaves-lit-idsp-of-less
           (implies (and (cutsdb-leaves-lit-idsp n aignet cutsdb)
                         (<= (nfix m) (nfix n)))
                    (cutsdb-leaves-lit-idsp m aignet cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp)))))

  (local (defret cutsdb-leaves-lit-idsp-of-copy-cut
           (implies (and (cutsdb-leaves-lit-idsp k aignet cutsdb)
                         (cut-leaves-lit-idsp src aignet cutsdb))
                    (cutsdb-leaves-lit-idsp k aignet new-cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp-by-badguy-literal)))
           :fn copy-cut))

  (local (defret cutsdb-leaves-lit-idsp-of-cuts-invalidate-any-contained
           (equal (cutsdb-leaves-lit-idsp n aignet new-cutsdb)
                  (cutsdb-leaves-lit-idsp n aignet cutsdb))
           :fn cuts-invalidate-any-contained))


  (local (defret cutsdb-leaves-lit-idsp-of-node-locate-cut
           (implies (and (cutsdb-leaves-lit-idsp ;; (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                          (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                                 aignet cutsdb)
                         (cut-leaves-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       aignet cutsdb)
                         (equal nnodes (cut-nnodes cutsdb))
                         (cutsdb-ok cutsdb)
                         (not (equal 0 nnodes)))
                    (cutsdb-leaves-lit-idsp (nodecut-indicesi nnodes
                                                              new-cutsdb)
                                            aignet new-cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-leaves-lit-idsp-of-less)
                   :expand ((cutsdb-leaves-lit-idsp (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                                    aignet cutsdb)
                            (:free (cutsdb1)
                             (cutsdb-leaves-lit-idsp (+ 1 (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                                                     aignet cutsdb1)))))))

  (defret cutsdb-lit-idsp-of-node-locate-cut
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cut-leaves-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb))))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints(("Goal" :in-theory (e/d (cutsdb-lit-idsp)
                                   (node-locate-cut)))))


  (local (defthm cuts-consistent-of-copy-cut
           (implies (and (cuts-consistent min max value cutsdb bitarr)
                         (iff* (cut-value src cutsdb bitarr) value))
                    (cuts-consistent min max value
                                     (copy-cut src dst cutsdb)
                                     bitarr))
           :hints (("goal" :cases
                    ((equal (cuts-consistent-badguy
                             min max value (copy-cut src dst cutsdb)
                             bitarr)
                            (nfix dst))
                     (< (cuts-consistent-badguy
                         min max value (copy-cut src dst cutsdb)
                         bitarr)
                        (nfix dst)))
                    :in-theory (enable cuts-consistent-implies-cut-value
                                       cuts-consistent-by-badguy-literal)))))

  (local (defthm cuts-consistent-of-subrange-end
           (implies (and (cuts-consistent start end value cutsdb bitarr)
                         (<= (nfix end1) (nfix end)))
                    (cuts-consistent start end1 value cutsdb bitarr))
           :hints(("Goal" :in-theory (enable cuts-consistent)))))

  (local (defthm cuts-consistent-of-subrange
           (implies (and (cuts-consistent start end value cutsdb bitarr)
                         (<= (nfix start) (nfix start1))
                         (<= (nfix end1) (nfix end)))
                    (cuts-consistent start1 end1 value cutsdb bitarr))
           :hints(("Goal" :in-theory (enable* cuts-consistent
                                              acl2::arith-equiv-forwarding)))))


  (defret cuts-consistent-of-node-locate-cut
    (implies (and (cuts-consistent (nodecut-indicesi
                                    (+ -1 (cut-nnodes cutsdb)) cutsdb)
                                   (+ 1 (nodecut-indicesi
                                         (cut-nnodes cutsdb) cutsdb))
                                   value cutsdb bitarr)
                  (equal node-cuts-start (nodecut-indicesi
                                          (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nfix node-cuts-start) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (equal nnodes (cut-nnodes cutsdb)))
             (cuts-consistent node-cuts-start
                              (nodecut-indicesi nnodes new-cutsdb)
                              value new-cutsdb bitarr))
    :hints(("Goal" :in-theory (e/d (cuts-consistent-implies-cut-value))))))


(define node-merge-cuts ((cut0 natp)
                         (neg0 bitp)
                         (cut1 natp)
                         (neg1 bitp)
                         (xor bitp)
                         (config cuts4-config-p)
                         (refcounts)
                         (cutsdb cutsdb-ok))
  :guard (and (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (not (equal 0 (cut-nnodes cutsdb)))
              (<= (cut-nnodes cutsdb) (u32-length refcounts))
              ;; (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              )
  :returns (mv valid constp new-cutsdb)

  :prepwork ((local (in-theory (disable cuts-consistent-badguy-updater-independence
                                        cutsdb-ok-updater-independence
                                        cutsdb-ok-of-node-locate-cut))))

  (b* ((new-cut-idx (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-leaves (+ 4 (* 4 new-cut-idx)) cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-info new-cut-idx cutsdb))
       ((mv added cutsdb) (cuts-merge cut0 neg0 cut1 neg1 xor refcounts cutsdb))
       ((unless added) (mv nil nil cutsdb))
       ((mv constp cutsdb)
        (node-locate-cut config cutsdb)))
    (mv t constp cutsdb))
  ///

  (defret cutsdb-ok-of-node-merge-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok-of-node-locate-cut))))

  (defret cutsdb-lit-idsp-of-node-merge-cuts
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints(("Goal" :in-theory (e/d (cutsdb-lit-idsp-implies-cut-leaves-lit-idsp)))))


  (defret nth-of-node-merge-cuts
    (implies (and (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-node-merge-cuts
    (implies (and (equal node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  (< (nfix n) (* 4 node-cuts-start))
                  (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb))))
    ;; :hints(("Goal" :in-theory (enable cut-leaves-of-update-cut-leavesi)))
    )

  (defret nth-cut-info-of-node-merge-cuts
    (implies (and (equal node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  (< (nfix n) node-cuts-start)
                  (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb))))
    ;; :hints(("Goal" :in-theory (enable cut-leaves-of-update-cut-leavesi)))
    )

  (defret nth-nodecut-indices-of-node-merge-cuts
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret next-cut-of-node-merge-cuts-non-const
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not constp))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :rule-classes :linear)

  (defretd next-cut-of-node-merge-cuts
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                      (nodecut-indicesi nnodes cutsdb)))
             (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :hints(("Goal" :in-theory (enable next-cut-of-node-locate-cut)))
    :rule-classes :linear)

  (defret cut-leaves-length-nondecreasing-of-node-merge-cuts
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-info-length-nondecreasing-of-node-merge-cuts
    (<= (cut-info-length cutsdb) (cut-info-length new-cutsdb))
    :rule-classes :linear)

  (local (defthm cuts-consistent-of-max+1
           (implies (and (natp max)
                         (<= (nfix min) max))
                    (iff (cuts-consistent min (+ 1 max)
                                          value cutsdb bitarr)
                         (and (cuts-consistent min max value cutsdb bitarr)
                              (iff* (cut-value max cutsdb bitarr) value))))
           :hints (("goal" :use ((:instance cuts-consistent-compose
                                  (a min) (c (+ 1 max)) (b max)
                                  (val value)))
                    :in-theory (e/d (cuts-consistent-implies-cut-value)
                                    (cuts-consistent-compose))
                    :expand ((cuts-consistent max (+ 1 max) value cutsdb bitarr))))))



  (defret cuts-consistent-of-node-merge-cuts
    (implies (and (iff* value (cut-spec (cut-value cut0 cutsdb bitarr)
                                        neg0
                                        (cut-value cut1 cutsdb bitarr)
                                        neg1
                                        xor))
                  (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (equal node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  (cuts-consistent node-cuts-start
                                   (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                   value cutsdb bitarr)
                  (cutsdb-ok cutsdb)
                  (<= (nfix node-cuts-start) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cuts-consistent
              node-cuts-start
              (nodecut-indicesi nnodes new-cutsdb)
              value new-cutsdb bitarr))))




(define node-merge-cut-sets1 ((cut0 natp)
                              (neg0 bitp)
                              (cut0-max natp)
                              (cut1 natp)
                              (neg1 bitp)
                              (xor bitp)
                              (valid-count-in natp)
                              (config cuts4-config-p)
                              (refcounts)
                              (cutsdb cutsdb-ok))
  :guard (and (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut0 cut0-max)
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= (cut-nnodes cutsdb) (u32-length refcounts))
              ;; (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (not (equal 0 (cut-nnodes cutsdb))))
  :measure (nfix (- (nfix cut0-max) (nfix cut0)))
  :returns (mv (valid-count natp :rule-classes :type-prescription)
               (constp)
               (new-cutsdb))
  ;; :guard-debug t
  ;; :prepwork ((local (in-theory (disable cut-next$-updater-independence
  ;;                                       cut-base-index-when-cutp))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable cut-next$-updater-independence
  ;;                                         cut-base-index-when-cutp))))

  (b* (((when (mbe :logic (zp (- (nfix cut0-max) (nfix cut0)))
                   :exec (eql cut0-max cut0)))
        (mv (lnfix valid-count-in) nil cutsdb))
       ((cutinfo cut0inf) (cut-infoi cut0 cutsdb))
       ((unless cut0inf.valid)
        (node-merge-cut-sets1 (1+ (lnfix cut0)) neg0 cut0-max cut1 neg1 xor valid-count-in config refcounts cutsdb))
       ((mv valid constp cutsdb) (node-merge-cuts cut0 neg0 cut1 neg1 xor config refcounts cutsdb))
       (valid-count (+ (bool->bit valid) (lnfix valid-count-in)))
       ((when constp) (mv valid-count t cutsdb)))
    (node-merge-cut-sets1 (1+ (lnfix cut0)) neg0 cut0-max cut1 neg1 xor valid-count config refcounts cutsdb))
  ///



  (defret nth-of-node-merge-cut-sets1
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-node-merge-cut-sets1
    (implies (and (< (nfix n) (* 4 (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-merge-cut-sets1
    (implies (and (< (nfix n) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-merge-cut-sets1
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret cut-leaves-length-nondecreasing-of-node-merge-cut-sets1
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  ;; (set-stobj-updater node-merge-cut-sets1 5)

  (defret next-cut-of-node-merge-cut-sets1-non-const
    (implies (not constp)
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)))
    :rule-classes :linear)

  (defretd next-cut-of-node-merge-cut-sets1
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                      (nodecut-indicesi nnodes cutsdb)))
             (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :hints(("Goal" :in-theory (enable next-cut-of-node-merge-cuts)))
    :rule-classes :linear)


  (defret cutsdb-ok-of-node-merge-cut-sets1
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  ;; (equal cut0 )
                  ;; (equal cut1 (nfix cut1))
                  ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                  (<= (nfix cut0-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-ok new-cutsdb)))

  ;; (defret cutsdb-leaves-lit-idsp-of-node-merge-cut-sets1
  ;;   (implies (and (cutsdb-leaves-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
  ;;                 (equal nnodes (cut-nnodes cutsdb))
  ;;                 (cutsdb-ok cutsdb)
  ;;                 (not (equal 0 (cut-nnodes cutsdb)))
  ;;                 (<= (nfix cut0-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (<= (nfix cut0) (nfix cut0-max))
  ;;                 (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  ;;            (cutsdb-leaves-lit-idsp (nodecut-indicesi nnodes new-cutsdb)
  ;;                                    aignet new-cutsdb)))

  (defret cutsdb-lit-idsp-of-node-merge-cut-sets1
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (<= (nfix cut0-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (< (nfix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-lit-idsp aignet new-cutsdb)))


  (local (in-theory (disable cuts-consistent-badguy-updater-independence
                             cutsdb-ok-updater-independence
                             cutsdb-ok-of-node-locate-cut
                             cuts-consistent-ancestor-hack
                             cuts-consistent-compose2
                             cuts-consistent-by-badguy
                             cutsdb-ok-of-node-merge-cut-sets1
                             nth-cut-info-of-node-merge-cut-sets1
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-UPPER-BOUND-WHEN-NOT-EQUAL-REWRITE
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-UPPER-BOUND
                             acl2::nfix-when-not-natp
                             acl2::natp-when-integerp
                             acl2::nfix-equal-to-nonzero
                             acl2::nfix-positive-to-non-zp
                             acl2::natp-when-gte-0
                             acl2::nat-equiv
                             (:d node-merge-cut-sets1)
                             )))

  (defret cuts-consistent-of-node-merge-cut-sets1
    (implies (and (cuts-consistent cut0 cut0-max value0 cutsdb bitarr)
                  (iff* value (cut-spec value0 neg0
                                       (cut-value cut1 cutsdb bitarr)
                                       neg1
                                       xor))
                  (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (equal node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  (cuts-consistent node-cuts-start
                                   (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                   value cutsdb bitarr)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cut0-max) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (< (nfix cut1) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
             (cuts-consistent
              node-cuts-start
              (nodecut-indicesi nnodes new-cutsdb)
              value new-cutsdb bitarr))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (value0) (cuts-consistent cut0 cut0-max value0 cutsdb bitarr))
                     <call>)
            :do-not-induct t))))


(define node-merge-cut-sets ((cut0 natp)
                             (neg0 bitp)
                             (cut0-max natp)
                             (cut1 natp)
                             (neg1 bitp)
                             (cut1-max natp)
                             (xor bitp)
                             (valid-count-in natp)
                             (config cuts4-config-p)
                             (refcounts)
                             (cutsdb cutsdb-ok))
  :guard (and (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut0 cut0-max)
              (<= cut1-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut1 cut1-max)
              (<= (cut-nnodes cutsdb) (u32-length refcounts))
              ;; (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (not (equal 0 (cut-nnodes cutsdb))))
  :measure (nfix (- (nfix cut1-max) (nfix cut1)))
  :returns (mv (valid-count natp :rule-classes :type-prescription)
               (constp)
               (new-cutsdb))
  ;; :guard-debug t
  ;; :prepwork ((local (in-theory (disable cut-next$-updater-independence
  ;;                                       cut-base-index-when-cutp))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable cut-next$-updater-independence
  ;;                                         cut-base-index-when-cutp))))

  (b* (((when (mbe :logic (zp (- (nfix cut1-max) (nfix cut1)))
                   :exec (eql cut1-max cut1)))
        (mv (lnfix valid-count-in) nil cutsdb))
       ((cutinfo cut1inf) (cut-infoi cut1 cutsdb))
       ((unless cut1inf.valid)
        (node-merge-cut-sets cut0 neg0 cut0-max (1+ (lnfix cut1)) neg1 cut1-max xor valid-count-in config refcounts cutsdb))
       ((mv valid-count constp cutsdb)
        (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 xor valid-count-in config refcounts cutsdb))
       ((when constp) (mv valid-count t cutsdb)))
    (node-merge-cut-sets cut0 neg0 cut0-max (1+ (lnfix cut1)) neg1 cut1-max xor valid-count config refcounts cutsdb))
  ///



  (defret nth-of-node-merge-cut-sets
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-node-merge-cut-sets
    (implies (and (< (nfix n) (* 4 (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-merge-cut-sets
    (implies (and (< (nfix n) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-merge-cut-sets
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret cut-leaves-length-nondecreasing-of-node-merge-cut-sets
    (<= (cut-leaves-length cutsdb) (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  ;; (set-stobj-updater node-merge-cut-sets 5)

  (defret next-cut-of-node-merge-cut-sets-non-const
    (implies (not constp)
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)))
    :rule-classes :linear)

  (defretd next-cut-of-node-merge-cut-sets
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                      (nodecut-indicesi nnodes cutsdb)))
             (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :hints(("Goal" :in-theory (enable next-cut-of-node-merge-cut-sets1)))
    :rule-classes :linear)

  (defret cutsdb-ok-of-node-merge-cut-sets
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  ;; (equal cut0 )
                  ;; (equal cut1 (nfix cut1))
                  ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                  (<= (nfix cut0-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (<= (nfix cut1-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut1) (nfix cut1-max)))
             (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-node-merge-cut-sets
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (<= (nfix cut0-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (<= (nfix cut1-max) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nfix cut1) (nfix cut1-max)))
             (cutsdb-lit-idsp aignet new-cutsdb)))


  (local (in-theory (disable cuts-consistent-badguy-updater-independence
                             cutsdb-ok-updater-independence
                             cutsdb-ok-of-node-locate-cut
                             cuts-consistent-ancestor-hack
                             cuts-consistent-compose2
                             cuts-consistent-by-badguy
                             cutsdb-ok-of-node-merge-cut-sets
                             nth-cut-info-of-node-merge-cut-sets
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-UPPER-BOUND-WHEN-NOT-EQUAL-REWRITE
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-UPPER-BOUND
                             acl2::nfix-when-not-natp
                             acl2::natp-when-integerp
                             acl2::nfix-equal-to-nonzero
                             acl2::nfix-positive-to-non-zp
                             acl2::natp-when-gte-0
                             acl2::nat-equiv
                             (:d node-merge-cut-sets))))

  (defret cuts-consistent-of-node-merge-cut-sets
    (implies (and (cuts-consistent cut0 cut0-max value0 cutsdb bitarr)
                  (cuts-consistent cut1 cut1-max value1 cutsdb bitarr)
                  (iff* value (cut-spec value0 neg0 value1 neg1 xor))
                  (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (equal node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  (cuts-consistent node-cuts-start
                                   (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                   value cutsdb bitarr)
                  (cutsdb-ok cutsdb)
                  (<= (nfix cut0-max) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nfix cut0) (nfix cut0-max))
                  (<= (nfix cut1-max) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nfix cut1) (nfix cut1-max)))
             (cuts-consistent
              node-cuts-start
              (nodecut-indicesi nnodes new-cutsdb)
              value new-cutsdb bitarr))
    :hints(("Goal"
            :induct <call>
            :expand ((:free (value0) (cuts-consistent cut1 cut1-max value1 cutsdb bitarr))
                     <call>)
            :do-not-induct t))))












(define node-add-const0-cut ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  (b* ((node (cut-nnodes cutsdb))
       (cut (nodecut-indicesi node cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-leaves (+ 4 (* 4 cut)) cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-info cut cutsdb))
       (cutsdb (update-cut-infoi cut (make-cutinfo :size 0 :truth 0
                                                   :valid t :score 1000)
                                 cutsdb)))
    (update-nodecut-indicesi$ node (+ 1 cut) cutsdb))
  ///
  (defret nth-of-node-add-const0-cut
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-nodecut-indices-of-node-add-const0-cut
    (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret nth-cut-leaves-of-node-add-const0-cut
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-add-const0-cut
    (implies (not (eql (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))


  (local (defthm depends-on-of-consts
           (implies (< (nfix n) 4)
                    (and (not (truth::depends-on n -1 4))
                         (not (truth::depends-on n 0 4))))
           :hints (("goal" :use ((:instance truth::depends-on-witness-correct
                                  (truth -1) (n n) (numvars 4))
                                 (:instance truth::depends-on-witness-correct
                                  (truth 0) (n n) (numvars 4)))
                    :in-theory (e/d (truth::truth-eval)
                                    (truth::depends-on-witness-correct))))))

  (defret cutsdb-ok-of-node-add-const0-cut
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb))))
             (cutsdb-ok new-cutsdb))
    :hints (("goal" ;; :expand ((:free (cdb) (cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cdb)))
             :expand ((:free (data) (leaves-sorted data 0 cutsdb))
                      (:free (data bound) (leaves-bounded data 0 bound cutsdb)))
             :in-theory (enable cut-leaves-sorted
                                cut-truth-bounded
                                cut-leaves-bounded
                                ;; cut-leaves-bounded
                                ;; cutsdb-cut-bounded
                                truth4-deps-bounded))))

  ;; (local
  ;;  (defthm cutsdb-leaves-lit-idsp-of-add-node-free
  ;;    (implies (and (cutsdb-leaves-lit-idsp  aignet cutsdb)
  ;;                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
  ;;                  (equal next (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb))
  ;;                  (cut-leaves-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
  ;;                  (cutsdb-ok cutsdb))
  ;;             (cutsdb-leaves-lit-idsp aignet (update-nodecut-indicesi (cut-nnodes cutsdb1)
  ;;                                                              next
  ;;                                                              cutsdb)))))

  (defret cutsdb-lit-idsp-of-node-add-const0-cut
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb))))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints (("goal" :expand ((:free (cdb) (cutsdb-leaves-lit-idsp (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                                                  aignet cdb))
                             (:free (n) (leaves-lit-idsp n 0 aignet cutsdb)))
             :in-theory (enable cutsdb-lit-idsp cut-leaves-lit-idsp))))

  (local (defthm truth-eval-of-consts
           (and (equal (truth::truth-eval 0 env 4) nil)
                (equal (truth::truth-eval -1 env 4) t))
           :hints(("Goal" :in-theory (enable truth::Truth-eval)))))

  (defret cut-value-of-node-add-const0-cut
    (implies (cutsdb-ok cutsdb)
             (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
                    nil))
    :hints(("Goal" :in-theory (e/d (cut-and cut-value)
                                   ((truth::var) (truth::var4))))))

  (defret next-cut-of-node-add-const0-cut
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)))
    :rule-classes :linear)

  (defret cut-leaves-length-of-node-add-const0-cut
    (<= (cut-leaves-length cutsdb)
        (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defretd nodecut-indices-of-node-add-const0-cut
    (equal (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)
           (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))

  (defret cuts-consistent-of-node-add-const0-cut
    (implies (and (cutsdb-ok cutsdb)
                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb)))
             (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
                              (nodecut-indicesi
                               (cut-nnodes cutsdb1)
                               new-cutsdb)
                              nil
                              new-cutsdb
                              bitarr))
    :hints(("Goal" :in-theory (e/d (nodecut-indices-of-node-add-const0-cut)
                                   (node-add-const0-cut)
                                   )
            :expand ((:free (max val cutsdb1)
                      (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       max val cutsdb1 bitarr)))))))

(define node-add-trivial-cut ((refcounts) (cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  :guard (and (not (equal 0 (cut-nnodes cutsdb)))
              (<= (cut-nnodes cutsdb) (u32-length refcounts)))
  :guard-debug t
  :guard-hints (("goal" :in-theory (enable cut-leaves-bounded)
                 :expand ((:free (data bound cutsdb) (leaves-bounded data 1 bound cutsdb))
                          (:free (data bound cutsdb) (leaves-bounded data 0 bound cutsdb)))))
  (b* ((node (cut-nnodes cutsdb))
       (cut (nodecut-indicesi node cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-leaves (+ 4 (* 4 cut)) cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-info cut cutsdb))
       (info1 (make-cutinfo :size 1
                            :truth (truth::var4 0)
                            :score 0 ;; fixed later
                            :valid t))
       (cutsdb (update-cut-infoi cut info1 cutsdb))
       (cutsdb (update-cut-leavesi$ (* 4 cut) (1- node) cutsdb))
       (info2 (!cutinfo->score (cut-score cut refcounts cutsdb) info1))
       (cutsdb (update-cut-infoi cut info2 cutsdb)))
    (update-nodecut-indicesi$ node (+ 1 cut) cutsdb))
  ///
  (defret nth-of-node-add-trivial-cut
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-nodecut-indices-of-node-add-trivial-cut
    (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret nth-cut-leaves-of-node-add-trivial-cut
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-add-trivial-cut
    (implies (not (equal (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))


  (local (defthm depends-on-of-consts
           (implies (< (nfix n) 4)
                    (and (not (truth::depends-on n -1 4))
                         (not (truth::depends-on n 0 4))))
           :hints (("goal" :use ((:instance truth::depends-on-witness-correct
                                  (truth -1) (n n) (numvars 4))
                                 (:instance truth::depends-on-witness-correct
                                  (truth 0) (n n) (numvars 4)))
                    :in-theory (e/d (truth::truth-eval)
                                    (truth::depends-on-witness-correct))))))

  (defret cutsdb-ok-of-node-add-trivial-cut
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb))))
             (cutsdb-ok new-cutsdb))
    :hints (("goal" ;; :expand ((:free (cdb) (cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cdb)))
             :expand ((:free (data cutsdb) (leaves-sorted data 1 cutsdb))
                      (:free (data bound cutsdb) (leaves-bounded data 1 bound cutsdb))
                      (:free (data bound cutsdb) (leaves-bounded data 0 bound cutsdb))
                      ;; (:free (data) (leaves-sorted data 0 cutsdb))
                      )
             :in-theory (enable cut-leaves-sorted
                                cut-truth-bounded
                                cut-leaves-bounded
                                ;; cut-leaves-bounded
                                ;; cutsdb-cut-bounded
                                truth4-deps-bounded))))



  (defret cutsdb-lit-idsp-of-node-add-trivial-cut
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (aignet-idp (+ -1 (cut-nnodes cutsdb)) aignet)
                  (not (equal (ctype (stype (car (lookup-id (+ -1 (cut-nnodes cutsdb)) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints (("goal" :expand ((:free (cdb) (cutsdb-leaves-lit-idsp (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                                               aignet cdb))
                             (:free (n cutsdb) (leaves-lit-idsp n 1 aignet cutsdb))
                             (:free (n cutsdb) (leaves-lit-idsp n 0 aignet cutsdb)))
             :in-theory (enable cutsdb-lit-idsp cut-leaves-lit-idsp))))

  (local (defthm truth-eval-of-consts
           (and (equal (truth::truth-eval 0 env 4) nil)
                (equal (truth::truth-eval -1 env 4) t))
           :hints(("Goal" :in-theory (enable truth::Truth-eval)))))

  (defret cut-value-of-node-add-trivial-cut
    (implies (cutsdb-ok cutsdb)
             (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
                    (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))))
    :hints(("Goal" :in-theory (e/d (cut-value)
                                   ((truth::var) (truth::var4))))))

  (defret next-cut-of-node-add-trivial-cut
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)))
    :rule-classes :linear)

  (defret cut-leaves-length-of-node-add-trivial-cut
    (<= (cut-leaves-length cutsdb)
        (cut-leaves-length new-cutsdb))
    :rule-classes :linear)

  (defretd nodecut-indices-of-node-add-trivial-cut
    (equal (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)
           (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))

  (defret cuts-consistent-of-node-add-trivial-cut
    (implies (and (cutsdb-ok cutsdb)
                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (iff* val (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))))
             (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
                              (nodecut-indicesi
                               (cut-nnodes cutsdb1)
                               new-cutsdb)
                              val
                              new-cutsdb
                              bitarr))
    :hints(("Goal" :in-theory (e/d (nodecut-indices-of-node-add-trivial-cut)
                                   (node-add-trivial-cut))
            :expand ((:free (max val)
                      (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       max val new-cutsdb bitarr)))))))

;; (define node-add-trivial-and-cut ((child0 litp)
;;                                   (child1 litp)
;;                                   (cutsdb cutsdb-ok))
;;   ;; :guard (< (+ 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (cut-leaves-length cutsdb))
;;   :returns (new-cutsdb)
;;   :prepwork ((local (defthm unsigned-byte-p-of-truth4
;;                       (unsigned-byte-p 32 (truth::truth-norm x 4))
;;                       :hints(("Goal" :in-theory (enable truth::truth-norm))))))
;;   (b* ((node (cut-nnodes cutsdb))
;;        (cut (nodecut-indicesi node cutsdb))
;;        ((when (eql (lit-id child0) (lit-id child1)))
;;         ;; special cases
;;         (if (eql (b-xor (lit-neg child0) (lit-neg child1)) 1)
;;             ;; AND is const false
;;             (node-add-const0-cut cutsdb)
;;           (b* ((size 1)
;;                (truth (truth::truth-norm4
;;                        (logxor (truth::var4 0)
;;                                (- (bfix (lit-neg child0))))))
;;                (cutsdb (cutsdb-maybe-grow-cut-leaves (+ 5 cut) cutsdb))
;;                (cutsdb (update-cut-leavesi cut size cutsdb))
;;                (cutsdb (update-cut-leavesi (+ 1 cut) truth cutsdb))
;;                (cutsdb (update-cut-leavesi$ (+ 2 cut) (lit-id child0) cutsdb)))
;;             (update-nodecut-indicesi$ node (+ 3 cut) cutsdb))))
;;        (cutsdb (cutsdb-maybe-grow-cut-leaves (+ 5 cut) cutsdb))
;;        (size 2)
;;        ((mv child0 child1)
;;         (if (< (lit-id child0) (lit-id child1))
;;             (mv child0 child1)
;;           (mv child1 child0)))
;;        (truth (truth::truth-norm4
;;                (logand (logxor (truth::var4 0)
;;                                (- (bfix (lit-neg child0))))
;;                        (logxor (truth::var4 1)
;;                                (- (bfix (lit-neg child1)))))))
;;        (cutsdb (update-cut-leavesi cut size cutsdb))
;;        (cutsdb (update-cut-leavesi (+ 1 cut) truth cutsdb))
;;        (cutsdb (update-cut-leavesi$ (+ 2 cut) (lit-id child0) cutsdb))
;;        (cutsdb (update-cut-leavesi$ (+ 3 cut) (lit-id child1) cutsdb)))
;;     (update-nodecut-indicesi$ node (+ 4 cut) cutsdb))
;;   ///
;;   (defret nth-of-node-add-trivial-and-cut
;;     (implies (and (not (equal (nfix n) *cut-leavesi1*))
;;                   (not (equal (nfix n) *nodecut-indicesi1*)))
;;              (equal (nth n new-cutsdb)
;;                     (nth n cutsdb))))

;;   (defret nth-nodecut-indices-of-node-add-trivial-and-cut
;;     (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
;;              (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
;;                     (nth n (nth *nodecut-indicesi1* cutsdb)))))

;;   (defret nth-cut-leaves-of-node-add-trivial-and-cut
;;     (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;              (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
;;                         (nth n (nth *cut-leavesi1* cutsdb)))))

;;   (set-stobj-updater node-add-trivial-and-cut 2)

;;   (local (defthm cut-next$-of-update-cut-leaves
;;            (implies (cutp n cutsdb)
;;                     (equal (cut-next$ n (update-cut-leavesi n v cutsdb))
;;                            (+ 2 (nfix n) (nfix v))))
;;            :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
;;                                           (rewrite-to-cut-next$))))))

;;   (local (defthm depends-on-of-consts
;;            (implies (< (nfix n) 4)
;;                     (and (not (truth::depends-on n -1 4))
;;                          (not (truth::depends-on n 0 4))))
;;            :hints (("goal" :use ((:instance truth::depends-on-witness-correct
;;                                   (truth -1) (n n) (numvars 4))
;;                                  (:instance truth::depends-on-witness-correct
;;                                   (truth 0) (n n) (numvars 4)))
;;                     :in-theory (e/d (truth::truth-eval)
;;                                     (truth::depends-on-witness-correct))))))

;;   (local (defthm depends-on-of-minus-bit
;;            (implies (and (bitp b)
;;                          (< (nfix x) 4))
;;                     (not (truth::depends-on x (- b) 4)))
;;            :hints(("Goal" :in-theory (enable bitp)))))

;;   (defret cutsdb-ok-of-node-add-trivial-and-cut
;;     (implies (and (cutsdb-ok cutsdb)
;;                   (not (equal 0 (cut-nnodes cutsdb))))
;;              (cutsdb-ok new-cutsdb))
;;     :hints (("goal" :expand ((:free (cdb) (cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cdb)))
;;              :in-theory (enable cut-leaves-sorted
;;                                 truth4-deps-bounded))))

;;   (local (defthm truth-eval-of-minus-bit
;;            (implies (bitp b)
;;                     (equal (truth::truth-eval (- b) env 4)
;;                            (acl2::bit->bool b)))
;;            :hints(("Goal" :in-theory (enable truth::truth-eval bitp)))))

;;   (local (defthm truth-eval-of-consts
;;            (and (equal (truth::truth-eval 0 env 4) nil)
;;                 (equal (truth::truth-eval -1 env 4) t))
;;            :hints(("Goal" :in-theory (enable truth::Truth-eval)))))

;;   (defret cut-value-of-node-add-trivial-and-cut
;;     (implies (cutsdb-ok cutsdb)
;;              (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
;;                     (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
;;                              (lit-neg child0)
;;                              (acl2::bit->bool (get-bit (lit-id child1) bitarr))
;;                              (lit-neg child1))))
;;     :hints(("Goal" :in-theory (e/d (cut-and cut-value)
;;                                    ((truth::var) (truth::var4)
;;                                     cut-value-of-node-add-const0-cut))
;;             :use cut-value-of-node-add-const0-cut)))

;;   (defret next-cut-of-node-add-trivial-and-cut
;;     (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
;;              (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
;;                  (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)))
;;     :rule-classes :linear)

;;   (defret cut-leaves-length-of-node-add-trivial-and-cut
;;     (<= (cut-leaves-length cutsdb)
;;         (cut-leaves-length new-cutsdb))
;;     :rule-classes :linear)

;;   (defret cut-next$-of-node-add-trivial-and-cut
;;     (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
;;                   (cutsdb-ok cutsdb))
;;              (equal (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
;;                                new-cutsdb)
;;                     (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))))

;;   (defret cuts-consistent-of-node-add-trivial-and-cut
;;     (implies (and (cutsdb-ok cutsdb)
;;                   (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
;;                   (iff* val (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
;;                                      (lit-neg child0)
;;                                      (acl2::bit->bool (get-bit (lit-id child1) bitarr))
;;                                      (lit-neg child1))))
;;              (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
;;                               (nodecut-indicesi
;;                                (cut-nnodes cutsdb1)
;;                                new-cutsdb)
;;                               val
;;                               new-cutsdb
;;                               bitarr))
;;     :hints(("Goal" :in-theory (e/d ()
;;                                    (node-add-trivial-and-cut))
;;             :expand ((:free (max val)
;;                       (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
;;                                        max val new-cutsdb bitarr)))))))


;; (define print-cuts ((start natp)
;;                     (end natp)
;;                     (cutsdb))
;;   :guard (and (<= start end)
;;               (<= end (cut-info-length cutsdb))
;;               (<= (* 4 end) (cut-leaves-length cutsdb)))
;;   :measure (nfix (- (nfix end) (nfix start)))
;;   (b* (((when (mbe :logic (zp (- (nfix end) (nfix start)))
;;                    :exec (eql start end)))
;;         nil))
;;     (cw "~@0~%" (print-cut start cutsdb))
;;     (print-cuts (1+ (lnfix start)) end cutsdb)))



(define node-derive-cuts-aux ((child0 litp)
                              (child1 litp)
                              (xor bitp)
                              (config cuts4-config-p)
                              (refcounts)
                              (cutsdb cutsdb-ok))
  :guard (and (< (lit-id child0) (cut-nnodes cutsdb))
              (< (lit-id child1) (cut-nnodes cutsdb))
              (<= (cut-nnodes cutsdb) (u32-length refcounts)))
  :returns (mv (new-count natp :rule-classes :type-prescription) new-cutsdb)
  (b* ((node0 (lit-id child0))
       (node1 (lit-id child1))
       (neg0 (lit-neg child0))
       (neg1 (lit-neg child1))
       (cut0-min (nodecut-indicesi node0 cutsdb))
       (cut0-max (nodecut-indicesi (+ 1 node0) cutsdb))
       (cut1-min (nodecut-indicesi node1 cutsdb))
       (cut1-max (nodecut-indicesi (+ 1 node1) cutsdb))
       ((mv count constp cutsdb)
        (node-merge-cut-sets cut0-min neg0 cut0-max cut1-min neg1 cut1-max
                             xor 0 config refcounts cutsdb))
       ((when constp)
        (mv count cutsdb))
       (cutsdb (node-add-trivial-cut refcounts cutsdb)))
    ;; (cw "Cuts for node ~x0:~%" (1- (cut-nnodes cutsdb)))
    ;; (print-cuts (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb)
    ;;             (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
    ;;             cutsdb)
    (mv (+ 1 count) cutsdb))
  ///



  (defret nth-of-node-derive-cuts-aux
    (implies (and (not (equal (nfix n) *cut-infoi1*))
                  (not (equal (nfix n) *cut-leavesi1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-leaves-of-node-derive-cuts-aux
    (implies (and (< (nfix n) (* 4 (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-derive-cuts-aux
    (implies (and (< (nfix n) (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  (<= (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (eql 0 (cut-nnodes cutsdb))))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts-aux
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater node-derive-cuts-aux 2)

  (defret next-cut-of-node-derive-cuts-aux
    (implies (and (equal nnodes (cut-nnodes cutsdb))
                  (not (equal 0 nnodes))
                  (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                      (nodecut-indicesi nnodes cutsdb)))
             (<= (nodecut-indicesi (+ -1 nnodes) cutsdb)
                 (nodecut-indicesi nnodes new-cutsdb)))
    :hints(("Goal" :in-theory (enable next-cut-of-node-merge-cut-sets)))
    :rule-classes :linear)

  (defret cutsdb-ok-of-node-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb)))
             (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-node-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet cutsdb)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb))
                  (aignet-idp (+ -1 (cut-nnodes cutsdb)) aignet)
                  (not (equal (ctype (stype (car (lookup-id (+ -1 (cut-nnodes cutsdb)) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb)))

  ;; (local (in-theory (disable ;;CUT-BASE-INDEX-UPDATER-INDEPENDENCE
  ;;                            ;; cutsdb-ok-of-node-merge-cut-sets
  ;;                            cuts-consistent-updater-independence
  ;;                            nodecut-indicesi-updater-independence
  ;;                            ;; cut-base-index-lte-target-idx
  ;;                            )))

  (local (in-theory (disable cuts-consistent-ancestor-hack
                             cuts-consistent-by-badguy
                             nodecut-indicesi-updater-independence
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-UPPER-BOUND-WHEN-NOT-EQUAL-REWRITE
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-NOT-EQUAL-PAST-UPPER-BOUND
                             acl2::nfix-equal-to-nonzero
                             acl2::zp-when-gt-0
                             acl2::nfix-when-not-natp
                             acl2::nfix-positive-to-non-zp
                             acl2::zp-when-integerp
                             cut-leaves-length-updater-independence
                             nodecut-indices-length-updater-independence
                             acl2::natp-when-gte-0
                             STOBJS::RANGE-NAT-EQUIV-BADGUY-UPPER-BOUND-WHEN-NOT-EQUAL-REWRITE
                             RANGE-CUTINFO-EQUIV-UNDER-MASK-BADGUY-LOWER-BOUND-NOT-EQUAL
                             cuts-consistent-compose
                             cuts-consistent-compose2
                             len
                             cuts-consistent-updater-independence
                             range-cutinfo-equiv-under-mask-by-badguy
                             )))

  (defret cuts-consistent-of-node-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (equal nnodes (cut-nnodes cutsdb))
                  (equal prev-index (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb))
                  ;; (equal (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                  ;;        (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (cuts-consistent (nodecut-indicesi (lit-id child0) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child0)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                   cutsdb bitarr)
                  (cuts-consistent (nodecut-indicesi (lit-id child1) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child1)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                   cutsdb bitarr)
                  (iff* val (cut-spec (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                      (lit-neg child0)
                                      (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                      (lit-neg child1)
                                      xor))
                  (iff* val (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr)))
                  (< (+ 1 (lit-id child0)) (cut-nnodes cutsdb))
                  (< (+ 1 (lit-id child1)) (cut-nnodes cutsdb))
                  (cuts-consistent (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                                   (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                   val cutsdb bitarr))
             (cuts-consistent prev-index
                              (nodecut-indicesi
                               nnodes
                               new-cutsdb)
                              val
                              new-cutsdb
                              bitarr))
    :hints ((acl2::use-termhint
             (b* ((node0 (lit-id child0))
                  (node1 (lit-id child1))
                  (neg0 (lit-neg child0))
                  (neg1 (lit-neg child1))
                  (cut0-min (nodecut-indicesi node0 cutsdb))
                  (cut0-max (nodecut-indicesi (+ 1 node0) cutsdb))
                  (cut1-min (nodecut-indicesi node1 cutsdb))
                  (cut1-max (nodecut-indicesi (+ 1 node1) cutsdb))
                  (node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
                  ((mv & constp second-cutsdb)
                   (node-merge-cut-sets cut0-min neg0 cut0-max cut1-min neg1 cut1-max xor
                                        0 config refcounts cutsdb))
                  ((when constp) nil)
                  (third-cutsdb (node-add-trivial-cut refcounts second-cutsdb)))
               (acl2::termhint-seq
                `'(:use ((:instance cuts-consistent-compose
                          (a ,(hq node-cuts-start))
                          (b ,(hq (nodecut-indicesi (cut-nnodes second-cutsdb) second-cutsdb)))
                          (c ,(hq (nodecut-indicesi (cut-nnodes third-cutsdb) third-cutsdb)))
                          (val ,(hq val))
                          (cutsdb ,(hq third-cutsdb)))))
                `'(:in-theory (enable cuts-consistent-updater-independence
                                      range-cutinfo-equiv-under-mask-by-badguy))))))))

(define node-derive-cuts ((child0 litp)
                          (child1 litp)
                          (xor bitp)
                          (config cuts4-config-p)
                          (refcounts)
                          (cutsdb cutsdb-ok))
  :guard (and (< (lit-id child0) (cut-nnodes cutsdb))
              (< (lit-id child1) (cut-nnodes cutsdb))
              (< (cut-nnodes cutsdb) (u32-length refcounts)))
  :returns (mv (count natp :rule-classes :type-prescription) new-cutsdb)
  (b* ((cutsdb (cuts-add-node cutsdb)))
    (node-derive-cuts-aux child0 child1 xor config refcounts cutsdb))
  ///

  (defret cut-nnodes-of-node-derive-cuts
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-leaves-of-node-derive-cuts
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-derive-cuts
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret next-nodecut-index-of-node-derive-cuts
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (+ 1 (cut-nnodes cutsdb1)) new-cutsdb)))
    ;; :hints (("goal" :use ((:instance next-cut-of-node-derive-cuts-aux
    ;;                        (cutsdb (cuts-add-node cutsdb))))
    ;;          :in-theory (disable next-cut-of-node-derive-cuts-aux)))
    :rule-classes :linear)

  ;; (set-stobj-updater node-derive-cuts 2)

  ;; (defret next-cut-of-node-derive-cuts
  ;;   (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
  ;;       (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
  ;;   :rule-classes :linear)

  (defret cutsdb-ok-of-node-derive-cuts
      (implies (and (cutsdb-ok cutsdb)
                    (< (lit-id child0) (cut-nnodes cutsdb))
                    (< (lit-id child1) (cut-nnodes cutsdb)))
               (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-node-derive-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (equal nnodes (+ 1 (cut-nnodes cutsdb)))
                  (cutsdb-lit-idsp
                                          aignet cutsdb)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb))
                  (aignet-idp (cut-nnodes cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-nnodes cutsdb) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb)))

  (defret cuts-consistent-of-node-derive-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (equal prev-nnodes (cut-nnodes cutsdb))
                  (equal nnodes (+ 1 (cut-nnodes cutsdb)))
                  (equal (nodecut-indicesi prev-nnodes cutsdb1)
                         (nodecut-indicesi prev-nnodes cutsdb))
                  ;; (equal (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                  ;;        (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (cuts-consistent (nodecut-indicesi (lit-id child0) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child0)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                   cutsdb bitarr)
                  (cuts-consistent (nodecut-indicesi (lit-id child1) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child1)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                   cutsdb bitarr)
                  (iff* val (cut-spec (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                     (lit-neg child0)
                                     (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                     (lit-neg child1)
                                     xor))
                  (iff* val (acl2::bit->bool (get-bit (cut-nnodes cutsdb) bitarr)))
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb)))
             (cuts-consistent (nodecut-indicesi prev-nnodes cutsdb1)
                              (nodecut-indicesi nnodes new-cutsdb)
                              val
                              new-cutsdb
                              bitarr))))

(define node-cuts-consistent ((node natp)
                              (cutsdb cutsdb-ok)
                              (bitarr))
  :verify-guards nil
  (cuts-consistent (nodecut-indicesi node cutsdb)
                   (nodecut-indicesi (+ 1 (lnfix node)) cutsdb)
                   (acl2::bit->bool (get-bit node bitarr))
                   cutsdb bitarr)
  ///
  ;; (defthmd node-cuts-consistent-of-node-derive-cuts-aux
  ;;   (implies (and (node-cuts-consistent (lit-id child0) cutsdb bitarr)
  ;;                 (node-cuts-consistent (lit-id child1) cutsdb bitarr)
  ;;                 (< (+ 1 (lit-id child0)) (cut-nnodes cutsdb))
  ;;                 (< (+ 1 (lit-id child1)) (cut-nnodes cutsdb))
  ;;                 (cutsdb-ok cutsdb)
  ;;                 (equal (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
  ;;                        (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 (iff* (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))
  ;;                       (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
  ;;                                (lit-neg child0)
  ;;                                (acl2::bit->bool (get-bit (lit-id child1) bitarr))
  ;;                                (lit-neg child1))))
  ;;            (node-cuts-consistent
  ;;             (+ -1 (cut-nnodes cutsdb))
  ;;             (mv-nth 1 (node-derive-cuts-aux child0 child1 cutsdb config))
  ;;             bitarr)))

  (defthm node-cuts-consistent-of-node-derive-cuts
    (implies (and (node-cuts-consistent (lit-id child0) cutsdb bitarr)
                  (node-cuts-consistent (lit-id child1) cutsdb bitarr)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb)
                  (iff* (acl2::bit->bool (get-bit (cut-nnodes cutsdb) bitarr))
                        (cut-spec (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                 (lit-neg child0)
                                 (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                 (lit-neg child1)
                                 xor)))
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              (mv-nth 1 (node-derive-cuts child0 child1 xor config refcounts cutsdb))
              bitarr))
    ;; :hints(("Goal" :in-theory (enable node-derive-cuts)
    ;;         :use ((:instance node-cuts-consistent-of-node-derive-cuts-aux
    ;;                (cutsdb (cuts-add-node cutsdb))))))
    )

  (def-updater-independence-thm node-cuts-consistent-updater-independence
    (implies (and (equal node-idx (nodecut-indicesi node old))
                  (equal next-idx (nodecut-indicesi (+ 1 (lnfix node)) old))
                  (equal node-idx (nodecut-indicesi node new))
                  (equal next-idx (nodecut-indicesi (+ 1 (lnfix node)) new))
                  (<= node-idx next-idx)
                  (range-nat-equiv (* 4 node-idx) (* 4 (nfix (- next-idx node-idx)))
                                   (nth *cut-leavesi1* new) (nth *cut-leavesi1* old))
                  (range-cutinfo-equiv-under-mask node-idx (nfix (- next-idx node-idx))
                                                  #x7ffff
                                                  (nth *cut-infoi1* new) (nth *cut-infoi1* old)))
             (equal (node-cuts-consistent node new bitarr)
                    (node-cuts-consistent node old bitarr))))

  (defthm node-cuts-consistent-preserved-by-node-derive-cuts
    (implies (and (node-cuts-consistent node cutsdb bitarr)
                  (< (nfix node) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb))
             (node-cuts-consistent node (mv-nth 1 (node-derive-cuts child0 child1 xor config refcounts cutsdb)) bitarr))
    :hints(("Goal" :in-theory (disable node-cuts-consistent))))

  (defthm node-cuts-consistent-of-cuts-add-node
    (node-cuts-consistent (cut-nnodes cutsdb)
                          (cuts-add-node cutsdb)
                          bitarr))

  (defthmd node-cuts-consistent-implies-cut-value
    (implies (and (node-cuts-consistent node cutsdb bitarr)
                  (cutsdb-ok cutsdb)
                  (<= (nodecut-indicesi node cutsdb)
                      (lnfix cut))
                  (< (lnfix cut) (nodecut-indicesi (+ 1 (lnfix node)) cutsdb))
                  (< (nfix node) (cut-nnodes cutsdb)))
             (iff (cut-value cut cutsdb bitarr)
                  (acl2::bit->bool (nth node bitarr))))
    :hints(("Goal" :in-theory (enable cuts-consistent-implies-cut-value)))))


(define node-derive-cuts-const0 ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  (b* ((cutsdb (cuts-add-node cutsdb)))
    (node-add-const0-cut cutsdb))
  ///

  (defret cut-nnodes-of-node-derive-cuts-const0
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-leaves-of-node-derive-cuts-const0
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-derive-cuts-const0
    (implies (not (equal (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts-const0
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater node-derive-cuts-const0 0)


  (defret next-nodecut-index-of-node-derive-cuts-const0
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (+ 1 (cut-nnodes cutsdb1)) new-cutsdb)))
    :hints (("goal" :use ((:instance next-cut-of-node-add-const0-cut
                           (cutsdb (cuts-add-node cutsdb))
                           (cutsdb1 (cuts-add-node cutsdb))))
             :in-theory (disable next-cut-of-node-add-const0-cut)))
    :rule-classes :linear)

  ;; (defret next-cut-of-node-derive-cuts-const0
  ;;   (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
  ;;       (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
  ;;   :rule-classes :linear)

  (defret cutsdb-ok-of-node-derive-cuts-const0
      (implies (cutsdb-ok cutsdb)
               (cutsdb-ok new-cutsdb)))


  (defthm node-cuts-consistent-of-node-derive-cuts-const0
    (implies (and (cutsdb-ok cutsdb)
                  (not (acl2::bit->bool (get-bit (cut-nnodes cutsdb) bitarr))))
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              (node-derive-cuts-const0 cutsdb)
              bitarr))
    :hints(("Goal" :in-theory (enable node-cuts-consistent)
            :use ((:instance cuts-consistent-of-node-add-const0-cut
                   (cutsdb (cuts-add-node cutsdb))
                   (cutsdb1 (cuts-add-node cutsdb)))))))

  (defret cutsdb-lit-idsp-of-node-derive-cuts-const0
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet cutsdb))
             (cutsdb-lit-idsp aignet new-cutsdb))))


(define node-derive-cuts-input ((refcounts) (cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  :guard (< (cut-nnodes cutsdb) (u32-length refcounts))
  (b* ((cutsdb (cuts-add-node cutsdb)))
    (node-add-trivial-cut refcounts cutsdb))
  ///

  (defret cut-nnodes-of-node-derive-cuts-input
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-leaves-of-node-derive-cuts-input
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-node-derive-cuts-input
    (implies (not (equal (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts-input
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater node-derive-cuts-input 0)

  (defret next-nodecut-index-of-node-derive-cuts-input
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (+ 1 (cut-nnodes cutsdb1)) new-cutsdb)))
    :hints (("goal" :use ((:instance next-cut-of-node-add-trivial-cut
                           (cutsdb (cuts-add-node cutsdb))
                           (cutsdb1 (cuts-add-node cutsdb))))
             :in-theory (disable next-cut-of-node-add-const0-cut)))
    :rule-classes :linear)

  ;; (defret next-cut-of-node-derive-cuts-input
  ;;   (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
  ;;       (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
  ;;   :rule-classes :linear)

  (defret cutsdb-ok-of-node-derive-cuts-input
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb)))


  (defret node-cuts-consistent-of-node-derive-cuts-input
    (implies (cutsdb-ok cutsdb)
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              new-cutsdb
              bitarr))
    :hints(("Goal" :in-theory (enable node-cuts-consistent)
            :use ((:instance cuts-consistent-of-node-add-trivial-cut
                   (cutsdb (cuts-add-node cutsdb))
                   (cutsdb1 (cuts-add-node cutsdb))
                   (val (acl2::bit->bool (get-bit (cut-nnodes cutsdb) bitarr))))))))

  (defret cutsdb-lit-idsp-of-node-derive-cuts-input
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet cutsdb)
                  (aignet-idp (cut-nnodes cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-nnodes cutsdb) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb))))

(defsection cutsdb-consistent
  (defun-sk cutsdb-consistent (cutsdb bitarr)
    (forall node
            (implies (< (nfix node) (cut-nnodes cutsdb))
                     (node-cuts-consistent node cutsdb bitarr)))
    :rewrite :direct)

  (in-theory (disable cutsdb-consistent))

  (defthmd cutsdb-consistent-implies-cut-value
    (implies (and (cutsdb-consistent cutsdb bitarr)
                  (<= (nodecut-indicesi node cutsdb) (lnfix cut))
                  (< (lnfix cut) (nodecut-indicesi (+ 1 (nfix node)) cutsdb))
                  (< (nfix node) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb))
             (equal (cut-value cut cutsdb bitarr)
                    (acl2::bit->bool (nth node bitarr))))
    :hints (("goal" :use node-cuts-consistent-implies-cut-value))))





(include-book "centaur/aignet/eval" :dir :system)

(define aignet-derive-cuts-node ((aignet)
                                 (config cuts4-config-p)
                                 (refcounts)
                                 (cutsdb cutsdb-ok))
  :returns (mv (cuts-checked natp :rule-classes :type-prescription)
               new-cutsdb)
  :guard (and (< (cut-nnodes cutsdb) (num-fanins aignet))
              (< (cut-nnodes cutsdb) (u32-length refcounts)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* ((node (cut-nnodes cutsdb))
       (slot0 (id->slot node 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :in (b* ((cutsdb (node-derive-cuts-input refcounts cutsdb)))
            (mv 1 cutsdb))
      :const (b* ((cutsdb (node-derive-cuts-const0 cutsdb)))
               (mv 1 cutsdb))
      :out (b* ((cutsdb (cuts-add-node cutsdb)))
             (mv 0 cutsdb))
      :gate
      (b* ((lit0 (snode->fanin slot0))
           (slot1 (id->slot node 1 aignet))
           (lit1 (snode->fanin slot1)))
        (node-derive-cuts lit0 lit1 (snode->regp slot1) config refcounts cutsdb))))
  ///

  (defret cut-nnodes-of-aignet-derive-cuts-node
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-leaves-of-aignet-derive-cuts-node
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-aignet-derive-cuts-node
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-aignet-derive-cuts-node
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater aignet-derive-cuts-node 1)

  (defret next-nodecut-index-of-aignet-derive-cuts-node
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (+ 1 (cut-nnodes cutsdb1)) new-cutsdb)))
    :rule-classes :linear)

  (defret cutsdb-ok-of-aignet-derive-cuts-node
      (implies (cutsdb-ok cutsdb)
               (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-aignet-derive-cuts-node
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet cutsdb)
                  (<= (cut-nnodes cutsdb) (fanin-count aignet)))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints(("Goal" :in-theory (enable aignet-idp))))


  (local (defthm cut-and-is-eval-and-of-lits
           (equal (cut-and (equal 1 (id-eval (lit->var lit0) invals regvals aignet))
                           (lit->neg lit0)
                           (equal 1 (id-eval (lit->var lit1) invals regvals aignet))
                           (lit->neg lit1))
                  (equal 1 (eval-and-of-lits lit0 lit1 invals regvals aignet)))
           :hints(("Goal" :in-theory (enable cut-and eval-and-of-lits lit-eval b-and)))))

  (local (defthm cut-xor-is-eval-xor-of-lits
           (equal (cut-xor (equal 1 (id-eval (lit->var lit0) invals regvals aignet))
                           (lit->neg lit0)
                           (equal 1 (id-eval (lit->var lit1) invals regvals aignet))
                           (lit->neg lit1))
                  (equal 1 (eval-xor-of-lits lit0 lit1 invals regvals aignet)))
           :hints(("Goal" :in-theory (enable cut-xor eval-xor-of-lits lit-eval b-xor)))))

  (defret node-cuts-consistent-of-aignet-derive-cuts-node
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals aignet))
                  (<= (cut-nnodes cutsdb) (fanin-count aignet)))
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              new-cutsdb
              (aignet-record-vals vals invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                '(:cases ((bit->bool (regp (stype (car (lookup-id (cut-nnodes cutsdb) aignet))))))))
            (and stable-under-simplificationp
                 '(:expand ((id-eval (cut-nnodes cutsdb) invals regvals aignet))
                   :in-theory (enable cut-spec))))))


(define aignet-derive-cuts-aux ((aignet)
                                (cuts-checked-in natp)
                                (config cuts4-config-p)
                                (refcounts)
                                (cutsdb cutsdb-ok))
  :returns (mv (cuts-checked natp :rule-classes :type-prescription)
               new-cutsdb)
  :measure (nfix (- (num-fanins aignet) (cut-nnodes cutsdb)))
  :guard (and (<= (cut-nnodes cutsdb) (num-fanins aignet))
              (<= (num-fanins aignet) (u32-length refcounts)))
  (b* ((node (cut-nnodes cutsdb))
       ((when (mbe :logic (zp (+ (num-fanins aignet) (- (nfix node))))
                   :exec (eql (num-fanins aignet) node)))
        (mv (lnfix cuts-checked-in) cutsdb))
       ((mv count cutsdb) (aignet-derive-cuts-node aignet config refcounts cutsdb)))
    (aignet-derive-cuts-aux aignet (+ count (lnfix cuts-checked-in)) config refcounts cutsdb))
  ///
  (defret cut-nnodes-of-aignet-derive-cuts-aux
    (implies (<= (cut-nnodes cutsdb) (+ 1 (fanin-count aignet)))
             (equal (cut-nnodes new-cutsdb)
                    (+ 1 (fanin-count aignet)))))

  (defret nth-cut-leaves-of-aignet-derive-cuts-aux
    (implies (< (nfix n) (* 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (nat-equiv (nth n (nth *cut-leavesi1* new-cutsdb))
                        (nth n (nth *cut-leavesi1* cutsdb)))))

  (defret nth-cut-info-of-aignet-derive-cuts-aux
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (cutinfo-equiv (nth n (nth *cut-infoi1* new-cutsdb))
                            (nth n (nth *cut-infoi1* cutsdb)))))

  (defret nth-nodecut-indices-of-aignet-derive-cuts-aux
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater aignet-derive-cuts-aux 1)

  (defret cutsdb-ok-of-aignet-derive-cuts-aux
      (implies (cutsdb-ok cutsdb)
               (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-aignet-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-lit-idsp aignet cutsdb))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints(("Goal" :in-theory (disable cutsdb-lit-idsp-updater-independence))))

  (defret cutsdb-consistent-of-aignet-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals aignet)))
             (cutsdb-consistent
              new-cutsdb
              (aignet-record-vals vals invals regvals aignet)))
    :hints (("goal" :induct t
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (acl2::use-termhint
             (b* ((bitarr (aignet-record-vals vals invals regvals aignet))
                  ((mv & cuts) (aignet-derive-cuts-node aignet config refcounts cutsdb))
                  (witness (cutsdb-consistent-witness cuts bitarr))
                  ((acl2::termhint-seq
                    `'(:expand ((cutsdb-consistent ,(hq cuts) ,(hq bitarr)))))))
               `'(:cases ((nat-equiv ,(hq witness) ,(hq (cut-nnodes cutsdb))))))))))


(define aignet-derive-cuts (aignet (config cuts4-config-p) refcounts cutsdb)
  :returns (mv (cuts-checked natp :rule-classes :type-prescription)
               new-cutsdb)
  :guard (<= (num-fanins aignet) (u32-length refcounts))
  :verify-guards nil
  (b* ((cutsdb (update-cut-nnodes 0 cutsdb))
       (cutsdb (cutsdb-maybe-grow-nodecut-indices 1 cutsdb))
       (cutsdb (cutsdb-maybe-grow-cut-leaves 1 cutsdb))
       (cutsdb (update-nodecut-indicesi 0 0 cutsdb)))
    (aignet-derive-cuts-aux aignet 0 config refcounts cutsdb))
  ///
  (local (defthm cutsdb-ok-of-empty
           (implies (and (equal (cut-nnodes cutsdb) 0)
                         (equal (nodecut-indicesi 0 cutsdb) 0)
                         (<= 1 (nodecut-indices-length cutsdb))
                         (<= 1 (cut-leaves-length cutsdb)))
                    (cutsdb-ok cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-ok
                                             nodecut-indices-increasing
                                             cutsdb-truths-bounded
                                             nodecuts-leaves-bounded
                                             cutsdb-leaves-sorted)))))

  (local (defthm cutsdb-lit-idsp-of-empty
           (implies (and (equal (cut-nnodes cutsdb) 0)
                         (equal (nodecut-indicesi 0 cutsdb) 0))
                    (cutsdb-lit-idsp aignet cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-lit-idsp)
                   :expand ((cutsdb-leaves-lit-idsp 0 aignet cutsdb))))))

  (local (defthm cutsdb-consistent-of-empty
           (implies (equal (cut-nnodes cutsdb) 0)
                    (cutsdb-consistent cutsdb bitarr))
           :hints (("goal" :expand ((cutsdb-consistent cutsdb bitarr))))))

  (verify-guards aignet-derive-cuts)

  (defret cutsdb-ok-of-aignet-derive-cuts
    (cutsdb-ok new-cutsdb))

  (defret cutsdb-lit-idsp-of-aignet-derive-cuts
    (cutsdb-lit-idsp aignet new-cutsdb))

  (defret cutsdb-consistent-of-aignet-derive-cuts
    (cutsdb-consistent
     new-cutsdb
     (aignet-record-vals vals invals regvals aignet)))

  (defret cut-nnodes-of-aignet-derive-cuts
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (fanin-count aignet)))))






