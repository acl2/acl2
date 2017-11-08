

(in-package "AIGNET")

(include-book "centaur/aignet/semantics" :dir :system)
(include-book "centaur/truth/sizes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(include-book "centaur/misc/iffstar" :dir :system)

;; (include-book "std/stobjs/rewrites" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (acl2::use-trivial-ancestors-check))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable nth update-nth unsigned-byte-p)))

(local (in-theory (enable stobjs::nth-when-range-nat-equiv)))

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






(local (defthmd nth-past-len
         (implies (<= (len x) (nfix n))
                  (equal (nth n x) nil))
         :hints(("Goal" :in-theory (enable nth)))))


(fty::defprod cuts4-config
  ((max-cuts posp :rule-classes :type-prescription))
  :layout :tree)



(defstobj cutsdb
  ;; Cut-data contains all the node cut data.  Entries consist of
  ;; (size truth node0 ... noden), where n = size-1.
  ;; Nodecut-indices maps node IDs to cut data:
  ;; nodecut-indices[n] is the starting index of the cut data, so there needs
  ;; to be at least cut-nnodes+1 entries in nodecut-indices in order to track
  ;; the ending index of the last node.
  (cut-data :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (nodecut-indices :type (array (unsigned-byte 32) (1)) :initially 0 :resizable t)
  (cut-nnodes :type (integer 0 *) :initially 0)
  :renaming ((cut-datai cut-datai1)
             (nodecut-indicesi nodecut-indicesi1)
             (cut-nnodes cut-nnodes1))
  :inline t)


(defthm cut-datap-is-u32-listp
  (equal (cut-datap x)
         (acl2::u32-listp x)))

(defthm nodecut-indicesp-is-u32-listp
  (equal (nodecut-indicesp x)
         (acl2::u32-listp x)))

(local (in-theory (disable cut-datap nodecut-indicesp)))

;; (defmacro set-stobj-updater (fn argnum &optional retnum)
;;   `(table stobj-updaters ',(cons fn retnum) ',argnum))

;; (defmacro is-stobj-updater (fn &optional retnum)
;;   `(cdr (assoc-equal (cons ,fn ,retnum) (table-alist 'stobj-updaters (w state)))))

;; (define stobj-updater-returnval-binding ((arg "term to match")
;;                                          (var "variable to bind")
;;                                          &key (mfc 'mfc) (state 'state))
;;   :ignore-ok t :irrelevant-formals-ok t :mode :program
;;   (case-match arg
;;     (('mv-nth ('quote n) (fn . args))
;;      (let ((argnum (is-stobj-updater fn n)))
;;        (and argnum
;;             `((,var . ,(nth argnum args))))))
;;     ((fn . args)
;;      (let ((argnum (is-stobj-updater fn)))
;;        (and argnum
;;             `((,var . ,(nth argnum args))))))))

;; (defmacro bind-stobj-updater-returnval (arg var)
;;   `(and (syntaxp (consp ,arg)) ;; optimization
;;         (bind-free (stobj-updater-returnval-binding ,arg ',var) (,var))))

;; (set-stobj-updater update-nth 2)

;; (set-stobj-updater update-nth-array 3)

;; (defmacro def-updater-independence-thm (&rest args)
;;   (cons 'stobjs::def-updater-independence-thm args))


(defsection update-cut-datai
  (defthm nth-of-update-cut-datai
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n (update-cut-datai i v cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-data-of-update-cut-datai
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth n (nth *cut-datai1* (update-cut-datai i v cutsdb)))
                    (nth n (nth *cut-datai1* cutsdb)))))

  ;; (defthmd cut-data-of-update-cut-datai
  ;;   (equal (nth *cut-datai1* (update-cut-datai n v cutsdb))
  ;;          (update-nth n v (nth *cut-datai1* cutsdb))))

  (defthm nth-updated-index-of-update-cut-datai
    (equal (nth n (nth *cut-datai1* (update-cut-datai n v cutsdb)))
           v))

  (defthm cut-datai1-of-update-cut-datai
    (equal (cut-datai1 n (update-cut-datai n v cutsdb))
           v))

  (defthm cut-data-length-of-update-cut-datai
    (implies (< (nfix n) (cut-data-length cutsdb))
             (equal (cut-data-length (update-cut-datai n v cutsdb))
                    (cut-data-length cutsdb))))

  (defthm cut-data-length-of-update-cut-datai-greater
    (>= (cut-data-length (update-cut-datai n v cutsdb))
        (cut-data-length cutsdb))
    :hints(("Goal" :in-theory (enable cut-data-length)))
    :rule-classes :linear)

  (defthm cut-data-length-of-update-cut-datai-greater-than-index
    (> (cut-data-length (update-cut-datai n v cutsdb))
       (nfix n))
    :hints(("Goal" :in-theory (enable cut-data-length)))
    :rule-classes :linear)

  (fty::deffixequiv update-cut-datai :args ((acl2::i natp)))

  ;; (set-stobj-updater update-cut-datai 2)
  (in-theory (disable update-cut-datai)))

(defsection resize-cut-data
  (defthm nth-of-resize-cut-data
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n (resize-cut-data size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-data-of-resize-cut-data
    (implies (and (< (nfix n) (nfix size))
                  (< (nfix n) (cut-data-length cutsdb)))
             (equal (nth n (nth *cut-datai1* (resize-cut-data size cutsdb)))
                    (nth n (nth *cut-datai1* cutsdb)))))

  (defthm nth-cut-data-of-resize-cut-data-grow
    (implies (<= (cut-data-length cutsdb) (nfix size))
             (nat-equiv (nth n (nth *cut-datai1* (resize-cut-data size cutsdb)))
                        (nth n (nth *cut-datai1* cutsdb))))
    :hints(("Goal" :in-theory (enable nth-past-len))))

  ;; (defthmd cut-data-of-resize-cut-data
  ;;   (equal (nth *cut-datai1* (resize-cut-data size cutsdb))
  ;;          (resize-list (nth *cut-datai1* cutsdb) size 0)))

  (defthm cut-data-length-of-resize-cut-data
    (equal (cut-data-length (resize-cut-data size cutsdb))
           (nfix size)))

  (fty::deffixequiv resize-cut-data :args ((acl2::i natp)))

  ;; (set-stobj-updater resize-cut-data 1)
  (in-theory (disable resize-cut-data)))



(defsection cut-datai1

  (def-updater-independence-thm cut-datai1-updater-independence
    (implies (equal (nth n (nth *cut-datai1* new))
                    (nth n (nth *cut-datai1* old)))
             (equal (cut-datai1 n new)
                    (cut-datai1 n old))))

  (defthm natp-of-cut-datai1
    (implies (and (acl2::u32-listp (nth *cut-datai1* cutsdb))
                  (< (nfix n) (cut-data-length cutsdb)))
             (natp (cut-datai1 n cutsdb)))
    :hints(("Goal" :in-theory (enable cut-data-length))))

  (fty::deffixequiv cut-datai1 :args ((acl2::i natp)))

  (in-theory (disable cut-datai1)))

(defsection cut-data-length
  (def-updater-independence-thm cut-data-length-updater-independence
    (implies (equal (len (nth *cut-datai1* new))
                    (len (nth *cut-datai1* old)))
             (equal (cut-data-length new)
                    (cut-data-length old))))

  (in-theory (disable cut-data-length)))



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



(define cut-datai ((n natp) cutsdb)
  :returns (entry natp :rule-classes :type-prescription)
  :guard (< n (cut-data-length cutsdb))
  :inline t
  :prepwork ((local (in-theory (enable acl2::nth-in-u32-listp-natp))))
  (lnfix (cut-datai1 n cutsdb))
  ///
  (def-updater-independence-thm cut-datai-updater-independence
    (implies (nat-equiv (nth n (nth *cut-datai1* new))
                        (nth n (nth *cut-datai1* old)))
             (equal (cut-datai n new)
                    (cut-datai n old)))
    :hints(("Goal" :in-theory (enable cut-datai1))))

  (defthm cut-datai-of-update-cut-data
    (equal (cut-datai n (update-cut-datai n v cutsdb))
           (nfix v))))


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
;;   :array-accs (nodecut-indicesi cut-datai nth))

(local (in-theory (disable cutsdbp)))

(encapsulate nil
  ;; make sure our updater independence theory works
  (local (defthmd cut-nnodes-of-update-cut-datai
           (equal (cut-nnodes (update-cut-datai i val cut-data))
                  (cut-nnodes cut-data)))))


;; (define range-of-nths-equiv ((start natp) (num natp) (x true-listp) (y true-listp))
;;   :measure (nfix num)
;;   (if (zp num)
;;       t
;;     (and (ec-call (nat-equiv (nth start x) (nth start y)))
;;          (range-of-nths-equiv (1+ (lnfix start)) (1- num) x y)))
;;   ///
;;   (defthmd range-of-nths-equiv-open
;;     (implies (not (zp num))
;;              (equal (range-of-nths-equiv start num x y)
;;                     (and (nat-equiv (nth start x) (nth start y))
;;                          (range-of-nths-equiv (1+ (lnfix start)) (1- num) x y)))))

;;   (fty::deffixequiv range-of-nths-equiv)

;;   (local (defthm range-of-nths-equiv-when-greater-num-lemma
;;            (implies (range-of-nths-equiv start (+ (nfix num2) (nfix n)) x y)
;;                     (range-of-nths-equiv start num2 x y))
;;            :rule-classes nil))

;;   (defthm range-of-nths-equiv-when-greater-num
;;     (implies (and (range-of-nths-equiv start num x y)
;;                   (syntaxp (not (equal num num2)))
;;                   (<= (nfix num2) (nfix num)))
;;              (range-of-nths-equiv start num2 x y))
;;     :hints (("goal" :use ((:instance range-of-nths-equiv-when-greater-num-lemma
;;                            (num2 num2) (n (- (nfix num) (nfix num2))))))))

;;   (defthm range-of-nths-equiv-when-superrange
;;     (implies (and (range-of-nths-equiv start num x y)
;;                   (syntaxp (not (and (equal start start2)
;;                                      (equal num num2))))
;;                   (<= (nfix start) (nfix start2))
;;                   (<= (+ (nfix num2) (nfix start2)) (+ (nfix num) (nfix start))))
;;              (range-of-nths-equiv start2 num2 x y))
;;     :hints (("goal" :induct (range-of-nths-equiv start num x y)
;;              :in-theory (enable* acl2::arith-equiv-forwarding))
;;             (and stable-under-simplificationp
;;                  '(:expand ((range-of-nths-equiv start num2 x y))))))

;;   (defthm nth-when-range-of-nths-equiv
;;     (implies (and (range-of-nths-equiv start num x y)
;;                   (<= (nfix start) (nfix n))
;;                   (< (nfix n) (+ (nfix start) (nfix num))))
;;              (nat-equiv (nth n x) (nth n y)))
;;     :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

;;   (defthm range-of-nths-equiv-self
;;     (range-of-nths-equiv start num x x))


;;   (defthm range-of-nths-equiv-of-update-out-of-range-1
;;     (implies (not (and (<= (nfix start) (nfix n))
;;                        (< (nfix n) (+ (nfix start) (nfix num)))))
;;              (equal (range-of-nths-equiv start num (update-nth n v x) y)
;;                     (range-of-nths-equiv start num x y))))

;;   (defthm range-of-nths-equiv-of-update-out-of-range-2
;;     (implies (not (and (<= (nfix start) (nfix n))
;;                        (< (nfix n) (+ (nfix start) (nfix num)))))
;;              (equal (range-of-nths-equiv start num x (update-nth n v y))
;;                     (range-of-nths-equiv start num x y))))

;;   (defthm range-of-nths-equiv-of-empty
;;     (range-of-nths-equiv start 0 x y)))

;; (define stobjs::range-nat-equiv-badguy ((start natp) (num natp) (x true-listp) (y true-listp))
;;   :measure (nfix num)
;;   :returns (badguy natp :rule-classes :type-prescription)
;;   (if (or (zp num) (eql num 1))
;;       (nfix start)
;;     (if (ec-call (nat-equiv (nth start x) (nth start y)))
;;         (stobjs::range-nat-equiv-badguy (1+ (lnfix start)) (1- num) x y)
;;       (nfix start)))
;;   ///
;;   (local (in-theory (enable range-of-nths-equiv)))
;;   (defret stobjs::range-nat-equiv-badguy-lower-bound
;;     (<= (nfix start) badguy)
;;     :rule-classes :linear)

;;   (defret stobjs::range-nat-equiv-badguy-upper-bound
;;     (implies (posp num)
;;              (< badguy (+ (nfix start) (nfix num))))
;;     :rule-classes :linear)

;;   (defret stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
;;     ;; Note!! This rule relies heavily on the use of the ancestors stack to
;;     ;; relieve its hyp.  E.g., we are trying to prove
;;     ;; (range-of-nths-equiv start num x y).
;;     ;; So we apply range-of-nths-equiv-by-badguy.  In relieving its hyp, we 
;;     ;; need to know something about the range of the badguy, so we apply this rule which 
;;     ;; is allowed to assume its hyp, (not (range-of-nths-equiv start num x y)),
;;     ;; because its negation is an ancestor.
;;     ;;
;;     ;; We have previously run into problems with this because the ancestors
;;     ;; stack in ACL2 doesn't store normal forms of its hyps.  E.g., 
;;     ;; we had a rule cut-next$-updater-independence:
;;     ;; (implies (range-of-nths-equiv 0 (+ 1 (cut-base-index cut old))
;;     ;;                               (nth *cut-datai1* new)
;;     ;;                               (nth *cut-datai1* old)))
;;     ;;          (equal (cut-next$ cut new)
;;     ;;                 (cut-next$ cut old)))
;;     ;; In relieving the range-of-nths-equiv hyp for this rule, sometimes we
;;     ;; would first rewrite (cut-base-index cut old) to just (nfix cut) because
;;     ;; we knew (cutp cut old).  This would then disrupt the processing of this
;;     ;; rule later because the ancestors stack would still include the original
;;     ;; form of this hyp,
;;     ;;  (range-of-nths-equiv 0 (+ 1 (cut-base-index cut old)) ...)
;;     ;; whereas we'd be trying to relieve
;;     ;;  (not (range-of-nths-equiv 0 (+ 1 (nfix cut)) ...))
;;     ;; To solve this sort of problem, we rephrase cut-next$-updater-independence
;;     ;; as follows:
;;     ;; (implies (and (equal idx (+ 1 (cut-base-index cut old)))
;;     ;;               (range-of-nths-equiv 0 idx
;;     ;;                                    (nth *cut-datai1* new)
;;     ;;                                    (nth *cut-datai1* old)))
;;     ;;          (equal (cut-next$ cut new)
;;     ;;                 (cut-next$ cut old)))
;;     ;; Adding this binding hyp makes it so the ancestor recorded is in normal
;;     ;; form, at least wrt idx. (Usually (nth *cut-datai* ...) isn't rewritten,
;;     ;; so we don't use binding hyps for these.)
;;     (implies (not (range-of-nths-equiv start num x y))
;;              (< badguy (+ (nfix start) (nfix num))))
;;     :rule-classes :linear)

;;   (defret range-of-nths-equiv-by-badguy
;;     (implies (nat-equiv (nth badguy x) (nth badguy y))
;;              (range-of-nths-equiv start num x y)))

;;   (defret range-of-nths-equiv-by-badguy-literal
;;     (implies (acl2::rewriting-positive-literal `(range-of-nths-equiv ,start ,num ,x ,y))
;;              (iff (range-of-nths-equiv start num x y)
;;                   (or (not (< badguy (+ (nfix start) (nfix num))))
;;                       (nat-equiv (nth badguy x) (nth badguy y))))))

;;   (defthm range-of-nths-equiv-by-superrange
;;     (implies (and (range-of-nths-equiv min1 max1 x y)
;;                   (<= (nfix min1) (nfix min))
;;                   (<= (+ (nfix min) (nfix max))
;;                       (+ (nfix min1) (nfix max1))))
;;              (range-of-nths-equiv min max x y))
;;     :hints(("Goal" :in-theory (disable range-of-nths-equiv-open)))))


(define cutsdb-data-nodes-sorted ((idx natp)
                                  (num natp)
                                  cutsdb)
  :guard (<= (+ idx num) (cut-data-length cutsdb))
  :measure (nfix num)
  (b* (((when (<= (lnfix num) 1)) t))
    (and (< (cut-datai idx cutsdb)
            (cut-datai (+ 1 (lnfix idx)) cutsdb))
         (cutsdb-data-nodes-sorted (+ 1 (lnfix idx)) (1- (lnfix num)) cutsdb)))
  ///
  ;; (local (defthm nfix-bound-when-integerp
  ;;          (implies (integerp x)
  ;;                   (<= x (nfix x)))
  ;;          :hints(("Goal" :in-theory (enable nfix)))
  ;;          :rule-classes :linear))

  ;; (local (include-book "std/lists/nthcdr" :dir :system))
  ;; ;; (local (defthm car-of-nthcdr
  ;; ;;          (equal (car (nthcdr n x))
  ;; ;;                 (nth n x))
  ;; ;;          :hints(("Goal" :in-theory (enable nthcdr nth)))))

  ;; (local (defthm take-of-nthcdr-open
  ;;          (implies (not (zp num))
  ;;                   (equal (take num (nthcdr idx x))
  ;;                          (cons (nth idx x) (take (1- num) (nthcdr (+ 1 (nfix idx)) x)))))
  ;;          :hints(("Goal" :in-theory (enable nthcdr)
  ;;                  :do-not-induct t
  ;;                  :expand ((take num (nthcdr idx x)))))))

  ;; (local (defthm zp-of-num-minus-1
  ;;          (implies (and (integerp num)
  ;;                        (< 1 num))
  ;;                   (not (zp (+ -1 num))))))

  ;; (local (defthm cdr-of-nthcdr
  ;;          (equal (cdr (nthcdr n x))
  ;;                 (nthcdr (+ 1 (nfix n)) x))))

  (def-updater-independence-thm cutsdb-data-nodes-sorted-updater-independence
    (implies (stobjs::range-nat-equiv idx num (nth *cut-datai1* new) (nth *cut-datai1* old))
             (equal (cutsdb-data-nodes-sorted idx num new)
                    (cutsdb-data-nodes-sorted idx num old)))
    :hints (("goal" :induct (cutsdb-data-nodes-sorted idx num new)
             :expand ((:free (new) (cutsdb-data-nodes-sorted idx num new))
                      ;; (:free (x) (range-of-nths idx num x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  ;; (defthm cutsdb-data-nodes-sorted-preserved-by-write
  ;;   (implies (<= (+ (nfix idx) (nfix num)) (nfix dest-idx))
  ;;            (equal (cutsdb-data-nodes-sorted idx num (update-cut-datai dest-idx val cutsdb))
  ;;                   (cutsdb-data-nodes-sorted idx num cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-array-acc-meta-split))))

  (defthmd cutsdb-data-nodes-sorted-implies-compare
    (implies (and (cutsdb-data-nodes-sorted idx num cutsdb)
                  (< (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (< (cut-datai idx cutsdb)
                (cut-datai n cutsdb)))
    :rule-classes (:rewrite :linear)))


(define cutsdb-data-nodes-bounded ((idx natp)
                                  (num natp)
                                  (bound natp)
                                  cutsdb)
  :guard (<= (+ idx num) (cut-data-length cutsdb))
  :measure (nfix num)
  (b* (((when (zp num)) t))
    (and (< (cut-datai idx cutsdb) (lnfix bound))
         (cutsdb-data-nodes-bounded (+ 1 (lnfix idx)) (1- (lnfix num)) bound cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-data-nodes-bounded-updater-independence
    (implies (stobjs::range-nat-equiv idx num (nth *cut-datai1* new) (nth *cut-datai1* old))
             (equal (cutsdb-data-nodes-bounded idx num bound new)
                    (cutsdb-data-nodes-bounded idx num bound old)))
    :hints (("goal" :induct (cutsdb-data-nodes-bounded idx num bound new)
             :expand ((:free (new) (cutsdb-data-nodes-bounded idx num bound new))
                      ;; (:free (x) (range-of-nths idx num bound x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  ;; (defthm cutsdb-data-nodes-bounded-preserved-by-write
  ;;   (implies (<= (+ (nfix idx) (nfix num)) (nfix dest-idx))
  ;;            (equal (cutsdb-data-nodes-bounded idx num bound (update-cut-datai dest-idx val cutsdb))
  ;;                   (cutsdb-data-nodes-bounded idx num bound cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-array-acc-meta-split))))

  (defthmd cutsdb-data-nodes-bounded-implies-compare
    (implies (and (cutsdb-data-nodes-bounded idx num bound cutsdb)
                  (<= (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (< (cut-datai n cutsdb) (nfix bound)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defthmd cutsdb-data-nodes-bounded-when-bounded-lesser
    (implies (and (cutsdb-data-nodes-bounded idx num bound1 cutsdb)
                  (<= (nfix bound1) (nfix bound)))
             (cutsdb-data-nodes-bounded idx num bound cutsdb))))



       
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

(define cut-next ((n natp) cutsdb)
  :guard (< n (cut-data-length cutsdb))
  :returns (next natp :rule-classes :type-prescription)
  :inline t
  (+ 2 (lnfix n) (cut-datai n cutsdb))
  ///
  (defret cut-next-bound
    (<= (+ 2 (nfix n)) (cut-next n cutsdb))
    :rule-classes :linear)

  (def-updater-independence-thm cut-next-updater-independence
    (implies (nat-equiv (nth n (nth *cut-datai1* new))
                        (nth n (nth *cut-datai1* old)))
             (equal (cut-next n new)
                    (cut-next n old))))

  (defthm cut-next-of-set-size
    (equal (cut-next n (update-cut-datai n size cutsdb))
           (+ 2 (nfix n) (nfix size)))))



(define cut-base-index-aux ((curr-idx natp)
                            (target-idx natp)
                            (cutsdb))
  ;; curr-idx is always a base index.
  :guard (and (<= curr-idx target-idx)
              (<= target-idx (cut-data-length cutsdb)))
  :returns (cut-idx natp :rule-classes :type-prescription)
  :measure (+ 1 (nfix (- (nfix target-idx) (nfix curr-idx))))
  (mbe :logic (b* ((nextcut (cut-next curr-idx cutsdb))
                   ((when (< (lnfix target-idx) nextcut))
                    (lnfix curr-idx)))
                (cut-base-index-aux nextcut target-idx cutsdb))
       :exec
       (b* (((when (int= target-idx curr-idx)) curr-idx)
            (nextcut (cut-next curr-idx cutsdb))
            ((when (< target-idx nextcut))
             curr-idx))
         (cut-base-index-aux nextcut target-idx cutsdb)))
  ///
  (defret cut-base-index-aux-gte-curr-idx
    (<= (nfix curr-idx) cut-idx)
    :rule-classes :linear)

  (defret cut-base-index-aux-lte-target-idx
    (implies (<= (nfix curr-idx) (nfix target-idx)) 
             (<= cut-idx (nfix target-idx)))
    :rule-classes :linear)

  (defret cut-base-index-aux-monotonic
    (implies (<= (nfix target-idx) (nfix target-idx1))
             (<= cut-idx (let ((target-idx target-idx1)) <call>))))

  (defret cut-base-index-aux-target-idempotent
    (equal (cut-base-index-aux curr-idx cut-idx cutsdb)
           cut-idx))

  (defret cut-base-index-aux-curr-idx-compose 
    (implies (<= (nfix target-idx) (nfix target-idx1))
             (equal (cut-base-index-aux cut-idx target-idx1 cutsdb)
                    (cut-base-index-aux curr-idx target-idx1 cutsdb))))

  (defret cut-base-index-aux-of-next-cut
    (equal (cut-base-index-aux curr-idx
                               (cut-next cut-idx cutsdb)
                               cutsdb)
           (cut-next cut-idx cutsdb)))

  (defret cut-base-index-aux-of-less-than-next-cut
    (implies (and (<= cut-idx (nfix next-idx))
                  (< next-idx (cut-next cut-idx cutsdb)))
             (equal (cut-base-index-aux curr-idx next-idx
                                        cutsdb)
                    cut-idx)))

  (def-updater-independence-thm cut-base-index-aux-updater-independence
    (implies (and (nat-equiv (nth curr-idx (nth *cut-datai1* new))
                             (nth curr-idx (nth *cut-datai1* old)))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
                  (equal idx (+ (if (equal (cut-base-index-aux curr-idx target-idx old)
                                           (nfix target-idx))
                                    0
                                  1)
                                (- (cut-base-index-aux curr-idx target-idx old)
                                   (nfix curr-idx))))
                  (stobjs::range-nat-equiv curr-idx
                                       idx
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (equal (cut-base-index-aux curr-idx target-idx new)
                    (cut-base-index-aux curr-idx target-idx old)))
    :hints ((and stable-under-simplificationp
                 (equal (car id) '(0))
                 '(:induct (cut-base-index-aux curr-idx target-idx new)
                   :expand ((:free (x) (cut-base-index-aux curr-idx target-idx x)))
                   :in-theory (disable acl2::inequality-with-nfix-hyp-1
                                       acl2::inequality-with-nfix-hyp-2
                                       acl2::nfix-equal-to-nonzero))))))


(define cut-base-index ((target-idx natp)
                        (cutsdb))
  :guard (<= target-idx (cut-data-length cutsdb))
  :returns (cut-idx natp :rule-classes :type-prescription)
  (cut-base-index-aux 0 target-idx cutsdb)
  ///
  (defret cut-base-index-lte-target-idx
    (<= cut-idx (nfix target-idx))
    :rule-classes :linear)


  (defret cut-base-index-monotonic
    (implies (<= (nfix target-idx) (nfix target-idx1))
             (<= cut-idx (let ((target-idx target-idx1)) <call>)))
    :rule-classes :linear)

  (defret cut-base-index-target-idempotent
    (equal (cut-base-index cut-idx cutsdb)
           cut-idx))

  (defthm cut-base-index-of-less-than-next-cut
    (implies (and (<= (cut-base-index target-idx cutsdb) (nfix other-idx))
                  (< other-idx (cut-next (cut-base-index target-idx cutsdb) cutsdb)))
             (equal (cut-base-index other-idx cutsdb)
                    (cut-base-index target-idx cutsdb)))
    :rule-classes nil)

  (defret cut-base-index-of-next-cut
    (equal (cut-base-index (cut-next cut-idx cutsdb) cutsdb)
           (cut-next cut-idx cutsdb)))

  (defret next-cut-of-cut-base-index-bound
    (implies (equal (cut-base-index cut cutsdb1)
                    (cut-base-index cut cutsdb))
             (< (nfix cut) (cut-next (cut-base-index cut cutsdb1) cutsdb)))
    :hints (("goal" :in-theory (disable cut-base-index
                                        cut-base-index-monotonic)
             :use ((:instance cut-base-index-monotonic
                    (target-idx (cut-next (cut-base-index cut cutsdb) cutsdb))
                    (target-idx1 cut)))))
    :rule-classes :linear)

  (def-updater-independence-thm cut-base-index-updater-independence
    (implies (and (equal idx (+ (if (equal (nfix target-idx)
                                           (cut-base-index target-idx old))
                                    0
                                  1)
                                (cut-base-index target-idx old)))
                  (stobjs::range-nat-equiv 0 idx
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (equal (cut-base-index target-idx new)
                    (cut-base-index target-idx old)))
    :hints (("goal" :cases ((nat-equiv target-idx 0)))))

  (defthm cut-base-index-of-update-greater
    (implies (<= (nfix n) (nfix k))
             (equal (cut-base-index n (update-cut-datai k v cutsdb))
                    (cut-base-index n cutsdb)))
    :hints (("goal" :cases ((equal (nfix n) (cut-base-index n cutsdb)))
             :in-theory (disable cut-base-index))
            (and stable-under-simplificationp
                 '(:cases ((< (nfix n) (nfix k))))))))


(define cutp ((cut natp) cutsdb)
  :guard (<= cut (cut-data-length cutsdb))
  :returns (cutp booleanp :rule-classes :type-prescription)
  (eql (cut-base-index cut cutsdb) (lnfix cut))
  ///
  (defthm cutp-of-cut-base-index
    (implies (equal (cut-base-index cut cutsdb1)
                    (cut-base-index cut cutsdb))
             (cutp (cut-base-index cut cutsdb1) cutsdb)))

  (defthm cut-base-index-when-cutp
    (implies (cutp cut cutsdb)
             (equal (cut-base-index cut cutsdb)
                    (nfix cut))))

  (defthm cutp-of-cut-next
    (implies (and (cutp cut cutsdb)
                  (equal (cut-next cut cutsdb1)
                         (cut-next cut cutsdb)))
             (cutp (cut-next cut cutsdb1) cutsdb))
    :hints (("goal" :use ((:instance cut-base-index-of-next-cut
                           (target-idx cut)))
             :in-theory (disable cut-base-index-of-next-cut))))

  (defthm cutp-of-0
    (cutp 0 cutsdb))

  

  (def-updater-independence-thm cutp-updater-independence
    (implies (and (stobjs::range-nat-equiv 0 cut
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old))
                  (Cutp cut old))
             (cutp cut new)))

  (defthm cut-base-index-of-update-cut-data
    (implies (and (cutp cut cutsdb)
                  (<= (nfix cut) (nfix k)))
             (equal (cut-base-index cut (update-cut-datai k v cutsdb))
                    (cut-base-index cut cutsdb)))
    :hints (("goal" :use ((:instance cut-base-index-updater-independence
                           (new (update-cut-datai k v cutsdb))
                           (idx (cut-base-index cut cutsdb))
                           (target-idx cut)
                           (old cutsdb)))
             :in-theory (disable cut-base-index-updater-independence)))))


(defmacro cutp$ (x &optional (cutsdb 'cutsdb))
  (declare (xargs :guard (symbolp cutsdb)))
  `(let ((x ,x))
     (and (natp x)
          (< x (cut-data-length ,cutsdb))
          (cutp x ,cutsdb))))

(fty::set-fixequiv-guard-override cutp$ natp)

(defmacro cut-fix (x &optional (cutsdb 'cutsdb))
  `(let ((x ,x))
     (mbe :logic (cut-base-index x ,cutsdb)
          :exec x)))

(define cut-next$ ((cut cutp$) (cutsdb))
  ;; :guard (and (< cut (cut-data-length cutsdb))
  ;;             (cutp cut cutsdb))
  :returns (next natp :rule-classes :type-prescription)
  :inline t
  (cut-next (cut-fix cut)
            cutsdb)
  ///
  (defthm cut-next$-of-cut-base-index
    (implies (equal (cut-base-index cut cutsdb1)
                    (cut-base-index cut cutsdb))
             (equal (cut-next$ (cut-base-index cut cutsdb1) cutsdb)
                    (cut-next$ cut cutsdb))))

  (defthm cut-next$-cut-base-index-congruence
    (implies (and (equal m (cut-base-index n cutsdb))
                  (bind-free
                   (and (not (equal m n))
                        (let ((mm (case-match m
                                   (('cut-base-index mm &) mm)
                                   (('nfix mm) mm)
                                   (& m))))
                          (and (not (equal mm n))
                               `((mm . ,mm)))))
                   (mm))
                  (equal (cut-base-index mm cutsdb) m))
             (equal (cut-next$ n cutsdb)
                    (cut-next$ mm cutsdb))))

  (defthm cutp-of-cut-next$
    (implies (equal (cut-next$ cut cutsdb1)
                    (cut-next$ cut cutsdb))
             (cutp (cut-next$ cut cutsdb1) cutsdb)))

  (def-updater-independence-thm cut-next$-updater-independence
    ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
    (implies (and (equal idx (+ 1 (cut-base-index cut old)))
                  (stobjs::range-nat-equiv 0 idx
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (equal (cut-next$ cut new)
                    (cut-next$ cut old)))
    :hints(("Goal" :in-theory (disable stobjs::range-nat-equiv-open))))

  (defret cut-next$-lower-bound
    (< (nfix cut) (cut-next$ cut cutsdb))
    :rule-classes :linear)

  (defretd cut-next$-base-index-lower-bound
    (<= (+ 2 (cut-base-index cut cutsdb)) (cut-next$ cut cutsdb))
    :rule-classes :linear)

  (defret cut-next$-upper-bound
    (implies (and (< (cut-base-index cut cutsdb) max)
                  (natp max)
                  (cutp max cutsdb))
             (<= (cut-next$ cut cutsdb) max))
    :hints (("goal" :in-theory (disable cut-base-index-monotonic))
            (acl2::use-termhint
             (b* ((cut1 (cut-base-index cut cutsdb))
                  (nxt (cut-next cut1 cutsdb))
                  ((unless (< max nxt))
                   `'(:use ((:instance cut-base-index-monotonic
                             (target-idx ,(hq nxt))
                             (target-idx1 max))))))
               `'(:use ((:instance cut-base-index-of-less-than-next-cut
                         (other-idx max)
                         (target-idx cut)))))))
    :otf-flg t
    :rule-classes (:rewrite :linear))

  (defthm cut-base-index-of-less-than-cut-next$
    (implies (and (<= (cut-base-index target-idx cutsdb) (nfix other-idx))
                  (< other-idx (cut-next$ target-idx cutsdb)))
             (equal (cut-base-index other-idx cutsdb)
                    (cut-base-index target-idx cutsdb)))
    :hints (("goal" :use cut-base-index-of-less-than-next-cut))
    :rule-classes nil))


(local (defthm rewrite-to-cut-next$
         (implies (and (natp cut)
                       (nat-equiv cut1 cut)
                       (cutp cut1 cutsdb))
                  (equal (+ 2 cut (cut-datai cut1 cutsdb))
                         (cut-next$ cut1 cutsdb)))
         :hints(("Goal" :in-theory (enable cut-next cut-next$)))))
                  
(define cutsdb-cut-ok ((n cutp$) cutsdb)
  :guard-debug t
  :returns ok
  :prepwork ((local (in-theory (enable cut-next$-base-index-lower-bound))))
  ;; :guard-hints (("goal" :in-theory (enable cut-next)))
  ;; :guard (and (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
  ;;             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb)))
  (b* ((n (cut-fix n))
       (size (cut-datai n cutsdb)))
    (and (<= size 4)
         (< (cut-next$ n cutsdb) (cut-data-length cutsdb))
         ;; (<= (+ 2 size (lnfix n)) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (b* ((truth (cut-datai (+ 1 n) cutsdb)))
           (and (truth4-p truth)
                (truth4-deps-bounded size truth)
                (cutsdb-data-nodes-sorted (+ 2 n) size cutsdb)))))
  ///
  (def-updater-independence-thm cutsdb-cut-ok-updater-independence
    (implies (and (cutsdb-cut-ok n old)
                  ;; (equal (cut-next$ n new)
                  ;;        (cut-next$ n old))
                  (<= (cut-data-length old) (cut-data-length new))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
                  (equal next (cut-next$ n old))
                  (stobjs::range-nat-equiv 0 next (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-cut-ok n new))
    :hints(("Goal" :in-theory (disable stobjs::range-nat-equiv-open)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthm cutsdb-cut-ok-implies-truth4
    (implies (and (natp nn)
                  (cutp nn cutsdb)
                  (cutsdb-cut-ok nn cutsdb))
             (truth4-p (cut-datai (+ 1 nn) cutsdb))))

  (defthm cutsdb-cut-ok-implies-truth4-deps-bounded
    (implies (and (natp nn)
                  (equal (nfix n) nn)
                  (cutp nn cutsdb)
                  (cutsdb-cut-ok nn cutsdb))
             (truth4-deps-bounded (cut-datai n cutsdb)
                                  (cut-datai (+ 1 nn) cutsdb))))

  (defthm cutsdb-cut-ok-implies-nodes-sorted
    (implies (and (natp nn)
                  (equal (nfix n) nn)
                  (cutp nn cutsdb)
                  (cutsdb-cut-ok nn cutsdb))
             (cutsdb-data-nodes-sorted (+ 2 nn)
                                       (cut-datai n cutsdb)
                                       cutsdb)))

  (defthm cutsdb-cut-ok-of-update-cut-data-past-next
    (implies (and (<= (cut-next$ n cutsdb) (nfix k))
                  (cutsdb-cut-ok n cutsdb))
             (cutsdb-cut-ok n (update-cut-datai k v cutsdb)))
    :hints(("Goal" :in-theory (disable cutsdb-cut-ok)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthm cutsdb-cut-ok-implies-size
    (implies (and (cutp n cutsdb)
                  (cutsdb-cut-ok n cutsdb))
             (<= (cut-datai n cutsdb) 4))
    :rule-classes :linear)

  (defthm cutsdb-cut-ok-implies-cut-next$-less-than-length
    (implies (cutsdb-cut-ok n cutsdb)
             (< (cut-next$ n cutsdb) (cut-data-length cutsdb)))
    :rule-classes (:rewrite :linear))

  (defthm cutsdb-cut-ok-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-cut-ok (cut-base-index n cutsdb1) cutsdb)
                    (cutsdb-cut-ok n cutsdb)))))


(define cutsdb-cut-bounded ((n cutp$) (bound natp) cutsdb)
  :guard-debug t
  :returns ok
  :prepwork ((local (in-theory (enable cut-next$-base-index-lower-bound))))
  :guard (cutsdb-cut-ok n cutsdb)
  :guard-hints (("goal" :in-theory (enable cutsdb-cut-ok)))
  ;; :guard-hints (("goal" :in-theory (enable cut-next)))
  ;; :guard (and (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
  ;;             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb)))
  (b* ((n (cut-fix n))
       (size (cut-datai n cutsdb)))
    (cutsdb-data-nodes-bounded (+ 2 n) size bound cutsdb))
  ///
  (def-updater-independence-thm cutsdb-cut-bounded-updater-independence
    (implies (and (cutsdb-cut-bounded n bound old)
                  ;; (equal (cut-next$ n new)
                  ;;        (cut-next$ n old))
                  (<= (cut-data-length old) (cut-data-length new))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
                  (equal next (cut-next$ n old))
                  (stobjs::range-nat-equiv 0 next (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-cut-bounded n bound new))
    :hints(("Goal" :in-theory (disable stobjs::range-nat-equiv-open)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthmd cutsdb-cut-bounded-implies-nodes-bounded
    (implies (and (cutsdb-cut-bounded n bound cutsdb)
                  (<= (+ 2 (cut-fix n)) (nfix i))
                  (< (nfix i) (cut-next$ n cutsdb)))
             (< (cut-datai i cutsdb) (nfix bound)))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding
                                     cut-next$
                                     cut-next)
                                   (rewrite-to-cut-next$))
            :use ((:instance cutsdb-data-nodes-bounded-implies-compare
                   (idx (+ 2 (cut-fix n)))
                   (num (cut-datai (cut-fix n) cutsdb))
                   (n i)))))
    :rule-classes :linear)

  (defthm cutsdb-cut-bounded-of-update-cut-data-past-next
    (implies (and (<= (cut-next$ n cutsdb) (nfix k))
                  (cutsdb-cut-bounded n bound cutsdb))
             (cutsdb-cut-bounded n bound (update-cut-datai k v cutsdb)))
    :hints(("Goal" :in-theory (disable cutsdb-cut-bounded)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthm cutsdb-cut-bounded-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-cut-bounded (cut-base-index n cutsdb1) bound cutsdb)
                    (cutsdb-cut-bounded n bound cutsdb))))
  

  (defthm cutsdb-cut-bounded-of-equal-cut-base-index
    (implies (and (equal m (cut-base-index n cutsdb))
                  (bind-free
                   (and (not (equal m n))
                        (let ((mm (case-match m
                                   (('cut-base-index mm &) mm)
                                   (('nfix mm) mm)
                                   (& m))))
                          (and (not (equal mm n))
                               `((mm . ,mm)))))
                   (mm))
                  (equal (cut-base-index mm cutsdb) m))
             (equal (cutsdb-cut-bounded n bound cutsdb)
                    (cutsdb-cut-bounded mm bound cutsdb))))

  (defthmd cutsdb-cut-bounded-when-bounded-lesser
    (implies (and (cutsdb-cut-bounded n bound1 cutsdb)
                  (<= (nfix bound1) (nfix bound)))
             (cutsdb-cut-bounded n bound cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-data-nodes-bounded-when-bounded-lesser)))))

(define cut-measure ((cut natp)
                     (max natp)
                     (cutsdb))
  :returns (measure natp :rule-classes :type-prescription)
  :verify-guards nil
  ;; (if (< (nfix cut) (nfix max))
      (nfix (- (nfix max)
               (cut-base-index cut cutsdb)))
      ;; 0)
  ///
  (defret cut-measure-of-cut-next$
    (implies (posp (- (nfix max)
                      (cut-base-index cut cutsdb)))
             (< (cut-measure (cut-next$ cut cutsdb) max cutsdb)
                (cut-measure cut max cutsdb)))
    :hints(("Goal" :in-theory (enable cut-next$))))

  (defret cut-measure-of-cut-base-index-cut
    (equal (cut-measure (cut-base-index cut cutsdb) max cutsdb)
           (cut-measure cut max cutsdb))
    :hints (("goal" :use (;; (:instance cut-base-index-monotonic
                          ;;  (target-idx (cut-base-index cut cutsdb))
                          ;;  (target-idx1 max))
                          (:instance cut-base-index-monotonic
                           (target-idx max)
                           (target-idx1 cut)))
             :in-theory (disable cut-base-index-monotonic))))

  ;; (defret cut-measure-of-cut-base-index-max
  ;;   (equal (cut-measure cut (cut-base-index max cutsdb) cutsdb)
  ;;          (cut-measure cut max cutsdb))
  ;;   :hints (("goal" :use ((:instance cut-base-index-monotonic
  ;;                          (target-idx (cut-base-index max cutsdb))
  ;;                          (target-idx1 cut)))
  ;;            :in-theory (disable cut-base-index-monotonic))))

  (def-updater-independence-thm cut-measure-updater-independence
    ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
    (implies (and (equal idx (+ (if (cutp cut old) 0 1)
                                (cut-base-index cut old)))
                  (stobjs::range-nat-equiv 0 idx
                                       (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (equal (cut-measure cut max new)
                    (cut-measure cut max old)))
    :hints(("Goal" :in-theory (disable stobjs::range-nat-equiv-open)))))


(define cutsdb-data-ok ((n cutp$) (max natp) cutsdb)
  :guard (and (<= n max)
              (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb))
              (<= max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  :measure (cut-measure n max cutsdb)
  :returns ok
  (b* ((n (cut-fix n))
       ((when (mbe :logic (zp (- (nfix max) (nfix n)))
                   :exec (eql n max)))
        t)
       ;; (size (cut-datai n cutsdb))
        (next (cut-next$ n cutsdb)))
    (and (cutsdb-cut-ok n cutsdb)
         (<= next (lnfix max))
         ;; (<= next (lnfix max))
         ;; (mbt (<= next (cut-data-length cutsdb))) ;; (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
         ;; (b* ((truth (cut-datai (+ 1 (lnfix n)) cutsdb)))
         ;;   (and (truth4-p truth)
         ;;        (truth4-deps-bounded size truth)
         ;;        (cutsdb-data-nodes-sorted (+ 2 (lnfix n)) size cutsdb)
         (cutsdb-data-ok next max cutsdb)))
  ///
  (local (in-theory (disable (:d cutsdb-data-ok))))

  (def-updater-independence-thm cutsdb-data-ok-updater-independence
    (implies (and (cutsdb-data-ok n max old)
                  (<= (cut-data-length old) (cut-data-length new))
                  ;; (cutp n new)
                  ;; (cutp n old)
                  (<= (nfix n) (nfix max))
                  (stobjs::range-nat-equiv 0 max (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-data-ok n max new))
    :hints(("Goal" :in-theory (e/d (;; cut-next
                                    )
                                   (stobjs::range-nat-equiv-open))
            :induct (cutsdb-data-ok n max old)
            :expand ((:free (x) (cutsdb-data-ok n max x))))))

  (defretd cutsdb-data-ok-implies-next
    (implies (and ok
                  (equal (cut-next$ n cutsdb1) (cut-next$ n cutsdb))
                  (< (nfix n) (nfix max)))
             (cutsdb-data-ok (cut-next$ n cutsdb1) max cutsdb))
    :hints (("Goal" 
            :induct (cutsdb-data-ok n max cutsdb)
            :expand ((:free (cutsdb) (cutsdb-data-ok n max cutsdb))))))

  (defretd open-cutsdb-data-ok
    (implies (and (acl2::rewriting-negative-literal `(cutsdb-data-ok ,n ,max ,cutsdb))
                  (< (nfix n) (nfix max)))
             (equal ok
                    (and (cutsdb-cut-ok n cutsdb)
                         (<= (cut-next$ n cutsdb) (lnfix max))
                         (cutsdb-data-ok (cut-next$ n cutsdb) max cutsdb))))
    :hints(("Goal" :in-theory (enable cutsdb-cut-ok)
            :expand ((cutsdb-data-ok n max cutsdb)))))

  (defthmd cutsdb-data-ok-compose
    (implies (and (cutsdb-data-ok a b cutsdb)
                  (cutsdb-data-ok b c cutsdb)
                  (<= (nfix a) (nfix b))
                  (<= (nfix b) (nfix c)))
             (cutsdb-data-ok a c cutsdb))
    :hints (("goal" :induct (cutsdb-data-ok a b cutsdb)
             :in-theory (e/d* (acl2::arith-equiv-forwarding)
                              (open-cutsdb-data-ok))
             :expand ((:free (b) (cutsdb-data-ok a b cutsdb))
                      (cutsdb-data-ok b c cutsdb)))))

  (defthm cutsdb-data-ok-implies-max-cutp
    (implies (and (cutsdb-data-ok n m cutsdb)
                  (<= (nfix n) (nfix m)))
             (cutp m cutsdb))
    :hints (("Goal" 
             :in-theory (enable cutp)
            :induct (cutsdb-data-ok n m cutsdb)
            :expand ((:free (cutsdb) (cutsdb-data-ok n m cutsdb))))))

  (defthm cutsdb-data-ok-of-add-node
    (implies (and (cutsdb-data-ok n m cutsdb)
                  (<= (nfix n) (nfix m)))
             (b* (;; (size (cut-datai m cutsdb))
                  ;; (truth (cut-datai (+ 1 (nfix m)) cutsdb))
                  ;; (data (+ 2 (nfix m)))
                  (next (cut-next$ m cutsdb)))
               (implies (and (cutsdb-cut-ok m cutsdb)
                             ;; (<= size 4)
                             ;; (<= next (cut-data-length cutsdb))
                             ;; (truth4-p truth)
                             ;; (truth4-deps-bounded size truth)
                             ;; (cutsdb-data-nodes-sorted data size cutsdb)
                             )
                        (cutsdb-data-ok n next cutsdb))))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct (cutsdb-data-ok n m cutsdb)
            :expand ((:free (m cutsdb) (cutsdb-data-ok n m cutsdb))
                     (:free (n) (cutsdb-data-ok n n cutsdb))))))

  ;; (defthm cutsdb-data-ok-of-add-node
  ;;   (implies (and (cutsdb-data-ok n m cutsdb)
  ;;                 (<= (nfix n) m))
  ;;            (b* (;; (size (cut-datai m cutsdb))
  ;;                 ;; (truth (cut-datai (+ 1 m) cutsdb))
  ;;                 ;; (data (+ 2 m))
  ;;                 (next (cut-next m cutsdb)))
  ;;              (implies (and (natp m)
  ;;                            (cutsdb-cut-ok m cutsdb);; (natp m)
  ;;                            ;; (<= size 4)
  ;;                            ;; (<= next (cut-data-length cutsdb))
  ;;                            ;; (truth4-p truth)
  ;;                            ;; (truth4-deps-bounded size truth)
  ;;                            ;; (cutsdb-data-nodes-sorted data size cutsdb)
  ;;                            )
  ;;                       (cutsdb-data-ok n next cutsdb))))
  ;;   :hints (("goal" :use cutsdb-data-ok-of-add-node-nfix
  ;;            :in-theory (disable cutsdb-data-ok-of-add-node-nfix))))

  
  (defthm cutsdb-data-ok-of-update-past-last
    (implies (and (cutsdb-data-ok n m cutsdb)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (nfix k)))
             (cutsdb-data-ok n m (update-cut-datai k v cutsdb)))
    :hints (("goal" :induct (cutsdb-data-ok n m cutsdb)
             :expand ((:free (cutsdb) (cutsdb-data-ok n m cutsdb))))
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix n) (nfix k)))))))

  (defthm cutsdb-data-ok-self
    (implies (cutp n cutsdb)
             (cutsdb-data-ok n n cutsdb))
    :hints (("goal" :expand ((cutsdb-data-ok n n cutsdb)))))

  (local (defthm cut-base-index-not-out-of-order
           (implies (<= (cut-base-index n cutsdb) (nfix k))
                    (<= (cut-base-index n cutsdb) (cut-base-index k cutsdb)))
           :hints (("goal" :use ((:instance cut-base-index-monotonic
                                  (target-idx (cut-base-index n cutsdb))
                                  (target-idx1 k)))
                    :in-theory (disable cut-base-index-monotonic)))))

  ;; (local (defthm cut-base-index-when-less-than-next
  ;;          (implies (and (<= (cut-base-index n cutsdb) (nfix k))
  ;;                        (< (nfix k) (cut-next$ n cutsdb)))
  ;;                   (equal (cut-base-index k cutsdb)
  ;;                          (cut-base-index n cutsdb)))
  ;;          :hints (("goal" :use ((:instance cut-base-index-monotonic
  ;;                                 (target-idx))

  (local (defthm cutsdb-cut-ok-when-base-indices-equal
           (implies (equal (Cut-base-index k cutsdb)
                           (Cut-base-index n cutsdb))
                    (equal (cutsdb-cut-ok k cutsdb)
                           (cutsdb-cut-ok n cutsdb)))
           :hints(("Goal" :in-theory (enable cutsdb-cut-ok)))
           :rule-classes nil))

  (defthmd cutsdb-cut-ok-when-data-ok
    (implies (and (cutsdb-data-ok n m cutsdb)
                  (<= (cut-base-index n cutsdb) (nfix k))
                  (< (cut-base-index k cutsdb) (nfix m)))
             (cutsdb-cut-ok k cutsdb))
    :hints (("goal" :induct (cutsdb-data-ok n m cutsdb)
             :expand ((:free (cutsdb) (cutsdb-data-ok n m cutsdb)))
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (acl2::use-termhint
             (b* (((when (<= (nfix m) (cut-base-index n cutsdb)))
                   `'(:use ((:instance cut-base-index-not-out-of-order))
                      :in-theory (disable cut-base-index-not-out-of-order))))
               `'(:use ((:instance cut-base-index-of-less-than-cut-next$
                         (other-idx (nfix k))
                         (target-idx n))
                        cutsdb-cut-ok-when-base-indices-equal))))))

  ;; (defthm cutsdb-data-ok-implies-max-less-than-cut-data-length
  ;;   (implies (and (cutsdb-data-ok n m cutsdb)
  ;;                 (natp m)
  ;;                 (<= (nfix n) m)
  ;;                 (< (cut-base-index n cutsdb) (cut-data-length cutsdb)))
  ;;            (< m (cut-data-length cutsdb)))
  ;;   :hints (("goal" :induct (cutsdb-data-ok n m cutsdb)
  ;;            :expand ((:free (cutsdb) (cutsdb-data-ok n m cutsdb))))))
  

  (defthm cutsdb-data-ok-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-data-ok (cut-base-index n cutsdb1) m cutsdb)
                    (cutsdb-data-ok n m cutsdb)))
    :hints (("goal"
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-ok n m cutsdb))
                      (:free (cutsdb) (cutsdb-data-ok (cut-base-index n cutsdb) m cutsdb)))))))


(define cutsdb-data-bounds-ok ((n cutp$) (max cutp$) (bound natp) cutsdb)
  :guard (and (<= n max)
              (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb))
              (<= max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (cutsdb-data-ok n max cutsdb))
  :guard-hints (("goal" :in-theory (enable open-cutsdb-data-ok)))
  :measure (cut-measure n (cut-fix max) cutsdb)
  :returns ok
  (b* ((n (cut-fix n))
       (max (cut-fix max))
       ((when (mbe :logic (zp (- max n))
                   :exec (eql n max)))
        t)
       ;; (size (cut-datai n cutsdb))
        (next (cut-next$ n cutsdb)))
    (and (cutsdb-cut-bounded n bound cutsdb)
         ;; (<= next (lnfix max))
         ;; (mbt (<= next (cut-data-length cutsdb))) ;; (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
         ;; (b* ((truth (cut-datai (+ 1 (lnfix n)) cutsdb)))
         ;;   (and (truth4-p truth)
         ;;        (truth4-deps-bounded size truth)
         ;;        (cutsdb-data-nodes-sorted (+ 2 (lnfix n)) size cutsdb)
         (cutsdb-data-bounds-ok next max bound cutsdb)))
  ///
  (local (in-theory (disable (:d cutsdb-data-bounds-ok))))

  (def-updater-independence-thm cutsdb-data-bounds-ok-updater-independence
    (implies (and (equal max-fix (cut-fix max old))
                  (equal (cut-fix max new) max-fix)
                  (equal (cut-fix n new) (cut-fix n old))
                  (cutsdb-data-bounds-ok n max bound old)
                  (<= (cut-data-length old) (cut-data-length new))
                  ;; (cutp n new)
                  ;; (cutp n old)
                  ;; (<= (cut-fix n old) max-fix)
                  (stobjs::range-nat-equiv 0 max-fix (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-data-bounds-ok n max bound new))
    :hints(("Goal" :in-theory (e/d (;; cut-next
                                    )
                                   (stobjs::range-nat-equiv-open))
            :induct (cutsdb-data-bounds-ok n max bound old)
            :expand ((:free (x) (cutsdb-data-bounds-ok n max bound x))))))

  (defthm cutsdb-data-bounds-ok-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-data-bounds-ok (cut-base-index n cutsdb1) m bound cutsdb)
                    (cutsdb-data-bounds-ok n m bound cutsdb)))
    :hints (("goal"
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-bounds-ok n m bound cutsdb))
                      (:free (cutsdb) (cutsdb-data-bounds-ok (cut-base-index n cutsdb) m bound cutsdb))))))

  (defthm cutsdb-data-bounds-ok-of-cut-base-index-max
    (implies (equal (cut-base-index m cutsdb1) (cut-base-index m cutsdb))
             (equal (cutsdb-data-bounds-ok n (cut-base-index m cutsdb1) bound cutsdb)
                    (cutsdb-data-bounds-ok n m bound cutsdb)))
    :hints (("goal"
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-bounds-ok n m bound cutsdb))
                      (:free (cutsdb) (cutsdb-data-bounds-ok n (cut-base-index m cutsdb) bound cutsdb))))))

  (defretd cutsdb-data-bounds-ok-implies-next
    (implies (and ok
                  (equal (cut-next$ n cutsdb1) (cut-next$ n cutsdb))
                  (< (cut-fix n) (cut-fix max)))
             (cutsdb-data-bounds-ok (cut-next$ n cutsdb1) max bound cutsdb))
    :hints (("Goal" 
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-bounds-ok n max bound cutsdb))))))

  (defretd open-cutsdb-data-bounds-ok
    (implies (and (acl2::rewriting-negative-literal `(cutsdb-data-bounds-ok ,n ,max ,bound ,cutsdb))
                  (< (cut-fix n) (cut-fix max)))
             (equal ok
                    (and (cutsdb-cut-bounded n bound cutsdb)
                         (cutsdb-data-bounds-ok (cut-next$ n cutsdb) max bound cutsdb))))
    :hints(("Goal" :in-theory (enable cutsdb-cut-bounded)
            :expand ((cutsdb-data-bounds-ok n max bound cutsdb)))))

  (defthmd cutsdb-data-bounds-ok-compose
    (implies (and (cutsdb-data-bounds-ok a b bound cutsdb)
                  (cutsdb-data-bounds-ok b c bound cutsdb)
                  (<= (cut-fix a) (cut-fix b))
                  (<= (cut-fix b) (cut-fix c)))
             (cutsdb-data-bounds-ok a c bound cutsdb))
    :hints (("goal" :induct (cutsdb-data-bounds-ok a b bound cutsdb)
             :in-theory (e/d* (acl2::arith-equiv-forwarding)
                              (open-cutsdb-data-bounds-ok))
             :expand ((:free (b) (cutsdb-data-bounds-ok a b bound cutsdb))
                      (cutsdb-data-bounds-ok b c bound cutsdb)))
            ;; (and stable-under-simplificationp
            ;;      '(:use ((:instance cut-next$-of-cut-base-index
            ;;               (cut a) (cutsdb1 cutsdb))
            ;;              (:instance cut-next$-of-cut-base-index
            ;;               (cut b) (cutsdb1 cutsdb))
            ;;              (:instance cutsdb-cut-bounded-of-cut-base-index
            ;;               (n a) (cutsdb1 cutsdb))
            ;;              (:instance cutsdb-cut-bounded-of-cut-base-index
            ;;               (n b) (cutsdb1 cutsdb)))
            ;;        :in-theory (disable cut-next$-of-cut-base-index
            ;;                            cutsdb-cut-bounded-of-cut-base-index)))
            ))


  (defthm cutsdb-data-bounds-ok-of-add-node
    (implies (and (cutsdb-data-bounds-ok n m bound cutsdb)
                  (<= (cut-fix n) (cut-fix m)))
             (b* (;; (size (cut-datai m cutsdb))
                  ;; (truth (cut-datai (+ 1 (nfix m)) cutsdb))
                  ;; (data (+ 2 (nfix m)))
                  (next (cut-next$ m cutsdb)))
               (implies (and (cutsdb-cut-bounded m bound cutsdb)
                             ;; (<= size 4)
                             ;; (<= next (cut-data-length cutsdb))
                             ;; (truth4-p truth)
                             ;; (truth4-deps-bounded size truth)
                             ;; (cutsdb-data-nodes-sorted data size cutsdb)
                             )
                        (cutsdb-data-bounds-ok n next bound cutsdb))))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct (cutsdb-data-bounds-ok n m bound cutsdb)
            :expand ((:free (m cutsdb) (cutsdb-data-bounds-ok n m bound cutsdb))
                     (:free (n) (cutsdb-data-bounds-ok n n bound cutsdb))))))

  ;; (defthm cutsdb-data-bounds-ok-of-add-node
  ;;   (implies (and (cutsdb-data-bounds-ok n m bound cutsdb)
  ;;                 (<= (nfix n) m))
  ;;            (b* (;; (size (cut-datai m cutsdb))
  ;;                 ;; (truth (cut-datai (+ 1 m) cutsdb))
  ;;                 ;; (data (+ 2 m))
  ;;                 (next (cut-next m cutsdb)))
  ;;              (implies (and (natp m)
  ;;                            (cutsdb-cut-bounded m bound cutsdb);; (natp m)
  ;;                            ;; (<= size 4)
  ;;                            ;; (<= next (cut-data-length cutsdb))
  ;;                            ;; (truth4-p truth)
  ;;                            ;; (truth4-deps-bounded size truth)
  ;;                            ;; (cutsdb-data-nodes-sorted data size cutsdb)
  ;;                            )
  ;;                       (cutsdb-data-bounds-ok n next bound cutsdb))))
  ;;   :hints (("goal" :use cutsdb-data-bounds-ok-of-add-node-nfix
  ;;            :in-theory (disable cutsdb-data-bounds-ok-of-add-node-nfix))))

  
  (defthm cutsdb-data-bounds-ok-of-update-past-last
    (implies (and (cutsdb-data-bounds-ok n m bound cutsdb)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (nfix k)))
             (cutsdb-data-bounds-ok n m bound (update-cut-datai k v cutsdb)))
    :hints (("goal" :in-theory (disable cutsdb-data-bounds-ok))))

  (defthm cutsdb-data-bounds-ok-self
    (implies (cutp n cutsdb)
             (cutsdb-data-bounds-ok n n bound cutsdb))
    :hints (("goal" :expand ((cutsdb-data-bounds-ok n n bound cutsdb)))))

  (local (defthm cut-base-index-not-out-of-order
           (implies (<= (cut-base-index n cutsdb) (nfix k))
                    (<= (cut-base-index n cutsdb) (cut-base-index k cutsdb)))
           :hints (("goal" :use ((:instance cut-base-index-monotonic
                                  (target-idx (cut-base-index n cutsdb))
                                  (target-idx1 k)))
                    :in-theory (disable cut-base-index-monotonic)))))

  ;; (local (defthm cut-base-index-when-less-than-next
  ;;          (implies (and (<= (cut-base-index n cutsdb) (nfix k))
  ;;                        (< (nfix k) (cut-next$ n cutsdb)))
  ;;                   (equal (cut-base-index k cutsdb)
  ;;                          (cut-base-index n cutsdb)))
  ;;          :hints (("goal" :use ((:instance cut-base-index-monotonic
  ;;                                 (target-idx (nfix k))
  ;;                                 (target-idx1 (+ -1 (cut-next$ n cutsdb))))
  ;;                                (:instance cut-base-index-monotonic
  ;;                                 (target-idx (cut-fix n))
  ;;                                 (target-idx1 )))
  ;;                   :in-theory (disable cut-base-index-monotonic
  ;;                                       cut-base-index-not-out-of-order)))))

  ;; (local (defthm cutsdb-cut-bounded-when-base-indices-equal
  ;;          (implies (equal (Cut-base-index k cutsdb)
  ;;                          (Cut-base-index n cutsdb))
  ;;                   (equal (cutsdb-cut-bounded k bound cutsdb)
  ;;                          (cutsdb-cut-bounded n bound cutsdb)))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-cut-bounded)))
  ;;          :rule-classes nil))

  (defthmd cutsdb-cut-bounded-when-data-bounds-ok
    (implies (and (cutsdb-data-bounds-ok n m bound cutsdb)
                  (<= (cut-base-index n cutsdb) (nfix k))
                  (< (cut-base-index k cutsdb) (cut-fix m)))
             (cutsdb-cut-bounded k bound cutsdb))
    :hints (("goal" :induct (cutsdb-data-bounds-ok n m bound cutsdb)
             :expand ((:free (cutsdb) (cutsdb-data-bounds-ok n m bound cutsdb)))
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (acl2::use-termhint
             (b* (((when (<= (nfix m) (cut-base-index n cutsdb)))
                   `'(:use ((:instance cut-base-index-not-out-of-order))
                      :in-theory (disable cut-base-index-not-out-of-order))))
               `'(:use ((:instance cut-base-index-of-less-than-cut-next$
                         (other-idx (nfix k))
                         (target-idx n))
                        ;; cutsdb-cut-bounded-when-base-indices-equal
                        ))))))

  ;; (defthm cutsdb-data-bounds-ok-implies-max-less-than-cut-data-length
  ;;   (implies (and (cutsdb-data-bounds-ok n m bound cutsdb)
  ;;                 (natp m)
  ;;                 (<= (nfix n) m)
  ;;                 (< (cut-base-index n cutsdb) (cut-data-length cutsdb)))
  ;;            (< m (cut-data-length cutsdb)))
  ;;   :hints (("goal" :induct (cutsdb-data-bounds-ok n m bound cutsdb)
  ;;            :expand ((:free (cutsdb) (cutsdb-data-bounds-ok n m bound cutsdb))))))
  
  
  )



(define cutsdb-nodecuts-ok ((n natp) cutsdb)
  :guard (and (<= n (cut-nnodes cutsdb))
              (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
              (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                  (cut-data-length cutsdb))
              (<= (nodecut-indicesi n cutsdb)
                  (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (cutp (nodecut-indicesi n cutsdb) cutsdb))
  :measure (nfix (- (cut-nnodes cutsdb) (nfix n)))
  :returns ok
  ;; :verify-guards nil
  (b* (((when (mbe :logic (zp (- (cut-nnodes cutsdb) (nfix n)))
                   :exec (eql n (cut-nnodes cutsdb))))
        (mbt (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb))))
       (data-start (nodecut-indicesi n cutsdb))
       (data-next (nodecut-indicesi (+ 1 (lnfix n)) cutsdb)))
    (and (<= data-start data-next)
         (<= data-next (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (cutsdb-data-ok data-start data-next cutsdb)
         (cutsdb-data-bounds-ok data-start data-next (+ 1 (lnfix n)) cutsdb)
         (cutsdb-nodecuts-ok (+ 1 (lnfix n)) cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-nodecuts-ok-updater-independence
    (implies (and (cutsdb-nodecuts-ok n old)
                  (equal (nth *cut-nnodes1* new) (nth *cut-nnodes1* old))
                  (equal (nth (cut-nnodes old) (nth *nodecut-indicesi1* new))
                         (nth (cut-nnodes old) (nth *nodecut-indicesi1* old)))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
                  (equal old-minus-n (- (cut-nnodes old) (nfix n)))
                  (stobjs::range-nat-equiv n old-minus-n
                                       (nth *nodecut-indicesi1* new)
                                       (nth *nodecut-indicesi1* old))
                  (equal max-idx (nodecut-indicesi (cut-nnodes old) old))
                  (stobjs::range-nat-equiv 0 max-idx
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old))
                  (<= (cut-data-length old) (cut-data-length new)))
             (cutsdb-nodecuts-ok n new))
    :hints((and stable-under-simplificationp
                (equal (car id) '(0))
                '(:in-theory (disable stobjs::range-nat-equiv-open)
                  :induct (cutsdb-nodecuts-ok n new)))
           (and stable-under-simplificationp
                '(:cases ((equal (+ 1 (nfix n)) (cut-nnodes old)))))
           (and stable-under-simplificationp
                '(:cases ((equal (nodecut-indicesi n old)
                                 (nodecut-indicesi (cut-nnodes old) old)))))))
                  

  (defret cutsdb-nodecuts-ok-implies-start-<=-next
    (implies (and ok
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi m cutsdb) (nodecut-indicesi (+ 1 (nfix m)) cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (local (defret cutsdb-nodecuts-ok-implies-last-<-len-lemma
           (implies (and ok
                         (<= (nfix n) (cut-nnodes cutsdb)))
                    (<= (nodecut-indicesi n cutsdb)
                        (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
           :rule-classes :linear))

  (defret cutsdb-nodecuts-ok-implies-last-<-len
    (implies (and ok
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi m cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes (:rewrite :linear))

  

  (local (defret cutsdb-nodecuts-ok-implies-indices-monotonic-lemma
           (implies (and ok
                         (<= (nfix n) (nfix j))
                         (<= (nfix j) (cut-nnodes cutsdb)))
                    (<= (nodecut-indicesi n cutsdb) (nodecut-indicesi j cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
           :rule-classes ((:linear :match-free :all))))

  (defret cutsdb-nodecuts-ok-implies-indices-monotonic
    (implies (and ok
                  (<= (nfix n) (nfix i))
                  (<= (nfix i) (nfix j))
                  (<= (nfix j) (cut-nnodes cutsdb)))
             (<= (nodecut-indicesi i cutsdb) (nodecut-indicesi j cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes (:rewrite (:linear :match-free :all)))

  (defret cutsdb-nodecuts-ok-implies-data-ok
    (implies (and ok
                  (<= (nfix n) (nfix m))
                  (equal (nfix m+1) (+ 1 (nfix m)))
                  (< (nfix m) (cut-nnodes cutsdb)))
             (cutsdb-data-ok (nodecut-indicesi m cutsdb)
                             (nodecut-indicesi m+1 cutsdb)
                             cutsdb))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret cutsdb-nodecuts-ok-implies-data-bounds-ok
    (implies (and ok
                  (equal mm (nfix m))
                  (<= (nfix n) mm)
                  (equal (nfix m+1) (+ 1 mm))
                  (< (nfix m) (cut-nnodes cutsdb)))
             (cutsdb-data-bounds-ok (nodecut-indicesi m cutsdb)
                                    (nodecut-indicesi m+1 cutsdb)
                                    (+ 1 mm)
                                    cutsdb))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct t)))

  (verify-guards cutsdb-nodecuts-ok :guard-debug t)

  (defret open-cutsdb-nodecuts-ok
    (implies (and (acl2::rewriting-negative-literal `(cutsdb-nodecuts-ok ,n ,cutsdb))
                  (< (nfix n) (cut-nnodes cutsdb)))
             (equal ok
                    (b* ((data-start (nodecut-indicesi n cutsdb))
                         (data-next (nodecut-indicesi (+ 1 (lnfix n)) cutsdb)))
                      (and (<= data-start data-next)
                           ;; (<= data-next (cut-data-length cutsdb))
                           (cutsdb-data-ok data-start data-next cutsdb)
                           (cutsdb-data-bounds-ok data-start data-next (+ 1 (lnfix n)) cutsdb)
                           (cutsdb-nodecuts-ok (+ 1 (lnfix n)) cutsdb))))))

  
  (defret cutsdb-nodecuts-ok-implies-cutp-of-nodecut-indices
    (implies (and (equal (nodecut-indicesi m cutsdb1)
                         (nodecut-indicesi m cutsdb))
                  (cutsdb-nodecuts-ok n cutsdb)
                  (cutp (nodecut-indicesi n cutsdb) cutsdb)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (cutp (nodecut-indicesi m cutsdb1) cutsdb))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret cutsdb-nodecuts-ok-implies-cutsdb-data-ok-long
    (implies (and ok
                  (cutp (nodecut-indicesi n cutsdb) cutsdb)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (cutsdb-data-ok (nodecut-indicesi n cutsdb)
                             (nodecut-indicesi m cutsdb)
                             cutsdb))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
            :induct t)
           (and stable-under-simplificationp
                '(:cases ((< (nfix n) (nfix m)))))
           (and stable-under-simplificationp
                '(;; :expand ((:free (x) (cutsdb-data-ok x x cutsdb)))
                  :in-theory (enable* cutsdb-data-ok-compose
                                      acl2::arith-equiv-forwarding)))))

  (defthm cutsdb-nodecuts-ok-of-update-past-last
    (implies (and (cutsdb-nodecuts-ok n cutsdb)
                  (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix k)))
             (cutsdb-nodecuts-ok n (update-cut-datai k v cutsdb))))

  
  (defthm cutsdb-nodecuts-ok-of-update-last-node
    (implies (cutsdb-nodecuts-ok n cutsdb)
             (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (size (cut-datai m cutsdb))
                  ;; (truth (cut-datai (+ 1 m) cutsdb))
                  ;; (data (+ 2 m))
                  )
               (implies (and (cutsdb-cut-ok m cutsdb)
                             (cutsdb-cut-bounded m (cut-nnodes cutsdb) cutsdb)
                             ;; (cutp (nodecut-indicesi n cutsdb) cutsdb)
                             ;; (< (nodecut-indicesi n cutsdb) (cut-data-length cutsdb))
                             ;; (<= size 4)
                             ;; (<= (+ 2 m size) (cut-data-length cutsdb))
                             ;; (truth4-p truth)
                             ;; (truth4-deps-bounded size truth)
                             ;; (cutsdb-data-nodes-sorted data size cutsdb)
                             )
                        (cutsdb-nodecuts-ok n (update-nodecut-indicesi (cut-nnodes cutsdb)
                                                                       (cut-next$ m cutsdb)
                                                                       cutsdb)))))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct (cutsdb-nodecuts-ok n cutsdb))
            (and stable-under-simplificationp
                 '(:cases ((equal (+ 1 (nfix n)) (cut-nnodes cutsdb)))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable cutsdb-cut-ok)))
            ))

  (defthmd cutsdb-cut-ok-when-nodecuts-ok
    (implies (and (cutsdb-nodecuts-ok n cutsdb)
                  (<= (nodecut-indicesi n cutsdb)
                      (nfix k))
                  (<= (nfix n) (cut-nnodes cutsdb))
                  (< (nfix k) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cutp (nodecut-indicesi n cutsdb) cutsdb))
             (cutsdb-cut-ok k cutsdb))
    :hints (("goal" :in-theory (enable cutsdb-cut-ok-when-data-ok))))
  
  (defthmd cutsdb-cut-bounded-when-nodecuts-ok
    (implies (and (cutsdb-nodecuts-ok n cutsdb)
                  (<= (nodecut-indicesi n cutsdb)
                      (nfix k))
                  (<= (nfix n) (cut-nnodes cutsdb))
                  (< (nfix k) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cutp (nodecut-indicesi n cutsdb) cutsdb))
             (cutsdb-cut-bounded k (cut-nnodes cutsdb) cutsdb))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance cutsdb-cut-bounded-when-data-bounds-ok
                          (n (nodecut-indicesi n cutsdb))
                          (m (nodecut-indicesi (+ 1 (nfix n)) cutsdb))
                          (bound (+ 1 (nfix n)))))
                   :in-theory (enable cutsdb-cut-bounded-when-bounded-lesser))))))

(define cutsdb-ok (cutsdb)
  :returns (ok)
  (and (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
       (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb))
       (eql (nodecut-indicesi 0 cutsdb) 0)
       (cutsdb-nodecuts-ok 0 cutsdb))
  ///

  (defthm cutsdb-ok-implies-initial-nodecut-index
    (implies (cutsdb-ok cutsdb)
             (equal (nodecut-indicesi 0 cutsdb) 0)))
  

  (defret cutsdb-ok-implies-nodecut-indices-monotonic
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb))
                  (<= (nfix n) (nfix m)))
             (<= (nodecut-indicesi n cutsdb) (nodecut-indicesi m cutsdb))))

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

  (defret cutsdb-ok-implies-indices-in-range
    (implies (and ok
                  (<= (nfix m) (cut-nnodes cutsdb)))
             (< (nodecut-indicesi m cutsdb) (cut-data-length cutsdb)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
    :rule-classes (:rewrite :linear))

  (defret cutsdb-ok-implies-nnodes-<-indices-length
    (implies ok
             (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb)))
    :rule-classes (:rewrite :linear))

  (defret cutsdb-data-ok-when-cutsdb-ok
    (implies (and ok
                  (equal n+1 (+ 1 (nfix n)))
                  (< (nfix n) (cut-nnodes cutsdb)))
             (cutsdb-data-ok (nodecut-indicesi n cutsdb)
                             (nodecut-indicesi n+1 cutsdb)
                             cutsdb))
    :hints(("Goal" :in-theory (disable open-cutsdb-nodecuts-ok))))

  (defret cutsdb-data-bounds-ok-when-cutsdb-ok
    (implies (and ok
                  (equal n+1 (+ 1 (nfix n)))
                  (< (nfix n) (cut-nnodes cutsdb)))
             (cutsdb-data-bounds-ok (nodecut-indicesi n cutsdb)
                                    (nodecut-indicesi n+1 cutsdb)
                                    n+1
                                    cutsdb))
    :hints(("Goal" :in-theory (disable open-cutsdb-nodecuts-ok))))

  ;; (defret cutsdb-ok-implies-indices-monotonic
  ;;   (implies (and ok
  ;;                 (<= (nfix i) (nfix j))
  ;;                 (<= (nfix j) (cut-nnodes cutsdb)))
  ;;            (<= (nodecut-indicesi i cutsdb) (nodecut-indicesi j cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
  ;;   :rule-classes (:rewrite (:linear :match-free :all)))



  (defthm cutsdb-ok-implies-cut-less-than-length
    (implies (and (cutp n cutsdb)
                  (cutsdb-ok cutsdb)
                  (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (and (< (nfix n) (cut-data-length cutsdb))
                  (< (+ 1 (nfix n)) (cut-data-length cutsdb))
                  (<= (+ 2 (nfix n)) (cut-data-length cutsdb))
                  ;; (<= (cut-next$ n cutsdb) (cut-data-length cutsdb))
                  (implies (natp n)
                           (and (< n (cut-data-length cutsdb))
                                (< (+ 1 n) (cut-data-length cutsdb))
                                (<= (+ 2 n) (cut-data-length cutsdb))))))
    :hints(("Goal" :in-theory (enable cutsdb-cut-ok)
            :do-not-induct t))
    :otf-flg t)

  (defthm cutsdb-ok-implies-cutsdb-cut-ok
    (implies (and (cutsdb-ok cutsdb)
                  (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-cut-ok n cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-cut-ok-when-nodecuts-ok))))

  (defthm cutsdb-cut-bounded-when-cutsdb-ok
    (implies (and (cutsdb-ok cutsdb)
                  (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-cut-bounded n (cut-nnodes cutsdb) cutsdb))
    :hints (("goal" :in-theory (enable cutsdb-cut-bounded-when-nodecuts-ok))))

  (defthm cutsdb-ok-implies-cutsdb-data-ok
    (implies (and (cutsdb-ok cutsdb)
                  (<= (nfix n) (cut-nnodes cutsdb)))
             (cutsdb-data-ok 0 (nodecut-indicesi n cutsdb) cutsdb))
    :hints (("goal" :use ((:instance cutsdb-nodecuts-ok-implies-cutsdb-data-ok-long
                           (n 0) (m n)))
             :in-theory (disable cutsdb-nodecuts-ok-implies-cutsdb-data-ok-long))))

  ;; (local (defthm stobjs::range-nat-equiv-badguy-not-equal-n-at-upper-bound
  ;;          (implies (and (<= (nfix upper-bound) (nfix n))
  ;;                        (posp upper-bound))
  ;;                   (not (equal (stobjs::range-nat-equiv-badguy 0 upper-bound x y) (nfix n))))
  ;;          :hints (("goal" :use ((:instance stobjs::range-nat-equiv-badguy-upper-bound
  ;;                                 (start 0) (num upper-bound)))
  ;;                   :in-theory (disable stobjs::range-nat-equiv-badguy-upper-bound)))))

  (def-updater-independence-thm cutsdb-ok-updater-independence
    (implies (and (cutsdb-ok old)
                  (equal (nth *cut-nnodes1* new) (nth *cut-nnodes1* old))
                  (equal (nth *nodecut-indicesi1* new) (nth *nodecut-indicesi1* old))
                  (<= (cut-data-length old) (cut-data-length new))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-bound-when-not-equal
                  (equal max-idx (nodecut-indicesi (cut-nnodes old) old))
                  (stobjs::range-nat-equiv 0 max-idx
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (cutsdb-ok new)))

  (defthm cutsdb-ok-of-update-cut-data-past-last
    (implies (and (cutsdb-ok cutsdb)
                  (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix n))
                  ;; (< (nfix n) (cut-data-length cutsdb))
                  )
             (cutsdb-ok (update-cut-datai n v cutsdb)))
    :hints (("goal" :cases ((equal 0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))))

  (defthm cutsdb-ok-of-update-last-node
    (implies (cutsdb-ok cutsdb)
             (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)))
               (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                             (not (equal 0 (cut-nnodes cutsdb)))
                             (equal next (cut-next$ m cutsdb))
                             (cutsdb-cut-ok m cutsdb)
                             (cutsdb-cut-bounded m (cut-nnodes cutsdb) cutsdb)
                             ;; (<= size 4)
                             ;; (< (+ 2 m size) (cut-data-length cutsdb))
                             ;; (truth4-p truth)
                             ;; (truth4-deps-bounded size truth)
                             ;; (cutsdb-data-nodes-sorted data size cutsdb)
                             (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                                    (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)))
                        (cutsdb-ok (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                            next cutsdb)))))
    :hints (("goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                     (open-cutsdb-nodecuts-ok)))
            (and stable-under-simplificationp
                 '(:in-theory (enable cutsdb-cut-ok)))))
    ;; :hints (("Goal" :use cutsdb-ok-of-update-last-node
    ;;          :in-theory (disable cutsdb-ok-of-update-last-node))))
  ;; (defthm cutsdb-ok-of-update-last-node
  ;;   (implies (cutsdb-ok cutsdb)
  ;;            (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                 ;; (size (cut-datai m cutsdb))
  ;;                 ;; (truth (cut-datai (+ 1 m) cutsdb))
  ;;                 ;; (data (+ 2 m))
  ;;                 )
  ;;              (implies (and (not (equal 0 (cut-nnodes cutsdb)))
  ;;                            (cutsdb-cut-ok m cutsdb)
  ;;                            ;; (<= size 4)
  ;;                            ;; (< (cut-next m cutsdb) (cut-data-length cutsdb))
  ;;                            ;; (truth4-p truth)
  ;;                            ;; (truth4-deps-bounded size truth)
  ;;                            ;; (cutsdb-data-nodes-sorted data size cutsdb)
  ;;                            )
  ;;                       (cutsdb-ok (update-nodecut-indicesi (cut-nnodes cutsdb) (cut-next$ m cutsdb) cutsdb)))))
  ;;   :hints (("goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
  ;;                                    (open-cutsdb-nodecuts-ok)))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable cutsdb-cut-ok)))))

  (defthm cutp-of-nodecut-indicies-when-cutsdb-ok
    (implies (and (equal (nodecut-indicesi n cutsdb1)
                         (nodecut-indicesi n cutsdb))
                  (cutsdb-ok cutsdb)
                  (<= (nfix n) (cut-nnodes cutsdb)))
             (cutp (nodecut-indicesi n cutsdb1) cutsdb))))

(define cutsdb-data-nodes-lit-idsp ((idx natp)
                                     (num natp)
                                     (aignet)
                                     cutsdb)
  :guard (<= (+ idx num) (cut-data-length cutsdb))
  :measure (nfix num)
  (b* (((when (zp num)) t)
       (data (cut-datai idx cutsdb)))
    (and (id-existsp data aignet)
         (not (eql (id->type data aignet) (out-type)))
         (cutsdb-data-nodes-lit-idsp (+ 1 (lnfix idx)) (1- (lnfix num)) aignet cutsdb)))
  ///
  (def-updater-independence-thm cutsdb-data-nodes-lit-idsp-updater-independence
    (implies (stobjs::range-nat-equiv idx num (nth *cut-datai1* new) (nth *cut-datai1* old))
             (equal (cutsdb-data-nodes-lit-idsp idx num aignet new)
                    (cutsdb-data-nodes-lit-idsp idx num aignet old)))
    :hints (("goal" :induct (cutsdb-data-nodes-lit-idsp idx num aignet new)
             :expand ((:free (new) (cutsdb-data-nodes-lit-idsp idx num aignet new))
                      ;; (:free (x) (range-of-nths idx num aignet x))
                      ;; (:free (x) (range-of-nths (+ 1 (nfix idx)) (+ -1 num) x))
                      ;; (:free (x) (nthcdr idx x))
                      ;; (:free (x) (take num x))
                      ))))

  ;; (defthm cutsdb-data-nodes-lit-idsp-preserved-by-write
  ;;   (implies (<= (+ (nfix idx) (nfix num)) (nfix dest-idx))
  ;;            (equal (cutsdb-data-nodes-lit-idsp idx num aignet (update-cut-datai dest-idx val cutsdb))
  ;;                   (cutsdb-data-nodes-lit-idsp idx num aignet cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-array-acc-meta-split))))

  (defthmd cutsdb-data-nodes-lit-idsp-implies
    (implies (and (cutsdb-data-nodes-lit-idsp idx num aignet cutsdb)
                  (<= (nfix idx) (nfix n))
                  (< (nfix n) (+ (nfix idx) (nfix num))))
             (and (aignet-idp (cut-datai n cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-datai n cutsdb) aignet)))) :output))
                  (not (equal (stype (car (lookup-id (cut-datai n cutsdb) aignet))) :po))
                  (not (equal (stype (car (lookup-id (cut-datai n cutsdb) aignet))) :nxst))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

(define cutsdb-cut-lit-idsp ((n cutp$) (aignet) cutsdb)
  :guard-debug t
  :returns ok
  :prepwork ((local (in-theory (enable cut-next$-base-index-lower-bound))))
  :guard (cutsdb-cut-ok n cutsdb)
  :guard-hints (("goal" :in-theory (enable cutsdb-cut-ok)))
  ;; :guard-hints (("goal" :in-theory (enable cut-next)))
  ;; :guard (and (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
  ;;             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (cut-data-length cutsdb)))
  (b* ((n (cut-fix n))
       (size (cut-datai n cutsdb)))
    (cutsdb-data-nodes-lit-idsp (+ 2 n) size aignet cutsdb))
  ///
  (def-updater-independence-thm cutsdb-cut-lit-idsp-updater-independence
    (implies (and (cutsdb-cut-lit-idsp n aignet old)
                  ;; (equal (cut-next$ n new)
                  ;;        (cut-next$ n old))
                  ;; (<= (cut-data-length old) (cut-data-length new))
                  ;; See the comment in stobjs::range-nat-equiv-badguy-upper-aignet-when-not-equal
                  (equal next (cut-next$ n old))
                  (stobjs::range-nat-equiv 0 next (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-cut-lit-idsp n aignet new))
    :hints(("Goal" :in-theory (disable stobjs::range-nat-equiv-open)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthmd cutsdb-cut-lit-idsp-implies-nodes-lit-idsp
    (implies (and (cutsdb-cut-lit-idsp n aignet cutsdb)
                  (<= (+ 2 (cut-fix n)) (nfix i))
                  (< (nfix i) (cut-next$ n cutsdb)))
             (and (aignet-idp (cut-datai i cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-datai i cutsdb) aignet)))) :output))
                  (not (equal (stype (car (lookup-id (cut-datai i cutsdb) aignet))) :po))
                  (not (equal (stype (car (lookup-id (cut-datai i cutsdb) aignet))) :nxst))))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding
                                     cut-next$
                                     cut-next
                                     cutsdb-data-nodes-lit-idsp-implies)
                                   (rewrite-to-cut-next$)))))

  (defthm cutsdb-cut-lit-idsp-of-update-cut-data-past-next
    (implies (and (<= (cut-next$ n cutsdb) (nfix k))
                  (cutsdb-cut-lit-idsp n aignet cutsdb))
             (cutsdb-cut-lit-idsp n aignet (update-cut-datai k v cutsdb)))
    :hints(("Goal" :in-theory (disable cutsdb-cut-lit-idsp)))
    ;; :hints(("Goal" :in-theory (enable cut-next)))
    )

  (defthm cutsdb-cut-lit-idsp-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-cut-lit-idsp (cut-base-index n cutsdb1) aignet cutsdb)
                    (cutsdb-cut-lit-idsp n aignet cutsdb))))
  

  (defthm cutsdb-cut-lit-idsp-of-equal-cut-base-index
    (implies (and (equal m (cut-base-index n cutsdb))
                  (bind-free
                   (and (not (equal m n))
                        (let ((mm (case-match m
                                   (('cut-base-index mm &) mm)
                                   (('nfix mm) mm)
                                   (& m))))
                          (and (not (equal mm n))
                               `((mm . ,mm)))))
                   (mm))
                  (equal (cut-base-index mm cutsdb) m))
             (equal (cutsdb-cut-lit-idsp n aignet cutsdb)
                    (cutsdb-cut-lit-idsp mm aignet cutsdb)))))


(define cutsdb-data-lit-idsp ((n cutp$) (aignet) (cutsdb cutsdb-ok))
  :guard (<= n (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  :guard-hints (("goal" :in-theory (enable open-cutsdb-data-ok)))
  :measure (cut-measure n (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb)
  :returns ok
  (b* ((n (cut-fix n))
       (max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       ((when (mbe :logic (zp (- max n))
                   :exec (eql n max)))
        t)
       ;; (size (cut-datai n cutsdb))
        (next (cut-next$ n cutsdb)))
    (and (cutsdb-cut-lit-idsp n aignet cutsdb)
         ;; (<= next (lnfix max))
         ;; (mbt (<= next (cut-data-length cutsdb))) ;; (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
         ;; (b* ((truth (cut-datai (+ 1 (lnfix n)) cutsdb)))
         ;;   (and (truth4-p truth)
         ;;        (truth4-deps-lit-idsp size truth)
         ;;        (cutsdb-data-nodes-sorted (+ 2 (lnfix n)) size cutsdb)
         (cutsdb-data-lit-idsp next aignet cutsdb)))
  ///
  (local (in-theory (disable (:d cutsdb-data-lit-idsp))))

  (def-updater-independence-thm cutsdb-data-lit-idsp-updater-independence
    (implies (and (equal (cut-fix n new) (cut-fix n old))
                  (cutsdb-data-lit-idsp n aignet old)
                  (equal (nodecut-indicesi (cut-nnodes new) new)
                         (nodecut-indicesi (cut-nnodes old) old))
                  (cutsdb-ok old)
                  ;; (cutp n new)
                  ;; (cutp n old)
                  ;; (<= (cut-fix n old) max-fix)
                  (stobjs::range-nat-equiv 0 (nodecut-indicesi (cut-nnodes old) old)
                                       (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-data-lit-idsp n aignet new))
    :hints(("Goal" :in-theory (e/d (;; cut-next
                                    )
                                   (stobjs::range-nat-equiv-open))
            :induct (cutsdb-data-lit-idsp n aignet old)
            :expand ((:free (x) (cutsdb-data-lit-idsp n aignet x))))
           (and stable-under-simplificationp
                '(:cases ((< (nodecut-indicesi (Cut-nnodes old) old)
                             (cut-next$ n old)))))))

  (defthm cutsdb-data-lit-idsp-of-cut-base-index
    (implies (equal (cut-base-index n cutsdb1) (cut-base-index n cutsdb))
             (equal (cutsdb-data-lit-idsp (cut-base-index n cutsdb1) aignet cutsdb)
                    (cutsdb-data-lit-idsp n aignet cutsdb)))
    :hints (("goal"
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-lit-idsp n aignet cutsdb))
                      (:free (cutsdb) (cutsdb-data-lit-idsp (cut-base-index n cutsdb) aignet cutsdb))))))

  (defretd cutsdb-data-lit-idsp-implies-next
    (implies (and ok
                  (equal (cut-next$ n cutsdb1) (cut-next$ n cutsdb))
                  (< (cut-fix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (Cutsdb-ok cutsdb)
                  )
             (cutsdb-data-lit-idsp (cut-next$ n cutsdb1) aignet cutsdb))
    :hints (("Goal" 
             :do-not-induct t
             :expand ((:free (cutsdb) (cutsdb-data-lit-idsp n aignet cutsdb))))))

  (defretd open-cutsdb-data-lit-idsp
    (implies (and (acl2::rewriting-negative-literal `(cutsdb-data-lit-idsp ,n ,aignet ,cutsdb))
                  (< (cut-fix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal ok
                    (and (cutsdb-cut-lit-idsp n aignet cutsdb)
                         (cutsdb-data-lit-idsp (cut-next$ n cutsdb) aignet cutsdb))))
    :hints(("Goal" :in-theory (enable cutsdb-cut-lit-idsp)
            :expand ((cutsdb-data-lit-idsp n aignet cutsdb)))))
            ;; (and stable-under-simplificationp
            ;;      '(:use ((:instance cut-next$-of-cut-base-index
            ;;               (cut a) (cutsdb1 cutsdb))
            ;;              (:instance cut-next$-of-cut-base-index
            ;;               (cut b) (cutsdb1 cutsdb))
            ;;              (:instance cutsdb-cut-lit-idsp-of-cut-base-index
            ;;               (n a) (cutsdb1 cutsdb))
            ;;              (:instance cutsdb-cut-lit-idsp-of-cut-base-index
            ;;               (n b) (cutsdb1 cutsdb)))
            ;;        :in-theory (disable cut-next$-of-cut-base-index
            ;;                            cutsdb-cut-lit-idsp-of-cut-base-index)))

  (defthm cutsdb-data-lit-idsp-of-add-node
    (implies (and (cutsdb-data-lit-idsp n aignet cutsdb)
                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                         (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (cut-fix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
                  (cutsdb-ok cutsdb))
             (cutsdb-data-lit-idsp n aignet (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                                     (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) cutsdb)
                                                                     cutsdb)))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct (cutsdb-data-lit-idsp n aignet cutsdb)
             :expand ((:free (cutsdb) (cutsdb-data-lit-idsp n aignet cutsdb))))
            (and stable-under-simplificationp
                 '(:expand ((:free (cutsdb2) (cutsdb-data-lit-idsp (cut-next$ n cutsdb) aignet cutsdb2)))))))

  ;; (defthm cutsdb-data-lit-idsp-of-add-node
  ;;   (implies (and (cutsdb-data-lit-idsp n m aignet cutsdb)
  ;;                 (<= (nfix n) m))
  ;;            (b* (;; (size (cut-datai m cutsdb))
  ;;                 ;; (truth (cut-datai (+ 1 m) cutsdb))
  ;;                 ;; (data (+ 2 m))
  ;;                 (next (cut-next m cutsdb)))
  ;;              (implies (and (natp m)
  ;;                            (cutsdb-cut-lit-idsp m aignet cutsdb);; (natp m)
  ;;                            ;; (<= size 4)
  ;;                            ;; (<= next (cut-data-length cutsdb))
  ;;                            ;; (truth4-p truth)
  ;;                            ;; (truth4-deps-lit-idsp size truth)
  ;;                            ;; (cutsdb-data-nodes-sorted data size cutsdb)
  ;;                            )
  ;;                       (cutsdb-data-lit-idsp n next aignet cutsdb))))
  ;;   :hints (("goal" :use cutsdb-data-lit-idsp-of-add-node-nfix
  ;;            :in-theory (disable cutsdb-data-lit-idsp-of-add-node-nfix))))

  
  (defthm cutsdb-data-lit-idsp-of-update-past-last
    (implies (and (cutsdb-data-lit-idsp n aignet cutsdb)
                  (<= (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix k))
                  (cutsdb-ok cutsdb))
             (cutsdb-data-lit-idsp n aignet (update-cut-datai k v cutsdb)))
    :hints (("goal" :in-theory (disable cutsdb-data-lit-idsp))))

  (defthm cutsdb-data-lit-idsp-self
    (implies (and (cutsdb-ok cutsdb)
                  (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                         (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-data-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) aignet cutsdb))
    :hints (("goal" :expand ((:free (cutsdb1)
                              (cutsdb-data-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                                                    aignet cutsdb))))))

  (local (defthm cut-base-index-not-out-of-order
           (implies (<= (cut-base-index n cutsdb) (nfix k))
                    (<= (cut-base-index n cutsdb) (cut-base-index k cutsdb)))
           :hints (("goal" :use ((:instance cut-base-index-monotonic
                                  (target-idx (cut-base-index n cutsdb))
                                  (target-idx1 k)))
                    :in-theory (disable cut-base-index-monotonic)))))

  ;; (local (defthm cut-base-index-when-less-than-next
  ;;          (implies (and (<= (cut-base-index n cutsdb) (nfix k))
  ;;                        (< (nfix k) (cut-next$ n cutsdb)))
  ;;                   (equal (cut-base-index k cutsdb)
  ;;                          (cut-base-index n cutsdb)))
  ;;          :hints (("goal" :use ((:instance cut-base-index-monotonic
  ;;                                 (target-idx (nfix k))
  ;;                                 (target-idx1 (+ -1 (cut-next$ n cutsdb))))
  ;;                                (:instance cut-base-index-monotonic
  ;;                                 (target-idx (cut-fix n))
  ;;                                 (target-idx1 )))
  ;;                   :in-theory (disable cut-base-index-monotonic
  ;;                                       cut-base-index-not-out-of-order)))))

  ;; (local (defthm cutsdb-cut-lit-idsp-when-base-indices-equal
  ;;          (implies (equal (Cut-base-index k cutsdb)
  ;;                          (Cut-base-index n cutsdb))
  ;;                   (equal (cutsdb-cut-lit-idsp k aignet cutsdb)
  ;;                          (cutsdb-cut-lit-idsp n aignet cutsdb)))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-cut-lit-idsp)))
  ;;          :rule-classes nil))

  (defthmd cutsdb-cut-lit-idsp-when-data-lit-idsp
    (implies (and (cutsdb-data-lit-idsp n aignet cutsdb)
                  (<= (cut-base-index n cutsdb) (nfix k))
                  (< (cut-base-index k cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-cut-lit-idsp k aignet cutsdb))
    :hints (("goal" :induct (cutsdb-data-lit-idsp n aignet cutsdb)
             :expand ((:free (cutsdb) (cutsdb-data-lit-idsp n aignet cutsdb)))
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (acl2::use-termhint
             (b* (((when (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                             (cut-base-index n cutsdb)))
                   `'(:use ((:instance cut-base-index-not-out-of-order))
                      :in-theory (disable cut-base-index-not-out-of-order))))
               `'(:use ((:instance cut-base-index-of-less-than-cut-next$
                         (other-idx (nfix k))
                         (target-idx n))
                        ;; cutsdb-cut-lit-idsp-when-base-indices-equal
                        ))))))

  ;; (defthm cutsdb-data-lit-idsp-implies-max-less-than-cut-data-length
  ;;   (implies (and (cutsdb-data-lit-idsp n m aignet cutsdb)
  ;;                 (natp m)
  ;;                 (<= (nfix n) m)
  ;;                 (< (cut-base-index n cutsdb) (cut-data-length cutsdb)))
  ;;            (< m (cut-data-length cutsdb)))
  ;;   :hints (("goal" :induct (cutsdb-data-lit-idsp n m aignet cutsdb)
  ;;            :expand ((:free (cutsdb) (cutsdb-data-lit-idsp n m aignet cutsdb))))))
  
  
  )

(define cutsdb-lit-idsp (aignet (cutsdb cutsdb-ok))
  :guard (cutsdb-ok cutsdb)
  :guard-hints (("goal" :in-theory (enable cutsdb-ok)))
  (cutsdb-data-lit-idsp 0 aignet cutsdb)
  ///
  (def-updater-independence-thm cutsdb-lit-idsp-updater-independence
    (implies (and (cutsdb-lit-idsp aignet old)
                  (equal (nodecut-indicesi (cut-nnodes new) new)
                         (nodecut-indicesi (cut-nnodes old) old))
                  (cutsdb-ok old)
                  ;; (cutp n new)
                  ;; (cutp n old)
                  ;; (<= (cut-fix n old) max-fix)
                  (stobjs::range-nat-equiv 0 (nodecut-indicesi (cut-nnodes old) old)
                                       (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (cutsdb-lit-idsp aignet new)))

  (defthm cutsdb-lit-idsp-of-add-node
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                         (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
                  (cutsdb-ok cutsdb))
             (cutsdb-lit-idsp aignet (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                              (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1) cutsdb)
                                                              cutsdb))))
  
  (defthm cutsdb-lit-idsp-of-update-past-last
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix k))
                  (cutsdb-ok cutsdb))
             (cutsdb-lit-idsp aignet (update-cut-datai k v cutsdb)))
    :hints (("goal" :in-theory (disable cutsdb-lit-idsp))))


  (defthm cutsdb-cut-lit-idsp-when-cutsdb-lit-idsp
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (< (cut-base-index k cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-cut-lit-idsp k aignet cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-cut-lit-idsp-when-data-lit-idsp)))))




(define cuts-maybe-grow-nodecut-indices ((size natp) cutsdb)
  :returns (new-cutsdb)
  (if (<= (nodecut-indices-length cutsdb) (lnfix size))
      (resize-nodecut-indices (max 16 (* 2 (lnfix size))) cutsdb)
    cutsdb)
  ///

  (defthm nth-of-cuts-maybe-grow-nodecut-indices
    (implies (not (equal (nfix n) *nodecut-indicesi1*))
             (equal (nth n (cuts-maybe-grow-nodecut-indices size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-nodecut-indices-of-cuts-maybe-grow-nodecut-indices
    (nat-equiv (nth n (nth *nodecut-indicesi1* (cuts-maybe-grow-nodecut-indices size cutsdb)))
               (nth n (nth *nodecut-indicesi1* cutsdb))))

  (defthm nth-nodecut-indices-of-cuts-maybe-grow-nodecut-indices-below-size
    (implies (< (nfix n) (nodecut-indices-length cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* (cuts-maybe-grow-nodecut-indices size cutsdb)))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater cuts-maybe-grow-nodecut-indices 1)


  ;; (local (defthm cutsdb-data-nodes-sorted-of-resize-nodecut-indices
  ;;          (equal (cutsdb-data-nodes-sorted a b (resize-nodecut-indices val cutsdb))
  ;;                 (cutsdb-data-nodes-sorted a b cutsdb))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-data-nodes-sorted)))))

  ;; (local (defthm cutsdb-data-ok-of-resize-nodecut-indices
  ;;          (equal (cutsdb-data-ok n m (resize-nodecut-indices val cutsdb))
  ;;                 (cutsdb-data-ok n m cutsdb))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-data-ok)
  ;;                  :induct (cutsdb-data-ok n m cutsdb)))))

  ;; (local (defthm cutsdb-nodecuts-ok-of-resize-nodecut-indices
  ;;          (implies (and (cutsdb-nodecuts-ok n cutsdb)
  ;;                        (< (cut-nnodes cutsdb) (nodecut-indices-length cutsdb))
  ;;                        (< (cut-nnodes cutsdb) (nfix m))
  ;;                        (<= (nfix n) (cut-nnodes cutsdb)))
  ;;                   (cutsdb-nodecuts-ok n (resize-nodecut-indices m cutsdb)))
  ;;          :hints(("Goal" :in-theory (e/d* (cutsdb-nodecuts-ok
  ;;                                           nodecut-indices-length
  ;;                                           acl2::arith-equiv-forwarding)
  ;;                                          (open-cutsdb-data-ok
  ;;                                           open-cutsdb-nodecuts-ok))
  ;;                  :induct t :do-not-induct t))))

  (defret cutsdb-ok-of-cuts-maybe-grow-nodecut-indices
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok))))

  (defret nodecut-indices-length-of-cuts-maybe-grow-nodecut-indices
    (< (nfix size) (nodecut-indices-length new-cutsdb))
    :rule-classes :linear))


(define cuts-maybe-grow-cut-data ((size natp) cutsdb)
  :returns (new-cutsdb)
  (if (<= (cut-data-length cutsdb) (lnfix size))
      (resize-cut-data (max 16 (* 2 (lnfix size))) cutsdb)
    cutsdb)
  ///

  (defthm nth-of-cuts-maybe-grow-cut-data
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n (cuts-maybe-grow-cut-data size cutsdb))
                    (nth n cutsdb))))

  (defthm nth-cut-data-of-cuts-maybe-grow-cut-data
    (nat-equiv (nth n (nth *cut-datai1* (cuts-maybe-grow-cut-data size cutsdb)))
               (nth n (nth *cut-datai1* cutsdb))))

  (defthm nth-cut-data-of-cuts-maybe-grow-cut-data-below-size
    (implies (< (nfix n) (cut-data-length cutsdb))
             (equal (nth n (nth *cut-datai1* (cuts-maybe-grow-cut-data size cutsdb)))
                    (nth n (nth *cut-datai1* cutsdb)))))

  ;; (set-stobj-updater cuts-maybe-grow-cut-data 1)


  ;; (local (defthm cutsdb-data-nodes-sorted-of-resize-cut-data
  ;;          (implies (and (<= (+ (nfix a) (nfix b)) (cut-data-length cutsdb))
  ;;                        (<= (cut-data-length cutsdb) (nfix val)))
  ;;                   (equal (cutsdb-data-nodes-sorted a b (resize-cut-data val cutsdb))
  ;;                          (cutsdb-data-nodes-sorted a b cutsdb)))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-data-nodes-sorted)))))

  ;; (local (defthm cutsdb-data-ok-of-resize-cut-data
  ;;          (implies (and ;; (<= (nfix m) (cut-data-length cutsdb))
  ;;                        (<= (cut-data-length cutsdb) (nfix val))
  ;;                        (cutsdb-data-ok n m cutsdb))
  ;;                   (cutsdb-data-ok n m (resize-cut-data val cutsdb)))
  ;;          :hints(("Goal" :in-theory (enable cutsdb-data-ok
  ;;                                            cutsdb-cut-ok)
  ;;                  :induct (cutsdb-data-ok n m cutsdb)))))

  ;; (local (defthm cutsdb-nodecuts-ok-of-resize-cut-data
  ;;          (implies (and (cutsdb-nodecuts-ok n cutsdb)
  ;;                        (<= (nfix n) (cut-nnodes cutsdb))
  ;;                        (<= (cut-data-length cutsdb) (nfix m)))
  ;;                   (cutsdb-nodecuts-ok n (resize-cut-data m cutsdb)))
  ;;          :hints(("Goal" :in-theory (e/d* (cutsdb-nodecuts-ok
  ;;                                           acl2::arith-equiv-forwarding)
  ;;                                          (open-cutsdb-data-ok
  ;;                                           open-cutsdb-nodecuts-ok))
  ;;                  :induct t :do-not-induct t))))

  (defret cutsdb-ok-of-cuts-maybe-grow-cut-data
    (implies (cutsdb-ok cutsdb)
             (cutsdb-ok new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-ok))))

  (defret cut-data-length-of-cuts-maybe-grow-cut-data
    (< (nfix size) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-data-length-nondecreasing-of-cuts-maybe-grow-cut-data
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-data-length-of-cuts-maybe-grow-cut-data-rw
    (implies (natp size)
             (and (< size (cut-data-length new-cutsdb))
                  (<= size (cut-data-length new-cutsdb))))))


(define cuts-add-node-aux ((cutsdb cutsdb-ok))
  :guard (< (+ 1 (cut-nnodes cutsdb)) (nodecut-indices-length cutsdb))
  :returns (new-cutsdb)
  (b* ((old-nnodes (cut-nnodes cutsdb))
       (new-nnodes (+ 1 old-nnodes))
       (cutsdb (update-cut-nnodes new-nnodes cutsdb)))
    (update-nodecut-indicesi new-nnodes (nodecut-indicesi old-nnodes cutsdb) cutsdb))
  
  :prepwork ((local (in-theory (e/d (cutsdb-ok)
                                    (open-cutsdb-nodecuts-ok))))
             (local (defthm nodecuts-ok-lemma
                      (IMPLIES
                       (AND (CUTSDB-NODECUTS-OK n CUTSDB)
                            (cutp (nodecut-indicesi n cutsdb) cutsdb)
                            (<= (NODECUT-INDICESI (CUT-NNODES CUTSDB)
                                                  CUTSDB)
                                (CUT-DATA-LENGTH CUTSDB))
                            ;; (equal v (+ 1 (CUT-NNODES CUTSDB)))
                            )
                       (CUTSDB-NODECUTS-OK
                        n
                        (UPDATE-NODECUT-INDICESI (+ 1 (CUT-NNODES CUTSDB))
                                                 (NODECUT-INDICESI (CUT-NNODES CUTSDB)
                                                                   CUTSDB)
                                                 (UPDATE-CUT-NNODES (+ 1 (CUT-NNODES CUTSDB))
                                                                    CUTSDB))))
                      :hints(("Goal" :in-theory (e/d* (cutsdb-nodecuts-ok
                                                         acl2::arith-equiv-forwarding)
                                                      (open-cutsdb-nodecuts-ok
                                                       cutsdb-ok
                                                       ;; nodecut-indices-of-update-nodecut-indicesi
                                                       ))
                              :induct (cutsdb-nodecuts-ok n cutsdb)
                              :do-not-induct t
                              :expand ((:free (cutsdb) (cutsdb-nodecuts-ok n cutsdb))
                                       (:free (x cutsdb) (cutsdb-data-ok x x cutsdb))))))))
  ///
  (defret cutsdb-ok-of-cuts-add-node-aux
    (implies (and (cutsdb-ok cutsdb)
                  (< (+ 1 (cut-nnodes cutsdb)) (nodecut-indices-length cutsdb)))
             (cutsdb-ok new-cutsdb)))

  (defret cut-nnodes-of-cuts-add-node-aux
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defthm nth-of-cuts-add-node-aux
    (implies (and (not (equal (nfix n) *cut-nnodes1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n (cuts-add-node-aux cutsdb))
                    (nth n cutsdb))))

  (defthm nth-nodecut-indices-of-cuts-add-node-aux
    (implies (not (equal (nfix n) (+ 1 (cut-nnodes cutsdb))))
             (equal (nth n (nth *nodecut-indicesi1* (cuts-add-node-aux cutsdb)))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret nodecut-indices-length-of-cuts-add-node-aux
    (implies (< (+ 1 (cut-nnodes cutsdb)) (nodecut-indices-length cutsdb))
             (equal (nodecut-indices-length new-cutsdb)
                    (nodecut-indices-length cutsdb))))

  (defret last-node-index-of-cuts-add-node-aux
    (implies (equal (nfix new-node) (+ 1 (cut-nnodes cutsdb)))
             (equal (nodecut-indicesi new-node new-cutsdb)
                    (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))

  ;; (set-stobj-updater cuts-add-node-aux 0)
  )

(define cuts-add-node ((cutsdb cutsdb-ok))
  :returns (new-cutsdb cutsdb-ok :hyp (cutsdb-ok cutsdb))
  (b* ((new-nnodes (+ 1 (cut-nnodes cutsdb)))
       (cutsdb (cuts-maybe-grow-nodecut-indices new-nnodes cutsdb)))
    (cuts-add-node-aux cutsdb))
  ///

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
                    (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))

  ;; (set-stobj-updater cuts-add-node 0)
  )









(defstobj-clone cutsdb2 cutsdb :suffix "2")
       

(define node-merge-cuts-count ((idx0 natp) (size0 natp)
                               (idx1 natp) (size1 natp)
                               cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-data-length cutsdb))
              (<= (+ idx1 size1) (cut-data-length cutsdb)))
  :measure (+ (lnfix size1) (lnfix size0))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((when (zp size0)) (lnfix size1))
       ((when (zp size1)) (lnfix size0))
       (node0 (cut-datai idx0 cutsdb))
       (node1 (cut-datai idx1 cutsdb))
       ((when (eql node0 node1))
        (+ 1 (node-merge-cuts-count (1+ (lnfix idx0)) (1- size0)
                                    (1+ (lnfix idx1)) (1- size1)
                                    cutsdb)))
       ((when (< node0 node1))
        (+ 1 (node-merge-cuts-count (1+ (lnfix idx0)) (1- size0)
                                    idx1 size1
                                    cutsdb))))
    (+ 1 (node-merge-cuts-count idx0 size0
                                (1+ (lnfix idx1)) (1- size1)
                                cutsdb)))
  ///
  (def-updater-independence-thm node-merge-cuts-count-updater-independence
    (implies (and (stobjs::range-nat-equiv idx0 size0 (nth *cut-datai1* new) (nth *cut-datai1* old))
                  (stobjs::range-nat-equiv idx1 size1 (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (equal (node-merge-cuts-count idx0 size0 idx1 size1 new)
                    (node-merge-cuts-count idx0 size0 idx1 size1 old))))

  ;; (defthm node-merge-cuts-count-normalize-cutsdb
  ;;   (implies (and (equal cut-data (nth *cut-datai1* cutsdb))
  ;;                 (bind-free (case-match cut-data
  ;;                              (('nth ''0 x)
  ;;                               (and (not (equal x cutsdb))
  ;;                                    `((new-cutsdb . ,x))))
  ;;                              (& nil))
  ;;                            (new-cutsdb))
  ;;                 (equal cut-data
  ;;                        (nth *cut-datai1* new-cutsdb)))
  ;;            (equal (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)
  ;;                   (node-merge-cuts-count idx0 size0 idx1 size1 new-cutsdb)))
  ;;   :hints (("goal" :induct t)
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable cut-datai cut-datai1)))))

  ;; (defthm node-merge-cuts-count-update-out-of-range
  ;;   (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
  ;;                 (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
  ;;            (equal (node-merge-cuts-count idx0 size0 idx1 size1 (update-cut-datai dest-idx val cutsdb))
  ;;                   (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))
  ;;   :hints(("Goal" :in-theory (enable cutsdb-array-acc-meta-split))))
  )

(defthm nth-in-u32-listp-nfix-u32p
  (implies (and (acl2::u32-listp gates)
                (< (nfix idx) (len gates)))
           (unsigned-byte-p 32 (nfix (nth idx gates))))
  :hints(("Goal" :in-theory (enable nth))))


(defthm unsigned-byte-p-of-cut-datai
  (implies (and (cutsdbp cutsdb)
                (< (nfix n) (cut-data-length cutsdb)))
           (unsigned-byte-p 32 (cut-datai n cutsdb)))
  :hints(("Goal" :in-theory (enable cut-datai cut-datai1 cutsdbp cut-data-length))))

(defthm unsigned-byte-p-of-nodecut-indicesi
  (implies (and (cutsdbp cutsdb)
                (< (nfix n) (nodecut-indices-length cutsdb)))
           (unsigned-byte-p 32 (nodecut-indicesi n cutsdb)))
  :hints(("Goal" :in-theory (enable nodecut-indicesi nodecut-indicesi1 cutsdbp nodecut-indices-length))))


(define node-merge-cuts-write1 ((src-idx natp) (size natp)
                                (dest-idx natp)
                                cutsdb)
  :guard (and (<= (+ src-idx size) (cut-data-length cutsdb))
              (<= (+ dest-idx size) (cut-data-length cutsdb)))
  :returns (new-cutsdb)
  (b* (((when (zp size)) cutsdb)
       (cutsdb (update-cut-datai dest-idx (cut-datai src-idx cutsdb) cutsdb)))
    (node-merge-cuts-write1 (1+ (lnfix src-idx)) (1- size) (1+ (lnfix dest-idx)) cutsdb))
  ///
  (defret nth-of-node-merge-cuts-write1
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-cuts-write1
    (implies (not (and (<= (nfix dest-idx) (nfix n))
                       (< (nfix n) (+ (nfix dest-idx) (nfix size)))))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb)))))

  ;; (set-stobj-updater node-merge-cuts-write1 3)

  (local (defthm x-x+y
           (equal (+ x (- x) y)
                  (fix y))))

  (defret cut-datai-of-node-merge-cuts-write1
    (implies (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx))
             (equal (cut-datai n new-cutsdb)
                    (if (or (< (nfix n) (nfix dest-idx))
                            (<= (+ (nfix dest-idx) (nfix size)) (nfix n)))
                        (cut-datai n cutsdb)
                      (cut-datai (+ (nfix src-idx) (- (nfix n) (nfix dest-idx))) cutsdb)))))

  (local (Defthm pos-fix-when-zp
           (implies (zp x) (equal (acl2::pos-fix x) 1))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (defret cutsdb-data-nodes-sorted-of-node-merge-cuts-write1
    (implies (and (cutsdb-data-nodes-sorted src-idx size cutsdb)
                  (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx)))
             (cutsdb-data-nodes-sorted dest-idx size new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-data-nodes-sorted
                                      node-merge-cuts-count)
            :induct <call>
            :expand ((:free (cutsdb) (cutsdb-data-nodes-sorted dest-idx size cutsdb))))))

  (defret cut-data-length-of-node-merge-cuts-write1
    (implies (<= (+ (nfix dest-idx) (nfix size)) (cut-data-length cutsdb))
             (equal (cut-data-length new-cutsdb) (cut-data-length cutsdb))))

  (defret cutsdb-ok-of-node-merge-cuts-write1
    (implies (and (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix dest-idx))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))

  (defret cut-data-length-nondecreasing-of-node-merge-cuts-write1
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defretd cut-data-length-lower-bound-of-node-merge-cuts-write1
    (implies (posp size)
             (<= (+ (nfix dest-idx) size) (cut-data-length new-cutsdb)))
    :rule-classes :linear)

  (defret cutsdb-data-nodes-bounded-of-node-merge-cuts-write1
    (implies (and (cutsdb-data-nodes-bounded src-idx size bound cutsdb)
                  (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx)))
             (cutsdb-data-nodes-bounded dest-idx size bound new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-data-nodes-bounded)
            :induct <call>)))

  (defret cutsdb-data-nodes-lit-idsp-of-node-merge-cuts-write1
    (implies (and (cutsdb-data-nodes-lit-idsp src-idx size aignet cutsdb)
                  (<= (+ (nfix src-idx) (nfix size)) (nfix dest-idx)))
             (cutsdb-data-nodes-lit-idsp dest-idx size aignet new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-data-nodes-lit-idsp)
            :induct <call>))))

(define node-merge-cuts-write ((idx0 natp) (size0 natp)
                               (idx1 natp) (size1 natp)
                               (dest-idx natp)
                               cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-data-length cutsdb))
              (<= (+ idx1 size1) (cut-data-length cutsdb))
              (<= (+ idx0 size0) dest-idx)
              (<= (+ idx1 size1) dest-idx)
              (<= (+ dest-idx (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))
                  (cut-data-length cutsdb)))
  :guard-hints (("goal" ;; :in-theory (enable cut-data-of-update-cut-datai)
                 :expand ((node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))))
  :returns (new-cutsdb)
  :measure (+ (lnfix size1) (lnfix size0))
  (b* (((when (zp size0)) (node-merge-cuts-write1 idx1 size1 dest-idx cutsdb))
       ((when (zp size1)) (node-merge-cuts-write1 idx0 size0 dest-idx cutsdb))
       (node0 (cut-datai idx0 cutsdb))
       (node1 (cut-datai idx1 cutsdb))
       ((when (eql node0 node1))
        (b* ((cutsdb (update-cut-datai dest-idx node0 cutsdb)))
          (node-merge-cuts-write (1+ (lnfix idx0)) (1- size0)
                                 (1+ (lnfix idx1)) (1- size1)
                                 (1+ (lnfix dest-idx))
                                 cutsdb)))
       ((when (< node0 node1))
        (b* ((cutsdb (update-cut-datai dest-idx node0 cutsdb)))
          (node-merge-cuts-write (1+ (lnfix idx0)) (1- size0)
                                 idx1 size1
                                 (1+ (lnfix dest-idx))
                                 cutsdb)))
       (cutsdb (update-cut-datai dest-idx node1 cutsdb)))
    (node-merge-cuts-write idx0 size0
                           (1+ (lnfix idx1)) (1- size1)
                           (1+ (lnfix dest-idx))
                           cutsdb))
  ///
  ;; (local (in-theory (enable cut-data-of-update-cut-datai)))

  (local (in-theory (disable cutp-updater-independence)))

  (defret nth-of-node-merge-cuts-write
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defretd nth-cut-data-of-node-merge-cuts-write
    (implies (and (not (and (<= (nfix dest-idx) (nfix n))
                            (< (nfix n) (+ (nfix dest-idx)
                                           (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))))
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb))))
    :hints(("Goal" :in-theory (enable node-merge-cuts-count))))

  (defret nth-cut-data-of-node-merge-cuts-write-weaker
    (implies (< (nfix n) (nfix dest-idx))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb))))
    :hints(("Goal" :in-theory (enable node-merge-cuts-count))))

  ;; (set-stobj-updater node-merge-cuts-write 5)

  (local (Defthm pos-fix-when-zp
           (implies (zp x) (equal (acl2::pos-fix x) 1))
           :hints(("Goal" :in-theory (enable acl2::pos-fix)))))

  (local (defthm cut-datai-of-update-cut-datai-split
           (equal (cut-datai n (update-cut-datai m v cutsdb))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-datai n cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (defretd first-element-of-node-merge-cuts-write
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (cut-datai dest-idx new-cutsdb)
                    (if (zp size1)
                        (if (zp size0)
                            (cut-datai dest-idx cutsdb)
                          (cut-datai idx0 cutsdb))
                      (if (zp size0)
                          (cut-datai idx1 cutsdb)
                        (min (cut-datai idx0 cutsdb)
                             (cut-datai idx1 cutsdb))))))
    :hints (("Goal" ;; :induct <call>
             :do-not-induct t
             :expand ((:free (size0 size1) <call>)
                      (:free (size0) (node-merge-cuts-write1 idx0 size0 dest-idx cutsdb))
                      (:free (size1) (node-merge-cuts-write1 idx1 size1 dest-idx cutsdb))))))

  (local (in-theory (enable first-element-of-node-merge-cuts-write)))

  (local (in-theory (disable stobjs::range-nat-equiv-open
                             stobjs::range-nat-equiv-of-update-out-of-range-2
                             acl2::nfix-when-not-natp)))

  ;; (defret first-element-of-node-merge-cuts-write
  ;;   (implies (posp size1)
  ;;            (<= (cut-datai dest-idx new-cutsdb)
  ;;                (cut-datai idx1 cutsdb)))
  ;;   :hints (("Goal" :induct <call>
  ;;            :expand ((:free (size0 size1) <call>)
  ;;                     (node-merge-cuts-write1 idx1 size1 dest-idx cutsdb))))
  ;;   :rule-classes :linear)

  (defret cutsdb-data-nodes-sorted-of-node-merge-cuts-write
    (implies (and (cutsdb-data-nodes-sorted idx0 size0 cutsdb)
                  (cutsdb-data-nodes-sorted idx1 size1 cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (cutsdb-data-nodes-sorted dest-idx (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)
                                       new-cutsdb))
    :hints(("Goal" :in-theory (enable node-merge-cuts-count)
            :induct <call>
            :expand ((:free (size cutsdb) (cutsdb-data-nodes-sorted dest-idx size cutsdb))
                     (:free (size1 size0) <call>)))
           (acl2::use-termhint
            (b* ((node0 (cut-datai idx0 cutsdb))
                 (node1 (cut-datai idx1 cutsdb))
                 ((when (eql node0 node1))
                  ''(:expand ((:free (size cutsdb) (cutsdb-data-nodes-sorted idx0 size cutsdb))
                              (:free (size cutsdb) (cutsdb-data-nodes-sorted idx1 size cutsdb)))))
                 ((when (< node0 node1))
                  ''(:expand ((:free (size cutsdb) (cutsdb-data-nodes-sorted idx0 size cutsdb))))))
              ''(:expand ((:free (size cutsdb) (cutsdb-data-nodes-sorted idx1 size cutsdb))))))))

  

  (defret cut-data-length-of-node-merge-cuts-write
    (implies (and (<= (+ (nfix dest-idx)
                         (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))
                      (cut-data-length cutsdb))
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (equal (cut-data-length new-cutsdb) (cut-data-length cutsdb)))
    :hints(("Goal" :in-theory (enable node-merge-cuts-count)
            :induct <call>
            :expand (<call>))))

  (defret cutsdb-ok-of-node-merge-cuts-write
    (implies (and (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix dest-idx))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))

  (defret cut-data-length-nondecreasing-of-node-merge-cuts-write
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (local (defthm node-merge-cuts-count-is-zero
           (equal (equal 0 (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))
                  (and (zp size0) (zp size1)))
           :hints(("Goal" :in-theory (enable node-merge-cuts-count)))))

  (defretd cut-data-length-lower-bound-of-node-merge-cuts-write
    (b* ((size (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))
      (implies (and (posp size)
                    (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                    (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
               (<= (+ (nfix dest-idx) size) (cut-data-length new-cutsdb))))
    :hints(("Goal" :in-theory (enable cut-data-length-lower-bound-of-node-merge-cuts-write1
                                      node-merge-cuts-count)
            :induct <call>
            :expand (<call>)))
    :rule-classes :linear)

  (defret cutsdb-data-nodes-bounded-of-node-merge-cuts-write
    (implies (and (cutsdb-data-nodes-bounded idx0 size0 bound cutsdb)
                  (cutsdb-data-nodes-bounded idx1 size1 bound cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (cutsdb-data-nodes-bounded dest-idx
                                        (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)
                                        bound
                                        new-cutsdb))
    :hints(("Goal" :in-theory (enable cutsdb-data-nodes-bounded)
            :induct <call>
            :expand (<call>
                     (:free (size0 size1) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))))))

  (defret cutsdb-data-nodes-lit-idsp-of-node-merge-cuts-write
    (implies (and (cutsdb-data-nodes-lit-idsp idx0 size0 aignet cutsdb)
                  (cutsdb-data-nodes-lit-idsp idx1 size1 aignet cutsdb)
                  (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
             (cutsdb-data-nodes-lit-idsp dest-idx
                                        (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)
                                        aignet
                                        new-cutsdb))
    :hints(("Goal" :in-theory (e/d (cutsdb-data-nodes-lit-idsp)
                                   (lookup-id-implies-aignet-idp
                                    lookup-id-in-bounds-when-positive))
            :induct <call>
            :expand (<call>
                     (:free (size0 size1) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))))))


(define node-cut-contained ((subidx natp) (subsize natp)
                            (idx natp) (size natp)
                            cutsdb)
  :guard (and (<= (+ subidx subsize) (cut-data-length cutsdb))
              (<= (+ idx size) (cut-data-length cutsdb)))
  ;; Checks whether the cut at subidx (of size subsize) is contained in the one at index idx (of size size)
  :measure (nfix size)
  (b* (((when (zp subsize)) t)
       ((when (zp size)) nil)
       (subdata (cut-datai subidx cutsdb))
       (data (cut-datai idx cutsdb))
       ((when (< subdata data)) nil)
       ((when (eql subdata data))
        (node-cut-contained (1+ (lnfix subidx)) (1- subsize)
                            (1+ (lnfix idx)) (1- size)
                            cutsdb)))
    (node-cut-contained subidx subsize
                        (1+ (lnfix idx)) (1- size)
                        cutsdb))
  ///
  (def-updater-independence-thm node-cut-contained-updater-independence
    (implies (and (stobjs::range-nat-equiv subidx subsize (nth *cut-datai1* new) (nth *cut-datai1* old))
                  (stobjs::range-nat-equiv idx size (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (equal (node-cut-contained subidx subsize idx size new)
                    (node-cut-contained subidx subsize idx size old))))

  (defthm node-cut-contained-of-node-merge-cuts-write1
    (implies (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
             (b* ((cutsdb (node-merge-cuts-write1 idx1 size1 dest-idx cutsdb)))
               (node-cut-contained idx1 size1 dest-idx size1 cutsdb)))
    :hints(("Goal" :in-theory (enable node-merge-cuts-write1)
            :induct (node-merge-cuts-write1 idx1 size1 dest-idx cutsdb))))

  (fty::deffixequiv node-cut-contained)

  (local (in-theory (enable first-element-of-node-merge-cuts-write)))

  (local (defthm cut-datai-of-update-cut-datai-split
           (equal (cut-datai n (update-cut-datai m v cutsdb))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-datai n cutsdb)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (local
   (defthm node-cut-contained-of-node-merge-cuts-write-first-lemma
     (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                   (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
              (b* ((size (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))
                   (cutsdb (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)))
                (node-cut-contained idx0 size0 dest-idx size cutsdb)))
     :hints(("Goal" :in-theory (enable node-merge-cuts-write
                                       node-merge-cuts-count
                                       ;; cut-data-of-update-cut-datai
                                       )
             :induct (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)
             :expand ((node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)
                      (:free (cutsdb) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))))))

  (defthm node-cut-contained-of-node-merge-cuts-write-first
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
                  (equal (nfix size) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))
             (b* ((cutsdb (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)))
               (node-cut-contained idx0 size0 dest-idx size cutsdb)))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                    (node-cut-contained
                                     node-cut-contained-of-node-merge-cuts-write-first-lemma))
            :use node-cut-contained-of-node-merge-cuts-write-first-lemma)))

  (local
   (defthm node-cut-contained-of-node-merge-cuts-write-second-lemma
     (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                   (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx)))
              (b* ((size (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb))
                   (cutsdb (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)))
                (node-cut-contained idx1 size1 dest-idx size cutsdb)))
     :hints(("Goal" :in-theory (enable node-merge-cuts-write
                                       node-merge-cuts-count
                                       ;; cut-data-of-update-cut-datai
                                       )
             :induct (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)
             :expand ((node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)
                      (:free (cutsdb) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))))))

  (defthm node-cut-contained-of-node-merge-cuts-write-second
    (implies (and (<= (+ (nfix idx0) (nfix size0)) (nfix dest-idx))
                  (<= (+ (nfix idx1) (nfix size1)) (nfix dest-idx))
                  (equal (nfix size) (node-merge-cuts-count idx0 size0 idx1 size1 cutsdb)))
             (b* ((cutsdb (node-merge-cuts-write idx0 size0 idx1 size1 dest-idx cutsdb)))
               (node-cut-contained idx1 size1 dest-idx size cutsdb)))
    :hints(("Goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                    (node-cut-contained
                                     node-cut-contained-of-node-merge-cuts-write-second-lemma))
            :use node-cut-contained-of-node-merge-cuts-write-second-lemma))))
  


(define node-cut-expandmask ((idx0 natp) (size0 natp)
                             (dest-idx natp) (dest-size natp)
                             (bit-idx natp)
                             cutsdb)
  :guard (and (<= (+ idx0 size0) (cut-data-length cutsdb))
              (<= (+ dest-idx dest-size) (cut-data-length cutsdb))
              (node-cut-contained idx0 size0 dest-idx dest-size cutsdb))
  :verify-guards nil
  :measure (nfix dest-size)
  :returns (bitmask natp :rule-classes :type-prescription)
  (b* (((when (zp size0)) 0)
       ((unless (mbt (not (zp dest-size)))) 0)
       (data0 (cut-datai idx0 cutsdb))
       (destdata (cut-datai dest-idx cutsdb))
       ((when (eql data0 destdata))
        (install-bit bit-idx 1
                           (node-cut-expandmask (+ 1 (lnfix idx0)) (1- size0)
                                                (+ 1 (lnfix dest-idx)) (1- dest-size)
                                                (+ 1 (lnfix bit-idx))
                                                cutsdb))))
    (node-cut-expandmask idx0 size0
                         (+ 1 (lnfix dest-idx)) (1- dest-size)
                         (+ 1 (lnfix bit-idx))
                         cutsdb))
  ///
  (def-updater-independence-thm node-cut-expandmask-updater-independence
    (implies (and (stobjs::range-nat-equiv idx0 size0 (nth *cut-datai1* new) (nth *cut-datai1* old))
                  (stobjs::range-nat-equiv dest-idx dest-size (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (equal (node-cut-expandmask idx0 size0 dest-idx dest-size bit-idx new)
                    (node-cut-expandmask idx0 size0 dest-idx dest-size bit-idx old))))

  (Verify-guards node-cut-expandmask
                 :hints (("goal" :in-theory (enable node-cut-contained))))

  (defret size-of-node-cut-expandmask
    (implies (and (natp n)
                  (<= (+ (nfix bit-idx) (nfix dest-size)) n))
             (unsigned-byte-p n bitmask)))





  (local (defret logbitp-early-of-node-cut-expandmask
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


  (defret logcount-of-node-cut-expandmask
    (implies (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
             (equal (logcount bitmask)
                    (nfix size0)))
    :hints(("Goal" :in-theory (enable node-cut-contained)
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

  (defret loghead-of-node-cut-expandmask
    (implies (<= (nfix m) (nfix bit-idx))
             (equal (loghead m bitmask) 0))
    :hints (("goal" :induct <call>)))

  ;; (local
  ;;  (defret lookup-index-permute-stretch-of-node-cut-expandmask-lemma
  ;;    (implies (and (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
  ;;                  (<= (nfix size0) (- 4 (nfix bit-idx)))
  ;;                  (<= (nfix idx0) (nfix idx))
  ;;                  (< (nfix idx) (+ (nfix idx0) (nfix size0))))
  ;;             (equal (cut-datai (+ (nfix dest-idx)
  ;;                                  (truth::index-permute-stretch bit-idx nil bitmask
  ;;                                                                (- (nfix idx) (nfix idx0))
  ;;                                                                4)) cutsdb)
  ;;                    (cut-datai idx cutsdb)))
  ;;    :hints(("Goal" :in-theory (enable* node-cut-contained
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
     (implies (and (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
                   (<= (nfix idx0) (nfix idx))
                   (< (nfix idx) (+ (nfix idx0) (nfix size0))))
              (equal (cut-datai (+ (nfix dest-idx)
                                   (nth-set-bit-pos (- (nfix idx) (nfix idx0))
                                                           (logtail bit-idx bitmask))) cutsdb)
                     (cut-datai idx cutsdb)))
     :hints(("Goal" :in-theory (enable* node-cut-contained
                                        acl2::arith-equiv-forwarding)
             :induct <call>
             ;; :expand ((:free (x) (logtail bit-idx x)))
             )
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix idx) (nfix idx0))))))
     :rule-classes nil))

  (defret lookup-nth-set-bit-pos-of-node-cut-expandmask
    (implies (and (equal bit-idx 0)
                  (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
                  (< (nfix n) (nfix size0)))
              (equal (cut-datai (+ (nfix dest-idx)
                                   (nth-set-bit-pos n bitmask)) cutsdb)
                     (cut-datai (+ (nfix idx0) (nfix n)) cutsdb)))
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
                    

  (defret nth-set-bit-pos-bound-of-node-cut-expandmask
    (implies (and (< (nfix n) (nfix size0))
                  (node-cut-contained idx0 size0 dest-idx dest-size cutsdb))
             (< (nth-set-bit-pos n bitmask) (+ (nfix bit-idx) (nfix dest-size))))
    :hints (("goal" :use ((:instance nth-set-bit-pos-bound-when-unsigned-byte-p
                           (k n) (x bitmask) (n (+ (nfix bit-idx) (nfix dest-size)))))
             :in-theory (disable nth-set-bit-pos-bound-when-unsigned-byte-p)
             :do-not-induct t))
    :rule-classes :linear)


  (local (defret logcount-of-loghead-expandmask-lemma
           (implies (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
                    (equal (logcount (loghead (+ (nfix bit-idx) (nfix dest-size) (nfix n)) bitmask))
                           (nfix size0)))
           :hints(("Goal" :in-theory (enable node-cut-contained
                                             bitops::loghead**)
                   :induct <call>))
           :rule-classes nil))

  (defret logcount-of-loghead-expandmask
    (implies (and (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
                  (equal bit-idx 0)
                  (<= (nfix dest-size) (nfix n)))
             (equal (logcount (loghead n bitmask))
                    (nfix size0)))
    :hints (("goal" :use ((:instance logcount-of-loghead-expandmask-lemma
                           (n (- (nfix n) (nfix dest-size)))))
             :in-theory (disable logcount-of-node-cut-expandmask
                                 acl2::loghead-identity)
             :do-not-induct t)))
  )
           

(define node-cut-truthenv ((idx natp) (size natp) (bit-idx natp) cutsdb bitarr)
  :verify-guards nil
  :returns (env natp :rule-classes :type-prescription)
  (b* (((when (zp size)) 0)
       (rest (node-cut-truthenv (+ 1 (lnfix idx)) (1- size) (1+ (lnfix bit-idx)) cutsdb bitarr))
       (node (cut-datai idx cutsdb)))
    (install-bit bit-idx (get-bit node bitarr) rest))
  ///
  (def-updater-independence-thm node-cut-truthenv-updater-independence
    (implies (stobjs::range-nat-equiv idx size (nth *cut-datai1* new) (nth *cut-datai1* old))
             (equal (node-cut-truthenv idx size bit-idx new bitarr)
                    (node-cut-truthenv idx size bit-idx old bitarr))))

  (defthm lookup-in-node-cut-truthenv
    (equal (truth::env-lookup k (node-cut-truthenv idx size bit-idx cutsdb bitarr))
           (and (<= (nfix bit-idx) (nfix k))
                (< (nfix k) (+ (nfix bit-idx) (nfix size)))
                (acl2::bit->bool (get-bit (cut-datai (+ (nfix idx) (- (nfix k) (nfix bit-idx))) cutsdb) bitarr))))
    :hints(("Goal" :in-theory (enable truth::env-lookup
                                      bitops::logbitp-of-install-bit-split)))))






;; (define cuts-add-cut ((cutsdb cutsdb-ok))
;;   :returns (new-cutsdb)
;;   :guard (b* ((
;;   ;; Adds a cut that has already been written in the empty space beyond the last nodecut index.
;;   (b* ((last-index (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;        (new-cut-size (cut-datai last-index cutsdb))
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

(define update-cut-datai$ ((n natp) (v natp) (cutsdb))
  :guard (< n (cut-data-length cutsdb))
  :enabled t
  :inline t
  :hooks nil
  (mbe :logic (update-cut-datai n v cutsdb)
       :exec (if (unsigned-byte-p 32 v)
                 (update-cut-datai n v cutsdb)
               (ec-call (update-cut-datai n v cutsdb)))))

(define cuts-check-any-contained ((start cutp$)
                                  (end cutp$)
                                  (data natp)
                                  (size natp)
                                  (cutsdb cutsdb-ok))
  :guard (and (<= (+ data size) (cut-data-length cutsdb))
              (<= start end)
              (<= end (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  :returns (cut-is-redundant)
  :measure (cut-measure start (cut-fix end) cutsdb)
  (b* ((start (cut-fix start))
       (end (cut-fix end))
       ((when (mbe :logic (zp (- end start))
                   :exec (eql start end)))
        nil)
       (cut-size (cut-datai start cutsdb))
       (cut-data (+ 2 start))
       (contained (node-cut-contained cut-data cut-size data size cutsdb)))
    (or contained
        (cuts-check-any-contained (cut-next$ start cutsdb) end data size cutsdb))))
       
  

(define node-merge-cuts-aux ((cut0 cutp$)
                             (neg0 bitp)
                             (cut1 cutp$)
                             (neg1 bitp)
                             (node-cuts-start cutp$)
                             (cutsdb cutsdb-ok))
  :guard (and (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cut-data-length cutsdb))
              )
  :verify-guards nil
  :returns (mv (updatedp)
               (new-cutsdb))
  (b* ((cut0 (cut-fix cut0))
       (data0 (+ 2 cut0))
       (size0 (cut-datai cut0 cutsdb))
       (cut1 (cut-fix cut1))
       (data1 (+ 2 cut1))
       (size1 (cut-datai cut1 cutsdb))
       (dest-cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       (dest-data (+ 2 dest-cut))
       (dest-size (node-merge-cuts-count data0 size0 data1 size1 cutsdb))
       ((when (< 4 dest-size))
        (mv nil cutsdb))
       (cutsdb (node-merge-cuts-write data0 size0 data1 size1 dest-data cutsdb))
       ((when (cuts-check-any-contained node-cuts-start dest-cut dest-data dest-size cutsdb))
        (mv nil cutsdb))
       (expmask0 (node-cut-expandmask data0 size0 dest-data dest-size 0 cutsdb))
       (expmask1 (node-cut-expandmask data1 size1 dest-data dest-size 0 cutsdb))
       (truth0 (truth::truth-norm4 (logxor (- (bfix neg0)) (cut-datai (+ 1 cut0) cutsdb))))
       (truth1 (truth::truth-norm4 (logxor (- (bfix neg1)) (cut-datai (+ 1 cut1) cutsdb))))
       (exptruth0 (truth::permute-stretch4 0 0 expmask0 truth0))
       (exptruth1 (truth::permute-stretch4 0 0 expmask1 truth1))
       (dest-truth (logand exptruth0 exptruth1))
       (cutsdb (update-cut-datai dest-cut dest-size cutsdb))
       (cutsdb (update-cut-datai (+ 1 dest-cut) dest-truth cutsdb)))
    (mv t cutsdb))
  ///

  (local (defthm cutsdb-cut-base-index-implies-cut-data-long-enough
           (implies (and (cutsdb-ok cutsdb)
                         (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (< ;; (+ 2 base (cut-datai base cutsdb))
                     (cut-next$ cut cutsdb) (cut-data-length cutsdb)))
           :rule-classes (:rewrite :linear)))

  (local (defthm cutsdb-cut-base-index-implies-next-cut-index-greater
           (implies (and (cutsdb-ok cutsdb)
                         (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (<= ;; (+ 2 base (cut-datai base cutsdb))
                     (cut-next$ cut cutsdb)
                     (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
           :hints (("goal" :use ((:instance cut-base-index-of-less-than-next-cut
                                  (other-idx (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                                  (target-idx cut)))))
           :rule-classes (:rewrite :linear)))

  (local (defthm cutsdb-cut-base-index-implies-next-cut-index-greater-special
           (implies (and (cutsdb-ok cutsdb)
                         (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (<= ;; (+ 2 base (cut-datai base cutsdb))
                     (cut-next$ cut cutsdb)
                     (+ 2 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))
           :hints (("goal" :use cutsdb-cut-base-index-implies-next-cut-index-greater
                    :in-theory (disable cutsdb-cut-base-index-implies-next-cut-index-greater
                                        CUTP-OF-NODECUT-INDICIES-WHEN-CUTSDB-OK)))
           :rule-classes (:rewrite :linear)))

  ;; (local (defthm cutsdb-cut-base-index-implies-next-cut-index-greater2
  ;;          (implies (and (cutsdb-ok cutsdb)
  ;;                        (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  ;;                   (<= ;; (+ 2 (cut-base-index cut cutsdb) (cut-datai (cut-base-index cut cutsdb) cutsdb))
  ;;                    (cut-next (cut-base-index cut cutsdb) cutsdb)
  ;;                       (+ 2 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))
  ;;          :hints (("goal" :use ((:instance cutsdb-cut-base-index-implies-next-cut-index-greater
  ;;                                 (cut (cut-base-index cut cutsdb))))
  ;;                   :in-theory (disable cutsdb-cut-base-index-implies-next-cut-index-greater)))
  ;;          :rule-classes (:rewrite :linear)))

  (local (defthm cutsdb-cut-base-index-implies-next-cut-index-range-of-nths
           (implies (and (cutsdb-ok cutsdb)
                         (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (< (stobjs::range-nat-equiv-badguy
                        (+ 2 (cut-base-index cut cutsdb))
                        (cut-datai (cut-base-index cut cutsdb) cutsdb)
                        x y)
                       (+ 2 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))
           :hints (("goal" :use ((:instance cutsdb-cut-base-index-implies-next-cut-index-greater
                                  ;; (base (cut-base-index cut cutsdb))
                                  (cut (cut-base-index cut cutsdb))))
                    :in-theory (disable cutsdb-cut-base-index-implies-next-cut-index-greater)
                    :cases ((equal 0 (cut-datai (cut-base-index cut cutsdb) cutsdb)))
                    :expand ((:free (start x y) (stobjs::range-nat-equiv-badguy start 0 x y)))))
           :rule-classes (:rewrite :linear)))

  (local (defthm cutsdb-cut-base-index-implies-next-cut-index-range-nat-equiv-badguy-not-size
           (implies (and (cutsdb-ok cutsdb)
                         (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                         (not (stobjs::range-nat-equiv
                               (+ 2 (cut-base-index cut cutsdb))
                               (cut-datai (cut-base-index cut cutsdb) cutsdb)
                               x y)))
                    (not (equal (stobjs::range-nat-equiv-badguy
                                 (+ 2 (cut-base-index cut cutsdb))
                                 (cut-datai (cut-base-index cut cutsdb) cutsdb)
                                 x y)
                                (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))
           :hints (("goal" :use ((:instance cutsdb-cut-base-index-implies-next-cut-index-greater
                                  ;; (base (cut-base-index cut cutsdb))
                                  (cut (cut-base-index cut cutsdb))))
                    :in-theory (disable cutsdb-cut-base-index-implies-next-cut-index-greater)
                    :cases ((equal 0 (cut-datai (cut-base-index cut cutsdb) cutsdb)))
                    :expand ((:free (start x y) (stobjs::range-nat-equiv start 0 x y)))))))

  (local (defthm cutsdb-cut-base-index-implies-next-cut-index-range-nat-equiv-badguy-not-truth
           (implies (and (cutsdb-ok cutsdb)
                         (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (not (equal (stobjs::range-nat-equiv-badguy
                                 (+ 2 (cut-base-index cut cutsdb))
                                 (cut-datai (cut-base-index cut cutsdb) cutsdb)
                                 x y)
                                (+ 1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))))
           :hints (("goal" :use ((:instance cutsdb-cut-base-index-implies-next-cut-index-greater
                                  ;; (base (cut-base-index cut cutsdb))
                                  (cut (cut-base-index cut cutsdb))))
                    :in-theory (e/d (cut-next$-base-index-lower-bound)
                                    (cutsdb-cut-base-index-implies-next-cut-index-greater
                                     CUTP-OF-NODECUT-INDICIES-WHEN-CUTSDB-OK))
                    :cases ((equal 0 (cut-datai (cut-base-index cut cutsdb) cutsdb)))
                    :expand ((:free (start x y) (stobjs::range-nat-equiv-badguy start 0 x y)))))))

  (verify-guards node-merge-cuts-aux
    :hints (("goal" :do-not-induct t)))

  (defret nth-of-node-merge-cuts-aux
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-cuts-aux
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb))))
    ;; :hints(("Goal" :in-theory (enable cut-data-of-update-cut-datai)))
    )

  ;; (set-stobj-updater node-merge-cuts-aux 4)

  (defret cutsdb-ok-of-node-merge-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;; (<= (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  ;;     (cut-data-length cutsdb))
                  )
             (cutsdb-ok new-cutsdb)))

  ;; (local (defthm cut-data-length-of-update-cut-datai
  ;;          (implies (< (nfix n) (cut-data-length cutsdb))
  ;;                   (equal (cut-data-length (update-cut-datai n val cutsdb))
  ;;                          (cut-data-length cutsdb)))))

  (defret cut-data-length-of-node-merge-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                      (cut-data-length cutsdb)))
             (equal (cut-data-length new-cutsdb)
                    (cut-data-length cutsdb)))
    ;; :hints(("Goal" :in-theory (enable cut-data-of-update-cut-datai)))
    )

  (defret cut-data-length-nondecreasing-of-node-merge-cuts-aux
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  ;; (defret node-merge-cuts-aux-when-not-updated
  ;;   (implies (not updatedp)
  ;;            (equal new-cutsdb cutsdb)))

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
           (b* ((mask (node-cut-expandmask cut-data cut-size dst-data dst-size 0 cutsdb))
                (dst-env (node-cut-truthenv dst-data dst-size 0 cutsdb bitarr))
                (cut-env (node-cut-truthenv cut-data cut-size 0 cutsdb bitarr))
                (shrink-env (truth::env-permute-shrink 0 nil mask dst-env 4)))
             (implies (and (truth4-deps-bounded cut-size cut-truth)
                           (node-cut-contained cut-data cut-size dst-data dst-size cutsdb)
                           (<= (nfix dst-size) 4))
                      (equal (truth::truth-eval cut-truth shrink-env 4)
                             (truth::truth-eval cut-truth cut-env 4))))
           :hints (("goal" :in-theory (enable truth::index-permute-stretch-redef))
                   (acl2::use-termhint
                    (b* ((mask (node-cut-expandmask cut-data cut-size dst-data dst-size 0 cutsdb))
                         (dst-env (node-cut-truthenv dst-data dst-size 0 cutsdb bitarr))
                         (cut-env (node-cut-truthenv cut-data cut-size 0 cutsdb bitarr))
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
                      


  ;; (local (defthmd truth-eval-by-other-env
  ;;          (implies (and (acl2::rewriting-positive-literal `(truth::truth-eval ,x ,env1 ,nvars))
  ;;                        (truth::truth-eval x env nvars)
  ;;                        (natp nvars))
  ;;                   (iff (truth::truth-eval x env1 nvars)
  ;;                        (or (hide (truth::truth-eval x env1 nvars))
  ;;                            (let ((mismatch (truth::env-mismatch x env env1 nvars)))
  ;;                              (or (equal (truth::env-lookup mismatch env)
  ;;                                         (truth::env-lookup mismatch env1))
  ;;                                  (not (truth::depends-on mismatch x nvars))
  ;;                                  (<= nvars mismatch))))))
  ;;          :hints (("goal" :expand ((:free (x) (hide x)))))))


  

  (local (defthm cutsdb-cut-base-index-implies-truth-deps-bounded
           (b* ((cut (cut-base-index cut cutsdb)))
             (implies (and (cutsdb-ok cutsdb)
                           (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (b* ((size (cut-datai cut cutsdb))
                           (truth (cut-datai (+ 1 cut) cutsdb)))
                        (truth4-deps-bounded size truth))))
           ;; :hints(("Goal" :use ((:instance cutsdb-cut-ok-when-base-index-p
           ;;                       (target-idx (cut-base-index cut cutsdb))))
           ;;         :in-theory (e/d (cutsdb-cut-ok) (cutsdb-cut-ok-when-base-index-p))))
           ))

  ;; (local (defthm cutsdb-cut-base-index-implies-bound-when-truth-depends-on
  ;;          (b* ((cut (cut-base-index cut cutsdb))
  ;;               (size (cut-datai cut cutsdb))
  ;;               (truth (cut-datai (+ 1 cut) cutsdb)))
  ;;            (implies (and (truth::depends-on v truth 4)
  ;;                          (natp v)
  ;;                          (< v 4)
  ;;                          (cutsdb-ok cutsdb)
  ;;                          (< (nfix cut) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  ;;                     (< v size)))
  ;;          :hints(("Goal" :use ((:instance cutsdb-cut-base-index-implies-truth-deps-bounded)
  ;;                               (:instance depends-on-implies-bound-when-truth4-deps-bounded
  ;;                                (truth (cut-datai (+ 1 (cut-base-index cut cutsdb)) cutsdb))
  ;;                                (n  (cut-datai (cut-base-index cut cutsdb) cutsdb))))
  ;;                  :in-theory (e/d (cutsdb-cut-ok) (cutsdb-cut-base-index-implies-truth-deps-bounded))))
  ;;          :rule-classes (:rewrite :linear)))

  ;; (local (defret lookup-nth-set-bit-pos-of-node-cut-expandmask-special
  ;;          (implies (and (equal bit-idx 0)
  ;;                        (node-cut-contained idx0 size0 dest-idx dest-size cutsdb)
  ;;                        (< (nfix n) (nfix size0))
  ;;                        (equal (+ a b) (nfix dest-idx)))
  ;;                   (equal (cut-datai (+ a b
  ;;                                        (nth-set-bit-pos n bitmask)) cutsdb)
  ;;                          (cut-datai (+ (nfix idx0) (nfix n)) cutsdb)))
  ;;          :hints (("goal" :use ((:instance lookup-nth-set-bit-pos-of-node-cut-expandmask
  ;;                                 (dest-idx (nfix dest-idx))))
  ;;                   :in-theory (disable lookup-nth-set-bit-pos-of-node-cut-expandmask)))
  ;;          :fn node-cut-expandmask))

  (defret truth-value-of-node-merge-cuts-aux2
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb))
         (data (+ 2 m))
         (truth (cut-datai (+ 1 m) new-cutsdb))
         (cut0 (cut-base-index cut0 cutsdb))
         (truth0 (cut-datai (+ 1 cut0) cutsdb))
         (data0 (+ 2 cut0))
         (size0 (cut-datai cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (truth1 (cut-datai (+ 1 cut1) cutsdb))
         (data1 (+ 2 cut1))
         (size1 (cut-datai cut1 cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval truth env 4)
                      (and (xor (eql neg0 1)
                                (truth::truth-eval truth0
                                                   (truth::env-permute-shrink
                                                    0 nil (node-cut-expandmask data0 size0 data size 0 new-cutsdb)
                                                    env 4)
                                                   4))
                           (xor (eql neg1 1)
                                (truth::truth-eval truth1
                                                   (truth::env-permute-shrink
                                                    0 nil (node-cut-expandmask data1 size1 data size 0 new-cutsdb)
                                                    env 4)
                                                   4)))))))

  (defret truth-value-of-node-merge-cuts-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb))
         (data (+ 2 m))
         (truth (cut-datai (+ 1 m) new-cutsdb))
         (cut0 (cut-base-index cut0 cutsdb))
         (truth0 (cut-datai (+ 1 cut0) cutsdb))
         (data0 (+ 2 cut0))
         (size0 (cut-datai cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (truth1 (cut-datai (+ 1 cut1) cutsdb))
         (data1 (+ 2 cut1))
         (size1 (cut-datai cut1 cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                      (and (xor (eql neg0 1)
                                (truth::truth-eval truth0 (node-cut-truthenv data0 size0 0 cutsdb bitarr) 4))
                           (xor (eql neg1 1)
                                (truth::truth-eval truth1 (node-cut-truthenv data1 size1 0 cutsdb bitarr) 4)))))))
  
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

  (local (defthm cutsdb-cut-base-index-implies-cut-data-lte-4
           (implies (and (cutsdb-ok cutsdb)
                         (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                    (<= (cut-datai (cut-base-index cut cutsdb) cutsdb) 4))
           ;; :hints(("Goal" :use ((:instance cutsdb-cut-ok-when-base-index-p
           ;;                       (target-idx (cut-base-index cut cutsdb))))
           ;;         :in-theory (e/d (cutsdb-cut-ok) (cutsdb-cut-ok-when-base-index-p))))
           :rule-classes (:rewrite :linear)))
  
  (local (defthm cut-next-upper-bound-by-size
           (implies (and (cutp cut cutsdb)
                         (natp cut)
                         (<= (cut-datai cut cutsdb) 4))
                    (<= (cut-next$ cut cutsdb) (+ 6 cut)))
           :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
                                          (rewrite-to-cut-next$))))
           :rule-classes (:rewrite :linear)))

  (defret new-data-ok-of-node-merge-cuts-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         ;; (size (cut-datai m new-cutsdb))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (data (+ 2 m))
         )
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (+ 6 m) (cut-data-length cutsdb)))
               (cutsdb-cut-ok m new-cutsdb)))
    :hints((acl2::use-termhint
            `'(:expand ((cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       ,(hq new-cutsdb)))))))

  (defret new-data-bounded-of-node-merge-cuts-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    ;; (cutsdb-cut-bounded cut0 bound cutsdb)
                    ;; (cutsdb-cut-bounded cut1 bound cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cutsdb-cut-bounded m (cut-nnodes cutsdb) new-cutsdb)))
    :hints(("goal" :in-theory (e/d (cutsdb-cut-bounded)
                                   (cutsdb-cut-bounded-when-cutsdb-ok))
            :use ((:instance cutsdb-cut-bounded-when-cutsdb-ok
                   (n (cut-base-index cut0 cutsdb)))
                  (:instance cutsdb-cut-bounded-when-cutsdb-ok
                   (n (cut-base-index cut1 cutsdb)))))))

  (defret new-data-lit-ids-of-node-merge-cuts-aux
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)))
      (implies (and updatedp
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (cutsdb-cut-lit-idsp cut0 aignet cutsdb)
                    (cutsdb-cut-lit-idsp cut1 aignet cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cutsdb-cut-lit-idsp m aignet new-cutsdb)))
    :hints(("goal" :in-theory (e/d (cutsdb-cut-lit-idsp)
                                   ()))))
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-bounded size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb)))))

  (defret node-merge-cuts-aux-cutsize
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb)))
      (implies (and updatedp)
               (<= size 4)))
    :rule-classes :linear)

  (local (defthm cut-next$-of-update-cut-data
           (implies (cutp n cutsdb)
                    (equal (cut-next$ n (update-cut-datai n v cutsdb))
                           (+ 2 (nfix n) (nfix v))))
           :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
                                          (rewrite-to-cut-next$))))))

  (local (defthm stobjs::range-nat-equiv-badguy-<-2-plus-max
           (implies (and (not (stobjs::range-nat-equiv 0 max a b))
                         (natp max))
                    (< (stobjs::range-nat-equiv-badguy 0 max a b) (+ 2 max)))))

  ;; (defthm stobjs::range-nat-equiv-of-update-max-plus-2
  ;;   (implies (natp max)
  ;;            (stobjs::range-nat-equiv 0 max (update-nth (+ 2 max) v x) x)))

  (defret node-merge-cuts-aux-next-cut
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (next (cut-next$ m new-cutsdb)))
      (implies (and updatedp
                    (cutp m cutsdb))
               (<= next (+ 6 m))))
    :hints(("Goal" :in-theory (disable rewrite-to-cut-next$)
            :rw-cache-state nil))
    :rule-classes (:rewrite :linear))

  ;; (set-stobj-updater node-merge-cuts-aux 4 1)

)

;; (trace$ #!acl2 (relieve-hyp :entry (list 'relieve-hyp
;;                                          rune bkptr hyp0 unify-subst
;;                                          ancestors)
;;                             :exit (b* (((list ?step-limit ?wonp ?failure-reason) values))
;;                                     (list 'relieve-hyp wonp failure-reason))))

;; (define cuts-mergeable ((cut0 cutp$)
;;                         (cut1 cutp$)
;;                         (node-cuts-start cutp$)
;;                         (cutsdb cutsdb-ok))
;;   :non-executable t
;;   :guard (and (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;               (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;               (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
;;   :verify-guards nil
;;   :returns (mergeable)
;;   (b* ((cut0 (cut-fix cut0))
;;        (data0 (+ 2 cut0))
;;        (size0 (cut-datai cut0 cutsdb))
;;        (cut1 (cut-fix cut1))
;;        (data1 (+ 2 cut1))
;;        (size1 (cut-datai cut1 cutsdb))
;;        (dest-size (node-merge-cuts-count data0 size0 data1 size1 cutsdb))
;;        (dest-cut (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;        (dest-data (+ 2 dest-cut))
;;        (cutsdb (node-merge-cuts-write data0 size0 data1 size1 dest-data cutsdb))
;;        ((when (< 4 dest-size)) nil))
;;     (not (cuts-check-any-contained node-cuts-start dest-cut dest-data dest-size cutsdb)))
;;   ///
;;   (defret node-merge-cuts-aux-updatedp
;;     (iff updatedp
;;          (cuts-mergeable cut0 cut1 cutsdb))
;;     :hints (("goal" :expand (<call>)))
;;     :fn node-merge-cuts-aux)

;;   (def-updater-independence-thm cuts-mergeable-updater-independence
;;     (implies (and (equal cut0-next (cut-next$ cut0 old))
;;                   (stobjs::range-nat-equiv 0 cut0-next
;;                                            (nth *cut-datai1* new)
;;                                            (nth *cut-datai1* old))
;;                   (equal cut1-next (cut-next$ cut1 old))
;;                   (stobjs::range-nat-equiv 0 cut1-next
;;                                            (nth *cut-datai1* new)
;;                                            (nth *cut-datai1* old))
;;                   ;; (stobjs::range-nat-equiv 0 cut1
;;                   ;;                      (nth *cut-datai1* new)
;;                   ;;                      (nth *cut-datai1* old))
;;                   )
;;              (equal (cuts-mergeable cut0 cut1 node-cuts-start new)
;;                     (cuts-mergeable cut0 cut1 node-cuts-start old))))

;;   (defret cuts-mergeable-of-cut-fix-0
;;     (implies (Equal (cut-base-index cut0 cutsdb1)
;;                     (cut-base-index cut0 cutsdb))
;;              (equal (cuts-mergeable (cut-base-index cut0 cutsdb1) cut1 node-cuts-start cutsdb)
;;                     (cuts-mergeable cut0 cut1 node-cuts-start cutsdb))))

;;   (defret cuts-mergeable-of-cut-fix-1
;;     (implies (Equal (cut-base-index cut1 cutsdb1)
;;                     (cut-base-index cut1 cutsdb))
;;              (equal (cuts-mergeable cut0 (cut-base-index cut1 cutsdb1) node-cuts-start cutsdb)
;;                     (cuts-mergeable cut0 cut1 node-cuts-start cutsdb)))))




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


(define node-cut-reduce ((read-loc natp) (read-size natp) (write-loc natp)
                         (bit-idx natp) (mask natp) cutsdb)
  :guard (and (<= (+ read-loc read-size) (cut-data-length cutsdb))
              (<= write-loc read-loc))
  :measure (nfix read-size)
  :returns (new-cutsdb)
  (b* (((when (zp read-size)) cutsdb)
       ((when (or (not (logbitp bit-idx (lnfix mask)))
                  (<= (lnfix read-loc) (lnfix write-loc))))
        (node-cut-reduce (+ 1 (lnfix read-loc))
                         (1- read-size)
                         (+ (logbit bit-idx (lnfix mask)) (lnfix write-loc))
                         (1+ (lnfix bit-idx)) mask cutsdb))
       (cutsdb (update-cut-datai write-loc (cut-datai read-loc cutsdb) cutsdb)))
    (node-cut-reduce (+ 1 (lnfix read-loc))
                     (1- read-size)
                     (+ 1 (lnfix write-loc))
                     (1+ (lnfix bit-idx)) mask cutsdb))
  ///
  (defret nth-of-node-cut-reduce
    (implies (not (Equal (nfix n) *cut-datai1*))
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

  ;; (local (defthmd nth-cut-datai-of-update-cut-datai-split
  ;;          (equal (nth n (nth *cut-datai1* (update-cut-datai m v x)))
  ;;                 (if (equal (nfix n) (nfix m))
  ;;                     v
  ;;                   (nth n (nth *cut-datai1* x))))
  ;;          :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding
  ;;                                             update-cut-datai)))))

  

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



  (local (defthm cut-datai-of-update-cut-datai-split
           (equal (cut-datai n (update-cut-datai m v x))
                  (if (equal (nfix n) (nfix m))
                      (nfix v)
                    (cut-datai n x)))
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

  (defret nth-cut-data-of-node-cut-reduce
    (implies (not (and (<= (nfix write-loc) (nfix n))
                       (< (nfix n) (+ (nfix write-loc) (logcount (loghead read-size (logtail bit-idx (nfix mask))))))))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb))))
    :hints (("goal" :induct t :in-theory (enable* acl2::bool->bit
                                                  ;; nth-cut-datai-of-update-cut-datai-split
                                                  ;; cut-data-of-update-cut-datai
                                                  acl2::arith-equiv-forwarding))
            (and stable-under-simplificationp
                 '(:in-theory (enable ;; nth-cut-datai-of-update-cut-datai-split
                                      logcount-loghead-monotonic)))
            ;; (and stable-under-simplificationp
            ;;      '(:expand ((logtail bit-idx (nfix mask))
            ;;                 (logtail 1 (nfix mask))
            ;;                 (:free (x) (loghead read-size x))
            ;;                 (:free (a b) (logcount (logcons a b))))))
            ))

  ;; for fixequiv hint
  ;; (set-stobj-updater node-cut-reduce 5)


  (defret cut-data-entry-of-node-cut-reduce
    (implies (and (<= (nfix write-loc) (nfix read-loc))
                  (<= (nfix write-loc) (nfix n))
                  (< (nfix n) (+ (nfix write-loc) (logcount (loghead read-size (logtail bit-idx (nfix mask)))))))
             (equal (cut-datai n new-cutsdb)
                    (cut-datai (+ (nfix read-loc)
                                  (nth-set-bit-pos (- (nfix n) (nfix write-loc))
                                                          (loghead read-size (logtail bit-idx (nfix mask)))))
                               cutsdb)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit))
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix n) (nfix write-loc)))))))



  (defret cut-data-length-of-node-cut-reduce
    (implies (<= (+ (nfix write-loc) (nfix read-size)) (cut-data-length cutsdb))
             (equal (cut-data-length new-cutsdb)
                    (cut-data-length cutsdb))))


  (defret cutsdb-ok-of-node-cut-reduce
    (implies (and (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix write-loc))
                  (cutsdb-ok cutsdb))
             (cutsdb-ok new-cutsdb)))
             

  (local (in-theory (disable (:d node-cut-reduce))))

  (local (defthmd cutsdb-data-nodes-sorted-implies-order
           (implies (and (cutsdb-data-nodes-sorted idx size cutsdb)
                         (< (nfix idx) (nfix idx2))
                         (< (nfix idx2) (+ (nfix idx) (nfix size))))
                    (< (cut-datai idx cutsdb) (cut-datai idx2 cutsdb)))
           :hints(("Goal" :in-theory (enable cutsdb-data-nodes-sorted)))))

  (local (defthm cutsdb-data-nodes-sorted-implies-order-rw
           (implies (and (cutsdb-data-nodes-sorted idx size cutsdb)
                         (<= (nfix idx) (nfix idx2))
                         (case-split (< (nfix idx2) (+ (nfix idx) (nfix size))))
                         (< (cut-datai idx1 cutsdb) (cut-datai idx cutsdb)))
                    (< (cut-datai idx1 cutsdb) (cut-datai idx2 cutsdb)))
           :hints (("goal" :use cutsdb-data-nodes-sorted-implies-order
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

 
  (local (defret cutsdb-data-nodes-sorted-of-node-cut-reduce-lemma
           (implies (and (cutsdb-data-nodes-sorted read-loc read-size cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (cutsdb-data-nodes-sorted
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 cutsdb-data-nodes-sorted)))))


  (defret cutsdb-data-nodes-sorted-of-node-cut-reduce
    (implies (and (cutsdb-data-nodes-sorted read-loc read-size cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (cutsdb-data-nodes-sorted write-loc size new-cutsdb))
    :hints (("goal" :use cutsdb-data-nodes-sorted-of-node-cut-reduce-lemma
             :in-theory (disable cutsdb-data-nodes-sorted-of-node-cut-reduce-lemma))))

  (local (defret cutsdb-data-nodes-bounded-of-node-cut-reduce-lemma
           (implies (and (cutsdb-data-nodes-bounded read-loc read-size bound cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (cutsdb-data-nodes-bounded
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     bound
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 cutsdb-data-nodes-bounded)))))

  (defret cutsdb-data-nodes-bounded-of-node-cut-reduce
    (implies (and (cutsdb-data-nodes-bounded read-loc read-size bound cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (cutsdb-data-nodes-bounded write-loc size bound new-cutsdb))
    :hints (("goal" :use cutsdb-data-nodes-bounded-of-node-cut-reduce-lemma
             :in-theory (disable cutsdb-data-nodes-bounded-of-node-cut-reduce-lemma))))

  (local (defret cutsdb-data-nodes-lit-idsp-of-node-cut-reduce-lemma
           (implies (and (cutsdb-data-nodes-lit-idsp read-loc read-size aignet cutsdb)
                         (<= (nfix write-loc) (nfix read-loc)))
                    (cutsdb-data-nodes-lit-idsp
                     write-loc
                     (logcount (loghead read-size (logtail bit-idx (nfix mask))))
                     aignet
                     new-cutsdb))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* acl2::arith-equiv-forwarding acl2::bool->bit
                                 cutsdb-data-nodes-lit-idsp)))))

  (defret cutsdb-data-nodes-lit-idsp-of-node-cut-reduce
    (implies (and (cutsdb-data-nodes-lit-idsp read-loc read-size aignet cutsdb)
                  (<= (nfix write-loc) (nfix read-loc))
                  (equal size (logcount (loghead read-size (logtail bit-idx (nfix mask))))))
             (cutsdb-data-nodes-lit-idsp write-loc size aignet new-cutsdb))
    :hints (("goal" :use cutsdb-data-nodes-lit-idsp-of-node-cut-reduce-lemma
             :in-theory (disable cutsdb-data-nodes-lit-idsp-of-node-cut-reduce-lemma))))

  (defret cut-data-length-nondecreasing-of-node-cut-reduce
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :hints (("goal" :induct <call>
             :expand ((:free (read-size) <call>))))
    :rule-classes :linear))



(define node-reduce-new-cut ((cutsdb cutsdb-ok))
  :guard (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              ((unless (< m (cut-data-length cutsdb))) nil))
           (cutsdb-cut-ok m cutsdb))
           ;;    (size (cut-datai m cutsdb))
           ;;    ((unless (<= (cut-next m cutsdb) (cut-data-length cutsdb))) nil)
           ;;    (truth (cut-datai (+ 1 m) cutsdb))
           ;;    (data (+ 2 m)))
           ;; (and (<= size 4)
           ;;      (truth4-p truth)
           ;;      (truth4-deps-bounded size truth)
  ;;      (cutsdb-data-nodes-sorted data size cutsdb)))
  :prepwork ((local (defthm unsigned-byte-p-when-natp
                      (implies (and (natp x)
                                    (< x (expt 2 32)))
                               (unsigned-byte-p 32 x))
                      :hints(("Goal" :in-theory (enable unsigned-byte-p))))))
  :returns (new-cutsdb)
  (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       (size (cut-datai m cutsdb))
       (truth (cut-datai (+ 1 m) cutsdb))
       (mask (truth-reducemask size 0 truth))
       ((when (eql mask (loghead size -1)))
        ;; No reduction
        cutsdb)
       (new-size (logcount mask))
       (new-truth (truth::permute-shrink4 0 0 mask truth))
       (cutsdb (node-cut-reduce (+ 2 m) size (+ 2 m) 0 mask cutsdb))
       (cutsdb (update-cut-datai m new-size cutsdb))
       (cutsdb (update-cut-datai (+ 1 m) new-truth cutsdb)))
    cutsdb)
  ///
  (defret cutsdb-ok-of-node-reduce-new-cut
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
                (orig-env (node-cut-truthenv data cut-size 0 cutsdb bitarr))
                (new-cutsdb (node-cut-reduce data cut-size data 0 mask cutsdb))
                (cut-env (node-cut-truthenv data (logcount mask) 0 new-cutsdb bitarr))
                (stretch-env (truth::env-permute-stretch 0 nil mask cut-env 4)))
             (implies (and (truth4-deps-bounded cut-size truth)
                           (<= (nfix cut-size) 4))
                      (equal (truth::truth-eval truth stretch-env 4)
                             (truth::truth-eval truth orig-env 4))))
           :hints (("goal" :in-theory (enable truth::index-permute-shrink-redef))
                   (acl2::use-termhint
                    (b* ((mask (truth-reducemask cut-size 0 truth))
                         (orig-env (node-cut-truthenv data cut-size 0 cutsdb bitarr))
                         (new-cutsdb (node-cut-reduce data cut-size data 0 mask cutsdb))
                         (cut-env (node-cut-truthenv data (logcount mask) 0 new-cutsdb bitarr))
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


  (defret truth-value-of-node-reduce-new-cut
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb))
         (data (+ 2 m))
         (truth (cut-datai (+ 1 m) new-cutsdb))
         (old-size (cut-datai m cutsdb))
         (old-truth (cut-datai (+ 1 m) cutsdb)))
      (implies (and (cutsdb-ok cutsdb)
                    (cutsdb-cut-ok m cutsdb)
                    ;; (<= old-size 4)
                    ;; (truth4-deps-bounded old-size old-truth)
                    )
               (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                      (truth::truth-eval old-truth (node-cut-truthenv data old-size 0 cutsdb bitarr) 4)))))

  (local (defthm cut-next$-of-update-cut-data
           (implies (and (cutp n cutsdb)
                         (<= (nfix size) (cut-datai n cutsdb)))
                    (<= (cut-next$ n (update-cut-datai n size cutsdb))
                        (cut-next$ n cutsdb)))
           :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
                                          (rewrite-to-cut-next$))))
           :rule-classes :linear))
  
  ;; (local (defthm cut-next-upper-bound-by-size
  ;;          (implies (and (cutp cut cutsdb)
  ;;                        (natp cut)
  ;;                        (<= (cut-datai cut cutsdb) 4))
  ;;                   (<= (cut-next$ cut cutsdb) (+ 6 cut)))
  ;;          :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
  ;;                                         (rewrite-to-cut-next$))))
  ;;          :rule-classes (:rewrite :linear)))

  (defret new-data-ok-of-node-reduce-new-cut
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-datai m new-cutsdb))
         ;; (data (+ 2 m))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (old-size (cut-datai m cutsdb))
         ;; (old-truth (cut-datai (+ 1 m) cutsdb))
         )
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-cut-ok m cutsdb)
                    (cutsdb-ok cutsdb) 
                    ;; (<= old-size 4)
                    ;; (truth4-p old-truth)
                    ;; (truth4-deps-bounded old-size old-truth)
                    ;; (cutsdb-data-nodes-sorted data old-size cutsdb)
                    ;; (cutsdb-ok cutsdb)
                    )
               (cutsdb-cut-ok m new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-bounded size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               ))
    :hints ((acl2::use-termhint
             (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (new new-cutsdb)
                  ((acl2::termhint-seq
                    `'(:expand ((cutsdb-cut-ok ,(hq m) ,(hq cutsdb))
                                (cutsdb-cut-ok ,(hq m) ,(hq new)))))))
               ''(:in-theory (e/d (cut-next)
                                  (rewrite-to-cut-next$)))))))

  (defret new-data-bounded-of-node-reduce-new-cut
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-datai m new-cutsdb))
         ;; (data (+ 2 m))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (old-size (cut-datai m cutsdb))
         ;; (old-truth (cut-datai (+ 1 m) cutsdb))
         )
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-cut-bounded m bound cutsdb)
                    (cutsdb-ok cutsdb) 
                    ;; (<= old-size 4)
                    ;; (truth4-p old-truth)
                    ;; (truth4-deps-bounded old-size old-truth)
                    ;; (cutsdb-data-nodes-sorted data old-size cutsdb)
                    ;; (cutsdb-ok cutsdb)
                    )
               (cutsdb-cut-bounded m bound new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-bounded size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               ))
    :hints(("Goal" :in-theory (enable cutsdb-cut-bounded))))

  (defret new-data-lit-idsp-of-node-reduce-new-cut
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-datai m new-cutsdb))
         ;; (data (+ 2 m))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (old-size (cut-datai m cutsdb))
         ;; (old-truth (cut-datai (+ 1 m) cutsdb))
         )
      (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-cut-lit-idsp m aignet cutsdb)
                    (cutsdb-ok cutsdb) 
                    ;; (<= old-size 4)
                    ;; (truth4-p old-truth)
                    ;; (truth4-deps-lit-idsp old-size old-truth)
                    ;; (cutsdb-data-nodes-sorted data old-size cutsdb)
                    ;; (cutsdb-ok cutsdb)
                    )
               (cutsdb-cut-lit-idsp m aignet new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-lit-idsp size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               ))
    :hints(("Goal" :in-theory (enable cutsdb-cut-lit-idsp))))

  (defret nth-of-node-reduce-new-cut
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-reduce-new-cut
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb)))))

  (defret cut-data-length-of-node-reduce-new-cut
    (implies (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (size (cut-datai m cutsdb)))
               (<= (+ 2 m size) (cut-data-length cutsdb)))
             (equal (cut-data-length new-cutsdb)
                    (cut-data-length cutsdb))))

  (defret node-reduce-new-cut-cutsize
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb)))
      (<= size (cut-datai m cutsdb)))
    :rule-classes :linear)
  
  (defret cut-data-length-nondecreasing-of-node-reduce-new-cut
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  ;; (set-stobj-updater node-reduce-new-cut 0)
  )



(define node-merge-and-reduce-cuts ((cut0 cutp$)
                                    (neg0 bitp)
                                    (cut1 cutp$)
                                    (neg1 bitp)
                                    (node-cuts-start cutp$)
                                    (cutsdb cutsdb-ok))
  :guard (and (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                 (cut-data-length cutsdb))
              )
  :returns (mv (updatedp)
               (new-cutsdb))
  (b* (((mv updatedp cutsdb) (node-merge-cuts-aux cut0 neg0 cut1 neg1 node-cuts-start cutsdb))
       ((unless updatedp) (mv nil cutsdb))
       (cutsdb (node-reduce-new-cut cutsdb)))
    (mv t cutsdb))
  ///
  

  (defret nth-of-node-merge-and-reduce-cuts
    (implies (not (equal (nfix n) *cut-datai1*))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-and-reduce-cuts
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (equal (nth n (nth *cut-datai1* new-cutsdb))
                    (nth n (nth *cut-datai1* cutsdb))))
    ;; :hints(("Goal" :in-theory (enable cut-data-of-update-cut-datai)))
    )

  ;; (set-stobj-updater node-merge-and-reduce-cuts 4 1)

  (defret cutsdb-ok-of-node-merge-and-reduce-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (cutsdb-ok new-cutsdb)))

  ;; (local (defthm cut-data-length-of-update-cut-datai
  ;;          (implies (< (nfix n) (cut-data-length cutsdb))
  ;;                   (equal (cut-data-length (update-cut-datai n val cutsdb))
  ;;                          (cut-data-length cutsdb)))))

  (defret cut-data-length-of-node-merge-and-reduce-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (<= (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                      (cut-data-length cutsdb)))
             (equal (cut-data-length new-cutsdb)
                    (cut-data-length cutsdb)))
    ;; :hints(("Goal" :in-theory (enable cut-data-of-update-cut-datai)))
    )

  ;; (defret node-merge-and-reduce-cuts-when-not-updated
  ;;   (implies (not updatedp)
  ;;            (equal new-cutsdb cutsdb)))

  (local (defret node-reduce-new-cut-cutsize-free
           (b* ((m (nodecut-indicesi (cut-nnodes cdb) cdb))
                (size (cut-datai m new-cutsdb)))
             (implies (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                      (<= size (cut-datai m cutsdb))))
           :fn node-reduce-new-cut
           :rule-classes :linear))

  (local
   (defret truth-value-of-node-reduce-new-cut-free
     (b* ((m (nodecut-indicesi (cut-nnodes cdb) cdb))
          (size (cut-datai m new-cutsdb))
          (data (+ 2 m))
          (truth (cut-datai (+ 1 m) new-cutsdb))
          (old-size (cut-datai m cutsdb))
          (old-truth (cut-datai (+ 1 m) cutsdb)))
       (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                     (cutsdb-ok cutsdb)
                     (cutsdb-cut-ok m cutsdb))
                (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                       (truth::truth-eval old-truth (node-cut-truthenv data old-size 0 cutsdb bitarr) 4))))
     :fn node-reduce-new-cut))

  ;; (local (defret new-data-ok-of-node-reduce-new-cut-free
  ;;          (b* ((m (nodecut-indicesi (cut-nnodes cdb) cdb))
  ;;               ;; (size (cut-datai m new-cutsdb))
  ;;               ;; (data (+ 2 m))
  ;;               ;; (truth (cut-datai (+ 1 m) new-cutsdb))
  ;;               ;; (old-size (cut-datai m cutsdb))
  ;;               ;; (old-truth (cut-datai (+ 1 m) cutsdb))
  ;;               )
  ;;            (implies (and (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                          (cutsdb-cut-ok m cutsdb)
  ;;                          (cutsdb-ok cutsdb)
  ;;                          ;; (cutsdb-ok cutsdb)
  ;;                          ;; (<= old-size 4)
  ;;                          ;; (truth4-p old-truth)
  ;;                          ;; (truth4-deps-bounded old-size old-truth)
  ;;                          ;; (cutsdb-data-nodes-sorted data old-size cutsdb)
  ;;                          ;; (cutsdb-ok cutsdb)
  ;;                          )
  ;;                     (cutsdb-cut-ok m new-cutsdb)
  ;;                     ;; (and (<= size 4)
  ;;                     ;;      (truth4-p truth)
  ;;                     ;;      (truth4-deps-bounded size truth)
  ;;                     ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
  ;;                     ))
  ;;          ;; :hints (("goal" :use new-data-ok-of-node-reduce-new-cut
  ;;          ;;          :in-theory (disable new-data-ok-of-node-reduce-new-cut)))
  ;;          :fn node-reduce-new-cut))

  (defret truth-value-of-node-merge-and-reduce-cuts
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb))
         (data (+ 2 m))
         (truth (cut-datai (+ 1 m) new-cutsdb))
         (cut0 (cut-base-index cut0 cutsdb))
         (truth0 (cut-datai (+ 1 cut0) cutsdb))
         (data0 (+ 2 cut0))
         (size0 (cut-datai cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (truth1 (cut-datai (+ 1 cut1) cutsdb))
         (data1 (+ 2 cut1))
         (size1 (cut-datai cut1 cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (+ 6 m) (cut-data-length cutsdb)))
               (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                      (and (xor (eql neg0 1)
                                (truth::truth-eval truth0 (node-cut-truthenv data0 size0 0 cutsdb bitarr) 4))
                           (xor (eql neg1 1)
                                (truth::truth-eval truth1 (node-cut-truthenv data1 size1 0 cutsdb bitarr) 4))))))
    ;; :hints ((acl2::use-termhint
    ;;          (b* (((mv ?updatedp cutsdb) (node-merge-cuts-aux cut0 neg0 cut1 neg1 cutsdb)))
    ;;            `'(:use ((:instance truth-value-of-node-reduce-new-cut
    ;;                      (cutsdb ,(hq cutsdb))))
    ;;               :in-theory (disable truth-value-of-node-reduce-new-cut)))))
    )

  (defret new-data-ok-of-node-merge-and-reduce-cuts
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         ;; (size (cut-datai m new-cutsdb))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (data (+ 2 m))
         )
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (+ 6 m) (cut-data-length cutsdb)))
               (cutsdb-cut-ok m new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-bounded size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               )))

  (defret new-data-bounded-of-node-merge-and-reduce-cuts
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-datai m new-cutsdb))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (data (+ 2 m))
         )
      (implies (and updatedp
                    (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (+ 6 m) (cut-data-length cutsdb)))
               (cutsdb-cut-bounded m (cut-nnodes cutsdb1) new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-bounded size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               )))

  (defret new-data-lit-idsp-of-node-merge-and-reduce-cuts
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
         ;; (size (cut-datai m new-cutsdb))
         ;; (truth (cut-datai (+ 1 m) new-cutsdb))
         ;; (data (+ 2 m))
         )
      (implies (and updatedp
                    (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                    (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (cutsdb-ok cutsdb)
                    (cutsdb-cut-lit-idsp cut0 aignet cutsdb)
                    (cutsdb-cut-lit-idsp cut1 aignet cutsdb)
                    (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< (+ 6 m) (cut-data-length cutsdb)))
               (cutsdb-cut-lit-idsp m aignet new-cutsdb)
               ;; (and (<= size 4)
               ;;      (truth4-p truth)
               ;;      (truth4-deps-lit-idsp size truth)
               ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
               )))

  (defret cut-data-length-nondecreasing-of-node-merge-and-reduce-cuts
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defret node-merge-and-reduce-cuts-updatedp
    (iff updatedp
         (mv-nth 0 (node-merge-cuts-aux cut0 neg0 cut1 neg1 node-cuts-start cutsdb))))
  )






(define node-merge-cuts ((cut0 cutp$)
                         (neg0 bitp)
                         (cut1 cutp$)
                         (neg1 bitp)
                         (node-cuts-start cutp$)
                         (cutsdb cutsdb-ok))
  :guard (and (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
  :returns (mv updatedp new-cutsdb)
  :prepwork ((local (in-theory (disable stobjs::range-nat-equiv-open
                                        ;; cutsdb-cut-ok-implies-less-than-length
                                        ))))
  (b* ((new-cut-idx (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
       (cutsdb (cuts-maybe-grow-cut-data (+ 7 new-cut-idx) cutsdb))
       ((mv added cutsdb) (node-merge-and-reduce-cuts cut0 neg0 cut1 neg1 node-cuts-start cutsdb))
       ((unless added) (mv nil cutsdb))
       (cutsdb (update-nodecut-indicesi$
                (cut-nnodes cutsdb)
                (+ 2 new-cut-idx (cut-datai new-cut-idx cutsdb))
                cutsdb)))
    (mv t cutsdb))
  ///
  

  ;; (local (defthm cut-target-less-than-nodecut-index-when-base-index-less
  ;;          (implies (and (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                        (cutsdb-ok cutsdb)
  ;;                        (natp cut))
  ;;                   (< cut (cut-data-length cutsdb)))
  ;;          :hints (("goal" :use ((:instance cutsdb-cut-ok-of-base-index
  ;;                                 (target-idx cut))
  ;;                                (:instance cut-base-index-of-next-cut
  ;;                                 (target-idx cut))
  ;;                                (:instance cut-base-index-monotonic
  ;;                                 (target-idx1 cut)
  ;;                                 (target-idx  (+ 2 (cut-base-index cut cutsdb)
  ;;                                                 (cut-datai (cut-base-index cut cutsdb) cutsdb)))))
  ;;                   :in-theory (e/d (cutsdb-cut-ok)
  ;;                                   (cutsdb-cut-ok-of-base-index
  ;;                                    cut-base-index-of-next-cut
  ;;                                    cut-base-index-monotonic))))
  ;;          :rule-classes (:rewrite :linear)))

  ;; (local (defthm cut-target-range-less-than-nodecut-index-when-base-index-less
  ;;          (implies (and (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                        (cutsdb-ok cutsdb)
  ;;                        (not (stobjs::range-nat-equiv 0 cut x y)))
  ;;                   (< (stobjs::range-nat-equiv-badguy 0 cut x y) (cut-data-length cutsdb)))
  ;;          :hints (("goal" :use cut-target-less-than-nodecut-index-when-base-index-less
  ;;                   :in-theory (disable cut-target-less-than-nodecut-index-when-base-index-less)))
  ;;          :rule-classes (:rewrite :linear)))

  ;; (local (defthm cut-base-index-of-cuts-maybe-grow-cut-data
  ;;          (implies (and (< (cut-base-index cut cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                        (Cutsdb-ok cutsdb))
  ;;                   (equal (cut-base-index cut (cuts-maybe-grow-cut-data size cutsdb))
  ;;                          (cut-base-index cut cutsdb)))
  ;;          :hints (("goal" :use cut-target-less-than-nodecut-index-when-base-index-less
  ;;                   :in-theory (disable cut-target-less-than-nodecut-index-when-base-index-less)))))

  (local (defret new-data-ok-of-node-merge-and-reduce-cuts-special
           (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                ;; (size (cut-datai m new-cutsdb))
                ;; (truth (cut-datai (+ 1 m) new-cutsdb))
                ;; (data (+ 2 m))
                )
             (implies (and updatedp
                           (cutsdb-ok cutsdb)
                           (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< (+ 6 m) (cut-data-length cutsdb))
                           (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                                  (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (cutsdb-cut-ok m new-cutsdb)
                      ;; (and (<= size 4)
                      ;;      (truth4-p truth)
                      ;;      (truth4-deps-bounded size truth)
                      ;;      (cutsdb-data-nodes-sorted data size new-cutsdb))
                      ))
           :hints (("goal" :use new-data-ok-of-node-merge-and-reduce-cuts
                    :in-theory (disable new-data-ok-of-node-merge-and-reduce-cuts)))
           :fn node-merge-and-reduce-cuts))

  (local (defret new-data-ok-of-node-merge-and-reduce-cuts-special-size
           (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                (size (cut-datai m new-cutsdb)))
             (implies (and updatedp
                           (cutsdb-ok cutsdb)
                           (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< (+ 6 m) (cut-data-length cutsdb))
                           (equal (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1)
                                  (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
                      (<= size 4)))
           ;; :hints (("goal" :use new-data-ok-of-node-merge-and-reduce-cuts-special
           ;;          :in-theory (disable new-data-ok-of-node-merge-and-reduce-cuts-special
           ;;                              new-data-ok-of-node-merge-and-reduce-cuts)))
           :rule-classes :linear
           :fn node-merge-and-reduce-cuts))

  (defret cutsdb-ok-of-node-merge-cuts
    (implies (and (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) )
             (cutsdb-ok new-cutsdb)))

  (defret cutsdb-lit-idsp-of-node-merge-cuts
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (< (cut-base-index cut0 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-base-index cut1 cutsdb) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) )
             (cutsdb-lit-idsp aignet new-cutsdb)))

  
  (defret nth-of-node-merge-cuts
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-cuts
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb))))
    ;; :hints(("Goal" :in-theory (enable cut-data-of-update-cut-datai)))
    )

  (defret nth-nodecut-indices-of-node-merge-cuts
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret next-cut-of-node-merge-cuts
    (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
        (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
    :rule-classes :linear)

  ;; (set-stobj-updater node-merge-cuts 4)

  (defret cut-data-length-nondecreasing-of-node-merge-cuts
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (local (defret truth-value-of-node-merge-and-reduce-cuts-special
           (b* ((m (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb1))
                (size (cut-datai m new-cutsdb))
                (data (+ 2 m))
                (truth (cut-datai (+ 1 m) new-cutsdb))
                (cut0 (cut-base-index cut0 cutsdb))
                (truth0 (cut-datai (+ 1 cut0) cutsdb))
                (data0 (+ 2 cut0))
                (size0 (cut-datai cut0 cutsdb))
                (cut1 (cut-base-index cut1 cutsdb))
                (truth1 (cut-datai (+ 1 cut1) cutsdb))
                (data1 (+ 2 cut1))
                (size1 (cut-datai cut1 cutsdb)))
             (implies (and updatedp
                           (equal m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (cutsdb-ok cutsdb)
                           (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                           (< (+ 6 m) (cut-data-length cutsdb)))
                      (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                             (and (xor (eql neg0 1)
                                       (truth::truth-eval truth0 (node-cut-truthenv data0 size0 0 cutsdb bitarr) 4))
                                  (xor (eql neg1 1)
                                       (truth::truth-eval truth1 (node-cut-truthenv data1 size1 0 cutsdb bitarr) 4))))))
           ;; :hints ((acl2::use-termhint
           ;;          (b* (((mv ?updatedp cutsdb) (node-merge-cuts-aux cut0 neg0 cut1 neg1 cutsdb)))
           ;;            `'(:use ((:instance truth-value-of-node-reduce-new-cut
           ;;                      (cutsdb ,(hq cutsdb))))
           ;;               :in-theory (disable truth-value-of-node-reduce-new-cut)))))
           :hints (("goal" :use ((:instance truth-value-of-node-merge-and-reduce-cuts))
                    :in-theory (disable truth-value-of-node-merge-and-reduce-cuts)))
           :fn node-merge-and-reduce-cuts))

  (defret truth-value-of-node-merge-cuts
    (b* ((m (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (size (cut-datai m new-cutsdb))
         (data (+ 2 m))
         (truth (cut-datai (+ 1 m) new-cutsdb))
         (cut0 (cut-base-index cut0 cutsdb))
         (truth0 (cut-datai (+ 1 cut0) cutsdb))
         (data0 (+ 2 cut0))
         (size0 (cut-datai cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (truth1 (cut-datai (+ 1 cut1) cutsdb))
         (data1 (+ 2 cut1))
         (size1 (cut-datai cut1 cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (truth::truth-eval truth (node-cut-truthenv data size 0 new-cutsdb bitarr) 4)
                      (and (xor (eql neg0 1)
                                (truth::truth-eval truth0 (node-cut-truthenv data0 size0 0 cutsdb bitarr) 4))
                           (xor (eql neg1 1)
                                (truth::truth-eval truth1 (node-cut-truthenv data1 size1 0 cutsdb bitarr) 4))))))
    ;; :hints ((acl2::use-termhint
    ;;          (b* (((mv ?updatedp cutsdb) (node-merge-cuts-aux cut0 neg0 cut1 neg1 cutsdb)))
    ;;            `'(:use ((:instance truth-value-of-node-reduce-new-cut
    ;;                      (cutsdb ,(hq cutsdb))))
    ;;               :in-theory (disable truth-value-of-node-reduce-new-cut)))))
    )

  
  (defretd node-merge-cuts-last-index
    (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb)
                  (< (cut-fix cut0) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (< (cut-fix cut1) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (equal (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)
                    (if updatedp
                        (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                   new-cutsdb)
                      (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))))))




  

(define node-merge-cut-sets1 ((cut0 cutp$)
                              (neg0 bitp)
                              (cut0-max cutp$)
                              (cut1 cutp$)
                              (neg1 bitp)
                              (node-cuts-start cutp$)
                              (cutsdb cutsdb-ok)
                              (count natp)
                              (config cuts4-config-p))
  :guard (and (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut0 cut0-max)
              (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (not (equal 0 (cut-nnodes cutsdb))))
  :measure (cut-measure cut0 (cut-fix cut0-max) cutsdb)
  :returns (mv (new-count natp :rule-classes :type-prescription)
               new-cutsdb)
  ;; :guard-debug t
  :prepwork ((local (in-theory (disable cut-next$-updater-independence
                                        cut-base-index-when-cutp))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable cut-next$-updater-independence
                                          cut-base-index-when-cutp))))

  (b* ((cut0 (cut-fix cut0))
       (cut1 (cut-fix cut1))
       (cut0-max (cut-fix cut0-max))
       ((when (or (mbe :logic (or (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cut0-max)
                                  (zp (- (nfix cut0-max) cut0)))
                       :exec (eql cut0-max cut0))
                  (eql (lnfix count) (cuts4-config->max-cuts config))))
        (mv (lnfix count) cutsdb))
       (next (cut-next$ cut0 cutsdb)) ;; (+ 2 cut0 (cut-datai cut0 cutsdb)))
       ((mv updatedp cutsdb) (node-merge-cuts cut0 neg0 cut1 neg1 node-cuts-start cutsdb)))
    (node-merge-cut-sets1 next neg0 cut0-max cut1 neg1 node-cuts-start cutsdb
                          (+ (if updatedp 1 0) (lnfix count))
                          config))
  ///
  

  
  (defret nth-of-node-merge-cut-sets1
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-cut-sets1
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-merge-cut-sets1
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret cut-data-length-nondecreasing-of-node-merge-cut-sets1
    (<= (cut-data-length cutsdb) (cut-data-length new-cutsdb))
    :rule-classes :linear)

  ;; (set-stobj-updater node-merge-cut-sets1 5)

  (defret next-cut-of-node-merge-cut-sets1
    (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
        (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
    :rule-classes :linear)

  (defret cutsdb-ok-of-node-merge-cut-sets1
    (b* ((cut0 (cut-base-index cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (cut0-max (cut-base-index cut0-max cutsdb)))
      (implies (and (cutsdb-ok cutsdb)
                    (not (equal 0 (cut-nnodes cutsdb)))
                    ;; (equal cut0 )
                    ;; (equal cut1 (cut-base-index cut1 cutsdb))
                    ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                    (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut0 cut0-max)
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cutsdb-ok new-cutsdb))))

  (defret cutsdb-lit-idsp-of-node-merge-cut-sets1
    (b* ((cut0 (cut-base-index cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (cut0-max (cut-base-index cut0-max cutsdb)))
      (implies (and (cutsdb-lit-idsp aignet cutsdb)
                    (cutsdb-ok cutsdb)
                    (not (equal 0 (cut-nnodes cutsdb)))
                    ;; (equal cut0 )
                    ;; (equal cut1 (cut-base-index cut1 cutsdb))
                    ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                    (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut0 cut0-max)
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (cutsdb-lit-idsp aignet new-cutsdb))))

  (defret node-merge-cut-sets1-of-cut-base-index-0
    (equal (let ((cut0 (cut-fix cut0))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut0) <call>)))))

  (defret node-merge-cut-sets1-of-cut-base-index-0-max
    (equal (let ((cut0-max (cut-fix cut0-max))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut0-max) <call>)))))

  (defret node-merge-cut-sets1-of-cut-base-index-1
    (equal (let ((cut1 (cut-fix cut1))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut1) <call>))))))



(define node-merge-cut-sets ((cut0 cutp$)
                             (neg0 bitp)
                             (cut0-max cutp$)
                             (cut1 cutp$)
                             (neg1 bitp)
                             (cut1-max cutp$)
                             (node-cuts-start cutp$)
                             (cutsdb cutsdb-ok)
                             (count natp)
                             (config cuts4-config-p))
  :guard (and (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut1-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= node-cuts-start (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
              (<= cut0 cut0-max)
              (<= cut1 cut1-max)
              (not (equal 0 (cut-nnodes cutsdb))))
  :measure (cut-measure cut1 (cut-fix cut1-max) cutsdb)
  :returns (mv (new-count natp :rule-classes :type-prescription)
               new-cutsdb)
  :prepwork ((local (in-theory (disable cut-next$-updater-independence
                                        cut-base-index-when-cutp))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable cut-next$-updater-independence
                                          cut-base-index-when-cutp))))
  (b* ((cut1 (cut-fix cut1))
       (cut1-max (cut-fix cut1-max))
       (cut0 (cut-fix cut0))
       (cut0-max (cut-fix cut0-max))
       ((when (mbe :logic (or (< (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cut1-max)
                              (zp (- (nfix cut1-max) cut1)))
                   :exec (eql cut1-max cut1)))
        (mv (lnfix count) cutsdb))
       (next (cut-next$ cut1 cutsdb))
       ((mv count cutsdb) (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 node-cuts-start cutsdb count config)))
    (node-merge-cut-sets cut0 neg0 cut0-max next neg1 cut1-max node-cuts-start cutsdb count config))
  ///
  

  
  (defret nth-of-node-merge-cut-sets
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-merge-cut-sets
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-merge-cut-sets
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater node-merge-cut-sets 6)

  (defret next-cut-of-node-merge-cut-sets
    (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
        (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
    :rule-classes :linear)

  (defret cutsdb-ok-of-node-merge-cut-sets
    (b* ((cut0 (cut-base-index cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (cut0-max (cut-base-index cut0-max cutsdb))
         (cut1-max (cut-base-index cut1-max cutsdb)))
      (implies (and (cutsdb-ok cutsdb)
                    (not (equal 0 (cut-nnodes cutsdb)))
                    ;; (equal cut0 (cut-base-index cut0 cutsdb))
                    ;; (equal cut1 (cut-base-index cut1 cutsdb))
                    ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                    ;; (equal cut1-max (cut-base-index cut1-max cutsdb))
                    (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut0 cut0-max)
                    (<= cut1-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut1 cut1-max))
               (cutsdb-ok new-cutsdb)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (e/d (cut-next$-updater-independence
                                      cut-base-index-when-cutp)
                             ((:d node-merge-cut-sets))))))

  (defret cutsdb-lit-idsp-of-node-merge-cut-sets
    (b* ((cut0 (cut-base-index cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb))
         (cut0-max (cut-base-index cut0-max cutsdb))
         (cut1-max (cut-base-index cut1-max cutsdb)))
      (implies (and (cutsdb-lit-idsp aignet cutsdb)
                    (cutsdb-ok cutsdb)
                    (not (equal 0 (cut-nnodes cutsdb)))
                    ;; (equal cut0 (cut-base-index cut0 cutsdb))
                    ;; (equal cut1 (cut-base-index cut1 cutsdb))
                    ;; (equal cut0-max (cut-base-index cut0-max cutsdb))
                    ;; (equal cut1-max (cut-base-index cut1-max cutsdb))
                    (<= cut0-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut0 cut0-max)
                    (<= cut1-max (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (<= cut1 cut1-max))
               (cutsdb-lit-idsp aignet new-cutsdb)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (e/d (cut-next$-updater-independence
                                      cut-base-index-when-cutp)
                             ((:d node-merge-cut-sets))))))

  (defret node-merge-cut-sets-of-cut-base-index-0
    (equal (let ((cut0 (cut-fix cut0))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut0) <call>)))))

  (defret node-merge-cut-sets-of-cut-base-index-0-max
    (equal (let ((cut0-max (cut-fix cut0-max))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut0-max) <call>)))))

  (defret node-merge-cut-sets-of-cut-base-index-1
    (equal (let ((cut1 (cut-fix cut1))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut1) <call>)))))

  (defret node-merge-cut-sets-of-cut-base-index-1-max
    (equal (let ((cut1-max (cut-fix cut1-max))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (cut1-max) <call>))))))


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



(define cut-value ((cut natp)
                   (cutsdb)
                   (bitarr))
  :verify-guards nil
  (b* ((cut (cut-fix cut))
       (cut-size (cut-datai cut cutsdb))
       (cut-truth (cut-datai (1+ (lnfix cut)) cutsdb))
       (data (+ 2 (lnfix cut)))
       (truthenv (node-cut-truthenv data cut-size 0 cutsdb bitarr)))
    (truth::truth-eval4 cut-truth truthenv))
  ///
  (def-updater-independence-thm cut-value-updater-independence
    (implies (and (equal old-next (cut-next$ cut old))
                  (equal (cut-next$ cut new) old-next)
                  (stobjs::range-nat-equiv 0 old-next
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (equal (cut-value cut new bitarr)
                    (cut-value cut old bitarr)))
    :hints(("goal" :in-theory (enable cut-next$-base-index-lower-bound))))

  ;; (defret cut-value-of-node-merge-and-reduce-cuts
  ;;   (b* ((cut0 (cut-base-index cut0 cutsdb))
  ;;        (cut1 (cut-base-index cut1 cutsdb)))
  ;;     (implies (and updatedp
  ;;                   (cutsdb-ok cutsdb)
  ;;                   (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  ;;                   (< (+ 6 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (cut-data-length cutsdb)))
  ;;              (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
  ;;                     (and (xor (cut-value cut0 cutsdb bitarr)
  ;;                               (acl2::bit->bool neg0))
  ;;                          (xor (cut-value cut1 cutsdb bitarr)
  ;;                               (acl2::bit->bool neg1))))))
  ;;   :fn node-merge-and-reduce-cuts)

  (defret cut-value-of-node-merge-cuts
    (b* ((cut0 (cut-base-index cut0 cutsdb))
         (cut1 (cut-base-index cut1 cutsdb)))
      (implies (and updatedp
                    (cutsdb-ok cutsdb)
                    (< cut0 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                    (< cut1 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
               (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
                      (cut-and (cut-value cut0 cutsdb bitarr)
                               neg0
                               (cut-value cut1 cutsdb bitarr)
                               neg1))))
    :hints(("Goal" :in-theory (enable cut-and)))
    :fn node-merge-cuts)

  

  (defthm cut-value-of-cut-base-index
    (implies (and (equal m (cut-base-index n cutsdb))
                  (bind-free
                   (let ((mm (case-match m
                               (('cut-base-index mm &) mm)
                               (('nfix mm) mm)
                               (& m))))
                     (and (not (equal mm n))
                          `((mm . ,mm))))
                   (mm))
                  (equal (cut-base-index mm cutsdb) m))
             (equal (cut-value n cutsdb bitarr)
                    (cut-value mm cutsdb bitarr)))))


(define cuts-consistent ((cut natp)
                         (max natp)
                         (value booleanp)
                         (cutsdb)
                         (bitarr))
  :verify-guards nil
  :measure (cut-measure cut (cut-fix max) cutsdb)
  (b* ((cut (cut-fix cut))
       (max (cut-fix max))
       ((when (mbe :logic (zp (- max cut))
                   :exec (eql max cut)))
        t))
    (and (iff* (cut-value cut cutsdb bitarr) value)
         (cuts-consistent (cut-next$ cut cutsdb) max value cutsdb bitarr)))
  ///


  (def-updater-independence-thm cuts-consistent-updater-independence
    (implies (and (equal max-fix (cut-fix max old))
                  (equal (cut-fix max new) max-fix)
                  (equal (cut-fix cut new) (cut-fix cut old))
                  (stobjs::range-nat-equiv 0 max-fix
                                       (nth *cut-datai1* new)
                                       (nth *cut-datai1* old)))
             (equal (cuts-consistent cut max value new bitarr)
                    (cuts-consistent cut max value old bitarr)))
    :hints (("goal" :induct (cuts-consistent cut max value new bitarr)
             :in-theory (disable (:d cuts-consistent))
             :expand ((:free (value new) (cuts-consistent cut max value new bitarr))))))

  (defthm cuts-consistent-of-cut-base-index-1
    (implies (equal (cut-base-index a cutsdb1) (cut-base-index a cutsdb))
             (equal (cuts-consistent (cut-base-index a cutsdb1) b val cutsdb bitarr)
                    (cuts-consistent a b val cutsdb bitarr)))
    :hints (("goal" :Expand ((cuts-consistent (cut-base-index a cutsdb) b val cutsdb bitarr)
                             (cuts-consistent a b val cutsdb bitarr)))))

  

  (defthm cuts-consistent-of-cut-base-index-2
    (implies (equal (cut-base-index b cutsdb1) (cut-base-index b cutsdb))
             (equal (cuts-consistent a (cut-base-index b cutsdb1) val cutsdb bitarr)
                    (cuts-consistent a b val cutsdb bitarr)))
    :hints (("goal" :Expand ((cuts-consistent a (cut-base-index b cutsdb) val cutsdb bitarr)
                             (cuts-consistent a b val cutsdb bitarr)))))

  (local (defthm cuts-consistent-preserved-by-node-merge-cuts
           (b* ((cut0-next (cut-next$ cut0 cutsdb))
                (cut0 (cut-fix cut0))
                (cut0-max (cut-fix cut0-max))
                (cut1 (cut-fix cut1))
                (last (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (implies (and (< cut0 cut0-max)
                           (<= cut0-max last)
                           (< cut1 last)
                           (not (equal 0 (cut-nnodes cutsdb)))
                           (cutsdb-ok cutsdb))
                      (iff (cuts-consistent cut0-next cut0-max val0
                                            (mv-nth 1 (node-merge-cuts cut0 neg0 cut1 neg1 node-cuts-start cutsdb))
                                            bitarr)
                           (cuts-consistent cut0-next cut0-max val0
                                            cutsdb
                                            bitarr))))
           :hints(("Goal" :in-theory (disable cuts-consistent)))))

  (local (defthm cuts-consistent-preserved-by-node-merge-cut-sets1-0
           (b* ((cut0 (cut-fix cut0))
                (cut0-max (cut-fix cut0-max))
                (cut1 (cut-fix cut1))
                (last (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (implies (and (<= cut0 cut0-max)
                           (<= cut0-max last)
                           (< cut1 last)
                           (not (equal 0 (cut-nnodes cutsdb)))
                           (cutsdb-ok cutsdb))
                      (iff (cuts-consistent cut0 cut0-max val0
                                            (mv-nth 1 (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 node-cuts-start cutsdb count config))
                                            bitarr)
                           (cuts-consistent cut0 cut0-max val0
                                            cutsdb
                                            bitarr))))
           :hints(("Goal" :in-theory (disable cuts-consistent
                                              cuts-consistent-updater-independence))
                  (acl2::use-termhint
                   (b* ((cut0 (cut-fix cut0))
                        (cut0-max (cut-fix cut0-max))
                        (cut1 (cut-fix cut1)))
                   
                     `'(:use ((:instance cuts-consistent-updater-independence
                               (new ,(hq (mv-nth 1 (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 node-cuts-start cutsdb count config))))
                               (old cutsdb)
                               (cut ,(hq cut0))
                               (max ,(hq cut0-max))
                               (max-fix ,(hq cut0-max))
                               (value val0)))))))))

  (local (defthm cuts-consistent-preserved-by-node-merge-cut-sets1-1
           (b* ((cut0 (cut-fix cut0))
                (cut0-max (cut-fix cut0-max))
                (cut1-next (cut-next$ cut1 cutsdb))
                (cut1 (cut-fix cut1))
                (cut1-max (cut-fix cut1-max))
                (last (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)))
             (implies (and (<= cut0 cut0-max)
                           (<= cut0-max last)
                           (< cut1 cut1-max)
                           (<= cut1-max last)
                           (not (equal 0 (cut-nnodes cutsdb)))
                           (cutsdb-ok cutsdb))
                      (iff (cuts-consistent cut1-next cut1-max val0
                                            (mv-nth 1 (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 node-cuts-start cutsdb count config))
                                            bitarr)
                           (cuts-consistent cut1-next cut1-max val0
                                            cutsdb
                                            bitarr))))
           :hints(("Goal" :in-theory (disable cuts-consistent
                                              cuts-consistent-updater-independence))
                  (acl2::use-termhint
                   (b* ((cut0 (cut-fix cut0))
                        (cut0-max (cut-fix cut0-max))
                        (cut1-next (cut-next$ cut1 cutsdb))
                        (cut1 (cut-fix cut1))
                        (cut1-max (cut-fix cut1-max)))
                   
                     `'(:use ((:instance cuts-consistent-updater-independence
                               (new ,(hq (mv-nth 1 (node-merge-cut-sets1 cut0 neg0 cut0-max cut1 neg1 node-cuts-start cutsdb count config))))
                               (old cutsdb)
                               (cut ,(hq cut1-next))
                               (max ,(hq cut1-max))
                               (max-fix ,(hq cut1-max))
                               (value val0)))))))))

  (local (in-theory (disable cutsdb-ok-of-node-merge-cut-sets1
                             cutsdb-ok-of-node-merge-cut-sets
                             cuts-consistent-updater-independence
                             cutsdb-cut-ok-implies-cut-next$-less-than-length
                             cut-base-index-updater-independence
                             acl2::nfix-equal-to-nonzero)))

  (defthm cuts-consistent-compose
    (implies (and (cuts-consistent b c val cutsdb bitarr)
                  (cuts-consistent a b val cutsdb bitarr)
                  (<= (nfix a) (nfix b))
                  (<= (nfix b) (nfix c)))
             (cuts-consistent a c val cutsdb bitarr))
    :hints (("goal" :induct (cuts-consistent a b val cutsdb bitarr)
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

  (local (defret cuts-consistent-of-node-merge-cut-sets1-lemma
           (b* ((min (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                (max (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
                (cut0 (cut-fix cut0))
                (cut0-max (cut-fix cut0-max))
                (cut1 (cut-fix cut1)))
             (implies (and (cuts-consistent cut0 cut0-max val0 cutsdb bitarr)
                           (iff* val1 (cut-value cut1 cutsdb bitarr))
                           (cutsdb-ok cutsdb)
                           (<= cut0 cut0-max)
                           (<= cut0-max min)
                           (< cut1 min)
                           (not (equal 0 (cut-nnodes cutsdb)))
                           (iff* val (cut-and val0 neg0 val1 neg1)))
                      (cuts-consistent min max
                                       val
                                       new-cutsdb
                                       bitarr)))
           :hints (("goal" :induct <call>
                    :in-theory (e/d ((:i node-merge-cut-sets1)
                                     node-merge-cuts-last-index)
                                    ((:d cuts-consistent)))
                    :expand (<call>))
                   (acl2::use-termhint
                    (b* ((new new-cutsdb)
                         (min (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                         (max (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)))
                      `'(:expand ((cuts-consistent ,(hq cut0) ,(hq cut0-max)
                                                   ,(hq val0) ,(hq cutsdb) ,(hq bitarr))
                                  (cuts-consistent ,(hq min) ,(hq max)
                                                   ,(hq val)
                                                   ,(hq new) ,(hq bitarr))))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (cutsdb-ok-of-node-merge-cut-sets1)
                                          (cuts-consistent)))))
           :rule-classes nil
           :fn node-merge-cut-sets1))

  (defret cuts-consistent-of-node-merge-cut-sets1
    (b* ((min (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
         (max (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb)))
      (implies (and ;; (iff* val )
                    (equal cut0-fix (cut-fix cut0))
                    (equal cut0-max-fix (cut-fix cut0-max))
                    (cuts-consistent cut0-fix cut0-max-fix val0 cutsdb bitarr)
                    (equal cut1-fix (cut-fix cut1))
                    (iff* val1 (cut-value cut1-fix cutsdb bitarr))
                    (cutsdb-ok cutsdb)
                    (<= cut0-fix cut0-max-fix)
                    (<= cut0-max-fix min)
                    (< cut1-fix min)
                    (not (equal 0 (cut-nnodes cutsdb))))
               (cuts-consistent min max
                                (cut-and val0 neg0 val1 neg1);; val
                                new-cutsdb
                                bitarr)))
    :hints (("goal" :use ((:instance cuts-consistent-of-node-merge-cut-sets1-lemma
                           (val (cut-and val0 neg0 val1 neg1))))
             :in-theory nil))
    :fn node-merge-cut-sets1)
                  
  

  (defret next-cut-of-node-merge-cut-sets-special
    (implies (equal (cut-nnodes cutsdb) (cut-nnodes cutsdb1))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)))
    :rule-classes :linear
    :fn node-merge-cut-sets)

  (defthm cut-base-index-of-cut-base-index
    (equal (cut-base-index (cut-base-index cut cutsdb) cutsdb)
           (cut-base-index cut cutsdb)))

  (defret cuts-consistent-of-node-merge-cut-sets
    (b* ((min (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb))
         (max (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb))
         (cut0 (cut-fix cut0))
         (cut0-max (cut-fix cut0-max))
         (cut1 (cut-fix cut1))
         (cut1-max (cut-fix cut1-max)))
      (implies (and ;; (iff* val )
                    (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                    (cuts-consistent cut0 cut0-max val0 cutsdb bitarr)
                    (cuts-consistent cut1 cut1-max val1 cutsdb bitarr)
                    (cutsdb-ok cutsdb)
                    (<= cut0 cut0-max)
                    (<= cut0-max min)
                    (<= cut1 cut1-max)
                    (<= cut1-max min)
                    (not (equal 0 (cut-nnodes cutsdb))))
               (cuts-consistent min max
                                (cut-and val0 neg0 val1 neg1) ;; val
                                new-cutsdb
                                bitarr)))
    :hints (("goal" :induct <call>
             :in-theory (e/d ((:i node-merge-cut-sets)
                              node-merge-cuts-last-index)
                             ((:d cuts-consistent)))
             :expand (<call>
                      (cuts-consistent cut1 cut1-max val1 cutsdb bitarr)))
            ;; (acl2::use-termhint
            ;;  `'(:expand ((cuts-consistent ,(hq cut1) ,(hq cut1-max)
            ;;                                 ,(hq val1) ,(hq cutsdb) ,(hq bitarr))
            ;;                ;; (cuts-consistent ,(hq min) ,(hq max)
            ;;                ;;                  ,(hq (cut-and val0 neg0 val1 neg1))
            ;;                ;;                  ,(hq new) ,(hq bitarr))
            ;;                )))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (cutsdb-ok-of-node-merge-cut-sets1
                                    cuts-consistent-updater-independence)
                                   (cuts-consistent)))))
    :fn node-merge-cut-sets)

  (defthmd cuts-consistent-implies-cut-value
    (implies (and (cuts-consistent n max value cutsdb bitarr)
                  (<= (cut-fix n) (cut-fix cut))
                  (< (cut-fix cut) (cut-fix max)))
             (iff (cut-value cut cutsdb bitarr) value))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal (cut-base-index n cutsdb)
                                  (cut-base-index cut cutsdb))))))))
                  


(define node-add-const0-cut ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  (b* ((node (cut-nnodes cutsdb))
       (cut (nodecut-indicesi node cutsdb))
       (cutsdb (cuts-maybe-grow-cut-data (+ 2 cut) cutsdb))
       (size 0)
       (truth 0)
       (cutsdb (update-cut-datai cut size cutsdb))
       (cutsdb (update-cut-datai (+ 1 cut) truth cutsdb)))
    (update-nodecut-indicesi$ node (+ 2 cut) cutsdb))
  ///
  (defret nth-of-node-add-const0-cut
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-nodecut-indices-of-node-add-const0-cut
    (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret nth-cut-data-of-node-add-const0-cut
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  ;; (set-stobj-updater node-add-const0-cut 0)

  (local (defthm cut-next$-of-update-cut-data
           (implies (cutp n cutsdb)
                    (equal (cut-next$ n (update-cut-datai n v cutsdb))
                           (+ 2 (nfix n) (nfix v))))
           :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
                                          (rewrite-to-cut-next$))))))

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
    :hints (("goal" :expand ((:free (cdb) (cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cdb)))
             :in-theory (enable cutsdb-data-nodes-sorted
                                cutsdb-data-nodes-bounded
                                cutsdb-cut-bounded
                                truth4-deps-bounded))))

  (local
   (defthm cutsdb-lit-idsp-of-add-node-free
     (implies (and (cutsdb-lit-idsp aignet cutsdb)
                   (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                   (equal next (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb))
                   (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
                   (cutsdb-ok cutsdb))
              (cutsdb-lit-idsp aignet (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                               next
                                                               cutsdb)))))

  (defret cutsdb-lit-idsp-of-node-add-const0-cut
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb))))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints (("goal" :expand ((:free (cdb) (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cdb))
                             (:free (n) (cutsdb-data-nodes-lit-idsp n 0 aignet cutsdb))))))

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

  (defret cut-data-length-of-node-add-const0-cut
    (<= (cut-data-length cutsdb)
        (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-next$-of-node-add-const0-cut
    (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (equal (nodecut-indicesi (cut-nnodes cutsdb) cutsdb2)
                         (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (cutsdb-ok cutsdb))
             (equal (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb2)
                               new-cutsdb)
                    (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))))

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
    :hints(("Goal" :in-theory (e/d ()
                                   (node-add-const0-cut))
            :expand ((:free (max val)
                      (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       max val new-cutsdb bitarr)))))))

(define node-add-trivial-cut ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  :guard (not (equal 0 (cut-nnodes cutsdb)))
  (b* ((node (cut-nnodes cutsdb))
       (cut (nodecut-indicesi node cutsdb))
       (cutsdb (cuts-maybe-grow-cut-data (+ 3 cut) cutsdb))
       (size 1)
       (truth (truth::var4 0))
       (cutsdb (update-cut-datai cut size cutsdb))
       (cutsdb (update-cut-datai (+ 1 cut) truth cutsdb))
       (cutsdb (update-cut-datai$ (+ 2 cut) (1- node) cutsdb)))
    (update-nodecut-indicesi$ node (+ 3 cut) cutsdb))
  ///
  (defret nth-of-node-add-trivial-cut
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-nodecut-indices-of-node-add-trivial-cut
    (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret nth-cut-data-of-node-add-trivial-cut
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  ;; (set-stobj-updater node-add-trivial-cut 0)

  (local (defthm cut-next$-of-update-cut-data
           (implies (cutp n cutsdb)
                    (equal (cut-next$ n (update-cut-datai n v cutsdb))
                           (+ 2 (nfix n) (nfix v))))
           :hints(("Goal" :in-theory (e/d (cut-next$ cut-next)
                                          (rewrite-to-cut-next$))))))

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
    :hints (("goal" :expand ((:free (cdb) (cutsdb-cut-ok (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cdb)))
             :in-theory (enable cutsdb-data-nodes-sorted
                                cutsdb-cut-bounded
                                cutsdb-data-nodes-bounded
                                truth4-deps-bounded))))

  

  (local
   (defthm cutsdb-lit-idsp-of-add-node-free
     (implies (and (cutsdb-lit-idsp aignet cutsdb)
                   (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                   (equal next (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb))
                   (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cutsdb)
                   (cutsdb-ok cutsdb))
              (cutsdb-lit-idsp aignet (update-nodecut-indicesi (cut-nnodes cutsdb1)
                                                               next
                                                               cutsdb)))))

  (defret cutsdb-lit-idsp-of-node-add-trivial-cut
    (implies (and (cutsdb-lit-idsp aignet cutsdb)
                  (cutsdb-ok cutsdb)
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (aignet-idp (+ -1 (cut-nnodes cutsdb)) aignet)
                  (not (equal (ctype (stype (car (lookup-id (+ -1 (cut-nnodes cutsdb)) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints (("goal" :expand ((:free (cdb) (cutsdb-cut-lit-idsp (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) aignet cdb))
                             (:free (n cutsdb) (cutsdb-data-nodes-lit-idsp n 1 aignet cutsdb))
                             (:free (n cutsdb) (cutsdb-data-nodes-lit-idsp n 0 aignet cutsdb))))))

  (local (defthm truth-eval-of-consts
           (and (equal (truth::truth-eval 0 env 4) nil)
                (equal (truth::truth-eval -1 env 4) t))
           :hints(("Goal" :in-theory (enable truth::Truth-eval)))))

  (defret cut-value-of-node-add-trivial-cut
    (implies (cutsdb-ok cutsdb)
             (equal (cut-value (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) new-cutsdb bitarr)
                    (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))))
    :hints(("Goal" :in-theory (e/d (cut-and cut-value)
                                   ((truth::var) (truth::var4))))))

  (defret next-cut-of-node-add-trivial-cut
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (cut-nnodes cutsdb1) new-cutsdb)))
    :rule-classes :linear)

  (defret cut-data-length-of-node-add-trivial-cut
    (<= (cut-data-length cutsdb)
        (cut-data-length new-cutsdb))
    :rule-classes :linear)

  (defret cut-next$-of-node-add-trivial-cut
    (implies (and (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb))
             (equal (cut-next$ (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
                               new-cutsdb)
                    (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))))

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
    :hints(("Goal" :in-theory (e/d ()
                                   (node-add-trivial-cut))
            :expand ((:free (max val)
                      (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                                       max val new-cutsdb bitarr)))))))

;; (define node-add-trivial-and-cut ((child0 litp)
;;                                   (child1 litp)
;;                                   (cutsdb cutsdb-ok))
;;   ;; :guard (< (+ 4 (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)) (cut-data-length cutsdb))
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
;;                (cutsdb (cuts-maybe-grow-cut-data (+ 5 cut) cutsdb))
;;                (cutsdb (update-cut-datai cut size cutsdb))
;;                (cutsdb (update-cut-datai (+ 1 cut) truth cutsdb))
;;                (cutsdb (update-cut-datai$ (+ 2 cut) (lit-id child0) cutsdb)))
;;             (update-nodecut-indicesi$ node (+ 3 cut) cutsdb))))
;;        (cutsdb (cuts-maybe-grow-cut-data (+ 5 cut) cutsdb))
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
;;        (cutsdb (update-cut-datai cut size cutsdb))
;;        (cutsdb (update-cut-datai (+ 1 cut) truth cutsdb))
;;        (cutsdb (update-cut-datai$ (+ 2 cut) (lit-id child0) cutsdb))
;;        (cutsdb (update-cut-datai$ (+ 3 cut) (lit-id child1) cutsdb)))
;;     (update-nodecut-indicesi$ node (+ 4 cut) cutsdb))
;;   ///
;;   (defret nth-of-node-add-trivial-and-cut
;;     (implies (and (not (equal (nfix n) *cut-datai1*))
;;                   (not (equal (nfix n) *nodecut-indicesi1*)))
;;              (equal (nth n new-cutsdb)
;;                     (nth n cutsdb))))

;;   (defret nth-nodecut-indices-of-node-add-trivial-and-cut
;;     (implies (not (equal (nfix n) (cut-nnodes cutsdb)))
;;              (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
;;                     (nth n (nth *nodecut-indicesi1* cutsdb)))))

;;   (defret nth-cut-data-of-node-add-trivial-and-cut
;;     (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
;;              (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
;;                         (nth n (nth *cut-datai1* cutsdb)))))

;;   (set-stobj-updater node-add-trivial-and-cut 2)

;;   (local (defthm cut-next$-of-update-cut-data
;;            (implies (cutp n cutsdb)
;;                     (equal (cut-next$ n (update-cut-datai n v cutsdb))
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
;;              :in-theory (enable cutsdb-data-nodes-sorted
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

;;   (defret cut-data-length-of-node-add-trivial-and-cut
;;     (<= (cut-data-length cutsdb)
;;         (cut-data-length new-cutsdb))
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





(define node-derive-cuts-aux ((child0 litp)
                              (child1 litp)
                              (cutsdb cutsdb-ok)
                              (config cuts4-config-p))
  :guard (and (< (lit-id child0) (cut-nnodes cutsdb))
              (< (lit-id child1) (cut-nnodes cutsdb)))
  :returns (mv (new-count natp :rule-classes :type-prescription) new-cutsdb)
  (b* ((node0 (lit-id child0))
       (node1 (lit-id child1))
       (neg0 (lit-neg child0))
       (neg1 (lit-neg child1))
       (cut0-min (nodecut-indicesi node0 cutsdb))
       (cut0-max (nodecut-indicesi (+ 1 node0) cutsdb))
       (cut1-min (nodecut-indicesi node1 cutsdb))
       (cut1-max (nodecut-indicesi (+ 1 node1) cutsdb))
       (node-cuts-start (nodecut-indicesi (1- (cut-nnodes cutsdb)) cutsdb))
       ((mv count cutsdb)
        (node-merge-cut-sets cut0-min neg0 cut0-max cut1-min neg1 cut1-max
                             node-cuts-start cutsdb 0 config))
       (cutsdb (node-add-trivial-cut cutsdb)))
    (mv (+ 1 count) cutsdb))
  ///
  

  
  (defret nth-of-node-derive-cuts-aux
    (implies (and (not (equal (nfix n) *cut-datai1*))
                  (not (equal (nfix n) *nodecut-indicesi1*)))
             (equal (nth n new-cutsdb)
                    (nth n cutsdb))))

  (defret nth-cut-data-of-node-derive-cuts-aux
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts-aux
    (implies (< (nfix n) (cut-nnodes cutsdb))
             (equal (nth n (nth *nodecut-indicesi1* new-cutsdb))
                    (nth n (nth *nodecut-indicesi1* cutsdb)))))

  ;; (set-stobj-updater node-derive-cuts-aux 2)

  (defret next-cut-of-node-derive-cuts-aux
    (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
        (nodecut-indicesi (cut-nnodes cutsdb) new-cutsdb))
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

  (local (in-theory (disable CUT-BASE-INDEX-UPDATER-INDEPENDENCE
                             ;; cutsdb-ok-of-node-merge-cut-sets
                             cuts-consistent-updater-independence
                             nodecut-indicesi-updater-independence 
                             cut-base-index-lte-target-idx)))

  (defret cuts-consistent-of-node-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
                  (not (equal 0 (cut-nnodes cutsdb)))
                  (cuts-consistent (nodecut-indicesi (lit-id child0) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child0)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                   cutsdb bitarr)
                  (cuts-consistent (nodecut-indicesi (lit-id child1) cutsdb)
                                   (nodecut-indicesi (+ 1 (lit-id child1)) cutsdb)
                                   (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                   cutsdb bitarr)
                  (iff* val (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                     (lit-neg child0)
                                     (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                     (lit-neg child1)))
                  (iff* val (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr)))
                  (< (+ 1 (lit-id child0)) (cut-nnodes cutsdb))
                  (< (+ 1 (lit-id child1)) (cut-nnodes cutsdb)))
             (cuts-consistent (nodecut-indicesi (cut-nnodes cutsdb1) cutsdb)
                              (nodecut-indicesi
                               (cut-nnodes cutsdb1)
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
                  ((mv & second-cutsdb)
                   (node-merge-cut-sets cut0-min neg0 cut0-max cut1-min neg1 cut1-max
                                        node-cuts-start cutsdb 0 config)))
               `'(:use ((:instance cuts-consistent-of-node-merge-cut-sets
                         (cut0 ,(hq cut0-min)) (neg0 ,(hq neg0)) (cut0-max ,(hq cut0-max))
                         (cut1 ,(hq cut1-min)) (neg1 ,(hq neg1)) (cut1-max ,(hq cut1-max))
                         (node-cuts-start ,(hq node-cuts-start))
                         (cutsdb ,(hq cutsdb)) (count ,(hq 0)) (config ,(hq config))
                         (val0 ,(hq (acl2::bit->bool (get-bit node0 bitarr))))
                         (val1 ,(hq (acl2::bit->bool (get-bit node1 bitarr)))))
                        (:instance cuts-consistent-of-node-add-trivial-cut
                         (cutsdb1 ,(hq second-cutsdb))
                         (cutsdb ,(hq second-cutsdb))
                         (val ,(hq (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))))))
                  :in-theory (disable cuts-consistent-of-node-merge-cut-sets
                                      cuts-consistent-of-node-add-trivial-cut))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (cuts-consistent-updater-independence)
                                   (cuts-consistent-of-node-merge-cut-sets
                                    cuts-consistent-of-node-add-trivial-cut)))))))

(define node-derive-cuts ((child0 litp)
                          (child1 litp)
                          (cutsdb cutsdb-ok)
                          (config cuts4-config-p))
  :guard (and (< (lit-id child0) (cut-nnodes cutsdb))
              (< (lit-id child1) (cut-nnodes cutsdb)))
  :returns (mv (count natp :rule-classes :type-prescription) new-cutsdb)
  (b* ((cutsdb (cuts-add-node cutsdb)))
    (node-derive-cuts-aux child0 child1 cutsdb config))
  ///
  
  (defret cut-nnodes-of-node-derive-cuts
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-data-of-node-derive-cuts
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

  (defret nth-nodecut-indices-of-node-derive-cuts
    (implies (<= (nfix n) (cut-nnodes cutsdb))
             (nat-equiv (nth n (nth *nodecut-indicesi1* new-cutsdb))
                        (nth n (nth *nodecut-indicesi1* cutsdb)))))

  (defret next-nodecut-index-of-node-derive-cuts
    (implies (equal (cut-nnodes cutsdb1) (cut-nnodes cutsdb))
             (<= (nodecut-indicesi (cut-nnodes cutsdb) cutsdb)
                 (nodecut-indicesi (+ 1 (cut-nnodes cutsdb1)) new-cutsdb)))
    :hints (("goal" :use ((:instance next-cut-of-node-derive-cuts-aux
                           (cutsdb (cuts-add-node cutsdb))))
             :in-theory (disable next-cut-of-node-derive-cuts-aux)))
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
                  (cutsdb-lit-idsp aignet cutsdb)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb))
                  (aignet-idp (cut-nnodes cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-nnodes cutsdb) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb))))

(define node-cuts-consistent ((node natp)
                              (cutsdb cutsdb-ok)
                              (bitarr))
  :verify-guards nil
  (cuts-consistent (nodecut-indicesi node cutsdb)
                   (nodecut-indicesi (+ 1 (lnfix node)) cutsdb)
                   (acl2::bit->bool (get-bit node bitarr))
                   cutsdb bitarr)
  ///
  (defthmd node-cuts-consistent-of-node-derive-cuts-aux
    (implies (and (node-cuts-consistent (lit-id child0) cutsdb bitarr)
                  (node-cuts-consistent (lit-id child1) cutsdb bitarr)
                  (< (+ 1 (lit-id child0)) (cut-nnodes cutsdb))
                  (< (+ 1 (lit-id child1)) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb)
                  (equal (nodecut-indicesi (+ -1 (cut-nnodes cutsdb)) cutsdb)
                         (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
                  (iff* (acl2::bit->bool (get-bit (+ -1 (cut-nnodes cutsdb)) bitarr))
                        (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                 (lit-neg child0)
                                 (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                 (lit-neg child1))))
             (node-cuts-consistent
              (+ -1 (cut-nnodes cutsdb))
              (mv-nth 1 (node-derive-cuts-aux child0 child1 cutsdb config))
              bitarr)))

  (defthm node-cuts-consistent-of-node-derive-cuts
    (implies (and (node-cuts-consistent (lit-id child0) cutsdb bitarr)
                  (node-cuts-consistent (lit-id child1) cutsdb bitarr)
                  (< (lit-id child0) (cut-nnodes cutsdb))
                  (< (lit-id child1) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb)
                  (iff* (acl2::bit->bool (get-bit (cut-nnodes cutsdb) bitarr))
                        (cut-and (acl2::bit->bool (get-bit (lit-id child0) bitarr))
                                 (lit-neg child0)
                                 (acl2::bit->bool (get-bit (lit-id child1) bitarr))
                                 (lit-neg child1))))
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              (mv-nth 1 (node-derive-cuts child0 child1 cutsdb config))
              bitarr))
    :hints(("Goal" :in-theory (enable node-derive-cuts)
            :use ((:instance node-cuts-consistent-of-node-derive-cuts-aux
                   (cutsdb (cuts-add-node cutsdb)))))))

  (def-updater-independence-thm node-cuts-consistent-updater-independence
    (implies (and (equal node-idx (nodecut-indicesi node old))
                  (equal next-idx (nodecut-indicesi (+ 1 (lnfix node)) old))
                  (equal node-idx (nodecut-indicesi node new))
                  (equal next-idx (nodecut-indicesi (+ 1 (lnfix node)) new))
                  (equal next-fix (cut-fix next-idx old))
                  (equal next-fix (cut-fix next-idx new))
                  (equal (cut-fix node-idx old) (cut-fix node-idx new))
                  (stobjs::range-nat-equiv 0 next-fix (nth *cut-datai1* new) (nth *cut-datai1* old)))
             (equal (node-cuts-consistent node new bitarr)
                    (node-cuts-consistent node old bitarr))))

  (defthm node-cuts-consistent-preserved-by-node-derive-cuts
    (implies (and (node-cuts-consistent node cutsdb bitarr)
                  (< (nfix node) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb))
             (node-cuts-consistent node (mv-nth 1 (node-derive-cuts child0 child1 cutsdb config)) bitarr))
    :hints(("Goal" :in-theory (disable node-cuts-consistent))))

  (defthm node-cuts-consistent-of-cuts-add-node
    (node-cuts-consistent (cut-nnodes cutsdb)
                          (cuts-add-node cutsdb)
                          bitarr))

  (defthmd node-cuts-consistent-implies-cut-value
    (implies (and (node-cuts-consistent node cutsdb bitarr)
                  (cutsdb-ok cutsdb)
                  (<= (nodecut-indicesi node cutsdb)
                      (cut-fix cut))
                  (< (cut-fix cut) (nodecut-indicesi (+ 1 (lnfix node)) cutsdb))
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

  (defret nth-cut-data-of-node-derive-cuts-const0
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

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
                  (cutsdb-lit-idsp aignet cutsdb)
                  (aignet-idp (cut-nnodes cutsdb) aignet)
                  (not (equal (ctype (stype (car (lookup-id (cut-nnodes cutsdb) aignet)))) :output)))
             (cutsdb-lit-idsp aignet new-cutsdb))))


(define node-derive-cuts-input ((cutsdb cutsdb-ok))
  :returns (new-cutsdb)
  (b* ((cutsdb (cuts-add-node cutsdb)))
    (node-add-trivial-cut cutsdb))
  ///
  
  (defret cut-nnodes-of-node-derive-cuts-input
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-data-of-node-derive-cuts-input
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

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


  (defthm node-cuts-consistent-of-node-derive-cuts-input
    (implies (cutsdb-ok cutsdb)
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              (node-derive-cuts-input cutsdb)
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
                  (<= (nodecut-indicesi node cutsdb) (cut-fix cut))
                  (< (cut-fix cut) (nodecut-indicesi (+ 1 (nfix node)) cutsdb))
                  (< (nfix node) (cut-nnodes cutsdb))
                  (cutsdb-ok cutsdb))
             (equal (cut-value cut cutsdb bitarr)
                    (acl2::bit->bool (nth node bitarr))))
    :hints (("goal" :use node-cuts-consistent-implies-cut-value))))





(include-book "centaur/aignet/eval" :dir :system)

(define aignet-derive-cuts-node ((aignet)
                                 (cutsdb cutsdb-ok)
                                 (config cuts4-config-p))
  :returns (new-cutsdb)
  :guard (<= (cut-nnodes cutsdb) (max-fanin aignet))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* ((node (cut-nnodes cutsdb))
       (slot0 (id->slot node 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :in (node-derive-cuts-input cutsdb)
      :const (node-derive-cuts-const0 cutsdb)
      :out (cuts-add-node cutsdb)
      :gate
      (b* ((lit0 (snode->fanin slot0))
           (slot1 (id->slot node 1 aignet))
           (lit1 (snode->fanin slot1))
           ((mv & cutsdb)
            (node-derive-cuts lit0 lit1 cutsdb config)))
        cutsdb)))
  ///
  
  (defret cut-nnodes-of-aignet-derive-cuts-node
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (cut-nnodes cutsdb))))

  (defret nth-cut-data-of-aignet-derive-cuts-node
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

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
                  (<= (cut-nnodes cutsdb) (node-count aignet))
                  (cutsdb-lit-idsp aignet cutsdb))
             (cutsdb-lit-idsp aignet new-cutsdb))
    :hints(("Goal" :in-theory (enable aignet-idp))))


  (local (defthm cut-and-is-eval-and-of-lits
           (equal (cut-and (equal 1 (id-eval (lit->var lit0) invals regvals aignet))
                           (lit->neg lit0)
                           (equal 1 (id-eval (lit->var lit1) invals regvals aignet))
                           (lit->neg lit1))
                  (equal 1 (eval-and-of-lits lit0 lit1 invals regvals aignet)))
           :hints(("Goal" :in-theory (enable cut-and eval-and-of-lits lit-eval b-and)))))

  (defthm node-cuts-consistent-of-aignet-derive-cuts-node
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals aignet))
                  (<= (cut-nnodes cutsdb) (max-fanin aignet)))
             (node-cuts-consistent
              (cut-nnodes cutsdb)
              (aignet-derive-cuts-node aignet cutsdb config)
              (aignet-record-vals vals invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((id-eval (cut-nnodes cutsdb) invals regvals aignet)))))))


(define aignet-derive-cuts-aux ((aignet)
                                (cutsdb cutsdb-ok)
                                (config cuts4-config-p))
  :returns (new-cutsdb)
  :measure (nfix (- (+ 1 (max-fanin aignet)) (cut-nnodes cutsdb)))
  :guard (<= (cut-nnodes cutsdb) (+ 1 (max-fanin aignet)))
  (b* ((node (cut-nnodes cutsdb))
       ((when (mbe :logic (zp (+ 1 (max-fanin aignet) (- (nfix node))))
                   :exec (eql (+ 1 (max-fanin aignet)) node)))
        cutsdb)
       (cutsdb (aignet-derive-cuts-node aignet cutsdb config)))
    (aignet-derive-cuts-aux aignet cutsdb config))
  ///
  (defret cut-nnodes-of-aignet-derive-cuts-aux
    (implies (<= (cut-nnodes cutsdb) (+ 1 (max-fanin aignet)))
             (equal (cut-nnodes new-cutsdb)
                    (+ 1 (max-fanin aignet)))))

  (defret nth-cut-data-of-aignet-derive-cuts-aux
    (implies (< (nfix n) (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
             (nat-equiv (nth n (nth *cut-datai1* new-cutsdb))
                        (nth n (nth *cut-datai1* cutsdb)))))

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
             (cutsdb-lit-idsp aignet new-cutsdb)))

  (defthm cutsdb-consistent-of-aignet-derive-cuts-aux
    (implies (and (cutsdb-ok cutsdb)
                  (cutsdb-consistent cutsdb (aignet-record-vals vals invals regvals aignet)))
             (cutsdb-consistent
              (aignet-derive-cuts-aux aignet cutsdb config)
              (aignet-record-vals vals invals regvals aignet)))
    :hints (("goal" :induct t
             :in-theory (enable* acl2::arith-equiv-forwarding))
            (acl2::use-termhint
             (b* ((bitarr (aignet-record-vals vals invals regvals aignet))
                  (cuts (aignet-derive-cuts-node aignet cutsdb config))
                  (witness (cutsdb-consistent-witness cuts bitarr))
                  ((acl2::termhint-seq
                    `'(:expand ((cutsdb-consistent ,(hq cuts) ,(hq bitarr)))))))
               `'(:cases ((nat-equiv ,(hq witness) ,(hq (cut-nnodes cutsdb))))))))))


(define aignet-derive-cuts (aignet cutsdb (config cuts4-config-p))
  :returns (new-cutsdb)
  :verify-guards nil
  (b* ((cutsdb (update-cut-nnodes 0 cutsdb))
       (cutsdb (cuts-maybe-grow-nodecut-indices 1 cutsdb))
       (cutsdb (cuts-maybe-grow-cut-data 1 cutsdb))
       (cutsdb (update-nodecut-indicesi 0 0 cutsdb)))
    (aignet-derive-cuts-aux aignet cutsdb config))
  ///
  (local (defthm cutsdb-ok-of-empty
           (implies (and (equal (cut-nnodes cutsdb) 0)
                         (equal (nodecut-indicesi 0 cutsdb) 0)
                         (<= 1 (nodecut-indices-length cutsdb))
                         (<= 1 (cut-data-length cutsdb)))
                    (cutsdb-ok cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-ok)
                   :expand ((cutsdb-nodecuts-ok 0 cutsdb))))))

  (local (defthm cutsdb-lit-idsp-of-empty
           (implies (and (equal (cut-nnodes cutsdb) 0)
                         (equal (nodecut-indicesi 0 cutsdb) 0))
                    (cutsdb-lit-idsp aignet cutsdb))
           :hints(("Goal" :in-theory (enable cutsdb-lit-idsp)
                   :expand ((cutsdb-data-lit-idsp 0 aignet cutsdb))))))

  (local (defthm cutsdb-consistent-of-empty
           (implies (equal (cut-nnodes cutsdb) 0)
                    (cutsdb-consistent cutsdb bitarr))
           :hints (("goal" :expand ((cutsdb-consistent cutsdb bitarr))))))

  (verify-guards aignet-derive-cuts)

  (defret cutsdb-ok-of-aignet-derive-cuts
    (cutsdb-ok new-cutsdb))

  (defret cutsdb-lit-idsp-of-aignet-derive-cuts
    (cutsdb-lit-idsp aignet new-cutsdb))

  (defthm cutsdb-consistent-of-aignet-derive-cuts
    (cutsdb-consistent
     (aignet-derive-cuts aignet cutsdb config)
     (aignet-record-vals vals invals regvals aignet)))

  (defret cut-nnodes-of-aignet-derive-cuts
    (equal (cut-nnodes new-cutsdb)
           (+ 1 (max-fanin aignet)))))





(define cutsdb-count-cuts ((n cutp$) (count natp) (cutsdb cutsdb-ok))
  :guard (<= n (nodecut-indicesi (cut-nnodes cutsdb) cutsdb))
  :measure (cut-measure n (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) cutsdb)
  (b* ((n (cut-fix n))
       ((when (mbe :logic (zp (- (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix n)))
                   :exec (eql (nodecut-indicesi (cut-nnodes cutsdb) cutsdb) (nfix n))))
        (lnfix count)))
    (cutsdb-count-cuts (cut-next$ n cutsdb) (+ 1 (lnfix count)) cutsdb)))






