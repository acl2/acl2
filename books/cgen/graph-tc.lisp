#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")

(acl2::begin-book t :ttags ((:hash-stobjs) (:redef+)));$ACL2s-Preamble$|#

(in-package "DEFDATA")

(include-book "tools/bstar" :dir :system)

(include-book "add-ons/hash-stobjs" :dir :system :ttags :all) ;((:hash-stobjs) (:redef+)))
; key: type name (symbolp)
; value: vertex
;;   - vertex is the index of key into adjacency list array rgraph

(defstobj types-ht$
  (types-count :type (integer 0 *) :initially 0)
  (type-vertex-ht :type (hash-table eql)) ;symbols
  )


;; (defdata aa-tree (oneof nil 
;;                         (node (key . rational)
;;                               (level . nat)
;;                               (left . aa-tree)
;;                               (right . aa-tree))))

(include-book "library-support")

(defun aa-treep (v)
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (acl2::good-map v)
         (rationalp (mget :key v))
         (natp (mget :level v))
         (aa-treep (mget :left v))
         (aa-treep (mget :right v)))))

(defun node (key level left right)
  (declare (xargs :guard (and (rationalp key)
                              (natp level)
                              (aa-treep left)
                              (aa-treep right))))
  (mset :key key
        (mset :level level
              (mset :left left
                    (mset :right right nil)))))

;; (defthm node-sig
;;   (implies (and (rationalp key)
;;                 (natp level)
;;                 (aa-treep left)
;;                 (aa-treep right))
;;            (aa-treep (node key level left right)))
;;   :hints (("goal" :use 
;;            ((:instance field-not-empty-implies-record-not-empty1
;;                        (a :key) 
;;                        (x (MSET :KEY KEY
;;                                 (MSET :LEFT LEFT
;;                                       (MSET :LEVEL
;;                                             LEVEL (MSET :RIGHT RIGHT NIL))))))))))
    
;(in-theory (disable node))       

(defthm aa-tree-fields-type
  (implies (and (aa-treep v)
                v)
           (and (rationalp (mget :key v))
                (natp (mget :level v))
                (aa-treep (mget :left v))
                (aa-treep (mget :right v))))
  :rule-classes (:rewrite :forward-chaining))

(defthm aa-tree-imples-good-map
  (implies (aa-treep v)
           (acl2::good-map v))
  :rule-classes :forward-chaining)

(defun wf-aa-treep (tree)
  (declare (xargs :guard T))
  (if (null tree)
      t
    (and (aa-treep tree)
         (let ((n (mget :level tree))
               (l (mget :left tree))
               (r (mget :right tree)))
           (if (null l)
               (and (equal 1 n)
                    (or (null r)
                        (and (equal 1 (mget :level r))
                             (null (mget :left r))
                             (null (mget :right r)))))
             (and (wf-aa-treep l)
                  (wf-aa-treep r)
                  (not (null r))
                  (< (mget :level l) n)
                  (<= (mget :level r) n)
                  (mget :right r)
                  (< (mget :level (mget :right r)) n)))))))

(defun skew (tree)
  (declare (xargs :guard (aa-treep tree)))
  (if (null tree)
    tree
    (if (and (mget :left tree) ;guard
             (= (mget :level (mget :left tree)) (mget :level tree)))
      ;;rotate right
      (let ((ltree (mget :left tree))
            (rtree (mget :right tree)))
        (node (mget :key ltree)
              (mget :level ltree)
              (mget :left ltree)
              (node (mget :key tree)
                    (mget :level tree)
                    (mget :right ltree)
                    rtree)))
      tree)))

(defun split (tree)
  (declare (xargs :guard (aa-treep tree)))
  (if (null tree)
    tree
    (if (and (mget :right tree) ;guard
             (mget :right (mget :right tree)) ;guard
             (<= (mget :level tree)
                 (mget :level (mget :right (mget :right tree)))))
      ;;rotate left
      (let* ((rtree (mget :right tree))
             (rrtree (mget :right rtree)))
        (node (mget :key rtree)
              (1+ (mget :level rtree))
              (node (mget :key tree)
                    (mget :level tree)
                    (mget :left tree)
                    (mget :left rtree))
              rrtree))
      tree)))

(defthm skew-sig
  (implies (aa-treep v)
           (aa-treep (skew v))))

(defthm skew-wf
  (implies (and (aa-treep v)
                (wf-aa-treep v))
           (equal (skew v) v)))


(defthm split-sig
  (implies (aa-treep v)
           (aa-treep (split v))))



(defthm split-wf
  (implies (and (aa-treep v)
                (wf-aa-treep v))
           (equal (split v) v)))

(defun insert (e tree)
  (declare (xargs :verify-guards nil
                  :guard (and (rationalp e)
                              (aa-treep tree))))
  (if (or (null tree)
          (not (aa-treep tree))) ;termination
    (node e 1 nil nil)
    (if (equal e (mget :key tree))
      tree
      (let ((newtree (if (< e (mget :key tree))
                       (mset :left 
                             (insert e (mget :left tree))
                             tree)
                       (mset :right
                             (insert e (mget :right tree))
                             tree))))
        (split (skew newtree))))))



;This took a few hours. Its strange that an extra hypothesis
;was obstructing a proof. e.g (acl2::good-map v) was killing
;(acl2::good-map (mset a x v)) because of mset-preserves-acl2::good-map
(defthm insert-sig-supporting-lemma
 (IMPLIES (AND (ACL2::GOOD-MAP V)
               (not (equal a (acl2::ill-formed-key)))
;(ACL2::GOOD-MAP (MSET a x V))
               (MSET a x V))
          (CONSP (MSET a x V)))
 :hints (("goal" :cases ((ACL2::GOOD-MAP (MSET a x V))))
         ("Subgoal 1'" :in-theory (e/d () (acl2::MSET-PRESERVES-GOOD-MAP)))))

(in-theory (disable skew split)) 


(defthm insert-sig-lemma2
  (implies (and (aa-treep v)
                (consp v)
                (aa-treep x))
           (and (aa-treep (mset :left x v))
                (aa-treep (mset :right x v)))))

(defthm insert-sig
  (implies (and (rationalp e)
                (aa-treep v))
           (aa-treep (insert e v))))

(verify-guards insert)

(defun R-index-p (x N)
  (declare (xargs :guard T))
  (and (natp x)
       (< x (nfix N))))

(defun R-index-listp (x N)
  (declare (xargs :guard T))
  (if (atom x)
      (null x)
    (and (R-index-p (car x) N)
         (R-index-listp (cdr x) (nfix N)))))

(defthm R-index-listp-implies-true-listp
  (implies (R-index-listp x N)
           (true-listp x))
  :rule-classes :forward-chaining)

(defun aa-treep2 (v N)
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (acl2::good-map v)
         (R-index-p (mget :key v) N)
         (natp (mget :level v))
         (aa-treep2 (mget :left v) N)
         (aa-treep2 (mget :right v) N))))

(in-theory (enable skew split))

(defthm skew-sig2
  (implies (aa-treep2 v N)
           (aa-treep2 (skew v) N)))


(defthm split-sig2
  (implies (aa-treep2 v N)
           (aa-treep2 (split v) N)))

(defthm insert-sig-lemma2-sp
  (implies (and (aa-treep2 v N)
                (consp v)
                (aa-treep2 x N))
           (and (aa-treep2 (mset :left x v) N)
                (aa-treep2 (mset :right x v) N))))

(in-theory (disable skew split))

(defthm insert-sig-specialized
  (implies (and (R-index-p e N)
                (aa-treep2 v N))
           (aa-treep2 (insert e v) N)))

;; (defthm insert-wf-aa-tree
;;   (implies (and (aa-treep tr);type hyp
;;                 (rationalp n);type hyp
;;                 (wf-aa-treep tr));constraint
;;            (wf-aa-treep (insert n tr))))


(defun insert-list (es tree)
  (declare (xargs :guard (and (rational-listp es)
                              (aa-treep tree))))
  (if (endp es)
      tree
    (insert-list (cdr es)
                 (insert (car es) tree))))

(defthm insert-list-sig
  (implies (and (rational-listp es)
                (aa-treep v))
           (aa-treep (insert-list es v))))

(defthm insert-list-sig-specialized
  (implies (and (R-index-listp es N)
                (aa-treep2 v N))
           (aa-treep2 (insert-list es v) N)))

;what is its complexity?
(defun aa-tree-to-list (tree)
  "convert tree to sorted list"
  (declare (xargs :guard (aa-treep tree)))
  (if (endp tree)
      nil
    (b* ((L (aa-tree-to-list (mget :left tree)))
         (R (aa-tree-to-list (mget :right tree)))
         (key (mget :key tree)))
      (append L (cons key R)))))
         
(defthm aa-tree-to-list-sig
  (implies (aa-treep tree)
           (rational-listp (aa-tree-to-list tree))))

;parameterized types would help here
(defthm append-R-index-listp
  (implies (and (R-index-listp x N)
                (R-index-listp y N))
           (R-index-listp (append x y) N)))

(defthm aa-tree-to-list-sig-specialized
  (implies (aa-treep2 tree N)
           (R-index-listp (aa-tree-to-list tree) N)))

(defun bsearch (key tree)
  (declare (xargs :guard (and (rationalp key)
                              (aa-treep tree))))
  (if (or (null tree)
          (not (aa-treep tree))) ;termination
      nil
    (cond ((< key (mget :key tree)) (bsearch key (mget :left tree)))
          ((> key (mget :key tree)) (bsearch key (mget :right tree)))
          (t key))))


#||
(defrec+ rg%
  ((reachable . unreachable) visited-code typename)
  :sig (and (nat-listp reachable)
            (nat-listp unreachable)
            ;; (or (null representative)
            ;;     (natp representative))
            (unsigned-byte-p 32 visited-code)
            (symbolp typename)
            ))
||#

(defrec rg%
  (visited-code reachable-set can-reach-set unreachable-set typename)
  nil)

(defconst *undefined-typename* :undef) ;'this-cannot-possibly-be-a-type-name-please-dont-even-think-of-it-no-nooooo)

(defconst *default-rg%*
  (acl2::make rg% 
              :reachable-set nil
              :can-reach-set nil
              :unreachable-set nil
              :visited-code 0
              :typename *undefined-typename*
              ))

(defconst *max-unsigned-number* (1- (expt 2 32)))
(defconst *initial-num-types* 2000)
(defconst *block-num-types* 500)


(defun rg%-p (v)
  (declare (xargs :guard T))
  (and 
   (weak-rg%-p v)
   (case-match v
     (('rg% visited-code reachable-set can-reach-set 
            unreachable-set typename)   
      (and (natp visited-code)
           (aa-treep reachable-set)
           (aa-treep unreachable-set)
           (aa-treep can-reach-set)
           (symbolp typename))))))

(defun change-rg% (u% field new)
  (declare (xargs :guard 
                  (and (rg%-p u%)
                       (case field
                         (:typename (symbolp new))
                         (:reachable-set (aa-treep new))
                         (:unreachable-set (aa-treep new))
                         (:can-reach-set (aa-treep new))
                         (:visited-code (natp new))
                         (otherwise nil)))))
  (mbe :logic
       (case field
         (:typename (if (symbolp new)
                        (acl2::change rg% u% :typename new)
                      (assert$ nil u%)))
         (:reachable-set (if (aa-treep new)
                             (acl2::change rg% u% :reachable-set new)
                           (assert$ nil u%)))
         (:unreachable-set (if (aa-treep new)
                               (acl2::change rg% u% :unreachable-set new)
                             (assert$ nil u%)))
         (:can-reach-set (if (aa-treep new)
                             (acl2::change rg% u% :can-reach-set new)
                           (assert$ nil u%)))
         (:visited-code (if (natp new)
                            (acl2::change rg% u% :visited-code new)
                          (assert$ nil u%)))
         (otherwise (assert$ nil u%)))
       :exec 
       (case field
         (:typename (acl2::change rg% u% :typename new))
         (:reachable-set (acl2::change rg% u% :reachable-set new))
         (:unreachable-set (acl2::change rg% u% :unreachable-set new))
         (:can-reach-set (acl2::change rg% u% :can-reach-set new))
         (:visited-code (acl2::change rg% u% :visited-code new))
         (otherwise (assert$ nil u%)))))
                                                 
(defthm change-rg%-sig
  (implies (rg%-p u%)
           (rg%-p (change-rg% u% field new))))

(in-theory (disable weak-rg%-p rg%-p change-rg%))
              

(defstobj R$
  (unique-visited-code :type (integer 0 *) :initially 0)
  (num-types :type (integer 0 *) :initially 0) 
  (rgraph :type (array (satisfies rg%-p) (*initial-num-types*))
          :initially (RG% 0 NIL NIL NIL :UNDEF) :resizable t))
  
;(equal *default-rg%* (RG% 0 NIL NIL NIL :UNDEF))

(defthm rgraphp-implies-true-listp
  (implies (rgraphp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm rgraph-element-type-lemma
  (implies (and (rgraphp x) 
                (natp i) 
                (< i (len x))) 
           (rg%-p (nth i x))))

(defthm rgraph-element-update-lemma
  (implies (and (rgraphp x) 
                (natp i) 
                (< i (len x))
                (rg%-p u%))
           (rgraphp (update-nth i u% x))))

;; (defthm rgraph-element-type
;;   (implies (and (R$p R$) 
;;                 (natp i) 
;;                 (< i (rgraph-length R$))) 
;;            (weak-rg%-p (rgraphi i R$))))


(defthm resize-list-rgraph-sig
  (implies (and (rgraphp x)
                (natp n)
                (rg%-p default))
           (rgraphp (resize-list x n default))))

;; (defthm resize-graph-sig
;;   (implies (and (R$p R$) (natp n)) 
;;            (R$p (resize-rgraph n r$))))

;; (defthm update-numtypes-R$-sig
;;   (implies (and (R$p R$) (natp n)) 
;;            (R$p (update-num-types n r$))))

;; (defthm update-numtypes-R$-length-remains-same
;;   (implies (and (R$p R$) (natp n)) 
;;            (equal (rgraph-length (update-num-types n r$))
;;                   (rgraph-length R$))))


  



(defun add-vertex$ (name R$)
  "Symbol* R$ -> (mv erp new-vertex R$).
   add new vertex with typename name to graph. 
   return new vertex u. post-condition (R-index-p u)"
  (declare (xargs :stobjs (R$)
                  :guard (and (symbolp name)
                              (R$p R$))
                  ;; :guard-hints (("goal" :in-theory 
                  ;;                (disable rgraphi
                  ;;                         rgraph-length
                  ;;                         update-rgraphi
                  ;;                         resize-rgraph
                  ;;                         update-num-types
                  ;;                         change-rg%)))))
                  ))
                 
  (b* ((num-types (num-types R$))
       (size (rgraph-length R$))
       (new-num-types (1+ num-types)))
    (if (< new-num-types size) ;no need to resize
        (b* ((R$ (update-num-types new-num-types R$))
             (u new-num-types)
             (u% (rgraphi u R$))
             (u% (change-rg% u% :typename name))
             (R$ (update-rgraphi u u% R$)))
          (mv nil u R$))
  
      (b* ((R$ (update-num-types new-num-types R$))
           (R$ (resize-rgraph (+ size *block-num-types*) R$))
           (u new-num-types)
           ((unless (< u (rgraph-length R$))) (mv t u R$))
           (u% (rgraphi u R$))
           (u% (change-rg% u% :typename name))
           (R$ (update-rgraphi u u% R$)))
        (mv nil u R$)))))


 
(in-theory (enable rg%-p))

(defun access-rg% (u% field)
  (declare (xargs :guard 
                  (and (rg%-p u%)
                       (member-eq field 
                                  '(:typename :reachable-set 
                                    :unreachable-set :can-reach-set 
                                    :visited-code)))))
                
                         
  (case field
         (:typename (acl2::access rg% u% :typename))
         (:reachable-set (acl2::access rg% u% :reachable-set ))
         (:unreachable-set (acl2::access rg% u% :unreachable-set ))
         (:can-reach-set (acl2::access rg% u% :can-reach-set ))
         (:visited-code (acl2::access rg% u% :visited-code ))
         (otherwise (assert$ nil field))))

(defthm access-rg%-type
  (implies (rg%-p u%)
           (and (symbolp (access-rg% u% :typename))
                (aa-treep (access-rg% u% :reachable-set))
                (aa-treep (access-rg% u% :unreachable-set))
                (aa-treep (access-rg% u% :can-reach-set))
                (integerp (access-rg% u% :visited-code))
                (<= 0 (access-rg% u% :visited-code)))))

(in-theory (disable access-rg% rg%-p))
           

(defun is-subtype$ (u v R$)
  (declare (xargs :guard (and (R$p R$) ;invariant below
                              (R-index-p u (rgraph-length R$))
                              (R-index-p v (rgraph-length R$)))
                  :guard-hints (("goal" :in-theory (e/d (rg%-p) (rgraphp))))
                  :stobjs (R$)))
  ;; (decl :sig ((R-index-p R-index-p R$) -> boolean)
  ;;       :doc "is v in reach-set of u?")
  (b* (((when (int= u v)) t)
       (u% (rgraphi u R$))
       (u-reach-set (access-rg% u% :reachable-set)))
    (bsearch v u-reach-set)))

(defun is-disjoint$ (u v R$)
  (declare (xargs :guard (and (R$p R$)
                              (R-index-p u (rgraph-length R$))
                              (R-index-p v (rgraph-length R$)))
                  :stobjs (R$)))
  ;; (decl :sig ((R-index-p R-index-p R$) -> boolean)
  ;;       :doc "is v in unreachable-set of u?")
  (b* (((when (int= u v)) nil)
       (u% (rgraphi u R$))
       (u-unreach-set (access-rg% u% :unreachable-set)))
    (bsearch v u-unreach-set)))

                   

(defun set-rg%++ (vs field S R$)
  "field[v] =+ S"
  (declare (xargs :stobjs (R$)
                  :guard (and (R$p R$)
                              (R-index-listp vs (rgraph-length R$))
                              (aa-treep S)
                              (member-eq field 
                                  '(:reachable-set 
                                    :unreachable-set :can-reach-set 
                                    )))))
  (if (endp vs)
      R$
    (b* ((v (car vs))
         (v% (rgraphi v R$))
         (v-rs (access-rg% v% field))
         (v-rs (insert-list (aa-tree-to-list S) v-rs))
         (v% (change-rg% v% field v-rs))
         (R$ (update-rgraphi v v% R$)))
      (set-rg%++ (cdr vs) field S R$))))




(defthm set-rg%++-sig1
  (implies (and (R$p R$)
                (R-index-listp vs (rgraph-length R$))
                (aa-treep S))
           (R$p (set-rg%++ vs field S R$))))

(defthm set-rg%++-sig2
  (implies (and (R$p R$)
                (R-index-listp vs (rgraph-length R$))
                (aa-treep S))
           (equal (len (nth *rgraphi* (set-rg%++ vs field S R$)))
                  (len (nth *rgraphi* R$)))))


(defthm R-index-listp-implies-nat-listp
  (implies (R-index-listp x N)
           (nat-listp x))
  :rule-classes :forward-chaining)

; pre-cond: G is transitively-closed. 
; algo: 
;  for each w in can-reach-set[u] U {u}: reach-set[w] =+ {v} U reach-set[v]
;  can-reach-set[v] =+ {u} U can-reach-set[u]
; post-cond: G' is transitively-closed.
       

;need parameterized type theorem for aa-tree i.e r-index-p instead of
;rationalp
(defun rg%-p2 (v N)
  (declare (xargs :guard T))
  (and 
   (weak-rg%-p v)
   (case-match v
     (('rg% visited-code reachable-set can-reach-set 
            unreachable-set typename)   
      (and (natp visited-code)
           (aa-treep2 reachable-set N)
           (aa-treep2 unreachable-set N)
           (aa-treep2 can-reach-set N)
           (symbolp typename))))))

(in-theory (enable access-rg%))

(defthm access-rg%-type2
  (implies (rg%-p2 u% N)
           (and (symbolp (access-rg% u% :typename))
                (aa-treep2 (access-rg% u% :reachable-set) N)
                (aa-treep2 (access-rg% u% :unreachable-set) N)
                (aa-treep2 (access-rg% u% :can-reach-set) N)
                (integerp (access-rg% u% :visited-code))
                (<= 0 (access-rg% u% :visited-code)))))
               
(defthm default-rg%-is-rg%-p2
  (implies (natp N)
           (rg%-p2 *default-rg%* N)))
 
(in-theory (disable access-rg% rg%-p2))

(defun rgraphp2 (x N)
  (declare (xargs :guard t :verify-guards t))
  (if (atom x)
      (equal x nil)
    (and (rg%-p2 (car x) N)
         (rgraphp2 (cdr x) N))))

(defun rg%-p2-forall-i (m N R$)
  (declare (xargs :guard (and (R$p R$)
                              (natp m)
                              (natp N)
                              (<= m N)
                              (<= N (rgraph-length R$)))
                  :stobjs (R$)))
  (if (zp m)
      t
    (and (rg%-p2 (rgraphi (1- m) R$) N)
         (rg%-p2-forall-i (1- m) N R$))))

(defthm rgraphp2-element-type
  (implies (and (natp i)
                (< i (len x)) ;if I add N and N<=(len x). fails! ??
                (rgraphp2 x N)
                )
           (rg%-p2 (nth i x) N)))
                
                
(defun take-first (n xs)
  (declare (xargs :guard (and (natp n) (true-listp xs))))
  (if (endp xs)
      nil
    (if (zp n)
        nil
      (cons (car xs)
            (take-first (1- n) (cdr xs))))))

(encapsulate
 nil
 (local (include-book "arithmetic/top" :dir :system))
 (defthm take-all
   (implies (true-listp x)
            (equal (take-first (len x) x)
                   x))))

(encapsulate 
 nil
 (local
  (progn
    (defthm what11
      (IMPLIES (AND (INTEGERP I)
                    (< 0 I)
                    (INTEGERP I0)
                    (<= 0 I0)
                    (NOT (ZP M))
                    (<= M I)
                    (<= 0 M)
                    (RG%-P2 (NTH I0 (CONS L1 L2)) I)
                    (RG%-P2 L1 I))
               (EQUAL (RGRAPHP2 (TAKE-FIRST I0 (CONS L1 L2)) I)
                      (RGRAPHP2 (TAKE-FIRST I0 L2) I)))
      :hints (("goal" :cases ((zp i0)))))



    (defthm what2211
      (IMPLIES (AND ;(natp N)
                (natp j)
                (natp i)
                (< j i)
                (<= i (len L2))
                (RGRAPHP2 (TAKE-FIRST I L2) N)) 
               (RG%-P2 (NTH j L2) N)))

;; (defthm what33
;;   (IMPLIES (AND (natp i)
;;                 (< j i)
;;                 (natp j)
;;                 (rg%-p2-forall-i i N R$))
;;            (RG%-P2 (nth j (nth *rgraphi* R$)) N)))

    (defthm what33-constrapositive
      (IMPLIES (AND (natp i)
                    (< j i)
                    (natp j)
                    (not (RG%-P2 (nth j (nth *rgraphi* R$)) N))
                    )
               (not (rg%-p2-forall-i i N R$))))

    (defthm subgoal-*1/6.1
      (IMPLIES (AND (CONSP (NTH *RGRAPHI* R$))
                    (NOT (ZP M))
                    (RGRAPHP2 (TAKE-FIRST (+ -1 M) (NTH *RGRAPHI* R$))
                              (LEN (NTH *RGRAPHI* R$)))
                    (R$P R$)
                    (<= M (LEN (NTH *RGRAPHI* R$)))
                    (<= 0 M)
                    (RG%-P2 (NTH (+ -1 M) (NTH *RGRAPHI* R$))
                            (LEN (NTH *RGRAPHI* R$)))
                    (NOT (RG%-P2 (CAR (NTH *RGRAPHI* R$))
                                 (LEN (NTH *RGRAPHI* R$)))))
               (NOT (RG%-P2-FORALL-I (+ -1 M)
                                     (LEN (NTH *RGRAPHI* R$))
                                     R$)))
      :hints (("goal" :cases ((zp (+ -1 M))))))
  

    (defthm what00
      (IMPLIES (and (R$P R$)
                    (NOt (CONSP (NTH *RGRAPHI* R$))))
               (<= (len (NTH *RGRAPHI* R$)) 0))
      :rule-classes :linear)
    
    
    (defthm one-last-lemma-enabling-take-all
      (implies (R$p R$)
               (true-listp (nth *rgraphi* R$))))
    
    ))                

    (defthm rg%-p2-forall-i<=>rgraphp2-main-inductive-strengthening
      (implies (and (R$p R$)
                    (<= m (len (nth *rgraphi* R$)))
                    (natp m))
               (equal (rg%-p2-forall-i m (len (nth *rgraphi* R$)) R$)
                      (rgraphp2 (take-first m (nth *rgraphi* R$)) 
                                (len (nth *rgraphi* R$)))))
      :hints (("goal" :in-theory (disable R$p len))))
    
    (defthm rg%-p2-forall-i<=>rgraphp2
      (implies (R$p R$)               
               (equal (rg%-p2-forall-i (len (nth *rgraphi* R$)) (len (nth *rgraphi* R$)) R$)
                      (rgraphp2 (nth *rgraphi* R$) (len (nth *rgraphi* R$)))))
      :hints (("goal" :in-theory (disable R$p len))))
               
    )

(defun R$p2 (N R$)
  (declare (xargs :guard (and (R$p R$)
                              (natp N)
                              (<= N (rgraph-length R$)))
                  :stobjs (R$)))
  (and (R$p R$)
       (rg%-p2-forall-i N N R$)))


       

;; (defthm R$p2-fc1
;;   (implies (R$p2 R$)
;;            (and (R$p R$)
;;                 (rgraphp2 (nth *rgraphi* R$) (rgraph-length R$))))
;;   :rule-classes :forward-chaining)

(defun add-subtype-edge$ (u v R$)
  "R-index * R-index * R$ -> R$.
   add u->v to graph. Do incremental transitive closure."
  (declare (xargs :stobjs (R$)
                  :guard (and (R$p2 (rgraph-length R$) R$)
                              (R-index-p u (rgraph-length R$))
                              (R-index-p v (rgraph-length R$))
                              )))
  (b* (((when (is-subtype$ u v R$)) R$) ;redundant and idempotent actions 
       (u% (rgraphi u R$))
       (v% (rgraphi v R$))
       (u-can-reach-set (access-rg% u% :can-reach-set))
       (ws (aa-tree-to-list (insert u u-can-reach-set)))
       (R$ (set-rg%++ ws :reachable-set (insert v (access-rg% v% :reachable-set)) R$))
       (v% (change-rg% v% :can-reach-set
                       (insert-list ws
                                    (access-rg% v% :can-reach-set))))
       (R$ (update-rgraphi v v% R$)))
    R$))

; pre-cond: G is transitively-closed. 
; algo: 
;  for each w in can-reach-set[u] U {u}: unreachable-set[w] =+ {v} U can-reach-set[v]
;  for each w in can-reach-set[v] U {v}: unreachable-set[w] =+ {u} U can-reach-set[u]
; post-cond: G' is transitively-closed.

  
(defun add-disjoint-edge$ (u v R$)
  "R-index * R-index * R$ -> R$.
   add u --- v to graph. Do incremental transitive closure."
  (declare (xargs :stobjs (R$)
                  :guard (and (R$p2 (rgraph-length R$) R$)
                              (R-index-p u (rgraph-length R$))
                              (R-index-p v (rgraph-length R$))
                              )))
  (b* (((when (is-disjoint$ u v R$)) R$) ;redundant and idempotent actions 
       (u% (rgraphi u R$))
       (v% (rgraphi v R$))
       (u-can-reach-set (access-rg% u% :can-reach-set))
       (ws (aa-tree-to-list (insert u u-can-reach-set)))
       (R$ (set-rg%++ ws :unreachable-set (insert v (access-rg% v% :can-reach-set)) R$))
       (v-can-reach-set (access-rg% v% :can-reach-set))
       (ws (aa-tree-to-list (insert v v-can-reach-set)))
       (R$ (set-rg%++ ws :unreachable-set (insert u (access-rg% u% :can-reach-set)) R$)))
    R$))
       
;Now top-level calls will be:
;1. Is T1 a subtype of T2?
;2. Are T1 and T2 disjoint?
;3. Add vertex (type) to R$
;4. Add a subtype edge 
;5. Add disjoint edge

(defun add-vertex$$ (T1 R$ types-ht$)
  (declare (xargs :guard (and (symbolp T1)
                              (R$p R$)
                              (types-ht$p types-ht$)
                              (= (types-count types-ht$) (num-types R$)))
                  :stobjs (R$ types-ht$)))
  (if (type-vertex-ht-boundp T1 types-ht$)
      (mv nil R$ types-ht$) ;include-book and other idempotent actions
    (b* ((types-count (types-count types-ht$))
         ((mv erp u R$) (add-vertex$ T1 R$))
         (types-ht$ (update-types-count (1+ types-count) types-ht$))
         ((when erp) (mv erp R$ types-ht$))
         (types-ht$ (type-vertex-ht-put T1 u types-ht$))
         (- (assert$ (= (types-count types-ht$) (num-types R$)) nil)))
      (mv nil R$ types-ht$))))
 

(defun remove-vertex$ (u R$)
  "vertex * R$ -> (mv erp R$).
   remove vertex from graph."
  (declare (xargs :stobjs (R$)
                  :guard (and (R$p2 (rgraph-length R$) R$)
                              (R-index-p u (rgraph-length R$))
                              (> (num-types R$) 0)
                              )))
                 
  (b* ((num-types (num-types R$))
;TODO: check if no edges are incident or leaving vertex 'u'
       (R$ (update-rgraphi u *default-rg%* R$))
       (R$ (update-num-types (1- num-types) R$)))
    (mv nil R$)))


(defun vertex-ht-valid-p (T1 N types-ht$)
  (declare (xargs :guard (types-ht$p types-ht$)
                  :stobjs (types-ht$)))
  (and (symbolp T1)
       (natp N)
       (type-vertex-ht-boundp T1 types-ht$)
       (R-index-p (type-vertex-ht-get T1 types-ht$) N)))  

(defun remove-vertex$$ (T1 R$ types-ht$)
  (declare (xargs :guard (and (R$p2 (rgraph-length R$) R$)
                              (> (num-types R$) 0)
                              (types-ht$p types-ht$)
                              (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
                              (= (types-count types-ht$) (num-types R$)))
                  :stobjs (R$ types-ht$)))
  (if (not (type-vertex-ht-boundp T1 types-ht$))
      (mv nil R$ types-ht$) ;idempotent actions
    (b* ((types-count (types-count types-ht$))
         (types-ht$ (update-types-count (1- types-count) types-ht$))
         (u (type-vertex-ht-get T1 types-ht$))
         ((mv erp R$) (remove-vertex$ u R$))
         ((when erp) (mv erp R$ types-ht$))
         (types-ht$ (type-vertex-ht-rem T1 types-ht$))
         (- (assert$ (= (types-count types-ht$) (num-types R$)) nil)))
      (mv nil R$ types-ht$))))



                  

;pre-cond: T1 and T2 are bound in types-ht$  
(defun add-edge$$ (kind T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p2 (rgraph-length R$) R$)
                              (types-ht$p types-ht$)
                              (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
                              (vertex-ht-valid-p T2 (rgraph-length R$) types-ht$)
                              (or (eq kind :subtype)
                                  (eq kind :disjoint)))
                  :stobjs (R$ types-ht$)))

  (b* ((u1 (type-vertex-ht-get T1 types-ht$))
       (u2 (type-vertex-ht-get T2 types-ht$)))
    (cond ((or (eq T1 'acl2::all) ;some cases impossible,
               (eq T2 'acl2::all) ;others trivially true
               (eq T1 'acl2::empty)
               (eq T2 'acl2::empty)) R$) 
          ((eq kind :subtype) (add-subtype-edge$ u1 u2 R$))
          (t (add-disjoint-edge$ u1 u2 R$)))))


(defmacro add-edge-event (kind T1 T2)
  `(make-event
    (er-progn
     (trans-eval `(add-edge$$ ',',kind ',',T1 ',',T2 R$ types-ht$)
                 'add-edge-event state t)
     (value '(value-triple :invisible)))
    :check-expansion t))


(defun is-disjoint$$0 (T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p R$)
                              (types-ht$p types-ht$)
                              (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
                              (vertex-ht-valid-p T2 (rgraph-length R$) types-ht$))
                  :stobjs (R$ types-ht$)))
  (b* ((u1 (type-vertex-ht-get T1 types-ht$))
       (u2 (type-vertex-ht-get T2 types-ht$)))
    (is-disjoint$ u1 u2 R$)))

(defun is-disjoint$$ (T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p R$)
                              (types-ht$p types-ht$)
                              (symbolp T1)
                              (symbolp T2))
                  :stobjs (R$ types-ht$)))
  (cond ((or (eq T1 'acl2::all) (eq T2 'acl2::all)) nil)
        ((or (eq T1 'acl2::empty) (eq T2 'acl2::empty)) t)
        ((and (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
              (vertex-ht-valid-p T2 (rgraph-length R$) types-ht$))
         (is-disjoint$$0 T1 T2 R$ types-ht$))
        (t nil))) ;conservative


(defun is-subtype$$0 (T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p R$)
                              (types-ht$p types-ht$)
                              (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
                              (vertex-ht-valid-p T2 (rgraph-length R$) types-ht$))
                  :stobjs (R$ types-ht$)))
  (b* ((u1 (type-vertex-ht-get T1 types-ht$))
       (u2 (type-vertex-ht-get T2 types-ht$)))
    (is-subtype$ u1 u2 R$)))

;relax it to take into accound singleton types (constants)
(defun is-subtype$$ (T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p R$)
                              (types-ht$p types-ht$)
                              (symbolp T1)
                              (symbolp T2))
                  :stobjs (R$ types-ht$)))
  (cond ((eq T2 'acl2::all) t)
        ((eq T1 'acl2::empty) t)
;ASSUMPTION: Types equivalent to all and empty should be recognized
;separately. In this function, we simply return nil, so we can have false
;positives.
        ((eq T2 'acl2::empty) nil)
        ((eq T1 'acl2::all) nil)
        ((and (vertex-ht-valid-p T1 (rgraph-length R$) types-ht$)
              (vertex-ht-valid-p T2 (rgraph-length R$) types-ht$))
         (is-subtype$$0 T1 T2 R$ types-ht$))
        (t nil))) ;be conservative
                              

(defun is-alias$$ (T1 T2 R$ types-ht$)
  (declare (xargs :guard (and (R$p R$)
                              (types-ht$p types-ht$)
                              (symbolp T1) 
                              (symbolp T2))
                  :stobjs (R$ types-ht$)))
  (and (is-subtype$$ T1 T2 R$ types-ht$)
       (is-subtype$$ T2 T1 R$ types-ht$)))

  

;; (defun is-subtype-gv (t1 t2 wrld)
;;   (ec-call (is-subtype-current t1 t2 state)))

;; (defun is-disjoint-gv (t1 t2 wrld)
;;   (ec-call (is-disjoint-current t1 t2 state)))

;; (defattach is-subtype is-subtype-gv)
;; (defattach is-disjoint is-disjoint-gv)

;; (defun is-alias-current (t1 t2 state)
;;   (declare (xargs :mode :program
;;                   :stobjs (state)
;;                   :guard (and (symbolp t1)
;;                               (symbolp t2))))
;;   (b* (((er b1) (is-subtype t1 t2 state))
;;        ((er b2) (is-subtype t2 t1 state)))
;;     (value (and b1 b2))))

;; (defun is-alias-gv (t1 t2 state)
;;   (ec-call (is-alias-current t1 t2 state)))

;; (defattach is-alias is-alias-gv)

; pretty printing utilities

(defabbrev vname$ (u)
  (access-rg% (rgraphi u R$) :typename))
  
(defun vnames$ (us R$)
  (declare (xargs :guard (R$p R$)
                  :stobjs (R$)))
  (if (atom us)
      nil
    (if (R-index-p (car us) (rgraph-length R$))
        (cons (vname$ (car us))
              (vnames$ (cdr us) R$))
      (cw "~% ~x0 is not a valid vertex of R$~%" (car us)))))

(defun display-R$ (u R$ field)
  "display field for vertices less than u+"
  (declare (xargs :guard (and (R$p R$)
                               (natp u)
                               (member-eq field '(:reachable-set :unreachable-set :can-reach-set)))
                  :stobjs (R$)))
  (if (zp u)
      nil
    (if (< u (rgraph-length R$))
        (b* ((nm (vname$ u))
             (u% (rgraphi u R$))
             (fset (aa-tree-to-list (access-rg% u% field)))
             (- (cw "~% ~x0 ~x1 : ~x2 " nm field (vnames$ fset R$))))
          (display-R$ (1- u) R$ field))
      (display-R$ (1- u) R$ field))))
             
  
(defun display-subtype-graph (R$)
  (declare (xargs :guard (R$p R$)
                  :stobjs (R$)))
  (b* ((num-types (num-types R$)))
    (display-R$ num-types R$ :reachable-set)))










;; alternative hash-table implementation - incomplete

#||
;from practice of programming. MULTIPLIER = 31 or 37
/* hash: compute hash value of string */
unsigned int hash(char *str)
{
   unsigned int h;
   unsigned char *p;

   h = 0;
   for (p = (unsigned char*)str; *p != '\0'; p++)
      h = MULTIPLIER * h + *p;
   return h; // or, h % ARRAY_SIZE;
}


(defun mod-fast1 (x y)
  (if (< x y)
      x
    (mod-fast1 (- x y) y)))

(defstub mod-fast (* *) => *)
(defattach mod-fast mod-fast1) ;or just attach it to mod

(defconst *hash_prime* 1777)

(def knuth-texbook-hash1. (cs ans)
  (decl :sig ((character-listp natp) -> natp)
        :doc "see #261, pg108 of TexBook.")
  (if (endp cs)
      (mod-fast ans *hash_prime*)
    (b* ((code (char-code (car cs))))
    (knuth-texbook-hash1. (cdr cs) (+ (* 2 ans) code)))))
      
(def knuth-texbook-hash. (a)
  (decl :sig ((stringp) -> natp) ;non-empty string
        :doc "given a non-empty string, return its hash value")
  (b* ((cL (coerce a 'list))
       (ctx 'knuth-texbook-hash.)
       ((unless (consp cL))
        (er hard ctx "~|CEgen/Error: Cannot pass an empty string!~|"))
       ((when (consp (cdr cL))) (char-code (car cL))))
    (knuth-texbook-hash1. (cdr cL) (char-code (car cL)))))

; key: symbol name of type (stringp)
; value: (list* key vertex next-index)
;;   - if A is the array implementing the hash table, then next-index
;;     is an index into it.
;;   - vertex is the index of key into adjacency list array G
(defstobj types-hash-table$
  (types-count :type (integer 0 *) :initially 0)
  (ht-array :type (array (unsigned-byte 32) (0))
            :initially nil
            :resizable t))
||#


#||

; code which might be thrown, since now i have implemented incremental
; transitive closure

; we will maintain a global subtype graph, with following invariants
; Let p = types-ht(P) be the vertex in subtype graph for type P.

; I1 -- (defdata-subtype P Q) =>  q in s-adj(p).reachable-set
;                                 p in s-adj(q).can-reach-set

; I2 -- (defdata-disjoint P Q) => q in s-adj(p).unreachable-set and vice-versa

; I3 -- q in s-adj(p).unreachable => (p,q) not in edges of reachability closure of s-adj

; I4 -- forall i s-adj(i).reachable mutually disjoint with s-adj(i).unreachable

; I5 -- lists reachable and unreachable are sorted (for binary search)

; I6 -- at the beginning of a new graph traversal, the
;       unique-visited-code is incremented by 1, so that old visited
;       information is invalidated. 




(mutual-recursion
;returns -> (mv boolean R-index-listp R$)
; simple DFS variant.
(defun find-path-s$. (u R$ v N path.)
  (declare (xargs :guard (and (natp N)
                              (R-index-p u N)
                              (R$p R$)
                              (R-index-p v N)
                              (R-index-listp path. N))
                  :stobjs (R$)))
  (declare (xargs :measure (nfix N)))
; pre-conditions
; - u has not been visited.
; post-conditions
; - (car result) = t => (car path.) = v && (last path.) = u
  (if (zp N)
      (mv nil '() R$)
    (b* (((when (int= u v)) (mv t (cons u path.) R$))
         (u-rg% (rgraphi u R$))
         (u-rg% (acl2::change rg% u-rg% 
                                     :visited-code (unique-visited-code R$)))
         (R$ (update-rgraphi u u-rg% R$)) ;update visited info

         (path. (cons u path.)) ; extend the path

         (ws (acl2::access rg% u-rg% :reachable))
         ((when (bsearch v ws)) ;found in adjacent, abort
          (mv t (cons v path.) R$))

         (disjoint-ws (acl2::access rg% u-rg% :unreachable))
         ((when (bsearch v disjoint-ws)) ;cannot be subtype, abort
          (mv nil '() R$)))

      (find-path-s$-lst. ws R$ v (1- N) path.))))

(defun find-path-s$-lst. (us R$ v N path.)
  (declare (xargs :guard (and (natp N)
                              (R-index-listp us N)
                              (R$p R$)
                              (R-index-p v N)
                              (R-index-listp path. N))
                  :stobjs (R$)))
  (if (endp us)
      (mv nil path. R$)
    (b* ((u (car us))
         (u-rg% (rgraphi u R$))
         (u-visited-code (acl2::access rg% u-rg% :visited-code))
         ((when (int= u-visited-code (unique-visited-code R$))) 
          (find-path-s$-lst. (cdr us) R$ v path.)) ;already visited, move on
         ((mv found-v? path1 R$) (find-path-s$. u R$ v N path.))
         ((when found-v?) (mv t path1 R$))) ;abort with success
      (find-path-s$-lst. (cdr us) R$ v path.)))))
         

(defun reset-visited-codes1 (n R$)
  (declare (xargs :stobjs (R$)))
  (if (zp n)
      R$
    (b* ((u (1- n))
         (u% (rgraphi u R$))
         (u% (acl2::change rg% u% :visited-code 0))
         (R$ (update-rgraphi u u% R$)))
      (reset-visited-codes1 (1- n) R$))))
         
        
(defun reset-visited-codes (R$)
  (declare (xargs :stobjs (R$)))
  (b* ((R$ (update-unique-visited-code 0 R$))
  (reset-visited-codes1 (num-types R$) R$))


(def is-subtype-R$ (u v R$)
  (decl :sig ((R-index-p R-index-p R$) -> (mv booleanp R$p))
        :doc 
"update visited-code for new traversal of R$. do DFS on u.")
  (b* (((when (int= u v)) (mv t R$))
       (R$ (if (< (unique-visited-code R$) *max-unsigned-number*)
               R$
             (reset-visited-codes R$)))
       (R$ (update-unique-visited-code (1+ (unique-visited-code R$)) R$)) ;reset for new traversal
;possible optimization: on every traversal, we obtain
;valuable reachability information P. update R$ with it.
       ((mv b ?path R$) (find-path-s$. u R$ v (num-types R$) '())))
    (mv b R$)))
||#