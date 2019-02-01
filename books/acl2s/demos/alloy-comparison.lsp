(in-package "ACL2")
(include-book "alloy-support")
(include-book "acl2s/cgen/top" :dir :system)
;;(acl2::in-package "ACL2S")

(acl2s-defaults :set :use-fixers nil)
(acl2s-defaults :set :search-strategy :incremental)
(acl2s-defaults :set :backtrack-limit 2)


;Address Book example    
;Fig 2.14 from Alloy Book
;(defdata Address character)
(defdata Address acl2s::pos)
;(defdata Address (cons 'A acl2s::pos))
;(defdata Alias neg)
;(defdata Alias (cons 'S acl2s::pos))
(defdata Alias (enum (defdata::numbered-vars 'A 50)))
;(defdata Group acl2s::pos)
(defdata Group (enum (defdata::numbered-vars 'G 50)))

(defthm alias-is-a-symbol
  (implies (aliasp x)
           (symbolp x))
  :rule-classes :forward-chaining)

(defthm group-is-a-symbol
  (implies (groupp x)
           (symbolp x))
  :rule-classes :forward-chaining)

(in-theory (disable aliasp groupp GROUP=>DEF ALIAS=>DEF DEF=>GROUP DEF=>ALIAS ))


;(defdata Group (cons 'G acl2s::pos)) ;bad because it gets dest-elimed. 
;records also dont work since map lemmas do not go through

(defdata Name (oneof Alias Group))
(defdata Target (oneof Address Name))


;(defdata Names (set Name))
(defdata Name-list (oneof nil (set::insert Name Name-list)))
;(defdata Targets (set Target))
(defdata Targets (oneof nil (set::insert Target Targets)))

(defdata name-target-map (map Name Targets))

(defdata Book (record (names . Name-list)
                      (addr . name-target-map)))



(defun names-not-cyclic (names N-T-map)
  (if (endp names)
    t
    (and (not (set::in (car names) (reachable (car names) N-T-map)))
         (names-not-cyclic (cdr names) N-T-map))))

(defun names-not-cyclic-fix (names N-T-map)
  (if (endp names)
    N-T-map
    (if (set::in (car names) (reachable (car names) N-T-map))
      (names-not-cyclic-fix (cdr names) (remove1-assoc-equal (car names) N-T-map))
      (names-not-cyclic-fix (cdr names) N-T-map))))


(defun aliases-have-atmost-one-address (N-T-map)
  (if (endp N-T-map)
    t
    (let* ((name (caar N-T-map))
           (targets (cdar N-T-map))
           (num-targets (len targets)))
      (and (implies (aliasp name) (<= num-targets 1))
           (aliases-have-atmost-one-address (cdr N-T-map))))))

(defun aliases-have-atmost-one-address-fix (N-T-map)
  (if (endp N-T-map)
    N-T-map
    (let* ((name (caar N-T-map))
           (targets (cdar N-T-map)))
      (if (and (consp targets)
               (aliasp name))
        (cons (cons name (list (car targets)))
              (aliases-have-atmost-one-address-fix (cdr N-T-map)))
        (cons (car N-T-map) (aliases-have-atmost-one-address-fix (cdr N-T-map)))))))
           
(defun good-addressp (addr names)
  (and (equal names (dom addr))
       (names-not-cyclic names addr)
       (aliases-have-atmost-one-address addr)))
       
(defun good-bookp (b)
  (and (bookp b)
       (good-addressp (g :addr b) (g :names b))))

(defun good-book-enum (n)
  (declare (xargs :mode :program))
  (b* ((book (nth-book-builtin n))
       (A (g :addr book))
       (A1 (names-not-cyclic-fix (dom A) A))
       (A2 (aliases-have-atmost-one-address-fix A1)))
      (book (dom A2) A2)))

;(acl2s::defdata-attach book :enumerator good-book-enum)


(defun add (b n tg)
  (let* ((b.addr (g :addr b))
         (b.addr1 (s n (set::insert tg (g n b.addr)) b.addr)))
    (s :addr b.addr1 b)))

(defun del (b n tg)
  (let* ((b.addr (g :addr b))
         (b1.addr (s n (set::delete tg (g n b.addr)) b.addr)))
    (s :addr b1.addr b)))

(defun filter-addresses (tgts)
  (if (endp tgts)
    nil
    (if (Addressp (car tgts))
        (cons (car tgts) (filter-addresses (cdr tgts)))
      (filter-addresses (cdr tgts)))))

;return all addresses pointed by n
(defun lookup (b n)
  (let ((rtargets (reachable n (g :addr b))))
    (filter-addresses rtargets)))

(time$
 ;0.19
(defthm addIdempotent
  (implies (and (good-bookp b)
                (Namep n)
                (Targetp tgt))
           
           (equal (g :addr (add (add b n tgt) n tgt))
                (g :addr (add b n tgt)))))
)
(time$
;0.07
 (defthm delUndoesAdd
  (implies (and (good-bookp b)
                (Namep n)
                (not (g n (g :addr b))) ;Doesnt catch the error
                (Targetp tgt))
           (equal (del (add b n tgt) n tgt) b)))
)

(include-book "misc/eval" :dir :system)#|ACL2s-ToDo-Line|#

;(in-theory (disable reachable))

(must-fail
;
(time$
 (test?; lookupYields
  (implies (and (good-bookp b)
                (namep n)
                (member-equal n (g :names b))
                )
           (lookup b n))))
)

#|
;(must-fail
;88.30, 
(time$ (test?; addLocal
  (implies (and (good-bookp b)
                (namep n)
                (targetp tgt)
                (namep n1)
                (not (equal n1 n))
                )
           (equal (lookup (add b n tgt) n1)
                  (lookup b n1))))
       
)
;|#

#|
;SIMULATING BOUNDED EXHAUSTIVE TESTING
(defdata addr1 (oneof #\a #\b #\c))
(defdata Alias1 (oneof -1 -2 -3))
(defdata Group1 (oneof 1 2 3))
(defdata Name1 (oneof Alias1 Group1))
(defdata Target1 (oneof Addr1 Name1))

(defdata Names1 (oneof nil (set::insert Name1 Names1)))
(defdata Targets1 (oneof nil (set::insert Target1 Targets1)))

(defdata name-target-map1 (map Name1 Targets1))
(defdata Book1 (record (names . Names1)
                       (addr . name-target-map1)))

(defun good-book1p (b)
  (and (book1p b)
       (good-addressp (g :addr b) (g :names b))))

;some settings related to testing engine
:set-ignore-ok t
(include-book "misc/eval" :dir :system)
(must-fail
;12.63sec
(time$ (test?; addLocal
  (implies (and (good-book1p b)
                (name1p n)
                (target1p tgt)
                (name1p n1)
                (not (equal n1 n))
                )
           (equal (lookup (add b n tgt) n1)
                  (lookup b n1)))))
)

(must-fail
;0.83sec
(time$
 (test?; lookupYields
  (implies (and (good-book1p b)
                (name1p n)
                (set::in n (g :names b))
                )
           (lookup b n))))
)
|#


;Abstract Memory
;Fig 6.18 Page 217 from Alloy Book
(defdata maddr acl2s::pos)
(defdata mdata (oneof nil acl2s::neg))
(defdata memory (map maddr mdata))

;maps are already canonicalized
;init constraint is not necessary

(defun mwrite (m a d)
  (s a d m))

(defun mread (m a)
  (g a m))

(time$
 ;0.01
(defthm WriteRead 
  (implies (and (memoryp m)
                (maddrp a)
                (mdatap d))
           (equal (mread (mwrite m a d) a)
                  d)))
)
(time$
 ;0.01
(defthm WriteIdempotent
  (implies (and (memoryp m)
                (maddrp a)
                (mdatap d))
           (equal (mwrite (mwrite m a d) a d)
                  (mwrite m a d))))
)

;Media Assets
;This is a model of a media storage as described
;on Pages 210-212 of the Alloy book.

(defdata Asset acl2s::pos)
(defdata AssetsT (oneof nil (set::insert Asset AssetsT)))
(defdata assetsU (oneof AssetsT 'Undefined))
(defdata CatalogState
  (record (assets . AssetsT)
          (showing . AssetsT)
          (selection . AssetsU)))
;Note: hidden+showing = assets

(defdata Catalog (record (cname . string)
                         (cstate . CatalogState)))

(defdata CatalogsT (oneof nil (set::insert Catalog CatalogsT)))
    
(defdata ApplicationState
  (record (catalogs . CatalogsT)
          (currentCatalog . Catalog);in catalogs
          (buffer .  AssetsT)))

(defun catalogStateInv (cs)
  (let* ((cs.selection (g :selection cs))
        (cs.showing (g :showing cs))
        ;(cs.hidden (s- (g :assets cs) cs.showing))
       )
    (or (equal  cs.selection 'Undefined)
        (and (not (set::empty cs.selection))
             (set::subset cs.selection cs.showing)))))
   
(defun catalogsInv (Cs)
  (if (set::empty Cs)
    t
    (and (catalogStateInv (g :cstate (set::head Cs)))
         (catalogsInv (set::tail Cs))))) 

(defun appInv (xs)
  (catalogsInv (g :catalogs xs)))


(defun showSelected (cs)
  (let ((cs.selection (g :selection cs))
        ;(cs.assets (g :assets cs))
        )
    (if  (equal cs.selection 'Undefined)
      (er hard 'showSel "junk")
      (up cs 
          :showing cs.selection
          :selection cs.selection))))
          

(defun hideSelected (cs)
  (let* ((cs.selection (g :selection cs))
        ;(cs.assets (g :assets cs))
        (cs.showing (g :showing cs))
        ;(cs.hidden (s- cs.assets (g :showing cs)))
        )
    (if  (equal cs.selection 'Undefined)
      (er hard 'showSel "junk")
      (up cs 
          :showing (s- cs.showing cs.selection)
          :selection 'Undefined
          ))))

;gives new xs applicationstate
(defun cut (xs)
  (let* ((currC (g :currentCatalog xs))
         (cs (g :cstate currC))
         (sel (g :selection cs))
         (cs.showing (g :showing cs))
         ;(cs.assets (s+ cs.showing (g :hidden cs)))
         
         (xs.catalogs (g :catalogs xs)))
    (if (equal sel 'Undefined)
      (er hard 'cut "junk")
      ;make xs'
      (let* ((newshowing (s- cs.showing sel))
             ;(newassets (s- cs.assets sel))
            (newCurrCat 
             (up currC
                 :cstate (up cs 
                             :showing newshowing
                             :selection 'Undefined)))
            (newcatalogs 
             (set::insert newCurrCat
                        (set::delete currC xs.catalogs))))
                 
      (up nil
          :buffer sel
          :currentCatalog newCurrCat
          :catalogs newcatalogs)))))

;gives new xs applicationstate
(defun paste (xs)
  (let* ((currC (g :currentCatalog xs))
         (cs (g :cstate currC))
         (cs.assets (g :assets cs))
         (cs.showing (g :showing cs))
         (xs.catalogs (g :catalogs xs))
         (buf (g :buffer xs)))
      ;make xs'
      (let* ((newshowing (s+ cs.showing (s- buf cs.assets)))
            (newCurrCat 
             (up currC
                 :cstate (up cs 
                             :assets (s+ cs.assets buf)
                             :showing newshowing
                             :selection (s- buf cs.assets))))
            (newcatalogs 
             (set::insert newCurrCat
                        (set::delete currC xs.catalogs))))
                 
      (up nil
          :buffer buf
          :currentCatalog newCurrCat
          :catalogs newcatalogs))))

(time$
 ;0.26
(defthm HidePreservesInv
  (implies (and (catalogStatep cs)
                (catalogStateInv cs)
                ;precondition for hideSelected
                (not (equal (g :selection cs)
                            'Undefined)))
           (catalogStateInv (hideSelected cs))))
)

(must-fail
(time$ 
 ;0.49 sec
 (test?; CutPaste {
    (implies (and (applicationStatep xs)
                  (appInv xs))
             (equal (paste (cut xs))
                    xs))))
)

(must-fail
(time$ 
 ;4.58 sec
 (test?; PasteCut {
    (implies (and (applicationStatep xs)
                  (appInv xs))
             (equal (cut (paste xs))
                    xs)))
 ))

(defun hidden (c)
  (let ((cs (g :catalogState c)))
    (s- (g :assets cs) (g :showing cs))))

(time$
;0.42 sec
 (defthm PasteNotAffectHidden
  (implies (and (applicationStatep xs)
                (appInv xs)
                )
           (equal (hidden (g :currentCatalog (paste xs)))
                  (hidden (g :currentCatalog xs)))))
)

;Mark and Sweep garbage collection  [El Ghazi paper]
;Adapted from the Alloy model at http://www.rz.uni-karlsruhe.de/~ kh133/alloyToSMT/

(defdata node acl2s::pos)
(defdata nodes (oneof nil (set::insert node nodes)))
(defdata pointsToMap (map node node))
(defdata heapState (record (hnodes . nodes)
                           (left . pointsToMap)
                           (right . pointsToMap)
                           (marked . nodes)
                           (freelist . nodes)))


(defun reachable-in-heap1 (x H i marked)
  (if (zp i)
    marked
    (if (null x) ;leaf
      marked
      (let ((left-x (g x (g :left H)))
            (right-x (g x (g :right H))))
        (reachable-in-heap1 
         right-x H (1- i) 
         (set::insert 
          x (reachable-in-heap1 left-x H (1- i) marked)))))))

(defun reachable-in-heap (n H)
  (reachable-in-heap1 n H (len (g :hnodes H)) nil))


;sweep through heap and move all unmarked nodes to freelist
(defun sweep (H)
  (let* ((marked (g :marked H))
         (unmarked (s- (g :hnodes H) marked))
         ;is the following necessary for correctness?
         ;is the following even really done?
         (p (delete-entries (g :left H) unmarked))
         (n (delete-entries (g :right H) unmarked))
         )
    (up H :freelist unmarked :left p :right n)))
            
(defun GC (root H)
  (let* ((ns (reachable-in-heap root H ))
         (H (s :marked ns H)))
    (sweep H)))
         

(time$           
(defthm Completeness
    (implies (and (heapStatep H)
                  (set::in n (s- (g :hnodes H);n is garbage
                                  (reachable-in-heap root H))))
             (set::in n (g :freelist (GC root H)))))
)
(time$
(defthm Soundness
  (implies (and (heapStatep H)
                (set::in n (reachable-in-heap root H));live
                )
           (not (set::in n (g :freelist (GC root H))))))
)
         
