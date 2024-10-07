(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;----------------------------------------------------------------------


(defthm if-found-pc-in-suffix-found-in-stackmaps
  (implies (and (is-suffix stack-maps1 stack-maps)
                (strictly-ordered (extract-frame-pc stack-maps))
                (member pc (extract-frame-pc stack-maps1)))
           (member pc (extract-frame-pc stack-maps))))

(defthm is-suffix-is-suffix-extract-frame-pc
  (implies (is-suffix stack-maps1 stack-maps)
           (is-suffix (extract-frame-pc stack-maps1)
                      (extract-frame-pc stack-maps))))



(defthm prefix-member-equal
  (implies (and (ordered (extract-frame-pc l1))
                (isstackmapframe x)
                (<= (mapOffset (getMap (car l1))) y)
                (< (mapOffset (getMap x)) (mapOffset (getMap (car l1)))))
           (equal (searchStackFrame y (cons x l1))
                  (searchStackFrame y l1)))
  :hints (("Goal" :in-theory (disable isstackmapframe 
                                      getMap
                                      mapFrame
                                      mapOffset))))


(defun prefix-less-stack-maps (v l)
  (if (endp l) nil
    (if (< (mapOffset (getMap (car l))) v)
        (cons (car l) (prefix-less-stack-maps v (cdr l)))
      nil)))

(defun all-stack-map (l)
  (if (endp l)
      t
    (and (isstackmapframe (car l))
         (all-stack-map (cdr l)))))
         

(defthm searchStackFrame-equal-if-append-prefix-less 
  (implies (and (<= v pc)
                (all-stack-map l2))
           (equal (searchStackFrame pc (append (prefix-less-stack-maps v l2)
                                               l1))
                  (searchStackFrame pc l1)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isstackmapframe 
                               getMap
                               mapFrame
                               mapOffset))))

(defun extract-frame-pc-2 (l2)
  (if (endp l2) nil
    (cons (mapOffset (getMap (car l2)))
          (extract-frame-pc-2 (cdr l2)))))
  

(defthm strictly-ordered-is-suffix-reduce
  (implies (and (strictly-ordered (extract-frame-pc-2 l2))
                (is-suffix l1 l2)
                (consp l1))
           (equal (append (prefix-less-stack-maps (mapOffset (getMap (car l1))) l2)
                          l1)
                  l2))
  :hints (("Goal" :do-not '(generalize)
           :induct (is-suffix l1 l2)
           :in-theory (disable isstackmapframe 
                               getMap
                               mapFrame
                               mapOffset))))

(defthm is-suffix-member-x
  (implies (and (IS-SUFFIX L1 L2)
                (member x l1))
           (member x l2)))


(defthm all-stack-map-stack-map-wrap
  (all-stack-map (stack-map-wrap anylist)))

(defthm extract-frame-pc-2-equal-extract-frame-pc
  (equal (extract-frame-pc-2 (stack-map-wrap stack-maps))
         (extract-frame-pc stack-maps)))

(defthm is-suffix-is-suffix-wrap
  (implies    (IS-SUFFIX STACK-MAPS1 STACK-MAPS)
              (IS-SUFFIX (STACK-MAP-WRAP STACK-MAPS1)
                         (STACK-MAP-WRAP STACK-MAPS))))
           

(defthm searchStackFrame-reduce-lemma
  (implies (equal (mapOffset stackframe) pc)
           (equal (SEARCHSTACKFRAME pc (cons (makestackmap stackframe) l))
                  (mapFrame stackframe))))

(defthm isstackmapframe-make-stack-map
  (ISSTACKMAPFRAME (MAKESTACKMAP STACK-MAPS2)))
        
(defthm searchStackFrame-reduce
  (implies (and (is-suffix stack-maps1 stack-maps)
                (consp stack-maps1)
                (strictly-ordered (extract-frame-pc stack-maps))
                (<= (mapOffset (car stack-maps1)) pc))
           (equal (searchStackFrame pc (stack-map-wrap stack-maps1))
                  (searchStackFrame pc (stack-map-wrap stack-maps))))
    :hints (("Goal" :do-not '(generalize)
             :do-not-induct t
             :in-theory (disable isstackmapframe 
                                 getMap
                                 ;;searchStackFrame-equal-if-append-prefix-less 
                                 strictly-ordered-is-suffix-reduce
                                 makestackmap
                                 mapFrame
                                 mapOffset)
             :use ((:instance strictly-ordered-is-suffix-reduce
                              (l2 (stack-map-wrap stack-maps))
                              (l1 (stack-map-wrap stack-maps1)))))))
                              
