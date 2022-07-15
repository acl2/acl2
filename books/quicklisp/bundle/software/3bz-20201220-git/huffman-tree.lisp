(in-package 3bz)


;; accessors/predicates/constructors for node in tree
;; low bits 00 = literal
;; low bits 01 = link flag, #x0001 = end, #xffff = invalid
;; low bits 10 = len/dist
;; (low bits 11 = invalid)

(declaim (inline ht-linkp ht-invalidp ht-endp ht-node-type
                 ht-link-bits ht-link-offset
                 ht-literalp ht-extra-bits ht-value
                 ht-link-node ht-literal-node ht-len-node ht-dist-node
                 ht-invalid-node ht-end-node))
(defun ht-linkp (node)
  (oddp node))
(defun ht-invalidp (node)
  (= node #xffff))
;; (usually will just check for link bits or link-offset = 0 for endp)
(defun ht-endp (node)
  (= node #x0001))
(defun ht-node-type (node)
  (ldb (byte 2 0) node))

;; for valid link, store 4 bits of bit-count, 10 bits of table base
(defun ht-link-node (bits index)
  (logior +ht-link/end+
          (ash bits 2)
          (ash index 6)))
(defun ht-link-bits (node)
  (ldb (byte 4 2) node))
(defun ht-link-offset (node)
  (ldb (byte 10 6) node))


(defun ht-literalp (node)
  (zerop (ldb (byte 2 0) node)))
(defun ht-len/dist-p (node)
  (= 1 (ldb (byte 2 0) node)))
;; literals just store an 8-bit code value. len/dist codes store an
;; 8-bit index into base array, and 4bits extra bits count
;; fixme: merge these with link, so decoded can treat them the same?
(defun ht-extra-bits (node)
  (ldb (byte 4 2) node))
(defun ht-value (node)
  (ldb (byte 10 6) node))



(defun ht-literal-node (value)
  (logior +ht-literal+
          (ash value 6)))

(defun ht-len-node (value extra-bits)
  (assert (>= value +lengths-start+))
  ;; value stored in tree is offset so we can use single table
  ;; for extra-bits and base-values for lengths and distances
  (let ((v (+ +lengths-extra-bits-offset+
              (if (>= value +lengths-start+)
                  (- value +lengths-start+)
                  value))))
    (ldb (byte 16 0)
         (logior +ht-len/dist+
                 (ash v 6)
                 (ash (aref extra-bits v) 2)))))

(defun ht-dist-node (value extra-bits)
  (ldb (byte 16 0)
       (logior +ht-len/dist+
               (ash value 6)
               (ash (aref extra-bits value) 2))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun ht-invalid-node () #xffff)
  (defun ht-end-node () #x0001)
  #-cmucl(declaim (inline ht-max-bits ht-start-bits))

  (defstruct (huffman-tree (:conc-name ht-))
    (start-bits 0 :type ht-bit-count-type)
    (max-bits 0 :type (mod 29))
    (nodes (make-array +max-tree-size+
                       :element-type 'ht-node-type
                       :initial-element (ht-invalid-node))
           :type ht-node-array-type)))

(defmethod make-load-form ((object huffman-tree) &optional environment)
  (make-load-form-saving-slots object :environment environment))

(defparameter *fixed-lit/length-table*
  (concatenate 'code-table-type
               (make-array (1+ (- 143 0)) :initial-element 8)
               (make-array (1+ (- 255 144)) :initial-element 9)
               (make-array (1+ (- 279 256)) :initial-element 7)
               (make-array (1+ (- 287 280)) :initial-element 8)))

(defparameter *fixed-dist-table*
  (coerce (make-array 32 :initial-element 5) 'code-table-type))

(defun build-tree-part (tree tree-offset table type start end
                        scratch
                        extra-bits)
  (declare (type (and fixnum unsigned-byte) tree-offset start end)
           (type code-table-type table extra-bits)
           (optimize speed))
  (assert (typep scratch 'huffman-tree))
  ;; # of entries of each bit size
  (let* ((counts (let ((a (make-array 16 :element-type '(unsigned-byte 11)
                                      :initial-element 0)))
                   (loop for x from start below end
                      for i = (aref table x)
                      do (incf (aref a i)))
                   (loop for s fixnum = 1 then (ash s 1)
                      for c across a
                      for i from 0 below 16
                      unless (zerop i)
                      do (if (> c s)
                             (error "too many entries in huffman table with bit length ~s: ~s/~s." i c s)
                             (decf s c))
                      finally (when (and (plusp s)
                                         (< 1 (- (- end start)
                                                 (aref a 0))))
                                (error "incomplete huffman table ~s~%" s)))
                   (setf (aref a 0) 0)
                   a))
         ;; first position of each used bit size
         (offsets (let ((c 0))
                    (declare (type (unsigned-byte 11) c))
                    (map '(simple-array (unsigned-byte 11) (16))
                         (lambda (a)
                           (prog1
                               (if (zerop a) 0 c)
                             (incf c a)))
                         counts)))
         ;; first code of each used bit size
         (code-offsets (let ((c 0))
                         (declare (type (unsigned-byte 17) c))
                         (map '(simple-array (unsigned-byte 16) (16))
                              (lambda (a)
                                (prog1
                                    (if (zerop a) 0 c)
                                  (setf c (ash (+ c a) 1))))
                              counts)))
         ;; range of bit sizes used
         (min (position-if-not 'zerop counts))
         ;; max # of bits needed to read entry + extra bits for this tree
         (max-bits (+ (or (position-if-not 'zerop counts :from-end t) 0)
                      (ecase type
                        (:dist 13)
                        (:lit/len 5)
                        (:dht-len 7))))
         ;; temp space for sorting table
         (terminals scratch))
    (declare (type (or null (unsigned-byte 4)) min)
             (type (simple-array (unsigned-byte 11) (16)) counts)
             (dynamic-extent counts offsets code-offsets))
    (unless min
      (return-from build-tree-part (values 0 0 0)))
    ;; sort table/allocate codes
    (loop with offset-tmp = (copy-seq offsets)
       for i fixnum from 0
       for to fixnum from start below end
       for l = (aref table to)
       for nodes of-type (simple-array (unsigned-byte 16) 1)
         = (ht-nodes terminals)
       for o = (aref offset-tmp l)
       for co = (aref code-offsets l)
       when (plusp l)
       do (incf (aref offset-tmp l))
         (cond
           ((member type '(:dist :dht-len))
            (setf (aref nodes o)
                  (if (<= i 29)
                      (ht-dist-node i extra-bits)
                      ;; codes above 29 aren't used
                      (ht-invalid-node))))
           ((> i +lengths-end+)
            (setf (aref nodes o) (ht-invalid-node)))
           ((>= i +lengths-start+)
            (setf (aref nodes o) (ht-len-node i extra-bits)))
           ((= i +end-code+)
            (setf (aref nodes o) (ht-end-node)))
           (t
            (setf (aref nodes o) (ht-literal-node i)))))

    ;; fill tree:
    (let ((next-subtable tree-offset))
      (declare (type (unsigned-byte 12) next-subtable))
      (labels ((next-len (l)
                 (position-if #'plusp counts :start l))
               (subtable (prefix prefix-bits)
                 (declare (ignorable prefix))
                 (or
                  (loop for entry-bits = (if (zerop (aref counts prefix-bits))
                                             (next-len prefix-bits)
                                             prefix-bits)
                     while entry-bits
                     if (= prefix-bits entry-bits)
                     return (prog1 (aref (ht-nodes terminals)
                                         (aref offsets entry-bits))
                              (incf (aref offsets entry-bits))
                              (decf (aref counts entry-bits)))
                     else
                     return (let ((start next-subtable)
                                  (b  (- entry-bits prefix-bits)))
                              (declare (type (unsigned-byte 16) b))
                              (incf next-subtable (expt 2 b))
                              (loop for i below (expt 2 b)
                                 do (setf (aref (ht-nodes tree)
                                                (+ start (bit-rev i b)))
                                          (subtable i entry-bits)))
                              (values (ht-link-node b start))))
                  (ht-invalid-node))))
        (incf next-subtable (expt 2 min))
        (loop for i below (expt 2 min)
           do (setf (aref (ht-nodes tree)
                          (+ tree-offset (bit-rev i min)))
                    (subtable i min))))
      (values next-subtable min max-bits))))



#++
(defun build-tree (tree lit/len dist)
  (declare (optimize speed)
           (type code-table-type lit/len dist))
  (multiple-value-bind (count bits)
      (build-tree-part tree 0 lit/len :lit/len 0 (length lit/len)
                       (make-huffman-tree)
                       +extra-bits+)
    (setf (ht-len-start-bits tree) bits)
    (setf (ht-dist-offset tree) count)
    (setf (ht-dist-start-bits tree)
          (nth-value 1 (build-tree-part tree count dist :dist
                                        0 (length dist)
                                        (make-huffman-tree)
                                        +extra-bits+)))))
#++
(defun build-tree* (tree lit/len/dist mid end scratch)
  (declare (optimize speed)
           (type (vector (unsigned-byte 4)) lit/len/dist)
           (type (and unsigned-byte fixnum) mid))
  (multiple-value-bind (count bits)
      (build-tree-part tree 0 lit/len/dist :lit/len 0 mid scratch +extra-bits+)
    (setf (ht-len-start-bits tree) bits)
    (setf (ht-dist-offset tree) count)
    (setf (ht-dist-start-bits tree)
          (nth-value 1 (build-tree-part tree count
                                        lit/len/dist :dist
                                        mid end
                                        scratch
                                        +extra-bits+)))
    #++(dump-tree tree)))

(defun build-trees (ltree dtree lit/len dist)
  (declare (optimize speed)
           (type code-table-type lit/len dist))
  (multiple-value-bind (count bits max)
      (build-tree-part ltree 0 lit/len :lit/len 0 (length lit/len)
                       (make-huffman-tree) +extra-bits+)
    (declare (ignore count))
    (setf (ht-start-bits ltree) bits)
    (setf (ht-max-bits ltree) max)
    (multiple-value-bind (count bits max)
        (build-tree-part dtree 0 dist :dist 0 (length dist)
                         (make-huffman-tree)
                         +extra-bits+)
      (declare (ignore count))
      (setf (ht-start-bits dtree) bits)
      (setf (ht-max-bits dtree) max))
    #++(dump-tree tree)))

(defun build-trees* (ltree dtree lit/len/dist mid end scratch)
  (declare (optimize speed)
           (type (vector (unsigned-byte 4)) lit/len/dist)
           (type (and unsigned-byte fixnum) mid))
  (multiple-value-bind (count bits max)
      (build-tree-part ltree 0 lit/len/dist :lit/len 0 mid scratch +extra-bits+)
    (declare (ignore count))
    (setf (ht-start-bits ltree) bits)
    (setf (ht-max-bits ltree) max)
    (multiple-value-bind (count bits max)
        (build-tree-part dtree 0 lit/len/dist :dist mid end
                         scratch +extra-bits+)
      (declare (ignore count))
      (setf (ht-start-bits dtree) bits)
      (setf (ht-max-bits dtree) max))
    #++(dump-tree tree)))



#++
(defun dump-tree (tree &key bits base (depth 0))
  (cond
    ((and bits base)
     (loop for i below (expt 2 bits)
           for node = (aref (ht-nodes tree) (+ i base))
           do (format *debug-io* "~a~4,' d: ~a~%"
                      (make-string depth :initial-element #\~)
                      i
                      (ecase (ht-node-type node)
                        (#.+ht-literal+ (list :literal (ht-value node)))
                        (#.+ht-link/end+
                         (if (ht-endp node) :end
                             (list :link
                                   :bits (ht-link-bits node)
                                   :offset (ht-link-offset node))))
                        (#.+ht-len/dist+
                         (let ((v  (ht-value node)))
                           (list :len/dist v
                                 (when (> v +lengths-extra-bits-offset+)
                                   (+ v
                                      +lengths-start+
                                      (- +lengths-extra-bits-offset+)))
                                 :start (aref +len/dist-bases+ v)
                                 :end (+ (aref +len/dist-bases+ v)
                                         (1- (expt 2 (aref +extra-bits+ v)))))))
                        (#.+ht-invalid+ :invalid)))
              (when (and (ht-linkp node)
                         (not (or (ht-endp node)
                                  (ht-invalidp node))))
                (dump-tree tree :bits (ht-link-bits node)
                                :base (ht-link-offset node)
                                :depth (+ depth 2)))))
    (t
     (format *debug-io* "lit/len table:~%")
     (dump-tree tree :bits (ht-len-start-bits tree)
                     :base 0 :depth 1)
     (format *debug-io* "distance table:~%")
     (when (plusp (ht-dist-start-bits tree))
       (dump-tree tree :bits (ht-dist-start-bits tree)
                       :base (ht-dist-offset tree)
                       :depth 1)))))

