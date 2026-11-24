; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/hash-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "../../internal/keys-defs")
(include-book "../../internal/lookup-defs")
(include-book "../../internal/split-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")
(include-book "zip-side-defs")
(include-book "zip-seek-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/hash" :dir :system))
(local (include-book "kestrel/data/tset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "../../internal/keys"))
(local (include-book "../../internal/lookup"))
(local (include-book "../../internal/in-order"))
(local (include-book "../../internal/split"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))
(local (include-book "zip-side"))
(local (include-book "zip-seek"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-while-lower
  (key
   (hash (unsigned-byte-p 32 hash))
   (zip zipp))
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  :returns (zip$ zipp)
  :short "Move the focus up for as long as its parent is below a key in the
          heap order."
  :long
  (xdoc::topstring
   (xdoc::p
     "This finds the subtree which a new node for the key would sit on top
      of.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus. Over
      a @(see tmap), the expected number of moves is constant."))
  (let ((path (zip->path zip)))
    (if (acl2::endp path)
        (zip-fix zip)
      (let ((elem (zip-frame->elem (first path))))
        (if (heap<-with-hashes (tree-element->key elem)
                               key
                               (tree-element->hash elem)
                               hash)
            (zip-ascend-while-lower key hash (zip-ascend-one zip))
          (zip-fix zip)))))
  :measure (len (zip->path zip))
  :guard-hints (("Goal" :in-theory (enable data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-ascend-while-lower-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-ascend-while-lower key hash zip0)
                  (zip-ascend-while-lower key hash zip1)))
  :rule-classes :congruence
  :expand ((zip-ascend-while-lower key hash zip0)
           (zip-ascend-while-lower key hash zip1)))

(defrule zip-plug-of-zip-ascend-while-lower
  (equal (zip-plug (zip-ascend-while-lower key hash zip))
         (zip-plug zip))
  :induct t
  :enable zip-ascend-while-lower)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-update-hole-loop
  (key
   (hash (unsigned-byte-p 32 hash))
   val
   (focus treep)
   (path zip-frame-listp))
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  :short "Move up as @(tsee zip-ascend-while-lower) does, from a focus and a
          path, and put a new node for the entry on top of the subtree
          reached."
  :long
  (xdoc::topstring-p
    "This is the form of @(tsee zip-update-hole) to execute. It builds a
     single zipper, at the end.")
  (mbe :logic (let ((zip (zip-ascend-while-lower key hash (zip focus path))))
                (mv-let (assoc left right)
                        (tree-split key (zip->focus zip))
                  (declare (ignore assoc))
                  (zip (tree-node (tree-element (hash key) key val) left right)
                       (zip->path zip))))
       :exec (if (and (consp path)
                      (let ((elem (zip-frame->elem (first path))))
                        (heap<-with-hashes (tree-element->key elem)
                                           key
                                           (tree-element->hash elem)
                                           hash)))
                 (zip-update-hole-loop key
                                       hash
                                       val
                                       (zip-frame-plug (first path) focus)
                                       (rest path))
               (mv-let (assoc left right)
                       (tree-split key focus)
                 (declare (ignore assoc))
                 (zip (tree-node (tree-element hash key val) left right)
                      path))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-update-hole-loop
                                           zip-ascend-one
                                           data::u32-equal)
                        :expand ((zip-ascend-while-lower
                                   key (hash key) (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-update-hole
  (key
   val
   (zip zipp))
  :guard (tree-empty-p (zip->focus zip))
  :returns (zip$ zipp)
  :short "Add an entry at the hole the zipper is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The key is assumed to belong at the hole: above every key before it and
      below every key after it. The new node goes above the nodes below it in
      the heap order, whose subtree is split around the key to make its
      children. The zipper is left at the new node.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the hole. Over
      a @(see tmap), the expected time is constant, aside from hashing the
      key."))
  (mbe :logic (let* ((hash (hash key))
                     (zip (zip-ascend-while-lower key hash zip)))
                (mv-let (assoc left right)
                        (tree-split key (zip->focus zip))
                  (declare (ignore assoc))
                  (zip (tree-node (tree-element hash key val) left right)
                       (zip->path zip))))
       :exec (zip-update-hole-loop key
                                   (hash key)
                                   val
                                   (zip->focus zip)
                                   (zip->path zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-update-hole-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-update-hole key val zip0)
                  (zip-update-hole key val zip1)))
  :rule-classes :congruence
  :enable zip-update-hole)

(defrule tree-empty-p-of-focus-of-zip-update-hole
  (not (tree-empty-p (zip->focus (zip-update-hole key val zip))))
  :enable zip-update-hole)

(defrule zip-key-of-zip-update-hole
  (equal (zip-key (zip-update-hole key val zip))
         key)
  :enable (zip-update-hole
           zip-key))

(defrule zip-val-of-zip-update-hole
  (equal (zip-val (zip-update-hole key val zip))
         val)
  :enable (zip-update-hole
           zip-val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The ascent keeps the key bracketed by the path.

(defrulel zip-path-brackets-p-of-path-of-zip-ascend-while-lower
  (implies (zip-path-brackets-p x (zip->path zip))
           (zip-path-brackets-p x (zip->path
                                    (zip-ascend-while-lower key hash zip))))
  :induct (zip-ascend-while-lower key hash zip)
  :enable (zip-ascend-while-lower
           zip-path-brackets-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The ascent stops under a frame which is above the key in the heap order, and
;; everything it has passed is below the key.

(defrulel heapp-of-focus-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip->focus zip)))
  :enable zip-plug)

(defrulel heap<-all-l-of-focus-of-zip-ascend-while-lower
  (implies (and (heapp (zip-plug zip))
                (heap<-all-l (zip->focus zip) key))
           (heap<-all-l (zip->focus (zip-ascend-while-lower key hash zip))
                        key))
  :induct (zip-ascend-while-lower key hash zip)
  :enable (zip-ascend-while-lower
           zip-frame-plug
           heap<-all-l-weaken)
  :hints ('(:use (:instance heapp-of-focus-when-heapp-of-zip-plug
                            (zip (zip-ascend-one zip))))))

(defrulel not-heap<-of-first-frame-of-zip-ascend-while-lower
  (implies (consp (zip->path (zip-ascend-while-lower key hash zip)))
           (not (heap< (tree-element->key
                         (zip-frame->elem
                           (car (zip->path
                                  (zip-ascend-while-lower key hash zip)))))
                       key)))
  :induct (zip-ascend-while-lower key hash zip)
  :enable zip-ascend-while-lower)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Replacing the focus by a tree with one more key keeps the order invariant,
;; when the path brackets the key.

(defruledl bstp-of-zip-path-plug-when-subset-of-insert
  (implies (and (bstp (zip-path-plug path tree))
                (bstp new)
                (zip-path-brackets-p key path)
                (tset::subset (tree-key-set new)
                              (tset::insert key (tree-key-set tree))))
           (bstp (zip-path-plug path new)))
  :induct (zip-path-plug-bi-induction path tree new)
  :expand ((zip-path-plug path tree)
           (zip-path-plug path new))
  :enable ((:induction zip-path-plug-bi-induction)
           zip-frame-plug
           zip-path-brackets-p
           <<-all-l-when-subset-of-insert-of-tree-key-set
           <<-all-r-when-subset-of-insert-of-tree-key-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Likewise for the heap invariant, when every frame of the path is above the
;; key in the heap order. In a heap, that holds of a whole path once it holds
;; of its first frame.

(local
  (define zip-path-heap-above-p
    (key
     (path zip-frame-listp))
    :returns (yes/no booleanp :rule-classes :type-prescription)
    :verify-guards nil
    (or (acl2::endp path)
        (and (heap< key (tree-element->key (zip-frame->elem (first path))))
             (zip-path-heap-above-p key (rest path))))))

(defruledl zip-path-heap-above-p-when-heap<-of-head
  (implies (and (heapp (zip-path-plug path tree))
                (not (tree-empty-p tree))
                (heap< key (tree-element->key (tree->head tree))))
           (zip-path-heap-above-p key path))
  :induct (zip-path-plug path tree)
  :expand ((zip-path-plug path tree))
  :enable ((:induction zip-path-plug)
           zip-frame-plug
           zip-path-heap-above-p
           heap<-rules))

(defruledl zip-path-heap-above-p-when-heap<-of-first-frame
  (implies (and (heapp (zip-path-plug path tree))
                (consp path)
                (heap< key (tree-element->key (zip-frame->elem (car path)))))
           (zip-path-heap-above-p key path))
  :use (:instance zip-path-heap-above-p-when-heap<-of-head
                  (path (cdr path))
                  (tree (zip-frame-plug (car path) tree)))
  :expand ((zip-path-plug path tree))
  :enable (zip-frame-plug
           zip-path-heap-above-p))

(defruledl heapp-of-zip-path-plug-when-subset-of-insert
  (implies (and (heapp (zip-path-plug path tree))
                (heapp new)
                (zip-path-heap-above-p key path)
                (tset::subset (tree-key-set new)
                              (tset::insert key (tree-key-set tree))))
           (heapp (zip-path-plug path new)))
  :induct (zip-path-plug-bi-induction path tree new)
  :expand ((zip-path-plug path tree)
           (zip-path-plug path new))
  :enable ((:induction zip-path-plug-bi-induction)
           zip-frame-plug
           zip-path-heap-above-p
           heap<-all-l-when-subset-of-insert-of-tree-key-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The keys and values of a plugged tree, read off the entries around the
;; focus.

(defruledl in-of-tree-key-set-of-zip-path-plug
  (equal (tset::in x (tree-key-set (zip-path-plug path tree)))
         (if (assoc-equal x (zip-path-before path))
             t
           (if (tset::in x (tree-key-set tree))
               t
             (and (assoc-equal x (zip-path-after path))
                  t))))
  :use ((:instance in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order
                   (key x)
                   (tree (zip-path-plug path tree)))
        (:instance in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order
                   (key x))))

(defruledl tree-lookup-of-zip-path-plug
  (implies (bstp (zip-path-plug path tree))
           (equal (tree-lookup x (zip-path-plug path tree))
                  (if (assoc-equal x (zip-path-before path))
                      (cdr (assoc-equal x (zip-path-before path)))
                    (if (tset::in x (tree-key-set tree))
                        (tree-lookup x tree)
                      (cdr (assoc-equal x (zip-path-after path)))))))
  :use ((:instance assoc-equal-of-tree-in-order-when-bstp
                   (key x)
                   (tree (zip-path-plug path tree)))
        (:instance in-of-tree-key-set-of-zip-path-plug)))

;; In a search tree, no key of a plugged tree is also bound before it.

(defruledl not-assoc-equal-of-zip-path-before-when-in-of-tree-key-set
  (implies (and (bstp (zip-path-plug path tree))
                (tset::in key (tree-key-set tree)))
           (not (assoc-equal key (zip-path-before path))))
  :use ((:instance omapp-of-tree-in-order-when-bstp
                   (tree (zip-path-plug path tree)))
        (:instance in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order))
  :enable data::not-assoc-equal-of-prefix-when-omapp-of-append
  :disable omapp-of-tree-in-order-when-bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The new node, plugged in place of the tree it was split from, adds its key
;; and changes nothing else.

(defruledl in-of-tree-key-set-of-zip-path-plug-of-new-node
  (implies (bstp (zip-path-plug path tree))
           (equal (tset::in x
                            (tree-key-set
                              (zip-path-plug
                                path
                                (tree-node (tree-element hash key val)
                                           (mv-nth 1 (tree-split key tree))
                                           (mv-nth 2 (tree-split key tree))))))
                  (or (equal x key)
                      (tset::in x (tree-key-set (zip-path-plug path tree))))))
  :enable (in-of-tree-key-set-of-zip-path-plug
           data::<<-rules))

(defruledl tree-lookup-of-zip-path-plug-of-new-node
  (implies (and (bstp (zip-path-plug path tree))
                (bstp (zip-path-plug
                        path
                        (tree-node (tree-element hash key val)
                                   (mv-nth 1 (tree-split key tree))
                                   (mv-nth 2 (tree-split key tree))))))
           (equal (tree-lookup x
                               (zip-path-plug
                                 path
                                 (tree-node (tree-element hash key val)
                                            (mv-nth 1 (tree-split key tree))
                                            (mv-nth 2 (tree-split key tree)))))
                  (if (equal x key)
                      val
                    (tree-lookup x (zip-path-plug path tree)))))
  :enable (tree-lookup-of-zip-path-plug
           in-of-tree-key-set-of-zip-path-plug
           not-assoc-equal-of-zip-path-before-when-in-of-tree-key-set
           data::<<-rules))

(defruledl subset-of-tree-key-set-of-new-node
  (implies (bstp tree)
           (tset::subset
             (tree-key-set (tree-node (tree-element hash key val)
                                      (mv-nth 1 (tree-split key tree))
                                      (mv-nth 2 (tree-split key tree))))
             (tset::insert key (tree-key-set tree))))
  :enable tset::pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; So, at a hole whose path brackets the key, adding the entry keeps the
;; invariants of the whole tree and adds just that entry.

(defrulel zip-path-plug-of-path-and-focus
  (equal (zip-path-plug (zip->path zip) (zip->focus zip))
         (zip-plug zip))
  :enable zip-plug)

(defrulel bstp-of-focus-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip->focus zip)))
  :enable zip-plug
  :disable zip-path-plug-of-path-and-focus)

(defruledl bstp-of-zip-plug-of-zip-update-hole-when-brackets
  (implies (and (bstp (zip-plug zip))
                (zip-path-brackets-p key (zip->path zip)))
           (bstp (zip-plug (zip-update-hole key val zip))))
  :use (:instance
         bstp-of-zip-path-plug-when-subset-of-insert
         (path (zip->path (zip-ascend-while-lower key (hash key) zip)))
         (tree (zip->focus (zip-ascend-while-lower key (hash key) zip)))
         (new (tree-node
                (tree-element (hash key) key val)
                (mv-nth 1 (tree-split
                            key
                            (zip->focus
                              (zip-ascend-while-lower key (hash key) zip))))
                (mv-nth 2 (tree-split
                            key
                            (zip->focus
                              (zip-ascend-while-lower key (hash key) zip)))))))
  :enable (zip-update-hole
           subset-of-tree-key-set-of-new-node))

(defruledl heapp-of-zip-plug-of-zip-update-hole-when-brackets
  (implies (and (heapp (zip-plug zip))
                (bstp (zip-plug zip))
                (tree-empty-p (zip->focus zip))
                (zip-path-brackets-p key (zip->path zip)))
           (heapp (zip-plug (zip-update-hole key val zip))))
  :use ((:instance
          heapp-of-zip-path-plug-when-subset-of-insert
          (path (zip->path (zip-ascend-while-lower key (hash key) zip)))
          (tree (zip->focus (zip-ascend-while-lower key (hash key) zip)))
          (new (tree-node
                 (tree-element (hash key) key val)
                 (mv-nth 1 (tree-split
                             key
                             (zip->focus
                               (zip-ascend-while-lower key (hash key) zip))))
                 (mv-nth 2 (tree-split
                             key
                             (zip->focus
                               (zip-ascend-while-lower key (hash key) zip)))))))
        (:instance
          zip-path-heap-above-p-when-heap<-of-first-frame
          (path (zip->path (zip-ascend-while-lower key (hash key) zip)))
          (tree (zip->focus (zip-ascend-while-lower key (hash key) zip))))
        (:instance
          zip-path-brackets-p-of-path-of-zip-ascend-while-lower
          (x key)
          (hash (hash key)))
        (:instance
          tset::heap<-trichotomy
          (x key)
          (y (tree-element->key
               (zip-frame->elem
                 (car (zip->path
                        (zip-ascend-while-lower key (hash key) zip))))))))
  :expand ((zip-path-brackets-p
             key
             (zip->path (zip-ascend-while-lower key (hash key) zip))))
  :enable (zip-update-hole
           zip-path-heap-above-p
           subset-of-tree-key-set-of-new-node
           heap<-all-l-of-tree-split.left-when-heap<-all-l
           heap<-all-l-of-tree-split.right-when-heap<-all-l
           heap<-all-l-when-tree-empty-p
           heap<-rules
           data::<<-rules)
  :disable zip-path-brackets-p-of-path-of-zip-ascend-while-lower)

(defruledl in-of-tree-key-set-of-zip-plug-of-zip-update-hole-when-bstp
  (implies (bstp (zip-plug zip))
           (equal (tset::in x (tree-key-set
                                (zip-plug (zip-update-hole key val zip))))
                  (or (equal x key)
                      (tset::in x (tree-key-set (zip-plug zip))))))
  :use (:instance
         in-of-tree-key-set-of-zip-path-plug-of-new-node
         (hash (hash key))
         (path (zip->path (zip-ascend-while-lower key (hash key) zip)))
         (tree (zip->focus (zip-ascend-while-lower key (hash key) zip))))
  :enable zip-update-hole)

(defruledl tree-lookup-of-zip-plug-of-zip-update-hole-when-brackets
  (implies (and (bstp (zip-plug zip))
                (zip-path-brackets-p key (zip->path zip)))
           (equal (tree-lookup x (zip-plug (zip-update-hole key val zip)))
                  (if (equal x key)
                      val
                    (tree-lookup x (zip-plug zip)))))
  :use ((:instance
          tree-lookup-of-zip-path-plug-of-new-node
          (hash (hash key))
          (path (zip->path (zip-ascend-while-lower key (hash key) zip)))
          (tree (zip->focus (zip-ascend-while-lower key (hash key) zip))))
        bstp-of-zip-plug-of-zip-update-hole-when-brackets)
  :enable zip-update-hole)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A search for a key which is not in the tree ends at such a hole.

(defrule bstp-of-zip-plug-of-zip-update-hole-of-zip-seek
  (implies (bstp tree)
           (bstp (zip-plug (zip-update-hole key
                                            val
                                            (zip-seek key (zip-root tree))))))
  :enable (bstp-of-zip-plug-of-zip-update-hole-when-brackets
           zip-path-brackets-p))

(defrule heapp-of-zip-plug-of-zip-update-hole-of-zip-seek
  (implies (and (bstp tree)
                (heapp tree)
                (not (tset::in key (tree-key-set tree))))
           (heapp (zip-plug (zip-update-hole key
                                             val
                                             (zip-seek key (zip-root tree))))))
  :enable (heapp-of-zip-plug-of-zip-update-hole-when-brackets
           zip-path-brackets-p))

(defrule in-of-tree-key-set-of-zip-plug-of-zip-update-hole-of-zip-seek
  (implies (bstp tree)
           (equal (tset::in x
                            (tree-key-set
                              (zip-plug
                                (zip-update-hole
                                  key
                                  val
                                  (zip-seek key (zip-root tree))))))
                  (or (equal x key)
                      (tset::in x (tree-key-set tree)))))
  :enable in-of-tree-key-set-of-zip-plug-of-zip-update-hole-when-bstp)

(defrule tree-lookup-of-zip-plug-of-zip-update-hole-of-zip-seek
  (implies (bstp tree)
           (equal (tree-lookup x
                               (zip-plug
                                 (zip-update-hole
                                   key
                                   val
                                   (zip-seek key (zip-root tree)))))
                  (if (equal x key)
                      val
                    (tree-lookup x tree))))
  :enable (tree-lookup-of-zip-plug-of-zip-update-hole-when-brackets
           zip-path-brackets-p))
