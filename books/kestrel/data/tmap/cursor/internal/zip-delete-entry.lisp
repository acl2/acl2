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

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/join-defs")
(include-book "../../internal/delete-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-side-defs")
(include-book "zip-seek-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/join"))
(local (include-book "../../internal/delete"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-side"))
(local (include-book "zip-seek"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-delete-entry ((zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Remove the element the zipper is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The children of the focus are joined in its place, as in @(tsee
      tree-delete), and the path is untouched. The zipper is then moved down
      to the hole where the element was, between the two children. Logically,
      a zipper at a hole is left as it is.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of that hole below
      the focus. Over a @(see tmap), the expected time is constant."))
  (let ((focus (zip->focus zip)))
    (if (mbt (not (tree-empty-p focus)))
        (zip-seek (tree-element->key (tree->head focus))
                  (zip (tree-join (tree->left focus)
                                  (tree->right focus))
                       (zip->path zip)))
      (zip-fix zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-delete-entry-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-delete-entry zip0)
                  (zip-delete-entry zip1)))
  :rule-classes :congruence
  :enable zip-delete-entry)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A deletion of a key which a path brackets happens within the focus.

(defruledl tree-delete-of-zip-frame-plug
  (implies (if (zip-frame->from-left frame)
               (<< key (tree-element->key (zip-frame->elem frame)))
             (<< (tree-element->key (zip-frame->elem frame)) key))
           (equal (tree-delete key (zip-frame-plug frame tree))
                  (zip-frame-plug frame (tree-delete key tree))))
  :enable (zip-frame-plug
           tree-delete
           data::<<-rules))

(defruled tree-delete-of-zip-path-plug
  (implies (zip-path-brackets-p key path)
           (equal (tree-delete key (zip-path-plug path tree))
                  (zip-path-plug path (tree-delete key tree))))
  :induct (zip-path-plug path tree)
  :enable (zip-path-plug
           zip-path-brackets-p
           tree-delete-of-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;

;; So removing the element at the focus is a deletion from the whole tree,
;; followed by a search for the hole it leaves.

(defruled zip-delete-entry-becomes-zip-seek-of-zip-root-of-tree-delete
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (zip-delete-entry zip)
                  (zip-seek (zip-key zip)
                            (zip-root (tree-delete (zip-key zip)
                                                   (zip-plug zip))))))
  :use ((:instance zip-seek-of-zip-root-of-zip-plug
                   (x (zip-key zip))
                   (zip (zip (tree-join (tree->left (zip->focus zip))
                                        (tree->right (zip->focus zip)))
                             (zip->path zip))))
        (:instance tree-delete-of-zip-path-plug
                   (key (zip-key zip))
                   (path (zip->path zip))
                   (tree (zip->focus zip)))
        zip-path-brackets-p-of-zip-key-and-path)
  :expand ((tree-delete (tree-element->key (tree->head (zip->focus zip)))
                        (zip->focus zip)))
  :enable (zip-delete-entry
           zip-plug
           zip-key
           tree-join-at)
  :disable zip-path-brackets-p-of-zip-key-and-path)
