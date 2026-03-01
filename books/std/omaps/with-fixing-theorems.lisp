; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection emptyp-fix
  :extension emptyp
  (defcong mequiv equal (emptyp map) 1
    :hints (("Goal" :in-theory (enable emptyp)))))

(defsection head-fix
  :extension head
  (defcong mequiv equal (head map) 1
    :hints (("Goal" :in-theory (enable head)))))

(defsection tail-fix
  :extension tail
  (defcong mequiv equal (tail map) 1
    :hints (("Goal" :in-theory (enable tail)))))

(defsection update-fix
  :extension update
  (defcong mequiv equal (update key val map) 3
    :hints (("Goal" :induct t
                    :in-theory (enable update)))))

(defsection update*-fix
  :extension update*
  (defcong mequiv equal (update* new old) 1
    :hints (("Goal" :induct t
                    :in-theory (enable update*))))

  (defcong mequiv equal (update* new old) 2
    :hints (("Goal" :induct t
                    :in-theory (enable update*)))))

(defsection delete-fix
  :extension delete
  (defcong mequiv equal (delete key map) 2
    :hints (("Goal" :induct t
                    :in-theory (enable delete)))))

(defsection delete*-fix
  :extension delete*
  (defcong mequiv equal (delete* keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (enable delete*)))))

(defsection assoc-fix
  :extension assoc
  (defcong mequiv equal (assoc key map) 2
    :hints (("Goal" :induct t
                    :in-theory (enable assoc)))))

(defsection in*-fix
  :extension in*
  (defcong mequiv equal (in* keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (in*) (mequiv))))))

(defsection list-in-fix
  :extension list-in
  (defruled list-in-of-true-list-fix
    (equal (list-in (true-list-fix keys) map)
           (list-in keys map))
    :induct t
    :enable (list-in
             true-list-fix))

  (defcong list-equiv equal (list-in keys map) 1
    :hints (("Goal" :in-theory (enable list-equiv)
                    :use ((:instance list-in-of-true-list-fix
                                     (keys keys))
                          (:instance list-in-of-true-list-fix
                                     (keys keys-equiv))))))

  (defcong mequiv equal (list-in keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (list-in) (mequiv))))))

(defsection list-notin-fix
  :extension list-notin
  (defruled list-notin-of-true-list-fix
    (equal (list-notin (true-list-fix keys) map)
           (list-notin keys map))
    :induct t
    :enable (list-notin
             true-list-fix))

  (defcong list-equiv equal (list-notin keys map) 1
    :hints (("Goal" :in-theory (enable list-equiv)
                    :use ((:instance list-notin-of-true-list-fix
                                     (keys keys))
                          (:instance list-notin-of-true-list-fix
                                     (keys keys-equiv))))))

  (defcong mequiv equal (list-notin keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (list-notin) (mequiv))))))

(defsection lookup-fix
  :extension lookup
  (defcong mequiv equal (lookup key map) 2
    :hints (("Goal" :in-theory (e/d (lookup) (mequiv))))))

(defsection lookup*-fix
  :extension lookup*
  (defcong mequiv equal (lookup* keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (lookup*) (mequiv))))))

(defsection list-lookup-fix
  :extension list-lookup
  (defruled list-lookup-of-true-list-fix
    (equal (list-lookup (true-list-fix keys) map)
           (list-lookup keys map))
    :induct t
    :enable (list-lookup
             true-list-fix))

  (defcong list-equiv equal (list-lookup keys map) 1
    :hints (("Goal" :in-theory (enable list-equiv)
                    :use ((:instance list-lookup-of-true-list-fix
                                     (keys keys))
                          (:instance list-lookup-of-true-list-fix
                                     (keys keys-equiv))))))

  (defcong mequiv equal (list-lookup keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (list-lookup) (mequiv))))))

(defsection rlookup-fix
  :extension rlookup
  (defcong mequiv equal (rlookup val map) 2
    :hints (("Goal" :induct t
                    :in-theory (enable rlookup)))))

(defsection rlookup*-fix
  :extension rlookup*
  (defcong mequiv equal (rlookup* vals map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (rlookup*) (mequiv))))))

(defsection restrict-fix
  :extension restrict
  (defcong mequiv equal (restrict keys map) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (restrict) (mequiv))))))

(defsection keys-fix
  :extension keys
  (defcong mequiv equal (keys map) 1
    :hints (("Goal" :induct t
                    :in-theory (e/d (keys) (mequiv))))))

(defsection values-fix
  :extension values
  (defcong mequiv equal (values map) 1
    :hints (("Goal" :induct t
                    :in-theory (e/d (values) (mequiv))))))

(defsection compatiblep-fix
  :extension compatiblep
  (defcong mequiv equal (compatiblep map1 map2) 1
    :hints (("Goal" :induct t
                    :in-theory (e/d (compatiblep) (mequiv)))))

  (defcong mequiv equal (compatiblep map1 map2) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (compatiblep) (mequiv))))))

(defsection submap-fix
  :extension submap
  (defcong mequiv equal (submap sub sup) 1
    :hints (("Goal" :induct t
                    :in-theory (e/d (submap) (mequiv)))))

  (defcong mequiv equal (submap sub sup) 2
    :hints (("Goal" :induct t
                    :in-theory (e/d (submap) (mequiv))))))

(defsection size-fix
  :extension size
  (defcong mequiv equal (size map) 1
    :hints (("Goal" :induct t
                    :in-theory (e/d (size) (mequiv))))))
