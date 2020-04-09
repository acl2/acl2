; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/crypto/interfaces/keccak-256" :dir :system)
(include-book "kestrel/utilities/defmax-nat/implementation" :dir :system)
(include-book "kestrel/utilities/lists/take-theorems" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/lists/prefixp" :dir :system)

(include-book "hex-prefix")
(include-book "rlp/encoding")
(include-book "database")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mmp-trees
  :parents (ethereum)
  :short "Modified Merkle Patricia trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Modified Merkle Patricia tree
     (which we abbreviate as `MMP tree'
     in the documentation of our Ethereum model)
     is an Ethereum data structure
     that combines characteristics of
     Merkle trees and Patricia (a.k.a. radix) trees.
     MMP trees are described in [YP:D] and in
     <a href=\"https://github.com/ethereum/wiki/wiki/Patricia-Tree\"
     >Page `Patricia Tree' of [Wiki]</a>;
     we reference that page of [Wiki] as `[Wiki:MMP]'.")
   (xdoc::p
    "MMP trees are not merely implementation-level entities.
     Their root hashes appear
     at the interface of Ethereum with the external world,
     e.g. as the <b>stateRoot</b> component of a block [YP:4.3].
     Thus, a formalization of MMP trees,
     in particular of the calculation of root hashes,
     belongs to a formal model of Ethereum
     that covers the interface to the external world,
     even if the formal model is high-level, declarative, and non-executable."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bytelist-bytelist-map
  :parents (mmp-trees)
  :short "Finite maps from byte arrays to byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a <see topic='@(url acl2::fty)'>fixtype</see> for finite maps
     from <see topic='@(url byte-arrays)'>byte arrays</see> to byte arrrays,
     based on the fixtype of <see topic='@(url omap::omaps)'>omaps</see>.")
   (xdoc::p
    "An MMP tree represents a finite map from byte arrays to byte arrays,
     as described by @($\\mathfrak{I}$) [YP:(188)].
     The type we introduce here models these finite maps.
     Note that there are no constraints on the lengths of the keys or values,
     because the construction of MMP trees from these finite maps
     (which is described in [YP:D])
     does not depend on any such length constraints."))

  (fty::defomap bytelist-bytelist-map
                :key-type byte-list
                :val-type byte-list
                :pred bytelist-bytelist-mapp
                :fix bytelist-bytelist-mfix
                :equiv bytelist-bytelist-mequiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nibblelist-bytelist-map
  :parents (mmp-trees)
  :short "Finite maps from nibble arrays to byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a <see topic='@(url acl2::fty)'>fixtype</see> for finite maps
     from <see topic='@(url nibble-arrays)'>nibble arrays</see>
     to <see topic='@(url byte-arrays)'>byte arrrays</see>,
     based on the fixtype of <see topic='@(url omap::omaps)'>omaps</see>.")
   (xdoc::p
    "This is similar to @(tsee bytelist-bytelist-map),
     but the keys of the map are nibble arrays instead of byte arrays.
     This is the type of the result of @($y$) [YP:(190), YP:(191)]."))

  (fty::defomap nibblelist-bytelist-map
                :key-type nibble-list
                :val-type byte-list
                :pred nibblelist-bytelist-mapp
                :fix nibblelist-bytelist-mfix
                :equiv nibblelist-bytelist-mequiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bytelist-to-nibblelist-keys ((map bytelist-bytelist-mapp))
  :returns (map1 nibblelist-bytelist-mapp)
  :parents (mmp-trees)
  :short "Turn (i) a finite map from byte arrays to byte arrays
          into (ii) a finite map from nibble arrays to byte arrays."
  :long
  (xdoc::topstring-p
   "This corresponds to @($y$) [YP:(190), YP:(191)].")
  (b* (((unless (mbt (bytelist-bytelist-mapp map))) nil)
       ((when (omap::empty map)) nil)
       ((mv key val) (omap::head map))
       (key (byte-list-fix key))
       (val (byte-list-fix val))
       (key1 (bytelist-to-nibblelist-keys-aux key))
       (map1 (bytelist-to-nibblelist-keys (omap::tail map))))
    (omap::update key1 val map1))
  :hooks (:fix)
  :no-function t

  :prepwork
  ((define bytelist-to-nibblelist-keys-aux ((bytes byte-listp))
     :returns (nibbles nibble-listp
                       :hints (("Goal" :in-theory (enable nibblep
                                                          bytep
                                                          byte-fix))))
     :parents (bytelist-to-nibblelist-keys)
     :short "Turn a sequence of bytes into a sequence of nibbles."
     :long
     (xdoc::topstring-p
      "This corresponds to [YP:(191)],
       but here the conversion is expressed via recursion instead of indexing.")
     (b* (((when (endp bytes)) nil)
          (byte (byte-fix (car bytes)))
          (nibble-hi (floor byte 16))
          (nibble-lo (mod byte 16))
          (nibbles (bytelist-to-nibblelist-keys-aux (cdr bytes))))
       (list* nibble-hi nibble-lo nibbles))
     :hooks (:fix)
     :no-function t
     :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))))

  :verify-guards nil ; done below
  ///
  (verify-guards bytelist-to-nibblelist-keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk mmp-encode-c-forall
  ((map nibblelist-bytelist-mapp) (x natp) (l nibble-listp))
  :returns (yes/no booleanp)
  :parents (mmp-trees)
  :short "Universally quantified formula
          in the second case of the definition of @($c$) [YP:(194)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used (indirectly) in the definition of @(tsee mmp-encode-c),
     hence the name.")
   (xdoc::p
    "Here @($\\mathfrak{I}$) is the argument @('map'),
     @($x$) is the argument @('x'),
     and @($\\mathbf{l}$) is the argument @('l').")
   (xdoc::p
    "Instead of quantifying over the pairs in the map
     and projecting their key component [YP:(189)] as in [YP:(194)],
     here we directly quantify over the keys in the map.
     The values in the map are not referenced in this formula.")
   (xdoc::p
    "If this universally quantified formula holds,
     the length of every key in the map is greater than or equal to @('x').
     The reason is that
     @('(take x key)') returns a list with some @('nil')s at the end
     if @('x') is greater than the length of @('key'),
     but the formula requires
     all the elements in that list to be nibbles instead.
     This property is used to show the existence of the maximum
     defined by @(tsee mmp-encode-c-max)."))
  (forall (key)
          (implies (omap::in key (nibblelist-bytelist-mfix map))
                   (equal (take x key) (nibble-list-fix l))))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::true-listp-when-nibble-listp-rewrite)))
  ///

  (fty::deffixequiv-sk mmp-encode-c-forall
    :args ((map nibblelist-bytelist-mapp) (x natp) (l nibble-listp)))

  (defrule mmp-encode-c-forall-len-key-geq-x
    (implies (and (mmp-encode-c-forall map x l)
                  (nibblelist-bytelist-mapp map)
                  (natp x)
                  (nibble-listp l)
                  (omap::in key map))
             (>= (len key) x))
    :rule-classes nil
    :use (mmp-encode-c-forall-necc lemma)

    :prep-lemmas
    ((defrule lemma
       (implies (and (nibble-listp l)
                     (equal (take x key) l))
                (>= (len key) (nfix x)))
       :rule-classes nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk mmp-encode-c-exists ((map nibblelist-bytelist-mapp) (x natp))
  :returns (yes/no booleanp)
  :parents (mmp-trees)
  :short "Existentially quantified formula
          in the second case of the definition of @($c$) [YP:(194)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used (indirectly) in the definition of @(tsee mmp-encode-c),
     hence the name.")
   (xdoc::p
    "Here @($\\mathfrak{I}$) is the argument @('map')
     and @($x$) is the argument @('x').")
   (xdoc::p
    "If this existentially quantified formula holds,
     the length of every key in the map is greater than or equal to @('x'),
     because this follows from
     the universally quantified formula @(tsee mmp-encode-c-forall)."))
  (exists (l)
          (and (nibble-listp l)
               (= (len l) (nfix x))
               (mmp-encode-c-forall map x l)))
  ///

  (local (in-theory (disable nfix)))

  (fty::deffixequiv-sk mmp-encode-c-exists
    :args ((map nibblelist-bytelist-mapp) (x natp)))

  (defrule mmp-encode-c-exists-len-key-geq-x
    (implies (and (mmp-encode-c-exists map x)
                  (nibblelist-bytelist-mapp map)
                  (natp x)
                  (omap::in key map))
             (>= (len key) x))
    :rule-classes nil
    :use (:instance mmp-encode-c-forall-len-key-geq-x
          (l (mmp-encode-c-exists-witness map x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nibblelist-bytelist-map-sup-len-key ((map nibblelist-bytelist-mapp))
  :returns (sup natp)
  :parents (mmp-trees)
  :short "Natural number supremum of the lenghts of the keys
          in a map from nibble arrays to byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 0 if the map is empty.
     Otherwise, it is the maximum key length.
     Thus, if we limit the values of interest to the natural numbers,
     this is the supremum of the set of the key lengths,
     i.e. the minimum upper bound.")
   (xdoc::p
    "This function,
     and its property of being greater than or equal to
     the length of every key in the map
     (expressed by the linear rule below),
     are used to prove that
     the maximum defined by @(tsee mmp-encode-c-max) exists.
     See that function for details.")
   (xdoc::p
    "When updating the map, the result of this function is the maximum of
     the length of the udpated key and the result prior to updating."))
  (b* (((unless (mbt (nibblelist-bytelist-mapp map))) 0)
       ((when (omap::empty map)) 0)
       ((mv key &) (omap::head map)))
    (max (len key)
         (nibblelist-bytelist-map-sup-len-key (omap::tail map))))
  :hooks (:fix)
  :no-function t
  ///

  (defrule nibblelist-bytelist-map-sup-len-key-geq-len-key
    (implies (and (omap::in key map) ; bind free KEY
                  (nibblelist-bytelist-mapp map))
             (>= (nibblelist-bytelist-map-sup-len-key map)
                 (len key)))
    :rule-classes :linear
    :enable omap::in)

  (defrule nibblelist-bytelist-map-sup-len-key-of-update
    (implies (and (nibble-listp key)
                  (byte-listp val)
                  (nibblelist-bytelist-mapp map))
             (equal (nibblelist-bytelist-map-sup-len-key
                     (omap::update key val map))
                    (max (nibblelist-bytelist-map-sup-len-key map)
                         (len key))))
    :hints ('(:expand ((nibblelist-bytelist-map-sup-len-key
                        (omap::update key val map)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection mmp-encode-c-max
  :parents (mmp-trees)
  :short "Value of the maximum operator
          in the second case of the definition of @($c$) [YP:(194)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the definition of @(tsee mmp-encode-c),
     hence the name.")
   (xdoc::p
    "The @($x$) in the set being maximized is a natural number,
     because it is equated to a length.
     Therefore, we use @(tsee defmax-nat) to introduce this maximum.")
   (xdoc::p
    "This maximum always exists if the map is not empty.
     We can establish this by showing that:")
   (xdoc::ol
    (xdoc::li
     "The set @($\\{x\\mid\\ldots\\}$) being maximized is never empty
      because 0 is always in the set.
      This is expressed by theorem @('mmp-encode-c-max-set-nonempty') below,
      which does not actually need the map to be non-empty.")
    (xdoc::li
     "The elements of the set cannot exceed
      the maximum length of the keys of the map,
      which is returned by @(tsee nibblelist-bytelist-map-sup-len-key).
      This is expressed by theorem @('mmp-encode-c-max-set-bounded') below.
      The reason why this theorem holds is that
      the elements of the set are
      the @('x')s that are lengths of prefixes of the keys in the map,
      which are therefore no larger than the lengths of the whole keys,
      which are no larger than their maximum.
      Here the non-emptiness of the map is needed:
      without it, @('x') could be arbitrarily large
      because there would be no keys to take the prefix of,
      @(tsee mmp-encode-c-forall) would be trivially true,
      @(tsee mmp-encode-c-exists) would be also true because
      there is always an @('l') of any length.
      Concretely, in the proof of the theorem,
      we need to instantiate the @('key') variable
      in both the linear rule of @(tsee nibblelist-bytelist-map-sup-len-key)
      and the inequality theorem about @(tsee mmp-encode-c-exists),
      which we do with the key returned by @(tsee omap::head):
      any other key in the map would have worked,
      but the point is that the map must be non-empty for a key to exist."))
   (xdoc::p
    "With these two theorems in hand,
     we use a suitable instance of the helper theorem
     @('mmp-encode-c-max.existsp-when-nonempty-and-bounded')
     generated by @(tsee defmax-nat),
     whose proof uses the two theorems as rewrite rules.")
   (xdoc::p
    "Since @(tsee nibblelist-bytelist-map-sup-len-key) is an upper bound,
     it is greater than or equal to @(tsee mmp-encode-c-max)
     and any element in the set.
     This is expressed by two additional linear rules below,
     whose hypotheses match the ones under which
     @(tsee nibblelist-bytelist-map-sup-len-key) is an upper bound.")
   (xdoc::p
    "When the map has two or more keys,
     @(tsee nibblelist-bytelist-map-sup-len-key) is a strict upper bound,
     i.e. it is not equal to any element in the set.
     This is proved below by taking the first two keys in the map,
     called @('key1') and @('key2') in the lemmas,
     and showing that:")
   (xdoc::ol
    (xdoc::li
     "The two keys differ, because they are strictly ordered in the map.")
    (xdoc::li
     "If @(tsee nibblelist-bytelist-map-sup-len-key) were an element of the set,
      then the two keys would have the same prefix,
      of length @(tsee nibblelist-bytelist-map-sup-len-key).")
    (xdoc::li
     "@(tsee nibblelist-bytelist-map-sup-len-key) is an upper bound
      of the lengths of the keys,
      by its definition.")
    (xdoc::li
     "If @(tsee nibblelist-bytelist-map-sup-len-key) were an element of the set,
      then it would also be an upper bound of the lengths of the keys,
      by the definition of the set.")
    (xdoc::li
     "If @(tsee nibblelist-bytelist-map-sup-len-key) were an element of the set,
      then by (2), (3), and (4) above it would be the length of both keys
      and thus the two keys would be equal.
      But this contradicts (1) above,
      and thus @(tsee nibblelist-bytelist-map-sup-len-key) must differ
      from any element @('i') of the set."))
   (xdoc::p
    "Every element of the set, including the maximum if it exists,
     is less than or equal to the length of every key in the map.")
   (xdoc::p
    "If the map is empty,
     then all the natural numbers are in the set."))

  (defmax-nat mmp-encode-c-max x (map)
    (mmp-encode-c-exists map x)
    :guard (nibblelist-bytelist-mapp map))

  (fty::deffixequiv mmp-encode-c-max.elementp
    :args ((map nibblelist-bytelist-mapp) (x natp))
    :hints (("Goal" :in-theory (enable mmp-encode-c-max.elementp))))

  (defrule mmp-encode-c-max.elementp-when-not-natp-x
    (implies (and (syntaxp (not (equal x ''0)))
                  (not (natp x)))
             (equal (mmp-encode-c-max.elementp map x)
                    (mmp-encode-c-max.elementp map 0)))
    :use (:instance mmp-encode-c-max.elementp-nat-equiv-congruence-on-x
          (x-equiv 0)))

  (fty::deffixequiv-sk mmp-encode-c-max.uboundp
    :args ((map nibblelist-bytelist-mapp) (x natp)))

  (fty::deffixequiv-sk mmp-encode-c-max.existsp
    :args ((map nibblelist-bytelist-mapp)))

  (defrule mmp-encode-c-max-set-nonempty
    (mmp-encode-c-max.elementp map 0)
    :enable (mmp-encode-c-max.elementp mmp-encode-c-forall)
    :use (:instance mmp-encode-c-exists-suff (x 0) (l nil)))

  (defrule mmp-encode-c-max-set-bounded
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map)))
             (mmp-encode-c-max.uboundp
              map (nibblelist-bytelist-map-sup-len-key map)))
    :enable (mmp-encode-c-max.uboundp
             mmp-encode-c-max.elementp)
    :use ((:instance mmp-encode-c-exists-len-key-geq-x
           (x (mmp-encode-c-max.uboundp-witness
               map (nibblelist-bytelist-map-sup-len-key map)))
           (key (mv-nth 0 (omap::head map))))
          (:instance nibblelist-bytelist-map-sup-len-key-geq-len-key
           (key (mv-nth 0 (omap::head map))))))

  (defrule mmp-encode-c-max-exists
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map)))
             (mmp-encode-c-max.existsp map))
    :use ((:instance mmp-encode-c-max.existsp-when-nonempty-and-bounded
           (x0 0)
           (x1 (nibblelist-bytelist-map-sup-len-key map)))))

  (defrule nibblelist-bytelist-map-sup-len-key-geq-mmp-encode-c-max
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map)))
             (>= (nibblelist-bytelist-map-sup-len-key map)
                 (mmp-encode-c-max map)))
    :rule-classes :linear)

  (defrule nibblelist-bytelist-map-sup-len-key-geq-element
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map))
                  (mmp-encode-c-max.elementp map x)) ; bind free X
             (>= (nibblelist-bytelist-map-sup-len-key map)
                 (nfix x)))
    :rule-classes :linear
    :use (:instance mmp-encode-c-max.uboundp-necc
          (x (nibblelist-bytelist-map-sup-len-key map))
          (x1 x)))

  (defrule nibblelist-bytelist-map-sup-len-key-neq-element-when-2+-keys
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map))
                  (not (equal (omap::size map) 1))
                  (natp x)
                  (mmp-encode-c-max.elementp map x))
             (not (equal (nibblelist-bytelist-map-sup-len-key map) x)))
    :use (keys-len-lower-bound keys-len-upper-bound keys-same-prefix)
    :enable acl2::true-listp-when-nibble-listp-rewrite

    :prep-lemmas

    ((defrule keys-differ
       (implies (and (not (omap::empty map))
                     (not (equal (omap::size map) 1)))
                (b* ((key1 (mv-nth 0 (omap::head map)))
                     (key2 (mv-nth 0 (omap::head (omap::tail map)))))
                  (not (equal key1 key2))))
       :enable (omap::size
                omap::empty
                omap::mfix
                omap::mapp
                omap::tail
                omap::head))

     (defrule keys-same-prefix
       (implies (and (nibblelist-bytelist-mapp map)
                     (not (omap::empty map))
                     (not (equal (omap::size map) 1))
                     (mmp-encode-c-max.elementp
                      map (nibblelist-bytelist-map-sup-len-key map)))
                (b* ((key1 (mv-nth 0 (omap::head map)))
                     (key2 (mv-nth 0 (omap::head (omap::tail map)))))
                  (equal (take (nibblelist-bytelist-map-sup-len-key map)
                               key1)
                         (take (nibblelist-bytelist-map-sup-len-key map)
                               key2))))
       :rule-classes nil
       :enable (mmp-encode-c-max.elementp
                mmp-encode-c-exists
                mmp-encode-c-forall-necc
                omap::unfold-equal-size-const))

     (defrule keys-len-lower-bound
       (implies (and (nibblelist-bytelist-mapp map)
                     (not (omap::empty map))
                     (not (equal (omap::size map) 1))
                     (mmp-encode-c-max.elementp
                      map (nibblelist-bytelist-map-sup-len-key map)))
                (b* ((key1 (mv-nth 0 (omap::head map)))
                     (key2 (mv-nth 0 (omap::head (omap::tail map)))))
                  (and (>= (len key1)
                           (nibblelist-bytelist-map-sup-len-key map))
                       (>= (len key2)
                           (nibblelist-bytelist-map-sup-len-key map)))))
       :rule-classes nil
       :use ((:instance mmp-encode-c-exists-len-key-geq-x
              (x (nibblelist-bytelist-map-sup-len-key map))
              (key (mv-nth 0 (omap::head map))))
             (:instance mmp-encode-c-exists-len-key-geq-x
              (x (nibblelist-bytelist-map-sup-len-key map))
              (key (mv-nth 0 (omap::head (omap::tail map))))))
       :enable (mmp-encode-c-max.elementp omap::unfold-equal-size-const))

     (defrule keys-len-upper-bound
       (implies (and (nibblelist-bytelist-mapp map)
                     (not (omap::empty map))
                     (not (equal (omap::size map) 1)))
                (b* ((key1 (mv-nth 0 (omap::head map)))
                     (key2 (mv-nth 0 (omap::head (omap::tail map)))))
                  (and (<= (len key1)
                           (nibblelist-bytelist-map-sup-len-key map))
                       (<= (len key2)
                           (nibblelist-bytelist-map-sup-len-key map)))))
       :rule-classes nil
       :use ((:instance nibblelist-bytelist-map-sup-len-key-geq-len-key
              (key (mv-nth 0 (omap::head map))))
             (:instance nibblelist-bytelist-map-sup-len-key-geq-len-key
              (key (mv-nth 0 (omap::head (omap::tail map))))))
       :enable omap::unfold-equal-size-const
       :disable nibblelist-bytelist-map-sup-len-key-geq-len-key)

     (defrule not-empty-tail-when-not-empty-and-size-not-1
       (implies (and (not (omap::empty map))
                     (not (equal (omap::size map) 1)))
                (not (omap::empty (omap::tail map))))
       :enable (omap::empty omap::size))))

  (defruled mmp-encode-c-max-element-leq-len-key
    (implies (and (nibblelist-bytelist-mapp map)
                  (natp x)
                  (mmp-encode-c-max.elementp map x)
                  (omap::in key map)) ; bind free KEY
             (<= x (len key)))
    :rule-classes ((:linear
                    :trigger-terms ((mmp-encode-c-max.elementp map x))))
    :enable mmp-encode-c-max.elementp
    :use mmp-encode-c-exists-len-key-geq-x)

  (defruled mmp-encode-c-max-leq-len-key
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map))
                  (omap::in key map)) ; bind free KEY
             (<= (mmp-encode-c-max map)
                 (len key)))
    :rule-classes ((:linear :trigger-terms ((mmp-encode-c-max map))))
    :use (:instance mmp-encode-c-max-element-leq-len-key
          (x (mmp-encode-c-max map)))
    :disable mmp-encode-c-max-element-leq-len-key)

  (defrule mmp-encode-c-max.elementp-of-empty-map
    (implies (and (nibblelist-bytelist-mapp map)
                  (omap::empty map))
             (mmp-encode-c-max.elementp map x))
    :enable (mmp-encode-c-max.elementp mmp-encode-c-forall)
    :use (:instance mmp-encode-c-exists-suff (l (repeat x 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mmp-encode-u-map
  ((map nibblelist-bytelist-mapp) (i natp) (nibble nibblep))
  :returns (map1 nibblelist-bytelist-mapp)
  :parents (mmp-trees)
  :short "Submaps used to define @($u(0),\\ldots,u(15)$)
          in the third case of the definition of @($c$) [YP:(194)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the definition of @(tsee mmp-encode-c),
     hence the name.")
   (xdoc::p
    "Here @($\\mathfrak{I}$) is the argument @('map'),
     @($i$) is the argument @('i'),
     and @($j$) is the argument @('nibble').")
   (xdoc::p
    "This function returns the submap (i.e. subset) of @('map')
     whose keys all have value @('nibble') at index @('i').
     This is the set calculated
     in the third case of the definition of @($c$)
     and passed to the function @($n$),
     whose result is assigned to @($u(j)$).")
   (xdoc::p
    "The supremum natural number of the lengths of the keys
     decreases or remains constant for the submap.")
   (xdoc::p
    "By construction,
     every key in the submap has the nibble at position @('i').")
   (xdoc::p
    "A nibble array is in the submap iff
     it is in the map and has the nibble at position @('i').")
   (xdoc::p
    "If @('i') is an element of the set maximized by @(tsee mmp-encode-c-max),
     then @('(1+ i)') is an element of the set for the submap."))
  (b* (((unless (mbt (nibblelist-bytelist-mapp map))) nil)
       ((when (omap::empty map)) nil)
       ((mv key val) (omap::head map))
       (nibble (nibble-fix nibble)))
    (if (eql (nth i key) nibble)
        (omap::update key val (mmp-encode-u-map (omap::tail map) i nibble))
      (mmp-encode-u-map (omap::tail map) i nibble)))
  :no-function t
  :verify-guards nil ; done below
  ///
  (verify-guards mmp-encode-u-map
    :hints (("Goal"
             :in-theory (enable acl2::true-listp-when-nibble-listp-rewrite))))

  (defrule nibblelist-bytelist-map-sup-len-key-of-mmp-encode-u-map-leq
    (<= (nibblelist-bytelist-map-sup-len-key (mmp-encode-u-map map i nibble))
        (nibblelist-bytelist-map-sup-len-key map))
    :rule-classes :linear
    :enable nibblelist-bytelist-map-sup-len-key)

  (defruled nth-of-key-in-mmp-encode-u-map
    (implies (and (nibblelist-bytelist-mapp map) ; bind free MAP
                  (nibblep nibble) ; bind free NIBBLE
                  (omap::in key (mmp-encode-u-map map i nibble)))
             (equal (nth i key) nibble))
    :enable omap::in)

  (defrule in-of-mmp-encode-u-map
    (implies (and (nibblelist-bytelist-mapp map)
                  (nibblep nibble))
             (equal (omap::in key (mmp-encode-u-map map i nibble))
                    (and (equal (nth i key) nibble)
                         (omap::in key map)))))

  (defrule mmp-encode-c-forall-of-mmp-encode-u-map
    (implies (and (nibblelist-bytelist-mapp map)
                  (natp i)
                  (nibblep nibble)
                  (nibble-listp l)
                  (mmp-encode-c-forall map i l))
             (mmp-encode-c-forall (mmp-encode-u-map map i nibble)
                                  (1+ i)
                                  (rcons nibble l)))
    :expand ((mmp-encode-c-forall (mmp-encode-u-map map i nibble)
                                  (1+ i)
                                  (rcons nibble l)))
    :enable (nth-of-key-in-mmp-encode-u-map
             acl2::take-of-1+-to-rcons)
    :use (:instance mmp-encode-c-forall-necc
          (x i)
          (key (mmp-encode-c-forall-witness (mmp-encode-u-map map i nibble)
                                            (+ 1 i)
                                            (rcons nibble l)))))

  (defrule mmp-encode-c-max.elementp-of-mmp-encode-u-map
    (implies (and (nibblelist-bytelist-mapp map)
                  (natp i)
                  (nibblep nibble)
                  (mmp-encode-c-max.elementp map i))
             (mmp-encode-c-max.elementp
              (mmp-encode-u-map map i nibble)
              (1+ i)))
    :cases ((omap::empty (mmp-encode-u-map map i nibble)))

    :prep-lemmas
    ((defrule lemma
       (implies (and (not (omap::empty (mmp-encode-u-map map i nibble)))
                     (nibblelist-bytelist-mapp map)
                     (natp i)
                     (nibblep nibble)
                     (mmp-encode-c-max.elementp map i))
                (mmp-encode-c-max.elementp
                 (mmp-encode-u-map map i nibble)
                 (1+ i)))
       :enable (mmp-encode-c-max.elementp
                nth-of-key-in-mmp-encode-u-map)
       :disable in-of-mmp-encode-u-map
       :expand ((mmp-encode-c-exists map i))
       :use ((:instance mmp-encode-c-exists-suff
              (map (mmp-encode-u-map map i nibble))
              (x (1+ i))
              (l (rcons (nth i (mv-nth 0 (omap::head
                                          (mmp-encode-u-map map i nibble))))
                        (mmp-encode-c-exists-witness map i))))))))

  (fty::deffixequiv mmp-encode-u-map)

  (defrule mmp-encode-u-map-when-not-natp-i
    (implies (and (syntaxp (not (equal i ''0)))
                  (not (natp i)))
             (equal (mmp-encode-u-map map i nibble)
                    (mmp-encode-u-map map 0 nibble)))
    :use (:instance mmp-encode-u-map-nat-equiv-congruence-on-i (i-equiv 0)))

  (defrule mmp-encode-u-map-when-not-nibblep-nibble
    (implies (and (syntaxp (not (equal nibble ''0)))
                  (not (nibblep nibble)))
             (equal (mmp-encode-u-map map i nibble)
                    (mmp-encode-u-map map i 0)))
    :use (:instance mmp-encode-u-map-nibble-equiv-congruence-on-nibble
          (nibble-equiv 0))
    :enable nibble-fix)

  (defrule mmp-encode-u-map-when-not-natp-nibble
    (implies (and (syntaxp (not (equal nibble ''0)))
                  (not (natp nibble)))
             (equal (mmp-encode-u-map map i nibble)
                    (mmp-encode-u-map map i 0)))
    :enable nibblep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines mmp-encode-n/c
  :parents (mmp-trees)
  :short "Definition of @($n$) [YP:(193)] and @($c$) [YP:(194)]."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(tsee mmp-encode-n) corresponds to @($n$),
     while @(tsee mmp-encode-c) corresponds to @($c$).
     @(tsee mmp-encode-u) corresponds to the ``local function'' @($u$)
     used in the third case of the definition of @($c$):
     since there are always exactly 16 calls to this function,
     we could have avoided introducing @(tsee mmp-encode-u)
     and just included 16 calls of @(tsee mmp-encode-n)
     in the definition of @(tsee mmp-encode-c),
     but instead we just include 1 call of @(tsee mmp-encode-u),
     which recursively performs the 16 iterations itself.
     Introducing @(tsee mmp-encode-u) seems clearer and more elegant
     than including 16 calls of @(tsee mmp-encode-n).")
   (xdoc::p
    "Here @($\\mathfrak{I}$) is the argument @('map') of all these functions,
     @($i$) is the argument @('i') of all these functions,
     and @($j$) in the third case of the definition of @($c$)
     is the argument @('nibble-counter') of @(tsee mmp-encode-u).")
   (xdoc::p
    "In [YP], @($n$) and @($c$) just return byte arrays,
     which are the ``roots'' of the MMP trees.
     However, their computation relies on the database:
     every call of Keccak-256 implicitly adds a pair to the database:
     the pair associates the result of the call of Keccak-256 (key)
     to the argument of the call of Keccak-256 (value).
     This is implicit in [YP],
     which mentions `prescience of the byte array' just before [YP:(193)].
     In our formalization, we explicate the database,
     by having
     @(tsee mmp-encode-n), @(tsee mmp-encode-c), and @(tsee mmp-encode-u)
     all return a database, which they construct.
     This returned database contains all and only the pairs
     necessary to encode @('map').")
   (xdoc::p
    "Since we cannot ignore the mathematical possibility of hash collisions,
     @(tsee mmp-encode-n), @(tsee mmp-encode-c), and @(tsee mmp-encode-u)
     all return an error flag that, when equal to @(':collision'),
     indicates that a collision in the constructed database took place.
     In practice, we do not expect to ever see this flag be @(':collision'),
     but the mathematical possibility remains.
     Databases constructed by sub-computations are merged,
     when no collisions occur (i.e. when the two databases are compatible maps).
     If a collision occurs,
     @('nil') is returned as both root and database;
     these values are irrelevant.
     Note that a collision happens if not only a key is already in the database,
     but also the associated value in the database differs
     from the one that is to be added to the database;
     this check is performed in @(tsee mmp-encode-n),
     the only function that directly extends the database
     (the other functions merge databases from sub-computations).
     If the key is already in the database but the value does not differ,
     then there is no collision, and no change to the database;
     if we view hashes as implementation-independent pointers
     (which is a way to view MMP trees),
     this situation just corresponding to two aliased pointers.")
   (xdoc::p
    "Since @($c$) involves RLP encoding,
     and since RLP encoding may fail (see @(tsee rlp-encode-tree)),
     the error flag returned by our functions
     is @(':rlp') when an RLP encoding fails.
     In this case, @('nil') is returned as both root and database;
     these values are irrelevant.")
   (xdoc::p
    "If no hash collisions occur and all RLP encodings succeed,
     the error flag returned by our functions is @('nil'),
     indicating no error.")
   (xdoc::p
    "The definition of @(tsee mmp-encode-n) follows
     the definition of @($n$) [YP:(193)] rather closely,
     with the additional propagation of errors
     from the recursive call of @(tsee mmp-encode-c),
     the additional propagation of the database from @(tsee mmp-encode-c),
     and the additional extension of the database mentioned above.")
   (xdoc::p
    "The definition of @(tsee mmp-encode-c) follows
     the definition of @($c$) [YP:(194)] also rather closely.
     However, since all three cases of the definition of @($c$)
     apply RLP encoding at the end,
     we factor that out of the three cases.
     First, @(tsee mmp-encode-c) calculates
     an error flag, an RLP tree, and a database according to the three cases.
     Then, @(tsee mmp-encode-c) RLP encodes the tree.
     If an error occurs prior to RLP encoding,
     the ``inner'' computation of @(tsee mmp-encode-c) returns
     an RLP tree consisting of an empty byte array and an empty database,
     but these values are irrelevant.
     Because of this factoring,
     and because some tests relevant to termination (see section below)
     appear in this factored code,
     we need to extend the @(see acl2::rulers) of @(tsee mmp-encode-c)
     with @(':lambdas').")
   (xdoc::p
    "The first case of the definition of @($c$)
     includes an existential quantifier for @($I$)
     whose scope does not actually extend
     to the use of @($I$) in @($\\mathtt{RLP}(\\ldots)$).
     In our definition we do not use an existential quantifier:
     we test whether the size of the map is 1
     and then we extract its only key and value if the test succeeds.")
   (xdoc::p
    "We use @(tsee mmp-encode-c-max) to calculate the variable @($j$)
     (which is the variable @('j') in @(tsee mmp-encode-c))
     in the second case of the definition of @($c$).
     As discussed in @(tsee mmp-encode-c-max),
     the map must be non-empty for this @('j') to be well-defined.
     Thus, we add this non-emptiness condition
     to the guard of @(tsee mmp-encode-c).")
   (xdoc::p
    "Note that the scope of the universal quantifier
     in the second case of the definition of @($c$)
     does not actually extend
     to the use of @($I$) in @($\\mathtt{RLP}(\\ldots)$):
     in this expression, @($I$) may be any pair in the map,
     because by the definition of @($j$) we know that
     all the keys in the map have the same nibbles
     at indices @($i$) through @($j-1$).
     In our definition, we pick the first key in the map.")
   (xdoc::p
    "Note that the @($j$) in the third case of the definition of @($c$)
     has no relationship to the @($j$)
     in the second case of the definition of @($c$).
     As stated above, the @($j$) in the third case
     is the argument @('nibble-counter') of @(tsee mmp-encode-u);
     this function corresponds to
     the ``local function'' @($u$)
     in the third case of the definition of @($c$).
     The nibble counter argument is initialized to 0
     by @(tsee mmp-encode-c), when it calls @(tsee mmp-encode-u).
     The latter function returns,
     essentially (but see below for more precision), @($u(0),\\ldots,u(15)$),
     along with an error flag
     and with the database resulting from all the 16 computations.")
   (xdoc::p
    "@(tsee mmp-encode-u) loops through nibble 0 to 15,
     extracting submaps and recursively calling @(tsee mmp-encode-n) on them.
     Errors are propagated and databases are merged, checking for collisions.
     @(tsee mmp-encode-u) does not quite return
     the list of roots @($u(0),\\ldots,u(15)$):
     more precisely, it returns a list of RLP leaf trees
     containing those byte arrays;
     the byte arrays and the RLP leaf trees are isomorphic,
     but the calling @(tsee mmp-encode-c) can more easily assemble the trees
     into an RLP (branching) tree.")
   (xdoc::p
    "The variable @($v$) in the third case of the definition of @($c$)
     is the value associated to the key of length @($i$) in the map,
     if it exists, in which case it is unique,
     because it is an invariant that all the keys
     have the same first @($i$) nibbles (see below).
     We pick the first key in the map (but any other would do),
     we take its first @('i') nibbles,
     and we see if the resulting key has an associated value in the map.
     Note that we do not need
     the existential quantifier in the third case of the definition of @($c$),
     whose scope does not extend to
     the expression @($I_1$) that defines @($v$) anyways.")
   (xdoc::p
    "It is not clear whether @($()$)
     in the second case of the definition of @($v$)
     in the third case of the definition of @($c$)
     is the empty byte array in @($\\mathbb{B}$) [YP:(178)]
     or the empty tuple in @($\\mathbb{L}$) [YP:(177)].
     The empty byte array is consistent with the fact that
     the @($I_1$) in the first case of the definition of @($v$)
     is also a byte array.
     However, in this case maps @($\\mathfrak{I}$) some of whose keys
     have the empty byte array associated as value
     cannot be unambiguously encoded as MMP trees,
     because we would be unable to distinguish
     between the two cases in the definition of @($v$).
     This ambiguity does not exist
     if instead the @($()$) denotes the empty tuple;
     note that the first paragraph of [YP:D] mentions
     maps between arbitrary-length byte arrays
     (suggesting that zero lengths are allowed),
     and that in the third case of the definition of @($c$),
     the argument tuple of @($\\mathtt{RLP}$),
     whose last component is @($v$),
     is well-formed whether @($v$) is a byte array or a tuple.
     So for now we interpret the @($()$) as the empty tuple.")
   (xdoc::h4 "Termination")
   (xdoc::p
    "The termination of
     @(tsee mmp-encode-n), @(tsee mmp-encode-c), and @(tsee mmp-encode-u)
     is proved via a lexicographic measure
     that consists of three components.")
   (xdoc::p
    "This termination proof relies on
     some invariants satisfied by the arguments of these functions.
     These invariants are added as guards,
     and tested with @(tsee mbt) at the beginning of the functions.
     An invariant that applies to all three functions is that
     all the keys in the map have the same first @('i') nibbles:
     this is expressed by
     <see topic='@(url mmp-encode-c-max)'>@('mmp-encode-c-max.elementp')</see>.
     An invariant that applies to @(tsee mmp-encode-c) and @(tsee mmp-encode-u)
     is that the map is not empty.
     An invariant that applies to @(tsee mmp-encode-u) is that
     the map is not a singleton.")
   (xdoc::p
    "@(tsee mmp-encode-n) calls @(tsee mmp-encode-c)
     with the same arguments @('map') and @('i'),
     and therefore the measure must involve the fact that
     @(tsee mmp-encode-c) is ``smaller'' than @(tsee mmp-encode-c).
     Similarly, @(tsee mmp-encode-c) calls @(tsee mmp-encode-u)
     with the same arguments @('map') and @('i'),
     and therefore the measure must involve the fact that
     @(tsee mmp-encode-u) is ``smaller'' than @(tsee mmp-encode-u).
     Thus, we order these functions by assigning 0, 1, and 2 to them:
     this is the second component of the lexicographic measure.")
   (xdoc::p
    "Since @(tsee mmp-encode-u) calls @(tsee mmp-encode-n)
     and @(tsee mmp-encode-c) calls @(tsee mmp-encode-n),
     the relative ordering of these functions cannot be
     the first component of the lexicographic measure.
     Instead, the first component involves @('map') and @('i').
     In the calls just mentioned,
     the recursion makes progress because @('i') strictly increases:
     it becomes either @('(1+ i)') or @('j').
     Before calling @(tsee mmp-encode-n),
     @(tsee mmp-encode-c) checks that @('j') is not @('i').
     The reason why it @('j') is larger than @('i') in this case
     is the aforementioned invariant about @('i') and the definition of @('j'):
     all the keys in the map have the same @('i') nibbles,
     and @('j') is, by definition, the maximum length of the common prefix
     of the keys in the map:
     thus, @('j') is greater than or equal to @('i'),
     and since it is different, it is larger.")
   (xdoc::p
    "The increase of @('i') in the recursive calls is bounded by
     @(tsee nibblelist-bytelist-map-sup-len-key):
     the first component of the lexicographic measure is
     the difference between that and @('i').
     When @(tsee mmp-encode-c) calls @(tsee mmp-encode-n),
     @(tsee nibblelist-bytelist-map-sup-len-key) remains the same;
     since it is greater than or equal to @('j'),
     and @('i') is strictly less than @('j'),
     the first component of the measure strictly decreases.
     When @(tsee mmp-encode-u) calls @(tsee mmp-encode-n),
     @(tsee nibblelist-bytelist-map-sup-len-key)
     either stays the same or becomes smaller,
     as proved in @(tsee mmp-encode-u-map),
     because we are calling @(tsee mmp-encode-n) on a submap of the map;
     to show that the first component of the measure strictly decreases
     as @('i') becomes @('(1+ i)'),
     we use the fact that @('i') is strictly less than
     @(tsee nibblelist-bytelist-map-sup-len-key),
     as proved in @(tsee mmp-encode-c-max),
     given that the map has at least two elements,
     as asserted by the invariant of @(tsee mmp-encode-u).")
   (xdoc::h4 "Guard Verification")
   (xdoc::p
    "The guard verification of
     @(tsee mmp-encode-n), @(tsee mmp-encode-c), and @(tsee mmp-encode-u)
     involves proving the preservation, in the recursive calls,
     of the invariants used for the termination proof, mentioned above.")
   (xdoc::p
    "This is easy for most recursive calls,
     where @('map') and @('i') do not change.")
   (xdoc::p
    "In the call of @(tsee mmp-encode-n) from @(tsee mmp-encode-c),
     @('map') stays the same, while @('i') changes to the maximum @('j');
     since in this case the maximum exists,
     it is in the set.")
   (xdoc::p
    "In the call of @(tsee mmp-encode-n) from @(tsee mmp-encode-u),
     the map becomes the submap and @('i') becomes @('(1+ i)').
     We start with the fact that
     all the keys in the map have the same first @('i') nibbles,
     By construction,
     the submap has keys with the same nibble at position @('i').
     Therefore, all the keys in the submap has the first @('(1+ i)') nibbles,
     and thus @('(1+ i)') is in the set."))

  (define mmp-encode-n ((map nibblelist-bytelist-mapp) (i natp))
    :guard (mmp-encode-c-max.elementp map i)
    :returns (mv (error? (member-eq error? '(nil :collision :rlp)))
                 (root byte-listp)
                 (database databasep))
    :parents (mmp-encode-n/c)
    (b* (((unless (mbt (mmp-encode-c-max.elementp map i)))
          (mv nil nil nil)) ; irrelevant
         ((when (or (not (mbt (nibblelist-bytelist-mapp map)))
                    (omap::empty map)))
          (mv nil nil nil))
         ((mv c-error? c-root c-database) (mmp-encode-c map i))
         ((when c-error?) (mv c-error? nil nil))
         ((when (< (len c-root) 32)) (mv nil c-root c-database))
         (hash (keccak-256-bytes c-root))
         (pair? (omap::in hash c-database))
         (collisionp (and pair?
                          (not (equal (cdr pair?)
                                      c-root))))
         ((when collisionp) (mv :collision nil nil))
         (database (omap::update hash c-root c-database)))
      (mv nil hash database))
    :measure (acl2::nat-list-measure
              (list (nfix (- (nibblelist-bytelist-map-sup-len-key map)
                             (nfix i)))
                    2
                    0))
    :no-function t)

  (define mmp-encode-c ((map nibblelist-bytelist-mapp) (i natp))
    :guard (and (mmp-encode-c-max.elementp map i)
                (not (omap::empty map)))
    :returns (mv (error? (member-eq error? '(nil :collision :rlp)))
                 (root byte-listp)
                 (database databasep))
    :parents (mmp-encode-n/c)
    (b* (((unless (mbt (and (mmp-encode-c-max.elementp map i)
                            (nibblelist-bytelist-mapp map)
                            (not (omap::empty map)))))
          (mv nil nil nil)) ; irrelevant
         ((mv error? rlp-tree database)
          (b* (((when (= (omap::size map) 1))
                (b* (((mv key val) (omap::head map))
                     (key-rest (nthcdr i key)))
                  (mv nil
                      (rlp-tree-branch
                       (list (rlp-tree-leaf (hp-encode key-rest t))
                             (rlp-tree-leaf val)))
                      nil)))
               (j (mmp-encode-c-max map))
               ((when (/= (nfix i) j))
                (b* (((mv n-error? n-root n-database) (mmp-encode-n map j))
                     ((when n-error?) (mv n-error? (rlp-tree-leaf nil) nil))
                     ((mv any-key &) (omap::head map))
                     (key-part (nthcdr i (take j any-key))))
                  (mv nil
                      (rlp-tree-branch
                       (list (rlp-tree-leaf (hp-encode key-part nil))
                             (rlp-tree-leaf n-root)))
                      n-database)))
               ((mv u-error? u-trees u-database) (mmp-encode-u map i 0))
               ((when u-error?) (mv u-error? (rlp-tree-leaf nil) nil))
               ((mv any-key &) (omap::head map))
               (key-prefix (take i any-key))
               (pair (omap::in key-prefix map))
               (v (and pair (cdr pair)))
               (v-tree (if v (rlp-tree-leaf v) (rlp-tree-branch nil))))
            (mv nil
                (rlp-tree-branch (rcons v-tree u-trees))
                u-database)))
         ((when error?) (mv error? nil nil))
         ((mv rlp-error? rlp-encoding) (rlp-encode-tree rlp-tree))
         ((when rlp-error?) (mv :rlp nil nil)))
      (mv nil rlp-encoding database))
    :measure (acl2::nat-list-measure
              (list (nfix (- (nibblelist-bytelist-map-sup-len-key map)
                             (nfix i)))
                    1
                    0))
    :no-function t)

  (define mmp-encode-u
    ((map nibblelist-bytelist-mapp) (i natp) (nibble-counter natp))
    :guard (and (mmp-encode-c-max.elementp map i)
                (not (omap::empty map))
                (not (equal (omap::size map) 1)))
    :returns (mv (error? (member-eq error? '(nil :collision :rlp)))
                 (trees rlp-tree-listp)
                 (database databasep))
    :parents (mmp-encode-n/c)
    (b* (((unless (mbt (and (mmp-encode-c-max.elementp map i)
                            (nibblelist-bytelist-mapp map)
                            (not (omap::empty map))
                            (not (equal (omap::size map) 1)))))
          (mv nil nil nil)) ; irrelevant
         ((when (> (nfix nibble-counter) 15)) (mv nil nil nil))
         (submap (mmp-encode-u-map map i nibble-counter))
         ((mv n-error? n-root n-database) (mmp-encode-n submap (1+ (nfix i))))
         ((when n-error?) (mv n-error? nil nil))
         ((mv u-error? u-trees u-database)
          (mmp-encode-u map i (1+ (nfix nibble-counter))))
         ((when u-error?) (mv u-error? nil nil))
         ((unless (omap::compatiblep n-database u-database))
          (mv :collision nil nil))
         (trees (cons (rlp-tree-leaf n-root) u-trees))
         (database (omap::update* n-database u-database)))
      (mv nil trees database))
    :measure (acl2::nat-list-measure
              (list (nfix (- (nibblelist-bytelist-map-sup-len-key map)
                             (nfix i)))
                    0
                    (nfix (- 16 (nfix nibble-counter)))))
    :no-function t)

  :ruler-extenders :lambdas

  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))

  :verify-guards nil ; done below

  :flag-local nil

  ///

  (defruledl verify-guards-lemma
    (implies (and (nibblelist-bytelist-mapp map)
                  (not (omap::empty map)))
             (nibble-listp (take (mmp-encode-c-max map)
                                 (mv-nth 0 (omap::head map)))))
    :use (:instance mmp-encode-c-max-leq-len-key
          (key (mv-nth 0 (omap::head map))))
    :disable mmp-encode-c-max-leq-len-key)

  (verify-guards mmp-encode-n
    :hints (("Goal" :in-theory (enable verify-guards-lemma nibblep))))

  (fty::deffixequiv-mutual mmp-encode-n/c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mmp-encode ((map bytelist-bytelist-mapp))
  :returns (mv (error? (member-eq error? '(nil :collision :rlp)))
               (root byte-listp)
               (database databasep))
  :parents (mmp-trees)
  :short "Encode a finite map into an MMP tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the definition of @($\\mathtt{TRIE}$) [YP:(192)].")
   (xdoc::p
    "The input is a finite map from byte arrays to byte arrays,
     which we convert to a finite map from nibble arrays to byte arrays
     before calling the mutually recursive encoding functions.
     This is left somewhat implicit in [YP:D],
     which uses the same symbol @($\\mathfrak{I}$)
     for both kinds of maps.")
   (xdoc::p
    "Even though @($\\mathtt{TRIE}$) just returns a root (a byte array),
     the encoding relies on the database.
     As done for
     @(tsee mmp-encode-n), @(tsee mmp-encode-c), and @(tsee mmp-encode-u),
     we explicate the database constructed to encode the map
     as an additional result;
     the returned root and database form the MMP tree.
     We also return an error flag
     with the same meaning as the one returned by those functions.")
   (xdoc::p
    "[YP:(192)] may call @($c$) with an empty map,
     which, as discussed in @(tsee mmp-encode-n/c),
     is prohibited by the guard of @(tsee mmp-encode-c),
     because the maximum calculated
     in the second case of the definition of @($c$)
     is not well-defined if the map is empty.
     Looking at [YP:(192)] and [YP:(193)],
     it seems more plausible that
     @($\\mathtt{TRIE}$) should be defined as @($n(\\mathfrak{I},0)$),
     which should often be the same as @($\\mathtt{KEC}(c(\\mathfrak{I},0))$),
     except (critically) in the case in which the map is empty,
     and except in the case in which the byte array returned by @($c$) is short
     (i.e. less than 32 bytes in length).
     The first paragraph of [YP:D] says that
     the map is encoded as a single value that is
     either a 32-byte sequence of bytes (i.e. a hash)
     or the empty byte sequence.
     The mention of the empty sequence contradicts
     the definition of @($\\mathtt{TRIE}$) as @($\\mathtt{KEC}(\\ldots)$)
     (since @($\\mathtt{KEC}$) always returns 32 bytes),
     and supports our interpretation.
     On the other hand, the lack of mention
     of byte sequences of lengths between 1 and 31
     contradicts our interpretation,
     for the case in which @($n$) returns a short byte sequence.
     For now we take this interpretation anyhow,
     but we may revise our formal definition
     once we disambiguate the definition of @($\\mathtt{TRIE}$).")
   (xdoc::p
    "We note that another possible interpretation might be
     to define @($\\mathtt{TRIE}(\\mathfrak{I})$) as
     @($\\mathtt{KEC}(n(\\mathfrak{I},0))$) (i.e. @($n$) instead of @($c$)).
     But this would involve a double hash for the common case,
     and would never allow the empty byte sequence.")
   (xdoc::p
    "Note that, according to our disambiguation and definition,
     the root hash returned by this function
     is not necessarily a Keccak-256 hash;
     it may be a shorter byte sequence."))
  (mmp-encode-n (bytelist-to-nibblelist-keys map) 0)
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk mmp-encoding-p ((root byte-listp) (database databasep))
  :returns (yes/no booleanp)
  :parents (mmp-trees)
  :short "Check if a root and database are an MMP encoding
          of a finite map from byte arrays to byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declarative, non-executable definition,
     which essentially characterizes the image of @(tsee mmp-encode)
     (over finite maps that can be encoded,
     i.e. such that @(tsee mmp-encode) returns a @('nil') error flag,
     except that we allow the database to be larger.")
   (xdoc::p
    "The reason is the following.
     @(tsee mmp-encode) produces the minimum database
     that suffices to encode the map.
     However, it seems reasonable that
     there is one global database [YP:D.1] [YP:4.1],
     used to encode a variety of finite maps in the Ethereum state.
     Thus, given a root and the global database,
     we can say that they together encode a finite map,
     even though the database may be larger
     then needed to encode the map."))
  (exists (map)
          (and (bytelist-bytelist-mapp map)
               (b* (((mv map-error? map-root map-database) (mmp-encode map)))
                 (and (not map-error?)
                      (equal map-root (byte-list-fix root))
                      (omap::submap map-database (database-fix database))))))
  :skolem-name mmp-encoding-witness
  ///

  (fty::deffixequiv-sk mmp-encoding-p
    :args ((root byte-listp) (database databasep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mmp-decode ((root byte-listp) (database databasep))
  :returns
  (mv (error? booleanp)
      (map bytelist-bytelist-mapp
           :hints (("Goal"
                    :in-theory
                    (e/d
                     (mmp-encoding-p)
                     (mmp-encoding-p-of-byte-list-fix-root
                      mmp-encoding-p-of-database-fix-database))))))
  :parents (mmp-trees)
  :short "Decode an MMP tree into a finite map."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the MMP tree encodes some finite map, we return that map,
     along with @('nil') as the error flag (i.e. no error).
     Otherwise, we return @('t') as error flag,
     and @('nil') as the map (which is irrelevant in this case).")
   (xdoc::p
    "Here the MMP tree is represented as the root and supporting database,
     which are the arguments of this function.
     These are the same arguments as @(tsee mmp-encoding-p),
     and correspond to the results of @(tsee mmp-encode)
     (excluding the error flag).
     As explained in @(tsee mmp-encoding-p),
     the database may be larger than strictly needed
     for representing the finite map.")
   (xdoc::p
    "This is a declarative, non-executable definition,
     which says that decoding is the inverse of encoding.")
   (xdoc::p
    "More precisely, we define decoding as, essentially,
     the right inverse of encoding
     (with respect to MMP trees that are valid encodings of finite maps),
     as explicated by the theorem @('mmp-encode-of-mmp-decode').
     It is not quite the right inverse,
     because, as discussed in @(tsee mmp-encoding-p),
     we allow a larger (global) database to encode a map.
     Thus, the theorem @('mmp-encode-of-mmp-decode') is a weaker version
     of an actual inversion theorem:
     it asserts equality of roots and containment of databases.")
   (xdoc::p
    "To prove that decoding is left inverse of encoding
     (with respect to finite maps that can be encoded),
     we need to show that encoding is injective over maps that can be encoded.
     We conjecture that the proof of this property
     may be a by-product of deriving an executable implementation of decoding
     via stepwise refinement
     (e.g. using <see topic='@(url apt::apt)'>APT</see>):
     if there were two different maps whose encodings are equal,
     an executable implementation of decoding, which returns a unique map,
     could not be shown to be equal to @('mmp-endoding-witness'),
     which is introduced by a @(tsee defchoose) inside @(tsee defun-sk)
     and therefore could be either map.
     Thus, we defer the injectivity and left inverse proofs for now."))
  (b* ((root (byte-list-fix root))
       (database (database-fix database)))
    (if (mmp-encoding-p root database)
        (mv nil (mmp-encoding-witness root database))
      (mv t nil)))
  :hooks (:fix)
  :no-function t
  ///

  (defrule mmp-encode-of-mmp-decode
    (implies (and (byte-listp root)
                  (databasep database)
                  (mmp-encoding-p root database))
             (b* (((mv d-error? d-map) (mmp-decode root database))
                  ((mv e-error? e-root e-database) (mmp-encode d-map)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-root root)
                    (omap::submap e-database database))))
    :enable mmp-encoding-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mmp-read ((key byte-listp)
                  (root byte-listp)
                  (database databasep))
  :guard (mmp-encoding-p root database)
  :returns (mv (presentp booleanp) (value byte-listp))
  :parents (mmp-trees)
  :short "Read the value associated to a key in an MMP tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require (in the guard) that the MMP tree is valid,
     i.e. it encodes a finite map.")
   (xdoc::p
    "We provide a high-level definition here.
     We decode the MMP tree and we look up the key.
     We return a flag indicating whether the key is present,
     and we return the byte array value associated to key
     (@('nil') if the key is absent."))
  (b* (((mv & map) (mmp-decode root database))
       (pair? (omap::in (byte-list-fix key)
                        (bytelist-bytelist-mfix map))))
    (if (consp pair?)
        (mv t (cdr pair?))
      (mv nil nil)))
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mmp-write ((key byte-listp)
                   (value byte-listp)
                   (root byte-listp)
                   (database databasep))
  :guard (mmp-encoding-p root database)
  :returns (mv (error? (member-eq error? '(nil :collision :rlp))
                       :hints (("Goal"
                                :in-theory (disable member-equal
                                                    acl2::member-of-cons
                                                    acl2::member-when-atom)
                                :use (:instance
                                      return-type-of-mmp-encode.error?
                                      (map (omap::update
                                            (byte-list-fix key)
                                            (byte-list-fix value)
                                            (mv-nth 1 (mmp-decode
                                                       root
                                                       database))))))))
               (new-root byte-listp)
               (new-database databasep))
  :parents (mmp-trees)
  :short "Write a value for a key in an MMP tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require (in the guard) that the MMP tree is valid,
     i.e. it encodes a finite map.")
   (xdoc::p
    "We provide a high-level definition here.
     We decode the MMP tree, we update the key,
     and we re-encode the map.
     The key may already be present, in which case the old value is overwritten.
     If the key is not present, it is added to the map.")
   (xdoc::p
    "The @('database') argument of this function represents the global database.
     Thus, we return not just the database needed to encode the updated map,
     but the union of that with the input database.
     Thus, the resulting database may include more than needed
     to simply encode the new finite map.
     If we view the hashes in the database
     as implementation-independent pointers,
     updating the MMP tree may lead to
     ``garbage'' in the sense of garbage collection,
     i.e. portions of the database that are no longer referenced,
     directly or indirectly, starting from the ``roots'' in the Ethereum state.
     Presumably an Ethereum implementation
     could perform some garbage collection,
     but here we conservatively assume that it does not.")
   (xdoc::p
    "If the re-encoding of the new finite map causes a collision
     or produces some non-RLP-encodable data,
     we forward the error flag returned by @(tsee mmp-encode).
     We also check for collision when taking the union of
     the initial database and the one returned by @(tsee mmp-encode),
     returning @(':collision') if such a collision happens."))
  (b* (((mv & map) (mmp-decode root database))
       (new-map (omap::update (byte-list-fix key)
                              (byte-list-fix value)
                              map))
       ((mv error? new-root new-database-min) (mmp-encode new-map))
       ((when error?) (mv error? nil nil))
       ((unless (omap::compatiblep new-database-min
                                   (database-fix database)))
        (mv :collision nil nil))
       (new-database (omap::update* new-database-min
                                    (database-fix database))))
    (mv nil new-root new-database))
  :hooks (:fix)
  :no-function t)
