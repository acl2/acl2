(in-package "X86ISA")

(include-book "basic-structs")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(include-book "centaur/fty/bitstruct" :dir :system)

(defsection
  tlb
  :parents (x86isa)

  :short "A translation lookaside buffer for the @('x86isa') model."
  :long "
  <h3>Why?</h3>

  <p>Walking the page tables to translate virtual addresses to physical
  addresses is a relatively expensive operation, both in hardware and software.
  Real processors use various address translation caches to avoid page table
  walks and speed up memory access. These caches are not completely transparent
  to the software running on the processor, requiring software to explicitly
  invalidate cache entries, so the semantics of such caches is codified in the
  ISA.</p>

  <p>The x86 ISA supports a number of address translation caches including
  TLBs. The ISA leaves many details of the operation of such caches
  underspecified to allow for flexibility in implementation. For example, in
  hardware, all caches must be fixed size. A processor with a small cache will
  likely invalidate cache entries to make room for new ones more often than a
  processor with a large cache. Thus, the ISA says any address translation
  cache entry may be invalidated at any time.</p>

  <h3>How closely does this model the caching behavior allowed by the ISA?</h3>
  <p>Modeling the complete semantics of address translation caches is difficult
  due to how much behavior is underspecified. Doing so in a manner that allows
  us to use these caches to improve performance in execution, which was our
  primary goal when implementing the TLB, is even more difficult. Thus, we
  choose to instead model a particular implementation of an address translation
  caching system that is consistent with the ISA, but is not necessarily
  consistent with all valid address translation caching systems.</p>

  <h3>Some weirdness with our design</h3>
  <p>While we call our address translation cache system a TLB, it is important
  to note that, as far as the ISA is concerned, it is actually many independent
  TLBs. Why? A TLB as described in Intel's SDM (Volume 3 Chapter 4.10.2),
  assuming all pages are 4k in size (for this discussion; the general problem holds
  even for large pages, but with some added complexities) maps virtual page
  numbers to a summary of the information in the paging structures that govern
  that virtual page's translation. Thus, a given virtual page may only have one
  translation in cache.</p>

  <p>However, what we describe as our TLB maps virtual page numbers, various
  processor control bits, whether it was an implicit supervisor access, and the
  type of access (read/write/execute), to a physical page number. This allows
  for a single virtual page number to have multiple cached translations.</p>

  <h3>Is our weird TLB design allowed by the ISA?</h3>
  <p>It turns out, yes. Volume 3 Chapter 4.10.2.2 of Intel's SDM includes the
  following parenthetical \"(TLB entries may contain other information as well.
  A processor may implement multiple TLBs, and some of these may be for special
  purposes, e.g., only for instruction fetches. Such special-purpose TLBs may
  not contain some of this information if it is not necessary. For example, a
  TLB used only for instruction fetches need not contain information about the
  R/W and dirty flags.)\" This allows us to explain the behavior of our TLB by
  claiming that it is in fact multiple TLBs, one for however many entries a
  single virtual page can have in our TLB.</p>

  <h3>Why not a more \"normal\" TLB?</h3>
  <p>One may ask why the TLB was implemented this odd way. The address
  translation system (see @(tsee ia32e-la-to-pa) and friends) was initially
  implemented without a TLB. The way it worked was by walking the page tables
  and at each level determine whether the current level allowed or disallowed
  the access. If it was allowed it would continue to the next level, or, if it
  was at the last level, allow the translation. Otherwise, it would stop the
  page table walk early and set the @('fault') field of the model to indicate a
  page-fault.</p>

  <p>Changing the address translation system to instead walk the page tables
  and return a summary of the information in the page tables about the page an
  address is in and then determine whether the access is allowed after the page
  table walk is compelete, which would allow us to cache page table information
  in a TLB, would require making many updates to the lemma library. To avoid
  having to make significant changes to many of these proofs, we chose instead
  to use this odd implementation of a TLB which was easier to implement by
  modifying the old code and required less substantial changes to the proofs in
  the lemma library.</p>

  <h3>Looking up values quickly</h3>
  <p>The cache is pretty useless if we can't lookup entries quickly. We use a
  @(tsee acl2::fast-alist), which allows for fast lookups while reasoning about
  the TLB as if it is an alist. Additionally, to allow for fast lookup in a
  hash table, for the purposes of address translation caching we always treat
  pages as being 4k wide, which is allowed by the ISA as long as we invalidate
  all entries associated with a large page when the software requests to
  invalidate any one of them. To maintain this, we always invalidate the entire
  TLB when we wish to invalidate any part of it, even if that is not strictly
  necessary, like when the software issues an @('INVLPG') instruction, which is
  allowed by the ISA since we can invalidate any entry at any time.</p>")

(defbitstruct
  tlb-key
  :parents (tlb)
  :short "A key for our TLB implementation."
  :long "<p>TLB keys serve as keys into the @('tlb') field of the @('x86') stobj.</p>"
  ((wp bitp "the @('wp') field of cr0")
   (smep bitp "the @('smep') field of cr4")
   (smap bitp "the @('smap') field of cr4")
   (ac bitp "the @('ac') field of rflags")
   (nxe bitp "the @('nxe') field of the IA32E_EFER MSR")
   (implicit-supervisor-access bitp "0 or 1, corresponding to whether the the
  @('implicit-supervisor-access') field of the @('x86') state is nil or t")
   (r-w-x 2bits "0, 1, or 2, which correspond to read, write, and execute
          translations respectively. 3 is invalid.")
   (cpl 2bits "the current privilege level when the access was made - except
        when @('implicit-supervisor-access') is t, in which case it is 0.")
   (vpn 36bits "the virtual page number of the 4k page the corresponds to"))
  :inline t)

;; The make-tlb function generated by defbitstruct is incredibly slow because
;; it uses logapp and logapp isn't declared inline. We define logapp-inline,
;; which we define as a macro since ccl won't inline it if we define it as an
;; inline function and then use it to create tlb-key-fast which is defined
;; logically as tlb-key but in execution uses logapp-inline. We then define
;; make-tlb-key-fast, which is the same as make-tlb-key, but uses tlb-key-fast
;; internally instead of tlb-key.

(defmacro logapp-inline
  (n a b)
  `(logior (logand ,a (1- (ash 1 ,n)))
           (ash ,b ,n)))

(local
  (defthmd logapp-is-logapp-inline
           (implies (and (natp n)
                         (integerp a)
                         (integerp b))
                    (equal (logapp n a b)
                           (logapp-inline n a b)))
           :hints (("Goal" :in-theory (enable bitops::logapp** bitops::logapp-induct)))))

(local
  (define gen-fast-ctor (fields)
    :mode :program
    (b* (((list* field rst) fields)
         ((fty::bitstruct-field field))
         ((mv width body)
          (if (null rst)
            (mv field.width field.name)
            (b* (((mv rst-width rst-body) (gen-fast-ctor rst)))
                (mv (+ rst-width field.width)
                    `(logapp-inline ,field.width ,field.name
                                              ,rst-body))))))
        (mv width `(the (unsigned-byte ,width)
                        ,body)))))

(local
  (define gen-fast-ctor-arg-list (fields)
    :mode :program
    (b* (((when (null fields)) nil)
         ((list* field rst) fields)
         ((fty::bitstruct-field field)))
        (cons `(,field.name :type (unsigned-byte ,field.width))
              (gen-fast-ctor-arg-list rst)))))

(make-event
  (b* ((bitstruct-table (table-alist 'fty::bitstruct-table (w state)))
       (tlb-key-structure (fty::lookup-bitstruct 'tlb-key bitstruct-table))
       ((fty::bitstruct tlb-key-structure))
       (tlb-key-formals (acl2::formals 'tlb-key (w state)))
       ((mv & ctor-body) (gen-fast-ctor tlb-key-structure.fields)))
      `(define tlb-key-fast 
         :parents (tlb-key)
         :short "A faster constructor for @(tsee tlb-key)s."
         :long "<p>The @(tsee fty::defbitstruct) book creates a @('tlb-key')
         function and @('make-tlb-key') macro to construct TLB keys, but it is
         very slow because it uses logapp, which can't be inlined, and doesn't
         put in all the type declarations.</p>

         <p>This version is faster because it uses a macro which expands to a
         composition of @('logior'), @('ash'), @('logand'), and @('1-')
         instead of logapp (declaring it as an inlineable function instead of
         a macro wouldn't get inlined by CCL) and puts in the correct type
         declarations. Using this functions instead of @('tlb-key') provided a
         ~20% speed up in model execution. We also declare a
         @('make-tlb-key-fast') macro which is just like @('make-tlb-key') but
         uses @('tlb-key-fast') under the hood to construct the
         @('tlb-key').</p>

         <p>We use @(tsee mbe) and leave this enabled so it rewrites to
         @('tlb-key'). This allows us to reason about that function instead
         while getting the execution performance of this implementation.</p>"
         ,(gen-fast-ctor-arg-list tlb-key-structure.fields)
         :enabled t
         :guard-hints (("Goal" :in-theory (enable tlb-key logapp-is-logapp-inline)))
         (mbe :logic (tlb-key ,@tlb-key-formals)
              :exec ,ctor-body)
         ///
         ,(std::da-make-maker 'tlb-key-fast
                              (fty::bitstruct-primary-fields->names tlb-key-structure.fields)
                              (fty::bitstruct-fields->defaults tlb-key-structure.fields)))))

(define good-tlb-key-p (key)
  :enabled t
  :guard t
  :parents (tlb-key)
  :short "Recongnizer for a valid TLB key."
  :long "<p>The @(tsee fty::defbitstruct) book generates a @('tlb-key-p')
  recongnizer, but that allows a @('tlb-key') to have @('r-w-x') to be set to
  3, since it is a 2 bit field, but we only want to allow it to be 0-2 because
  we only have three kinds of accesses, read/write/execute. @('good-tlb-key-p')
  recongizes a @('tlb-key-p') which has the r-w-x field less than or equal to
  2. All keys in the TLB are @('good-tlb-key-p').</p>"
  (and (tlb-key-p key)
       (<= (tlb-key->r-w-x key) 2)))

(define good-tlb-key-fix (key)
  :guard (good-tlb-key-p key)
  :inline t
  (mbe :logic (if (good-tlb-key-p key)
                key
                0)
       :exec key)
  ///
  (defthm good-tlb-key-fix-is-identity-on-good-tlb-key-p
          (implies (good-tlb-key-p x)
                   (equal (good-tlb-key-fix x)
                          x)))

  (defthm good-tlb-key-fix-is-good-tlb-key
          (good-tlb-key-p (good-tlb-key-fix x))))

(fty::deffixtype good-tlb-key
                 :pred good-tlb-key-p
                 :fix good-tlb-key-fix
                 :equiv good-tlb-key-equiv
                 :define t
                 :forward t)

(define tlb-entryp (x)
  :guard t
  :enabled t
  :parents (tlb)
  :short "Recognizer for TLB entries."
  :long "<p>@('tlb-entryp') recognizes TLB entries, i.e. elements of the the
  @('tlb') field on the @('x86') stobj. Each entry is a @('cons'), where the
  @('car') is a @('good-tlb-key-p') and the cdr is a physical page number.</p>"
  (b* (((unless (consp x)) nil)
       ((cons key val) x))
      (and  (good-tlb-key-p key)
            (unsigned-byte-p (- #.*physical-address-size* 12) val))))

(define tlbp (tlb)
  :guard t
  :parents (tlb)
  :short "Recongizer for the @('tlb') field of the @('x86') state."
  :long "<p>@('tlbp') recongizes a list where all the entries are @(tsee
  tlb-entryp) and the final @('cdr') is @(':tlb'), which serves as the name
when the @('tlbp') is a @(tsee acl2::fast-alist). This is the type of the @('tlb')
field on the @('x86') stobj.</p>"
  (b* (((unless (consp tlb)) (equal tlb :tlb))
       ((list* el tail) tlb)
       ((unless (tlb-entryp el)) nil))
      (tlbp tail))
  ///
  (defthm |:tlb-is-tlbp|
          (tlbp :tlb))

  (defthm consing-tlb-entry-onto-tlbp-is-tlbp
          (implies (and (tlb-entryp entry)
                        (tlbp tlb))
                   (tlbp (cons entry tlb))))

  (defthm integerp-cdr-hons-assoc-equal-tlb
          (implies (tlbp tlb)
                   (b* ((result (hons-assoc-equal key tlb)))
                       (implies result
                                (integerp (cdr result)))))
          :hints (("Goal" :in-theory (enable (hons-assoc-equal)))))

  (defthm unsigned-byte-p-40-cdr-hons-assoc-equal-tlb
          (implies (tlbp tlb)
                   (b* ((result (hons-assoc-equal key tlb)))
                       (implies result
                                (unsigned-byte-p (- #.*physical-address-size* 12) (cdr result)))))
          :hints (("Goal" :in-theory (enable (hons-assoc-equal))))))

(define tlb-fix (x)
  :guard t
  :returns (tlb tlbp)
  (if (tlbp x)
    x
    :tlb)
  ///
  (defthm tlb-fix-of-tlb
          (implies (tlbp x)
                   (equal (tlb-fix x) x))))
